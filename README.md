# ASDlite
<b><i>ASDlite is a light-weight version of ASDF</i></b>


ASDlite is a light-weight version of [ASDF (Another System Definition Facility)](http://common-lisp.net/project/asdf/), an extensible build facility for Common Lisp. It supports basis ASDF functions and operation classes and can be used as a replacement in many cases.

Platforms
---------

ASDlite was tested on the following Lisp implementations:
* [LispWorks](http://www.lispworks.com/) 4.4, 5.0, and 6.1.
* [SBCL](http://www.sbcl.org/)SBCL 1.0.55.

ASDlite design goals
--------------------

* Small footprint.
* Ease of embedding into applications and systems not related to "compile-and-load Lisp files" tasks, for example, [YstokHelp](http://lisp.ystok.ru/yhelp/).
* ASDF compatibility for typical needs.
* Operation arguments specification in dependencies.

Operations in ASDlite
---------------------   

    operation ::= keyword | operation-instance
    operation-type ::= keyword | type-symbol
    operation-designator ::= keyword | (keyword . plist) | type-symbol | operation-instance
    
Operations are passed to <code>perform</code> and other operation-specific methods. Operation designators can be used in the right-hand side of rules.
We encourage using simple keywords like <code>:compile</code> or <code>:load</code>. For these, ASDlite defines corresponding methods with <code>eql</code> specializers.
The <i>plist</i> allows you to pass key arguments to the operation methods. In the <i>normal mode</i>, ASDlite accepts only keyword-based forms.

If you feel these are not enough and need "full-fledged" ASDF operation classes, you can switch to the ASDF <i>compatibility mode</i> as follows:
* push <code>:asdf-compat</code> into <code>*features*</code> before compiling [asdlite.lisp](https://github.com/RN-S1/ASDlite/blob/master/asdlite.lisp),
* refer to <code>asdf:compile-op</code>, <code>asdf:load-op</code> and the like,
* efine your own subclasses of the <code>operation</code> class etc.

In the compatibility mode, ASDlite accepts all the above forms of operations and designators.

Dependencies in ASDlite
---------------------

An <i>action</i> is a pair of an operation and a component. Some actions modify the file system, whereas other actions modify the current image, and this implies a difference in how to interpret timestamps.

<i>Dependencies (rules)</i> between actions are stored in each <i>(target)</i> component and represented by the two alists of target operations to other <i>(dependee)</i> actions.

<p>There are two kinds of rules:<br>
caused-by (named "in-order-to" in ASDF)<br>
- If any of dependee actions are already in the current plan (as its results have become out-of-date according to timestamp or as a result of other rules executing successfully), that triggers this rule, i.e. the target action is also placed into the plan.<br>
requires (named "do-first" in ASDF)<br>
- These dependee actions have to be planned before the operation on the target component. But they do not trigger this rule per se, i.e. re-performing the target operation.</p>

<b>Syntax</b>

    rule ::= (target-op (dep-op {dependee}+)+)
    target-op ::= operation-type
    dep-op ::= operation-designator | :features
    dependee ::= name-or-path | (name-or-path . plist)
    name-or-path ::= component-name | vector | feature
    plist ::= ([:features feature] [:version minimum-version] {property value}*)
    feature ::= keyword | feature-expression

<b>Example</b>

    (:component "A"
      :caused-by ((:compile (:compile "B" "C") (:load "D"))
                  (:load (:load "B" "C")))
      :requires ((:compile (:load "B"))))

If B has changed, B.fasl needs to be recompiled. So the caused-by rule triggers recompiling of A.fasl irrespective of whether A has itself changed.

If A has changed, this neither imply compiling B nor C. But due to the requires rule loading B.fasl must be in the image precede compiling A.

ASDlite macroexpands the <code>:depends-on</code> option into a batch of caused-by rules similarly to what ASDF does (though this behavior is considered rather application-specific):

    :depends-on dependee-list 
     =>
    (:caused-by (:compile (:compile dependee-list))
                (:load (:load dependee-list))
                ...)

CAUTION: A component is only allowed to depend on its siblings, i.e. the components of the same module, no mater how we define dependencies:
* either <code>:caused-by</code>, <code>:requires</code>, or <code>:depends-on</code> option,
* or <code>operation-caused-by/-requires</code> method.

Observation and rationale
-------------------------

<p>1. The ASDF built-in operation hierarchy is actually of two-level depth. The original ASDF code does not exploit operation inheritance much (though something can be found in asdf-ecl.lisp).</p>
<p>2. The operation slots are rather useless:<br>
<i>original-initargs</i><br>
- Is only referred in print-object<br>
<i>parent</i><br>
- In principle, indicates the target operation that required this one.<br>
- But due to reusing operation objects in <code>make-sub-operation</code>, this is not the case.<br>
- Also used for marking along with other visiting slots during traverse but we follow another approach.<br>
Adding entirely new operations, i.e. on the first level, is fine. But there is comfortable way to refine existing operations: the easiest way is to add slots to base operation classes as only those properties do get passed into dependency operations.<br>
There is a more simple way pass arguments from operate to operation functions - by means of key arguments!</p>
<p>3. The <code>:do-first</code> initarg is actually ignored by ASDF - its always set to<br>
<code>((compile-op (load-op ,@depends-on))))</code></p>
<p>4. Avoid inline methods, which are rather inelegant in ASDF:<br>
- they rely on <code>eval</code>,<br>
- ASDF tries to remove a method from a generic function of a different name. Due to non-standard behavior of <code>remove-method</code> in LW 4.4, system redefinition intrusively signals about this.<br></p>
<p>5. Referring to features in component definition is more useful than in dependency rules.<p>
<p>6. Despite adherence to the object-oriented representation of operations, the source code exhibits "non-generic" approach to naming slot readers and accessors :-).<br>
For example:<br>
     - <code>component-parent</code> vs. <code>operation-parent</code><br>
     - <code>component-version</code> vs. <code>missing-version</code><br>
     - <code>module-components</code> vs. <code>circular-dependency-components</code></p>

Platforms
---------

The source code was tested on the following Lisp implementations:
* [LispWorks](http://www.lispworks.com/) 4.4, 5.0 and 6.1 for Windows,
* [SBCL](http://www.sbcl.org/) 1.0.55 for Windows.

Download and installation
-------------------------

Simply download the file [asdlite.lisp](https://github.com/RN-S1/ASDlite/blob/master/asdlite.lisp), compile and load it.

Documentation
--------------

For general concepts and functions, follow the [ASDF documentation](http://common-lisp.net/project/asdf/#documentation).




<i>forked from
[http://ystok.ru/](http://lisp.ystok.ru/asdlite/)</i>
