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

<code>operation ::= keyword | operation-instance
operation-type ::= keyword | type-symbol
operation-designator ::= keyword | (keyword . plist) | type-symbol | operation-instance</code>

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

There are two kinds of rules.

caused-by (named "in-order-to" in ASDF)
    If any of dependee actions are already in the current plan (as its results have become out-of-date according to timestamp or as a result of other rules executing successfully), that triggers this rule, i.e. the target action is also placed into the plan.
requires (named "do-first" in ASDF)
    These dependee actions have to be planned before the operation on the target component. But they do not trigger this rule per se, i.e. re-performing the target operation.

Syntax

rule ::= (target-op (dep-op {dependee}+)+)
target-op ::= operation-type
dep-op ::= operation-designator | :features
dependee ::= name-or-path | (name-or-path . plist)
name-or-path ::= component-name | vector | feature
plist ::= ([:features feature] [:version minimum-version] {property value}*)
feature ::= keyword | feature-expression

Example

(:component "A"
  :caused-by ((:compile (:compile "B" "C") (:load "D"))
              (:load (:load "B" "C")))
  :requires ((:compile (:load "B"))))

If B has changed, B.fasl needs to be recompiled. So the caused-by rule triggers recompiling of A.fasl irrespective of whether A has itself changed.

If A has changed, this neither imply compiling B nor C. But due to the requires rule loading B.fasl must be in the image precede compiling A.

ASDlite macroexpands the :depends-on option into a batch of caused-by rules similarly to what ASDF does (though this behavior is considered rather application-specific):

:depends-on dependee-list 
 =>
(:caused-by (:compile (:compile dependee-list))
            (:load (:load dependee-list))
            ...)

CAUTION: A component is only allowed to depend on its siblings, i.e. the components of the same module, no mater how we define dependencies:

    either :caused-by, :requires, or :depends-on option,
    or operation-caused-by/-requires method.

Observation and rationale

    The ASDF built-in operation hierarchy is actually of two-level depth. The original ASDF code does not exploit operation inheritance much (though something can be found in asdf-ecl.lisp).
    The operation slots are rather useless:

    original-initargs
        Is only referred in print-object
    parent
        In principle, indicates the target operation that required this one.
        But due to reusing operation objects in make-sub-operation, this is not the case.
        Also used for marking along with other visiting slots during traverse but we follow another approach.

    Adding entirely new operations, i.e. on the first level, is fine. But there is comfortable way to refine existing operations: the easiest way is to add slots to base operation classes as only those properties do get passed into dependency operations.
    There is a more simple way pass arguments from operate to operation functions - by means of key arguments!
    The :do-first initarg is actually ignored by ASDF - its always set to
     ((compile-op (load-op ,@depends-on))))
    Avoid inline methods, which are rather inelegant in ASDF:
    - they rely on eval,
    - ASDF tries to remove a method from a generic function of a different name. Due to non-standard behavior of remove-method in LW 4.4, system redefinition intrusively signals about this.
    Referring to features in component definition is more useful than in dependency rules.
    Despite adherence to the object-oriented representation of operations, the source code exhibits "non-generic" approach to naming slot readers and accessors :-).
    For example:
     - component-parent vs. operation-parent
     - component-version vs. missing-version
     - module-components vs. circular-dependency-components

Platforms

The source code was tested on the following Lisp implementations:

    LispWorks 4.4, 5.0 and 6.1 for Windows,
    SBCL 1.0.55 for Windows.

Download and installation

Simply download the file asdlite.lisp, compile and load it.
Documentation

For general concepts and functions, follow the ASDF documentation.
Changes and additions

    Changed syntax of dependency to more consistent:
    (dep-op {component-name | (component-name . plist)}+),
    where plist can contain the :version and :features properties.
    Other properties are passed as the operation methods arguments (and to make-sub-operation in the compatibility mode).
    Component slots in-order-to and do-first were replaced by caused-by and requires correspondingly; the old initargs :in-order-to and :do-first are also retained.
    Dependencies are calculated by the two generic functions:
     * operation-caused-by (former component-depends-on),
     + operation-requires (added).
    The default list of "requires" dependencies usually involves cross-operation rules and is now initialized from a component type by virtue of of generic:
    + depends-on-requires (added).
    Turned into generic the following ordinary functions:
    - coerce-name.
    Turned into ordinary the following generic functions:
    - version-satisfies.
    Removed generics:
    - component-self-dependencies (in fact replaced with dependencies-on-component),
    - traverse (replaced by collect-plan)
    Added structure class action.
    Action is a minimal planning and performing unit, which stores the operation status and timestamp.
    Component
    slots properties
    Turned into plist instead of alist; the generic function component-property accepts the third optional parameter default.
    features
    Added, can be either a keyword or a feature expression (on LispWorks only). The component (and all its children) is only considered during planning when the feature expression is true. When it is false, every operation on the component is treated by the planner as done and does not trigger any caused-by target actions.
    actions
    Added, a list of unified actions - no duplicates according to operation-eq.
    operation-times
    Removed in favor of actions.
    Added component-output-pathname generic.
    It allows target directory specification, e.g. :output-pathname "/my-project/bin/"
    Added :initform nil form to many slots.
    Added structure class action with planned status and timestamp slots;
    Added the component slot actions keeping unique actions.
    Introduced helpers get-timestamp and set-timestamp.
    Introduced dynamic-file, a component subclass for cl-source-file and the like.
    The value of *verbose-out* can be either T or a stream.
    Renamed
    - class formatted-system-definition-error to system-definition-simple-error,
    - some readers of condition classes slots,
    - some helpers replaced by the similar borrowed from Ystok-Library.
    Removed
    - :weakly-depends-on option,
    - component inline methods,
    - all calls of the eval function,
    - standard-asdf-method-combination,
    - format strings ~<> as delivering them with LispWorks requires keeping the pretty-printer.


forked from
[http://ystok.ru/](http://lisp.ystok.ru/asdlite/)
