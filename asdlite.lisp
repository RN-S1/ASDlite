;;; -*- Mode: Lisp; Syntax: Common-Lisp; -*-
;;; ASDlite - Light-weight excerpt from ASDF with add-ons
;;; Copyright (c) 2009-2015 Dr. Dmitry Ivanov.  All rights reserved.
;;; Copyright (c) 2001-2011 Daniel Barlow and contributors (ASDF 1.131, 2.015)
;;; $Id: asdlite.lisp 2 2015-12-19 14:24:26Z digo $
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Version: 1.2
;;; Website: http://lisp.ystok.ru/asdlite/
;;; ASDF website: http://common-lisp.net/project/asdf/
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
;;; LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
;;; OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
;;; WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;; ASDLITE DESIGN GOALS
;;;
;;; 1. Small footprint.
;;; 2  Ease of embedding into applications and systems not related to
;;;    "compile-and-load Lisp files" tasks.
;;;    For example: YstokHelp (http://lisp.ystok.ru/yhelp/)
;;; 3. ASDF compatibility for basic needs.
;;; 4. Operation arguments specification in dependencies.

;;; OPERATIONS IN ASDLITE
;;;   operation ::= keyword | operation-instance
;;;   operation-type ::= keyword | type-symbol
;;;   operation-designator ::= keyword | (keyword . plist)
;;;			     | type-symbol | operation-instance
;;;
;;; Operations are passed to perform and other operation-specific  methods.
;;; Operation designators can be used in the right-hand side of rules.
;;;
;;; We encourage using simple keywords like :compile or :load.
;;; For these, ASDlite defines corresponding methods with eql specializers.
;;; The plist allows you to pass key arguments to the operation methods.
;;; In the "normal" mode, ASDlite accepts only keyword-based forms.
;;;
;;; If you feel these are not enough and need "full-fledged" ASDF operation
;;; classes, you can switch to the ASDF compatibility mode as follows:
;;; - push :asdf-compat into *features* before compiling asdlite.lisp,
;;; - refer to asdf:compile-op, asdf:load-op and the like,
;;; - define your own subclasses of the operation class
;;;   etc.
;;; In the compatibility mode, ASDlite accepts all the above forms of operations
;;; and designators.

;;; DEPENDENCIES IN ASDLITE
;;; An action is a pair of an operation and a component.
;;; Some actions modify the filesystem, whereas other actions modify the current
;;; image, and this implies a difference in how to interpret timestamps. 
;;;
;;; Dependencies (rules) between actions are stored in each (target) component
;;; and represented by the two alists of target operations to other (dependee)
;;; actions.
;;;
;;; There are two kinds of rules:
;;;
;;; caused-by (named "in-order-to" in ASDF)
;;;   If any of dependee actions are already in the current plan
;;;   (as its results have become out-of-date according to timestamp
;;;   or as a result of other rules executing successfully), that triggers
;;;   this rule, i.e. the target action is also placed into the plan.
;;;
;;; requires (named "do-first" in ASDF)
;;;   These dependee actions have to be planned before the operation on
;;;   the target component. But they do not trigger this rule per se,
;;;   i.e. re-performing the target operation.
;;;
;;; Syntax:
;;;   rule ::= (target-op (dep-op {dependee}+)+)
;;;   target-op ::= operation-type
;;;   dep-op ::= operation-designator | :features
;;;   dependee ::= name-or-path | (name-or-path . plist)
;;;   name-or-path ::= component-name | vector | feature
;;;   plist ::= ([:features feature] [:version minimum-version] {property value}*)
;;;   feature ::= keyword | feature-expression
;;;
;;; Example:
;;;   (:component "A"
;;;    :caused-by ((:compile (:compile "B" "C") (:load "D"))
;;;                (:load (:load "B" "C")))
;;;    :requires ((:compile (:load "B"))))
;;;
;;;   If B has changed, B.fasl needs to be recompiled. So the caused-by rule triggers
;;;   recompiling of A.fasl irrespective of whether A has itself changed.
;;;
;;;   If A has changed, this neither imply compiling B nor C. But due to the requires rule
;;;   loading B.fasl must be in the image precede compiling A.
;;;
;;; CAUTION:
;;;   A component is only allowed to depend on its siblings, i.e. the components
;;;   of the same module, no mater how we define dependencies:
;;;   - either :depends-on option,
;;;   - or operation-caused-by/-requires method.

;;; OBSERVATION AND RATIONALE
;;;  1. The ASDF built-in operation hierarchy is actually of two-level depth.
;;;     Original ASDF code does not exploit operation inheritance much
;;;     (though something can be found in asdf-ecl.lisp).
;;;
;;;  2. The operation slots are rather useless:
;;;     original-initargs
;;;	  Is only referred in print-object
;;;     parent
;;;       In principle, indicates the target operation that required this one.
;;;	  But due to reusing operation objects in make-sub-operation,
;;;       this is not the case. 
;;;	  Also used for marking along with other visiting slots during traverse
;;;       but we follow another approach.
;;;
;;;     Adding entirely new operations, i.e. on the first level, is fine.
;;;     But there is comfortable way to refine existing operations: the easiest way 
;;;     is to add slots to base operation classes as only those properties
;;;     do get passed into dependency operations.
;;;
;;;     There is a more simple way pass arguments from operate to
;;;     operation functions - by means of key arguments!
;;;
;;;  3. The :do-first initarg is actually ignored by ASDF - its always set to
;;;	  ((compile-op (load-op ,@depends-on))))
;;;
;;;  4. Avoid inline methods, which are rather inelegant in ASDF:
;;;     - they rely on eval,
;;;     - ASDF tries to remove a method from a generic function of a different name.
;;;     Due to non-standard behavior of remove-method in LW 4.4, system redefinition
;;;     intrusively signals about this.
;;;
;;;  5. Referring to features in component definition is more useful than in
;;;     dependency rules.
;;;
;;;  :) Despite adherence to the object-oriented representation of operations, the
;;;     source code exhibits "non-generic" approach to naming slot readers and accessors.
;;;     For example:
;;;     - component-parent vs. operation-parent
;;;     - component-version vs. missing-version
;;;     - module-components vs. circular-dependency-components

;;; CHANGES AND ADDITIONS
;;;  * Changed syntax of dependency to more consistent:
;;;    (dep-op {component-name | (component-name . plist)}+),
;;;    where plist can contain the :version and :features properties.
;;;
;;;    Other properties are passed as the operation methods arguments
;;;    (and to make-sub-operation in the compatibility mode).
;;;
;;;  * Component slots in-order-to and do-first were replaced by caused-by 
;;;    and requires correspondingly; the old initargs :in-order-to and 
;;;    :do-first are also retained.
;;;
;;;  * Dependencies are calculated by the two generic functions:
;;;    * operation-caused-by (former component-depends-on),
;;;    + operation-requires (added).
;;;
;;;  + The default list of "requires" dependencies usually involves cross-operation
;;;    rules and is now initialized from a component type by virtue of of generic:
;;;    + depends-on-requires (added).
;;;
;;;  * Turned into generic the following ordinary functions:
;;;    - coerce-name.
;;;
;;;  * Turned into ordinary the following generic functions:
;;;    - version-satisfies.
;;;
;;;  - Removed generics:
;;;    - component-self-dependencies (in fact replaced with dependencies-on-component),
;;;    - traverse (replaced by collect-plan)
;;;
;;;  * Added structure class action.
;;;    Action is a minimal planning and performing unit, which stores the
;;;    operation status and timestamp.
;;;
;;;  * Component slots
;;;    properties
;;;	  Turned into plist instead of alist; the generic function component-property
;;;	  accepts the third optional parameter default.
;;;       Generics component-property and (setf component-property) are turned
;;;       into ordinary functions.
;;;    features
;;;       Added, can be either a keyword or a feature expression (on LispWorks only).
;;;       The component (and all its children) is only considered during planning
;;;       when the feature expression is true. When it is false, every operation on
;;;       the component is treated by the planner as done and does not trigger any
;;;       caused-by target actions.
;;;    actions
;;;       Added, a list of unified actions - no duplicates according to operation-eq.
;;;    operation-times
;;;       Removed in favor of actions.
;;;
;;;  * Added component-output-pathname generic.
;;;    It allows target directory specification, e.g. :output-pathname "/my-project/bin/"
;;;
;;;  * Added :initform nil form to many slots.
;;;
;;;  + Added structure class action with planned status and timestamp slots;
;;;    Added the component slot actions keeping unique actions.
;;;    Introduced helpers get-timestamp and set-timestamp.
;;;
;;;  + Introduced dynamic-file, a component subclass for cl-source-file and the like.
;;;
;;;  * The value of *verbose-out* can be either T or a stream.
;;;
;;;  * Renamed
;;;    - class formatted-system-definition-error to system-definition-simple-error,
;;;    - some readers of condition classes slots,
;;;    - some helpers replaced by the similar borrowed from Ystok-Library.
;;;
;;;  - Removed
;;;    - :weakly-depends-on option,
;;;    - component inline methods,
;;;    - all calls of the eval function,
;;;    - standard-asdf-method-combination,
;;;    - format strings ~<> as delivering them with LispWorks requires keeping
;;;      the pretty-printer.

;;; CHANGE LOG
;;; Version 1.2
;;;  + The version option of defsystem is now evaluated.
;;; Version 1.1
;;;  + Added function component-featurep.
;;;  * Changed error message printed by #<method print-object (wrong-dependency T)>.

(in-package :cl-user)

;; Uncomment these lines if you are used to ASDF operation classes and names
;(eval-when (:compile-toplevel :load-toplevel)
;  (pushnew :asdf-compat *features*))

(defpackage :asdlite
 (:nicknames :asd #+asdf-compat :asdf)
 (:use :common-lisp)
 #+lispworks
 (:import-from :system
  sys:directory-pathname)
 (:export
  #:*central-registry* 		        ; variables only in :#+asdf-compat mode
  #:*compile-file-warnings-behaviour*
  #:*compile-file-failure-behaviour*
  #:*verbose-out*

  #:defsystem
  #:ensure-system
  #:find-system
  #:operate #:oos 

  #:component
  #:component-featurep
  #:component-name
  #:component-parent
  #:component-pathname
  #:component-property
  #:component-properties
  #:component-relative-pathname
  #:component-system
  #:component-version
  #:component-output-pathname
  #:find-component
  #:output-pathname			; slot name
  #:output-pathname-of-type		; helper
  #:source-file-type

  #:module
  #:module-components

  #:system
  #:system-author
  #:system-definition-pathname
  #:system-description
  #:system-license
  #:system-long-description
  #:system-maintainer
  #:system-source-file
					; component subclasses
  #:cl-source-file 
  #:dynamic-file
  #:source-file
  #:static-file
  ;#:c-source-file #:java-source-file #:doc-file #:html-file #:text-file
  #:depends-on-requires
					; operations
  #:input-files
  #:operation-caused-by
  #:operation-done-p 
  #:operation-on-failure #:operation-on-warnings
  #:operation-requires
  #:output-files
  #:perform
  #+asdf-compat #:feature		; pseudo-op, deprecated in favor of :features
  #+asdf-compat #:operation
  #+asdf-compat #:compile-op
  #+asdf-compat #:load-op
  #+asdf-compat #:load-source-op 
  #+asdf-compat #:test-op
  #+asdf-compat #:explain
				        ; errors
  #:circular-dependency
  #:compile-error #:compile-failed #:compile-warned
  #:duplicate-names
  #:error-component #:error-operation
  #:missing-component
  #:missing-component-of-version
  #:missing-dependency
  #:missing-dependency-of-version
  #:wrong-dependency
  #:operation-error
  #:system-definition-error
					; restarts
  #:try-recompiling
  #:retry
  #:accept
					; convenience function
  #:current-location))

(in-package :asdlite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  SPECIALS  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *default-component-class* 'cl-source-file)

;; Specifies
;; 1) where asdf-message prints: stream, T (means *standard-output*) or NIL;
;; 2) the value of the :verbose argument for compile-file and load.
(defvar *verbose-out* nil)

(defparameter *compile-file-warnings-behaviour* :warn)
(defparameter *compile-file-failure-behaviour* #+sbcl :error #-sbcl :warn)

(defvar *defined-systems* (make-hash-table :test 'equal))

;; List of directory pathnames
;; Calling eval on symbols was removed even from the compatibility mode.
(defvar *central-registry* ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  MACROS  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simplified versions from ylib/macros, functions, lw-compat.lisp, and file-utils

(defmacro if-bind ((var form) form1 form2)
  `(let ((,var ,form))
     (if ,var ,form1 ,form2)))

(defmacro when-bind ((var form) &body body)
  `(let ((,var ,form))
     (when ,var 
       ,@body)))

(declaim (inline cdr-assoq first-or-self))

(defun cdr-assoq (arg alist)
  (cdr (assoc arg alist :test #'eq)))

(defun first-or-self (arg)
  (if (consp arg) (first arg) arg))

(defun remove-properties (plist keywords)
  (if (get-properties plist keywords)
      (loop for rest on plist by #'cddr
            unless (member (first rest) keywords :test #'eq)
            collect (first rest) and collect (second rest))
      plist))

(defun split-string (delimiter seq)
  (declare (type character delimiter) (type string seq))
  (loop with length of-type fixnum = (length seq)
        for left of-type fixnum = 0 then (+ right 1)
        for right of-type fixnum = (or (position delimiter seq :start left) length)
        when (< left right) collect (subseq seq left right)
        until (<= length right)))

(defun current-location (&optional relative-path)
 ;;; Directory where the source file is located or another dir relative to the former
  (let ((pathname (or *compile-file-truename* *load-truename* (user-homedir-pathname))))
    (make-pathname :name nil :type nil :version nil
                   :defaults (if relative-path
                                 (merge-pathnames relative-path pathname)
                                 pathname))))

#-lispworks
(defun directory-pathname (arg)
 ;;; cl-fad:pathname-as-directory
  ;; Converts the non-wild pathname designator PATH to directory form.
  (let ((pathname (pathname arg)))
    (flet ((%component-present-p (value) (and value (not (eq value :unspecific)))))
      (if (or (%component-present-p (pathname-name pathname))
              (%component-present-p (pathname-type pathname)))
          (make-pathname :directory (append (or (pathname-directory pathname)
                                                (list :relative))
                                            (list (file-namestring pathname)))
                         :name nil
                         :type nil
                         :defaults pathname)
          pathname))))					; already directory-pathname-p

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  CONDITIONS  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-condition system-definition-error (error) ()
  #+cmu (:report print-object))

(define-condition system-definition-simple-error (simple-error system-definition-error)
  ())

(defun sysdef-error (format &rest arguments)
  (error 'system-definition-simple-error
         :format-control format :format-arguments arguments))

(defun sysdef-error-component (msg type name value)
  (sysdef-error (concatenate 'string msg "~&The value specified for ~(~A~) ~A is ~W")
                type name value))


(define-condition circular-dependency (system-definition-error)
  ((components :initarg :components :reader components)))

(define-condition duplicate-names (system-definition-error)
  ((name :initarg :name :reader name)))

(define-condition missing-component (system-definition-error)
  ((requires :initform "(unnamed)" :reader requires :initarg :requires)
   (parent :initform nil :reader parent :initarg :parent)))

(defmethod print-object ((condition missing-component) stream)
   (format stream "Component or feature ~S not found~@[ in ~A~]"
           (requires condition)
           (when-bind (parent (parent condition))
             (component-name parent))))

(define-condition missing-component-of-version (missing-component)
  ((version :initform nil :reader version :initarg :version)))

(defmethod print-object ((condition missing-component-of-version) stream)
  (format stream "Component ~S does not match version ~A~@[ in ~A~]"
           (requires condition) (version condition)
	   (when-bind (parent (parent condition))
	     (component-name parent))))

(define-condition missing-dependency (missing-component)
  ((target :initarg :target :reader target)))

(defmethod print-object ((condition missing-dependency) stream)
  (format stream "~A, required by ~A"
          (call-next-method condition nil) (target condition)))

(define-condition missing-dependency-of-version (missing-dependency
						 missing-component-of-version)
  ())

(define-condition wrong-dependency (system-definition-error)
  ((target :initarg :target :reader target)
   (requires :reader requires :initarg :requires)))

(defmethod print-object ((condition wrong-dependency) stream)
  (format stream "Within the rules of ~A, wrong dependency ~A
Dependee must be one of:~@
 - {name},
 - ({name} :version {version}),
 - ({name} :features {feature})."
          (target condition) (requires condition)))

(define-condition operation-error (error)
  ((component :reader error-component :initarg :component)
   (operation :reader error-operation :initarg :operation))
  (:report (lambda (condition stream)
             (format stream "Error while invoking ~A on ~A"
                     (error-operation condition) (error-component condition)))))

(define-condition compile-error (operation-error) ())
(define-condition compile-failed (compile-error) ())
(define-condition compile-warned (compile-error) ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  GENERICS  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun asdf-message (format-string &rest format-args)
  (declare (dynamic-extent format-args))
  (when *verbose-out*
    (when-bind (stream (if (streamp *verbose-out*) *verbose-out* *standard-output*))
      (fresh-line stream)
      (apply #'format stream format-string format-args))))

(defgeneric coerce-name (name)
 (:method ((name string))
  (string name))
 (:method ((name symbol))
  (string-downcase (symbol-name name)))
 (:method (name)
  (sysdef-error "Invalid component designator ~A" name)))

;; Default file type of the component within the system.
(defgeneric source-file-type (component system))

;; Extracts the pathname applicable for a particular component.
(defgeneric component-pathname (component))

;; Returns a pathname for the component argument intended to be
;; interpreted relative to the pathname of that component's parent.
;; Despite the function's name, the return value may be an absolute
;; pathname, because an absolute pathname may be interpreted relative to
;; another pathname in a degenerate way.
(defgeneric component-relative-pathname (component))

;; Target file(s) specification for component
;; For a module or system, returns a directory pathname, e.g. #P"/my-project/bin/"
(defgeneric component-output-pathname (component))
 ;(:method ((self null)) nil)

(defun output-pathname-of-type (component &optional (type nil supplied-p))
 ;;; Helper composing output pathname of the type specified.
  ;; Args: component Instance of a leaf component class (non-module).
  ;;       type      If null, use the same type as the source pathname is of;
  ;;                 uppercased for logical-pathname!
  ;; NB: source-file-type is not applicable here as it provides a default.
  (merge-pathnames
   (or (and (slot-exists-p component 'output-pathname)	; relative or absolute
            (slot-value component 'output-pathname))
       (merge-pathnames
        (component-name component)			; coerce name to pathname directly
        (make-pathname :type (if supplied-p		; but default type by relative
                                 type
                                 (pathname-type (component-relative-pathname
                                                 component))))))
   (or (component-output-pathname (component-parent component))
       *default-pathname-defaults*)))

(defun version-satisfies (component version)
  (let ((component-version (component-version component)))
    (if (and version component-version)
        (let ((x (mapcar #'parse-integer (split-string #\. component-version)))
              (y (mapcar #'parse-integer (split-string #\. version))))
          (labels ((%bigger (x y)
                     (cond ((not y) t)
                           ((not x) nil)
                           ((> (car x) (car y)) t)
                           ((= (car x) (car y)) (%bigger (cdr x) (cdr y))))))
            (and (= (car x) (car y))
                 (or (not (cdr y)) (%bigger (cdr x) (cdr y))))))
        t)))

;; Finds the component identified by PATH within base MODULE.
;; Args: module If null, we assume to seeking for a system.
;; TODO: Define method on (module vector) and use vectors inside rules.
;; ASDF Compatibility:
;;   On the contrary to asdf:find-component, ASDlite searches in case-insensitive manner
(defgeneric find-component (module path))

(defgeneric perform (operation component)
 (:method (operation component)
  (sysdef-error "The method PERFORM is not specialized for operation ~S on component ~A"
                (operation-type operation) component)))

(defgeneric output-files (operation component))
(defgeneric input-files (operation component))
(defgeneric operation-done-p (operation component))

;;; Functions producing effective lists of antecendens, i.e. right-hand sides of rules,
;;; required or causing for the component to perform the operation.
;;; An antecedent has one of the two following forms:
;;;
;;; ({operation} {dependee}+)
;;;   Means that the target depends on {operation} having been performed on each {dependee}
;;;   Here
;;;    operation is one of:
;;;    - keyword,
;;;    - symbol designating an operation subclass,
;;;    - instance of some operation subclass.
;;;    dependee is one of:
;;;    - {component-instance}
;;;    - ({component-instance} . {property-list})
;;;      where special properties are
;;;      -- :version {version}
;;;      -- :features {feature}),
;;;    The latter form is different from ASDF's.
;;;
;;; (:FEATURES {feature})
;;;   Means that the target heavily depends on {feature} presence in *FEATURES*.
;;;   When the feature is missing, an error is signaled.
;;;
;;; The {feature} is either a keyword or feature expression (only on LispWorks).
;;;
;;; Methods on subclasses should usually append their results to CALL-NEXT-METHOD.
;;; Q: Use :method-combination append?

(defgeneric operation-caused-by (operation component))
(defgeneric operation-requires (operation component))

(defgeneric depends-on-requires (component-or-type depends-on)
 ;;; As cross-operation dependencies are rather domain-specific,
  ;; we compute default "requires" rules basing on the component type.
  ;; Args: depends-on List of names and/or instances of required components.
 (:method (c depends-on)
  (declare (ignore c depends-on))
  ()))

;;; Helpers for filtering rules

(defun component-dependee-match-p (component dependee)
  (eq component (first-or-self dependee)))

(defun dependencies-on-component (component antecedents)
  (remove component antecedents		; ((op name1 ...) ...)
          :test-not (lambda (c antecedent)
                      (member c (rest antecedent) :test #'component-dependee-match-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  COMPONENT  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; name
;;;   stored as a string composed of portable pathname characters;
;;;   when a symbol is passed as a designator, the symbol name is taken and lowercased.
;;; relative-pathname
;;;   There is no direct accessor for source pathname, we do this as a method to allow
;;;   it to compute it default in funky ways if not supplied.
;;;   The :pathname initarg is always provided to reinitialize-instance
;;;   in parse-component-form
;;; TODO: Should we provide some atomic interface for updating the component-properties?

(defclass component ()
 ((name        :initarg :name        :accessor component-name  :type string)
  (version     :initarg :version     :accessor component-version     :initform nil)
  (parent      :initarg :parent      :reader   component-parent      :initform nil)
  (properties  :initarg :properties  :accessor component-properties  :initform nil)
  (features    :initarg :features    :accessor component-features    :initform nil)
  (relative-pathname :initarg :pathname :initform nil)
  (caused-by   :accessor caused-by  :initform ())		; synonym to in-order-to
  (requires    :accessor requires   :initform ())		; synonym to do-first
  (actions     :accessor actions    :initform ())))		; pull of actions

(defmethod print-object ((c component) stream)
  (print-unreadable-object (c stream :type t :identity nil)
    (format stream "~A~@[ v.~A~]" (component-name c) (component-version c))))

(defmethod coerce-name ((c component))
  (component-name c))

(defun component-parent-pathname (component)
  (if-bind (parent (component-parent component))
    (component-pathname parent)
    *default-pathname-defaults*))

(defmethod component-pathname ((component component))
  (merge-pathnames (component-relative-pathname component)
                   (component-parent-pathname component)))

(defmethod component-output-pathname ((component component))
  (output-pathname-of-type component))

(defgeneric component-system (component)
 ;;; Find the top-level system containing COMPONENT
 (:method ((component component))
  (if-bind (parent (component-parent component))
    (component-system parent)
    component)))

(defun component-featurep (component)
  (let ((features (component-features component)))
    (or (not features)
        #-lispworks (member features *features* :test #'eq)
        #+lispworks (sys:featurep features))))

#-asdf-compat
(defun component-property (component property &optional default)
  (getf (component-properties component) property default))
#-asdf-compat
(defun (setf component-property) (new-value component property &optional default)
  (declare (ignorable default))
  (setf (getf (component-properties component) property) new-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  MODULE  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; - When "." is specified as the :pathname or :output-pathname argument,
;;;   the components of the module are retrieved from or compiled into the
;;;   input or output folder of the module parent.
;;; - An operation on a module is invoked recursively on its components.

(defclass module (component)
  ((components :accessor module-components :initarg :components :initform nil)
   ;; What to do if we can't satisfy a dependency of one of this module's components.
   ;; This allows a limited form of conditional processing
   (if-component-dep-fails :accessor module-if-component-dep-fails
                           :initarg :if-component-dep-fails
                           :initform :fail)
   ;; default-component-class of a parent it taken by default
   (default-component-class :accessor module-default-component-class
                            :initarg :default-component-class
                            :initform *default-component-class*)
   ;; No standard reader - component-output-pathname is for that
   (output-pathname :initarg :output-pathname :initform nil)))

(defmethod component-relative-pathname ((m module))
  (if-bind (pathname (slot-value m 'relative-pathname))		; already tranlated?
    (directory-pathname pathname)
    (make-pathname :directory `(:relative ,(component-name m))
                   :host (pathname-host (component-parent-pathname m)))))

(defmethod component-output-pathname ((m module))
  (merge-pathnames
   (if-bind (pathname (slot-value m 'output-pathname))		; relative or absolute
     (directory-pathname pathname)
     (make-pathname :directory `(:relative ,(component-name m))))
   (or (component-output-pathname (component-parent m))
       *default-pathname-defaults*)))

(defmethod find-component ((module module) name)
  (find (coerce-name name) (module-components module)
        :test #'string-equal :key #'component-name))		; case insensitive

(defmethod find-component ((module module) (path cons))
 ;;; Args: path A result of uri:uri-parsed-path, relative by default.
  ;;		If absolute, the retrive from the root system, not from the module.
  ;; Values: component  if found
  ;;	  or (1) nil (2) last descendant found (3) rest of the path
  (do ((rest (case (first path)
               (:absolute (setq module (component-system module))
                          (rest path))
               (:relative (rest path))
               (otherwise path))
             (rest rest)))
      ((null rest)
       module)
    (let ((name (first rest)))
      (if-bind (component (cond ((or (eq name :up) (eq name :back) (string= name ".."))
                                 (component-parent module))
                                ((string= name ".")
                                 module)
                                (t (find-component module name))))
        (setq module component)
        (return (values nil module rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  SYSTEM  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass system (module)
  ((description      :reader system-description :initarg :description :initform nil)
   (long-description :reader system-long-description :initarg :long-description
                     :initform nil)
   (author           :reader system-author     :initarg :author     :initform nil)
   (maintainer       :reader system-maintainer :initarg :maintainer :initform nil)
   (licence          :reader system-license    :initarg :licence    :initform nil)))

(defmethod component-output-pathname ((system system))
  (or (slot-value system 'output-pathname)
      (slot-value system 'relative-pathname)
      *default-pathname-defaults*))

(defgeneric system-source-file (system)
  (:documentation "Return the source file in which system is defined.")
  (:method (system-name)
   (system-source-file (find-system system-name)))
  (:method ((system system))
   (when-bind (pathname (and (slot-value system 'relative-pathname)
                             (make-pathname :name (component-name system)
                                            :type "asd"
                                         :defaults (component-relative-pathname system))))
     (probe-file pathname))) )

(defun system-definition-pathname (system)
  (let ((name (coerce-name system)))
    (or (loop for directory in *central-registry*	; sysdef-central-registry-search
              for pathname = (make-pathname :name name :type "asd" :version :newest
                                            :case :local
                                            :defaults directory)
              when (and pathname (probe-file pathname))
              do (return pathname))
        (when-bind (pair (system-registered-p name))
          (system-source-file (cdr pair))))))

(defun find-system (name &optional (error-p t))
  (let* ((name (coerce-name name))
         (in-memory (system-registered-p name))
         (on-disk (system-definition-pathname name)))
    (when (and on-disk
               (or (not in-memory)
                   (< (car in-memory) (file-write-date on-disk))))
      (asdf-message "Loading system definition from ~A into ~A" on-disk *package*)
      (load on-disk))
    (let ((in-memory (system-registered-p name)))
      (cond (in-memory
             (when on-disk
               (setf (car in-memory) (file-write-date on-disk)))
             (cdr in-memory))
            (error-p
             (error 'missing-component :requires name))))))

(defmethod find-component ((parent null) name)
  (declare (ignore parent))
  (find-system name nil))		; a component without parent is a system

(defun register-system (system)
  #+debug (check-type system system)
  (let ((name (component-name system)))
    #+debug (check-type name string)
    (asdf-message "Registering ~A as ~A" system name)
    (unless (eq (cdr (gethash name *defined-systems*)) system)
      (setf (gethash name *defined-systems*) (cons (get-universal-time) system)))))

(defun system-registered-p (name)
  (gethash (coerce-name name) *defined-systems*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  COMPONENT SUBCLASSES  ;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Class dynamic-file is a super class for all "processed" components.

(defclass source-file (component)
  ((type :accessor source-file-explicit-type :initarg :type :initform nil)))

(defmethod source-file-type ((component source-file) (m module))
  (declare (ignore m))
  (source-file-explicit-type component))

(defmethod component-relative-pathname ((component source-file))
  (if-bind (relative-pathname (slot-value component 'relative-pathname))
    (merge-pathnames relative-pathname
                     (make-pathname :type (source-file-type component
                                                            (component-system component))))
    (make-pathname :name (component-name component)
                   :type (source-file-type component (component-system component))
                   :defaults (component-parent-pathname component))))

(defclass static-file (source-file) ())		; never compiled nor loaded

(defclass dynamic-file (source-file) ())	; can be complied and/or loaded(-source)

(defclass cl-source-file (dynamic-file)
 ((type :initform "lisp")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  OPERATIONS  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Abstract treatment both keywords, lists, and instances as operations.
;;; STUB: For now, assume operation-designator equality test to be equal.
;;;       (generally not correct as depends on the order of properties)
;;; Conversion: designator -> operation is two-fold:
;;;  first-or-self  - if designator can only be instance.
;;;  make-operation - if designator can be a type.

(defun make-operation (designator &optional args)
 ;;; What is passed as the first argument to various operation functions
  #-asdf-compat (declare (ignore args))
  (cond ((consp designator)
         (first designator))
        #+asdf-compat
        ((and (symbolp designator) (not (keywordp designator)))
         (apply #'make-instance designator :original-initargs args args))
        (t designator)))

#+unused
(defun operation-designator (operation &optional args)
  (cond ((keywordp operation)
         (if args (cons operation args) operation))
        ((consp operation)
         (if args			; or replace?
             (cons (first operation) (append args (rest operation)))
             operation))
        (t operation)))

(defun operation-type (designator)
  (cond ((symbolp designator) designator)
        ((consp designator) (first designator))
        (t (type-of designator))))

(defun operation-eq (x y)
  (eq (operation-type x) (operation-type y)))

(defmethod operation-caused-by ((o symbol) (c component))
  (if (keywordp o)
      (cdr-assoq o (caused-by c))
      (operation-caused-by (make-instance o) c)))

(defmethod operation-requires ((o symbol) (c component))
  (if (keywordp o)
      (cdr-assoq o (requires c))
      (operation-requires (make-instance o) c)))

;;; Collect only dependencies on c itself (but maybe on different operations)
;(defmethod component-self-dependencies ((o operation) (c component))
;  (dependencies-on-component c (component-depends-on o c)))

(defmethod input-files (o (c component))
 ;;; Collects all output files of the causing operations on the component c itself.
  (if-bind (deps (dependencies-on-component c (operation-caused-by o c)))
    (let ((parent (component-parent c)))
      (mapcan (lambda (antecedent)
                (let ((dep-o (make-operation (first antecedent))))
                  (mapcan (lambda (dependee &aux (dep-c (first-or-self dependee)))
                            (output-files dep-o (if (typep dep-c 'component)
                                                    dep-c
                                                    (find-component parent dep-c))))
                          (rest antecedent))))
              deps))
    ;; No triggering required operation - c seems an original source file
    (list (component-pathname c))))

(defmethod output-files (o (c component))
  (declare (ignore o c))
  ())

(defmethod input-files (o (m module))
  (declare (ignore o m))
  ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  ACTION  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Plan steps _UNIFIED_ within the actions slot of a the related component:
;;; an operation can be mentioned there only once (tested with operation-eq).

(defstruct action
  operation		; operation keyword or instance
  component		; component instance
  properties		; operation keyword arguments (passed to perform in future)
  planned		; planning status: NIL, :start, :done, or T
  timestamp)		; perform status: NIL or universal-time (or what else?)

(defmethod print-object ((a action) stream)
  (print-unreadable-object (a stream :type nil :identity t)
    (format stream "~S ~S~@[ time ~S~]~@[ plan ~S~] ~:S"
            (action-operation a) (action-component a)
            (action-timestamp a) (action-planned a) (action-properties a))))

(defun find-action (operation-designator component)
  (first (member operation-designator (actions component)
                 :key #'action-operation :test #'operation-eq)))

(defun ensure-action (operation-designator component &key timestamp properties)
  (let ((action (find-action operation-designator component))
        (properties (or properties
                        (setq properties (and (consp operation-designator)
                                              (rest operation-designator))))))
    (if action
         (progn
  	   ;; Update the slot with operation if it is an instance.
           (unless (or (symbolp operation-designator)
                       (eq (action-operation action) operation-designator))
             (setf (action-operation action) (first-or-self operation-designator)))
           (when properties
             (setf (action-properties action) properties))
           (when timestamp
             (setf (action-timestamp action) timestamp)))
         (push (setq action (make-action :component component
                                         :operation (first-or-self operation-designator)
                                         :timestamp timestamp :properties properties))
               (actions component)))
    action))

(defun get-timestamp (operation component)
  (when-bind (action (find-action operation component))
    (action-timestamp action)))

(defun set-timestamp (operation component &optional (timestamp (get-universal-time)))
  (ensure-action operation component :timestamp timestamp))

(defun safe-file-write-date (pathname)
  ;; If FILE-WRITE-DATE returns NIL, it's possible that the user or some other agent
  ;; has deleted an input file. Also, generated files will not exist at the time
  ;; planning is done and calls operation-done-p which calls safe-file-write-date.
  ;; Value: 0 if the file-write-date fails, so we survive and continue planning 
  ;;        as if the file were very old.
  (or (and pathname (probe-file pathname) (ignore-errors (file-write-date pathname)))
      (progn (when pathname
               (warn "Missing FILE-WRITE-DATE for ~S, treating it as zero." pathname))
        0)))

(defmethod operation-done-p (o (c component))
  (let ((output-files (output-files o c))
        (input-files (input-files o c)))
    (flet ((earliest-out () (reduce #'min (mapcar #'safe-file-write-date output-files)))
           (latest-in () (reduce #'max (mapcar #'safe-file-write-date input-files))))
      (if input-files
          (if output-files
              ;; An operation with both input and output files is
              ;; - assumed as computing the latter from the former,
              ;; - assumed to have been done if the latter are all older than the former.
              ;; We use <= instead of < to play nice with generated files.
              ;; This opens a race condition if an input file is changed
              ;; after the output is created but within the same second
              ;; of filesystem time; but the same race condition exists
              ;; whenever the computation from input to output takes more than 
              ;; one second of filesystem time (or just crosses the second).
              ;; So that's cool.
              (and (every #'truename input-files)
                   (every #'probe-file output-files)
                   (<= (latest-in) (earliest-out)))
              ;; An operation without output-files is probably meant
              ;; for its side-effects in the current image, assumed to be idem-potent,
              ;; e.g. :LOAD or :LOAD-SOURCE of some CL-SOURCE-FILE.
              (if-bind (time (get-timestamp o c))
                (<= (latest-in) time)
                nil))
          (if output-files
              ;; An operation without input-files but with output-files
              ;; is probably meant for its side-effects on the file-system,
              ;; assumed to have to be done everytime.
              nil
              ;; An operation that uses nothing to produce nothing is assumed done.
              ;; E.g. modules: operations have no immediate action,
              ;; but are only meaningful through traversing dependencies.
              t)))))

(defmethod perform :after (o (c component))
  (set-timestamp o c))

(defmethod perform (o (m module))
  (declare (ignore o m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  PLANNING  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-sub-operation (target-o target-c dep-od dep-c properties plist)
 ;;; A la make-operation
  ;; Args: target-o   Operation keyword, type or instance.
  ;;	   dep-od     Required operation designator returned by a caused-by/requires.
  ;;	   target-c, dep-c
  ;;		      Instances of component subclasses.
  ;;	   properties Target operation arguments.
  ;;       plist      Key arguments coming from the rule dependee.
  ;; Values 1) Dependee operation.
  ;;        2) Plist - dependee operation arguments, combined from:
  ;;		(dependee plist) (dep-o props) (target-o properties)
  ;; NB: Target operation properties are only taken if both the operations are eq.
  #-asdf-compat (declare (ignore target-c dep-c))
  (cond ((keywordp dep-od)
         (values dep-od (if (eq target-o dep-od) (append plist properties) plist)))
        ((consp dep-od)
         (let ((dep-o (first dep-od)))
           (values dep-od (append plist (rest dep-od)
                                  (if (eq target-o dep-o) properties) ()))))
        #+asdf-compat
        ((typep dep-od 'standard-object)			; operation instance
         (values dep-od plist))					; already - use as is
        #+asdf-compat
        (t
         (let ((args (operation-original-initargs target-o)))
           (cond ((and (null (component-parent target-c))	; both are systems
                       (null (component-parent dep-c))		; and distinct
                       (not (eq target-c dep-c)))
                  (when (eq (getf args :force) t)		; do not pass :force
                    (setq args (remove-properties args '(:force))))  ; to subsystem
                  (apply #'make-instance dep-od :parent target-o :original-initargs args
                         (append plist args)))
                 ((and (typep target-o dep-od) (null plist))
                  target-o)					; reuse target
                 (t
                  (apply #'make-instance dep-od :parent target-o :original-initargs args
                         (append plist args))))))))

(defun collect-plan (operation system &key properties force)
 ;;; Traverse the depedency graph in depth-first manner.
  ;; Args: properties
  ;;              The target opertation arguments.
  ;;       force  One of:
  ;;	     T     - rebuild everything,
  ;;         :self - enforce the operation on the given top-level system only,
  ;;         list of system names - enforce on the top-level and the subsystems mentioned.
  ;; Value: List of action instances.
  ;; NB1: The partial order consists of the following relations:
  ;;	   caused-by - explicit,
  ;;	   requires - explicit,
  ;;	   (o child) < (o parent)	    - implicit caused-by for all operation types o.
  ;;	   (o parent :before t) < (o child) - implicit requires for all operation types o,
  ;; NB2: As we exploit the effective topological-sort algorithm instead of full-fledged:
  ;;      - dependency on a child component of a different parent potentially leads
  ;;        to unpredictable results.
  (let ((actions-on-systems ()))			; registry of actions on systems
    (labels ((%clear-planned (c)
               ;; Turn off the planned status of all actions
               (dolist (action (actions c))
                 (setf (action-planned action) nil))
               (when (typep c 'module)
                 (mapc #'%clear-planned (module-components c))))
             (%visit-dep (target-o target-c dep-od dep-c &optional properties plist)
               ;; Collects a partial plan of performing
               ;; - dep-o with properties as arguments,
               ;; - on the component instance dep-c, which must be of :version property
               ;; Args: properties Target operation arguments
               ;;       plist      Dependee operation properties specified for dep-c.
               (loop
                (restart-case
                    (let* ((parent (component-parent target-c))
                           (c (if (typep dep-c 'component)		; canonicalized
                                  dep-c
                                  (find-component parent dep-c)))	; lazy reqires
                           (version (getf plist :version)))
                      (if c
                          (if (version-satisfies c version)
                              (multiple-value-bind (o properties)
                                  (make-sub-operation target-o target-c dep-od c
                                                      properties
                                                      (remove-properties
                                                       plist '(:version)))
                                (return (if (typep c 'system)
                                            (%visit-system o c properties)
                                            (%visit o c properties))))
                              (error 'missing-dependency-of-version
                                     :parent parent :target target-c :requires dep-c
                                     :version version))
                          (error 'missing-dependency
                                 :parent parent :target target-c :requires dep-c)))
                  (retry ()
		   :report (lambda (stream)
                             (format stream "Retry seeking component ~S." dep-c))
                   :test (lambda (condition)
                           (and (typep condition 'missing-dependency)
                                (equalp (requires condition) dep-c)))))))
             (%visit-deps (target-o target-c dep-od deps &optional properties)
               ;; Args: target-o Operation
               ;;	dep-od	 Required operation designator
               ;;       deps     List of dependee designators - names or sublists,
               ;;                i.e. (rest antecedent)
               ;; Value: T if already planned or
               ;;	 list of actions orderded as follows:
               ;;	 - on operation-caused-by,
               ;;	 - on operation-requires,
               ;;	 - on children,
               ;;	 - action (o c) on itself.
               (if (or (eq dep-od :features) #+asdf-compat (eq dep-od 'feature))
                   ;; The feature pseudo-operation considered obligatory. not optonal
                   (if #-lispworks (member (first deps) *features*)
                       #+lispworks (sys:featurep (first deps))
                       t					; only status planned
                       (error 'missing-dependency :target target-c :requires (first deps)))
                   (let ((plan ())
	                 ;; Status is set to true as soon as some dep is already planned
                         (planned nil))
                     (dolist (dependee deps)
                       (cond ((typep dependee 'component)
                              (let ((p (%visit-dep target-o target-c dep-od dependee
                                                   properties)))
                                #1=(cond ((consp p) (setq plan (nconc p plan)))
                                         (p (setq planned p)))))
                             ((and (consp dependee) (typep (first dependee) 'component))
                              (let* ((plist (rest dependee))
                                     (features (getf (rest dependee) :features)))
                                (when (or (not features)
                                         #-lispworks (member features *features*)
                                         #+lispworks (sys:featurep features))
                                  (let ((p (%visit-dep target-o target-c
                                                       dep-od (first dependee)
                                                       properties
                                                       (remove-properties plist
                                                                          '(:features)))))
                                    #1#))))
                             (t
                              (error 'wrong-dependency
                                     :target target-c :requires dependee))))
                     (or plan planned))))
             (%visit (target-o target-c &optional properties)
               ;; Args: properties Target operation arguments
               ;; Values: Plan (non-empty list) or planned status (NIL or T)
               (unless (component-featurep target-c)
                   (return-from %visit nil))
               (let ((action (ensure-action target-o target-c :properties properties)))
                 (case (action-planned action)
                   ((t)					; already traversed and planned
                    t)
                   (:done				; already traversed but operation
                    nil)				; was reported done - don't plan
                   (:start
                    (error 'circular-dependency :components (list target-c)))
                   (otherwise
                    (setf (action-planned action) :start)
                    (let ((status :done))		; final planned status := skipped
                      (unwind-protect
                          (let ((dep-plan ())
                                (dep-planned nil)	; status of caused-by
                                (children-plan ())
                                (children-planned nil))	; status of children
                            ;; Caused-by dependencies
                            (loop for (dep-od . deps)
                                  in (operation-caused-by target-o target-c)
                                  for p = (%visit-deps target-o target-c dep-od deps)
                                  do (cond ((consp p) (setq dep-plan (nconc p dep-plan)))
                                           (p (setq dep-planned p))))
                            ;; Components - traverse each for the same operation
                            (when (typep target-c 'module)
                              (let ((error nil))
                                (dolist (child (module-components target-c))
                                  (handler-case
                                      (let ((p (%visit target-o child properties)))
                                        (cond ((consp p) (setq children-plan
                                                               (nconc p children-plan)))
                                              (p (setq children-planned p))))
                                   (missing-dependency (condition)
                                    (if (eq (module-if-component-dep-fails target-c) :fail)
                                        (error condition)
                                        (setq error condition)))))
                                ;; Resignal only if none of the children has succeeded
                                (when (and error
                                           (not (or children-plan children-planned))
                                           (eq (module-if-component-dep-fails target-c)
                                               :try-next))
                                  (error error))))
                            ;; If some caused-by dependency or child produced a plan
                            ;;    or they have been already planned,
                            ;;    or the operation is reportedly done,
                            ;; then append a plan for the requires dependencies
                            ;;      and push the action on the component itself.
                            (when (or dep-plan dep-planned
                                      children-plan children-planned
                                      (cond ((eq force t))
                                            ((eq force :self)
                                             (eq (component-system target-c) system))
                                            ((consp force)	; list systems to force
                                             (let ((s (component-system target-c)))
                                               (or (eq s system)
                                                   (member (component-name s) force
                                                           :test #'string-equal
                                                           :key #'coerce-name)))))
                                      (not (operation-done-p target-o target-c)))
                              ;; Required dependencies
                              (loop for (dep-od . deps)
                                    in (operation-requires target-o target-c)
                                    for p = (%visit-deps target-o target-c dep-od deps)
                                    do (when (consp p)
                                         (setq dep-plan (nconc p dep-plan))))
                              (setq status t)
                              (cons action (nconc 
                                            (when (consp children-plan) children-plan)
                                            ;; It is too late to push :berore operation
                                            ;; if some child has been planned earlier
                                            ;; due to dependencies!
                                          #|(when (and (typep target-c 'module)
                                                       (module-before-operation target-o)
                                                       (not children-planned))
                                              (list (make-action :component target-c
                                                                 :operation target-o
                                                                 :plist '(:before t))))|#
                                            (when (consp dep-plan) dep-plan))) ))
                        ;; Protect marking as finished
                        (setf (action-planned action) status)))))))
             (%visit-system (target-o s &optional properties)
               ;; Place the same action instance both into actions-on-systems
               ;; and the actions slot of the system s
               (if-bind (action (loop for a in actions-on-systems
                                     when (and (operation-eq (action-operation a)
                                                             target-o)
                                               (eq (action-component a) s))
                                     do (return a)))
                 (case (action-planned action)
                   (:start (error 'circular-dependency :components (list s)))
                   ((t)	t)				; successfully traversed
                   (:done nil))				; reported or already done
                 (progn (unless (member s actions-on-systems
                                        :key #'action-component :test #'eq)
	                  ;; This is the first visit to system at all
                          (%clear-planned s))
                   (setq action (ensure-action target-o s :properties properties))
                   (push action actions-on-systems)
                   (%visit target-o s properties))))
             )
     (let ((plan (%visit-system operation system properties)))
       (if (consp plan) (nreverse plan) nil)))))

(defun perform-plan (plan &optional args)
 ;;; Each operation is wrapped in with-compilation-unit.
  ;; For error handling code, use perform-with-restarts.
  (with-compilation-unit ()
    (dolist (a plan)
      (let ((o (action-operation a))
            (c (action-component a)))
        (when (and (symbolp o) (not (keywordp o)))
          (setq o (make-operation o (append (action-properties a) args))))
        (loop
         (restart-case (progn (perform o c)  ;(apply #'perform o c (action-properties a))
                         (return)) 		;(perform-with-restarts)
           (retry ()
                  :report (lambda (stream)
                            (format stream "Retry performing ~S on ~S." o c)))
           (accept ()
                   :report (lambda (stream)
                             (format stream "Continue as if ~S on ~S were successful."
                                     o c))
                   (setf (action-timestamp a) (get-universal-time))
                   (return))))))))

(defun operate (operation-designator system-designator &rest args
                &key (verbose t) force version &allow-other-keys)
  ;; 1. Create an instance of operation-designator using any keyword parameters
  ;;    as initargs.
  ;; 2. Ensure an asdf-system instance specified by system-designator
  ;;    (possibly loading it from disk).
  ;;    If the version is supplied, then also ensures that the system  match it
  ;; 3. Generate plan - list of actions.
  ;; 4. Perform the plan
  ;; NB: Dependencies may cause the operation to invoke other
  ;;     operations on the system or its components: the new operations will be
  ;;     created with the same initargs as the original one.
  (let* ((operation (make-operation operation-designator args))
         (*verbose-out* verbose)
         (system (etypecase system-designator
                   (component system-designator)
                   ((or string symbol) (find-system system-designator)))))
    (unless (version-satisfies system version)
      (error 'missing-component-of-version :requires system :version version))
    (let* ((properties (remove-properties args '(:verbose :force :version)))
           (plan (collect-plan operation system :properties properties :force force)))
      (perform-plan plan properties)
      (values operation (length plan)))))

;; Abbreviation for _operate on system_ and an alias for the `operate` function.
(setf (fdefinition 'oos) (fdefinition 'operate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;  OPERATION CLASSES  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; COMPILE

(defgeneric operation-on-warnings (operation)
 (:method ((o (eql :compile)))
  (declare (ignore o))
  *compile-file-warnings-behaviour*))

(defgeneric operation-on-failure (operation)
 (:method ((o (eql :compile)))
  (declare (ignore o))
  *compile-file-failure-behaviour*))

(defun %compile-cl-source-file (o c)
  (let ((source-file (component-pathname c))
        (output-file (car (output-files o c))))
    (multiple-value-bind (output warnings-p failure-p)
        (compile-file source-file :output-file output-file :verbose *verbose-out*)
      (when warnings-p
        (case (operation-on-warnings o)
          (:warn (warn "COMPILE-FILE warned while performing ~A on ~A." o c))
          (:error (error 'compile-warned :component c :operation o))
          (:ignore nil)))
      (when failure-p
        (case (operation-on-failure o)
          (:warn (warn "COMPILE-FILE failed while performing ~A on ~A." o c))
          (:error (error 'compile-failed :component c :operation o))
          (:ignore nil)))
      (unless output
        (error 'compile-error :component c :operation o)))))

(defmethod perform :before ((o (eql :compile)) (c source-file))
  (mapc #'ensure-directories-exist (output-files o c)))

(defmethod output-files ((o (eql :compile)) (c cl-source-file))
  (declare (ignore o))
  (list (compile-file-pathname (component-output-pathname c))))

(defmethod perform ((o (eql :compile)) (c cl-source-file))
  (%compile-cl-source-file o c))

;;; LOAD

(defmethod operation-caused-by ((o (eql :load)) (c component))
  (declare (ignorable o)) 
  (cons (list :compile c) (call-next-method)))		; load heavily depends on compile

;(defmethod perform ((o (eql :load)) (c static-file))
;  (declare (ignore o c)))
;(defmethod operation-done-p ((o (eql :load)) (c static-file))
;  (declare (ignore o c))
;  t)

(defmethod input-files ((o (eql :load)) (c cl-source-file))
  (list (compile-file-pathname (component-output-pathname c))))

(defmethod perform ((o (eql :load)) (c cl-source-file))
  (dolist (pathname (input-files o c))
    (load pathname :verbose *verbose-out*)))

;;; LOAD-SOURCE

(defmethod perform ((o (eql :load-source)) (c static-file))
  (declare (ignore o c)))

(defmethod perform ((o (eql :load-source)) (c cl-source-file))
  (declare (ignore o))
  (load (component-pathname c) :verbose *verbose-out*))	; signals if does not exist

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  DEFSYSTEM  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun class-for-type (parent type)
  (let ((extra-symbols (list (find-symbol (symbol-name type) *package*)
                             (find-symbol (symbol-name type)(load-time-value *package*)))))
                                                              ;(package-name :asdf)))))
    (or (dolist (symbol (if (keywordp type) extra-symbols (cons type extra-symbols)))
          (when (and symbol
                     (find-class symbol nil)
                     (subtypep symbol 'component))
            (return (find-class symbol))))
        (and (eq type :file)
             (or (module-default-component-class parent)
                 (find-class *default-component-class*)))
        (sysdef-error "Unrecognized component type ~A" type))))

(defun canonicalize-rules (system &optional (slot-names '(caused-by requires)))
 ;;; Merge several antecedents on the same operation into one by megring dependees
  ;; Resolve component names replacing them by the component instances.
  ;; Operations are compared as designators!
  (labels ((%do-rules (target-c slot-name)
             (when-bind (rules (slot-value target-c slot-name))
               (setf (slot-value target-c slot-name)
                     (loop
                      with parent = (component-parent target-c)
                      for target-o in (remove-duplicates (mapcar #'first rules)
                                                         :test #'equal)
                      collect
                      (cons target-o
                       (loop with antecedents = (reduce		; mappend
                                                 #'append
                                                 (mapcar #'rest
                                                         (remove target-o rules
                                                                 :key #'first
                                                                 :test-not #'equal)))
                             for dep-o in (remove-duplicates (mapcar #'first antecedents)
                                                             :test #'equal)
                             collect
                             (cons dep-o
                              (loop with acc = ()
                                    for dependee in (reduce	; mappend
                                                     #'append
                                                     (mapcar #'rest
                                                             (remove dep-o antecedents
                                                                     :key #'first
                                                                     :test-not #'equal)))
                                    for component = (if (eq dep-o :features)
                                                        dependee
                                                        (find-component
                                                         parent (first-or-self dependee)))
                                    do (cond (component
                                              (pushnew (if (consp dependee)
                                                           (cons component (rest dependee))
                                                           component)
                                                       acc
                                                       :test #'equal))
                                             ((null parent)
		                              ;; Weak dependency - system definition
                                              ;; required but may be loaded later
                                              (pushnew dependee acc :test #'equal))
                                             (t
                                               (error 'missing-dependency
                                                      :parent parent :target target-o
                                                      :requires dependee)))
                                    finally (return (nreverse acc))))))))))
           (%do-component (c)
             (dolist (slot-name slot-names)
               (%do-rules c slot-name))
             (when (typep c 'module)
               (mapc #'%do-component (module-components c)))) )
    (%do-component system)))

(defmethod depends-on-requires ((type symbol) depends-on)
  (cond ((subtypep type 'cl-source-file)		; c-source-file
         `((:compile (:load ,@depends-on))
           #+asdf-compat (compile-op (load-op ,@depends-on))))))

(defmethod depends-on-requires ((c component) depends-on)
  (depends-on-requires (type-of c) depends-on))

(defmethod depends-on-requires ((m module) depends-on)
  (depends-on-requires (module-default-component-class m) depends-on))

;; Stores the name of a previous sibling component
(defvar %serial-depends-on% nil)

(defun parse-component-form (parent options)
 ;;; Args: pathname   Can be a logical pathname
  ;;       components List of component forms
  ;;       depends-on Explicit name list of caused-by components, for which
  ;;		      compile-op and load-op rules are generated automatically.
  ;;                  Useless for other operations.
  ;;       in-order-to, do-first
  ;;		      Compatibility synonyms for caused-by and requires.
  ;; CAUTION: Underscore '_' is treated differently from the "usual" pathname.
  ;;          It is not allowed in the name part of a logical pathname!
  ;; NB: We always reuse an existing objects when rereading the defsystem;
  ;;     reinitialize-instance is called even on existing components.
  ;;     Please, specialize it instead of initialize-instance!
  (destructuring-bind (type name &rest rest
                       &key pathname output-pathname
                            components default-component-class
                            depends-on serial
                            caused-by requires in-order-to do-first
                       &allow-other-keys) options
    ;; A partial test of the values of a component.
    (unless (listp components)
      (sysdef-error-component ":components must be a list of component forms."
                              type name components))
    (unless (listp depends-on)
      (sysdef-error-component ":depends-on must be a list of sibling component names."
                              type name depends-on))
    (unless (listp (or caused-by (setq caused-by in-order-to)))
      (sysdef-error-component ":caused-by/:in-order-to must be a list of rules."
                              type name (or caused-by in-order-to)))
    (unless (listp (or requires (setq requires do-first)))
      (sysdef-error-component ":requires/:do-first must be a list of rules."
                              type name (or requires do-first)))
    ;; Reuse old or create a new instance
    (let ((ret (find-component parent name)))
      (cond ((null ret)
             (setq ret (make-instance (class-for-type parent type))))
            ((and parent (not (typep ret (class-for-type parent type))))
             (error 'duplicate-names :name name)))
      ;; BAD: depends-on can contain a mixture of names and component instances
      (when %serial-depends-on%				 ; push previous sibling to tail
        (setq depends-on (append depends-on (list %serial-depends-on%))))
      (apply #'reinitialize-instance ret
             :name (coerce-name name)
             :parent parent
             :pathname (if (typep pathname 'logical-pathname)
                           (translate-logical-pathname pathname)
                           pathname)
             (remove-properties rest '(:pathname :components
                                       ;:perform :explain :output-files :operation-done-p
                                       :depends-on :serial
                                       :caused-by :requires :in-order-to :do-first)))
      (when (typep ret 'module)
        (when (typep output-pathname 'logical-pathname)
          (setf (slot-value ret 'output-pathname) (translate-logical-pathname
                                                   output-pathname)))
        (when (and (not default-component-class)		; not specifed explicitly
                   (typep parent 'module))
          (setf (module-default-component-class ret)
                (module-default-component-class parent)))
        (let ((%serial-depends-on% nil))		; recursively parse components
          (setf (module-components ret)
                (loop for form in components
                      for c = (parse-component-form ret form)
                      collect c
                      when serial do (setq %serial-depends-on% (component-name c)))))
        ;; Check for duplicate component names
        (let ((name-hash (make-hash-table :test #'equalp)))	; case-insensitively!
          (loop for c in (module-components ret)
                for name = (component-name c)
                do (if (gethash name name-hash)
                       (error 'duplicate-names :name name)
                       (setf (gethash name name-hash) t)))))
      ;; Append default rules for caused-by and requires.
      ;; Cross-operation requires rules should depend on component type!
      (setf (caused-by ret) (append caused-by
                                    (when depends-on
                                      `((:compile (:compile ,@depends-on))
                                        (:load (:load ,@depends-on))
                          #+asdf-compat (compile-op (compile-op ,@depends-on))
                          #+asdf-compat (load-op (load-op ,@depends-on)))))
            (requires ret) (append requires
                                   (when depends-on
                                     (depends-on-requires ret depends-on))))
      ret)))

(defun resolve-symlinks (path)
  #-allegro (truename path)
  #+allegro (if (typep path 'logical-pathname)
                path
                (excl:pathname-resolve-symbolic-links path)))

(defun ensure-system (name class &rest options)
 ;;; System must be registered before we parse the body,
  ;; otherwise (find-component nil name) fails.
  (let* ((name (coerce-name name))
         (registered (system-registered-p name))
         (system (cdr (or registered
                          (register-system (make-instance class :name name))))))
    (when registered
      (setf (car registered) (get-universal-time))
      ;(mapc 'load-system defsystem-depends-on)
      ;; We change-class (when necessary) AFTER we load the defsystem-dep's
      ;; since the class might not be defined as part of those.
      (unless (eq (type-of system) class)
        (change-class system class)))
    (parse-component-form nil (list* :module name options))
    (canonicalize-rules system)
    system))

(defmacro defsystem (name &body options
                          &key (class 'system)
                               (pathname nil supplied-p) output-pathnam
                               version
                          &allow-other-keys)
 ;;; Args: options  Not evaluated except for pathname, output-pathname, and version.
  ;; Compatibility note:
  ;;	asdf:defsystem (1.131) only evaluates the top-level :pathname option,
  ;;	but neither of the other options nor :pathname for components!
  ;(destructuring-bind (&key (class 'system) (pathname nil supplied-p) output-pathname
  ;                     &allow-other-keys) options
  `(apply 'ensure-system ',name ',class
          :pathname ,(if supplied-p			; stored in relative-pathname
                         pathname			; evaluated
                         `(if *load-truename*		; pathname-location
                              (make-pathname :name nil :type nil
                                             :defaults (resolve-symlinks *load-truename*))
                              *default-pathname-defaults*))
          :output-pathname ,output-pathname		; evaluated
          :version ,version				; evaluated
          ',(remove-properties options			; other options are not evaluated
                               '(:class :pathname :output-pathname :version))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  ASDF Compatibility  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+asdf-compat
(defgeneric component-property (component property &optional default))
#+asdf-compat
(defmethod component-property ((c component) property &optional default)
  (getf (component-properties c) property default))

#+asdf-compat
(defgeneric (setf component-property) (new-value component property &optional default))
#+asdf-compat
(defmethod (setf component-property) (new-value (c component) property &optional default)
  (declare (ignorable default))
  (setf (getf (component-properties c) property) new-value))

#+asdf-compat
(defclass operation ()
  ((forced :initform nil :initarg :force :accessor operation-forced)
   (original-initargs :initform nil :initarg :original-initargs
                      :accessor operation-original-initargs)
   (parent :initform nil :initarg :parent :accessor operation-parent)))

#+asdf-compat
(defmethod print-object ((o operation) stream)
  (print-unreadable-object (o stream :type t :identity t)
    (ignore-errors (format stream "~:S" (operation-original-initargs o)))))

#+asdf-compat
(defmethod shared-initialize :after ((operation operation) slot-names
                                     &key &allow-other-keys)
  (declare (ignore slot-names)))		; disable initarg validity checking

#+asdf-compat
(defmethod operation-caused-by ((o operation) (c component))
  (cdr-assoq (type-of o) (caused-by c)))

#+asdf-compat
(defmethod operation-requires ((o operation) (c component))
  (cdr-assoq (type-of o) (requires c)))

#+asdf-compat
(defclass compile-op (operation)
 (;(proclamations :initarg :proclamations :accessor compile-op-proclamations :initform nil)
  (on-warnings :initarg :on-warnings :accessor operation-on-warnings
               :initform *compile-file-warnings-behaviour*)
  (on-failure :initarg :on-failure :accessor operation-on-failure
              :initform *compile-file-failure-behaviour*)))

#+asdf-compat
(defmethod perform :before ((o compile-op) (c source-file))
  (mapc #'ensure-directories-exist (output-files o c)))

#+asdf-compat
(defmethod output-files ((o compile-op) (c cl-source-file))
  (declare (ignore o))
  (list (compile-file-pathname (component-output-pathname c))))

#+asdf-compat
(defmethod perform ((o compile-op) (c cl-source-file))
  (%compile-cl-source-file o c))

#+asdf-compat
(defclass basic-load-op (operation) ())

#+asdf-compat
(defclass load-op (basic-load-op) ())

#+asdf-compat
(defmethod operation-caused-by ((o load-op) (c component))
  (declare (ignorable o)) 
  (cons (list 'compile-op c) (call-next-method)))  ;(component-name c)

#+asdf-compat
(defmethod perform ((o load-op) (c static-file))
  (declare (ignore o c)))

#+asdf-compat
(defmethod operation-done-p ((o load-op) (c static-file))
  (declare (ignore o c))
  t)

#+asdf-compat
(defmethod input-files ((o load-op) (c cl-source-file))
  (list (compile-file-pathname (component-output-pathname c))))

#+asdf-compat
(defmethod perform ((o load-op) (c cl-source-file))
  (dolist (pathname (input-files o c))
    (load pathname :verbose *verbose-out*)))

#+asdf-compat
(defclass load-source-op (basic-load-op) ())

#+asdf-compat
(defmethod perform ((o load-source-op) (c static-file))
  (declare (ignore o c)))

#+asdf-compat
(defmethod perform ((o load-source-op) (c cl-source-file))
  (declare (ignore o))
  (load (component-pathname c) :verbose *verbose-out*))	; signals if does not exist


#|;;; FIXME: we simply copy load-op's dependencies.  this is Just Not Right.
(defmethod operation-caused-by ((o load-source-op) (c component))
  (mapcar (lambda (antecedent) (if (eq (first antecedent) 'load-op)
                                   (cons 'load-source-op (rest antecedent))
                                   antecedent))
          (cdr-assoq 'load-op (component-caused-by c))))

;;; Why does not the default method fit?
(defmethod operation-done-p ((o load-source-op) (c source-file))
  (if-bind (last-loaded-as-source (component-property c 'last-loaded-as-source))
    (< (file-write-date (component-pathname c)) last-loaded-as-source)
    nil))

(defmethod perform ((o load-source-op) (c cl-source-file))
  (when (load (component-pathname c))
    (setf (component-property c 'last-loaded-as-source) (get-universal-time))))|#

#+asdf-compat
(defclass test-op (operation) ())
#+asdf-compat
(defmethod operation-done-p ((o test-op) (c system))
  "Testing a system is _never_ done."
  (declare (ignore o c))
  nil)
#+asdf-compat
(defmethod perform ((o test-op) (c component))
  (declare (ignore o c))
  nil)

#+asdf-compat
(defgeneric explain (operation component)
 (:method (o (c component))
  (asdf-message "~A on ~A" o c)))

(pushnew :asdlite *features*)


#||;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; EVALUATION ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(compile-file *load-pathname*
              :output-file (make-pathname
                            :name #+(and (not asdf-compat) (not debug))	"asdlite"
                                  #+(and (not asdf-compat) debug)	"asdlite-debug"
                                  #+asdf-compat				"asdf-compat"
                            :defaults (make-pathname :name nil :type nil
                                                     :defaults *load-pathname*)))

(lw:removef *features* :asdf-compat)

;;; Other ASDF classes and methods: interesting but unused

(defclass c-source-file (dynamic-file) ())
 ((type :initform "c")))

(defclass java-source-file (dynamic-file) ())
 ((type :initform "java")))

(defclass doc-file (static-file) ())
(defclass html-file (doc-file)
 ((type :initform "html")))

(defmethod perform-with-restarts ((o compile-op) (c dynamic-file))
  (let ((state :initial))
    (loop until (or (eq state :success) (eq state :failure))
	  do (case state
               (:recompiled
                (setf state :failure)
                (call-next-method)
                (setf state :success))
               (:failed-compile
                (setf state :recompiled)
                (perform-with-restarts o c))
               (t
                (with-simple-restart (try-recompiling "Try recompiling ~a"
                                                      (component-name c))
                  (setf state :failed-compile)
                  (call-next-method)
                  (setf state :success)))))))

(defmethod perform-with-restarts ((o load-op) (c source-file))
  (let ((state :initial))
    (loop until (or (eq state :success) (eq state :failure))
          do (case state
               (:recompiled
                (setf state :failure)
                (call-next-method)
                (setf state :success))
               (:failed-load
                (setf state :recompiled)
                (perform (make-sub-operation c o c 'compile-op) c))
               (t
                (with-simple-restart
                    (try-recompiling "Recompile ~a and try loading it again"
                                     (component-name c))
                  (setf state :failed-load)
                  (call-next-method)
                  (setf state :success)))))))

;;; Optional extras

(defun run-shell-command (control-string &rest args)
  "Interpolate ARGS into CONTROL-STRING as if by FORMAT, and
synchronously execute the result using a Bourne-compatible shell, with
output to *VERBOSE-OUT*.  Returns the shell's exit code."
  (let ((command (apply #'format nil control-string args)))
    (format *verbose-out* "; $ ~A~%" command)
    #+sbcl
    (sb-ext:process-exit-code
     (sb-ext:run-program
      #+win32 "sh" #-win32 "/bin/sh"
      (list  "-c" command)
      #+win32 #+win32 :search t
      :input nil :output *verbose-out*))

    #+(or cmu scl)
    (ext:process-exit-code (ext:run-program "/bin/sh" (list  "-c" command)
                                            :input nil :output *verbose-out*))
    #+allegro
    (excl:run-shell-command command :input nil :output *verbose-out*)

    #+lispworks
    (system:call-system-showing-output command
           :shell-type "/bin/sh" :output-stream *verbose-out*)

    #+clisp					; XXX not exactly *verbose-out*, I know
    (ext:run-shell-command  command :output :terminal :wait t)

    #+openmcl
    (nth-value 1 (ccl:external-process-status
                  (ccl:run-program "/bin/sh" (list "-c" command)
                                   :input nil :output *verbose-out* :wait t)))
    #+ecl					; courtesy of Juan Jose Garcia Ripoll
    (si:system command)
    #-(or openmcl clisp lispworks allegro scl cmu sbcl ecl)
    (error "RUN-SHELL-PROGRAM not implemented for this Lisp")))

#+old
(defun union-dependencies (&rest args)
  (let ((tree nil))			; alist :: (op . antecedents)
    (flet ((%maybe-add-tree (dependent-op required-op dependee)
            ;; Add the node C at /OP1/OP2 in TREE, unless it's there already.
            ;; Returns the new tree (which probably shares structure with the old one)
            (if-bind (rule (assoc dependent-op tree :test #'eq))
              (let* ((alist (rest rule))
                     (antecedent (assoc required-op alist :test #'eq)))
                (if antecedent
                    ;; BAD: dependee can be either a string or component instance!
                    (pushnew dependee (rest antecedent))
                    (setf (rest rule) (acons required-op (list dependee) alist))))
              (setq tree (acons dependent-op (list (list required-op dependee)) tree)))))
      (dolist (rules args)		; each rules is rule list
        (dolist (rule rules)		; rule ::= (op (require-op name1 ...))
          (dolist (antecedent (rest rule))
            (dolist (dependee (rest antecedent))
              (%maybe-add-tree (car rule) (car antecedent) dependee))))))
    tree))
||#
