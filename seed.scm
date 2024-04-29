;; This file was part of SINK, a Scheme-based Interpreter for
;; Not-quite Kernel. Reworked under the name SEED.
;;
;; Copyright (c) 2009 John N. Shutt
;; Copyright (c) 2022 Amirouche A. BOUBEKKI
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU Library General Public License
;; as published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; Library General Public License for more details.
;;
;; You should have received a copy of the GNU Library General Public
;; License along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.  This
;; file is part of SINK, a Scheme-based Interpreter for Not-quite
;; Kernel
(library (seed)
  (export seed-exec)
  (import (chezscheme))


  (define any? (lambda args #t))   

  ;;
  ;; Evaluate an expression in an environment, with given youngest enclosing
  ;; context.  The normal result of evaluation is returned;; contexts are only
  ;; used for extraordinary purposes, i.e., Kernel abnormal passing of values
  ;; or Kernel keyed dynamic bindings, so most theoretical Kernel contexts don't
  ;; actually have to be constructed.
  ;;

  (define kernel-eval
    (lambda (exp env context)
      (cond ((kernel-pair? exp)  (combine (kernel-eval (kernel-car exp) env context)
                                          (kernel-cdr exp)
                                          env
                                          context))
            ((symbol? exp)  (lookup exp env context))
            (else exp))))

  ;;
  ;; Evaluate a combination in an environment,
  ;; with given youngest enclosing context.
  ;;

  (define combine
    (lambda (combiner operand-tree env context)
      (cond ((operative? combiner)
             (operate combiner operand-tree env context))
            ((applicative? combiner)
             (combine (unwrap combiner)
                      (map-eval operand-tree env context combiner)
                      env
                      context))
            (else
             (error-pass (make-error-descriptor
                          (list "Tried to call a non-combiner: "
                                (list combiner)))
                         context)))))

  ;;
  ;; Given improper kernel-list ls and nonnegative integer k, returns the (k)th
  ;; kernel-cdr of ls.  Thus, if k=0, returns ls.
  ;;
  (define kernel-list-tail
    (lambda (ls k)
      (if (> k 0)
          (kernel-list-tail (kernel-cdr ls) (- k 1))
          ls)))

  ;;
  ;; Given mutable kernel-list ls, nonnegative integer a, and nonnegative integer
  ;; c, where the number of kernel-pairs in ls is at least a+c, if c is zero does
  ;; nothing, otherwise sets the kernel-cdr of the (a+c)th kernel-pair of ls to
  ;; point to the (a+1)th kernel-pair of ls.  After mutation, ls has acyclic
  ;; prefix length a and cycle length c.
  ;;
  (define kernel-encycle!
    (lambda (ls a c)
      (if (> c 0)
          (kernel-set-cdr! (kernel-list-tail ls (+ a c -1))
                           (kernel-list-tail ls a)))))
  ;;
  ;; Given a value to be construed as an improper kernel-list, returns a list
  ;; of the following four statistics about the value:
  ;;
  ;;   p = the number of kernel-pairs in the improper list.
  ;;   n = the number of nils in the improper list
  ;;         (1 if proper and finite, else 0).
  ;;   a = the number of kernel-pairs in the acyclic prefix of the improper list.
  ;;   c = the number of kernel-pairs in the cycle of the improper list
  ;;         (0 if not a cyclic list).
  ;;
  ;; The algorithm here is linear-time, requiring two passes through the improper
  ;; list, of which the first pass may traverse the improper list for up to twice
  ;; its length, and the second pass traverses it for its length.
  ;;  (1) In the first pass, aux, we determine either that the list is acyclic,
  ;; or the length of its cycle;; to detect a cycle, each kernel-pair at position n
  ;; in the list is compared for eq?-ness to the kernel-pair at the most recent
  ;; power-of-two index.  Each kernel-pair is compared to only one other, and we
  ;; can't overshoot the beginning of the cycle by more than a factor of two, so
  ;; this pass takes time linear in the number of kernel-pairs.  If there's no
  ;; cycle, we're done.
  ;;  (2) A second pass, aux2, determines where the cycle begins, by comparing
  ;; each kernel-pair starting from the beginning of the list to the kernel-pair
  ;; displaced to its right by exactly the cycle length (which we know, from the
  ;; first pass).
  ;;
  ;; An alternative algorithm would be to use encapsulated integer marks on
  ;; kernel-pairs;; one would then require two passes of just the length of the
  ;; improper list.  That algorithm would have to be in file
  ;; "subfiles/kernel-pair.scm", since it would use private information about
  ;; kernel-pair.  However, even if one did that, it would save less than fifty
  ;; percent in traversal length, and the traversal steps could be significantly
  ;; more expensive since they would involve modifying the encapsulated mark
  ;; fields.  That's not even getting in to questions of reentrance and
  ;; parallelization.
  ;;
  (define get-list-metrics
    (lambda (x)

      ;; find the cycle length
      (define aux
        (lambda (current-x ;; the item we're going to look at now
                 current-n ;; the number of kernel-pairs we've already passed
                 old-x     ;; an earlier kernel-pair to compare with this item
                 old-n     ;; the number of kernel-pairs preceding old-x
                 next-n)   ;; when to replace old-x
          (cond ((not (kernel-pair? current-x))
                 (list current-n (if (null? current-x) 1 0)
                       current-n 0))
                ((eq? current-x old-x)
                 (aux2 (- current-n old-n)))
                ((< current-n next-n)
                 (aux (kernel-cdr current-x) (+ 1 current-n)
                      old-x                  old-n
                      next-n))
                (else
                 (aux (kernel-cdr current-x) (+ 1 current-n)
                      current-x              current-n
                      (* 2 current-n))))))

      ;; find the acyclic prefix length
      (define aux2
        (lambda (cycle-length)
          (let ((acyclic-prefix-length
                 (aux3 x (kernel-list-tail x cycle-length) 0)))
            (list (+ acyclic-prefix-length cycle-length)
                  0
                  acyclic-prefix-length
                  cycle-length))))

      ;; find the acyclic prefix length
      (define aux3
        (lambda (x y n)
          (if (eq? x y)
              n
              (aux3 (kernel-cdr x) (kernel-cdr y) (+ 1 n)))))

      (if (kernel-pair? x)
          (aux (kernel-cdr x) 1 x 0 8)
          (list 0 (if (null? x) 1 0) 0 0))))

  ;;
  ;; Given a cons-like procedure some-cons, returns a procedure that,
  ;; given integer n-pairs, procedure proc, and kernel-list ls, where the length
  ;; of ls is at least n-pairs, calls proc on each of the first n-pairs elements
  ;; of ls, and returns a finite some-list of the results.
  ;;
  ;; This higher-order procedure captures the common structure of
  ;; bounded-simple-map, which returns a finite mutable kernel-list, and
  ;; bounded-simple-map->list, which returns a list.
  ;;
  (define make-bounded-simple-map
    (lambda (some-cons)
      (letrec ((mapper  (lambda (n-pairs proc ls)
                          (if (> n-pairs 0)
                              (some-cons (proc (kernel-car ls))
                                         (mapper (- n-pairs 1)
                                                 proc
                                                 (kernel-cdr ls)))
                              '()))))
        mapper)))

  ;;
  ;; Given procedure proc and kernel-list ls, calls proc on each element of ls
  ;; (just once for each eq?-distinct position in ls), and returns
  ;; a mutable kernel-list of the results structurally isomorphic to ls.
  ;;
  ;; For example, using curly braces for a kernel-list,
  ;;
  ;;       (simple-map (lambda (x) (+ x 5)) {1 2 #0={3 4 . #0#}})
  ;;   ==>
  ;;       {6 7 #0={8 9 . #0#}}
  ;;
  (define simple-map
    (lambda (proc ls)
      (define bounded-simple-map       (make-bounded-simple-map kernel-cons))
      (let* ((metrics  (get-list-metrics ls))
             (p  (car metrics))
             (a  (caddr metrics))
             (c  (cadddr metrics)))
        (if (<= p 0)
            '()
            (let ((ls  (bounded-simple-map p proc ls)))
              (kernel-encycle! ls a c)
              ls)))))

  ;;
  ;; Evaluate a list of expressions, and return a list of the results, with given
  ;; youngest enclosing context;; given also the applicative for which the list is
  ;; being provided, just in case it's needed for an error message.
  ;;

  (define map-eval
    (lambda (operand-tree env context applicative)
      (if (not (kernel-list? operand-tree))
          (error-pass
           (make-error-descriptor
            (list "Operand tree not a list, passed to "
                  (describe-object applicative)))
           context)
          (simple-map
           (lambda (operand) (kernel-eval operand env context))
           operand-tree))))

  ;;
  ;; Although this file contains the top-level interpreter, it isn't the top-level
  ;; file;; it is just one of the files loaded by "sink.scm".
  ;;
  ;; The interpreter is a read-eval-print loop run on a child of the ground
  ;; environment.  The top-level context always returns to the point where the
  ;; interpreter ordered its construction, causing the inner let to rebind its
  ;; symbol "context" and re-run its body, (if (context? context) ...).
  ;;

  (define interpreter
    (lambda (ground-environment)
      (let ((env (make-standard-environment ground-environment)))
        (suggest-object-name env 'the-global-environment)
        (let ((context  (make-top-level-context report-error)))
          (if (context? context)
              (begin
                (initialize-context-bindings ground-environment context)
                (rep-loop env context))
              'SINK-terminated)))))

  ;;
  ;; The read-eval-print loop, parameterized by the global environment and the
  ;; top-level context.
  ;;

  (define rep-loop
    (lambda (env context)
      (display ">> ")
      (let ((exp  (kernel-read (get-kernel-current-input-port context)
                               context)))
        (newline)
        (if (eof-object? exp)
            (terminal-pass '() context))
        (kernel-write (kernel-eval exp env context)
                      (get-kernel-current-output-port context)
                      context)
        (newline)
        (newline)
        (rep-loop env context))))

  ;;
  ;; Reports an error, based on a descriptor argument.
  ;;
  ;; Ideally, the argument would always be an error-descriptor (cf. file
  ;; "subfiles/error.scm");; but then, ideally there would be no need for an error
  ;; handler.  If the argument isn't an error-descriptor, that fact is reported
  ;; along with the argument.
  ;;

  (define report-error
    (lambda (x)
      (if (error-descriptor? x)
          (describe-error x)
          (begin
            (display " ;; error, general handler given non-descriptor object:")
            (newline)
            (display " ;; ")
            (display-tree x (current-output-port))
            (newline)))
      (newline)))

  ;;
  ;; Given zero or more boolean arguments, returns their conjunction (i.e.,
  ;; returns #t unless at least one of them is false).
  ;;

  (define and?
    (lambda ls
      (or (null? ls)
          (and (car ls)
               (apply and? (cdr ls))))))

  ;;
  ;; Creates bindings for handling booleans in a given environment.
  ;;

  (define bind-boolean-primitives!
    (lambda (env)
      (add-bindings! env

        'boolean?
        (unary-predicate->applicative boolean?)

        ;; 'and?
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (apply and? (kernel-list->list operand-tree)))
        ;;   0 -1 boolean?)

        '$if
        (action->checked-operative
         (lambda (operand-tree env context)
           (let ((test  (kernel-eval (kernel-car operand-tree) env context)))
             (if (boolean? test)
                 (if test
                     (kernel-eval (kernel-cadr operand-tree) env context)
                     (kernel-eval (kernel-caddr operand-tree) env context))
                 (error-pass
                  (make-error-descriptor
                   "Non-boolean test result, when calling #[operative $if]")
                  context))))
         3 3)

        )))

  ;;
  ;; Encapsulated objects in the interpreted language are represented by
  ;; procedures.  The representing procedure takes a symbol as argument, and
  ;; returns one of several fields.  Internally, it's a dispatch procedure.
  ;;
  ;; The point of the exercise is to achieve guaranteed encapsulation of these
  ;; objects *in the interpreted language*.  The interpreter source code is
  ;; supposed to follow stylistic rules, which can be checked because the
  ;; interpreter source code is finite, and it is then technically impossible
  ;; for a Kernel program to violate the encapsulation of the objects.  The
  ;; essential point is that a Kernel program cannot directly require that
  ;; a procedure be called (procedure being a type in the Scheme meta-language,
  ;; not in the interpreted Kernel language), and therefore the Kernel program
  ;; is limited in its manipulations of encapsulated objects to those specific
  ;; manipulations for which Kernel tools are provided.
  ;;
  ;; Every object has two fields, 'type and 'name.
  ;;   'type is a symbol that names the object's type.
  ;;   'name is a list, whose car is either #f, meaning the object is unnameable;;
  ;; or #t, meaning the object can be named but hasn't been yet;; or a symbol or
  ;; string, which is then the object's name.  The cdr of the list is initially
  ;; nil, but could later be altered via designate-origin, which see.
  ;;
  ;;
  ;; For example, here's how one would idiomatically set up an object type 'foo
  ;; that is nameable and has attributes 'bar and 'quux.
  ;;
  ;;     (define make-foo
  ;;       (lambda (bar quux)
  ;;         (let ((name  (list #t)))
  ;;           (lambda (message)
  ;;             (case message
  ;;               ((type) 'foo)
  ;;               ((name) name)
  ;;               ((bar)  bar)
  ;;               ((quux) quux))))))
  ;;
  ;;     (define foo? (make-object-type-predicate 'foo))
  ;;
  ;; Sufficient accessors should be provided that clients never have to know that
  ;; encapsulated objects are dispatch procedures;; for example, if clients should
  ;; have the ability to access the 'bar and 'quux attributes of a foo,
  ;;
  ;;     (define get-foo-bar  (lambda (x) (x 'bar)))
  ;;     (define get-foo-quux (lambda (x) (x 'quux)))
  ;;

  ;;
  ;; Determines whether all its arguments are objects.
  ;;

  (define object? procedure?)

  ;;
  ;; Given some number of symbol arguments, constructs a predicate that takes
  ;; an argument and determines whether it is an object whose type is amongst
  ;; the given symbols.
  ;;

  (define make-object-type-predicate
    (lambda types
      (lambda (object)
        (and (object? object)
             (pair? (member (object 'type) types))))))

  ;;
  ;; If given object can be named but hasn't been yet, names it, and if the
  ;; object's name record is linked to others, suggets the name to them, too.
  ;;
  ;; If the second argument is an object, the name of that object is used.
  ;; If (after that substitution, if any) the second argument is a boolean,
  ;; no action is taken.
  ;;

  (define suggest-object-name
    (lambda (object name)
      (let ((name  (if (object? name) (car (name 'name)) name)))
        (if (not (boolean? name))
            (letrec ((aux  (lambda (ls)
                             (if (and (pair? ls) (boolean? (car ls)))
                                 (begin
                                   (if (eq? (car ls) #t)
                                       (set-car! ls name))
                                   (aux (cdr ls)))))))
              (aux (object 'name)))))))

  ;;
  ;; Designates a particular other object to which this object should suggest its
  ;; name (if it ever acquires one).  The designation is singular and permanent,
  ;; and should be another object that is in some sense the foundation for this
  ;; object, such as the underlying combiner of an applicative.  (If there weren't
  ;; already such a foundational relationship, the designation would prevent the
  ;; other object from being garbage collected before this one.)  It often happens
  ;; that the predecessor object is created just to found its successor, and is
  ;; never directly bound by a symbol, so that this facility becomes the most
  ;; likely way for the predecessor to receive a relevant name.
  ;;

  (define designate-name-inheritor!
    (lambda (object heir)
      (let ((oname  (object 'name))
            (hname  (heir 'name)))
        (if (null? (cdr oname))
            (begin
              (suggest-object-name heir (car oname))
              (set-cdr! oname hname))))))

  ;;
  ;; Generates a string describing given object.  Not for use on a kernel-pair.
  ;;

  (define describe-object
    (lambda (object)
      (let ((type  (symbol->string (object 'type)))
            (name  (car (object 'name))))
        (cond ((eq? name #f)  (string-append "#" type))
              ((string? name) (string-append "#[" type " " name "]"))
              ((symbol? name) (string-append "#[" type " " (symbol->string name)
                                             "]"))
              (else           (string-append "#[" type "]"))))))

  ;;
  ;; An applicative has type 'applicative, and attribute 'underlying whose value
  ;; is a combiner.
  ;;   The principal constructor is called "wrap" instead of "make-applicative",
  ;; and the accessor is called "unwrap" instead of "get-applicative-underlying".
  ;;

  (define wrap
    (lambda (combiner)
      (let ((appv  (let ((name  (list #t)))
                     (lambda (message)
                       (case message
                         ((type)       'applicative)
                         ((name)       name)
                         ((underlying) combiner))))))
        (designate-name-inheritor! appv combiner)
        appv)))

  (define applicative? (make-object-type-predicate 'applicative))

  (define unwrap (lambda (x) (x 'underlying)))

  ;;
  ;;
  ;;
  (define unary-predicate->applicative
    (lambda x
      (wrap (apply unary-predicate->operative x))))

  (define binary-predicate->applicative
    (lambda x
      (wrap (apply binary-predicate->operative x))))

  (define metered-action->checked-applicative
    (lambda x
      (wrap (apply metered-action->checked-operative x))))

  (define naive->checked-applicative
    (lambda x
      (wrap (apply naive->checked-operative x))))

  (define metered-naive->checked-applicative
    (lambda x
      (wrap (apply metered-naive->checked-operative x))))

  ;;
  ;; Given an action, and criteria for admissible argument-lists for that action,
  ;; constructs an applicative that checks its argument-list for those criteria,
  ;; and either invokes the given action, or throws an error.  Shorthand for
  ;; composition of wrap with action->checked-operative.
  ;;

  (define action->checked-applicative
    (lambda x
      (wrap (apply action->checked-operative x))))

  ;;
  ;; Given an action, constructs an applicative whose underlying operative has
  ;; that action.  Shorthand for composition of wrap with action->operative.
  ;;

  (define action->applicative
    (lambda (action)
      (wrap (action->operative action))))
  
  ;;
  ;; Predicates the combiner type.
  ;;
  (define combiner? (make-object-type-predicate 'operative 'applicative))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the applicative type.
  ;; It appears in this file, rather than in "subfiles/ground.scm", simply
  ;; because it is logically associated with the applicative type.
  ;;

  (define bind-applicative-primitives!
    (lambda (env)
      (add-bindings! env

        'applicative?
        (unary-predicate->applicative  applicative?)

        'wrap
        (action->checked-applicative
         (lambda (operand-tree env context)
           (wrap (kernel-car operand-tree)))
         1  1 combiner?)

        'unwrap
        (action->checked-applicative
         (lambda (operand-tree env context)
           (unwrap (kernel-car operand-tree)))
         1  1 applicative?)

        )))

  ;;
  ;; The name "context" is used within the interpreter for what the Kernel
  ;; programmer calls a "continuation".  The word "continuation" is used for
  ;; Scheme continuations.
  ;;
  ;; A context has type 'continuation (because that's the name that should be
  ;; visible within Kernel), and attributes 'receiver, 'parent, 'entry-guards,
  ;; 'exit-guards, 'error-context, 'terminal-context, 'alist, and 'mark.  None
  ;; of the attributes is directly accessible to clients.
  ;;
  ;;   'receiver is a continuation.  When an abnormal pass arrives at its
  ;; destination, the abnormally passed value goes to the destination's receiver.
  ;;
  ;;   'parent is either nil or a context.  The parent (even if nil) contains
  ;; this context, or equivalently, is an ancestor of this context.  Ancestry
  ;; and containment are improper unless otherwise stated, i.e., a context is
  ;; an ancestor of/contains itself.
  ;;
  ;;   'entry-guards and 'exit-guards are each a list of context/procedure pairs.
  ;; Each pair is called a "guard", its context a "selector", and its procedure
  ;; an "interceptor".
  ;;   When an abnormal pass is scheduled, a list is made of interceptors to be
  ;; called along the way.  At most one exit interceptor is selected from each
  ;; context to be exited, in the order they will be exited, and then at most one
  ;; entry interceptor from each context to be entered, in the order they will be
  ;; entered.  For each exited context, the first exit guard is selected whose
  ;; selector contains the destination of the abnormal pass;; for each entered
  ;; context, the first entry guard is selected whose selector contains the source
  ;; of the abnormal pass.
  ;;   Once the interceptors for the abnormal pass have been selected, they are
  ;; used in series to transform the abnormally passed value;; i.e., the value is
  ;; passed as an argument to the first interceptor, the output of the first is
  ;; passed as an argument to the second, etc.  The output of the last interceptor
  ;; goes to the destination's receiver.
  ;;
  ;;   'error-context is a context.  When an error occurs, a descriptor of the
  ;; error is abnormally passed to the error-context.
  ;;
  ;;   'terminal-context is a context.  Abnormally passing any value to the
  ;; terminal-context requests termination of the interpreter.
  ;;
  ;;   'alist is a list of keyed-bindings, constructed by tools in file
  ;; "subfiles/keyed.scm".
  ;;
  ;;   'mark is a pair, unique to this context, whose car is a boolean.  Its
  ;; car is #f except during ancestry-determination algorithms.  A context
  ;; whose mark's car is #t is said to be "marked".  Marking contexts allows
  ;; ancestry-determination algorithms to run in linear rather than quadratic
  ;; time.
  ;;

  (define make-context
    (lambda (receiver parent entry-guards exit-guards
                      error-context terminal-context alist)
      (let ((name  (list #t))
            (mark  (list #f)))
        (lambda (message)
          (case message
            ((type)             'continuation)
            ((name)             name)
            ((receiver)         receiver)
            ((parent)           parent)
            ((entry-guards)     entry-guards)
            ((exit-guards)      exit-guards)
            ((mark)             mark)
            ((error-context)    error-context)
            ((terminal-context) terminal-context)
            ((alist)            alist))))))

  (define context? (make-object-type-predicate 'continuation))

  ;;
  ;; A call to make-top-level-context may return multiple times.  The first time,
  ;; it returns a newly allocated top-level context.  On later returns from the
  ;; same call, it returns the same top-level context again, as long as processing
  ;; should continue;; if it returns nil, processing should terminate.
  ;;
  ;;   The top-level context's receiver returns the top-level context from the
  ;; make-top-level-context call.
  ;;
  ;;   The top-level context's error-context's receiver passes its received
  ;; value to the error-handling procedure (provided as an argument to
  ;; make-top-level-context), and calls the top-level context's receiver.
  ;;
  ;;   The top-level context's terminal-context's receiver returns nil from the
  ;; make-top-level-context call.
  ;;
  ;;   The top-level context's alist is provided by
  ;; make-top-level-dynamic-alist.
  ;;

  (define make-top-level-context
    (lambda (error-handler)
      (call-with-current-continuation
       (lambda (c)
         (letrec* ((receiver
                    (lambda ignore (c normal-context)))
                   (alist
                    (make-top-level-dynamic-alist))
                   (terminal-context
                    (let ((delegate  (make-context
                                      (lambda ignore (c '()))
                                      '() '() '() '() '() alist)))
                      (lambda (message)
                        (case message
                          ((error-context)     error-context)
                          ((terminal-context)  terminal-context)
                          (else                (delegate message))))))
                   (error-context
                    (let ((delegate  (make-context
                                      (lambda (ed)
                                        (receiver (error-handler ed)))
                                      '() '() '() '() '() alist)))
                      (lambda (message)
                        (case message
                          ((parent)            terminal-context)
                          ((error-context)     error-context)
                          ((terminal-context)  terminal-context)
                          (else                (delegate message))))))
                   (normal-context
                    (let ((delegate  (make-context
                                      receiver
                                      '() '() '() '() '() alist)))
                      (lambda (message)
                        (case message
                          ((parent)            terminal-context)
                          ((error-context)     error-context)
                          ((terminal-context)  terminal-context)
                          (else                (delegate message)))))))
           (receiver))))))

  ;;
  ;; call-with-guarded-context takes as arguments a procedure, parent context, and
  ;; entry and exit guards;; and passes as the single argument to the procedure
  ;; a new context whose receiver is the return continuation from the call to
  ;; call-with-guarded-context, whose parent and guards are as specified, and
  ;; whose error-context terminal-context and alist are inherited from the parent.
  ;;

  (define call-with-guarded-context
    (lambda (proc parent entry-guards exit-guards)
      (call-with-current-continuation
       (lambda (receiver)
         (let ((error-context     (parent 'error-context))
               (terminal-context  (parent 'terminal-context))
               (alist             (parent 'alist)))
           (proc (make-context receiver parent entry-guards exit-guards
                               error-context terminal-context alist)))))))

  ;;
  ;; call-with-keyed-context takes as arguments a procedure, parent context, and
  ;; key and value for a keyed binding;; and passes as the single argument to
  ;; the procedure a new context whose receiver is the return continuation from
  ;; the call to call-with-keyed-context, whose parent is as specified, whose
  ;; guard lists are empty, whose error-context and terminal-context are inherited
  ;; from the parent, and whose alist is inherited from the parent except for the
  ;; given keyed binding.
  ;;

  (define call-with-keyed-context
    (lambda (proc parent key value)
      (call-with-current-continuation
       (lambda (receiver)
         (let ((error-context     (parent 'error-context))
               (terminal-context  (parent 'terminal-context))
               (alist             (make-alist (parent 'alist) key value)))
           (proc (make-context receiver parent '() '()
                               error-context terminal-context alist)))))))

  ;;
  ;; Given the internal key for a keyed variable, and a context, looks up the
  ;; value of that keyed variable in that context's alist.  Returns the value
  ;; if found, or signals an error.
  ;;

  (define context-keyed-lookup
    (lambda (key context)
      (let ((binding  (alist-lookup key (context 'alist))))
        (if (pair? binding)
            (cdr binding)
            (error-pass
             (make-error-descriptor
              "Attempted to look up an unbound keyed dynamic variable"
              (list "in " (list context)))
             context)))))

  ;;
  ;; Given an environment and a context, binds symbols root-continuation and
  ;; error-continuation in the given environment to the terminal-context and
  ;; error-context of the given context.
  ;;

  (define initialize-context-bindings
    (lambda (env context)
      (add-bindings! env 'root-continuation (context 'terminal-context)
                     'error-continuation (context 'error-context))))

  ;;
  ;; Given a context, constructs an applicative that abnormally passes its
  ;; argument tree to that context.
  ;;

  (define context->applicative
    (lambda (dest-context)
      (let ((this
             (action->applicative
              (lambda (operand-tree env source-context)
                (abnormally-pass operand-tree source-context dest-context)))))
        (designate-name-inheritor! (unwrap this) dest-context)
        this)))

  ;;
  ;; Given an error descriptor and the context in which the error occurred,
  ;; abnormally passes the error descriptor to an appropriate error-handling
  ;; context.
  ;;

  (define error-pass
    (lambda (descriptor source)
      (abnormally-pass descriptor source (source 'error-context))))

  ;;
  ;; Given a value and the context in which interpreter termination is requested,
  ;; abnormally passes the value to that context's terminal-context.
  ;;

  (define terminal-pass
    (lambda (descriptor source)
      (abnormally-pass descriptor source (source 'terminal-context))))

  ;;
  ;; Abnormally passes a value from within a source context to a destination
  ;; context.
  ;;

  (define abnormally-pass
    (letrec (;;
             ;; Given a context and a boolean, stores the boolean in the cars of
             ;; the marks of all the ancestors of the context.
             ;;
             (set-marks!
              (lambda (context boolean)
                (if (not (null? context))
                    (begin
                      (set-car! (context 'mark) boolean)
                      (set-marks! (context 'parent) boolean)))))
             ;;
             ;; Given a list of guards and a list of previously selected
             ;; interceptors, and assuming that all ancestors of a target context
             ;; are marked, selects at most one interceptor whose selector
             ;; contains the target and prepends it to the list.  Returns the
             ;; updated list of selected interceptors.
             ;;
             (select-at-most-one
              (lambda (guards previously-selected)
                (cond ((null? guards)
                       previously-selected)
                      ((or (null? (caar guards))
                           (car ((caar guards) 'mark)))
                       (cons (cdar guards)
                             previously-selected))
                      (else (select-at-most-one (cdr guards)
                                                previously-selected)))))
             ;;
             ;; Given a context that contains the destination, and a list of
             ;; selected entry-interceptors strictly below the given context, and
             ;; assuming that all ancestors of the source are marked, returns a
             ;; list of all selected entry-interceptors for the abnormal pass.
             ;;
             (select-entry-interceptors
              (lambda (context previously-selected)
                (if (or (null? context)
                        (car (context 'mark)))
                    previously-selected
                    (select-entry-interceptors
                     (context 'parent)
                     (select-at-most-one
                      (context 'entry-guards)
                      previously-selected)))))
             ;;
             ;; Given a context that contains the source, and a list of all
             ;; selected entry-interceptors for the abnormal pass, and assuming
             ;; that all ancestors of the destination are marked, returns a list
             ;; of selected interceptors including exit-interceptors at or above
             ;; the given context.
             ;;
             (select-exit-interceptors
              (lambda (context previously-selected)
                (if (or (null? context)
                        (car (context 'mark)))
                    previously-selected
                    (select-at-most-one
                     (context 'exit-guards)
                     (select-exit-interceptors
                      (context 'parent)
                      previously-selected)))))
             ;;
             ;; Given a list of interceptors and an abnormally passed value, uses
             ;; the interceptors in series to transform the value;; i.e., the value
             ;; is passed as an argument to the first interceptor, the output of
             ;; the first is passed as an argument to the second, etc.
             ;;
             (serial-transform
              (lambda (interceptors value)
                (if (null? interceptors)
                    value
                    (serial-transform (cdr interceptors)
                                      ((car interceptors) value))))))

      (lambda (value source destination)
        (set-marks! source #t)
        (let ((selected  (select-entry-interceptors destination '())))
          (set-marks! source #f)
          (set-marks! destination #t)
          (let ((selected  (select-exit-interceptors source selected)))
            (set-marks! destination #f)
            ((destination 'receiver) (serial-transform selected value)))))))

  
  ;;
  ;; Given a value, determines whether that value is a list in the Kernel sense,
  ;; i.e., either a finite list terminated by nil, or a cyclic list.
  ;;
  (define kernel-list?
    (lambda (ls)
      (let* ((metrics  (get-list-metrics ls))
             (n  (cadr metrics))
             (c  (cadddr metrics)))
        (or (> n 0)
            (> c 0)))))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the context type.
  ;; It appears in this file, rather than in "subfiles/ground.scm", simply
  ;; because it is logically associated with the context type.
  ;;

  (define bind-context-primitives!
    (lambda (env)

      (define guards-list?
        (lambda (x)
          (and (kernel-list? x)
               (apply and?
                      (map (lambda (x)
                             (and (kernel-pair? x)
                                  (context? (kernel-car x))
                                  (kernel-pair? (kernel-cdr x))
                                  (applicative? (kernel-cadr x))
                                  (operative? (unwrap (kernel-cadr x)))
                                  (null? (kernel-cddr x))))
                           (kernel-list->list x))))))

      (add-bindings! env

        'continuation?
        (unary-predicate->applicative  context?)

        'call/cc
        (action->checked-applicative
         (lambda (operand-tree env context)
           (call-with-guarded-context
            (lambda (context)
              (kernel-eval (kernel-list (kernel-car operand-tree) context)
                           env context))
            context
            '()
            '()))
         1 1 combiner?)

        'extend-continuation
        (action->checked-applicative
         (lambda (operand-tree env context)
           (let ((parent  (kernel-car  operand-tree))
                 (appv    (kernel-cadr operand-tree))
                 (env     (if (kernel-pair? (kernel-cddr operand-tree))
                              (kernel-caddr operand-tree)
                              (make-environment))))
             (call-with-current-continuation
              (lambda (c)
                (let ((operand-tree
                       (call-with-current-continuation
                        (lambda (receiver)
                          (let ((error-context    (parent 'error-context))
                                (terminal-context (parent 'terminal-context))
                                (alist            (parent 'alist)))
                            (c (make-context receiver parent '() '()
                                             error-context terminal-context alist)))))))
                  ((parent 'receiver)
                   (kernel-eval (kernel-cons (unwrap appv) operand-tree)
                                env parent)))))))
         2 3 context? applicative? kernel-environment?)

        'guard-continuation
        (action->checked-applicative
         (lambda (operand-tree env context)
           (let* ((divert  '())
                  (convert-clause
                   (lambda (clause)
                     (let ((selector     (kernel-car clause))
                           (interceptor  (unwrap (kernel-cadr clause))))
                       (cons selector
                             (lambda (x)
                               (kernel-eval (kernel-list
                                             interceptor
                                             x (context->applicative divert))
                                            env divert))))))
                  (entry-guards  (map convert-clause
                                      (kernel-list->list
                                       (kernel-car operand-tree))))
                  (parent        (kernel-cadr operand-tree))
                  (exit-guards   (map convert-clause
                                      (kernel-list->list
                                       (kernel-caddr operand-tree)))))
             (call-with-current-continuation
              (lambda (c)
                (let ((operand-tree
                       (call-with-guarded-context
                        (lambda (outer-context)
                          (call-with-guarded-context
                           (lambda (inner-context)
                             (set! divert outer-context)
                             (c inner-context))
                           outer-context
                           '()
                           exit-guards))
                        parent
                        entry-guards
                        '())))
                  ((parent 'receiver)
                   operand-tree))))))
         3 3 guards-list? context? guards-list?)

        'continuation->applicative
        (action->checked-applicative
         (lambda (operand-tree env context)
           (context->applicative (kernel-car operand-tree)))
         1 1 context?)

        )))

  ;;
  ;; An encapsulation has type 'encapsulation, and attributes 'counter and 'value.
  ;; When viewed from within Kernel, the counter is part of the type.
  ;;
  ;; Each call to procedure make-encapsualtion-type returns a matched set of
  ;; encapsulator/type-predicate/decapsulator using a unique counter;;
  ;; the encapsulator manufactures encapsulations with that counter,
  ;; the type-predicate returns true only for encapsulations with that counter,
  ;; and the decapsulator only works on encapsulations with that counter.
  ;;

  (define make-encapsulation-type
    (let ((counter  0))
      (lambda ()
        (set! counter (+ counter 1))
        (let ((counter  counter))
          (let ((this-type?  (lambda (x)
                               (and (object? x)
                                    (eq? (x 'type) 'encapsulation)
                                    (= (x 'counter) counter)))))
            (kernel-list
             (naive->checked-applicative
              (lambda (operand-tree)
                (let ((value  (kernel-car operand-tree))
                      (name   (list #t)))
                  (lambda (message)
                    (case message
                      ((type)    'encapsulation)
                      ((name)    name)
                      ((counter) counter)
                      ((value)   value)))))
              "encapsulator"
              1 1)
             (unary-predicate->applicative this-type?)
             (naive->checked-applicative
              (lambda (operand-tree)
                ((kernel-car operand-tree) 'value))
              "decapsulator"
              1 1 this-type?)))))))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the encapsulation type.
  ;; It appears in this file, rather than in "subfiles/ground.scm", simply
  ;; because it is logically associated with the encapsulation type.
  ;;

  (define bind-encapsulation-primitives!
    (lambda (env)
      (add-bindings! env

        'make-encapsulation-type
        (action->checked-applicative
         (lambda x (make-encapsulation-type))
         0 0))))

  ;;
  ;; An environment has type 'environment, and attributes 'frames and 'alist.
  ;;
  ;;   'frames is a nonempty list of frames;; a frame is a list of length one whose
  ;; sole element is a list of name/value pairs.  Lookup starts with the first
  ;; frame.  There should never be any reason to work with frames outside this
  ;; file.
  ;;
  ;;   'alist is a list of keyed-bindings, constructed by tools in file
  ;; "subfiles/keyed.scm".
  ;;

  ;;
  ;; private constructor/accessors
  ;;

  (define internal-make-environment
    (lambda (frames alist)
      (let ((name  (list #t)))
        (lambda (message)
          (case message
            ((type)    'environment)
            ((name)    name)
            ((frames)  frames)
            ((alist)   alist))))))

  (define get-environment-frames (lambda (x) (x 'frames)))
  (define get-environment-alist  (lambda (x) (x 'alist)))

  ;;
  ;; public constructor/accessors
  ;;

  (define make-environment
    (lambda parents
      (internal-make-environment
       (cons (make-empty-frame)
             (apply append
                    (map get-environment-frames
                         parents)))
       (apply merge-alists
              (map get-environment-alist
                   parents)))))

  (define make-standard-environment
    (lambda (ground-environment)
      (make-environment ground-environment)))

  (define make-environment-with-keyed-binding
    (lambda (key value parent)
      (internal-make-environment
       (cons (make-empty-frame) (get-environment-frames parent))
       (make-alist (get-environment-alist parent) key value))))

  (define kernel-environment? (make-object-type-predicate 'environment))

  (define environment-keyed-lookup
    (lambda (key env context)
      (let ((binding  (alist-lookup key (get-environment-alist env))))
        (if (pair? binding)
            (cdr binding)
            (error-pass
             (make-error-descriptor
              "Attempted to look up an unbound keyed static variable"
              (list "in " (list env)))
             context)))))

  ;;
  ;; Returns the value bound to name if there is one, otherwise throws an error.
  ;;

  (define lookup
    (lambda (name env context)
      (let ((binding  (get-binding-from-frames
                       name (get-environment-frames env))))
        (if (eq? binding #f)
            (error-pass
             (make-error-descriptor
              (list "Unbound symbol: " (symbol->string name))
              (list "in " (describe-object env)))
             context)
            (cdr binding)))))

  ;;
  ;; Performs a series of local bind operations, mutating existing local bindings
  ;; when possible, creating new local bindings otherwise.  Takes an odd number of
  ;; arguments, of which the even arguments are names (i.e., symbols).  The first
  ;; argument is the environment in which local bindings are to be performed.
  ;; Each later odd argument is the value to be locally bound to the immediately
  ;; preceding name.
  ;;

  (define add-bindings!
    (lambda (env . x)
      (apply add-bindings-to-frame!
             (car (get-environment-frames env))
             x)))

  ;;
  ;; Removes local bindings for given symbols.  The first argument is the
  ;; environment from which local bindings are to be removed, and each later
  ;; argument is a symbol whose local binding, if any, is to be removed.
  ;;
  ;; This facility is not available to Kernel, but is used in
  ;; "subfiles/ground.scm" to allow certain facilities to be provided
  ;; temporarily in the ground environment while the Kernel library is being
  ;; loaded, and then removed from the ground environment before entering the
  ;; read-eval-print loop.
  ;;

  (define remove-bindings!
    (lambda (env . x)
      (apply remove-bindings-from-frame!
             (car (get-environment-frames env))
             x)))

  ;;
  ;; Determines whether a parameter tree is valid.
  ;;
  ;; A parameter tree is valid if it is acyclic, it contains no duplicate symbols,
  ;; and every leaf is either a symbol, nil, or ignore.
  ;;

  (define valid-ptree?
    (lambda (tree)

      (define aux ;; returns symbols if valid, #f if invalid
        (lambda (tree symbols)
          (cond ((ignore? tree)  symbols)
                ((null? tree)    symbols)
                ((symbol? tree)  (if (pair? (member tree symbols))
                                     #f
                                     (cons tree symbols)))
                ((kernel-pair? tree)
                 (let ((symbols  (aux (kernel-car tree) symbols)))
                   (if (eq? symbols #f)
                       #f
                       (aux (kernel-cdr tree) symbols))))
                (else  #f))))

      (and (not (cyclic-tree? tree))
           (list? (aux tree '())))))

  ;;
  ;; Locally binds a parameter-tree to an object.
  ;;
  ;; On success, returns nil.  On failure (invalid  parameter-tree, or
  ;; parameter-tree/object mismatch), returns an error-descriptor to whose
  ;; first line " when calling ..." might reasonably be appended.
  ;;

  (define match!
    (lambda (env ptree object)

      (define emsg '()) ;; repository for error-descriptor content

      ;; returns arguments for add-bindings-to-frame!
      (define aux
        (lambda (ptree object args)
          (cond ((kernel-pair? ptree)
                 (if (kernel-pair? object)
                     (aux      (kernel-cdr ptree) (kernel-cdr object)
                               (aux (kernel-car ptree) (kernel-car object) args))
                     (set! emsg
                           (append emsg
                                   (list (list "  mismatch:  " (list ptree)
                                               "  " (list object)))))))
                ((symbol? ptree)  (cons ptree (cons object args)))
                ((null? ptree)   (if (null? object)
                                     args
                                     (set! emsg
                                           (append emsg
                                                   (list (list "  mismatch:  '()  "
                                                               (list object)))))))
                (else args)))) ;; must be ignore

      (if (not (valid-ptree? ptree))
          (make-error-descriptor "Invalid parameter tree"
                                 (list "Parameter tree: " (list ptree)))
          (let ((args  (aux ptree object '())))
            (if (pair? emsg)
                (apply make-error-descriptor
                       "Definiend/object mismatch"
                       (list "Definiend:  " (list ptree))
                       (list "Object:     " (list object))
                       (list)
                       emsg)
                (begin
                  (apply add-bindings-to-frame!
                         (car (get-environment-frames env))
                         args)
                  '()))))))

  ;;
  ;; Constructs an empty frame.
  ;;

  (define make-empty-frame (lambda () (list '())))

  ;;
  ;; Performs a series of bind operations in given frame, mutating existing
  ;; bindings when possible, creating new bindings otherwise.  Arguments as
  ;; add-bindings!, except that the first argument is the local frame.
  ;;

  (define add-bindings-to-frame!
    (lambda (frame . x)
      (if (pair? x)
          (let ((name   (car  x))
                (value  (cadr x))
                (x      (cddr x)))
            (if (object? value)
                (suggest-object-name value name))
            (let ((binding  (get-binding-from-frame name frame)))
              (if (eq? binding #f)
                  (set-car! frame (cons (cons name value) (car frame)))
                  (set-cdr! binding value)))
            (apply add-bindings-to-frame! frame x)))))

  ;;
  ;; Deletes bindings for given symbols from given frame.  Arguments as
  ;; remove-bindings!, except that the first argument is the local frame.
  ;;

  (define remove-bindings-from-frame!
    (lambda (frame . x)

      (define aux-cdr!
        (lambda (bindings) ;; must be a pair whose car has already been checked
          (cond ((null? (cdr bindings)))
                ((pair? (member (caadr bindings) x))
                 (set-cdr! bindings (cddr bindings))
                 (aux-cdr! bindings))
                (#t
                 (aux-cdr! (cdr bindings))))))

      (define aux-car!
        (lambda (frame)
          (cond ((null? (car frame)))
                ((pair? (member (caaar frame) x))
                 (set-car! frame (cdar frame))
                 (aux-car! frame))
                (#t
                 (aux-cdr! (car frame))))))

      (aux-car! frame)))

  ;;
  ;; Returns the binding for name if there is one, otherwise returns #f.
  ;;

  (define get-binding-from-frames
    (lambda (name frames)
      (if (null? frames)
          #f
          (let ((binding  (get-binding-from-frame name (car frames))))
            (if (pair? binding)
                binding
                (get-binding-from-frames name (cdr frames)))))))

  ;;
  ;; Returns the binding for name if there is one, otherwise returns #f.
  ;;

  (define get-binding-from-frame
    (lambda (name frame)
      (assoc name (car frame))))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the environment type.
  ;; It appears in this file, rather than in "subfiles/ground.scm", simply
  ;; because it is logically associated with the type.
  ;;

  (define bind-environment-primitives!
    (lambda (env)

      ;;
      ;; Given a kernel-list, returns a freshly allocated list with the same elements
      ;; in the same order.
      ;;
      ;; If the resultant list certainly won't be mutated, use  kernel-list->list.
      ;;
      (define copy-kernel-list->list
        (lambda (ls)
          (define bounded-simple-map->list (make-bounded-simple-map cons))
          
          (bounded-simple-map->list (car (get-list-metrics ls))
                                    (lambda (x) x)
                                    ls)))

      (add-bindings! env

        'environment?
        (unary-predicate->applicative  kernel-environment?)

        'eval
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-eval (kernel-car operand-tree) (kernel-cadr operand-tree) context))
         2 2 any? kernel-environment?)

        'make-environment
        (naive->checked-applicative
         (lambda (operand-tree)
           (apply make-environment
                  (copy-kernel-list->list operand-tree)))
         "make-environment"
         0 -1 kernel-environment?)

        '$define!
        (action->checked-operative
         (lambda (operand-tree env context)
           (let ((ed  (match! env (kernel-car operand-tree)
                              (kernel-eval (kernel-cadr operand-tree)
                                           env context))))
             (if (error-descriptor? ed)
                 (begin
                   (error-add-to-first-line!  ed
                                              " when calling #[operative $define!]")
                   (error-pass ed context))
                 inert)))
         2 2)

        )))

  ;;
  ;; An error-descriptor has type 'error-descriptor, and attribute 'content whose
  ;; value is a Scheme list of Scheme lists of line elements.  A line element is
  ;; either a string, which is taken to be message text;; or a Scheme list of one
  ;; element, which is taken to be literal data.
  ;;

  (define make-error-descriptor
    (lambda content
      (let ((name     (list #t))
            (content  (map (lambda (x) (if (string? x) (list x) x)) content)))
        (lambda (message)
          (case message
            ((type)    'error-descriptor)
            ((name)    name)
            ((content) content))))))

  (define error-descriptor? (make-object-type-predicate 'error-descriptor))

  (define get-error-content (lambda (x) (x 'content)))

  (define error-add-to-first-line!
    (lambda (ed . suffix)
      (let ((content  (get-error-content ed)))
        (set-car! content
                  (append (car content) suffix)))))

  ;;
  ;; Describe an error.
  ;;
  ;; Since error descriptors can only be created directly by the interpreter,
  ;; if the internal format is wrong, it's SINK's fault.
  ;;

  (define describe-error
    (lambda (error-descriptor)

      ;; number of columns expended on strings on the current line
      (define column 0)

      ;; single element on a line
      (define aux3
        (lambda (element)
          (cond ((string? element)
                 (let ((new-column  (+ column (string-length element))))
                   (if (< 79 new-column)
                       (begin
                         (newline)
                         (display " ;;   ")
                         (set! column 5))
                       (set! column new-column)))
                 (display element))
                ((and (pair? element)
                      (null? (cdr element)))
                 (write-tree (car element) (current-output-port)))
                (else
                 (display " [[")
                 (write-tree element)
                 (display "]] ")))))

      ;; list of elements on a line
      (define aux2
        (lambda (ls)
          (if (pair? ls)
              (begin
                (aux3 (car ls))
                (aux2 (cdr ls))))))

      ;; list of lines
      (define aux
        (lambda (lss)
          (if (pair? lss)
              (begin
                (display " ;; ")
                (set! column 3)
                (aux2 (car lss))
                (newline)
                (aux (cdr lss))))))

      (aux (get-error-content error-descriptor))))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the error-descriptor
  ;; type.  It appears in this file, rather than in "subfiles/ground.scm", simply
  ;; because it is logically associated with the inert type.
  ;;

  (define bind-error-descriptor-primitives!
    (lambda (env)
      (add-bindings! env

        'error-descriptor?  (unary-predicate->applicative error-descriptor?))))

  ;;
  ;; The ignore value has type 'ignore and no attributes.
  ;;

  (define ignore (let ((name  (list #f)))
                   (lambda (message)
                     (case message
                       ((type) 'ignore)
                       ((name) name)))))

  (define ignore? (make-object-type-predicate 'ignore))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the ignore type (not
  ;; that there's anything much to use).  It appears in this file, rather than
  ;; in "subfiles/ground.scm", simply because it is logically associated with
  ;; the ignore type.
  ;;
  (define bind-ignore-primitives!
    (lambda (env)
      (add-bindings! env

        'ignore?  (unary-predicate->applicative ignore?))))

  ;;
  ;; The inert value has type 'inert and no attributes.
  ;;

  (define inert (let ((name  (list #f)))
                  (lambda (message)
                    (case message
                      ((type) 'inert)
                      ((name) name)))))

  (define inert? (make-object-type-predicate 'inert))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the inert type (not
  ;; that there's anything much to use).  It appears in this file, rather than
  ;; in "subfiles/ground.scm", simply because it is logically associated with
  ;; the inert type.
  ;;

  (define bind-inert-primitives!
    (lambda (env)
      (add-bindings! env

        'inert?  (unary-predicate->applicative inert?))))

  ;;
  ;; Pairs in the interpreted language ("Kernel") are a different data type from
  ;; pairs in the meta-language (Scheme).  The interpreted-language type is
  ;; called "kernel-pair".  Outside of this file, types pair and kernel-pair
  ;; cannot be assumed to be identical, nor can they be assumed to be disjoint.
  ;;
  ;; The interpreted language has both mutable and immutable kernel-pairs.
  ;; Their subtypes are called respectively "mutable" and "immutable".
  ;; Private to this file, immutables are disjoint from pairs, while two
  ;; different implementations are possible for mutables, one in which mutables
  ;; are actually pairs (unbeknownst to the rest of the interpreter), the other
  ;; in which they too are disjoint from pairs.
  ;;
  ;; When a procedure for kernel-pairs is cognate to one for pairs, it is named
  ;; by adding prefix "kernel-" to the Scheme name:  kernel-cons, kernel-car,
  ;; kernel-cdr, kernel-caar, etc.
  ;;
  ;; The only constructor of immutables is copy-es-immutable, which returns an
  ;; immutable copy of a kernel-pair and all other kernel-pairs reachable from
  ;; it without passing through any non-kernel-pair.  Consequently, it is not
  ;; possible for an immutable to have a mutable as its kernel-car or kernel-cdr.
  ;;
  ;; Type kernel-list differs from type list both by using kernel-pairs instead of
  ;; pairs, and by allowing cycles.  An "improper kernel-list" doesn't have to be
  ;; null-terminated, therefore all Kernel values are improper kernel-lists.
  ;; Similarly, every Kernel value is a kernel-tree;; but Scheme trees aren't used
  ;; in the interpreter, so kernel-trees are called simply "trees".
  ;;
  ;;
  ;; Implementing mutables disjointly is more expensive than implementing
  ;; immutables that way, because there is usually just one immutable copy of an
  ;; algorithm, but during evaluation of that one copy, many mutable argument
  ;; lists are constructed.  On the other hand, if mutables are represented by
  ;; pairs, it is appallingly easy for code elsewhere in the interpreter to treat
  ;; Kernel structures as if they were Scheme structures, without the bug being
  ;; detected for a long time.  Both implementations have been provided, one in
  ;; file "subfiles/kernel-pair-disjoint.scm" and the other in file
  ;; "subfiles/kernel-pair-overlapping.scm";; the file loaded by the interpreter,
  ;; called "subfiles/kernel-pair.scm", is a copy of one or the other version.
  ;;
  ;; This is the disjoint version of the type.  A mutable kernel-pair is an object
  ;; with type 'mutable and attribute 'kar, 'kdr, and 'content, where 'content is
  ;; a pair whose car and cdr are returned by 'kar and 'kdr.  An immutable
  ;; kernel-pair is an object with type 'immutable and attributes 'kar and 'kdr.
  ;;

  (define mutable? (make-object-type-predicate 'mutable))

  (define immutable? (make-object-type-predicate 'immutable))

  (define kernel-pair?
    (lambda (x)
      (or (mutable? x)
          (immutable? x))))

  (define kernel-car
    (lambda (x)
      (x 'kar)))

  (define kernel-cdr
    (lambda (x)
      (x 'kdr)))

  (define kernel-caar (lambda (x) (kernel-car (kernel-car x))))
  (define kernel-cadr (lambda (x) (kernel-car (kernel-cdr x))))
  (define kernel-cddr (lambda (x) (kernel-cdr (kernel-cdr x))))
  (define kernel-caddr (lambda (x) (kernel-car (kernel-cdr (kernel-cdr x)))))
  (define kernel-cadddr
    (lambda (x) (kernel-car (kernel-cdr (kernel-cdr (kernel-cdr x))))))

  (define kernel-cons
    (lambda (kar kdr)
      (let ((name     (list #t))
            (content  (cons kar kdr)))
        (lambda (message)
          (case message
            ((type)    'mutable)
            ((name)    name)
            ((kar)     (car content))
            ((kdr)     (cdr content))
            ((content) content))))))

  (define kernel-list
    (lambda x
      (if (pair? x)
          (kernel-cons (car x) (apply kernel-list (cdr x)))
          x)))

  (define kernel-set-car!
    (lambda (kernel-pair kar)
      (set-car! (kernel-pair 'content) kar)))

  (define kernel-set-cdr!
    (lambda (kernel-pair kdr)
      (set-cdr! (kernel-pair 'content) kdr)))

  ;;
  ;; Constructs a procedure that takes as its sole argument a possibly-cyclic
  ;; structure composed from some pair-like primitive data type, and returns a
  ;; list of nodes of the structure (i.e., pair-like entities) whose revisits
  ;; should be pruned during traversal of the structure.
  ;;
  ;; The precise condition that should be satisfied by the result is that the
  ;; listed revisits are a minimal set sufficient to minimize a traversal of the
  ;; structure.
  ;;   "Sufficient to minimize a traversal" means that, if the structure were
  ;; traversed, checking each node against the revisits-list;; and at the first
  ;; position where a listed node is visited, traversal would continue past it to
  ;; its descendants, but at other positions where it occurs, traversal would not
  ;; continue past it;; then this traversal would visit every node of the
  ;; structure at least once, and would revisit only nodes on the revisits-list.
  ;;   "Minimal set" means that if any member of the revisits-list were removed,
  ;; then it would no longer have this property, i.e., it would no longer be
  ;; sufficient to minimize a traversal.
  ;;
  ;; The purpose of this condition is to all clients to preserve structural
  ;; isomorphism.  This is a strictly more difficult task than merely preventing
  ;; infinite traversal of cyclic structures.  For example, commands
  ;;   ($define! x (list 1 2 3))
  ;;   (set-car! x (cdr x))
  ;; would produce acyclic structure  (#1=(2 3) . #1#)  whose revisit-list would
  ;; be a singleton list of node #1#.  Merely to prevent infinite traversals,
  ;; it would suffice to check each node against its ancestors;; but that would
  ;; not detect the redundancy in this example, so that any structural
  ;; transformation based on such an algorithm could not be expected to produce
  ;; a structurally isomorphic result.
  ;;
  ;; Arguments:
  ;;   tree               --- the structure itself, composed of pair-like nodes
  ;;   node?              --- predicate for the pair-like type
  ;;   node-car, node-cdr --- accessors for the pair-like type
  ;;
  (define make-get-revisits
    (lambda (node? node-car node-cdr)

      (define aux
        (lambda (revisits all . trees)
          (if (null? trees)
              revisits
              (let ((tree   (car trees))
                    (trees  (cdr trees)))
                (cond ((or (not (node? tree))
                           (pair? (memq tree revisits)))
                       (apply aux revisits all trees))
                      ((pair? (memq tree all))
                       (apply aux (cons tree revisits) all trees))
                      (else
                       (apply aux revisits (cons tree all)
                              (node-car tree) (node-cdr tree) trees)))))))

      ;; get-revisits
      (lambda (tree)
        (aux '() '() tree))))

  (define get-kernel-revisits
    (make-get-revisits kernel-pair? kernel-car kernel-cdr))

  ;;
  ;; Constructs a procedure that takes as its sole argument a possibly-cyclic
  ;; structure composed from some pair-like primitive data type, and returns
  ;; a structurally isomorphic copy of its evaluation structure, optionally
  ;; performing some transformation on leaf nodes during the copy.
  ;;
  ;; There will be three such procedures constructed:
  ;; copy-es-immutable, copy-es, and scheme-read-object->kernel.
  ;;
  ;; The evaluation structure of a value (under a given pair-like primitive type)
  ;; is the structure whose start is the value itself, and whose members are all
  ;; objects reachable from the start by following only car and cdr references
  ;; (of the given pair-like primitive type).  If the value is not of the
  ;; chosen pair-like type, then the value itself is the only object of the
  ;; data structure.
  ;;
  ;; Arguments:
  ;;     in-pair?       --- predicate for the input pair-like type
  ;;     in-car, in-cdr --- accessors for the input pair-like type
  ;;     make-record    --- constructs an alist record (see below)
  ;;     out-cons       --- constructs a copy of a non-pruned parent node
  ;;     xform-leaf     --- transformation to perform on leaves when copying
  ;;
  ;; First, compiles an alist whose keys are those in-pairs in the input
  ;; structure whose cyclic revisiting must be pruned during traversal.  For
  ;; each of these in-pairs, make-record constructs an alist record whose key
  ;; is the in-pair, whose cadr is an out-pair, and whose cddr is a pair whose
  ;; elements determine the out-car and out-cdr of the out-pair.  (Depending on
  ;; representations, the cadr and cddr might actually be the same object.)  Then
  ;; the in-pairs of the input structure are traversed a second time, creating
  ;; out-pairs for non-pruned mutables using out-cons, and setting the elements
  ;; of the previously constructed out-pairs for pruned in-pairs.  When the
  ;; elements of a pruned out-pair are to be set, its content pair is separated
  ;; out and the cddr of its record is set to nil, to prevent infinite recursion.
  ;;
  (define make-es-copier
    (lambda (in-pair? in-car in-cdr make-record out-cons xform-leaf)

      (define get-in-revisits (make-get-revisits in-pair? in-car in-cdr))

      ;; es-copier
      (lambda (tree)

        (define alist (map make-record (get-in-revisits tree)))

        (define aux
          (lambda (tree)
            (if (not (in-pair? tree))
                (xform-leaf tree)
                (let ((record  (assq tree alist)))
                  (if (pair? record)
                      (let ((content  (cddr record)))
                        (if (pair? content)
                            (begin
                              (set-cdr! (cdr record) '())
                              (set-car! content (aux (in-car tree)))
                              (set-cdr! content (aux (in-cdr tree)))))
                        (cadr record))
                      (out-cons (aux (in-car tree))
                                (aux (in-cdr tree))))))))

        (aux tree))))

  ;;
  ;; Given a Kernel value, returns an immutable copy of its evaluation structure.
  ;;
  (define copy-es-immutable
    (make-es-copier
     mutable? kernel-car kernel-cdr
     (let ((name  (list #f)))
       (lambda (key)
         (let ((content  (cons '() '())))
           (let ((immutable  (lambda (message)
                               (case message
                                 ((type) 'immutable)
                                 ((name) name)
                                 ((kar)  (car content))
                                 ((kdr)  (cdr content))))))
             (cons key
                   (cons immutable content))))))
     (let ((name  (list #f)))
       (lambda (kar kdr)
         (lambda (message)
           (case message
             ((type) 'immutable)
             ((name) name)
             ((kar)  kar)
             ((kdr)  kdr)))))
     (lambda (x) x)))

  ;;
  ;; Given a Kernel value, returns a mutable copy of its evaluation structure.
  ;;
  (define copy-es
    (make-es-copier
     kernel-pair? kernel-car kernel-cdr
     (lambda (key)
       (let* ((kernel-pair  (kernel-cons '() '()))
              (content      (kernel-pair 'content)))
         (cons key (cons kernel-pair content))))
     kernel-cons
     (lambda (x) x)))

  ;;
  ;; Given a scheme value presumed to have just been read, returns a mutable
  ;; Kernel version of the value, by copying its evaluation structure and
  ;; transforming certain symbols to their Kernel counterparts.
  ;;
  (define scheme-read-object->kernel
    (make-es-copier
     pair? car cdr
     (lambda (key)
       (let* ((kernel-pair  (kernel-cons '() '()))
              (content      (kernel-pair 'content)))
         (cons key (cons kernel-pair content))))
     kernel-cons
     (lambda (x)
       (if (symbol? x)
           (case x
             ((%ignore) ignore)
             ((%inert)  inert)
             ((%e+infinity)  exact-positive-infinity)
             ((%e-infinity)  exact-negative-infinity)
             ((%i+infinity)  inexact-positive-infinity)
             ((%i-infinity)  inexact-negative-infinity)
             (else      x))
           x))))

  
  ;;
  ;; Given a kernel-list, returns a freshly allocated list with the same elements
  ;; in the same order.
  ;;
  ;; If the resultant list certainly won't be mutated, use  kernel-list->list.
  ;;
  (define copy-kernel-list->list
    (lambda (ls)
      (define bounded-simple-map->list (make-bounded-simple-map cons))
      
      (bounded-simple-map->list (car (get-list-metrics ls))
                                (lambda (x) x)
                                ls)))
  ;;
  ;; Given a kernel-list, returns a list with the same elements in the same order.
  ;; The result is guaranteed to be a list (acyclic and made up of pairs), but is
  ;; not guaranteed to be distinct from the given kernel-list:  if mutables are
  ;; represented by pairs, the result may be the given kernel-list.  Therefore,
  ;; this tool should only be used if the resultant list certainly will not be
  ;; mutated (because mutating the result might mutate the original kernel-list).
  ;;
  ;; To guarantee that the result will be distinct from the argument,
  ;; use  copy-kernel-list->list.
  ;;
  (define kernel-list->list
    (lambda (ls)
      (copy-kernel-list->list ls)))

  ;;
  ;; Given a list, returns a mutable kernel-list with the same elements in the
  ;; same order.  The elements are assumed to be kernel values.  The result is
  ;; not guaranteed to be distinct from the given list:  if mutables are
  ;; represented by pairs, the result may be the given kernel-list.  Therefore,
  ;; this tool should only be used if the given list won't be needed again
  ;; (so that if it happens to be mutated, that won't be a problem).
  ;;
  (define list->kernel-list
    (lambda (ls)
      (if (null? ls)
          ls
          (kernel-cons (car ls)
                       (list->kernel-list (cdr ls))))))

  ;;
  ;; Determines whether a tree (i.e., an arbitrary interpreted-language value)
  ;; is cyclic.
  ;;
  (define cyclic-tree?
    (lambda (tree)

      (define aux
        (lambda (ancestors tree)
          (cond ((not (kernel-pair? tree))  #f)
                ((pair? (memq tree ancestors))  #t)
                (else
                 (let ((ancestors  (cons tree ancestors)))
                   (or (aux ancestors (kernel-car tree))
                       (aux ancestors (kernel-cdr tree))))))))

      (aux '() tree)))

  ;;
  ;; Given a tree of the interpreted language, output a representation of it to
  ;; a given output-port, using a given procedure to output the non-object leaves.
  ;; The latter takes as arguments the leaf and the output-port.  Either the third
  ;; argument, or the second and third arguments, may be omitted.  If the third
  ;; argument is omitted, write is used.  If the second argument is also omitted,
  ;; the current output-port is used.
  ;;
  ;; Cyclicity is handled by keeping an alist of revisits (kernel-pairs that will
  ;; be visited more than once and are to be expanded only on the first visit),
  ;; where the cadr of each record is the position of the record in the alist,
  ;; and the cddr of the record is #t or #f depending on whether that revisit has
  ;; already been expanded once.
  ;;
  (define write-tree
    (lambda (x . options)
      (let ((outport     (if (pair? options)
                             (car options)
                             (current-output-port)))
            (write-leaf  (if (and (pair? options) (pair? (cdr options)))
                             (cadr options)
                             write))
            (table  (letrec ((aux  (lambda (ls k)
                                     (if (null? ls)
                                         ls
                                         (cons (cons (car ls) (cons k #f))
                                               (aux (cdr ls) (+ k 1)))))))
                      (aux (get-kernel-revisits x) 0))))

        (define write-visit
          (lambda (x rec)
            (display "#"        outport)
            (display (cadr rec) outport)
            (if (cddr rec)
                (display "#" outport)
                (begin
                  (set-cdr! (cdr rec) #t)
                  (display   "=(" outport)
                  (write-car (kernel-car x))
                  (write-cdr (kernel-cdr x))
                  (display   ")" outport)))))

        (define write-cdr
          (lambda (x)
            (cond ((null? x))
                  ((kernel-pair? x)
                   (let ((rec  (assq x table)))
                     (if (pair? rec)
                         (begin
                           (display     " . " outport)
                           (write-visit x rec))
                         (begin
                           (display   " " outport)
                           (write-car (kernel-car x))
                           (write-cdr (kernel-cdr x))))))
                  (else
                   (display   " . " outport)
                   (write-car x)))))

        (define write-car
          (lambda (x)
            (cond ((kernel-pair? x)
                   (let ((rec  (assq x table)))
                     (if (pair? rec)
                         (write-visit x rec)
                         (begin
                           (display   "(" outport)
                           (write-car (kernel-car x))
                           (write-cdr (kernel-cdr x))
                           (display   ")" outport)))))
                  ((object? x)  (display (describe-object x) outport))
                  ((pair? x)
                   (display "#[misplaced meta-language structure: ")
                   (write x)
                   (display "]"))
                  (else  (write-leaf x outport)))))

        (write-car x))))

  ;;
  ;; As write-tree, except that there must be exactly two arguments, and the
  ;; non-object leaf output procedure is display rather than write.
  ;;
  (define display-tree
    (lambda (x outport)
      (write-tree x outport display)))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the kernel-pair type.
  ;; It appears in this file, rather than in "subfiles/ground.scm", simply
  ;; because it is logically associated with the kernel-pair type.
  ;;
  (define bind-kernel-pair-primitives!
    (lambda (env)
      (add-bindings! env

        'pair? (unary-predicate->applicative  kernel-pair?)

        'cons
        (naive->checked-applicative
         (lambda (operand-tree)
           (kernel-cons (kernel-car operand-tree)
                        (kernel-cadr operand-tree)))
         "cons"
         2 2)

        'copy-es-immutable
        (naive->checked-applicative
         (lambda (operand-tree)
           (copy-es-immutable (kernel-car operand-tree)))
         "copy-es-immutable"
         1 1)

        'copy-es
        (naive->checked-applicative
         (lambda (operand-tree)
           (copy-es (kernel-car operand-tree)))
         "copy-es"
         1 1)

        'set-car!
        (action->checked-applicative
         (lambda (operand-tree env context)
           (let ((x  (kernel-car operand-tree))
                 (y  (kernel-cadr operand-tree)))
             (if (mutable? x)
                 (kernel-set-car! x y)
                 (error-pass (make-error-descriptor
                              (list "Operand #1 is immutable"
                                    " when calling primitive set-car!")
                              (list "Operand tree: " (list operand-tree)))
                             context)))
           inert)
         2 2 kernel-pair? any?)

        'set-cdr!
        (action->checked-applicative
         (lambda (operand-tree env context)
           (let ((x  (kernel-car operand-tree))
                 (y  (kernel-cadr operand-tree)))
             (if (mutable? x)
                 (kernel-set-cdr! x y)
                 (error-pass (make-error-descriptor
                              (list "Operand #1 is immutable"
                                    " when calling primitive set-cdr!")
                              (list "Operand tree: " (list operand-tree)))
                             context)))
           inert)
         2 2 kernel-pair? any?)

        )))

  ;;
  ;; Keyed variables are (from the Kernel programmer's perspective) bound and
  ;; accessed via matched sets of combiners --- one binder and one accessor for
  ;; each "variable".  There are two kinds of keyed variables:  dynamic keyed
  ;; variables, which are bound in contexts, and static keyed variables, which are
  ;; bound in environments (but are entirely separate from symbolic variables).
  ;; Internally, each context or environment holds a list of key/value pairs;; the
  ;; holding object regulates access to the alist, but the actual operations
  ;; are handled by tools provided here --- key assignment, alist construction,
  ;; and lookup.
  ;;
  ;; The keys are integers.  Once an alist is in a context/environment, it is
  ;; never mutated.
  ;;
  ;; There is no need for the alists or the keys to be encapsulated, because the
  ;; purpose of encapsulation is to prevent Kernel programs from violating
  ;; abstraction barriers on the objects they manipulate, and Kernel programs
  ;; are never allowed to directly touch the alists or keys.
  ;;

  ;;
  ;; Assigns a fresh key.
  ;;
  (define get-fresh-key
    (let ((counter  0))
      (lambda ()
        (set! counter (+ counter 1))
        counter)))

  ;;
  ;; Given an alist and a key and value, constructs a new alist whose only
  ;; difference from the given alist is a binding of given key to given value.
  ;;
  ;; Allocates only as many new pairs as necessary to guarantee that the new alist
  ;; has only one binding for the given key (assuming that the given alist didn't
  ;; already have more than one binding for it).
  ;;
  (define make-alist
    (lambda (alist key value)

      (define aux       ;; assumes the key is bound somewhere in alist
        (lambda (alist)
          (if (eq? (caar alist) key)
              (cons (cons key value) (cdr alist))
              (cons (car alist) (aux (cdr alist))))))

      (if (and (pair? alist)
               (pair? (assq key alist)))
          (aux alist)
          (cons (cons key value) alist))))

  ;;
  ;; Given zero or more alists, constructs a single alist containing the first
  ;; binding for each key among the given alists.
  ;;
  (define merge-alists
    (lambda lss

      (define aux2
        (lambda (alist1 alist2)
          (if (null? alist1)
              alist2
              (make-alist (aux2 (cdr alist1) alist2)
                          (caar alist1)
                          (cdar alist1)))))

      (define aux
        (lambda (alist . lss)
          (if (null? lss)
              alist
              (aux2 alist (apply aux lss)))))

      (if (null? lss)
          lss
          (apply aux lss))))

  ;;
  ;; Looks up a key in an alist.
  ;;
  (define alist-lookup assq)

  ;;
  ;; Constructs a top-level dynamic alist.
  ;;
  ;; This must happen when the interpreter is called, not when the interpreter is
  ;; constructed, because the top-level input-port and output-port should be those
  ;; in effect when the interpreter is called, not when it is constructed.  The
  ;; bindings are provided by procedures in other files, which are called from
  ;; here, and which in turn are responsible for calling get-fresh-key.  The other
  ;; procedures return alists.
  ;;

  (define make-top-level-dynamic-alist
    (lambda ()
      (make-top-level-ports-alist)))

  ;;
  ;; Creates bindings for keyed variables in a given environment.
  ;;
  (define bind-keyed-variable-primitives!
    (lambda (env)
      (add-bindings! env

        'make-keyed-dynamic-variable
        (naive->checked-applicative
         (lambda (operand-tree)
           (let ((key  (get-fresh-key)))
             (list
              (action->checked-applicative
               (lambda (operand-list env context)
                 (call-with-keyed-context
                  (lambda (context)
                    (kernel-eval (kernel-cdr operand-list) env context))
                  context
                  key
                  (kernel-car operand-list)))
               2 2 any? combiner?)
              (action->checked-applicative
               (lambda (operand-list env context)
                 (context-keyed-lookup key context))
               0 0))))
         "make-keyed-dynamic-variable"
         0 0)

        'make-keyed-static-variable
        (naive->checked-applicative
         (lambda (operand-tree)
           (let ((key  (get-fresh-key)))
             (list
              (action->checked-applicative
               (lambda (operand-list env context)
                 (make-environment-with-keyed-binding
                  key
                  (kernel-car operand-list)
                  (kernel-cadr operand-list)))
               2 2 any? kernel-environment?)
              (action->checked-applicative
               (lambda (operand-list env context)
                 (environment-keyed-lookup key env context))
               0 0))))
         "make-keyed-static-variable"
         0 0)

        )))

  ;;
  ;; Infinities are incompletely supported.
  ;;
  ;; Exact and inexact, positive and negative, infinty have types
  ;; 'e+infinity 'e-infinity 'i+infinity 'i-infinity, and no attributes.
  ;;
  ;; Complex numbers are not supported.  They would be a substantial addition,
  ;; because of their interactions with infinities.
  ;;

  (define exact-positive-infinity
    (let ((name  (list #f)))
      (lambda (message)
        (case message
          ((type) 'e+infinity)
          ((name) name)))))

  (define exact-negative-infinity
    (let ((name  (list #f)))
      (lambda (message)
        (case message
          ((type) 'e-infinity)
          ((name) name)))))

  (define inexact-positive-infinity
    (let ((name  (list #f)))
      (lambda (message)
        (case message
          ((type) 'i+infinity)
          ((name) name)))))

  (define inexact-negative-infinity
    (let ((name  (list #f)))
      (lambda (message)
        (case message
          ((type) 'i-infinity)
          ((name) name)))))

  (define exact-positive-infinity?    (make-object-type-predicate 'e+infinity))
  (define exact-negative-infinity?    (make-object-type-predicate 'e-infinity))
  (define inexact-positive-infinity?  (make-object-type-predicate 'i+infinity))
  (define inexact-negative-infinity?  (make-object-type-predicate 'i-infinity))

  (define positive-infinity?
    (make-object-type-predicate 'e+infinity 'i+infinity))

  (define negative-infinity?
    (make-object-type-predicate 'e-infinity 'i-infinity))

  (define exact-infinity?
    (make-object-type-predicate 'e+infinity 'e-infinity))

  (define inexact-infinity?
    (make-object-type-predicate 'i+infinity 'i-infinity))

  (define infinity?
    (make-object-type-predicate 'e+infinity 'e-infinity
                                'i+infinity 'i-infinity))

  (define kernel-real?
    (lambda ls
      (or (null? ls)
          (and (or (infinity? (car ls))
                   (real? (car ls)))
               (apply kernel-real? (cdr ls))))))

  (define kernel-number? kernel-real?)

  (define kernel-<?
    (lambda (x y)
      (cond ((real? x)
             (if (real? y)
                 (< x y)
                 (positive-infinity? y)))
            ((negative-infinity? x)
             (not (negative-infinity? y)))
            (else
             #f))))

  (define kernel-<=?
    (lambda (x y)
      (cond ((real? x)
             (if (real? y)
                 (<= x y)
                 (positive-infinity? y)))
            ((negative-infinity? x)
             #t)
            (else
             (positive-infinity? y)))))

  (define kernel-=?
    (lambda (x y)
      (cond ((real? x)
             (if (real? y)
                 (= x y)
                 #f))
            ((negative-infinity? x)
             (negative-infinity? y))
            (else
             (positive-infinity? y)))))

  (define kernel->?
    (lambda (x y)
      (cond ((real? x)
             (if (real? y)
                 (> x y)
                 (negative-infinity? y)))
            ((negative-infinity? x)
             #f)
            (else
             (not (positive-infinity? y))))))

  (define kernel->=?
    (lambda (x y)
      (cond ((real? x)
             (if (real? y)
                 (>= x y)
                 (negative-infinity? y)))
            ((negative-infinity? x)
             (negative-infinity? y))
            (else
             #t))))

  (define kernel-zero?
    (lambda (x)
      (and (real? x)
           (zero? x))))

  (define kernel-exact?
    (lambda (x)
      (if (real? x)
          (exact? x)
          (exact-infinity? x))))

  (define describe-kernel-number
    (lambda (x)
      (if (real? x)
          (number->string x)
          (describe-object x))))

  ;;
  ;; The arithmetic operations return a string on error.
  ;;

  (define kernel-negate
    (lambda (x)
      (cond ((string? x)  x)
            ((real? x)  (- x))
            ((exact-positive-infinity? x)  exact-negative-infinity)
            ((exact-negative-infinity? x)  exact-positive-infinity)
            ((inexact-positive-infinity? x)  inexact-negative-infinity)
            (else  inexact-positive-infinity))))

  (define kernel-invert
    (lambda (x)
      (cond ((string? x)  x)
            ((real? x)  (if (zero? x)
                            "Division by zero"
                            (/ 1 x)))
            ((inexact-infinity? x)  0.0)
            (else 0))))

  (define kernel-binary-multiply
    (lambda (x y)

      (define indeterminate
        (lambda ()
          (string-append "Indeterminate product of "
                         (describe-kernel-number x) " with "
                         (describe-kernel-number y))))

      (cond ((string? y)  y)
            ((string? x)  x)
            ((real? x)
             (cond ((real? y)  (* x y))
                   ((zero? x)  (indeterminate))
                   ((exact? x)  (if (> x 0) y (kernel-negate y)))
                   ((positive-infinity? y)
                    (if (> x 0) inexact-positive-infinity
                        inexact-negative-infinity))
                   (else
                    (if (> x 0) inexact-negative-infinity
                        inexact-positive-infinity))))
            ((real? y)
             (cond ((zero? y)  (indeterminate))
                   ((exact? y)  (if (> y 0) x (kernel-negate x)))
                   ((positive-infinity? x)
                    (if (> y 0) inexact-positive-infinity
                        inexact-negative-infinity))
                   (else
                    (if (> y 0) inexact-negative-infinity
                        inexact-positive-infinity))))
            ((exact-positive-infinity? x)  y)
            ((exact-negative-infinity? x)  (kernel-negate y))
            ((inexact-positive-infinity? x)
             (if (positive-infinity? y) inexact-positive-infinity
                 inexact-negative-infinity))
            (else
             (if (positive-infinity? y) inexact-negative-infinity
                 inexact-positive-infinity)))))

  (define kernel-binary-add
    (lambda (x y)

      (define indeterminate
        (lambda ()
          (string-append "Indeterminate sum of "
                         (describe-kernel-number x) " with "
                         (describe-kernel-number y))))

      (cond ((string? y)  y)
            ((string? x)  x)
            ((real? x)
             (cond ((real? y)  (+ x y))
                   ((exact? x)  y)
                   ((positive-infinity? y)  inexact-positive-infinity)
                   (else                    inexact-negative-infinity)))
            ((positive-infinity? x)
             (cond ((real? y)  (if (exact? y) x inexact-positive-infinity))
                   ((negative-infinity? y)        (indeterminate))
                   ((exact-positive-infinity? y)  x)
                   (else  y)))
            (else
             (cond ((real? y)  (if (exact? y) x inexact-negative-infinity))
                   ((positive-infinity? y)        (indeterminate))
                   ((exact-negative-infinity? y)  x)
                   (else y))))))

  (define kernel-bounded-reduce
    (lambda (k ls binary identity)
      (cond ((> k 1)  (binary (kernel-car ls)
                              (kernel-bounded-reduce
                               (- k 1) (kernel-cdr ls) binary identity)))
            ((= k 1)  (kernel-car ls))
            (else identity))))

  (define kernel-bounded-test?
    (lambda (k ls unary?)
      (or (<= k 0)
          (and (unary? (kernel-car ls))
               (kernel-bounded-test? (- k 1) (kernel-cdr ls) unary?)))))

  (define kernel-add
    (lambda (ls)

      (define bounded-sum
        (lambda (k ls)
          (kernel-bounded-reduce
           k ls kernel-binary-add 0)))

      (define bounded-zero?
        (lambda (k ls)
          (kernel-bounded-test? k ls kernel-zero?)))

      (let* ((metrics  (get-list-metrics ls))
             (a  (caddr metrics))
             (c  (cadddr metrics)))
        (kernel-binary-add
         (bounded-sum a ls)
         (if (zero? c)
             0
             (let* ((cycle  (kernel-list-tail ls a))
                    (sum-c  (bounded-sum c cycle)))
               (if (kernel-zero? sum-c)
                   (if (bounded-zero? c cycle)
                       sum-c
                       "Sum of cycle doesn't converge")
                   (kernel-binary-multiply
                    sum-c
                    exact-positive-infinity))))))))

  (define kernel-multiply
    (lambda (ls)

      (define bounded-product
        (lambda (k ls)
          (kernel-bounded-reduce
           k ls kernel-binary-multiply 1)))

      (define bounded-nonnegative?
        (lambda (k ls)
          (kernel-bounded-test? k ls
                                (lambda (x) (kernel->=? x 0)))))

      (define bounded-one?
        (lambda (k ls)
          (kernel-bounded-test? k ls
                                (lambda (x) (kernel-=? x 1)))))

      (let* ((metrics  (get-list-metrics ls))
             (a  (caddr metrics))
             (c  (cadddr metrics)))
        (kernel-binary-multiply
         (bounded-product a ls)
         (if (zero? c)
             1
             (let* ((cycle      (kernel-list-tail ls a))
                    (product-c  (bounded-product c cycle)))
               (cond ((or (kernel-zero? product-c)
                          (bounded-one? c cycle))
                      product-c)
                     ((or (not (bounded-nonnegative? c cycle))
                          (kernel-=? product-c 1))
                      "Product of cycle doesn't converge")
                     (else
                      (kernel-binary-multiply
                       product-c
                       (if (kernel-<? product-c 1)
                           0
                           exact-positive-infinity))))))))))

  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; If there were any internal knowledge of the Kernel number type, this code
  ;; would ought not to use it.  The file currently exists solely as a place to
  ;; put this code, and if there were more to the type, the code would still
  ;; appear here simply because it is logically associated with the type.
  ;;
  (define bind-number-primitives!
    (lambda (env)
      (add-bindings! env

        'number?   (unary-predicate->applicative kernel-number?)
        'real?     (unary-predicate->applicative kernel-real?)
        'rational? (unary-predicate->applicative rational?)
        'integer?  (unary-predicate->applicative integer?)
        'exact?    (unary-predicate->applicative kernel-exact?)
        'inexact?  (unary-predicate->applicative
                    (lambda (x) (not (kernel-exact? x))))

        '+
        (letrec ((this
                  (action->checked-applicative
                   (lambda (operand-tree env context)
                     (let ((result  (kernel-add operand-tree)))
                       (if (string? result)
                           (error-pass
                            (make-error-descriptor
                             (list result ", " "when calling "
                                   (describe-object this))
                             (list "Operand tree: " operand-tree))
                            context)
                           result)))
                   0 -1 kernel-number?)))
          this)

        '-
        (letrec ((this
                  (action->checked-applicative
                   (lambda (operand-tree env context)
                     (let ((result  (kernel-add (kernel-cdr operand-tree))))
                       (if (not (string? result))
                           (set! result (kernel-binary-add
                                         (kernel-car operand-tree)
                                         (kernel-negate result))))
                       (if (string? result)
                           (error-pass
                            (make-error-descriptor
                             (list result ", " "when calling"
                                   (describe-object this))
                             (list "Operand-tree: " operand-tree))
                            context)
                           result)))
                   2 -1 kernel-number?)))
          this)

        '*
        (letrec ((this
                  (action->checked-applicative
                   (lambda (operand-tree env context)
                     (let ((result  (kernel-multiply operand-tree)))
                       (if (string? result)
                           (error-pass
                            (make-error-descriptor
                             (list result ", " "when calling "
                                   (describe-object this))
                             (list "Operand tree: " operand-tree))
                            context)
                           result)))
                   0 -1 kernel-number?)))
          this)

        '/
        (letrec ((this
                  (action->checked-applicative
                   (lambda (operand-tree env context)
                     (let ((result  (kernel-binary-multiply
                                     (kernel-car operand-tree)
                                     (kernel-invert
                                      (kernel-multiply
                                       (kernel-cdr operand-tree))))))
                       (if (string? result)
                           (error-pass
                            (make-error-descriptor
                             (list result ", " "when calling "
                                   (describe-object this))
                             (list "Operand tree: " operand-tree))
                            context)
                           result)))
                   2 -1 kernel-number?)))
          this)

        '<?  (binary-predicate->applicative  kernel-<?   kernel-real?)
        '<=? (binary-predicate->applicative  kernel-<=?  kernel-real?)
        '=?  (binary-predicate->applicative  kernel-=?   kernel-real?)
        '>?  (binary-predicate->applicative  kernel->?   kernel-real?)
        '>=? (binary-predicate->applicative  kernel->=?  kernel-real?)

        'round
        (naive->checked-applicative
         (lambda (operand-tree)
           (round (kernel-car operand-tree)))
         "round"
         1 1 (lambda (x) (and (kernel-real? x) (not (infinity? x)))))

        'floor
        (naive->checked-applicative
         (lambda (operand-tree)
           (floor (kernel-car operand-tree)))
         "floor"
         1 1 (lambda (x) (and (kernel-real? x) (not (infinity? x)))))

        'ceiling
        (naive->checked-applicative
         (lambda (operand-tree)
           (ceiling (kernel-car operand-tree)))
         "ceiling"
         1 1 (lambda (x) (and (kernel-real? x) (not (infinity? x)))))

        'quotient
        (naive->checked-applicative
         (lambda (operand-tree)
           (quotient (kernel-car operand-tree)
                     (kernel-cadr operand-tree)))
         "quotient"
         2 2 integer? (lambda (x) (and (integer? x) (not (zero? x)))))

        'remainder
        (naive->checked-applicative
         (lambda (operand-tree)
           (remainder (kernel-car operand-tree)
                      (kernel-cadr operand-tree)))
         "remainder"
         2 2 integer? (lambda (x) (and (integer? x) (not (zero? x)))))

        'modulo
        (naive->checked-applicative
         (lambda (operand-tree)
           (modulo (kernel-car operand-tree)
                   (kernel-cadr operand-tree)))
         "modulo"
         2 2 integer? (lambda (x) (and (integer? x) (not (zero? x)))))

        'exact->inexact
        (naive->checked-applicative
         (lambda (operand-tree)
           (let ((x  (kernel-car operand-tree)))
             (cond ((not (kernel-exact? x))  x)
                   ((exact-positive-infinity? x)  inexact-positive-infinity)
                   ((exact-negative-infinity? x)  inexact-negative-infinity)
                   (else  (exact->inexact x)))))
         "exact->inexact"
         1 1 kernel-real?)

        'inexact->exact
        (naive->checked-applicative
         (lambda (operand-tree)
           (let ((x  (kernel-car operand-tree)))
             (cond ((kernel-exact? x)  x)
                   ((inexact-positive-infinity? x)  exact-positive-infinity)
                   ((inexact-negative-infinity? x)  exact-negative-infinity)
                   (else  (inexact->exact x)))))
         "inexact->exact"
         1 1 kernel-real?)

        'random
        (naive->checked-applicative
         (lambda (operand-tree)
           (random (kernel-car operand-tree)))
         "random"
         1 1 (lambda (x) (and (integer? x) (exact? x) (>= x 0))))

        'log
        (naive->checked-applicative
         (lambda (operand-tree)
           (let ((x  (kernel-car operand-tree)))
             (cond ((positive-infinity? x)  x)
                   ((zero? x)  (if (exact? x)
                                   exact-negative-infinity
                                   inexact-negative-infinity))
                   (else  (log x)))))
         "log"
         1 1 (lambda (x) (and (kernel-real? x) (kernel-<? 0 x))))

        'sqrt
        (naive->checked-applicative
         (lambda (operand-tree)
           (let ((x  (kernel-car operand-tree)))
             (cond ((positive-infinity? x)  x)
                   (else  (sqrt x)))))
         "sqrt"
         1 1 (lambda (x) (and (kernel-real? x) (kernel-<=? 0 x))))

        'sin
        (naive->checked-applicative
         (lambda (operand-tree)
           (sin (kernel-car operand-tree)))
         "sin"
         1 1 (lambda (x) (and (kernel-real? x) (not (infinity? x)))))

        'cos
        (naive->checked-applicative
         (lambda (operand-tree)
           (cos (kernel-car operand-tree)))
         "cos"
         1 1 (lambda (x) (and (kernel-real? x) (not (infinity? x)))))

        'tan
        (naive->checked-applicative
         (lambda (operand-tree)
           (tan (kernel-car operand-tree)))
         "tan"
         1 1 (lambda (x) (and (kernel-real? x) (not (infinity? x)))))

        'asin
        (naive->checked-applicative
         (lambda (operand-tree)
           (asin (kernel-car operand-tree)))
         "asin"
         1 1 (lambda (x) (and (kernel-real? x) (<= -1 x 1))))

        'acos
        (naive->checked-applicative
         (lambda (operand-tree)
           (acos (kernel-car operand-tree)))
         "acos"
         1 1 (lambda (x) (and (kernel-real? x) (<= -1 x 1))))

        'atan
        (letrec ((this
                  (action->checked-applicative
                   (lambda (operand-tree env context)
                     (if (kernel-pair? (kernel-cdr operand-tree))
                         (let ((x  (kernel-car operand-tree))
                               (y  (kernel-cadr operand-tree)))
                           (cond ((or (and (infinity? x) (infinity? y))
                                      (and (kernel-zero? x) (kernel-zero? y)))
                                  (error-pass
                                   (make-error-descriptor
                                    (list "indeterminate result when calling"
                                          (describe-object this))
                                    (list "Operand tree: " operand-tree))
                                   context))
                                 ((positive-infinity? x)          (atan 1 0))
                                 ((negative-infinity? x)          (atan -1 0))
                                 ((exact-positive-infinity? y)    0)
                                 ((inexact-positive-infinity? y)  0.0)
                                 ((negative-infinity? y)          (atan 0 -1))
                                 (else  (atan x y))))
                         (let ((x  (kernel-car operand-tree)))
                           (cond ((positive-infinity? x)  (atan 1 0))
                                 ((negative-infinity? x)  (atan -1 0))
                                 (else  (atan x))))))
                   1 2 kernel-real?)))
          this)

        )))

  ;;
  ;; An operative has type 'operative, and attribute 'action whose value is a
  ;; procedure whose arguments are the operand tree, environment, and context.
  ;;

  (define action->operative
    (lambda (action)
      (let ((name  (list #t)))
        (lambda (message)
          (case message
            ((type)   'operative)
            ((name)   name)
            ((action) action)
            ((meta)   #f))))))

  (define action->meta-operative
    (lambda (meta action)
      (let ((name  (list #t)))
        (lambda (message)
          (case message
            ((type)   'operative)
            ((name)   name)
            ((action) action)
            ((meta)   meta))))))

  (define operative? (make-object-type-predicate 'operative))

  ;;
  ;; Calls an operative.
  ;;
  (define operate
    (lambda (operative operand-tree env context)
      ((operative 'action) operand-tree env context)))

  ;;
  ;; Checks a (kernel) operand list, given its min and max allowed lengths, and
  ;; optionally predicates with which to type-check the individual operands.
  ;; Arguments:
  ;;     operands   --- the unchecked operand tree.
  ;;     min        --- the minimum allowed number of operands.
  ;;     max        --- the maximum allowed number of operands, or negative
  ;;                   if there is no maximum.
  ;;   . predicates --- the predicates, if any.
  ;; If there are no predicates, only the number of operands is checked.
  ;; If there is just one predicate, it is used on all the operands.
  ;; If there is more than one predicate, each predicate is used on just one
  ;; operand, left-to-right, until either there are no more operands or there is
  ;; just one more predicate;; when there is just one more predicate, it is used
  ;; on any remaining operands.
  ;;
  ;; The result is an error message string if an error was detected;; otherwise,
  ;; the result is the list metrics of the operand list.
  ;;
  (define check-operand-list
    (lambda (operands min max . predicates)

      (define aux
        (lambda (p k operands . predicates)
          (cond ((<= k 0)  '())
                (((car predicates) (kernel-car operands))
                 (apply aux p
                        (- k 1)
                        (kernel-cdr operands)
                        (if (null? (cdr predicates))
                            predicates
                            (cdr predicates))))
                (else
                 (string-append
                  "Operand #" (number->string (- p k -1))
                  " has wrong type")))))

      (let* ((metrics  (get-list-metrics operands))
             (p  (car metrics))
             (n  (cadr metrics))
             (c  (cadddr metrics)))
        (cond ((and (= n 0) (= c 0))  "Operand tree is not a list")
              ((and (>= max 0)
                    (or (> p max) (> c 0)))
               (string-append
                "Too many operands (more than " (number->string max) ")"))
              ((< p min)
               (string-append
                "Not enough operands (fewer than " (number->string min) ")"))
              ((null? predicates)
               metrics)
              (else
               (let ((emsg  (apply aux p p operands predicates)))
                 (if (string? emsg)
                     emsg
                     metrics)))))))

  ;;
  ;; Given a "naive action", returns an action that does the same thing.
  ;; A string naming the action is also given, to be used if the naive action
  ;; doesn't return normally.
  ;;
  ;; Here, a "naive action" is a Scheme procedure that takes as its one argument
  ;; an operand tree, and either returns a result or causes a Scheme error.
  ;; (Recall that an action takes three arguments:  operand-tree, environment,
  ;; and context.)
  ;;
  ;; The constructed action ignores its second and third arguments (environment
  ;; and context), passes its first argument to the naive action, and returns the
  ;; normal result of the naive action.  If a Scheme error occurs during the call
  ;; to the naive action, the full action attempts to intercept the Scheme error
  ;; (by means of dynamic-wind) and throw a Kernel error in its place, using the
  ;; provided error-descriptor-line.
  ;;
  ;; There isn't anything in the R5RS that requires dynamic-wind to intercept
  ;; error-signals, although it does in MzScheme (version 103);; if dynamic-wind
  ;; doesn't intercept error-signals, then errors in the naive action will crash
  ;; the Kernel interpreter.
  ;;
  (define naive->action
    (lambda (naive name)
      (lambda (operand-tree env context)
        (let ((completed  #f))
          (dynamic-wind
              (lambda () '())
              (lambda () (let ((result  (naive operand-tree)))
                           (set! completed #t)
                           result))
              (lambda () (if (not completed)
                             (error-pass (make-error-descriptor
                                          (list "Error when calling primitive "
                                                name))
                                         context))))))))

  ;;
  ;; Given an action, and criteria for admissible operand-lists for that action,
  ;; constructs an operative that checks its operand-tree for those criteria,
  ;; and either invokes the given action, or throws an error.
  ;;
  ;; The first argument is the action to be safeguarded, and the second and later
  ;; arguments are as the second and later arguments to check-operand-list.
  ;;
  (define action->checked-operative
    (lambda (action . criteria)
      (letrec ((this  (action->operative
                       (lambda (operand-tree env context)
                         (let ((result  (apply check-operand-list
                                               operand-tree criteria)))
                           (if (string? result)
                               (error-pass
                                (make-error-descriptor
                                 (list result " when calling "
                                       (describe-object this))
                                 (list "Operand tree: " (list operand-tree)))
                                context)
                               (action operand-tree env context)))))))
        this)))

  ;;
  ;; metered-action->checked-operative
  ;;
  ;; As action->checked-operative, except that the first argument passed to the
  ;; action is the cons of the list metrics of the operand tree with the operand
  ;; tree.  (That is, the car of the first argument is the list metrics of the
  ;; tree, and the cdr of the first argument is the operand tree.)  This allows
  ;; the action to know the shape of the operand tree without a redundant call to
  ;; get-list-metrics.
  ;;
  (define metered-action->checked-operative
    (lambda (action . criteria)
      (letrec ((this  (action->operative
                       (lambda (operand-tree env context)
                         (let ((result  (apply check-operand-list
                                               operand-tree criteria)))
                           (if (string? result)
                               (error-pass
                                (make-error-descriptor
                                 (list result " when calling "
                                       (describe-object this))
                                 (list "Operand tree: " (list operand-tree)))
                                context)
                               (action (cons result operand-tree)
                                       env context)))))))
        this)))

  ;;
  ;; naive->checked-operative
  ;;
  ;; As action->checked-operative, except that it's given a naive action and a
  ;; name, instead of an action.
  ;;
  ;; This is the composition of naive->action with action->checked-operative.
  ;;
  (define naive->checked-operative
    (lambda (naive name . criteria)
      (apply action->checked-operative
             (naive->action naive name)
             criteria)))

  ;;
  ;; metered-naive->checked-operative
  ;;
  ;; As naive->checked-operative, except that the single argument passed to the
  ;; naive action is the cons of the list metrics of the operand tree with the
  ;; operand tree.  This is the composition of naive->action with
  ;; metered-action->checked-operative.
  ;;
  (define metered-naive->checked-operative
    (lambda (naive name . criteria)
      (apply metered-action->checked-operative
             (naive->action naive name)
             criteria)))

  ;;
  ;; Given a Scheme unary predicate, returns an operative that determines whether
  ;; the predicate returns true on all of the operands.
  ;;
  ;; The predicate must not throw a Scheme error.
  ;;
  (define unary-predicate->operative
    (lambda (unary)

      (define aux
        (lambda (n operands)
          (cond ((<= n 0)  #t)
                ((not (unary (kernel-car operands)))  #f)
                (else  (aux (- n 1) (kernel-cdr operands))))))

      (metered-action->checked-operative
       (lambda (x env context)
         (aux (caar x) (cdr x)))
       0 -1)))

  ;;
  ;; Given a Scheme binary predicate and a type predicate that must be satisfied
  ;; by all arguments to the predicate, returns an operative that determines
  ;; whether the Scheme predicate returns true on all consecutive operands (i.e.,
  ;; the first and second, second and third, etc.).
  ;;
  ;; The predicate must not throw a Scheme error, but it may return an error
  ;; message string instead of a boolean.
  ;;
  (define binary-predicate->operative
    (lambda (binary type?)
      (define this
        (metered-action->checked-operative
         (lambda (x env context)
           (let ((p  (car (car x)))
                 (c  (cadddr (car x)))
                 (operand-tree  (cdr x)))

             (define aux
               (lambda (n operands)
                 (if (<= n 1)
                     #t
                     (let ((result  (binary (kernel-car operands)
                                            (kernel-cadr operands))))
                       (if (string? result)
                           (error-pass
                            (make-error-descriptor
                             (list result " when calling primitive "
                                   (describe-object this))
                             (list "Failed comparing objects:  "
                                   (list (kernel-car operands)) "  "
                                   (list (kernel-cadr operands)))
                             (list "Operand tree: " (list operand-tree)))
                            context)
                           (if (not result)
                               #f
                               (aux (- n 1) (kernel-cdr operands))))))))

             (aux (+ p (if (> c 0) 1 0))
                  operand-tree)))

         0 -1 type?))

      this))

  ;;
  ;; Given a procedure with Scheme-style interface (that either returns a result
  ;; or causes a Scheme error), a Scheme-style argument list to be passed to it,
  ;; Kernel error-descriptor-line, and context, applies the procedure to the
  ;; argument list, signaling an error on failure.
  ;;
  ;; Uses the same platform-dependent technique to capture Scheme errors as
  ;; does naive->action, q.v.
  ;;
  (define apply-safely
    (lambda (proc arg-list message context)
      (let ((completed  #f))
        (dynamic-wind
            (lambda () '())
            (lambda () (let ((result  (apply proc arg-list)))
                         (set! completed #t)
                         result))
            (lambda () (if (not completed)
                           (error-pass (make-error-descriptor message)
                                       context)))))))

  ;;
  ;; Evaluates a sequence of expressions, and returns the last result.
  ;; Used by both $vau and $sequence.
  ;;
  (define eval-sequence
    (lambda (operand-tree env context)
      (cond ((null? operand-tree)  inert)
            ((not (kernel-pair? operand-tree))
             (error-pass
              (make-error-descriptor
               "Non-list operand-tree when calling #[operative $sequence]")
              context))
            ((null? (kernel-cdr operand-tree))
             (kernel-eval (kernel-car operand-tree) env context))
            (else
             (kernel-eval          (kernel-car operand-tree) env context)
             (eval-sequence (kernel-cdr operand-tree) env context)))))

  (define make-meta
    (lambda (static parameters dynamic body)
      (kernel-list (kernel-cons 'static static)
                   (kernel-cons 'parameters parameters)
                   (kernel-cons 'dynamic dynamic)
                   (kernel-cons 'body body))))
  ;;
  ;; Creates bindings for this type in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the operative type.
  ;; It appears in this file, rather than in "subfiles/ground.scm", simply because
  ;; it is logically associated with the operative type.
  ;;
  (define bind-operative-primitives!
    (lambda (env)
      (add-bindings! env

        'operative?  (unary-predicate->applicative operative?)

        'meta (action->applicative
               (lambda (args env context)
                 (let ((combiner (kernel-car args)))
                   (if (operative? combiner)
                       (combiner 'meta)
                       (kernel-cons 'applicative (unwrap combiner))))))

        '$vau
        (action->checked-operative
         (lambda (operand-tree static-env context)
           (let ((parameter-tree  (copy-es-immutable
                                   (kernel-car  operand-tree)))
                 (env-parameter   (kernel-cadr operand-tree))
                 (body            (copy-es-immutable
                                   (kernel-cddr operand-tree))))
             (letrec ((this
                       (action->meta-operative
                        (make-meta static-env parameter-tree env-parameter body)
                        (lambda (operand-tree dynamic-env context)
                          (let ((local-env  (make-environment static-env)))
                            (suggest-object-name local-env this)
                            (let ((ed  (match! local-env
                                               (kernel-cons parameter-tree env-parameter)
                                               (kernel-cons operand-tree   dynamic-env))))
                              (if (error-descriptor? ed)
                                  (begin
                                    (error-add-to-first-line!  ed
                                                               " when calling "
                                                               (describe-object this))
                                    (error-pass ed context))
                                  (eval-sequence body local-env context))))))))
               this)))
         3 3)
        ;; changing these numbers from "3 3" to "2 -1" enables compound bodies

        )))

  ;;
  ;; A kernel-input-port has type 'input-port, and attribute 'input-port whose
  ;; value is a Scheme input-port.  A kernel-output-port has type 'output-port,
  ;; and attribute 'output-port whose value is a Scheme output-port.
  ;;

  (define make-kernel-input-port
    (lambda (scheme-input-port)
      (let ((name  (list #t)))
        (lambda (message)
          (case message
            ((type)       'input-port)
            ((name)       name)
            ((input-port) scheme-input-port))))))

  (define make-kernel-output-port
    (lambda (scheme-output-port)
      (let ((name  (list #t)))
        (lambda (message)
          (case message
            ((type)        'output-port)
            ((name)        name)
            ((output-port) scheme-output-port))))))

  (define kernel-input-port?  (make-object-type-predicate 'input-port))
  (define kernel-output-port? (make-object-type-predicate 'output-port))

  ;;
  ;; Opens a Kernel port, or signals an error.
  ;;

  (define open-kernel-input-file
    (lambda (name context)
      (make-kernel-input-port
       (apply-safely
        open-input-file
        (list name)
        (string-append "Cannot open file for input: \"" name "\"")
        context))))

  (define open-kernel-output-file
    (lambda (name context)
      (make-kernel-output-port
       (apply-safely
        open-output-file
        (list name)
        (string-append "Cannot open file for output: \"" name "\"")
        context))))

  ;;
  ;; Closes a Kernel port, or signals an error.
  ;;

  (define close-kernel-input-port
    (lambda (kip context)
      (apply-safely
       close-input-port
       (list (kip 'input-port))
       (list "Cannot close " (list kip))
       context)))

  (define close-kernel-output-port
    (lambda (kop context)
      (apply-safely
       close-output-port
       (list (kop 'output-port))
       (list "Cannot close " (list kop))
       context)))

  ;;
  ;; Performs i/o on a Kernel port, or signals an error.
  ;;

  (define kernel-read
    (lambda (kip context)
      (apply-safely
       (lambda (inport) (scheme-read-object->kernel (read inport)))
       (list (kip 'input-port))
       (list "Failure during read, " (list kip))
       context)))

  (define kernel-read-char
    (lambda (kip context)
      (apply-safely
       read-char
       (list (kip 'input-port))
       (list "Failure during read-char, " (list kip))
       context)))

  (define kernel-peek-char
    (lambda (kip context)
      (apply-safely
       peek-char
       (list (kip 'input-port))
       (list "Failure during peek-char, " (list kip))
       context)))

  (define kernel-char-ready?
    (lambda (kip context)
      (apply-safely
       char-ready?
       (list (kip 'input-port))
       (list "Failure during char-ready?, " (list kip))
       context)))

  (define kernel-write
    (lambda (value kop context)
      (apply-safely
       write-tree
       (list value (kop 'output-port))
       (list "Failure during write, " (list kop))
       context)))

  (define kernel-display
    (lambda (value kop context)
      (apply-safely
       display-tree
       (list value (kop 'output-port))
       (list "Failure during display, " (list kop))
       context)))

  (define kernel-newline
    (lambda (kop context)
      (apply-safely
       newline
       (list (kop 'output-port))
       (list "Failure during newline, " (list kop))
       context)))

  (define kernel-write-char
    (lambda (char kop context)
      (apply-safely
       write-char
       (list char (kop 'output-port))
       (list "Failure during write-char, " (list kop))
       context)))

  ;;
  ;; Dynamic-binders, accessors, and top-level-alist constructor
  ;; for the Kernel current-input-port and current-output-port.
  ;;

  (define get-kernel-current-input-port  '())
  (define get-kernel-current-output-port '())

  (define call-with-input-context  '())
  (define call-with-output-context '())

  (define make-top-level-ports-alist '())

  (define i0
    (let ((make-top-level-input-port-alist  '())
          (make-top-level-output-port-alist  '()))

      (let ((kip-key  (get-fresh-key)))

        (set! get-kernel-current-input-port
              (lambda (context)
                (context-keyed-lookup kip-key context)))

        (set! call-with-input-context
              (lambda (proc parent kip)
                (call-with-keyed-context proc parent kip-key kip)))

        (set! make-top-level-input-port-alist
              (lambda ()
                (let ((kip  (make-kernel-input-port (current-input-port))))
                  (suggest-object-name kip "standard-input-port")
                  (make-alist
                   '()
                   kip-key
                   kip)))))

      (let ((kop-key  (get-fresh-key)))

        (set! get-kernel-current-output-port
              (lambda (context)
                (context-keyed-lookup kop-key context)))

        (set! call-with-output-context
              (lambda (proc parent kop)
                (call-with-keyed-context proc parent kop-key kop)))

        (set! make-top-level-output-port-alist
              (lambda ()
                (let ((kop  (make-kernel-output-port (current-output-port))))
                  (suggest-object-name kop "standard-output-port")
                  (make-alist
                   '()
                   kop-key
                   kop)))))

      (set! make-top-level-ports-alist
            (lambda ()
              (append (make-top-level-input-port-alist)
                      (make-top-level-output-port-alist))))))

  ;;
  ;; Creates bindings for these types in a given environment.
  ;;
  ;; This code should not use any internal knowledge of the kernel port types.
  ;; It appears in this file, rather than in "subfiles/ground.scm", simply
  ;; because it is logically associated with the kernel port types.
  ;;
  (define bind-port-primitives!
    (lambda (env)
      (add-bindings! env

        'input-port?
        (unary-predicate->applicative  kernel-input-port?)

        'output-port?
        (unary-predicate->applicative  kernel-output-port?)

        'open-input-file
        (action->checked-applicative
         (lambda (operand-tree env context)
           (open-kernel-input-file (kernel-car operand-tree) context))
         1 1 string?)

        'open-output-file
        (action->checked-applicative
         (lambda (operand-tree env context)
           (open-kernel-output-file (kernel-car operand-tree) context))
         1 1 string?)

        'close-input-port
        (action->checked-applicative
         (lambda (operand-tree env context)
           (close-kernel-input-port (kernel-car operand-tree) context)
           inert)
         1 1 kernel-input-port?)

        'close-output-port
        (action->checked-applicative
         (lambda (operand-tree env context)
           (close-kernel-output-port (kernel-car operand-tree) context)
           inert)
         1 1 kernel-output-port?)

        'read
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-read
            (if (null? operand-tree)
                (get-kernel-current-input-port context)
                (kernel-car operand-tree))
            context))
         0 1 kernel-input-port?)

        'read-char
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-read-char
            (if (null? operand-tree)
                (get-kernel-current-input-port context)
                (kernel-car operand-tree))
            context))
         0 1 kernel-input-port?)

        'peek-char
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-peek-char
            (if (null? operand-tree)
                (get-kernel-current-input-port context)
                (kernel-car operand-tree))
            context))
         0 1 kernel-input-port?)

        'char-ready?
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-char-ready?
            (if (null? operand-tree)
                (get-kernel-current-input-port context)
                (kernel-car operand-tree))
            context))
         0 1 kernel-input-port?)

        'write
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-write
            (kernel-car operand-tree)
            (if (null? (kernel-cdr operand-tree))
                (get-kernel-current-output-port context)
                (kernel-cadr operand-tree))
            context)
           inert)
         1 2 any? kernel-output-port?)

        'display
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-display
            (kernel-car operand-tree)
            (if (null? (kernel-cdr operand-tree))
                (get-kernel-current-output-port context)
                (kernel-cadr operand-tree))
            context)
           inert)
         1 2 any? kernel-output-port?)

        'newline
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-newline
            (if (null? operand-tree)
                (get-kernel-current-output-port context)
                (kernel-car operand-tree))
            context)
           inert)
         0 1 kernel-output-port?)

        'write-char
        (action->checked-applicative
         (lambda (operand-tree env context)
           (kernel-write-char
            (kernel-car operand-tree)
            (if (null? (kernel-cdr operand-tree))
                (get-kernel-current-output-port context)
                (kernel-cadr operand-tree))
            context)
           inert)
         1 2 char? kernel-output-port?)

        'get-current-input-port
        (action->checked-applicative
         (lambda (operand-tree env context)
           (get-kernel-current-input-port context))
         0 0)

        'get-current-output-port
        (action->checked-applicative
         (lambda (operand-tree env context)
           (get-kernel-current-output-port context))
         0 0)

        'with-input-from-file
        (action->checked-applicative
         (lambda (operand-tree env context)
           (let* ((name      (kernel-car operand-tree))
                  (combiner  (kernel-cadr operand-tree))
                  (kip       (open-kernel-input-file name context))
                  (result    (call-with-input-context
                              (lambda (context)
                                (combine combiner '() env context))
                              context
                              kip)))
             (close-kernel-input-port kip context)
             result))
         2 2 string? combiner?)

        'with-output-to-file
        (action->checked-applicative
         (lambda (operand-tree env context)
           (let* ((name      (kernel-car operand-tree))
                  (combiner  (kernel-cadr operand-tree))
                  (kop       (open-kernel-output-file name context))
                  (result    (call-with-output-context
                              (lambda (context)
                                (combine combiner '() env context))
                              context
                              kop)))
             (close-kernel-output-port kop context)
             result))
         2 2 string? combiner?)

        )))

  ;;
  ;; Kernel treats cyclic structures of kernel-pairs (such as cyclic lists) as
  ;; first-class objects, by guaranteeing that each standard combiner will handle
  ;; cyclic structures in finite time whenever that behavior is consistent with
  ;; the intended semantics of the combiner.
  ;;
  ;; The tools in this file help SINK to handle cyclic structures.  However,
  ;; despite the availability of these tools, at last check SINK did not (yet)
  ;; handle cyclic structures in all cases required by Kernel.
  ;;
  ;; The tools here do not use any internal knowledge of the kernel-pair type.
  ;; Cycle-related tools that do use internal knowledge of that type are in file
  ;; "subfiles/kernel-pair.scm".
  ;;
  ;; A kernel-tree is called simply a "tree", because the interpreter has no
  ;; occasion to use Scheme trees.  A kernel-pair may be visited more than once
  ;; during normal (left-to-right, depth first) traversal of a tree without
  ;; constituting a cycle, so long as the revisited kernel-pair isn't a
  ;; descendant of itself.
  ;;
  ;; Even if all kernel-pairs were known to be represented by pairs (which, if it
  ;; were true, should only be known in "subfiles/kernel-pair.scm"), it would be
  ;; necessary to handle them with tongs in Scheme, because Scheme doesn't grant
  ;; first-class status to cyclic pair-structures.  Notably, the argument list of
  ;; a procedure cannot be cyclic.  In Kernel, of course, there is no difficulty
  ;; in using a cyclic argument list (or operand list).
  ;;

  ;;
  ;; Given improper kernel-list ls and nonnegative integer k, returns the
  ;; kernel-car of the (k)th kernel-cdr of ls.  Thus, if k=0, returns the
  ;; kernel-car of ls;; if k=1, returns the kernel-cadr of ls;; and so on.
  ;;
  (define kernel-list-ref
    (lambda (ls k)
      (kernel-car (kernel-list-tail ls k))))


  ;;
  ;; Given a value, determines whether that value is a finite list.
  ;;
  (define finite-list?
    (lambda (ls)
      (> (cadr (get-list-metrics ls)) 0)))

  ;;
  ;; Given a value, determines whether that value is a cyclic list.
  ;;
  (define cyclic-list?
    (lambda (ls)
      (> (cadddr (get-list-metrics ls)) 0)))

  ;;
  ;; Given a nonempty kernel-list of kernel-lists lss, constructs a
  ;; finite mutable kernel-list whose n^th element is a mutable kernel-list of
  ;; the n^th elements of the kernel-lists in lss;; each element of the resultant
  ;; kernel-list has the topological structure of lss, and the length of the
  ;; resultant kernel-list is just large enough to include every combination of
  ;; elements from the kernel-lists in lss.  The result returned is a list whose
  ;; first element is the resultant kernel-list, and whose second and third
  ;; elements are the acyclic prefix length and cycle length that would encycle
  ;; the resultant kernel-list to be traversal-isomorphic to the infinite
  ;; transpose of lss.  If the kernel-lists in lss don't all have the same
  ;; length, an error-message string is returned.
  ;;
  ;;       (transpose-lists '{{1 2 3} {4 5 6}})
  ;;   ==>
  ;;       ({{1 4} {2 5} {3 6}} 3 0)
  ;;
  ;;       (transpose-lists '#0={{1 #1={2 3 . #1#}} {4 5 #2={6 . #2#}} . #0#})
  ;;   ==>
  ;;       ({#0={1 4 . #0#} #1={2 5 . #1#} #2={3 6 . #2#} #3={2 6 . #3#}} 2 2)
  ;;
  (define transpose-lists
    (lambda (lss)
      (define bounded-simple-map       (make-bounded-simple-map kernel-cons))
      (define bounded-simple-map->list (make-bounded-simple-map cons))

      (define get-results-metrics
        (lambda (so-far remaining)
          (if (null? remaining)
              so-far
              (let ((next       (car remaining))
                    (remaining  (cdr remaining)))
                (let ((sa  (caddr so-far))
                      (sc  (cadddr so-far))
                      (na  (caddr next))
                      (nc  (cadddr next)))
                  (if (or (not (eq? (zero? sc) (zero? nc)))
                          (and (zero? sc) (zero? nc) (not (= sa na))))
                      "lists don't have the same length"
                      (let ((a  (max sa na))
                            (c  (if (zero? sc) sc (lcm sc nc))))
                        (get-results-metrics (list (+ a c) (cadr so-far) a c)
                                             remaining))))))))

      (define aux
        (lambda (k lss p a c)

          (if (<= k 0)
              '()
              (let ((x  (bounded-simple-map p kernel-car lss))
                    (y  (bounded-simple-map p kernel-cdr lss)))
                (kernel-encycle! x a c)
                (kernel-cons x (aux (- k 1) y p a c))))))

      (let* ((lss-metrics  (get-list-metrics lss))
             (lss-p        (car lss-metrics))
             (lss-a        (caddr lss-metrics))
             (lss-c        (cadddr lss-metrics)))
        (let* ((metrics-list  (bounded-simple-map->list
                               lss-p get-list-metrics lss))
               (results-metrics  (get-results-metrics (car metrics-list)
                                                      (cdr metrics-list))))
          (if (string? results-metrics)
              results-metrics
              (let ((rp  (car results-metrics))
                    (ra  (caddr results-metrics))
                    (rc  (cadddr results-metrics)))
                (list (aux rp lss lss-p lss-a lss-c)
                      ra rc)))))))

  ;;
  ;; Given procedure proc and nonempty kernel-list of kernel-lists lss,
  ;; repeatedly calls proc with a single mutable kernel-list argument constructed
  ;; by taking the n^th elements of each kernel-list in lss, for n from 1 to a
  ;; large enough number to cover every combination of positions in the different
  ;; kernel-lists.  Each argument has the topological structure of lss.  Returns
  ;; a mutable kernel-list of the results of the calls to proc, with appropriate
  ;; topological structure.  If the kernel-lists in lss have different lengths,
  ;; the operation cannot be performed correctly, so an error-message string is
  ;; returned instead.
  ;;
  ;;       (full-map (lambda (x) (apply + x)) '{{1 2 3} {4 5 6}})
  ;;   ==>
  ;;       {5 7 9}
  ;;
  ;;       (full-map (lambda (x) (apply + x))
  ;;                 '{{1 #0={2 3 . #0#}} {4 5 #1={6 7 8 . #1#}}})
  ;;   ==>
  ;;       {5 7 #0={9 9 11 8 10 10 . #0#}}
  ;;
  (define full-map
    (lambda (proc lss)
      (define bounded-simple-map       (make-bounded-simple-map kernel-cons))

      (let ((x  (transpose-lists lss)))
        (if (string? x)
            x
            (let ((ls  (car x))
                  (a   (cadr x))
                  (c   (caddr x)))
              (let ((ls  (bounded-simple-map (+ a c) proc ls)))
                (kernel-encycle! ls a c)
                ls))))))

  ;;
  ;; Given two structures x and y, either of which may be cyclic, determine
  ;; whether they are equal?.
  ;;
  ;; A table is maintained to keep track of which constituents (kernel-pairs) of
  ;; x do not have to be compared again to which constituents of y.  The table
  ;; is a list;; each element of this list is a pair, whose first element is a
  ;; constituent of x, and whose subsequent elements are constituents of y that
  ;; don't have to be recompared to it.
  ;;
  ;; There is no call for this tool to use encapsulated knowledge about the
  ;; kernel-pair type, because marking individual kernel-pairs wouldn't help.
  ;;
  (define kernel-equal?
    (lambda (x y)

      (define table '())

      (define get-row
        (lambda (x)
          (let ((row  (assq x table)))
            (if (pair? row)
                row
                (let ((row  (list x)))
                  (set! table (cons row table))
                  row)))))

      (define is-in-row?
        (lambda (y row)
          (if (pair? (memq y row))
              #t
              (begin
                (set-cdr! row (cons y (cdr row)))
                #f))))

      (define aux
        (lambda (x y)
          (cond ((and (kernel-pair? x) (kernel-pair? y))
                 (if (is-in-row? y (get-row x))
                     #t
                     (and (aux (kernel-car x) (kernel-car y))
                          (aux (kernel-cdr x) (kernel-cdr y)))))
                ((and (kernel-number? x) (kernel-number? y))
                 (kernel-=? x y))
                ((and (string? x) (string? y))
                 (string=? x y))
                (else
                 (eq? x y)))))

      (aux x y)))

  ;;
  ;; Creates bindings for handling cyclic structures in a given environment.
  ;;
  (define bind-cyclic-primitives!
    (lambda (env)
      (add-bindings! env

        ;; 'get-list-metrics
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (list->kernel-list (get-list-metrics (kernel-car operand-tree))))
        ;;   1 1)

        ;; 'finite-list?
        ;; (unary-predicate->applicative finite-list?)

        ;; 'countable-list?
        ;; (unary-predicate->applicative kernel-list?)

        ;; 'member?
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (let* ((object (kernel-car operand-tree))
        ;;            (ls     (kernel-cadr operand-tree))
        ;;            (p      (car (get-list-metrics ls))))
        ;;       (letrec ((aux?  (lambda (k ls)
        ;;                         (if (<= k 0)
        ;;                             #f
        ;;                             (or (kernel-equal? object (kernel-car ls))
        ;;                                 (aux? (- k 1) (kernel-cdr ls)))))))
        ;;         (aux? p ls))))
        ;;   2 2 any? kernel-list?)

        ;; 'memq?
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (let* ((object (kernel-car operand-tree))
        ;;            (ls     (kernel-cadr operand-tree))
        ;;            (p      (car (get-list-metrics ls))))
        ;;       (letrec ((aux?  (lambda (k ls)
        ;;                         (if (<= k 0)
        ;;                             #f
        ;;                             (or (eq? object (kernel-car ls))
        ;;                                 (aux? (- k 1) (kernel-cdr ls)))))))
        ;;         (aux? p ls))))
        ;;   2 2 any? kernel-list?)

        ;; 'list-tail
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (let* ((ls  (kernel-car operand-tree))
        ;;            (k   (kernel-cadr operand-tree))
        ;;            (p   (car (get-list-metrics ls))))
        ;;       (if (< p k)
        ;;           (error-pass (make-error-descriptor
        ;;                         (list "List isn't long enough"
        ;;                               " when calling #[operative list-tail]")
        ;;                         (list "Operand tree: " (list operand-tree)))
        ;;                       context)
        ;;           (kernel-list-tail ls k))))
        ;;   2 2 kernel-list? integer?)

        ;; 'list-ref
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (let* ((ls  (kernel-car operand-tree))
        ;;            (k   (kernel-cadr operand-tree))
        ;;            (p   (car (get-list-metrics ls))))
        ;;       (if (<= p k)
        ;;           (error-pass (make-error-descriptor
        ;;                         (list "List isn't long enough"
        ;;                               " when calling #[operative list-ref]")
        ;;                         (list "Operand tree: " (list operand-tree)))
        ;;                       context)
        ;;           (kernel-list-ref ls k))))
        ;;   2 2 kernel-list? integer?)

        ;; 'encycle!
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (let* ((ls  (kernel-car operand-tree))
        ;;            (a   (kernel-cadr operand-tree))
        ;;            (c   (kernel-caddr operand-tree))
        ;;            (p   (car (get-list-metrics ls))))
        ;;       (cond ((< c 1)  '())
        ;;             ((< p (+ a c))
        ;;                (error-pass (make-error-descriptor
        ;;                              (list "List isn't long enough"
        ;;                                    " when calling #[operative encycle!]")
        ;;                              (list "Operand tree: " (list operand-tree)))
        ;;                            context))
        ;;             ((immutable? (kernel-list-tail ls (+ a c -1)))
        ;;                (error-pass (make-error-descriptor
        ;;                              (list "Target is immutable"
        ;;                                    " when calling #[operative encycle!]")
        ;;                              (list "Operand tree: " (list operand-tree)))
        ;;                            context))
        ;;             (else  (kernel-encycle! ls a c))))
        ;;     inert)
        ;;   3 3 any? integer? integer?)

        ;; 'map
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;     (let ((combiner  (unwrap (kernel-car operand-tree)))
        ;;           (lss       (kernel-cdr operand-tree)))
        ;;       (let ((result  (full-map (lambda (args)
        ;;                                  (eval (kernel-cons combiner args)
        ;;                                        env context))
        ;;                                lss)))
        ;;         (if (string? result)
        ;;             (error-pass
        ;;               (make-error-descriptor
        ;;                 (list result ", when calling #[operative map]"))
        ;;               context)
        ;;             result))))
        ;;   2 -1 applicative? kernel-list?)

    ;;;;;;;;;;;;;;;;;;;;;;;; doesn't look right
        ;; 'append
        ;; (action->checked-applicative
        ;;   (lambda (operand-tree env context)
        ;;
        ;;     (define mutable-finite-list?
        ;;       (lambda (ls)
        ;;         (let* ((metrics  (get-list-metrics ls))
        ;;                (p        (car metrics))
        ;;                (c        (cadddr metrics)))
        ;;           (and (zero? c)
        ;;                (or (zero? p)
        ;;                    (mutable? (kernel-list-tail ls (- p 1))))))))
        ;;
        ;;     (define check-operands
        ;;       (lambda (n k operands)
        ;;         (if (>= n k)
        ;;             (if (mutable-finite-list? (kernel-car operands))
        ;;                 (check-operands n (+ k 1) (kernel-cdr operands))
        ;;                 (error-pass
        ;;                   (make-error-descriptor
        ;;                     (string-append "Operand #" (number->string k)
        ;;                       (if (finite-list? (kernel-car operands))
        ;;                           " is immutable"
        ;;                           " has wrong type")
        ;;                       " when calling #[operative append]")
        ;;                     (list "Operand tree: " (list operand-tree)))
        ;;                   context)))))
        ;;
        ;;     (define binary-append
        ;;       (lambda (x y)
        ;;         (if (null? x)
        ;;             y
        ;;             (cons (kernel-car x)
        ;;                   (binary-append (kernel-cdr x) y)))))
        ;;
        ;;     (define bounded-append
        ;;       (lambda (k lss)
        ;;         (if (<= k 0)
        ;;             '()
        ;;             (binary-append (kernel-car lss)
        ;;                            (bounded-append (- k 1) (kernel-cdr lss))))))
        ;;
        ;;     (define finite-append
        ;;       (lambda (lss)
        ;;         (if (null? lss)
        ;;             '()
        ;;             (let ((ls   (kernel-car lss))
        ;;                   (lss  (kernel-cdr lss)))
        ;;               (if (null? lss)
        ;;                   ls
        ;;                   (binary-append ls (finite-append lss)))))))
        ;;
        ;;     (define set-last!
        ;;       (lambda (x y)
        ;;         (if (null? (kernel-cdr x))
        ;;             (kernel-set-cdr! x y)
        ;;             (set-last! (kernel-cdr x) y))))
        ;;
        ;;     (let* ((metrics  (get-list-metrics operand-tree))
        ;;            (p        (car metrics))
        ;;            (a        (caddr metrics))
        ;;            (c        (cadddr metrics)))
        ;;       (if (zero? c)
        ;;           (begin
        ;;             (check-operands (- p 1) 1 operand-tree)
        ;;             (finite-append operand-tree))
        ;;           (begin
        ;;             (check-operands p 1 operand-tree)
        ;;             (let ((cycle  (bounded-append c (kernel-list-tail
        ;;                                               operand-tree a))))
        ;;               (set-last! cycle cycle)
        ;;               (if (zero? a)
        ;;                   cycle
        ;;                   (let ((acyclic-prefix
        ;;                           (bounded-append a operand-tree)))
        ;;                     (set-last! acyclic-prefix cycle)
        ;;                     acyclic-prefix)))))))
        ;;   0 -1)
    ;;;;;;;;;;;;;;;;;;;;;;;;

        'equal?  (binary-predicate->applicative  kernel-equal?  any?)

        )))

  (define seed-exec
    (lambda (filename)

      ;;
      ;; The ground environment contains bindings for all built-in combiners.
      ;;

      (define ground-environment (make-environment))

      ;;
      ;; The primitive bindings.
      ;;
      ;; Many are enumerated here, especially those that are imported to Kernel from
      ;; Scheme and those that aren't strongly associated with one of the other files.
      ;; Others are handled by initializer procedures that were defined elsewhere.
      ;;
      (add-bindings! ground-environment

        ;; 'combiner?   (unary-predicate->applicative  combiner?)

        'char?       (unary-predicate->applicative  char?)
        'eof-object? (unary-predicate->applicative  eof-object?)
        'eq?         (binary-predicate->applicative eq?          any?)
        'null?       (unary-predicate->applicative  null?)
        'string?     (unary-predicate->applicative  string?)
        'symbol?     (unary-predicate->applicative  symbol?)

        'string=?     (binary-predicate->applicative  string=?      string?)
        'string<?     (binary-predicate->applicative  string<?      string?)
        'string>?     (binary-predicate->applicative  string>?      string?)
        'string<=?    (binary-predicate->applicative  string<=?     string?)
        'string>=?    (binary-predicate->applicative  string>=?     string?)
        'string-ci=?  (binary-predicate->applicative  string-ci=?   string?)
        'string-ci<?  (binary-predicate->applicative  string-ci<?   string?)
        'string-ci>?  (binary-predicate->applicative  string-ci>?   string?)
        'string-ci<=? (binary-predicate->applicative  string-ci<=?  string?)
        'string-ci>=? (binary-predicate->applicative  string-ci>=?  string?)

        'string-append
        (naive->checked-applicative
         (lambda (operand-tree)
           (apply string-append
                  (copy-kernel-list->list operand-tree)))
         "string-append"
         0 -1 string?)

        'number->string
        (naive->checked-applicative
         (lambda (operand-tree)
           (let ((number  (kernel-car operand-tree)))
             (if (object? number)
                 (string-copy (describe-object number))
                 (number->string number))))
         "number->string"
         1 1 kernel-number?)

        'list->string
        (naive->checked-applicative
         (lambda (operand-tree)
           (list->string (kernel-list->list (kernel-car operand-tree))))
         "list->string"
         1 1 kernel-list?)

        'integer->char
        (naive->checked-applicative
         (lambda (operand-tree)
           (integer->char (kernel-car operand-tree)))
         "integer->char"
         1 1 integer?)

        'char->integer
        (naive->checked-applicative
         (lambda (operand-tree)
           (char->integer (kernel-car operand-tree)))
         "char->integer"
         1 1 char?)

;;;;;;;;;;;;;;;;;;;;;;;; doesn't look right
        ;;  'assoc
        ;;  (naive->checked-applicative
        ;;    (lambda (operand-tree)
        ;;      (let* ((key     (kernel-car operand-tree))
        ;;             (alist   (kernel-cadr operand-tree))
        ;;             (result  (assoc key (kernel-list->list alist))))
        ;;        (if (pair? result)
        ;;            result
        ;;            '())))
        ;;    "assoc"
        ;;    2 2 any? kernel-list?)
;;;;;;;;;;;;;;;;;;;;;;;;

        ;;  'assq
        ;;  (naive->checked-applicative
        ;;    (lambda (operand-tree)
        ;;      (let* ((key     (kernel-car operand-tree))
        ;;             (alist   (kernel-cadr operand-tree))
        ;;             (result  (assq key (kernel-list->list alist))))
        ;;        (if (pair? result)
        ;;            result
        ;;            '())))
        ;;    "assq"
        ;;    2 2 any? kernel-list?)

        ;; '$sequence
        ;; (action->operative eval-sequence)

        'load
        (action->checked-applicative
         (lambda (operand-tree env context)
           (let* ((filename  (kernel-car operand-tree))
                  (kip       (open-kernel-input-file filename context)))
             (suggest-object-name kip (string-append "\"" filename "\""))
             (call-with-guarded-context
              (lambda (context)
                (letrec ((aux  (lambda (legacy)
                                 (let ((object  (copy-es-immutable
                                                 (kernel-read kip context))))
                                   (if (eof-object? object)
                                       (begin
                                         (close-kernel-input-port kip context)
                                         legacy)
                                       (aux (kernel-eval object env context)))))))
                  (aux inert)))
              context
              (list (cons '()
                          (lambda (v)
                            (error-pass
                             (make-error-descriptor
                              (list "Tried to reenter dynamic extent of load \""
                                    filename "\"")
                              (list "  Value sent: " (list v)))
                             context))))
              (list (cons '()
                          (lambda (v)
                            (close-kernel-input-port kip context)
                            v))))))
         1 1 string?)

        )
      
      (bind-applicative-primitives!      ground-environment)
      (bind-boolean-primitives!          ground-environment)
      (bind-context-primitives!          ground-environment)
      (bind-cyclic-primitives!           ground-environment)
      (bind-encapsulation-primitives!    ground-environment)
      (bind-environment-primitives!      ground-environment)
      (bind-error-descriptor-primitives! ground-environment)
      (bind-ignore-primitives!           ground-environment)
      (bind-inert-primitives!            ground-environment)
      (bind-kernel-pair-primitives!      ground-environment)
      (bind-keyed-variable-primitives!   ground-environment)
      (bind-number-primitives!           ground-environment)
      (bind-operative-primitives!        ground-environment)
      (bind-port-primitives!             ground-environment)

      (call-with-input-file filename
        (lambda (port)
          
          ;;
          ;; The library bindings.
          ;;
          ;; This code loads the Kernel library.  Since loading involves evaluation, it
          ;; has to create a top-level context, and in case an error message must be
          ;; generated during the load it also names the ground environment;; the code
          ;; is therefore rather similar to that of interpreter, in file
          ;; "subfiles/interpreter.scm".  After loading the library, bindings for
          ;; symbols "set-version" and "set-revision-date" are removed from the ground
          ;; environment (since they aren't meant to be available to Kernel programs).
          ;;

          (let ((okay  #t))
            (suggest-object-name ground-environment 'the-ground-environment)
            (let ((context  (make-top-level-context
                             (lambda (x)
                               (report-error x)
                               (set! okay #f)))))
              (if okay
                  (begin
                    (kernel-eval (list->kernel-list '(load "library.snk"))
                                 ground-environment context)
                    (let loop ()
                      (let ((sexp (scheme-read-object->kernel (read port))))
                        (unless (eof-object? sexp)
                          (kernel-eval sexp ground-environment context)
                          (loop))))))))

          (flush-output-port))))))
