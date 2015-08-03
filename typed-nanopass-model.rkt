#lang racket

(require redex)

(define-syntax quasiquote (make-rename-transformer #'term))
(define-syntax-rule (test-true arg)
  (test-equal arg #t))

;; ---------------------------------------------------------------------------------------------------

; Language describing typed nanopass
(define-language typed-nanopass
  (p (program e ...))
  (he (λ (x ...) he)
      (he he ...)
      (begin he ...)
      (if he he he)
      base
      x)
  (e (define-type pt he)
     (define-language l
       (lt lp ...) ...)
     (define-extended-language l l
       (lt (+ lp ...) (- lp ...)) ...)
     (define-pass (x (x : t) ...) (ret ...)
       (pr ((x : t) ...) (ret ...)
           [pp e ...] ...) ...
       b)
     (define-terms (x ...) e)
     (e e ...)
     (begin e ...)
     (term t pat)
     (new t he)
     x
     base)
  (b e #f)
  (ret [e : t] t)
  (t (→ (t ...) (t ...)) l (l lt) pt unit str num bool)
  (base string number boolean)
  ((x lt pt n l pr) variable-not-otherwise-mentioned)
  
  ;; Term patterns
  (pat (unterm e)
       (n pv ...))
  (pv (unterm e)
      x
      base
      ()
      (pv pve ...))
  (pve pv \\...)
  
  ;; Language Pattern
  (lp t (n lpv ...))
  (lpv t
       (lpv lpve ...))
  (lpve lpv \\...)
  
  ;; Pass pattern
  (pp (unterm e)
      (n ppv ...))
  (ppv x
       (unterm e)
       base
       ()
       (ppv ppve ...))
  (ppve ppv \\...))


(module+ test
  (test-true
   (redex-match? typed-nanopass p
                 `(program (define-type Integer integer?)
                           (define-language l
                             (Expr Integer)))))
  (test-true
   (redex-match? typed-nanopass p
                 `(program (define-type Integer integer?)
                           (define-language Lsrc
                             (Expr Integer
                                   (when0 Integer Integer)
                                   (if0 Integer Integer Integer)))
                           (define-extended-language Ltarget Lsrc
                             (Expr (+)
                                   (- (when0 Integer Integer))))
                           (define-pass (remove-when0 [e : Lsrc]) (Ltarget)
                             (mkExpr ([e : Expr]) (Expr)
                                     [(when0 (unterm cond) (unterm body))
                                      (term (Ltarget Expr) (if0 (unterm cond)
                                                                (unterm body)
                                                                0))])
                             #f))))
  
  (test-true
   (redex-match? typed-nanopass lp
                 `(let ([Variable Expr] \\...) Expr)))
  
  (test-true
   (redex-match? typed-nanopass e
                 `(term (Ltarget Expr)
                        (let ([(unterm x) (unterm expr)])
                          (unterm
                           (mkExpr
                            (term (Ltarget Expr)
                                  (let* ([(unterm x*) (unterm expr*)] \\...)
                                    (unterm (mkExpr body))))))))))

  (test-true
   (redex-match? typed-nanopass p
                 `(program (define-type Variable (λ (x) (or (symbol? x) (identifier? x))))
                           (define-language Lsrc
                             (Expr (let ([Variable Expr] \\...) Expr)
                                   (let* ([Variable Expr] \\...) Expr)))
                           (define-extended-language Ltarget Lsrc
                             (Expr (+)
                                   (- (let* ([Variable Expr] \\...) Expr))))
                           (define-pass (remove-let* [e : Lsrc]) (Ltarget)
                             (mkExpr ([e : Expr]) (Expr)
                                     [(let* () (unterm body))
                                      (term (Ltarget Expr) (let* () (unterm body)))]
                                     #;[(let* ([(unterm x) (unterm expr)]
                                             [(unterm x*) (unterm expr*)] \\...)
                                        body)
                                      (term (Ltarget Expr)
                                            (let ([(unterm x) (unterm expr)])
                                              (unterm
                                               (mkExpr
                                                (term (Ltarget Expr)
                                                      (let* ([(unterm x*) (unterm expr*)] \\...)
                                                        (unterm (mkExpr body))))))))])
                             #f)))))

;; ---------------------------------------------------------------------------------------------------

; Type environments for typed nanopass
(define-extended-language typed-nanopass+Γ typed-nanopass
  (Γ ((x : t) ...))
  (Σ (t ...))
  (Δ ((l : lt ...) ...)))

; Typing rules for typed nanopass
(define-judgment-form typed-nanopass+Γ
  #:mode (types I I I I O O O O)
  #:contract (types Γ Σ Δ e Γ Σ Δ (t ...))
  [(side-condition (valid-types Γ (pt t ...)))
   ------------------------------------------------------------- "define-type"
   (types Γ (t ...) Δ (define-type pt he) Γ (pt t ...) Δ (unit))]
  [(where ((n ...) ...) ((pattern-tags lp ...) ...))
   (where ((n_3 : t_3) ...) (splice-names ((n ...) ...) ((l lt) ...)))
   (side-condition (valid-types ((n_3 : t_3) ... (x : t_1) ...) (l (l lt) ... t_2 ...)))
   --------------------------------------------------------------------------------- "define-language"
   (types ((x : t_1) ...)
          (t_2 ...)
          ((l_3 : lt_3 ...) ...)
          (define-language l (lt lp ...) ...)
          ((n_3 : t_3) ... (x : t_1) ...)
          (l (l lt) ... t_2 ...)
          ((l : lt ...) (l_3 : lt_3 ...) ...)
          (unit))]
  [(where ((n ...) ...) ((pattern-tags lp ...) ...))
   (where ((n_3 : t_3) ...) (splice-names ((n ...) ...) ((l lt) ...)))
   (side-condition (valid-types ((x : t_1) ...) (t_2 ...)))
   --------------------------------------------------------------- "define-extended-language"
   (types ((x : t_1) ...)
          (t_2 ...)
          ((l_1 : lt_1 ...) ... (l_src : lt_src ...) (l_2 : lt_2) ...)
          (define-extended-langauge l l_src (lt lp ...) ...)
          ((n_3 : t_3) ... (x : t_1) ...)
          (l (l lt) ... (l lt_src) ... t_2 ...)
          ((l_1 : lt_1 ...) ... (l_src : lt ...) (l_2 : lt_2) ...)
          (unit))]
  [--------------------------------------------------- "define-pass"
   (types Γ
          Σ
          Δ
          (define-pass (p [x : t_in] ...) (ret ...) b)
          Γ
          Σ
          Δ
          (unit))]
  [(types ((x_1 : t_1) ...) Σ Δ e Γ_1 Σ_1 Δ_1 (t ...))
   (side-condition (valid-types ((x : t) ... (x_1 : t_1) ...) Σ))
   ------------------------------------------------------------------------------------- "define-term"
   (types ((x_1 : t_1) ...) Σ Δ (define-term (x ...) e) ((x : t) ... (x_1 : t_1) ...) Σ Δ (t ...))]
  [(side-condition (valid-types Γ Σ))
   ---------------------------- "new"
   (types Γ Σ Δ (new t he) Γ Σ Δ (t))]
  [(side-condition (valid-types Γ Σ))
   ------------------------------------ "term"
   (types Γ Σ Δ (term t pat) Γ Σ Δ (t))]
  [(side-condition (valid-types Γ Σ))
   ---------------------------------- "begin-0"
   (types Γ Σ Δ (begin) Γ Σ Δ (unit))]
  [(types Γ Σ Δ e Γ_1 Σ_1 Δ_1 (t ...))
   (side-condition (valid-types Γ Σ))
   ------------------------------------------- "begin-1"
   (types Γ Σ Δ (begin e) Γ_1 Σ_1 Δ_1 (t ...))]
  [(types Γ Σ Δ e_1 Γ_1 Σ_1 Δ_1 (t_1 ...))
   (types Γ_1 Σ_1 Δ_1 (begin e_2 e ...) Γ_2 Σ_2 Δ_2 (t ...))
   (side-condition (valid-types Γ Σ))
   --------------------------------------------------------- "begin-*"
   (types Γ Σ Δ (begin e_1 e_2 e ...) Γ_2 Σ_2 Δ_2 (t ...))]
  [(types Γ Σ Δ e Γ_1 Σ_1 Δ_1 (→ (t_1 ...) (t ...)))
   (types Γ Σ Δ e_1 Γ_2 Σ_2 Δ_2 (t_1)) ...
   (side-condition (valid-types Γ Σ))
   ------------------------------------------------- "application"
   (types Γ Σ Δ (e e_1 ...) Γ Σ Δ (t ...))]
  [(side-condition (valid-types ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...) Σ))
   -------------------------------------------------------------------------- "reference"
   (types ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...) Σ Δ x
          ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...) Σ Δ (t))]
  [(side-condition (valid-types Γ Σ))
   ---------------------------------- "numbers"
   (types Γ Σ Δ number Γ Σ Δ num)]
  [(side-condition (valid-types Γ Σ))
   ---------------------------------- "boolean"
   (types Γ Σ Δ boolean Γ Σ Δ bool)]
  [(side-condition (valid-types Γ Σ))
   ---------------------------------- "strings"
   (types Γ Σ Δ string Γ Σ Δ str)])

; Retrieve language types from language patterns
(define-metafunction typed-nanopass
  pattern-tags : lp ... -> (n ...)
  [(pattern-tags) ()]
  [(pattern-tags (n pv ...) pat ...) (n (pattern-tags pat ...))]
  [(pattern-tags t pat ...) (pattern-tags pat ...)])

; Splice a list of names and types into a form acceptable for Γ
(define-metafunction typed-nanopass
  splice-names : ((n ...) ...) (t ...) -> ((n : t) ...)
  [(splice-names () ()) ()]
  [(splice-names ((n_1 ...) (n_2 ...) ...) (t_1 t_2 ...))
   ((n_1 : t_1) ... ,@(term (splice-names ((n_2 ...) ...) (t_2 ...))))])

; Ensure all types in Γ are valid types (in Σ)
(define-metafunction typed-nanopass+Γ
  valid-types : Γ Σ -> boolean
  [(valid-types () Σ) #t]
  [(valid-types ((x : t) (x_rest : t_rest) ...) (t_1 ... t t_2 ...))
   (valid-types ((x_rest : t_rest) ...) (t_1 ... t t_2 ...))]
  [(valid-types Γ Σ) #f])

;; ---------------------------------------------------------------------------------------------------

(module+ test (test-results))