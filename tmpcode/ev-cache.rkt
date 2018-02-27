#lang racket/unit
(require racket/match
         racket/set
         "../map.rkt"
         "../transformers.rkt"
         "../syntax.rkt"
         "../signatures.rkt")

(import monad^ menv^ mstore^ mcache^ δ^ alloc^)
(export ev-cache^)
(init-depend monad^)

(define-monad M)

(define (((ev-cache ev₀) ev) e)
  (do ρ ← ask-env
      σ ← get-store
      ς ≔ (list e ρ σ) ;; configuration
      Σ ← get-$        ;; get-cache-out
      (if (∈  ς Σ)     ;; if config is in cache-out
          (for/monad+ ([v.σ (Σ ς)])
            (do (put-store (cdr v.σ))
                (return (car v.σ))))  ;; just return
          (do Σ⊥  ←  ask-⊥   ;; ask-cache-in
              ;; if cache-in contains s, then use it, otherwise empty set; and put it into cache-out
              (put-$ (Σ ς (if (∈  ς  Σ⊥) (Σ⊥ ς) (set)))) 
              v  ← ((ev₀ ev) e)
              σ  ← get-store
              ;; update-cache-out
              (update-$ (λ (Σ) (Σ ς (set-add (Σ ς) (cons v σ)))))
              (return v)))))
