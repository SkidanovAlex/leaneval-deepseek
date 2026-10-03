import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.levelPart_rootVec_magnus

namespace Work.ORLyndon

/-- **The `σ_t`-level decomposition of the root Fox vector (the "base" form).**

This is the `i`-th level part of the `x`-component of the root Fox vector `(∂u/∂x)_x` pushed to
`K[⟨α | r⟩]`, computed by the Magnus chain rule of the HNN step: it equals the image under the
presentation of the `(x,i)`-component of the Fox derivative of the Magnus rewriting `magRewRel t u`,
multiplied by `τ ^ i` where `τ = presentRho r (of t)` is the class of `t`.

This is exactly the statement already established as `Work.ORLyndon.levelPart_rootVec_magnus`; we
record it here under the requested name so that colleagues can `import` it directly. -/
theorem levelPart_rootVec_eq_base {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ) :
    Work.ORLyndon.levelPart t r u l hpow hσ i (Work.ORLyndon.rootVec K r u x) =
      MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
          (Work.ORLyndon.foxD (K := K) (X := ({a : α // a ≠ t} × ℤ))
            ((⟨x, hxt⟩ : {a : α // a ≠ t}), i) (Work.OROneRel.magRewRel t u)) *
        MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (i : ℤ)) :=
  levelPart_rootVec_magnus t x hxt r u l hpow hσ i

end Work.ORLyndon
