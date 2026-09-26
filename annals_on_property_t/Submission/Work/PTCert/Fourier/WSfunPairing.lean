import Mathlib
import Submission.Work.PTCert.TFDefs
import Submission.Work.PTCert.Math
import Submission.Work.PTCert.Fourier.sum_pair_fiber
import Submission.Work.PTCert.Fourier.fiber_sum_cSfun

/-!
# Pairing identity for the twisted Fourier form `WSfun`

`WSfunPairing` is the "fold the double sum onto the orbit representatives" step of the
twisted Fourier criterion (`Submission.PTCert.TwistedFourierCriterion`).

Writing `x = act (nu x) (rep x)` (`hactnu`) and applying the covariance law `hstar` together
with multiplicativity of the sign character `chiS` (`hchi`), the quadratic form of `WSfun`

`∑ x ∑ y, v x * v y * WSfun S x y`

is rewritten as `∑ x ∑ y, A x * A y * WSfun S (rep x) (rep y)` with
`A x = v x * chiS S (nu x) * sgn (nu x) (rep x)`.  Since `rep` is idempotent (`hreprep`),
its fibres over its fixed points partition `ι`, so this last sum regroups as a sum over
pairs of fixed points of the products `∑_{x ↦ x̄} A x`, which is exactly `cSfun`.
-/

namespace Work.PTCert.Fourier

open Submission.PTCert

theorem WSfunPairing {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (act : (Fin m → ZMod 2) → ι → ι) (sgn : (Fin m → ZMod 2) → ι → ℝ)
    (M : Matrix ι ι ℝ) (rep : ι → ι) (nu : ι → (Fin m → ZMod 2))
    (hactnu : ∀ x, act (nu x) (rep x) = x) (hreprep : ∀ x, rep (rep x) = rep x)
    (S : Finset (Fin m))
    (hchi : ∀ (S : Finset (Fin m)) (a b : Fin m → ZMod 2), chiS S (a + b) = chiS S a * chiS S b)
    (hstar : ∀ (a b : Fin m → ZMod 2) (x y : ι),
        WSfun act sgn M S (act a x) (act b y)
          = chiS S (a + b) * sgn a x * sgn b y * WSfun act sgn M S x y)
    (v : ι → ℝ) :
    (∑ x : ι, ∑ y : ι, v x * v y * WSfun act sgn M S x y)
      = ∑ xb : {x : ι // rep x = x}, ∑ yb : {x : ι // rep x = x},
          cSfun v sgn nu rep S xb.1 * cSfun v sgn nu rep S yb.1
            * WSfun act sgn M S xb.1 yb.1 := by
  -- Step 1: expand `WSfun` at `x = act (nu x) (rep x)`, `y = act (nu y) (rep y)`.
  have hW : ∀ x y, WSfun act sgn M S x y
      = chiS S (nu x) * chiS S (nu y) * sgn (nu x) (rep x) * sgn (nu y) (rep y)
          * WSfun act sgn M S (rep x) (rep y) := by
    intro x y
    have h := hstar (nu x) (nu y) (rep x) (rep y)
    rw [hactnu x, hactnu y, hchi S (nu x) (nu y)] at h
    exact h
  -- Steps 2-4: factor out the orbit sums and regroup them by the idempotent `rep`.
  calc (∑ x : ι, ∑ y : ι, v x * v y * WSfun act sgn M S x y)
      = ∑ x : ι, ∑ y : ι, (v x * chiS S (nu x) * sgn (nu x) (rep x))
              * (v y * chiS S (nu y) * sgn (nu y) (rep y))
              * WSfun act sgn M S (rep x) (rep y) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [hW x y]; ring
    _ = ∑ xb : {x : ι // rep x = x}, ∑ yb : {x : ι // rep x = x},
          (∑ x : {x : ι // rep x = xb.1}, v x.1 * chiS S (nu x.1) * sgn (nu x.1) (rep x.1))
            * (∑ y : {x : ι // rep x = yb.1},
                v y.1 * chiS S (nu y.1) * sgn (nu y.1) (rep y.1))
            * WSfun act sgn M S xb.1 yb.1 :=
        sum_pair_fiber rep hreprep (fun x => v x * chiS S (nu x) * sgn (nu x) (rep x))
          (fun x => v x * chiS S (nu x) * sgn (nu x) (rep x)) (WSfun act sgn M S)
    _ = ∑ xb : {x : ι // rep x = x}, ∑ yb : {x : ι // rep x = x},
          cSfun v sgn nu rep S xb.1 * cSfun v sgn nu rep S yb.1
            * WSfun act sgn M S xb.1 yb.1 := by
        refine Finset.sum_congr rfl (fun xb _ => Finset.sum_congr rfl (fun yb _ => ?_))
        rw [fiber_sum_cSfun v sgn nu rep S xb.1, fiber_sum_cSfun v sgn nu rep S yb.1]

end Work.PTCert.Fourier
