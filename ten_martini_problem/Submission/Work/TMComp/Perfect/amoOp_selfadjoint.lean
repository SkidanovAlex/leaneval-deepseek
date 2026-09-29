import Mathlib
import Submission.Work.TMComp.PerfectDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Self-adjointness of the canonical almost Mathieu operator

`Work.TMComp.Perfect.amoOp α lam θ` is the operator on `ℓ²(ℤ)` with the coordinate formula

`(amoOp f) n = f (n+1) + f (n-1) + 2λ cos 2π(θ + nα) f n`,

built in `PerfectDefs` as the sum

`sh 1 + sh (-1) + diag (potC α lam θ) (2 * |lam|) (potC_bound α lam θ)`

of two shifts and a diagonal operator.  We show that it is self-adjoint, i.e. that it equals
its Hilbert-space adjoint (`star` on `EllTwo →L[ℂ] EllTwo` is the adjoint).

The two ingredients are:

* `star_sh_one`  : the adjoint of `sh 1` is `sh (-1)` (the shift is unitary);
* `star_diag_of_real` : a diagonal operator with real coefficients is self-adjoint.

Both are proved through the inner product on `ℓ²(ℤ)` (`lp.inner_eq_tsum`) and
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`.
-/

open scoped ComplexConjugate

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Perfect

/-! ## The adjoint of the shift -/

/-- The shift is a unitary operator: `(sh 1)† = sh (-1)`. -/
theorem star_sh_one : star (sh (1 : ℤ)) = sh (-1) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [show sh (1 : ℤ) = ((shE 1 : EllTwo ≃ₗᵢ[ℂ] EllTwo) : EllTwo →L[ℂ] EllTwo) from rfl]
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext f n
  change ((shE 1 : EllTwo ≃ₗᵢ[ℂ] EllTwo).toLinearEquiv.symm) f n = sh (-1) f n
  simp [sh, shE, shiftFn]

/-! ## Self-adjointness of a diagonal operator with real coefficients -/

/-- A diagonal operator whose coefficient sequence is real-valued is self-adjoint. -/
theorem star_diag_of_real {c : ℤ → ℂ} (K : ℝ) (hK : ∀ n : ℤ, ‖c n‖ ≤ K)
    (hc : ∀ n : ℤ, starRingEnd ℂ (c n) = c n) :
    star (diag c K hK) = diag c K hK := by
  show IsSelfAdjoint (diag c K hK)
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  change inner ℂ (c n * f n) (g n) = inner ℂ (f n) (c n * g n)
  rw [← smul_eq_mul (c n) (f n), inner_smul_left, ← smul_eq_mul (c n) (g n), inner_smul_right,
    hc n]

/-- The almost Mathieu potential `potC α lam θ` is real-valued, hence fixed by conjugation. -/
theorem star_potC (α lam θ : ℝ) (n : ℤ) : starRingEnd ℂ (potC α lam θ n) = potC α lam θ n := by
  rw [potC_apply]
  exact Complex.conj_ofReal _

/-! ## The main statement -/

/-- The canonical almost Mathieu operator is self-adjoint. -/
theorem amoOp_selfadjoint (α lam θ : ℝ) : IsSelfAdjoint (Work.TMComp.Perfect.amoOp α lam θ) := by
  have hsh : star (sh (1 : ℤ)) = sh (-1) := star_sh_one
  have hsh' : star (sh (-1)) = sh (1 : ℤ) := by rw [← hsh, star_star]
  have hdiag : star (diag (potC α lam θ) (2 * |lam|) (potC_bound α lam θ))
      = diag (potC α lam θ) (2 * |lam|) (potC_bound α lam θ) :=
    star_diag_of_real _ _ (star_potC α lam θ)
  show star (amoOp α lam θ) = amoOp α lam θ
  simp only [amoOp, StarRing.star_add, hsh, hsh', hdiag]
  abel

end Work.TMComp.Perfect
