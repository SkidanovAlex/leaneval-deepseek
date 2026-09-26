import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KPlusQ1
import Submission.Work.Asymptotics.KhatE1Core.invDeltaSecondOrder

/-!
# `[dKPlus24]_{E²}` — the one nontrivial input

The `E²`-coefficient of the plus-side deviation sum `dKPlusSum` localises entirely to `dSm2`'s
second bracket, `-E4Ref³·Φ_ref·Donly`: every other term of `dSm1 … dSm5` is `O(q²)` or smaller.
Since `Donly = Δ(z)⁻¹ - (q⁻¹ + 24)` and the *proved* `invDeltaSecondOrder` gives

  `Δ(z)⁻¹ = (Ept z)⁻¹² + 24 + 324·q(z) + O(‖Ept z‖⁴)`,

one has `Donly = 324·q + O(q²)` — a *shallow* coefficient, from the leading term of `Δ⁻¹`
alone.  This module records that leading term (`Donly_leading`); with it, and the `O(q²)`
bounds for the other terms, `[dKPlus24]_{E²} = 324·c·z²·Φ_ref`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- `(Ept z)⁻¹²` and `(qParamFun z)⁻¹` agree (i.e. `q = E²` reflected through the inverse). -/
lemma qParamFun_inv_eq (z : ℍ) :
    (Work.Kernels.qParamFun z)⁻¹ = (Work.Residues.Ept z ^ 2)⁻¹ := by
  rw [Work.Asymptotics.K24F.qParamFun_eq_Ept_sq' z]

/-- **`Donly = 324·q + O(q²)`**, from the proved `invDeltaSecondOrder`. -/
lemma Donly_leading :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Donly z - 324 * Work.Kernels.qParamFun z‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := invDeltaSecondOrder
  refine ⟨C, hC, fun z hz => ?_⟩
  have hq := Work.Asymptotics.K24F.qParamFun_eq_Ept_sq' z
  have hkey : Donly z - 324 * Work.Kernels.qParamFun z
      = (Work.Kernels.DeltaFun z)⁻¹
          - ((Work.Residues.Ept z)⁻¹ ^ 2 + 24 + 324 * Work.Kernels.qParamFun z) := by
    simp only [Donly, DeltaInvRef]
    rw [hq]
    have hinv : ((Work.Residues.Ept z)⁻¹ ^ 2) = ((Work.Residues.Ept z) ^ 2)⁻¹ := by
      simp only [pow_two, mul_inv]
    rw [hinv]
    ring
  rw [hkey]
  have hbound := h z hz
  have hq2 : ‖Work.Residues.Ept z‖ ^ 4 = ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [hq, norm_pow]
    ring
  rw [hq2] at hbound
  exact hbound

end

end Work.Asymptotics.KhatE1Core
