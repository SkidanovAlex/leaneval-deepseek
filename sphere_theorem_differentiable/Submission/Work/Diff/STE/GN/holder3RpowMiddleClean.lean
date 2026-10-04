import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.holder3_int

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.GN

theorem holder3RpowMiddleClean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c p : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hp : 2 ≤ p)
    (habc : 1 / a + 1 / b + 1 / c = 1) (hmul : (p - 2) * b = p)
    (F G H : (ι → ℝ) → ℝ) (hF : Continuous F) (hG : Continuous G) (hH : Continuous H)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x) (hH0 : ∀ x, 0 ≤ H x) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), F x * G x ^ (p - 2) * H x
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι), F x ^ a) ^ (1 / a)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ p) ^ ((p - 2) / p)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), H x ^ c) ^ (1 / c) := by
  have hp2 : 0 ≤ p - 2 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hp0 : p ≠ 0 := by linarith
  -- `x ↦ G x ^ (p - 2)` is continuous and nonnegative
  have hGpow : Continuous fun x => G x ^ (p - 2) := hG.rpow_const (fun x => Or.inr hp2)
  have hGpow0 : ∀ x, 0 ≤ G x ^ (p - 2) := fun x => Real.rpow_nonneg (hG0 x) _
  -- three-function Hölder with exponents `(a, b, c)` applied to `(F, G^(p-2), H)`
  have hmain := holder3_int a b c ha hb hc habc F (fun x => G x ^ (p - 2)) H
    hF hGpow hH hF0 hGpow0 hH0
  -- `(G x ^ (p-2)) ^ b = G x ^ p`
  have hint : (∫ x in Work.Diff.STE.unitCube (ι := ι), (fun x => G x ^ (p - 2)) x ^ b)
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ p := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (fun x => G x ^ (p - 2)) x ^ b = G x ^ p
    rw [← Real.rpow_mul (hG0 x) (p - 2) b, hmul]
  -- `1 / b = (p - 2) / p` from `(p - 2) * b = p`
  have hexp : 1 / b = (p - 2) / p := by
    rw [div_eq_div_iff hb0 hp0]
    linarith [hmul]
  rw [hint, hexp] at hmain
  exact hmain

end Work.Diff.STE.GN
