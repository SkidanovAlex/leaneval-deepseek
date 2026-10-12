import Mathlib.Order.Interval.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Submission.Work.SmallBoxA0.OneDPotMainId.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0.OneDPotMainId

open MeasureTheory Set

open scoped Interval

theorem ibp_tail_shell {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) (p : ℝ → ℝ)
    (hInt : IntervalIntegrable (fun s : ℝ => s * p s) MeasureTheory.volume ε R)
    (hHon : IntervalIntegrable (Work.SmallBoxA0.TailI p R) MeasureTheory.volume 0 R) :
    ∫ r in ε..R, (r * p r) * Work.SmallBoxA0.ShellI p R r
      = (∫ r in ε..R, (Work.SmallBoxA0.TailI p R r) ^ 2)
        + Work.SmallBoxA0.TailI p R ε * Work.SmallBoxA0.ShellI p R ε := by
  have hεR' : ε ≤ R := hεR.le
  have h0R : (0 : ℝ) ≤ R := le_of_lt (lt_trans hε hεR)
  have hRmem : R ∈ uIcc ε R := by rw [uIcc_of_le hεR']; exact ⟨hεR', le_rfl⟩
  have h0mem : (0 : ℝ) ∈ uIcc 0 R := by rw [uIcc_of_le h0R]; exact ⟨le_rfl, h0R⟩
  -- Absolute continuity of the tail flux on `[ε,R]`, from the integrability of `s * p s`.
  have hTac : AbsolutelyContinuousOnInterval (Work.SmallBoxA0.TailI p R) ε R := by
    refine Work.SmallBoxA0.absolutelyContinuousOnInterval_congr
      (f := fun x : ℝ => -(∫ v in R..x, v * p v)) ?_ ?_
    · intro x _
      simp only [Work.SmallBoxA0.TailI]
      exact (intervalIntegral.integral_symm R x).symm
    · exact (hInt.absolutelyContinuousOnInterval_intervalIntegral hRmem).neg
  -- Absolute continuity of the shell potential on `[ε,R]`, from the integrability of `TailI p R`.
  have hSac : AbsolutelyContinuousOnInterval (Work.SmallBoxA0.ShellI p R) ε R := by
    have h0 : AbsolutelyContinuousOnInterval (Work.SmallBoxA0.ShellI p R) 0 R :=
      hHon.absolutelyContinuousOnInterval_intervalIntegral h0mem
    refine h0.mono ?_
    rw [uIcc_of_le hεR', uIcc_of_le h0R]
    exact Set.Icc_subset_Icc (le_of_lt hε) le_rfl
  have hsub : uIcc ε R ⊆ uIcc 0 R := by
    rw [uIcc_of_le hεR', uIcc_of_le h0R]
    exact Set.Icc_subset_Icc (le_of_lt hε) le_rfl
  -- A.e. derivative of the tail flux: `(TailI p R)' = -(r * p r)`.
  have hTderiv : ∀ᵐ x : ℝ, x ∈ Ι ε R →
      deriv (Work.SmallBoxA0.TailI p R) x = -(x * p x) := by
    filter_upwards [hInt.ae_hasDerivAt_integral] with x hx hxI
    have hxmem : x ∈ uIcc ε R := uIoc_subset_uIcc hxI
    have h1 : HasDerivAt (fun y : ℝ => ∫ v in R..y, v * p v) (x * p x) x := hx hxmem R hRmem
    have h2 : HasDerivAt (fun y : ℝ => -(∫ v in R..y, v * p v)) (-(x * p x)) x := h1.neg
    have h3 : HasDerivAt (Work.SmallBoxA0.TailI p R) (-(x * p x)) x :=
      h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        simp only [Work.SmallBoxA0.TailI]
        exact intervalIntegral.integral_symm R y))
    exact h3.deriv
  -- A.e. derivative of the shell potential: `(ShellI p R)' = TailI p R`.
  have hSderiv : ∀ᵐ x : ℝ, x ∈ Ι ε R →
      deriv (Work.SmallBoxA0.ShellI p R) x = Work.SmallBoxA0.TailI p R x := by
    filter_upwards [hHon.ae_hasDerivAt_integral] with x hx hxI
    have hxmem : x ∈ uIcc 0 R := hsub (uIoc_subset_uIcc hxI)
    have h1 := hx hxmem 0 h0mem
    exact h1.deriv
  -- Integration by parts for absolutely continuous functions.
  have hIBP := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hTac hSac
  have hL : ∫ x in ε..R, Work.SmallBoxA0.TailI p R x * deriv (Work.SmallBoxA0.ShellI p R) x
      = ∫ x in ε..R, (Work.SmallBoxA0.TailI p R x) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hSderiv] with x hx hxI
    rw [hx hxI]
    ring
  have hRr : ∫ x in ε..R, deriv (Work.SmallBoxA0.TailI p R) x * Work.SmallBoxA0.ShellI p R x
      = -∫ x in ε..R, (x * p x) * Work.SmallBoxA0.ShellI p R x := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hTderiv] with x hx hxI
    rw [hx hxI]
    ring
  rw [hL, hRr, Work.SmallBoxA0.TailI_self] at hIBP
  linarith

end Work.SmallBoxA0.OneDPotMainId
