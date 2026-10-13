import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.tracePi4_six
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.STBounds2
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.N6Trans.SixRoute
  (trace_morrey wsq_dzIter_le_HkIntegrand_pi4 wsq_mixed_le_HkIntegrand_pi4
    half_le_sin_two_pi4 w_nonneg_pi4)

set_option maxHeartbeats 1600000

/-! ## The angular trace at `θ = π/4` of the level-six pure `D_z`-slots, orders up to `5`

`SixRoute.tracePi4` proves the *integrated* trace estimate at `θ = π/4` for the pure
`D_z`-slots of order `j ≤ 2`, and `T6Gen.tracePi4_six` provides the same statement at
level six for `j ≤ 5`.  Here we record the *pointwise-in-`z`* form of that estimate, for
every `z ∈ Iz` separately: this is the exact form in which the level-six transport
estimates consume the trace (they need a bound at a fixed radial point, not an average).

The mathematics is the one-dimensional Morrey inequality on the fixed subinterval
`J = [π/8, 3π/8] ∋ π/4`, on which `sin(2θ) ≥ 1/2`:
`h(π/4)² ≤ (2/|J|)∫_J h² + 2|J|∫_J (h')²`, applied to the angular slice
`h = fun θ => D_z^j g z θ`, followed by the pointwise slot comparisons
`w(z)²(D_z^j g)² ≤ HkIntegrand` and `w(z)²(∂_θD_z^j g)² ≤ 4·HkIntegrand`
(the latter through `∂_θ D_z^j g = mixed j 1 g / sin(2θ)`).  This is precisely the
`hkey` sub-argument of `tracePi4_six`, exposed without the final `z`-integration. -/

theorem tracePi4Five : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (g : ℝ → ℝ → ℝ) (j : ℕ),
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → j ≤ 5 →
      ∀ z ∈ Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2
          ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10, by norm_num, ?_⟩
  intro α hα g j hg hmem hj z hz
  have hα0 : 0 < α := hα.1
  have hj6 : j ≤ 6 := by omega
  -- the subinterval `J = [π/8, 3π/8]` around the trace angle `π/4`
  have hsubI : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hsubI' : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- `z = 0`: the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by
      rw [Work.Spaces.w]; norm_num
    rw [hw0]
    have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [h0, zero_mul]
    exact mul_nonneg (by norm_num)
      (integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 g 0 θ))
  · -- `z > 0`: the genuine estimate
    have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j g) := hg.DzIter j
    set h : ℝ → ℝ := fun θ => Work.Spaces.DzIter j g z θ with hh
    have hcont : ContinuousOn h (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
      (hsm.curry_θ hzpos).continuousOn.mono hsubI'
    have hdc : ContinuousOn (deriv h) (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
      refine ContinuousOn.congr ((hsm.pth.curry_θ hzpos).continuousOn.mono hsubI') ?_
      intro x hx
      have := Work.FTS.EllSol.WeakSlice.pth_DzIter_Q0 hg j hzpos (hsubI' hx)
      simpa only [hh, Work.Spaces.pth] using this
    have hd : ∀ x ∈ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8),
        HasDerivAt h (deriv h x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
      have := ((hsm.curry_θ hzpos).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hx')
      simpa only [hh] using this.hasDerivAt
    have hmor := trace_morrey (h := h) (a := Real.pi / 8) (x₀ := Real.pi / 4)
      (b := 3 * Real.pi / 8) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      hcont hdc hd
    have hbma : (3:ℝ) * Real.pi / 8 - Real.pi / 8 = Real.pi / 4 := by ring
    rw [hbma] at hmor
    -- the `L²`-block: `∫_J w² h² ≤ K`
    have hIntHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 g z θ)
        (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
      (hmem.1 z hz).mono_set hsubI
    have hI1 : (Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
          (h x) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
      rw [← MeasureTheory.integral_const_mul]
      refine le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hIntHk
        (ae_restrict_of_forall_mem measurableSet_Icc
          (fun x hx => wsq_dzIter_le_HkIntegrand_pi4 hj6 (hsubI' hx)))) ?_
      exact MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
        (Eventually.of_forall (fun x => Work.Spaces.HkIntegrand_nonneg α 6 g z x))
        (Eventually.of_forall (fun x hx => hsubI hx))
    -- the `H¹`-block: `∫_J w² (h')² ≤ 4K`
    have hpt2 : ∀ x ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
        (Work.Spaces.w z) ^ 2 * (deriv h x) ^ 2
          ≤ 4 * Work.Spaces.HkIntegrand α 6 g z x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hsubI' hx
      have hsinpos : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx'.1])
          (by linarith [hx'.2, Real.pi_pos])
      have hder : deriv h x = Work.Spaces.DzIter j (Work.Spaces.pth g) z x := by
        have := Work.FTS.EllSol.WeakSlice.pth_DzIter_Q0 hg j hzpos hx'
        simpa only [hh, Work.Spaces.pth] using this
      have hmix : Work.Spaces.mixed j 1 g z x
          = Real.sin (2 * x) * Work.Spaces.DzIter j (Work.Spaces.pth g) z x :=
        (Work.FTS.H2.sin_mul_dzIter_pth g j z x).symm
      have hsin := half_le_sin_two_pi4 hx
      have hsinne : Real.sin (2 * x) ≠ 0 := ne_of_gt hsinpos
      have habs : |Work.Spaces.DzIter j (Work.Spaces.pth g) z x|
          = |Work.Spaces.mixed j 1 g z x| / Real.sin (2 * x) := by
        have h3 : Real.sin (2 * x)
            * |Work.Spaces.DzIter j (Work.Spaces.pth g) z x|
            = |Work.Spaces.mixed j 1 g z x| := by
          rw [← abs_of_pos hsinpos, ← abs_mul, ← hmix]
        rw [eq_div_iff hsinne, mul_comm]
        exact h3
      have hbound : |deriv h x| ≤ 2 * |Work.Spaces.mixed j 1 g z x| := by
        rw [hder, habs, div_le_iff₀ hsinpos]
        nlinarith [abs_nonneg (Work.Spaces.mixed j 1 g z x), hsin]
      have hd2 : (deriv h x) ^ 2 ≤ 4 * (Work.Spaces.mixed j 1 g z x) ^ 2 := by
        have h3 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
        rw [sq_abs, mul_pow, sq_abs] at h3
        nlinarith [h3]
      calc (Work.Spaces.w z) ^ 2 * (deriv h x) ^ 2
          ≤ (Work.Spaces.w z) ^ 2 * (4 * (Work.Spaces.mixed j 1 g z x) ^ 2) :=
            mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
        _ = 4 * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j 1 g z x) ^ 2) := by ring
        _ ≤ 4 * Work.Spaces.HkIntegrand α 6 g z x :=
            mul_le_mul_of_nonneg_left
              (wsq_mixed_le_HkIntegrand_pi4 hα0.le (by norm_num) (by omega) hx') (by norm_num)
    have hI2 : (Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
          (deriv h x) ^ 2)
        ≤ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
      rw [← MeasureTheory.integral_const_mul]
      have hInt4 : IntegrableOn (fun θ => 4 * Work.Spaces.HkIntegrand α 6 g z θ)
          (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := hIntHk.const_mul 4
      refine le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hInt4
        (ae_restrict_of_forall_mem measurableSet_Icc hpt2)) ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 4)
      exact MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
        (Eventually.of_forall (fun x => Work.Spaces.HkIntegrand_nonneg α 6 g z x))
        (Eventually.of_forall (fun x hx => hsubI hx))
    set K : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ with hK
    have hKnn : 0 ≤ K := by
      rw [hK]; exact integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
    have hc1 : 2 / (Real.pi / 4) = 8 / Real.pi := by
      field_simp
      norm_num
    have hc2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    have hcoef : 8 / Real.pi + 2 * Real.pi ≤ 10 := by
      have hp1 : (1:ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
      have hp4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
      have hprod : (Real.pi - 1) * (Real.pi - 4) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have heq : 8 / Real.pi + 2 * Real.pi = (8 + 2 * Real.pi * Real.pi) / Real.pi := by
        field_simp
      rw [heq, div_le_iff₀ Real.pi_pos]
      nlinarith [hprod]
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2
        = (Work.Spaces.w z) ^ 2 * (h (Real.pi / 4)) ^ 2 := by rw [hh]
      _ ≤ (Work.Spaces.w z) ^ 2 * ((2 / (Real.pi / 4)) * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (h x) ^ 2)
            + 2 * (Real.pi / 4) * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
              (deriv h x) ^ 2)) := mul_le_mul_of_nonneg_left hmor (sq_nonneg _)
      _ = (2 / (Real.pi / 4)) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (h x) ^ 2))
            + 2 * (Real.pi / 4) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (deriv h x) ^ 2)) := by ring
      _ = (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (h x) ^ 2))
            + (Real.pi / 2) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (deriv h x) ^ 2)) := by rw [hc1, hc2]
      _ ≤ (8 / Real.pi) * K + (Real.pi / 2) * (4 * K) := by
          have h8 : 0 ≤ (8:ℝ) / Real.pi := by positivity
          have hp2 : 0 ≤ Real.pi / 2 := by positivity
          have hA := mul_le_mul_of_nonneg_left hI1 h8
          have hB := mul_le_mul_of_nonneg_left hI2 hp2
          rw [hK] at hA hB ⊢
          linarith
      _ = (8 / Real.pi + 2 * Real.pi) * K := by ring
      _ ≤ 10 * K := mul_le_mul_of_nonneg_right hcoef hKnn

end
end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
