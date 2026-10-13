import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option maxHeartbeats 800000

/-! ## Elementary facts about the weight `η` and the angular kernel `sinθcos²θ` -/

private theorem eta_pos : 0 < Work.Spaces.eta := by
  rw [Work.Spaces.eta]
  norm_num

private theorem sinCos2_zero : Work.Elliptic.sinCos2 0 = 0 := by
  rw [Work.Elliptic.sinCos2]
  norm_num

private theorem sinCos2_pi_div_two : Work.Elliptic.sinCos2 (π / 2) = 0 := by
  rw [Work.Elliptic.sinCos2, Real.sin_pi_div_two, Real.cos_pi_div_two]
  norm_num

/-! ## Integrability of `∂_z u · sinθcos²θ` on a bounded box

The weighted square `(∂_z u)² · sin(2θ)^{-η}` dominates `|∂_z u · sinθcos²θ|` on the open
quadrant (`|sinθcos²θ| ≤ 1` and `sin(2θ)^{-η} ≥ 1` there), so the domination hypothesis
`hbox` gives integrability of the product. -/

theorem integrableOn_pz_mul_sinCos2 (u : ℝ → ℝ → ℝ) (hu : SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
      Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  set box : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Work.Spaces.Iθ with hboxdef
  set S : Set (ℝ × ℝ) := box ∩ Q0 with hSdef
  -- ## measurability and finiteness of the box
  have hSmeas : MeasurableSet S := by
    rw [hSdef, hboxdef, Q0]
    exact (measurableSet_Icc.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)).inter
      (measurableSet_Ioi.prod measurableSet_Ioo)
  have hboxfin : (volume : Measure (ℝ × ℝ)) box ≠ ⊤ := by
    rw [hboxdef, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Work.Spaces.Iθ,
      Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hSfin : (volume : Measure (ℝ × ℝ)) S ≠ ⊤ :=
    ne_top_of_le_ne_top hboxfin (measure_mono (by rw [hSdef]; exact Set.inter_subset_left))
  -- ## the dominating function
  have hg : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) box := by
    have h := hbox a b ha hab
    rw [MeasureTheory.IntegrableOn] at h ⊢
    simpa only [Function.uncurry_def] using h
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))) S := by
    have hmono : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) S :=
      hg.mono_set (by rw [hSdef]; exact Set.inter_subset_left)
    exact MeasureTheory.Integrable.const_mul hmono (1 / 2)
  have h2 : IntegrableOn (fun _ : ℝ × ℝ => (1 / 2 : ℝ)) S :=
    MeasureTheory.integrableOn_const (C := (1 / 2 : ℝ)) hSfin
  have hdom : IntegrableOn (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2) S :=
    MeasureTheory.IntegrableOn.add h1 h2
  -- ## continuity of the integrand on `S`
  have hsinCos2_cont : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
        = fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2 := rfl
    rw [hfun]
    exact (Real.continuous_sin.comp continuous_snd).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)
  have hsinOn : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) Q0 :=
    hsinCos2_cont.continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2) S :=
    ((hu.pz).continuousOn.mono (by rw [hSdef]; exact Set.inter_subset_right)).mul
      (hsinOn.mono (by rw [hSdef]; exact Set.inter_subset_right))
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2) (volume.restrict S) :=
    hcont.aestronglyMeasurable hSmeas
  -- ## the pointwise domination
  have hbound : ∀ᵐ p ∂(volume.restrict S),
      ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with p hp
    have hQ : p ∈ Q0 := hp.2
    rw [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hQ
    have hspos : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hQ.2.1]) (by linarith [hQ.2.2, Real.pi_pos])
    have hsle : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have hpow1 : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hspos hsle (by linarith [eta_pos])
    have hsq : (Work.Spaces.pz u p.1 p.2) ^ 2 ≤ (Work.Spaces.pz u p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
      calc (Work.Spaces.pz u p.1 p.2) ^ 2 = (Work.Spaces.pz u p.1 p.2) ^ 2 * 1 := by ring
        _ ≤ (Work.Spaces.pz u p.1 p.2) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left hpow1 (sq_nonneg _)
    have hsincos : |Work.Elliptic.sinCos2 p.2| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul, abs_pow]
      calc |Real.sin p.2| * |Real.cos p.2| ^ 2 ≤ 1 * 1 :=
            mul_le_mul (Real.abs_sin_le_one p.2)
              (by nlinarith [Real.abs_cos_le_one p.2, abs_nonneg (Real.cos p.2)])
              (by positivity) (by norm_num)
        _ = 1 := by ring
    calc ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        = |Work.Spaces.pz u p.1 p.2| * |Work.Elliptic.sinCos2 p.2| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |Work.Spaces.pz u p.1 p.2| * 1 := mul_le_mul_of_nonneg_left hsincos (abs_nonneg _)
      _ = |Work.Spaces.pz u p.1 p.2| := mul_one _
      _ ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2 + 1) := by
          nlinarith [sq_abs (Work.Spaces.pz u p.1 p.2),
            sq_nonneg (|Work.Spaces.pz u p.1 p.2| - 1)]
      _ ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) + 1) := by linarith
      _ = (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by ring
  -- ## the box differs from `S` by a null set
  have hnull : (volume : Measure (ℝ × ℝ)) (Set.univ ×ˢ ({(0 : ℝ), π / 2} : Set ℝ)) = 0 := by
    have hN : (volume : Measure ℝ) ({(0 : ℝ), π / 2} : Set ℝ) = 0 :=
      Set.Finite.measure_zero (by simp) volume
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, hN, mul_zero]
  have hae : box =ᵐ[(volume : Measure (ℝ × ℝ))] S := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    apply propext
    rw [hSdef]
    refine ⟨?_, ?_⟩
    · intro hpbox
      rw [hboxdef, Work.Spaces.Iθ] at hpbox
      refine ⟨hpbox, ?_⟩
      have hp1 : 0 < p.1 := lt_of_lt_of_le ha hpbox.1.1
      have hp2 : 0 < p.2 := by
        rcases lt_or_eq_of_le hpbox.2.1 with h | h
        · exact h
        · exact absurd ⟨Set.mem_univ _, by simp [h]⟩ hp
      have hp3 : p.2 < π / 2 := by
        rcases lt_or_eq_of_le hpbox.2.2 with h | h
        · exact h
        · exact absurd ⟨Set.mem_univ _, by simp [h]⟩ hp
      rw [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hp1, hp2, hp3⟩
    · intro hpS
      exact hpS.1
  -- ## conclusion
  have hFint : IntegrableOn (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2) S :=
    MeasureTheory.Integrable.mono' hdom hmeas hbound
  have hres := MeasureTheory.IntegrableOn.congr_set_ae hFint hae
  simpa only [Function.uncurry_def] using hres

/-! ## The fundamental theorem of calculus for the `z`-slice

For every interior angle `θ ∈ (0,π/2)` the slice `z ↦ u z θ` is differentiable on `(0,∞)` with
derivative `pz u · θ`, so on `[a,b]` (with `0 < a < b`) the fundamental theorem of calculus
applies; at the two boundary angles `sinθcos²θ` vanishes. -/

theorem ae_integral_slice_eq (u : ℝ → ℝ → ℝ) (hu : SmoothOpen u)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (fun θ : ℝ => ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
    (fun θ : ℝ => (u b θ - u a θ) * Work.Elliptic.sinCos2 θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact measurableSet_Icc
  filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h2 | h2
    · -- interior angle: the fundamental theorem of calculus
      have hIoo : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h2⟩
      have hderiv : ∀ x ∈ Set.uIcc a b,
          HasDerivAt (fun z : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
            (Work.Spaces.pz u x θ * Work.Elliptic.sinCos2 θ) x := by
        intro x hx
        rw [Set.uIcc_of_le hab.le] at hx
        exact (hu.hasDerivAt_slice hIoo (lt_of_lt_of_le ha hx.1)).mul_const _
      have hcont : ContinuousOn (fun s : ℝ =>
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab.le]
        exact (((hu.pz).curry_z hIoo).continuousOn.mono
          (fun x hx => lt_of_lt_of_le ha hx.1)).mul continuousOn_const
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
      rw [intervalIntegral.integral_of_le hab.le] at h
      have hIocIcc : (∫ s in Set.Ioc a b,
            Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
          = ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ :=
        setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
      rw [← hIocIcc, h]
      ring
    · -- right endpoint: `sinθcos²θ = 0`
      rw [h2, sinCos2_pi_div_two]
      simp
  · -- left endpoint: `sinθcos²θ = 0`
    rw [← h0, sinCos2_zero]
    simp

/-! ## The angular moment relation -/

theorem moment_relation (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  -- ## Fubini for the box `[a,b] × Iθ`
  have hInt : Integrable (Function.uncurry (fun s θ : ℝ =>
      Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h := integrableOn_pz_mul_sinCos2 u hu hbox ha hab
    rw [MeasureTheory.IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at h
    exact h
  have hswap : (∫ s in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ s in Set.Icc a b,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ :=
    MeasureTheory.integral_integral_swap hInt
  -- ## the inner integral on the angular slices
  have hstep : (∫ θ in Work.Spaces.Iθ, ∫ s in Set.Icc a b,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ :=
    MeasureTheory.integral_congr_ae (ae_integral_slice_eq u hu ha hab)
  -- ## the angular moment of the difference
  have hsplit : (∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
      = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ,
          (u b θ * Work.Elliptic.sinCos2 θ - u a θ * Work.Elliptic.sinCos2 θ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [h1, Work.Elliptic.Fstar, Work.Elliptic.Fstar,
      MeasureTheory.integral_sub (hsl b hb) (hsl a ha)]
  have hmain : Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a
      = ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
    rw [← hsplit, ← hstep, ← hswap]
  rw [← hmain]
  ring

end Work.FTS.EllipticEst
