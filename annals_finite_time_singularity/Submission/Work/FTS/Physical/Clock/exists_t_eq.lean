/-
# `Work.FTS.Physical.Clock.exists_t_eq` — surjectivity of the clock

The amplitude `A` of the dynamic rescaling solves `A' = -(1+μ)A` with the modulation bounds
`1/2 ≤ 1+μ ≤ 2`, and the physical time is `t(τ) = ∫₀^τ A`, with blow-up time `T = ∫₀^∞ A`.
This module proves **surjectivity of the clock**: every physical time `t ∈ [0,T)` is `t(τ)` for
some fake time `τ ≥ 0`.

The proof is self-contained (it does not rely on the sibling modules of this directory):

* the modulation bound `1 + μ ≥ 1/2` makes `τ ↦ A(τ)e^{τ/2}` antitone on `[0,∞)`
  (`A_decay`), hence `A(s) ≤ A(0)e^{-s/2}`: the amplitude decays at least as fast as
  `e^{-s/2}`;
* consequently `A` is integrable on `[0,∞)` (`extA_integrableOn`, proved for the extension
  `extA` of `A` to `ℝ` by constancy on the left, so that the extension is globally continuous);
* the improper-integral lemma `MeasureTheory.intervalIntegral_tendsto_integral_Ioi` then gives
  `t(τ) → T` as `τ → ∞`, whence `t(n) > t₀` for some `n : ℕ`;
* the intermediate value theorem on `[0,n]`, applied to the continuous primitive `t`, gives
  `τ ≥ 0` with `t(τ) = t₀`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology Interval
open Set Filter MeasureTheory

set_option autoImplicit false

namespace Work.FTS.Physical.Clock

/-- The amplitude `A` extended to all of `ℝ` by constancy to the left of `0`.  Unlike `A` itself,
`extA` is continuous everywhere, which is what makes `τ ↦ ∫₀^τ extA` (and hence the clock) a
globally continuous primitive.  On `[0,∞)` the extension agrees with `A` (see `extA_apply`). -/
private def extA (C : PhysClock) : ℝ → ℝ := fun τ => C.A (max τ 0)

@[simp]
private theorem extA_apply (C : PhysClock) (τ : ℝ) : extA C τ = C.A (max τ 0) := rfl

/-- `extA` is continuous. -/
private theorem extA_cont (C : PhysClock) : Continuous (extA C) := by
  have h : Continuous fun τ : ℝ => max τ 0 := continuous_id.max continuous_const
  have h2 := C.hAcont.comp_continuous h fun τ => le_max_right τ 0
  exact h2

/-- `extA` is nonnegative. -/
private theorem extA_nonneg (C : PhysClock) (τ : ℝ) : 0 ≤ extA C τ :=
  (C.hApos _ (le_max_right τ 0)).le

/-- **The decay bound.**  From `A' = -(1+μ)A` with `1 + μ ≥ 1/2`, the function
`τ ↦ A(τ)e^{τ/2}` has nonpositive derivative on `(0,∞)`, hence is antitone there; this gives
`A(s) ≤ A(τ)e^{(τ-s)/2}` for `0 ≤ τ ≤ s`. -/
private theorem A_decay (C : PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) :
    C.A s ≤ C.A τ * Real.exp (τ / 2 - s / 2) := by
  have hanti : AntitoneOn (fun x : ℝ => C.A x * Real.exp (x / 2)) (Ici (0 : ℝ)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Ici (0 : ℝ))
      (f := fun x : ℝ => C.A x * Real.exp (x / 2))
      (f' := fun x : ℝ => C.A x * Real.exp (x / 2) * (1 / 2 - (1 + C.mu x)))
      (convex_Ici 0) ?_ ?_ ?_
    · exact C.hAcont.mul
        (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
        simpa using (hasDerivAt_id x).div_const 2
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) * (1 / 2)) x :=
        h1.exp
      have h3 : HasDerivAt (fun y : ℝ => C.A y * Real.exp (y / 2))
          ((-(1 + C.mu x) * C.A x) * Real.exp (x / 2)
            + C.A x * (Real.exp (x / 2) * (1 / 2))) x :=
        (C.hAderiv x hx0).mul h2
      have h4 : HasDerivAt (fun y : ℝ => C.A y * Real.exp (y / 2))
          (C.A x * Real.exp (x / 2) * (1 / 2 - (1 + C.mu x))) x := by
        convert h3 using 1
        ring
      exact h4.hasDerivWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      have h5 : (1 : ℝ) / 2 - (1 + C.mu x) ≤ 0 := by
        have := C.hmu_lo x hx0
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (C.hApos x hx0).le (Real.exp_pos _).le) h5
  have hs : s ∈ Ici (0 : ℝ) := hτ.trans hτs
  have hle : C.A s * Real.exp (s / 2) ≤ C.A τ * Real.exp (τ / 2) := hanti hτ hs hτs
  have h6 : C.A s * Real.exp (s / 2) * Real.exp (-(s / 2))
      ≤ C.A τ * Real.exp (τ / 2) * Real.exp (-(s / 2)) :=
    mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  calc C.A s = C.A s * Real.exp (s / 2) * Real.exp (-(s / 2)) := by
        rw [mul_assoc, ← Real.exp_add, show s / 2 + -(s / 2) = 0 by ring, Real.exp_zero, mul_one]
    _ ≤ C.A τ * Real.exp (τ / 2) * Real.exp (-(s / 2)) := h6
    _ = C.A τ * Real.exp (τ / 2 - s / 2) := by
        rw [mul_assoc, ← Real.exp_add, show τ / 2 + -(s / 2) = τ / 2 - s / 2 by ring]

/-- The pointwise domination of the (extended) amplitude by an integrable exponential. -/
private theorem extA_bound (C : PhysClock) (a : ℝ) :
    ‖extA C a‖ ≤ extA C 0 * Real.exp (-(a / 2)) := by
  have h0 : extA C 0 = C.A 0 := by simp only [extA_apply, max_eq_left le_rfl]
  rcases lt_or_ge (0 : ℝ) a with ha | ha
  · have ha' : extA C a = C.A a := by simp only [extA_apply, max_eq_left ha.le]
    rw [ha', h0, Real.norm_of_nonneg (C.hApos a ha.le).le]
    simpa using A_decay C (le_refl 0) ha.le
  · have ha' : extA C a = C.A 0 := by simp only [extA_apply, max_eq_right ha]
    rw [ha', h0, Real.norm_of_nonneg (C.hApos 0 le_rfl).le]
    exact le_mul_of_one_le_right (C.hApos 0 le_rfl).le (Real.one_le_exp (by linarith))

/-- The (extended) amplitude is integrable on `(0,∞)`. -/
private theorem extA_integrableOn (C : PhysClock) : IntegrableOn (extA C) (Ioi (0 : ℝ)) := by
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-(s / 2))) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun s : ℝ => Real.exp ((-(1 : ℝ) / 2) * s)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by norm_num) 0
    refine h1.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show Real.exp ((-(1 : ℝ) / 2) * x) = Real.exp (-(x / 2))
    rw [show (-(1 : ℝ) / 2) * x = -(x / 2) by ring]
  have hg : Integrable (fun s : ℝ => extA C 0 * Real.exp (-(s / 2))) (volume.restrict (Ioi 0)) :=
    hexp.const_mul (extA C 0)
  refine hg.mono' ((extA_cont C).aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
  exact Eventually.of_forall fun a => extA_bound C a

/-- **Surjectivity of the clock.**  Every physical time `t ∈ [0,T)` is `t(τ)` for some fake time
`τ ≥ 0`. -/
theorem exists_t_eq (C : Work.FTS.Physical.PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    ∃ τ : ℝ, 0 ≤ τ ∧ C.t τ = t := by
  obtain ⟨ht0, htT⟩ := ht
  have hint : IntegrableOn (extA C) (Ioi (0 : ℝ)) := extA_integrableOn C
  have htend : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(n : ℝ), extA C x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), extA C x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop
  have hagree : ∀ b : ℝ, 0 ≤ b → (∫ x in (0 : ℝ)..b, C.A x) = ∫ x in (0 : ℝ)..b, extA C x := by
    intro b hb
    rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [extA_apply, max_eq_left (le_of_lt hx.1)]
  have hT : C.T = ∫ x in Ioi (0 : ℝ), extA C x := by
    rw [PhysClock.T, MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [extA_apply, max_eq_left (le_of_lt (mem_Ioi.mp hx))]
  have htend' : Tendsto (fun n : ℕ => C.t (n : ℝ)) atTop (𝓝 C.T) := by
    rw [hT]
    refine Filter.Tendsto.congr' ?_ htend
    filter_upwards with n
    exact (hagree (n : ℝ) (Nat.cast_nonneg n)).symm
  have hmem : {y : ℝ | t < y} ∈ 𝓝 C.T := isOpen_Ioi.mem_nhds htT
  obtain ⟨N, hN⟩ := (htend'.eventually hmem).exists
  have hcont : Continuous fun b : ℝ => ∫ x in (0 : ℝ)..b, extA C x :=
    intervalIntegral.continuous_primitive (fun a b => (extA_cont C).intervalIntegrable a b) 0
  have hcontOn : ContinuousOn C.t (Icc (0 : ℝ) (N : ℝ)) := by
    refine hcont.continuousOn.congr fun b hb => ?_
    exact hagree b hb.1
  have h0N : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmem' : t ∈ Icc (C.t 0) (C.t (N : ℝ)) := by
    rw [PhysClock.t_zero]
    exact ⟨ht0, hN.le⟩
  obtain ⟨τ, hτmem, hτeq⟩ := intermediate_value_Icc h0N hcontOn hmem'
  exact ⟨τ, hτmem.1, hτeq⟩

end Work.FTS.Physical.Clock
