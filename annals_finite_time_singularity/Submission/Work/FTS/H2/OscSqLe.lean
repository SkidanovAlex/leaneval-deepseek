/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular oscillation (Cauchy–Schwarz) bound `OscSqLe`

For `0 < α ≤ 1`, `γ = gam α = 1 + α/10` and `h : ℝ → ℝ` differentiable on the interval
between two points `θ θ₀` of `Iθ = [0, π/2]`, with `deriv h` continuous there and
`σ ↦ (deriv h σ)^2 sin(2σ)^{2-γ}` integrable on `Iθ`,

  `(h θ - h θ₀)^2 ≤ (100/(γ-1)) · ∫_{Iθ} (deriv h σ)^2 sin(2σ)^{2-γ}`.

This is the one-dimensional Hardy/Cauchy–Schwarz oscillation estimate used (at a fixed `z`,
for the slice `θ ↦ f z θ`) in the angular part of Elgindi's `ℋ²`-supremum estimates;
`Work.Spaces.HardyTheta` is the special case `θ₀ = 0`.

The proof is the Cauchy–Schwarz inequality `Work.Spaces.cs_integral` applied to the
splitting `h' = (h' sin^{(2-γ)/2})·sin^{(γ-2)/2}` on the open interval between `θ` and
`θ₀`, together with the explicit angular integral bound
`∫_{Iθ} sin(2σ)^{γ-2} ≤ 100/(γ-1)` of `Work.Spaces.sin_two_rpow`.  The auxiliary lemma
`coreInterval` is the general form of that Cauchy–Schwarz step on an arbitrary
subinterval `[a,b] ⊆ Iθ`; the last step is the fundamental theorem of calculus for
`deriv h`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` bookkeeping -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

/-- `x ^ ((2 - γ)/2) * x ^ ((γ - 2)/2) = 1` for `x > 0`. -/
private lemma rpow_half_mul_half (x γ : ℝ) (hx : 0 < x) :
    x ^ ((2 - γ) / 2) * x ^ ((γ - 2) / 2) = 1 := by
  rw [← Real.rpow_add hx, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero]

/-! ## The Cauchy–Schwarz step on a subinterval of `Iθ` -/

/-- Cauchy–Schwarz / Hardy oscillation bound on a subinterval of `Iθ = [0, π/2]`:
for `0 < α ≤ 1`, `a ≤ b` both in `Iθ` and `h` continuous on `[a,b]`,

  `(∫_a^b h)² ≤ (100/(γ-1)) · ∫_{Iθ} h² sin(2σ)^{2-γ}`.

This is a verbatim generalisation of the private lemma `core` of
`Submission/Work/Spaces/HardyTheta.lean` (the case `a = 0`, `b = θ`) from `Ioo 0 θ` to
`Ioo a b`. -/
private theorem coreInterval (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ) {a b : ℝ}
    (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ) (hab : a ≤ b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ) :
    (∫ s in a..b, h s) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) *
        ∫ s in Work.Spaces.Iθ,
          (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ2 : Work.Spaces.gam α ≤ 11 / 10 := by rw [Work.Spaces.gam]; linarith
  have hp1 : -1 < Work.Spaces.gam α - 2 := by linarith
  have hp0 : Work.Spaces.gam α - 2 ≤ 0 := by linarith
  have ha0 : 0 ≤ a := ha.1
  have hb1 : b ≤ π / 2 := hb.2
  -- positivity of `sin (2 ·)` on `(a,b)`, nonnegativity on `Iθ`
  have hsinpos : ∀ s ∈ Set.Ioo a b, 0 < Real.sin (2 * s) := by
    intro s hs
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1, ha0])
      (by linarith [hs.2, hb1, Real.pi_pos])
  have hsinIθ : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * x) := by
    intro x hx
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos])
  have hsub : Set.Ioo a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha0 hx.1.le, le_trans hx.2.le hb1⟩
  have hae_sub : Set.Ioo a b ≤ᵐ[volume] Work.Spaces.Iθ :=
    Filter.Eventually.of_forall (fun x hx => hsub hx)
  have hmIθ : MeasurableSet Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ]
    exact measurableSet_Icc
  have hFnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hSnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun s => (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (hsinIθ x hx) _)
  -- integrability of the weighted square over the open interval
  have hIntF : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo a b) :=
    hint.mono_set hsub
  -- measurability of the two Cauchy–Schwarz factors
  have hcont_sin : ContinuousOn (fun s : ℝ => Real.sin (2 * s)) (Set.Ioo a b) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hsm_h : AEMeasurable h (volume.restrict (Set.Ioo a b)) :=
    (hcont.mono Set.Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo
  have hsm_s : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2))
      (volume.restrict (Set.Ioo a b)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  have hsm_s2 : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2))
      (volume.restrict (Set.Ioo a b)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  -- the two squared integrands
  have eq_v2 : Set.EqOn
      (fun x => ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2)
      (fun x => (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) (Set.Ioo a b) := by
    intro x hx
    dsimp only
    rw [rpow_sq _ _ (hsinpos x hx),
      show 2 * ((Work.Spaces.gam α - 2) / 2) = Work.Spaces.gam α - 2 by ring]
  have eq_u2 : Set.EqOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
      (fun x => (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo a b) := by
    intro x hx
    dsimp only
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx),
      show 2 * ((2 - Work.Spaces.gam α) / 2) = 2 - Work.Spaces.gam α by ring]
  have hInt_v2 : MeasureTheory.IntegrableOn
      (fun x => ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2) (Set.Ioo a b) :=
    ((Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).1.mono_set hsub).congr_fun
      eq_v2.symm measurableSet_Ioo
  have hInt_u2 : MeasureTheory.IntegrableOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
      (Set.Ioo a b) :=
    hIntF.congr_fun eq_u2.symm measurableSet_Ioo
  have hu_mem : MeasureTheory.MemLp
      (fun x => h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) 2
      (volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hsm_h.mul hsm_s).aestronglyMeasurable).2 hInt_u2
  have hv_mem : MeasureTheory.MemLp
      (fun x => (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) 2
      (volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hsm_s2.aestronglyMeasurable).2 hInt_v2
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  -- identify the three integrals
  have e1 : (∫ x in Set.Ioo a b,
        (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2))
          * (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2))
      = ∫ x in Set.Ioo a b, h x := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_assoc, rpow_half_mul_half _ _ (hsinpos x hx), mul_one]
  have e2 : (∫ x in Set.Ioo a b,
        (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b,
          (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx),
      show 2 * ((2 - Work.Spaces.gam α) / 2) = 2 - Work.Spaces.gam α by ring]
  have e3 : (∫ x in Set.Ioo a b,
        ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [rpow_sq _ _ (hsinpos x hx),
      show 2 * ((Work.Spaces.gam α - 2) / 2) = Work.Spaces.gam α - 2 by ring]
  have key : (∫ x in Set.Ioo a b, h x) ^ 2 ≤
      (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
        * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) := by
    calc (∫ x in Set.Ioo a b, h x) ^ 2
        = (∫ x in Set.Ioo a b,
            (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2))
              * (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2 := by rw [e1]
      _ ≤ (∫ x in Set.Ioo a b,
              (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
            * (∫ x in Set.Ioo a b,
                ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2) := hcs
      _ = (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
            * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) := by
            rw [e2, e3]
  -- monotonicity and the explicit bound for the singular weight
  have hA : (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
      ≤ ∫ s in Work.Spaces.Iθ,
          (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_mono_set hint hFnn hae_sub
  have hB : (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2))
      ≤ 100 / (Work.Spaces.gam α - 1) := by
    have h1 : (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2))
        ≤ ∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2) :=
      MeasureTheory.setIntegral_mono_set (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2)
        hp1 hp0).1 hSnn hae_sub
    have h2 : (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2))
        ≤ 100 / ((Work.Spaces.gam α - 2) + 1) :=
      (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).2
    have h3 : 100 / ((Work.Spaces.gam α - 2) + 1) = 100 / (Work.Spaces.gam α - 1) := by
      ring_nf
    exact h1.trans (h2.trans (le_of_eq h3))
  have hA0 : 0 ≤ ∫ s in Work.Spaces.Iθ,
      (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_nonneg hmIθ
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hB0 : 0 ≤ ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => Real.rpow_nonneg (hsinIθ x (hsub hx)) _)
  have hIoo : (∫ s in a..b, h s) = ∫ x in Set.Ioo a b, h x := by
    rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc (∫ s in a..b, h s) ^ 2
      = (∫ x in Set.Ioo a b, h x) ^ 2 := by rw [hIoo]
    _ ≤ (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
          * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) := key
    _ ≤ (∫ s in Work.Spaces.Iθ,
            (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α))
          * (100 / (Work.Spaces.gam α - 1)) := mul_le_mul hA hB hB0 hA0
    _ = (100 / (Work.Spaces.gam α - 1)) *
          ∫ s in Work.Spaces.Iθ,
            (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by ring

/-! ## The oscillation bound -/

theorem OscSqLe (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ) {θ θ₀ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ₀ : θ₀ ∈ Work.Spaces.Iθ)
    (hderiv : ∀ x ∈ Set.uIcc θ θ₀, HasDerivAt h (deriv h x) x)
    (hcont : ContinuousOn (deriv h) (Set.uIcc θ θ₀))
    (hint : MeasureTheory.IntegrableOn
      (fun σ => (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ) :
    (h θ - h θ₀) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1)) *
      ∫ σ in Work.Spaces.Iθ,
        (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hcont' : ContinuousOn (deriv h) (Set.uIcc θ₀ θ) := by
    rw [Set.uIcc_comm]
    exact hcont
  have hFTC : ∫ σ in θ₀..θ, deriv h σ = h θ - h θ₀ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hcont'.intervalIntegrable
    intro x hx
    refine hderiv x ?_
    rw [Set.uIcc_comm] at hx
    exact hx
  rcases le_total θ₀ θ with hle | hle
  · -- `θ₀ ≤ θ`: apply the core on `[θ₀, θ]`; the fundamental theorem gives the difference.
    have hcc : ContinuousOn (deriv h) (Set.Icc θ₀ θ) := by
      rw [← Set.uIcc_of_le hle, Set.uIcc_comm]
      exact hcont
    have hcore := coreInterval α hα hα1 (deriv h) hθ₀ hθ hle hcc hint
    rw [hFTC] at hcore
    exact hcore
  · -- `θ ≤ θ₀`: the core on `[θ, θ₀]`; the reversed interval integral has the same square.
    have hcc : ContinuousOn (deriv h) (Set.Icc θ θ₀) := by
      rw [← Set.uIcc_of_le hle]
      exact hcont
    have hcore := coreInterval α hα hα1 (deriv h) hθ hθ₀ hle hcc hint
    have hsym : (∫ σ in θ₀..θ, deriv h σ) = -(∫ σ in θ..θ₀, deriv h σ) :=
      intervalIntegral.integral_symm θ θ₀
    have hsq : (h θ - h θ₀) ^ 2 = (∫ σ in θ..θ₀, deriv h σ) ^ 2 := by
      rw [← hFTC, hsym]
      ring
    rw [hsq]
    exact hcore

end Work.FTS.H2
