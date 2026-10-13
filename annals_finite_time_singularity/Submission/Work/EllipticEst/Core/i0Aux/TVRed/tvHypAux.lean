/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for `tvHypBundle`

The target `tvHypBundle` (in `TVRed/tvHypBundle.lean`) is the *bookkeeping* step of the
reduction of the open angular interpolation to the trace-vanishing case: given `f` (with
`C²` regularity on `(0, π/2)`, two traces `F₀, F₁` and finite weighted energies) and the
trace-matching surrogate `surrFun ψ F₀ F₁ L`, the difference `f - surrFun ψ F₀ F₁ L` is
again `C²` on `(0, π/2)`, has *vanishing* traces, and has finite weighted energies
`∫ (·)² thEta`.

This file collects the measure-theoretic ingredients of that assembly:

* `Iθ = [0, π/2]` agrees with the open interval `(0, π/2)` almost everywhere, so an
  `IntegrableOn` statement over one set transfers to the other;
* `thEta` is a.e. strongly measurable on `Iθ` (it is continuous on the open interval);
* a function that is continuous on the open interval is a.e. strongly measurable on `Iθ`;
* the dominated-integrability wrapper `tvh_integrableOn_of_abs_le`;
* the elementary combination rule `tvh_integrableOn_sq_sub`: if the two weighted squares
  `u² thEta`, `v² thEta` are integrable then so is `(u - v)² thEta`;
* the derivative identities `deriv (f - u) = deriv f - deriv u` and
  `deriv (deriv (f - u)) = deriv (deriv f) - deriv (deriv u)` on the open interval, for
  `f` of class `C²` on `(0, π/2)` and `u` globally `C²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## 1. `Iθ` and `(0, π/2)` agree almost everywhere -/

/-- `Icc a b` and `Ioo a b` agree almost everywhere. -/
lemma tvh_ae_eq_Icc_Ioo (a b : ℝ) : Set.Icc a b =ᵐ[volume] Set.Ioo a b := by
  have hsub : Set.Icc a b \ Set.Ioo a b ⊆ ({a, b} : Set ℝ) := by
    rintro x ⟨hx, hx'⟩
    rw [Set.mem_Icc] at hx
    rw [Set.mem_Ioo] at hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hxa : x = a
    · exact Or.inl hxa
    · by_cases hxb : x = b
      · exact Or.inr hxb
      · exfalso
        exact hx' ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have h0 : volume (Set.Icc a b \ Set.Ioo a b) = 0 := by
    refine measure_mono_null hsub ?_
    exact (Set.finite_singleton b).insert a |>.measure_zero volume
  have hmem : ∀ᵐ x : ℝ, x ∉ (Set.Icc a b \ Set.Ioo a b) := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬x ∉ (Set.Icc a b \ Set.Ioo a b)} = Set.Icc a b \ Set.Ioo a b := by
      ext x; simp only [Set.mem_ofPred_eq, not_not]
    rw [hset]; exact h0
  filter_upwards [hmem] with x hx
  exact propext ⟨fun h1 => by by_contra h2; exact hx ⟨h1, h2⟩,
    fun h1 => ⟨le_of_lt h1.1, le_of_lt h1.2⟩⟩

/-- The closed angular interval and the open one agree almost everywhere. -/
lemma tvh_ae_eq_Iθ_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  simpa only [Work.Spaces.Iθ] using tvh_ae_eq_Icc_Ioo 0 (Real.pi / 2)

/-- `IntegrableOn` transfers from the open interval to `Iθ`. -/
lemma tvh_integrableOn_Iθ_of_Ioo {g : ℝ → ℝ}
    (h : IntegrableOn g (Set.Ioo 0 (Real.pi / 2))) : IntegrableOn g Work.Spaces.Iθ := by
  rw [IntegrableOn] at h ⊢
  rwa [Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo]

/-- `IntegrableOn` transfers from `Iθ` to the open interval. -/
lemma tvh_integrableOn_Ioo_of_Iθ {g : ℝ → ℝ}
    (h : IntegrableOn g Work.Spaces.Iθ) : IntegrableOn g (Set.Ioo 0 (Real.pi / 2)) := by
  rw [IntegrableOn] at h ⊢
  rwa [← Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo]

/-- Two functions agreeing on the open interval agree a.e. on `Iθ`. -/
lemma tvh_ae_eq_of_forall_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), g θ = h θ) :
    g =ᵐ[volume.restrict Work.Spaces.Iθ] h := by
  have hrestrict : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo
  rw [hrestrict]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => hgh θ hθ)

/-! ## 2. Almost-everywhere strong measurability on `Iθ` -/

/-- The angular weight `thEta θ = sin(2θ)^{-η}` is a.e. strongly measurable on `Iθ`: it is
continuous on the open interval `(0, π/2)`, and the two endpoints are null. -/
lemma tvh_aesm_thEta :
    AEStronglyMeasurable Work.FTS.EllipticEst.thEta (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo 0 (Real.pi / 2)) := by
    refine (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)).rpow_const ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (x := 2 * θ) (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  have h1 : AEStronglyMeasurable Work.FTS.EllipticEst.thEta
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  rw [show volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ from (Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo).symm] at h1
  exact h1

/-- A function that is continuous on the open interval `(0, π/2)` is a.e. strongly
measurable on `Iθ`. -/
lemma tvh_aesm_of_continuousOn {u : ℝ → ℝ}
    (h : ContinuousOn u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable u (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    h.aestronglyMeasurable measurableSet_Ioo
  rw [show volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ from (Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo).symm] at h1
  exact h1

/-- A function of class `C^n` on the open interval is a.e. strongly measurable on `Iθ`
(for `n = 0` this is just continuity there). -/
lemma tvh_aesm_of_contDiffOn {u : ℝ → ℝ} {n : WithTop ℕ∞}
    (h : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) :=
  tvh_aesm_of_continuousOn h.continuousOn

/-! ## 3. Dominated integrability on `Iθ` -/

/-- Domination by an integrable function on `Iθ` yields integrability. -/
lemma tvh_integrableOn_of_abs_le {g F : ℝ → ℝ}
    (hF : IntegrableOn F Work.Spaces.Iθ)
    (hg : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ F θ) : IntegrableOn g Work.Spaces.Iθ := by
  refine Integrable.mono' hF hg ?_
  refine (ae_restrict_iff' (measurableSet_Icc : MeasurableSet Work.Spaces.Iθ)).mpr ?_
  exact Eventually.of_forall fun θ hθ => by
    simpa only [Real.norm_eq_abs] using h θ hθ

/-- The angular weight is integrable on `Iθ`. -/
lemma tvh_thEta_integrableOn :
    IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.integrableOn_thEta.1

/-- A constant multiple of the angular weight is integrable on `Iθ`. -/
lemma tvh_integrableOn_const_mul_thEta (c : ℝ) :
    IntegrableOn (fun θ : ℝ => c * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
  tvh_thEta_integrableOn.const_mul c

/-! ## 4. The combination rule for weighted squares -/

/-- If the two weighted squares `u² thEta` and `v² thEta` are integrable on `Iθ`,
and `u`, `v` are a.e. strongly measurable there, then so is `(u - v)² thEta`. -/
lemma tvh_integrableOn_sq_sub {u v : ℝ → ℝ}
    (hu : IntegrableOn (fun θ : ℝ => u θ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hv : IntegrableOn (fun θ : ℝ => v θ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hau : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ))
    (hav : AEStronglyMeasurable v (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
  have hdom : IntegrableOn
      (fun θ : ℝ => 2 * (u θ ^ 2 * Work.FTS.EllipticEst.thEta θ
        + v θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
    (hu.add hv).const_mul 2
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => u θ - v θ)
        (volume.restrict Work.Spaces.Iθ) := hau.sub hav
    exact (h1.pow 2).mul tvh_aesm_thEta
  refine tvh_integrableOn_of_abs_le hdom haesm ?_
  intro θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have h1 : (u θ - v θ) ^ 2 ≤ 2 * (u θ ^ 2 + v θ ^ 2) := by
    nlinarith [sq_nonneg (u θ + v θ), sq_nonneg (u θ - v θ)]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
  calc (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ (2 * (u θ ^ 2 + v θ ^ 2)) * Work.FTS.EllipticEst.thEta θ :=
        mul_le_mul_of_nonneg_right h1 hσ
    _ = 2 * (u θ ^ 2 * Work.FTS.EllipticEst.thEta θ
          + v θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring

/-! ## 5. Derivative identities for `f - u` on the open interval -/

/-- First derivative of a difference: `deriv (f - u) = deriv f - deriv u` on `(0, π/2)`,
for `f` of class `C²` on that interval and `u` globally `C²`. -/
lemma tvh_deriv_sub {f u : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) (hu : ContDiff ℝ 2 u) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun θ : ℝ => f θ - u θ) θ = deriv f θ - deriv u θ := by
  intro θ hθ
  have hdf : DifferentiableAt ℝ f θ :=
    ((hf.contDiffAt (isOpen_Ioo.mem_nhds hθ))).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ u θ :=
    (hu.contDiffAt.differentiableAt) (by norm_num)
  exact deriv_sub hdf hdu

/-- Second derivative of a difference: `deriv (deriv (f - u)) = deriv (deriv f) -
deriv (deriv u)` on `(0, π/2)`. -/
lemma tvh_deriv2_sub {f u : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) (hu : ContDiff ℝ 2 u) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv (fun θ : ℝ => f θ - u θ)) θ = deriv (deriv f) θ - deriv (deriv u) θ := by
  intro θ hθ
  have hev : (fun y : ℝ => deriv f y - deriv u y)
      =ᶠ[𝓝 θ] deriv (fun θ : ℝ => f θ - u θ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    exact (tvh_deriv_sub hf hu y hy).symm
  rw [← hev.deriv_eq]
  have hdf : DifferentiableAt ℝ (deriv f) θ :=
    (((hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)).differentiableAt)
      (by norm_num)
  have hdu : DifferentiableAt ℝ (deriv u) θ := by
    have h1 : ContDiff ℝ 1 (deriv u) := by simpa using hu.deriv' (n := 1)
    exact h1.contDiffAt.differentiableAt (by norm_num)
  exact deriv_sub hdf hdu

/-! ## 6. Weighted integrability of the surrogate -/

/-- The surrogate and its first two derivatives satisfy global bounds depending only on
`C, F₀, F₁, L`, so their squares against the angular weight `thEta` are integrable on `Iθ`. -/
lemma tvh_surr_sq_integrable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) :
    IntegrableOn
        (fun θ : ℝ => (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    IntegrableOn
        (fun θ : ℝ => (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    IntegrableOn
        (fun θ : ℝ => (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hs : ContDiff ℝ 2 (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) :=
    surr_smooth hψ (ne_of_gt hL)
  have hds : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
    simpa using hs.deriv' (n := 1)
  have hdds : ContDiff ℝ 0 (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L))) := by
    simpa using hds.deriv' (n := 0)
  refine ⟨?_, ?_, ?_⟩
  · refine tvh_integrableOn_of_abs_le
      (tvh_integrableOn_const_mul_thEta ((|F₀| + |F₁|) ^ 2)) ?_ ?_
    · exact (hs.continuous.aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      refine mul_le_mul_of_nonneg_right ?_ hσ
      rw [← sq_abs (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (surr_bound hψ θ) 2
  · refine tvh_integrableOn_of_abs_le
      (tvh_integrableOn_const_mul_thEta ((C * (|F₀| + |F₁|) / L) ^ 2)) ?_ ?_
    · exact (hds.continuous.aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      refine mul_le_mul_of_nonneg_right ?_ hσ
      rw [← sq_abs (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (deriv_surr_bound hψ hL θ) 2
  · refine tvh_integrableOn_of_abs_le
      (tvh_integrableOn_const_mul_thEta ((C * (|F₀| + |F₁|) / L ^ 2) ^ 2)) ?_ ?_
    · exact (hdds.continuous.aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      refine mul_le_mul_of_nonneg_right ?_ hσ
      rw [← sq_abs (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (deriv2_surr_bound hψ hL θ) 2

end

end Work.EllipticEst.Core.i0Aux.TVRed
