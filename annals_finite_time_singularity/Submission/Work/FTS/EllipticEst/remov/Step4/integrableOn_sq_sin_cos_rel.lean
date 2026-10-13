/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of `X² σ` from a genuine pointwise relation

This file proves `Work.FTS.EllipticEst.remov.Step4.integrableOn_sq_sin_cos_rel`, an
elementary (but measure-theoretically slightly subtle) step-4 ingredient of the
`H²` estimate for T. M. Elgindi's finite-time singularity paper: if a function `X`
satisfies, on a set `s`, the *pointwise* relation

  `X θ = sin θ · A θ + 2 cos θ · B θ - sin θ · C θ`,

and `σ ≥ 0` on `s`, then from the integrability of `A² σ`, `B² σ`, `C² σ` on `s`
(and the a.e. strong measurability of `X` and `σ`) one gets both the integrability
of `X² σ` on `s` and the quantitative bound

  `∫_s X² σ ≤ 3 (∫_s A² σ + 4 ∫_s B² σ + ∫_s C² σ)`.

The mathematical content is the elementary inequality
`(p + q + r)² ≤ 3 (p² + q² + r²)` applied to `p = sin θ · A θ`, `q = 2 cos θ · B θ`,
`r = -sin θ · C θ`, together with `sin² , cos² ≤ 1` and `σ ≥ 0`:

  `X² σ ≤ 3 (A² σ + 4 B² σ + C² σ)`  on `s`.

The measure-theoretic point is that this pointwise bound is only available on `s`, while
integrability is asked with respect to `volume.restrict s`; for a badly non-measurable `s`
the naive `∀ᵐ`-transfer of a pointwise bound on `s` is *false*.  The way around it is
to work with measurable *representatives* `f'`, `g'` of the two functions: the "bad set"
`{g' < f'}` is then measurable, and it meets `s` only inside the (a.e. small) sets where
`f' ≠ f` resp. `g' ≠ g`; a set which is null for `volume.restrict s` has Lebesgue-null
intersection with `s`, and a measurable set meeting `s` in a Lebesgue-null set is itself
null for `volume.restrict s` (as its measure is the Lebesgue measure of its intersection
with `s`).  This is `restrict_measure_eq_zero_of_subset` below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Step4

open MeasureTheory

/-! ### Null sets for `volume.restrict s` versus null sets for `volume` -/

/-- If `N` is null for `volume.restrict s`, then `s ∩ N` is Lebesgue-null. -/
lemma volume_inter_eq_zero_of_restrict_eq_zero {s N : Set ℝ}
    (h : (volume.restrict s) N = 0) : volume (s ∩ N) = 0 := by
  have hB : MeasurableSet (toMeasurable (volume.restrict s) N) :=
    measurableSet_toMeasurable _ _
  have hNB : N ⊆ toMeasurable (volume.restrict s) N := subset_toMeasurable _ _
  have hsub : s ∩ N ⊆ s ∩ toMeasurable (volume.restrict s) N := by
    intro x hx
    exact ⟨hx.1, hNB hx.2⟩
  have hle0 : volume (s ∩ N) ≤ 0 := by
    calc volume (s ∩ N)
        ≤ volume (s ∩ toMeasurable (volume.restrict s) N) := measure_mono hsub
      _ = volume (toMeasurable (volume.restrict s) N ∩ s) := by rw [Set.inter_comm]
      _ = (volume.restrict s) (toMeasurable (volume.restrict s) N) :=
          (Measure.restrict_apply hB).symm
      _ = (volume.restrict s) N := measure_toMeasurable N
      _ = 0 := h
  exact le_antisymm hle0 (zero_le)

/-- A *measurable* set `T` which meets `s` only where the measurable functions `f'`, `g'`
disagree with `f`, `g` is null for `volume.restrict s`. -/
lemma restrict_measure_eq_zero_of_subset {s T : Set ℝ} (hT : MeasurableSet T)
    {f f' g g' : ℝ → ℝ} (hfeq : f =ᵐ[volume.restrict s] f')
    (hgeq : g =ᵐ[volume.restrict s] g')
    (hsub : T ∩ s ⊆ (s ∩ {x | f x ≠ f' x}) ∪ (s ∩ {x | g x ≠ g' x})) :
    (volume.restrict s) T = 0 := by
  have h1 : volume (s ∩ {x | f x ≠ f' x}) = 0 :=
    volume_inter_eq_zero_of_restrict_eq_zero (ae_iff.mp hfeq)
  have h2 : volume (s ∩ {x | g x ≠ g' x}) = 0 :=
    volume_inter_eq_zero_of_restrict_eq_zero (ae_iff.mp hgeq)
  have hvol : volume (T ∩ s) = 0 :=
    measure_mono_null hsub (measure_union_null h1 h2)
  rwa [Measure.restrict_apply hT]

/-! ### Transferring pointwise bounds on `s` to measurable representatives -/

/-- If `f ≤ g` pointwise on `s`, then the measurable representatives of `f` and `g`
satisfy `f' ≤ g'` a.e. with respect to `volume.restrict s`. -/
theorem ae_le_mk_of_forall_le_on {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hg : AEStronglyMeasurable g (volume.restrict s))
    (hle : ∀ x ∈ s, f x ≤ g x) :
    AEStronglyMeasurable.mk f hf ≤ᵐ[volume.restrict s] AEStronglyMeasurable.mk g hg := by
  refine (ae_iff).mpr ?_
  rw [show {x : ℝ | ¬ (AEStronglyMeasurable.mk f hf x ≤ AEStronglyMeasurable.mk g hg x)} =
      {x : ℝ | AEStronglyMeasurable.mk g hg x < AEStronglyMeasurable.mk f hf x} by
    ext x
    exact not_le]
  refine restrict_measure_eq_zero_of_subset
    (measurableSet_lt (hg.stronglyMeasurable_mk).measurable
      (hf.stronglyMeasurable_mk).measurable) hf.ae_eq_mk hg.ae_eq_mk ?_
  rintro x ⟨hgx, hxs⟩
  by_cases h1 : f x = AEStronglyMeasurable.mk f hf x
  · by_cases h2 : g x = AEStronglyMeasurable.mk g hg x
    · exact absurd (hle x hxs) (not_le.mpr (by
        have hgf : AEStronglyMeasurable.mk g hg x < AEStronglyMeasurable.mk f hf x := hgx
        rwa [← h2, ← h1] at hgf))
    · exact Or.inr ⟨hxs, h2⟩
  · exact Or.inl ⟨hxs, h1⟩

/-- If `0 ≤ f ≤ g` pointwise on `s`, then the measurable representatives of `f` and `g`
satisfy `‖f'‖ ≤ ‖g'‖` a.e. with respect to `volume.restrict s`. -/
theorem ae_norm_mk_le_of_forall_le_on {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hg : AEStronglyMeasurable g (volume.restrict s))
    (hfn : ∀ x ∈ s, 0 ≤ f x) (hgn : ∀ x ∈ s, 0 ≤ g x)
    (hle : ∀ x ∈ s, f x ≤ g x) :
    ∀ᵐ x ∂(volume.restrict s),
      ‖AEStronglyMeasurable.mk f hf x‖ ≤ ‖AEStronglyMeasurable.mk g hg x‖ := by
  refine (ae_iff).mpr ?_
  rw [show {x : ℝ | ¬ (‖AEStronglyMeasurable.mk f hf x‖ ≤
        ‖AEStronglyMeasurable.mk g hg x‖)} =
      {x : ℝ | ‖AEStronglyMeasurable.mk g hg x‖ < ‖AEStronglyMeasurable.mk f hf x‖} by
    ext x
    exact not_le]
  refine restrict_measure_eq_zero_of_subset
    (measurableSet_lt ((hg.stronglyMeasurable_mk).measurable.norm)
      ((hf.stronglyMeasurable_mk).measurable.norm)) hf.ae_eq_mk hg.ae_eq_mk ?_
  rintro x ⟨hgx, hxs⟩
  by_cases h1 : f x = AEStronglyMeasurable.mk f hf x
  · by_cases h2 : g x = AEStronglyMeasurable.mk g hg x
    · refine absurd (hle x hxs) (not_le.mpr ?_)
      have h3 : ‖AEStronglyMeasurable.mk f hf x‖ = f x := by
        rw [← h1, Real.norm_eq_abs, abs_of_nonneg (hfn x hxs)]
      have h4 : ‖AEStronglyMeasurable.mk g hg x‖ = g x := by
        rw [← h2, Real.norm_eq_abs, abs_of_nonneg (hgn x hxs)]
      have hgf : ‖AEStronglyMeasurable.mk g hg x‖ < ‖AEStronglyMeasurable.mk f hf x‖ := hgx
      rwa [h3, h4] at hgf
    · exact Or.inr ⟨hxs, h2⟩
  · exact Or.inl ⟨hxs, h1⟩

/-! ### The main statement -/

theorem integrableOn_sq_sin_cos_rel {s : Set ℝ} {σ X A B C : ℝ → ℝ}
    (hσ0 : ∀ θ ∈ s, 0 ≤ σ θ)
    (hrel : ∀ θ ∈ s, X θ = Real.sin θ * A θ + 2 * Real.cos θ * B θ - Real.sin θ * C θ)
    (hXm : MeasureTheory.AEStronglyMeasurable X (MeasureTheory.volume.restrict s))
    (hσm : MeasureTheory.AEStronglyMeasurable σ (MeasureTheory.volume.restrict s))
    (hA : MeasureTheory.IntegrableOn (fun θ => (A θ) ^ 2 * σ θ) s)
    (hB : MeasureTheory.IntegrableOn (fun θ => (B θ) ^ 2 * σ θ) s)
    (hC : MeasureTheory.IntegrableOn (fun θ => (C θ) ^ 2 * σ θ) s) :
    MeasureTheory.IntegrableOn (fun θ => (X θ) ^ 2 * σ θ) s
      ∧ (∫ θ in s, (X θ) ^ 2 * σ θ)
        ≤ 3 * ((∫ θ in s, (A θ) ^ 2 * σ θ) + 4 * (∫ θ in s, (B θ) ^ 2 * σ θ)
            + (∫ θ in s, (C θ) ^ 2 * σ θ)) := by
  set f : ℝ → ℝ := fun θ => (X θ) ^ 2 * σ θ with hf_def
  set uA : ℝ → ℝ := fun θ => (A θ) ^ 2 * σ θ with huA_def
  set uB : ℝ → ℝ := fun θ => (B θ) ^ 2 * σ θ with huB_def
  set uC : ℝ → ℝ := fun θ => (C θ) ^ 2 * σ θ with huC_def
  set g : ℝ → ℝ := fun θ => 3 * (uA θ + 4 * uB θ + uC θ) with hg_def
  -- Integrability of the pieces and of `g`.
  have huA_int : Integrable uA (volume.restrict s) := by
    rw [huA_def]; exact hA.integrable
  have huB_int : Integrable uB (volume.restrict s) := by
    rw [huB_def]; exact hB.integrable
  have huC_int : Integrable uC (volume.restrict s) := by
    rw [huC_def]; exact hC.integrable
  have h1_int : Integrable (fun θ => uA θ + 4 * uB θ) (volume.restrict s) :=
    huA_int.add (huB_int.const_mul 4)
  have h2_int : Integrable (fun θ => uA θ + 4 * uB θ + uC θ) (volume.restrict s) :=
    h1_int.add huC_int
  have hg_int : Integrable g (volume.restrict s) := by
    simp only [hg_def]
    exact h2_int.const_mul 3
  -- A.e. strong measurability of `f` and `g`.
  have hf_aesm : AEStronglyMeasurable f (volume.restrict s) := by
    simp only [hf_def]
    exact (hXm.pow 2).mul hσm
  have hg_aesm : AEStronglyMeasurable g (volume.restrict s) := by
    simp only [hg_def]
    exact ((huA_int.aestronglyMeasurable.add
      (huB_int.aestronglyMeasurable.const_mul 4)).add huC_int.aestronglyMeasurable).const_mul 3
  -- The pointwise bound on `s`, from `(p+q+r)² ≤ 3(p²+q²+r²)`.
  have hfg : ∀ θ ∈ s, f θ ≤ g θ := by
    intro θ hθ
    have hσθ : 0 ≤ σ θ := hσ0 θ hθ
    have hkey : (Real.sin θ * A θ + 2 * Real.cos θ * B θ - Real.sin θ * C θ) ^ 2
        ≤ 3 * ((A θ) ^ 2 + 4 * (B θ) ^ 2 + (C θ) ^ 2) := by
      have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
      have hc1 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
      have h1 : Real.sin θ ^ 2 * (A θ) ^ 2 ≤ (A θ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hs1 (sq_nonneg (A θ))]
      have h2 : Real.cos θ ^ 2 * (B θ) ^ 2 ≤ (B θ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hc1 (sq_nonneg (B θ))]
      have h3 : Real.sin θ ^ 2 * (C θ) ^ 2 ≤ (C θ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hs1 (sq_nonneg (C θ))]
      nlinarith [sq_nonneg (Real.sin θ * A θ - 2 * Real.cos θ * B θ),
        sq_nonneg (2 * Real.cos θ * B θ + Real.sin θ * C θ),
        sq_nonneg (Real.sin θ * A θ + Real.sin θ * C θ), h1, h2, h3]
    have hstep : (X θ) ^ 2 * σ θ
        ≤ (3 * ((A θ) ^ 2 + 4 * (B θ) ^ 2 + (C θ) ^ 2)) * σ θ := by
      rw [hrel θ hθ]
      exact mul_le_mul_of_nonneg_right hkey hσθ
    have hrt : (3 * ((A θ) ^ 2 + 4 * (B θ) ^ 2 + (C θ) ^ 2)) * σ θ = g θ := by
      simp only [hg_def, huA_def, huB_def, huC_def]
      ring
    simp only [hf_def]
    rw [← hrt]
    exact hstep
  have hf_nn : ∀ θ ∈ s, 0 ≤ f θ := by
    intro θ hθ
    simp only [hf_def]
    exact mul_nonneg (sq_nonneg _) (hσ0 θ hθ)
  have hg_nn : ∀ θ ∈ s, 0 ≤ g θ := by
    intro θ hθ
    have hσθ : 0 ≤ σ θ := hσ0 θ hθ
    have h1 : 0 ≤ (A θ) ^ 2 * σ θ := mul_nonneg (sq_nonneg _) hσθ
    have h2 : 0 ≤ (B θ) ^ 2 * σ θ := mul_nonneg (sq_nonneg _) hσθ
    have h3 : 0 ≤ (C θ) ^ 2 * σ θ := mul_nonneg (sq_nonneg _) hσθ
    simp only [hg_def, huA_def, huB_def, huC_def]
    linarith
  -- Measurable representatives.
  set f' : ℝ → ℝ := AEStronglyMeasurable.mk f hf_aesm with hf'_def
  set g' : ℝ → ℝ := AEStronglyMeasurable.mk g hg_aesm with hg'_def
  have hf'meas : Measurable f' := by
    rw [hf'_def]; exact (hf_aesm.stronglyMeasurable_mk).measurable
  have hg'meas : Measurable g' := by
    rw [hg'_def]; exact (hg_aesm.stronglyMeasurable_mk).measurable
  have hf'eq : f =ᵐ[volume.restrict s] f' := by
    rw [hf'_def]; exact hf_aesm.ae_eq_mk
  have hg'eq : g =ᵐ[volume.restrict s] g' := by
    rw [hg'_def]; exact hg_aesm.ae_eq_mk
  have hle' : f' ≤ᵐ[volume.restrict s] g' := by
    rw [hf'_def, hg'_def]
    exact ae_le_mk_of_forall_le_on hf_aesm hg_aesm hfg
  -- Integrability of `f`, first for the representative, then for `f` itself.
  have hg'_int : Integrable g' (volume.restrict s) := hg_int.congr hg'eq
  have hbound' : ∀ᵐ x ∂(volume.restrict s), ‖f' x‖ ≤ ‖g' x‖ := by
    rw [hf'_def, hg'_def]
    exact ae_norm_mk_le_of_forall_le_on hf_aesm hg_aesm hf_nn hg_nn hfg
  have hf'_int : Integrable f' (volume.restrict s) :=
    Integrable.mono' hg'_int.norm hf'meas.aestronglyMeasurable hbound'
  have hf_int : Integrable f (volume.restrict s) := hf'_int.congr hf'eq.symm
  -- Comparison of the integrals.
  have hmono : ∫ x, f' x ∂(volume.restrict s) ≤ ∫ x, g' x ∂(volume.restrict s) :=
    integral_mono_ae hf'_int hg'_int hle'
  have hsplit : ∫ x, g x ∂(volume.restrict s)
      = 3 * ((∫ x, uA x ∂(volume.restrict s)) + 4 * (∫ x, uB x ∂(volume.restrict s))
          + (∫ x, uC x ∂(volume.restrict s))) := by
    simp only [hg_def]
    rw [integral_const_mul 3 (fun x => uA x + 4 * uB x + uC x),
      integral_add (f := fun x => uA x + 4 * uB x) (g := fun x => uC x) h1_int huC_int,
      integral_add (f := fun x => uA x) (g := fun x => 4 * uB x) huA_int
        (huB_int.const_mul 4),
      integral_const_mul 4 (fun x => uB x)]
  have hmain : (∫ x, f x ∂(volume.restrict s))
      ≤ 3 * ((∫ x, uA x ∂(volume.restrict s)) + 4 * (∫ x, uB x ∂(volume.restrict s))
          + (∫ x, uC x ∂(volume.restrict s))) := by
    calc (∫ x, f x ∂(volume.restrict s)) = ∫ x, f' x ∂(volume.restrict s) :=
          integral_congr_ae hf'eq
      _ ≤ ∫ x, g' x ∂(volume.restrict s) := hmono
      _ = ∫ x, g x ∂(volume.restrict s) := integral_congr_ae hg'eq.symm
      _ = 3 * ((∫ x, uA x ∂(volume.restrict s)) + 4 * (∫ x, uB x ∂(volume.restrict s))
            + (∫ x, uC x ∂(volume.restrict s))) := hsplit
  refine ⟨?_, ?_⟩
  · simp only [IntegrableOn, hf_def]
    exact hf_int
  · simp only [hf_def, huA_def, huB_def, huC_def]
    exact hmain

end Work.FTS.EllipticEst.remov.Step4
