import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.integrable_chiMul_integral`

For a radial-`L¹` symbol `F` (`∫_p ‖F ‖p‖‖ dp < ∞`), the `t`-dependent function

    `t ↦ ∫_p F ‖p‖ · profHat (ℓ · p) · χ t · cos⟪ℓ · p, t⟫ dp`

is Lebesgue-integrable on `ℝ³`.

The inner `p`-integral is the (real part of the) cosine transform of the `L¹` function
`p ↦ F ‖p‖ · profHat (ℓ · p)`, hence a bounded function of `t`, so the whole thing is
`(bounded function) · χ t` with `χ` a compactly supported bump.

The proof has three ingredients:

* the bump profile is bounded, `|profHat q| ≤ ∫_z |χ z| dz`, so `p ↦ F ‖p‖ · profHat (ℓ · p)`
  is `L¹` (dominated by a constant times `p ↦ F ‖p‖`);
* `profHat` is continuous (dominated convergence in the defining integral);
* the resulting `t`-integral is continuous (dominated convergence again) and bounded by
  `(∫_p ‖F ‖p‖‖) · (∫_z |χ z|) · ‖χ t‖`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary API of the bump profile `profHat` -/

/-- **The bump profile is bounded by the total mass of the bump**:
`|profHat p| ≤ ∫_z |χ z| dz`.  This is the elementary `L¹ → L^∞` bound for the cosine transform
of the compactly supported bump `χ` (`‖cos‖ ≤ 1`); no decay of `profHat` is needed. -/
lemma profHat_abs_le_mass (p : ℝ³) : |profHat p| ≤ ∫ z : ℝ³, |chi z| := by
  have hchi : Integrable (fun z : ℝ³ => chi z) :=
    chi_continuous.integrable_of_hasCompactSupport chi_hasCompactSupport
  have hcos : Continuous (fun z : ℝ³ => Real.cos (inner ℝ p z)) :=
    Real.continuous_cos.comp (continuous_const.inner continuous_id)
  have hcont : Continuous (fun z : ℝ³ => chi z * Real.cos (inner ℝ p z)) :=
    chi_continuous.mul hcos
  have hb : ∀ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖ ≤ ‖chi z‖ := by
    intro z
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ p z))
  have hg : Integrable (fun z : ℝ³ => ‖chi z * Real.cos (inner ℝ p z)‖) := by
    refine Integrable.mono' hchi.norm hcont.norm.aestronglyMeasurable ?_
    filter_upwards with z
    simpa using hb z
  have hm : ‖∫ z : ℝ³, chi z * Real.cos (inner ℝ p z)‖
      ≤ ∫ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖ :=
    norm_integral_le_integral_norm _
  have h2 : (∫ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖) ≤ ∫ z : ℝ³, ‖chi z‖ :=
    integral_mono hg hchi.norm hb
  rw [profHat]
  calc |∫ z : ℝ³, chi z * Real.cos (inner ℝ p z)|
      = ‖∫ z : ℝ³, chi z * Real.cos (inner ℝ p z)‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖ := hm
    _ ≤ ∫ z : ℝ³, ‖chi z‖ := h2
    _ = ∫ z : ℝ³, |chi z| := by simp [Real.norm_eq_abs]

/-- **The bump profile is continuous**: `profHat p = ∫_z χ z · cos⟪p, z⟫ dz` is the
`p`-parametric integral of a jointly continuous function dominated by the integrable `|χ|`. -/
lemma continuous_profHat : Continuous (profHat : ℝ³ → ℝ) := by
  have hchi : Integrable (fun z : ℝ³ => chi z) :=
    chi_continuous.integrable_of_hasCompactSupport chi_hasCompactSupport
  have hbound : Integrable (fun z : ℝ³ => ‖chi z‖) := hchi.norm
  have hmeas : ∀ p : ℝ³,
      AEStronglyMeasurable (fun z : ℝ³ => chi z * Real.cos (inner ℝ p z)) := fun p =>
    (chi_continuous.mul
      (Real.continuous_cos.comp (continuous_const.inner continuous_id))).aestronglyMeasurable
  have hbd : ∀ p : ℝ³, ∀ᵐ z : ℝ³ ∂volume, ‖chi z * Real.cos (inner ℝ p z)‖ ≤ ‖chi z‖ := by
    intro p
    filter_upwards with z
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ p z))
  have hcont : ∀ᵐ z : ℝ³ ∂volume,
      Continuous (fun p : ℝ³ => chi z * Real.cos (inner ℝ p z)) :=
    Filter.Eventually.of_forall (fun z => continuous_const.mul
      (Real.continuous_cos.comp (continuous_id.inner continuous_const)))
  have key := continuous_of_dominated
    (F := fun (p : ℝ³) (z : ℝ³) => chi z * Real.cos (inner ℝ p z))
    (bound := fun z : ℝ³ => ‖chi z‖) hmeas hbd hbound hcont
  exact key

/-! ## The main theorem -/

theorem integrable_chiMul_integral {ℓ : ℝ} {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖)) :
    MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin 3) =>
        ∫ p : EuclideanSpace ℝ (Fin 3),
          F ‖p‖ * Work.OneBodyKin.profHat (ℓ • p) * Submission.BoseGases.chi t *
            Real.cos (inner ℝ (ℓ • p) t)) := by
  -- total mass of the bump and the sup bound on `χ`
  set C : ℝ := ∫ z : ℝ³, |chi z| with hC
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun z => abs_nonneg (chi z))
  set B : ℝ := (Real.sqrt chiNormSq)⁻¹ with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hchi_bd : ∀ t : ℝ³, ‖chi t‖ ≤ B := by
    intro t
    have hspos : 0 < Real.sqrt chiNormSq := Real.sqrt_pos.mpr chiNormSq_pos
    have h1 : |chiBase t| ≤ 1 := by
      rw [abs_of_nonneg (chiBase_nonneg t)]; exact chiBase_le_one t
    rw [Real.norm_eq_abs, chi, abs_div, abs_of_pos hspos, hB, div_eq_mul_inv]
    simpa using mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hspos.le)
  -- the `p`-integrand `g`
  set g : ℝ³ → ℝ := fun p => F ‖p‖ * profHat (ℓ • p) with hg
  have hgp : ∀ p : ℝ³, ‖g p‖ ≤ C * ‖F ‖p‖‖ := by
    intro p
    rw [hg]
    change ‖F ‖p‖ * profHat (ℓ • p)‖ ≤ C * ‖F ‖p‖‖
    have hp : ‖profHat (ℓ • p)‖ ≤ C := by
      rw [Real.norm_eq_abs, hC]; exact profHat_abs_le_mass (ℓ • p)
    rw [norm_mul]
    calc ‖F ‖p‖‖ * ‖profHat (ℓ • p)‖ ≤ ‖F ‖p‖‖ * C :=
          mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = C * ‖F ‖p‖‖ := by ring
  have hgmeas : AEStronglyMeasurable g := by
    rw [hg]
    exact hFi.aestronglyMeasurable.mul
      ((continuous_profHat.comp (continuous_const_smul ℓ)).aestronglyMeasurable)
  have hg_int : Integrable g := by
    refine Integrable.mono' ((hFi.norm).const_mul C) hgmeas ?_
    filter_upwards with p
    exact hgp p
  -- the `t`-integrand
  set H : ℝ³ → ℝ³ → ℝ := fun t p => (g p * chi t) * Real.cos (inner ℝ (ℓ • p) t) with hH
  have hpt : ∀ t p : ℝ³, ‖H t p‖ ≤ ‖g p‖ * ‖chi t‖ := by
    intro t p
    rw [hH]
    change ‖(g p * chi t) * Real.cos (inner ℝ (ℓ • p) t)‖ ≤ ‖g p‖ * ‖chi t‖
    rw [norm_mul, norm_mul]
    have hcos : ‖Real.cos (inner ℝ (ℓ • p) t)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    calc ‖g p‖ * ‖chi t‖ * ‖Real.cos (inner ℝ (ℓ • p) t)‖ ≤ ‖g p‖ * ‖chi t‖ * 1 :=
          mul_le_mul_of_nonneg_left hcos (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖g p‖ * ‖chi t‖ := by ring
  have hHmeas : ∀ t : ℝ³, AEStronglyMeasurable (fun p : ℝ³ => H t p) := by
    intro t
    rw [hH]
    change AEStronglyMeasurable (fun p : ℝ³ => (g p * chi t) * Real.cos (inner ℝ (ℓ • p) t))
    exact (hgmeas.mul_const (chi t)).mul
      ((Real.continuous_cos.comp
        ((continuous_const_smul ℓ).inner continuous_const)).aestronglyMeasurable)
  -- continuity of the `t`-parametrised integral
  have hHcont : Continuous (fun t : ℝ³ => ∫ p : ℝ³, H t p) := by
    refine continuous_of_dominated
      (F := fun (t : ℝ³) (p : ℝ³) => H t p)
      (bound := fun p : ℝ³ => (C * B) * ‖F ‖p‖‖) hHmeas ?_
      ((hFi.norm).const_mul (C * B)) ?_
    · intro t
      filter_upwards with p
      calc ‖H t p‖ ≤ ‖g p‖ * ‖chi t‖ := hpt t p
        _ ≤ (C * ‖F ‖p‖‖) * B :=
              mul_le_mul (hgp p) (hchi_bd t) (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
        _ = (C * B) * ‖F ‖p‖‖ := by ring
    · exact Filter.Eventually.of_forall (fun p => by
        rw [hH]
        change Continuous (fun t : ℝ³ => (g p * chi t) * Real.cos (inner ℝ (ℓ • p) t))
        exact (continuous_const.mul chi_continuous).mul
          (Real.continuous_cos.comp (continuous_const.inner continuous_id)))
  -- final domination
  set M : ℝ := ∫ p : ℝ³, ‖g p‖ with hM
  have hH_int : ∀ t : ℝ³, Integrable (fun p : ℝ³ => ‖H t p‖) := by
    intro t
    refine Integrable.mono' ((hg_int.norm).mul_const (‖chi t‖)) ((hHmeas t).norm) ?_
    filter_upwards with p
    simpa using hpt t p
  change MeasureTheory.Integrable (fun t : ℝ³ => ∫ p : ℝ³, H t p)
  refine Integrable.mono' (g := fun t : ℝ³ => M * ‖chi t‖)
    ?_ hHcont.aestronglyMeasurable ?_
  · exact (chi_continuous.integrable_of_hasCompactSupport chi_hasCompactSupport).norm.const_mul M
  · filter_upwards with t
    calc ‖∫ p : ℝ³, H t p‖ ≤ ∫ p : ℝ³, ‖H t p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p : ℝ³, ‖g p‖ * ‖chi t‖ :=
            integral_mono (hH_int t) ((hg_int.norm).mul_const (‖chi t‖)) (fun p => hpt t p)
      _ = (∫ p : ℝ³, ‖g p‖) * ‖chi t‖ :=
            integral_mul_const (‖chi t‖) (fun p : ℝ³ => ‖g p‖)
      _ = M * ‖chi t‖ := by rw [hM]

end Work.OneBodyKin
