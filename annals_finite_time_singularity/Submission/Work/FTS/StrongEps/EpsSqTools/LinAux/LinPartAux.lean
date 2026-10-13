/-
Copyright: work module for the Elgindi finite-time singularity project.

# `LinAux/LinPartAux.lean` — the measure-theoretic toolkit for `EpsSq_LinPart_le`

The junk-safe manipulation rules for the weighted size `EpsSq α f = ∫_z∫_θ (f·epsW α)²` of
`EpsSpace.lean` together with its companion membership predicate `EpsMem`:

* `EpsMem_iff_integrable` (the product-measure form), `AK` (a.e. strong measurability of the
  weighted profile) with its closure rules, `EpsMem_of_lintegral`, `EpsMem_add/sub/neg/const_mul`;
* `EpsSq_le_of_le(_on)` (domination), `EpsSq_add_le_of_mem`, `EpsSq_const_mul`, `EpsSq_neg`,
  `EpsSq_sub_le_of_mem`, and congruence rules along pointwise (or integrand-wise) equalities;
* `EpsSq_le_of_majorant` (the master domination lemma used by the shell argument), and
  `EpsSq_gam_mul` (the exact factorisation of `EpsSq` of an angular profile times a radial one).

Everything below is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## The product-measure form of the memberships -/

/-- The product of the two restricted measures is the restriction of the volume to the domain. -/
theorem prodRestrict_eq (s t : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (s ×ˢ t)
      = (volume.restrict s).prod (volume.restrict t) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]

/-- `EpsMem` as integrability for the product measure on the domain. -/
theorem EpsMem_iff_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} :
    EpsMem α f ↔ MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [EpsMem, MeasureTheory.IntegrableOn, prodRestrict_eq Work.Spaces.Iz Work.Spaces.Iθ]

/-- Almost-everywhere strong measurability of the weighted profile on the domain. -/
abbrev AK (α : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2)
    ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))

theorem AK_add {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : AK α f) (hg : AK α g) :
    AK α (fun z θ => f z θ + g z θ) := by
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2
      + g p.1 p.2 * epsW α p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.add hf hg
  refine h.congr ?_
  filter_upwards with p
  ring

theorem AK_neg {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : AK α f) : AK α (fun z θ => -f z θ) := by
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => -(f p.1 p.2 * epsW α p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.neg hf
  refine h.congr ?_
  filter_upwards with p
  ring

theorem AK_sub {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : AK α f) (hg : AK α g) :
    AK α (fun z θ => f z θ - g z θ) :=
  AK_add hf (AK_neg hg)

theorem AK_const_mul {α : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ) (hf : AK α f) :
    AK α (fun z θ => c * f z θ) := by
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => c * (f p.1 p.2 * epsW α p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.const_mul hf c
  refine h.congr ?_
  filter_upwards with p
  ring

theorem AK_mul_fst {α : ℝ} {f : ℝ → ℝ → ℝ} {c : ℝ → ℝ} (hc : Measurable c) (hf : AK α f) :
    AK α (fun z θ => c z * f z θ) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => c p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hc.comp measurable_fst).aestronglyMeasurable
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => c p.1 * (f p.1 p.2 * epsW α p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.mul hm hf
  refine h.congr ?_
  filter_upwards with p
  ring

theorem AK_congr {α : ℝ} {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) (hg : AK α g) :
    AK α f := by
  refine hg.congr ?_
  filter_upwards with p
  simp only [h p.1 p.2]

/-! ## Membership under domination -/

theorem EpsMem_of_lintegral {α : ℝ} {f : ℝ → ℝ → ℝ} (hak : AK α f)
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f z θ * epsW α z θ) ^ 2)) < ⊤) :
    EpsMem α f := by
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.pow hak 2
  refine (EpsMem_iff_integrable (α := α)).mpr ⟨haesm, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  have hme : AEMeasurable
      (Function.uncurry fun z θ => ENNReal.ofReal ((f z θ * epsW α z θ) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    convert haesm.aemeasurable.ennreal_ofReal using 1
    ext p; rfl
  rw [← MeasureTheory.lintegral_lintegral (μ := volume.restrict Work.Spaces.Iz)
    (ν := volume.restrict Work.Spaces.Iθ) hme]
  exact hfin

theorem EpsMem_ext {α : ℝ} {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ)
    (hf : EpsMem α f) : EpsMem α g := by
  rw [EpsMem] at hf ⊢
  refine hf.congr ?_
  filter_upwards with p
  rw [h p.1 p.2]

theorem EpsSq_ext {α : ℝ} {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) :
    EpsSq α f = EpsSq α g := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with θ
  rw [h z θ]

theorem EpsMem_neg {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : EpsMem α f) :
    EpsMem α (fun z θ => -f z θ) := by
  rw [EpsMem] at hf ⊢
  refine hf.congr ?_
  filter_upwards with p
  ring

theorem EpsMem_add {α : ℝ} {f g : ℝ → ℝ → ℝ} (hakf : AK α f) (hakg : AK α g)
    (hf : EpsMem α f) (hg : EpsMem α g) :
    EpsMem α (fun z θ => f z θ + g z θ) := by
  refine (EpsMem_iff_integrable (α := α)).mpr ?_
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ((f p.1 p.2 + g p.1 p.2) * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEStronglyMeasurable.pow (AK_add hakf hakg) 2
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * (f p.1 p.2 * epsW α p.1 p.2) ^ 2 + 2 * (g p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (((EpsMem_iff_integrable (α := α)).mp hf).const_mul 2).add
      (((EpsMem_iff_integrable (α := α)).mp hg).const_mul 2)
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  · filter_upwards with p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h : ((f p.1 p.2 + g p.1 p.2) * epsW α p.1 p.2) ^ 2
        = (f p.1 p.2 * epsW α p.1 p.2 + g p.1 p.2 * epsW α p.1 p.2) ^ 2 := by ring
    rw [h]
    nlinarith [sq_nonneg (f p.1 p.2 * epsW α p.1 p.2),
      sq_nonneg (g p.1 p.2 * epsW α p.1 p.2),
      sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 + g p.1 p.2 * epsW α p.1 p.2),
      sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 - g p.1 p.2 * epsW α p.1 p.2)]

theorem EpsMem_sub {α : ℝ} {f g : ℝ → ℝ → ℝ} (hakf : AK α f) (hakg : AK α g)
    (hf : EpsMem α f) (hg : EpsMem α g) :
    EpsMem α (fun z θ => f z θ - g z θ) :=
  EpsMem_ext (fun _ _ => (sub_eq_add_neg _ _).symm)
    (EpsMem_add hakf (AK_neg hakg) hf (EpsMem_neg hg))

theorem EpsMem_const_mul {α : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ) (hf : EpsMem α f) :
    EpsMem α (fun z θ => c * f z θ) := by
  refine (EpsMem_iff_integrable (α := α)).mpr ?_
  refine (((EpsMem_iff_integrable (α := α)).mp hf).const_mul (c ^ 2)).congr ?_
  filter_upwards with p
  ring

theorem EpsSq_le_of_le {α : ℝ} {f g : ℝ → ℝ → ℝ} (hg : EpsMem α g)
    (h : ∀ z θ, (f z θ) ^ 2 ≤ (g z θ) ^ 2) :
    EpsSq α f ≤ EpsSq α g := by
  have hgp : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (EpsMem_iff_integrable (α := α)).mp hg
  have hslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (g z θ * epsW α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := hgp.prod_right_ae
  have hBg : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine (hgp.integral_prod_left).congr ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    rfl
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2) := by
    filter_upwards [hslice] with z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) hz ?_
    filter_upwards with θ
    have h1 : (f z θ * epsW α z θ) ^ 2 = (f z θ) ^ 2 * (epsW α z θ) ^ 2 := by ring
    have h2 : (g z θ * epsW α z θ) ^ 2 = (g z θ) ^ 2 * (epsW α z θ) ^ 2 := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (h z θ) (sq_nonneg _)
  calc EpsSq α f
      = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2) := rfl
    _ ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hBg hae
    _ = EpsSq α g := rfl

theorem EpsSq_const_mul (α c : ℝ) (f : ℝ → ℝ → ℝ) :
    EpsSq α (fun z θ => c * f z θ) = c ^ 2 * EpsSq α f := by
  rw [EpsSq, EpsSq]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with θ
  ring

theorem EpsSq_add_le_of_mem {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : EpsMem α f) (hg : EpsMem α g) :
    EpsSq α (fun z θ => f z θ + g z θ) ≤ 2 * EpsSq α f + 2 * EpsSq α g := by
  have hfp := (EpsMem_iff_integrable (α := α)).mp hf
  have hgp := (EpsMem_iff_integrable (α := α)).mp hg
  have hslicef := hfp.prod_right_ae
  have hsliceg := hgp.prod_right_ae
  have hBf : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine (hfp.integral_prod_left).congr ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    rfl
  have hBg : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine (hgp.integral_prod_left).congr ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    rfl
  have hsum : MeasureTheory.Integrable
      (fun z => 2 * (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2))
      (volume.restrict Work.Spaces.Iz) :=
    (hBf.const_mul 2).add (hBg.const_mul 2)
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, ((f z θ + g z θ) * epsW α z θ) ^ 2)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2) := by
    filter_upwards [hslicef, hsliceg] with z hzf hzg
    have hmaj : MeasureTheory.Integrable
        (fun θ => 2 * (f z θ * epsW α z θ) ^ 2 + 2 * (g z θ * epsW α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hzf.const_mul 2).add (hzg.const_mul 2)
    have h1 : (∫ θ in Work.Spaces.Iθ, ((f z θ + g z θ) * epsW α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            (2 * (f z θ * epsW α z θ) ^ 2 + 2 * (g z θ * epsW α z θ) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _) hmaj ?_
      filter_upwards with θ
      nlinarith [sq_nonneg (f z θ * epsW α z θ), sq_nonneg (g z θ * epsW α z θ),
        sq_nonneg (f z θ * epsW α z θ + g z θ * epsW α z θ),
        sq_nonneg (f z θ * epsW α z θ - g z θ * epsW α z θ)]
    rw [MeasureTheory.integral_add (hzf.const_mul 2) (hzg.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h1
    exact h1
  calc EpsSq α (fun z θ => f z θ + g z θ)
      = ∫ z in Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, ((f z θ + g z θ) * epsW α z θ) ^ 2) := rfl
    _ ≤ ∫ z in Work.Spaces.Iz,
          (2 * (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
            + 2 * (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2)) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hsum hae
    _ = 2 * EpsSq α f + 2 * EpsSq α g := by
        rw [MeasureTheory.integral_add (hBf.const_mul 2) (hBg.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        rfl

/-! ## The master domination lemma -/

theorem EpsSq_le_of_majorant {α : ℝ} {f Θ : ℝ → ℝ → ℝ}
    (hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Θ z θ) (volume.restrict Work.Spaces.Iθ))
    (hint : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, Θ z θ) (volume.restrict Work.Spaces.Iz))
    (hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), (f z θ * epsW α z θ) ^ 2 ≤ Θ z θ) :
    EpsSq α f ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Θ z θ) := by
  have hpt : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Θ z θ) := by
    filter_upwards [hae, hle] with z hz hlez
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) hz hlez
  calc EpsSq α f
      = ∫ z in Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2) := rfl
    _ ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Θ z θ) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hint hpt

/-! ## The angular profile times a radial function -/

/-- `EpsSq` of `Γ(θ)` times a radial function is the product of the two one-dimensional integrals. -/
theorem EpsSq_gam_mul (α : ℝ) (T : ℝ → ℝ) :
    EpsSq α (fun z θ => Work.Spaces.Gam α θ * T z)
      = (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * (∫ z in Work.Spaces.Iz, (T z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  rw [EpsSq]
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ * T z * epsW α z θ) ^ 2)
        = (T z) ^ 2 * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
    intro θ hθ
    simp only []
    rw [show (Work.Spaces.Gam α θ * T z * epsW α z θ) ^ 2
        = (Work.Spaces.Gam α θ * T z) ^ 2 * (epsW α z θ) ^ 2 from by ring,
      epsW_sq_eq (α := α) (z := z) hθ]
    ring
  simp only [hinner]
  rw [MeasureTheory.integral_mul_const]
  ring

/-! ## Versions restricted to the domain `Iz × Iθ` -/

theorem AK_congr_ae {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : (fun p : ℝ × ℝ => f p.1 p.2)
      =ᵐ[((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => g p.1 p.2)) (hg : AK α g) : AK α f := by
  refine hg.congr ?_
  filter_upwards [h] with p hp
  rw [hp]

theorem AK_of_uncurry {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    AK α f := by
  have he : AEStronglyMeasurable (fun p : ℝ × ℝ => epsW α p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (by simpa only [Work.FTS.StrongEps.Quad] using continuousOn_epsW_quad α)
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2) _ :=
    AEStronglyMeasurable.mul h he
  exact h2

theorem EpsMem_on {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) (hf : EpsMem α f) :
    EpsMem α g := by
  rw [EpsMem] at hf ⊢
  refine hf.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) ?_
  · rintro ⟨z, θ⟩ hh
    simp only [Set.mem_prod] at hh
    simp only []
    rw [h z hh.1 θ hh.2]

theorem EpsSq_on {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) :
    EpsSq α f = EpsSq α g := by
  rw [EpsSq, EpsSq]
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) ?_
  intro z hz
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
  intro θ hθ
  simp only []
  rw [h z hz θ hθ]

theorem EpsSq_le_of_le_on {α : ℝ} {f g : ℝ → ℝ → ℝ} (hg : EpsMem α g)
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, (f z θ) ^ 2 ≤ (g z θ) ^ 2) :
    EpsSq α f ≤ EpsSq α g := by
  have hgp : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (EpsMem_iff_integrable (α := α)).mp hg
  have hslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (g z θ * epsW α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := hgp.prod_right_ae
  have hBg : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine (hgp.integral_prod_left).congr ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    rfl
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2) := by
    filter_upwards [hslice, MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => hz)] with z hz hzmem
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) hz ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hθ)] with θ hθmem
    have h1 : (f z θ * epsW α z θ) ^ 2 = (f z θ) ^ 2 * (epsW α z θ) ^ 2 := by ring
    have h2 : (g z θ * epsW α z θ) ^ 2 = (g z θ) ^ 2 * (epsW α z θ) ^ 2 := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (h z hzmem θ hθmem) (sq_nonneg _)
  calc EpsSq α f
      = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2) := rfl
    _ ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, (g z θ * epsW α z θ) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hBg hae
    _ = EpsSq α g := rfl

theorem EpsSq_neg (α : ℝ) (f : ℝ → ℝ → ℝ) :
    EpsSq α (fun z θ => -f z θ) = EpsSq α f := by
  rw [EpsSq, EpsSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with θ
  ring

theorem EpsSq_sub_le_of_mem {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : EpsMem α f) (hg : EpsMem α g) :
    EpsSq α (fun z θ => f z θ - g z θ) ≤ 2 * EpsSq α f + 2 * EpsSq α g := by
  calc EpsSq α (fun z θ => f z θ - g z θ)
      = EpsSq α (fun z θ => f z θ + -g z θ) :=
        EpsSq_on (fun z _ θ _ => by ring)
    _ ≤ 2 * EpsSq α f + 2 * EpsSq α (fun z θ => -g z θ) :=
        EpsSq_add_le_of_mem hf (EpsMem_neg hg)
    _ = 2 * EpsSq α f + 2 * EpsSq α g := by rw [EpsSq_neg]

theorem EpsSq_congr_integrand {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (f z θ * epsW α z θ) ^ 2 = (g z θ * epsW α z θ) ^ 2) :
    EpsSq α f = EpsSq α g := by
  rw [EpsSq, EpsSq]
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) ?_
  intro z hz
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
  intro θ hθ
  exact h z hz θ hθ

theorem EpsMem_congr_integrand {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (f z θ * epsW α z θ) ^ 2 = (g z θ * epsW α z θ) ^ 2) (hf : EpsMem α f) :
    EpsMem α g := by
  rw [EpsMem] at hf ⊢
  refine hf.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) ?_
  rintro ⟨z, θ⟩ hh
  simp only [Set.mem_prod] at hh
  exact h z hh.1 θ hh.2

end

end Work.FTS.StrongEps.EpsSqTools
