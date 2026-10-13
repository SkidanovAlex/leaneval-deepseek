/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLocalPStar/VolterraAux/Defs.lean`

The measure-theoretic vocabulary of the abstract Volterra/Picard engine
`Work.FTS.StrongEps.EpsLocalPStar.exists_volterra_v3`.

The engine iterates the map `u ↦ h₀ + ∫₀^· F(u s) ds` in the weighted space `X` of
`Submission/Work/FTS/StrongEps/EpsSpace.lean`, whose "norm" is `EpsSq α f = ∫∫ (f·W)²` with
`W = epsW α = w(z)/sin(2θ)^{γ/2}`.  Since `EpsSq` is a *Bochner* integral it is Lean's junk
value `0` on non-integrable data, which makes it unusable for "closure under a.e. limits"
arguments.  We therefore transport the whole bookkeeping to the `ℝ≥0∞`-valued Lebesgue integral

  `epsL2 α f = ∫⁻ p, ofReal ((f p.1 p.2 * epsW α p.1 p.2)²) ∂DomM`,   `DomM = (vol↾Iz).prod (vol↾Iθ)`,

which has no junk values, and keep the passage back and forth (`EpsMem`, `EpsSq`) in a small
conversion kit.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false

/-! ## The domain measure -/

/-- The product measure `dz dθ` on the domain `Iz × Iθ = [0,∞) × [0,π/2]` of the self-similar
variables. -/
def DomM : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The planar Lebesgue measure restricted to `s ×ˢ t` is the product of the two restrictions. -/
theorem prodRestrict_eq2 (s t : Set ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (s ×ˢ t)
      = (MeasureTheory.volume.restrict s).prod (MeasureTheory.volume.restrict t) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]

/-- `DomM` is the planar Lebesgue measure restricted to the closed quadrant. -/
theorem DomM_eq : DomM
    = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  (prodRestrict_eq2 Work.Spaces.Iz Work.Spaces.Iθ).symm

/-- `DomM` is dominated by the planar Lebesgue measure. -/
theorem DomM_le_volume : DomM ≤ (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) := by
  rw [DomM_eq]; exact MeasureTheory.Measure.restrict_le_self

instance : MeasureTheory.SFinite DomM := by
  rw [DomM_eq]; infer_instance

/-! ## The `ℝ≥0∞`-valued weighted size `epsL2` -/

/-- The weighted `L²`-size of a profile, as an `ℝ≥0∞`-valued integral over the domain: the honest
(no junk) form of `EpsSq`. -/
def epsL2 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ,
    ENNReal.ofReal ((f p.1 p.2 * epsW α p.1 p.2) ^ 2) ∂DomM

/-- Almost-everywhere strong measurability of the weighted profile on the domain. -/
def AK2 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : Prop :=
  MeasureTheory.AEStronglyMeasurable
    (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2) DomM

/-! ## `EpsMem` and `epsL2` on the product measure -/

/-- `EpsMem` is integrability of the squared weighted profile for the product measure `DomM`. -/
theorem EpsMem_iff_integrable2 {α : ℝ} {f : Work.FTS.Galerkin.Fn} :
    EpsMem α f ↔ MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM := by
  rw [EpsMem, MeasureTheory.IntegrableOn, DomM_eq]

/-! ## Measurability of the weight and the elementary `AK2` calculus -/

/-- The weight `epsW α` is a measurable function of the two variables. -/
theorem measurable_epsW (α : ℝ) :
    Measurable (fun p : ℝ × ℝ => epsW α p.1 p.2) := by
  simp only [epsW, Work.Spaces.w]
  fun_prop

/-- The constant profile `1` is `AK2` (i.e. `epsW α` is a.e. strongly measurable on `DomM`). -/
theorem AK2_one (α : ℝ) : AK2 α (fun _ _ => (1 : ℝ)) := by
  unfold AK2
  have h : (fun p : ℝ × ℝ => (1 : ℝ) * epsW α p.1 p.2)
      = (fun p : ℝ × ℝ => epsW α p.1 p.2) := by funext p; ring
  rw [h]
  exact (measurable_epsW α).aestronglyMeasurable

/-- `AK2` is preserved by addition. -/
theorem AK2_add {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (hf : AK2 α f) (hg : AK2 α g) :
    AK2 α (fun z θ => f z θ + g z θ) := by
  unfold AK2 at hf hg ⊢
  refine MeasureTheory.AEStronglyMeasurable.congr (hf.add hg) ?_
  filter_upwards with p
  simp only [Pi.add_apply]
  ring

/-- `AK2` is preserved by negation. -/
theorem AK2_neg {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : AK2 α f) :
    AK2 α (fun z θ => -f z θ) := by
  unfold AK2 at hf ⊢
  refine hf.neg.congr ?_
  filter_upwards with p
  simp only [Pi.neg_apply]
  ring

/-- `AK2` only depends on the a.e.-class of the profile. -/
theorem AK2_congr_ae {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (h : ∀ᵐ p ∂DomM, f p.1 p.2 = g p.1 p.2) (hg : AK2 α g) : AK2 α f := by
  unfold AK2 at hg ⊢
  refine MeasureTheory.AEStronglyMeasurable.congr hg ?_
  filter_upwards [h] with p hp
  rw [hp]

/-- `AK2` is preserved by subtraction. -/
theorem AK2_sub {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (hf : AK2 α f) (hg : AK2 α g) :
    AK2 α (fun z θ => f z θ - g z θ) :=
  AK2_congr_ae (by filter_upwards with p; ring) (AK2_add hf (AK2_neg hg))

/-- `AK2` is preserved by multiplication by a constant. -/
theorem AK2_const_mul {α : ℝ} {f : Work.FTS.Galerkin.Fn} (c : ℝ) (hf : AK2 α f) :
    AK2 α (fun z θ => c * f z θ) := by
  unfold AK2 at hf ⊢
  refine MeasureTheory.AEStronglyMeasurable.congr (hf.const_mul c) ?_
  filter_upwards with p
  ring

/-- A measurable function of the domain is `AK2`. -/
theorem AK2_of_measurable {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (h : Measurable (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2)) : AK2 α f :=
  h.aestronglyMeasurable

/-! ## A.e.-congruence of the sizes -/

/-- `epsL2` only depends on the a.e.-class of the profile. -/
theorem epsL2_congr_ae {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (h : ∀ᵐ p ∂DomM, f p.1 p.2 = g p.1 p.2) : epsL2 α f = epsL2 α g := by
  have h' : (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((f p.1 p.2 * epsW α p.1 p.2) ^ 2))
      =ᵐ[DomM] (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((g p.1 p.2 * epsW α p.1 p.2) ^ 2)) := by
    filter_upwards [h] with p hp
    rw [hp]
  unfold epsL2
  exact MeasureTheory.lintegral_congr_ae h'
/-- `EpsMem` only depends on the a.e.-class of the profile. -/
theorem EpsMem_congr_ae {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (h : ∀ᵐ p ∂DomM, f p.1 p.2 = g p.1 p.2) (hf : EpsMem α f) : EpsMem α g := by
  rw [EpsMem_iff_integrable2] at hf ⊢
  refine hf.congr ?_
  filter_upwards [h] with p hp
  rw [hp]

/-- `EpsSq` only depends on the a.e.-class of the profile. -/
theorem EpsSq_congr_ae {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (h : ∀ᵐ p ∂DomM, f p.1 p.2 = g p.1 p.2) : EpsSq α f = EpsSq α g := by
  have h' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), f z θ = g z θ :=
    Measure.ae_ae_of_ae_prod h
  rw [EpsSq, EpsSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h'] with z hz
  exact MeasureTheory.integral_congr_ae (hz.mono fun θ hθ => by simp only [hθ])

/-! ## The a.e. open quadrant -/

/-- Almost every point of the domain lies in the open quadrant. -/
theorem ae_open_DomM :
    ∀ᵐ p ∂DomM, 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 := by
  have hz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have h : Work.Spaces.Iz = Set.Ici (0 : ℝ) := rfl
    rw [h, ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hz)
  have hθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 < θ ∧ θ < Real.pi / 2 := by
    have h : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    rw [h, ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0)
        (b := Real.pi / 2))]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ⟨hz.1, hz.2⟩)
  rw [DomM]
  rw [Measure.ae_prod_iff_ae_ae
    (p := fun p : ℝ × ℝ => 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2)
    ((measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)))]
  filter_upwards [hz] with z hz'
  filter_upwards [hθ] with θ hθ'
  exact ⟨hz', hθ'.1, hθ'.2⟩

/-- A property which holds everywhere on the open quadrant holds almost everywhere on the
domain. -/
theorem ae_of_forall_open {Q : ℝ → ℝ → Prop}
    (h : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → Q z θ) :
    ∀ᵐ p ∂DomM, Q p.1 p.2 := by
  filter_upwards [ae_open_DomM] with p hp
  exact h p.1 hp.1 p.2 hp.2.1 hp.2.2

/-! ## The conversion kit between `epsL2` and `EpsSq`/`EpsMem` -/

/-- The squared weighted profile of a profile is integrable for `DomM` as soon as its `epsL2`
is finite and the weighted profile is a.e. strongly measurable. -/
theorem EpsMem_of_epsL2_lt_top {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hAK : AK2 α f)
    (h : epsL2 α f < ⊤) : EpsMem α f := by
  rw [EpsMem_iff_integrable2]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM := hAK.pow 2
  refine ⟨haesm, ?_⟩
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun p => sq_nonneg _)).mpr h

/-- `epsL2` is finite for a member of the weighted space. -/
theorem epsL2_lt_top_of_EpsMem {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f) :
    epsL2 α f < ⊤ := by
  have hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM :=
    EpsMem_iff_integrable2.mp hf
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun p => sq_nonneg _)).mp hg.hasFiniteIntegral

/-- For a member of the weighted space, `epsL2` is the (real) `EpsSq`. -/
theorem epsL2_eq_ofReal_EpsSq {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f) :
    epsL2 α f = ENNReal.ofReal (EpsSq α f) := by
  have hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM :=
    EpsMem_iff_integrable2.mp hf
  have hprod : (∫ p : ℝ × ℝ, (f p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂DomM) = EpsSq α f := by
    rw [EpsSq, DomM]
    exact MeasureTheory.integral_prod _ hg
  have h1 : (∫ p : ℝ × ℝ, (f p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂DomM)
      = (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal ((f p.1 p.2 * epsW α p.1 p.2) ^ 2) ∂DomM).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => sq_nonneg _) hg.aestronglyMeasurable
  have hfin : (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal ((f p.1 p.2 * epsW α p.1 p.2) ^ 2) ∂DomM) ≠ ⊤ :=
    (epsL2_lt_top_of_EpsMem hf).ne
  unfold epsL2
  rw [← hprod, h1, ENNReal.ofReal_toReal hfin]

/-- The `epsL2`-bound of a member of the weighted space. -/
theorem epsL2_le_ofReal_of_mem {α B : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f)
    (h : EpsSq α f ≤ B) : epsL2 α f ≤ ENNReal.ofReal B := by
  rw [epsL2_eq_ofReal_EpsSq hf]
  exact ENNReal.ofReal_le_ofReal h

/-- The passage back: a finite `epsL2`-bound (on an a.e. measurable profile) gives membership and
the `EpsSq`-bound. -/
theorem EpsMem_and_EpsSq_le_of_epsL2_le {α B : ℝ} (hB : 0 ≤ B)
    {f : Work.FTS.Galerkin.Fn} (hAK : AK2 α f) (h : epsL2 α f ≤ ENNReal.ofReal B) :
    EpsMem α f ∧ EpsSq α f ≤ B := by
  have hfin : epsL2 α f < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hmem := EpsMem_of_epsL2_lt_top hAK hfin
  refine ⟨hmem, ?_⟩
  rw [epsL2_eq_ofReal_EpsSq hmem] at h
  rwa [ENNReal.ofReal_le_ofReal_iff hB] at h

/-- Membership gives a finite `epsL2`-bound when the `EpsSq`-bound is finite. -/
theorem epsL2_le_ofReal_of_mem_of_le {α B : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f)
    (h : EpsSq α f ≤ B) : epsL2 α f ≤ ENNReal.ofReal B :=
  epsL2_le_ofReal_of_mem hf h

/-- A finite `epsL2`-bound of a *member* of the weighted space gives the `EpsSq`-bound. -/
theorem EpsSq_le_of_epsL2_le_of_mem {α B : ℝ} (hB : 0 ≤ B) {f : Work.FTS.Galerkin.Fn}
    (hf : EpsMem α f) (h : epsL2 α f ≤ ENNReal.ofReal B) : EpsSq α f ≤ B := by
  rw [epsL2_eq_ofReal_EpsSq hf] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h

/-! ## Elementary calculus of the two sizes -/

/-- The zero profile is a member of the weighted space. -/
theorem EpsMem_zero2 (α : ℝ) : EpsMem α (fun _ _ => (0 : ℝ)) := by
  rw [EpsMem_iff_integrable2]
  simp

/-- Negation preserves membership. -/
theorem EpsMem_neg2 {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f) :
    EpsMem α (fun z θ => -f z θ) := by
  rw [EpsMem_iff_integrable2] at hf ⊢
  refine hf.congr ?_
  filter_upwards with p
  ring

/-- `EpsSq` is invariant under negation. -/
theorem EpsSq_neg2 {α : ℝ} {f : Work.FTS.Galerkin.Fn} :
    EpsSq α (fun z θ => -f z θ) = EpsSq α f := by
  rw [EpsSq, EpsSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with θ
  ring

/-- `EpsSq` is invariant under swapping a difference. -/
theorem EpsSq_sub_comm {α : ℝ} {f g : Work.FTS.Galerkin.Fn} :
    EpsSq α (fun z θ => f z θ - g z θ) = EpsSq α (fun z θ => g z θ - f z θ) := by
  rw [EpsSq, EpsSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with θ
  ring

/-- Membership of a difference from membership (and a.e. strong measurability) of the two parts. -/
theorem EpsMem_sub2 {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (hakf : AK2 α f) (hakg : AK2 α g)
    (hf : EpsMem α f) (hg : EpsMem α g) : EpsMem α (fun z θ => f z θ - g z θ) := by
  have hf' := EpsMem_iff_integrable2.mp hf
  have hg' := EpsMem_iff_integrable2.mp hg
  rw [EpsMem_iff_integrable2]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ((f p.1 p.2 - g p.1 p.2) * epsW α p.1 p.2) ^ 2) DomM :=
    (AK2_sub hakf hakg).pow 2
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => 2 * (f p.1 p.2 * epsW α p.1 p.2) ^ 2
        + 2 * (g p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM :=
    (hf'.const_mul 2).add (hg'.const_mul 2)
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 : ((f p.1 p.2 - g p.1 p.2) * epsW α p.1 p.2) ^ 2
      = (f p.1 p.2 * epsW α p.1 p.2 - g p.1 p.2 * epsW α p.1 p.2) ^ 2 := by ring
  rw [h1]
  nlinarith [sq_nonneg (f p.1 p.2 * epsW α p.1 p.2),
    sq_nonneg (g p.1 p.2 * epsW α p.1 p.2),
    sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 - g p.1 p.2 * epsW α p.1 p.2),
    sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 + g p.1 p.2 * epsW α p.1 p.2)]

/-! ## Joint measurability of a family and its sections -/

/-- A.e. sections of a jointly a.e.-strongly-measurable family of profiles are `AK2`. -/
theorem AK2_sections {α : ℝ} {Φ : ℝ → Work.FTS.Galerkin.Fn}
    (h : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2) MeasureTheory.volume) :
    ∀ᵐ s ∂(MeasureTheory.volume : Measure ℝ), AK2 α (Φ s) := by
  have h2 : ∀ᵐ s ∂(MeasureTheory.volume : Measure ℝ),
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Φ s p.1 p.2) (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    h.prodMk_left (ν := (MeasureTheory.volume : Measure (ℝ × ℝ)))
  filter_upwards [h2] with s hs
  unfold AK2
  have hs' : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Φ s p.1 p.2) DomM := hs.mono_measure DomM_le_volume
  refine (hs'.mul (measurable_epsW α).aestronglyMeasurable).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]

/-- The weighted version of a jointly a.e.-strongly-measurable family, for the product of the
fake-time measure on `[0,τ]` with `DomM`. -/
theorem aesm_weighted_prod {α : ℝ} {Φ : ℝ → Work.FTS.Galerkin.Fn}
    (h : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2) MeasureTheory.volume) (τ : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM) := by
  have hle : (MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM
      ≤ (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ × ℝ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self DomM_le_volume
  have h1 := h.mono_measure hle
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM) :=
    ((measurable_epsW α).comp measurable_snd).aestronglyMeasurable
  exact (h1.mul h2).congr (by filter_upwards with p; simp only [Pi.mul_apply])

/-- Joint measurability of the weighted fake-time integral of a family. -/
theorem AK2_intervalIntegral {α : ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM)) :
    AK2 α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) := by
  rw [Set.uIoc_of_le hτ] at hmeas
  unfold AK2
  simp only [intervalIntegral.integral_of_le hτ]
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ × ℝ => ∫ y : ℝ, G y x.1 x.2 * epsW α x.1 x.2
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 τ))) DomM :=
    hmeas.prod_swap.integral_prod_right'
  refine h2.congr ?_
  filter_upwards with p
  rw [MeasureTheory.integral_mul_const]

end Work.FTS.StrongEps.EpsLocalPStar
