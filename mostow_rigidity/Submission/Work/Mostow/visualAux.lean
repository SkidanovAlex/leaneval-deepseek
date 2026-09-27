import Mathlib
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.coneImage
import Submission.Work.Mostow.visualBasic
import Submission.Work.Mostow.poTransitive
import Submission.Work.Mostow.o1SignTime
import Submission.Work.Mostow.homoExtJac
import Submission.Work.Mostow.homoExt_diff
import Submission.Work.Mostow.homoExtGeom

/-!
# Auxiliary lemmas for the area T3 development (`Work.Mostow.visualMeasure`)

Bijectivity of the boundary action on the sphere, a.e. composition rules, and the
change-of-variables identity for `sphMeas` under `bd g`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise Topology
open Filter

noncomputable section

variable {n : ℕ}

/-- The unit sphere is Borel. -/
theorem measurableSet_Sph (n : ℕ) : MeasurableSet (Sph n) := Metric.isClosed_sphere.measurableSet

theorem bd_sph (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g ξ ∈ Sph n := by
  obtain ⟨-, -, -, -, -, -, -, h, -, -, -, -⟩ := hA
  exact h g ξ hξ

theorem bd_one' (hA : POActionProp n) {ξ : E n} (hξ : ξ ∈ Sph n) : bd (1 : PO n 1) ξ = ξ := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -, -, -⟩ := hA
  exact h ξ hξ

theorem bd_mul' (hA : POActionProp n) (g h : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd (g * h) ξ = bd g (bd h ξ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hm, -, -⟩ := hA
  exact hm g h ξ hξ

theorem bd_cont (hA : POActionProp n) (g : PO n 1) : ContinuousOn (bd g) (Sph n) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := hA
  exact h g

theorem hmul_law (hA : POActionProp n) (g h : PO n 1) (u : E n) :
    (g * h) • u = g • (h • u) := by
  obtain ⟨-, -, -, -, hlaw, -, -, -, -, -, -, -⟩ := hA
  exact hlaw g h u

theorem bd_measurable (hA : POActionProp n) (g : PO n 1) : Measurable (bd g) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := hA
  exact h g

/-- `bd g⁻¹` is a left inverse of `bd g` on the sphere. -/
theorem bd_left (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g⁻¹ (bd g ξ) = ξ := by
  have h1 := bd_mul' hA g⁻¹ g hξ
  rw [inv_mul_cancel, bd_one' hA hξ] at h1
  exact h1.symm

/-- `bd g⁻¹` is a right inverse of `bd g` on the sphere. -/
theorem bd_right (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g (bd g⁻¹ ξ) = ξ := by
  have h1 := bd_mul' hA g g⁻¹ hξ
  rw [mul_inv_cancel, bd_one' hA hξ] at h1
  exact h1.symm

theorem bd_injOnv (hA : POActionProp n) (g : PO n 1) : Set.InjOn (bd g) (Sph n) := by
  intro a ha b hb hab
  have h1 := bd_left hA g ha
  have h2 := bd_left hA g hb
  rw [hab] at h1
  rw [h2] at h1
  exact h1.symm

theorem bd_image_sph (hA : POActionProp n) (g : PO n 1) : bd g '' Sph n = Sph n := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact bd_sph hA g hx
  · intro y hy
    exact ⟨bd g⁻¹ y, bd_sph hA g⁻¹ hy, bd_right hA g hy⟩

/-- Preimage of a set under `bd g`, intersected with the sphere, is the image of the
intersected preimage under `bd g⁻¹`. -/
theorem bd_preimage_eq (hA : POActionProp n) (g : PO n 1) (T : Set (E n)) :
    (bd g ⁻¹' T) ∩ Sph n = bd g⁻¹ '' (T ∩ Sph n) := by
  ext ξ
  constructor
  · rintro ⟨hξT, hξ⟩
    refine ⟨bd g ξ, ⟨hξT, bd_sph hA g hξ⟩, ?_⟩
    exact bd_left hA g hξ
  · rintro ⟨η, ⟨hηT, hη⟩, rfl⟩
    refine ⟨?_, bd_sph hA g⁻¹ hη⟩
    show bd g (bd g⁻¹ η) ∈ T
    rw [bd_right hA g hη]
    exact hηT

/-- Conversely, `bd g '' ((bd g ⁻¹' T) ∩ Sph) = T ∩ Sph`. -/
theorem bd_image_preimage (hA : POActionProp n) (g : PO n 1) (T : Set (E n)) :
    bd g '' ((bd g ⁻¹' T) ∩ Sph n) = T ∩ Sph n := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, ⟨hxT, hx⟩, rfl⟩
    exact ⟨hxT, bd_sph hA g hx⟩
  · rintro y ⟨hyT, hy⟩
    refine ⟨bd g⁻¹ y, ⟨?_, bd_sph hA g⁻¹ hy⟩, bd_right hA g hy⟩
    show bd g (bd g⁻¹ y) ∈ T
    rw [bd_right hA g hy]
    exact hyT

/-- The image of a measurable subset of the sphere under `bd g` is measurable. -/
theorem bd_image_measurable (hA : POActionProp n) (g : PO n 1) {B : Set (E n)}
    (hB : MeasurableSet B) (hBs : B ⊆ Sph n) : MeasurableSet (bd g '' B) := by
  have heq : bd g '' B = (bd g⁻¹ ⁻¹' B) ∩ Sph n := by
    ext y
    constructor
    · rintro ⟨x, hxB, rfl⟩
      refine ⟨?_, bd_sph hA g (hBs hxB)⟩
      show bd g⁻¹ (bd g x) ∈ B
      rw [bd_left hA g (hBs hxB)]
      exact hxB
    · rintro ⟨hy, hys⟩
      exact ⟨bd g⁻¹ y, hy, bd_right hA g hys⟩
  rw [heq]
  exact ((bd_measurable hA g⁻¹) hB).inter (measurableSet_Sph n)

/-- The cone over a measurable subset of the sphere is measurable. -/
theorem cone_measurable {B : Set (E n)} (hB : MeasurableSet B) (hBs : B ⊆ Sph n) :
    MeasurableSet (cone B) := by
  have heq : cone B = ((fun x : E n => ‖x‖) ⁻¹' Set.Ioo (0 : ℝ) 1) ∩
      ((fun x : E n => ‖x‖⁻¹ • x) ⁻¹' B) := by
    ext x
    constructor
    · intro hx
      rw [cone, Set.mem_smul] at hx
      obtain ⟨r, hr, b, hb, rfl⟩ := hx
      refine ⟨?_, ?_⟩
      · show ‖r • b‖ ∈ Set.Ioo (0 : ℝ) 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, (mem_Sph_iff b).1 (hBs hb), mul_one]
        exact hr
      · show ‖r • b‖⁻¹ • (r • b) ∈ B
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, (mem_Sph_iff b).1 (hBs hb), mul_one]
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hr.1), one_smul]
        exact hb
    · rintro ⟨h1, h2⟩
      rw [cone, Set.mem_smul]
      exact ⟨‖x‖, h1, ‖x‖⁻¹ • x, h2,
        by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h1.1), one_smul]⟩
  rw [heq]
  exact (measurable_norm measurableSet_Ioo).inter
    (hB.preimage (Measurable.smul measurable_norm.inv measurable_id))

/-- Points of `cone B` (`B ⊆ Sph n`) have norm in `(0,1)`. -/
theorem cone_norm_mem {B : Set (E n)} (hBs : B ⊆ Sph n) :
    cone B ⊆ {x : E n | ‖x‖ ∈ Set.Ioo (0:ℝ) 1} := by
  intro x hx
  rw [cone, Set.mem_smul] at hx
  obtain ⟨r, hr, b, hb, rfl⟩ := hx
  show ‖r • b‖ ∈ Set.Ioo (0 : ℝ) 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, (mem_Sph_iff b).1 (hBs hb), mul_one]
  exact hr

theorem cone_ne_zero {B : Set (E n)} (hBs : B ⊆ Sph n) : cone B ⊆ {x : E n | x ≠ 0} := by
  intro x hx hx0
  have h := cone_norm_mem hBs hx
  rw [hx0] at h
  have h1 : (0 : ℝ) < ‖(0 : E n)‖ := h.1
  rw [norm_zero] at h1
  exact lt_irrefl (0 : ℝ) h1

/-- Membership in the cone, for `B ⊆ Sph n`. -/
theorem cone_eq {B : Set (E n)} (hBs : B ⊆ Sph n) :
    cone B = ((fun x : E n => ‖x‖) ⁻¹' Set.Ioo (0 : ℝ) 1) ∩
      ((fun x : E n => ‖x‖⁻¹ • x) ⁻¹' B) := by
  ext x
  constructor
  · intro hx
    rw [cone, Set.mem_smul] at hx
    obtain ⟨r, hr, b, hb, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · show ‖r • b‖ ∈ Set.Ioo (0 : ℝ) 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, (mem_Sph_iff b).1 (hBs hb), mul_one]
      exact hr
    · show ‖r • b‖⁻¹ • (r • b) ∈ B
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, (mem_Sph_iff b).1 (hBs hb), mul_one]
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hr.1), one_smul]
      exact hb
  · rintro ⟨h1, h2⟩
    rw [cone, Set.mem_smul]
    exact ⟨‖x‖, h1, ‖x‖⁻¹ • x, h2,
      by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h1.1), one_smul]⟩

/-- `dfun g` is a measurable function of its second argument. -/
theorem measurable_dfun (g : PO n 1) : Measurable (fun ξ : E n => dfun g ξ) := by
  have hlin : (fun ξ : E n => dfun g ξ)
      = fun ξ => (∑ i : Fin n, (sMat g) (Sum.inr 0) (Sum.inl i) * ξ i)
          + (sMat g) (Sum.inr 0) (Sum.inr 0) := by
    funext ξ
    simp only [dfun, wvec_visualDefs, hvec]
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_one]
    simp
  rw [hlin]
  fun_prop

/-- **Polar coordinates for the surface measure** (measurable integrands). -/
theorem spherePolarv (n : ℕ) (hn : 1 ≤ n) (B : Set (E n)) (hB : MeasurableSet B)
    (hBs : B ⊆ Sph n) (F : E n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x in cone B, F (‖x‖⁻¹ • x) ∂(volume : Measure (E n))
      = (n : ENNReal)⁻¹ * ∫⁻ ξ, F ξ ∂((sphMeas n).restrict B) := by
  let K : Set (E n) := {0}
  have hK : MeasurableSet K := measurableSet_singleton 0
  have hfin : Module.finrank ℝ (E n) = n := finrank_euclideanSpace_fin
  have hcone_meas : MeasurableSet (cone B) := cone_measurable hB hBs
  have hcone_sub : cone B ⊆ Kᶜ := cone_ne_zero hBs
  have hpre_meas : MeasurableSet ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)) :=
    hcone_meas.preimage continuous_subtype_val.measurable
  -- (a) transfer the integral to the punctured space
  have stepA : ∫⁻ x in cone B, F (‖x‖⁻¹ • x) ∂(volume : Measure (E n))
      = ∫⁻ a : ↥(Kᶜ),
          ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
            (fun a => F (‖(a : E n)‖⁻¹ • (a : E n))) a
          ∂((volume : Measure (E n)).comap Subtype.val) := by
    have h1 : ∫⁻ x in cone B, F (‖x‖⁻¹ • x) ∂(volume : Measure (E n))
        = ∫⁻ x, (cone B).indicator (fun y => F (‖y‖⁻¹ • y)) x ∂(volume : Measure (E n)) :=
      (lintegral_indicator hcone_meas _).symm
    have h2 : ∫⁻ x, (cone B).indicator (fun y => F (‖y‖⁻¹ • y)) x ∂(volume : Measure (E n))
        = ∫⁻ x in Kᶜ, (cone B).indicator (fun y => F (‖y‖⁻¹ • y)) x
            ∂(volume : Measure (E n)) := by
      rw [← lintegral_indicator hK.compl]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ cone B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hcone_sub hx), Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        by_cases hx' : x ∈ Kᶜ
        · rw [Set.indicator_of_mem hx', Set.indicator_of_notMem hx]
        · rw [Set.indicator_of_notMem hx']
    have h3 : ∫⁻ x in Kᶜ, (cone B).indicator (fun y => F (‖y‖⁻¹ • y)) x
            ∂(volume : Measure (E n))
        = ∫⁻ a : ↥(Kᶜ), (cone B).indicator (fun y => F (‖y‖⁻¹ • y)) (a : E n)
            ∂((volume : Measure (E n)).comap Subtype.val) :=
      (lintegral_subtype_comap hK.compl _).symm
    have h4 : ∫⁻ a : ↥(Kᶜ), (cone B).indicator (fun y => F (‖y‖⁻¹ • y)) (a : E n)
            ∂((volume : Measure (E n)).comap Subtype.val)
        = ∫⁻ a : ↥(Kᶜ),
            ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
              (fun a => F (‖(a : E n)‖⁻¹ • (a : E n))) a
            ∂((volume : Measure (E n)).comap Subtype.val) := by
      apply lintegral_congr
      intro a
      by_cases ha : (a : E n) ∈ cone B <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_preimage, ha]
    exact h1.trans (h2.trans (h3.trans h4))
  -- (b) transport along the polar homeomorphism
  have stepB : ∫⁻ a : ↥(Kᶜ),
          ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
            (fun a => F (‖(a : E n)‖⁻¹ • (a : E n))) a
          ∂((volume : Measure (E n)).comap Subtype.val)
      = ∫⁻ p : ↥(Metric.sphere (0 : E n) 1) × ↥(Set.Ioi (0 : ℝ)),
          ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
            (fun a => F (‖(a : E n)‖⁻¹ • (a : E n)))
            ((homeomorphUnitSphereProd (E n)).symm p)
          ∂(((volume : Measure (E n)).toSphere).prod
              (Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) := by
    have hcomp := MeasurePreserving.lintegral_comp_emb
      (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (E n)))
      (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (E n)))
      (fun p : ↥(Metric.sphere (0 : E n) 1) × ↥(Set.Ioi (0 : ℝ)) =>
        ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
          (fun a => F (‖(a : E n)‖⁻¹ • (a : E n)))
          ((homeomorphUnitSphereProd (E n)).symm p))
    simpa [Homeomorph.symm_apply_apply] using hcomp
  -- (c) evaluate the transported integrand
  have stepC : ∫⁻ p : ↥(Metric.sphere (0 : E n) 1) × ↥(Set.Ioi (0 : ℝ)),
          ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
            (fun a => F (‖(a : E n)‖⁻¹ • (a : E n)))
            ((homeomorphUnitSphereProd (E n)).symm p)
          ∂(((volume : Measure (E n)).toSphere).prod
              (Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1)))
      = ∫⁻ p : ↥(Metric.sphere (0 : E n) 1) × ↥(Set.Ioi (0 : ℝ)),
          ((fun ξ : ↥(Metric.sphere (0 : E n) 1) => (B.indicator F) (ξ : E n)) p.1) *
            ((Set.Iio (⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ)))).indicator
              (fun _ => (1 : ℝ≥0∞)) p.2)
          ∂(((volume : Measure (E n)).toSphere).prod
              (Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) := by
    classical
    congr 1
    funext p
    obtain ⟨ξ, r⟩ := p
    have hr : (0 : ℝ) < (r : ℝ) := r.2
    have hξn : ‖(ξ : E n)‖ = 1 := (mem_Sph_iff (ξ : E n)).1 ξ.2
    have hnorm : ‖(r : ℝ) • (ξ : E n)‖ = (r : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hξn, mul_one]
    have hmem : ((r : ℝ) • (ξ : E n)) ∈ cone B ↔ ((ξ : E n) ∈ B ∧ (r : ℝ) < 1) := by
      rw [cone_eq hBs]
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        rw [hnorm] at h1 h2
        refine ⟨?_, h1.2⟩
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul] at h2
        exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [hnorm]; exact ⟨hr, h2⟩
        · rw [hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]; exact h1
    have hval : F (‖((r : ℝ) • (ξ : E n))‖⁻¹ • ((r : ℝ) • (ξ : E n))) = F (ξ : E n) := by
      rw [hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
    have hcoe : (((homeomorphUnitSphereProd (E n)).symm (ξ, r) : ↥(Kᶜ)) : E n)
        = (r : ℝ) • (ξ : E n) := homeomorphUnitSphereProd_symm_apply_coe (E n) (ξ, r)
    have hcoe_lt : ∀ r : ↥(Set.Ioi (0 : ℝ)),
        (r < (⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ)))) ↔ ((r : ℝ) < 1) := by
      intro r
      rw [← Subtype.coe_lt_coe]
    simp only [Set.indicator_apply]
    rw [Set.mem_preimage, hcoe, hmem, hval]
    by_cases h1 : (ξ : E n) ∈ B <;> by_cases h2 : (r : ℝ) < 1 <;>
      simp [h1, h2, Set.mem_Iio, hcoe_lt]
  -- (d) Fubini
  have stepD : ∫⁻ p : ↥(Metric.sphere (0 : E n) 1) × ↥(Set.Ioi (0 : ℝ)),
          ((fun ξ : ↥(Metric.sphere (0 : E n) 1) => (B.indicator F) (ξ : E n)) p.1) *
            ((Set.Iio (⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ)))).indicator
              (fun _ => (1 : ℝ≥0∞)) p.2)
          ∂(((volume : Measure (E n)).toSphere).prod
              (Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1)))
      = (∫⁻ ξ : ↥(Metric.sphere (0 : E n) 1), (B.indicator F) (ξ : E n)
            ∂((volume : Measure (E n)).toSphere)) *
          (∫⁻ r : ↥(Set.Ioi (0 : ℝ)),
            (Set.Iio (⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) r
            ∂(Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) :=
    lintegral_prod_mul
      (((hF.indicator hB).comp continuous_subtype_val.measurable).aemeasurable)
      ((measurable_const.indicator measurableSet_Iio).aemeasurable)
  -- (e1) the radial factor
  have hnu : (∫⁻ r : ↥(Set.Ioi (0 : ℝ)),
          (Set.Iio (⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) r
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) = (n : ENNReal)⁻¹ := by
    rw [lintegral_indicator measurableSet_Iio, setLIntegral_one, hfin,
      Measure.volumeIoiPow_apply_Iio, Nat.sub_add_cancel hn]
    have h1 : ((⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ))) : ℝ) = 1 := rfl
    rw [h1, one_pow, one_div]
    have h2 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by rw [Nat.cast_sub hn]; norm_num
    rw [h2, ENNReal.ofReal_inv_of_pos (by exact_mod_cast (by omega : 0 < n)),
      ENNReal.ofReal_natCast]
  -- (e2) the angular factor
  have hT : (∫⁻ ξ : ↥(Metric.sphere (0 : E n) 1), (B.indicator F) (ξ : E n)
        ∂((volume : Measure (E n)).toSphere))
      = ∫⁻ η, F η ∂((sphMeas n).restrict B) := by
    rw [← MeasurableEmbedding.lintegral_map
      (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet) (B.indicator F)]
    show ∫⁻ b, (B.indicator F) b ∂(sphMeas n) = ∫⁻ η, F η ∂((sphMeas n).restrict B)
    rw [lintegral_indicator hB]
  calc ∫⁻ x in cone B, F (‖x‖⁻¹ • x) ∂(volume : Measure (E n))
      = ∫⁻ a : ↥(Kᶜ),
          ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
            (fun a => F (‖(a : E n)‖⁻¹ • (a : E n))) a
          ∂((volume : Measure (E n)).comap Subtype.val) := stepA
    _ = ∫⁻ p : ↥(Metric.sphere (0 : E n) 1) × ↥(Set.Ioi (0 : ℝ)),
          ((Subtype.val : ↥(Kᶜ) → E n) ⁻¹' (cone B)).indicator
            (fun a => F (‖(a : E n)‖⁻¹ • (a : E n)))
            ((homeomorphUnitSphereProd (E n)).symm p)
          ∂(((volume : Measure (E n)).toSphere).prod
              (Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) := stepB
    _ = ∫⁻ p : ↥(Metric.sphere (0 : E n) 1) × ↥(Set.Ioi (0 : ℝ)),
          ((fun ξ : ↥(Metric.sphere (0 : E n) 1) => (B.indicator F) (ξ : E n)) p.1) *
            ((Set.Iio (⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ)))).indicator
              (fun _ => (1 : ℝ≥0∞)) p.2)
          ∂(((volume : Measure (E n)).toSphere).prod
              (Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) := stepC
    _ = (∫⁻ ξ : ↥(Metric.sphere (0 : E n) 1), (B.indicator F) (ξ : E n)
            ∂((volume : Measure (E n)).toSphere)) *
          (∫⁻ r : ↥(Set.Ioi (0 : ℝ)),
            (Set.Iio (⟨1, Set.mem_Ioi.2 one_pos⟩ : ↥(Set.Ioi (0 : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) r
            ∂(Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) := stepD
    _ = (∫⁻ η, F η ∂((sphMeas n).restrict B)) * (n : ENNReal)⁻¹ := by rw [hT, hnu]
    _ = (n : ENNReal)⁻¹ * ∫⁻ ξ, F ξ ∂((sphMeas n).restrict B) := by rw [mul_comm]

/-- **Change of variables for the surface measure under the boundary action** (core form,
with the geometric inputs as hypotheses so that the dependency on the WIP sibling files is
explicit). -/
theorem sphChangeOfVars_core (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (g : PO n 1)
    (B : Set (E n)) (hB : MeasurableSet B) (hBs : B ⊆ Sph n) (F : E n → ℝ≥0∞)
    (hF : Measurable F)
    (hjac : ∀ x : E n, x ≠ 0 →
      |(fderiv ℝ (homoExt g) x).det| = (dfun g (‖x‖⁻¹ • x)) ^ (-(n : ℝ) + 1))
    (hdiff : ∀ x : E n, x ≠ 0 → DifferentiableAt ℝ (homoExt g) x)
    (hnorm : ∀ x : E n, x ≠ 0 → ‖homoExt g x‖ = ‖x‖)
    (hdir : ∀ x : E n, x ≠ 0 → ‖x‖⁻¹ • homoExt g x = bd g (‖x‖⁻¹ • x))
    (hinj : Set.InjOn (homoExt g) {x : E n | x ≠ 0})
    (hpol : ∀ (B' : Set (E n)), MeasurableSet B' → B' ⊆ Sph n → ∀ (G : E n → ℝ≥0∞),
        Measurable G →
        ∫⁻ x in cone B', G (‖x‖⁻¹ • x) ∂(volume : Measure (E n))
          = (n : ENNReal)⁻¹ * ∫⁻ ξ, G ξ ∂((sphMeas n).restrict B')) :
    ∫⁻ ξ in B, F (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)) ∂(sphMeas n)
      = ∫⁻ η in bd g '' B, F η ∂(sphMeas n) := by
  let G : E n → ℝ≥0∞ := fun ξ => F (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1))
  have hG : Measurable G := by
    show Measurable (fun ξ : E n => F (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)))
    exact (hF.comp (bd_measurable hA g)).mul
      (((measurable_dfun g).pow_const _).ennreal_ofReal)
  have himg : MeasurableSet (bd g '' B) := bd_image_measurable hA g hB hBs
  have himg_sub : bd g '' B ⊆ Sph n := by
    rintro y ⟨x, hx, rfl⟩
    exact bd_sph hA g (hBs hx)
  have hcone : MeasurableSet (cone B) := cone_measurable hB hBs
  have hcone_sub : cone B ⊆ {x : E n | x ≠ 0} := cone_ne_zero hBs
  have hn0 : (n : ENNReal) ≠ 0 := by simp only [Nat.cast_ne_zero]; omega
  have hntop : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have step1 : ∫⁻ ξ in B, F (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)) ∂(sphMeas n)
      = (n : ENNReal) • ∫⁻ x in cone B, G (‖x‖⁻¹ • x) ∂(volume : Measure (E n)) := by
    have h := hpol B hB hBs G hG
    have hL : ∫⁻ ξ in B, F (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)) ∂(sphMeas n)
        = ∫⁻ ξ, G ξ ∂((sphMeas n).restrict B) := rfl
    rw [hL, h, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hn0 hntop, one_mul]
  have step2 : ∫⁻ x in cone B, G (‖x‖⁻¹ • x) ∂(volume : Measure (E n))
      = ∫⁻ x in cone B, ENNReal.ofReal |(fderiv ℝ (homoExt g) x).det| *
          F (‖homoExt g x‖⁻¹ • homoExt g x) ∂(volume : Measure (E n)) := by
    refine setLIntegral_congr_fun hcone fun x hx => ?_
    have hx0 : x ≠ 0 := hcone_sub hx
    have h1 : ENNReal.ofReal |(fderiv ℝ (homoExt g) x).det|
        = ENNReal.ofReal ((dfun g (‖x‖⁻¹ • x)) ^ (-(n : ℝ) + 1)) := by rw [hjac x hx0]
    have h2 : ‖homoExt g x‖⁻¹ • homoExt g x = bd g (‖x‖⁻¹ • x) := by
      rw [hnorm x hx0, hdir x hx0]
    show F (bd g (‖x‖⁻¹ • x)) * ENNReal.ofReal ((dfun g (‖x‖⁻¹ • x)) ^ (-(n : ℝ) + 1))
      = ENNReal.ofReal |(fderiv ℝ (homoExt g) x).det| * F (‖homoExt g x‖⁻¹ • homoExt g x)
    rw [h1, h2, mul_comm]
  have step3 : ∫⁻ x in cone B, ENNReal.ofReal |(fderiv ℝ (homoExt g) x).det| *
        F (‖homoExt g x‖⁻¹ • homoExt g x) ∂(volume : Measure (E n))
      = ∫⁻ y in homoExt g '' cone B, F (‖y‖⁻¹ • y) ∂(volume : Measure (E n)) := by
    have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (E n)) hcone
      (fun x hx => (hdiff x (hcone_sub hx)).hasFDerivAt.hasFDerivWithinAt)
      (hinj.mono hcone_sub) (fun y => F (‖y‖⁻¹ • y))
    exact h.symm
  have step5 : (n : ENNReal) • ∫⁻ y in cone (bd g '' B), F (‖y‖⁻¹ • y)
        ∂(volume : Measure (E n))
      = ∫⁻ η in bd g '' B, F η ∂(sphMeas n) := by
    have h := hpol (bd g '' B) himg himg_sub F hF
    rw [h, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hn0 hntop, one_mul]
  calc ∫⁻ ξ in B, F (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)) ∂(sphMeas n)
      = (n : ENNReal) • ∫⁻ x in cone B, G (‖x‖⁻¹ • x) ∂(volume : Measure (E n)) := step1
    _ = (n : ENNReal) • ∫⁻ x in cone B, ENNReal.ofReal |(fderiv ℝ (homoExt g) x).det| *
          F (‖homoExt g x‖⁻¹ • homoExt g x) ∂(volume : Measure (E n)) := by rw [step2]
    _ = (n : ENNReal) • ∫⁻ y in homoExt g '' cone B, F (‖y‖⁻¹ • y)
          ∂(volume : Measure (E n)) := by rw [step3]
    _ = (n : ENNReal) • ∫⁻ y in cone (bd g '' B), F (‖y‖⁻¹ • y)
          ∂(volume : Measure (E n)) := by rw [coneImage n hn hA g B hBs]
    _ = ∫⁻ η in bd g '' B, F η ∂(sphMeas n) := step5

/-- `sphMeas n` is carried by the unit sphere. -/
theorem sphMeas_compl_sphere (n : ℕ) : sphMeas n (Sph n)ᶜ = 0 := by
  have hmeas : MeasurableSet ((Sph n)ᶜ) := (measurableSet_Sph n).compl
  rw [sphMeas, Measure.map_apply continuous_subtype_val.measurable hmeas]
  have hpre : (Subtype.val : Metric.sphere (0 : E n) 1 → E n) ⁻¹' (Sph n)ᶜ = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact x.2
  rw [hpre, measure_empty]

/-- The transformation law for the unnormalised surface measure under the boundary action. -/
theorem sphMeas_map_bd_core (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (g : PO n 1)
    (hjac : ∀ x : E n, x ≠ 0 →
      |(fderiv ℝ (homoExt g) x).det| = (dfun g (‖x‖⁻¹ • x)) ^ (-(n : ℝ) + 1))
    (hdiff : ∀ x : E n, x ≠ 0 → DifferentiableAt ℝ (homoExt g) x)
    (hnorm : ∀ x : E n, x ≠ 0 → ‖homoExt g x‖ = ‖x‖)
    (hdir : ∀ x : E n, x ≠ 0 → ‖x‖⁻¹ • homoExt g x = bd g (‖x‖⁻¹ • x))
    (hinj : Set.InjOn (homoExt g) {x : E n | x ≠ 0})
    (hpol : ∀ (B' : Set (E n)), MeasurableSet B' → B' ⊆ Sph n → ∀ (G : E n → ℝ≥0∞),
        Measurable G →
        ∫⁻ x in cone B', G (‖x‖⁻¹ • x) ∂(volume : Measure (E n))
          = (n : ENNReal)⁻¹ * ∫⁻ ξ, G ξ ∂((sphMeas n).restrict B'))
    (hdfun_pos : ∀ ξ : E n, ξ ∈ Sph n → 0 < dfun g ξ) :
    (sphMeas n).map (bd g)
      = (sphMeas n).withDensity
          (fun η => ENNReal.ofReal ((dfun g (bd g⁻¹ η)) ^ (n - 1))) := by
  have hsupp := sphMeas_compl_sphere n
  let Dens : E n → ℝ≥0∞ := fun η => ENNReal.ofReal ((dfun g (bd g⁻¹ η)) ^ (n - 1))
  have hDens : Measurable Dens := by
    show Measurable (fun η : E n => ENNReal.ofReal ((dfun g (bd g⁻¹ η)) ^ (n - 1)))
    exact (((measurable_dfun g).comp (bd_measurable hA g⁻¹)).pow_const (n - 1)).ennreal_ofReal
  ext T hT
  rw [Measure.map_apply (bd_measurable hA g) hT]
  show sphMeas n (bd g ⁻¹' T) = ((sphMeas n).withDensity Dens) T
  rw [withDensity_apply Dens hT]
  have hB : MeasurableSet ((bd g ⁻¹' T) ∩ Sph n) :=
    ((bd_measurable hA g) hT).inter (measurableSet_Sph n)
  have hBs : (bd g ⁻¹' T) ∩ Sph n ⊆ Sph n := Set.inter_subset_right
  have hcore := sphChangeOfVars_core n hn hA g ((bd g ⁻¹' T) ∩ Sph n) hB hBs Dens hDens
    hjac hdiff hnorm hdir hinj hpol
  have hpt : ∀ ξ ∈ (bd g ⁻¹' T) ∩ Sph n,
      Dens (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)) = 1 := by
    rintro ξ ⟨-, hξ⟩
    have hξ' : bd g⁻¹ (bd g ξ) = ξ := bd_left hA g hξ
    have ha : 0 < dfun g ξ := hdfun_pos ξ hξ
    have h1 : Dens (bd g ξ) = ENNReal.ofReal ((dfun g ξ) ^ (n - 1)) := by
      show ENNReal.ofReal ((dfun g (bd g⁻¹ (bd g ξ))) ^ (n - 1))
        = ENNReal.ofReal ((dfun g ξ) ^ (n - 1))
      rw [hξ']
    have h2 : ENNReal.ofReal ((dfun g ξ) ^ (n - 1)) *
        ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_add ha]
      have hexp : (((n - 1 : ℕ) : ℝ) + (-(n : ℝ) + 1)) = 0 := by
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn]; norm_num
        rw [hcast]; ring
      rw [hexp, Real.rpow_zero]
    rw [h1, h2]
  have hmeasure : sphMeas n (bd g ⁻¹' T) = sphMeas n ((bd g ⁻¹' T) ∩ Sph n) := by
    have h := measure_inter_add_sdiff (μ := sphMeas n) (bd g ⁻¹' T) (measurableSet_Sph n)
    have h0 : sphMeas n ((bd g ⁻¹' T) \ Sph n) = 0 :=
      measure_mono_null (fun x hx => hx.2) hsupp
    rw [h0, add_zero] at h
    exact h.symm
  have hae : T =ᵐ[sphMeas n] (T ∩ Sph n) := by
    filter_upwards [(MeasureTheory.ae_iff).mpr
      (by rw [show {a : E n | ¬ a ∈ Sph n} = (Sph n)ᶜ from rfl]; exact hsupp)] with x hx
    exact propext ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  have hpull : ∫⁻ η in T, Dens η ∂(sphMeas n)
      = ∫⁻ η in T ∩ Sph n, Dens η ∂(sphMeas n) := by
    rw [Measure.restrict_congr_set hae]
  have hA1 : ∫⁻ ξ in (bd g ⁻¹' T) ∩ Sph n,
          Dens (bd g ξ) * ENNReal.ofReal ((dfun g ξ) ^ (-(n : ℝ) + 1)) ∂(sphMeas n)
      = ∫⁻ ξ in (bd g ⁻¹' T) ∩ Sph n, 1 ∂(sphMeas n) := by
    apply setLIntegral_congr_fun hB
    intro ξ hξ
    exact hpt ξ hξ
  rw [hmeasure, ← setLIntegral_one, ← hA1, hcore, bd_image_preimage hA g T, hpull]
/-- `sMat g` preserves the Minkowski form. -/
theorem mink_sMatv (g : PO n 1) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink ((sMat g).mulVec x) ((sMat g).mulVec y) = Hyper.mink x y := by
  rw [sMat, Matrix.smul_mulVec, Matrix.smul_mulVec, Hyper.mink_smul,
    Hyper.mink_mulVec (mat (rep g)) (Hyper.mat_conj (rep g)), Hyper.tsign_mul_self, one_mul]

/-- `⟨wvec_visualDefs g ξ, wvec_visualDefs g η⟩ = ⟪ξ,η⟫ - 1`. -/
theorem mink_wvecv (g : PO n 1) (ξ η : E n) :
    Hyper.mink (wvec_visualDefs g ξ) (wvec_visualDefs g η) = inner ℝ ξ η - 1 := by
  rw [wvec_visualDefs, wvec_visualDefs, mink_sMatv, Hyper.mink_apply, Hyper.inner_eq_sum]
  simp [hvec]

theorem tpart_zero : tpart (0 : E n) = 1 := by simp [tpart]

theorem mink_smul_rightv (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (r • y) = r * Hyper.mink x y := by
  rw [Hyper.mink_apply, Hyper.mink_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by ring)
  · ring

theorem hvec_zero' : hvec (0 : E n) = hlift (0 : E n) := by
  funext z; rcases z with i | j
  · simp [hvec, hlift]
  · fin_cases j; simp [hvec, hlift, tpart_zero]

/-- `wvec_visualDefs g 0 = hlift (g • 0)`. -/
theorem wvec_zerov (g : PO n 1) : wvec_visualDefs g (0 : E n) = hlift (g • (0 : E n)) := by
  rw [wvec_visualDefs, sMat, Matrix.smul_mulVec, hvec_zero']
  rw [show g • (0 : E n) = actO (rep g) 0 from rfl, Hyper.hlift_actO]

/-- `dfun g` is positive on the sphere. -/
theorem dfun_posv (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) : 0 < dfun g ξ := by
  have h := o1SignTime (rep g) ξ (le_of_eq ((mem_Sph_iff ξ).1 hξ))
  rw [dfun, wvec_visualDefs, sMat, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  exact h

/-- `dfun g ξ` is the inverse of the Busemann denominator at `g • 0`. -/
theorem dfun_formulav (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) :
    dfun g ξ = (tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) (bd g ξ))⁻¹ := by
  have ht : dfun g ξ ≠ 0 := ne_of_gt (dfun_posv g ξ hξ)
  have hkey : wvec_visualDefs g ξ = (dfun g ξ) • hvec (bd g ξ) := by
    funext z; rcases z with i | j
    · have h1 : (bd g ξ) i = (phiFun g ξ) i := by rw [← phiFun_eq_bd g ξ]
      simp only [Pi.smul_apply, smul_eq_mul, hvec, Sum.elim_inl, h1]
      rw [phiFun]
      simp only [WithLp.ofLp_toLp]
      field_simp
    · fin_cases j
      simp [hvec, dfun]
  have h1 : Hyper.mink (wvec_visualDefs g (0 : E n)) (wvec_visualDefs g ξ) = -1 := by
    rw [mink_wvecv]; simp
  rw [wvec_zerov, hkey, mink_smul_rightv] at h1
  have hmk : Hyper.mink (hlift (g • (0 : E n))) (hvec (bd g ξ))
      = inner ℝ (g • (0 : E n)) (bd g ξ) - tpart (g • (0 : E n)) := by
    rw [Hyper.mink_apply, Hyper.inner_eq_sum]
    simp [hlift, hvec]
  rw [hmk] at h1
  have hD : dfun g ξ * (tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) (bd g ξ)) = 1 := by
    linarith
  exact eq_inv_of_mul_eq_one_left hD

/-- A measure vanishing off the sphere only depends on the intersection with the sphere. -/
theorem measure_eq_measure_inter {μ : Measure (E n)} (h : μ (Sph n)ᶜ = 0) (X : Set (E n)) :
    μ X = μ (X ∩ Sph n) := by
  have h' := measure_inter_add_sdiff (μ := μ) X (measurableSet_Sph n)
  have h0 : μ (X \ Sph n) = 0 := measure_mono_null (fun x hx => hx.2) h
  rw [h0, add_zero] at h'
  exact h'.symm

/-- On the sphere, the `dfun`-density of the transformation law equals the Poisson density. -/
theorem dens_eq (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (g : PO n 1)
    (hdfun : ∀ ξ : E n, ξ ∈ Sph n →
        dfun g ξ = (tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) (bd g ξ))⁻¹)
    (hdfun_pos : ∀ ξ : E n, ξ ∈ Sph n → 0 < dfun g ξ) :
    (fun η : E n => ENNReal.ofReal ((dfun g (bd g⁻¹ η)) ^ (n - 1)))
      =ᵐ[sphMeas n]
      (fun ξ : E n => ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ (g • (0 : E n))))) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (sphMeas_compl_sphere n)
  intro η hη
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  intro hηS
  refine hη ?_
  have hb : bd g⁻¹ η ∈ Sph n := bd_sph hA g⁻¹ hηS
  have hb' : bd g (bd g⁻¹ η) = η := bd_right hA g hηS
  have ha : 0 < tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) η := by
    have hle : inner ℝ (g • (0 : E n)) η ≤ ‖g • (0 : E n)‖ := by
      calc inner ℝ (g • (0 : E n)) η ≤ ‖g • (0 : E n)‖ * ‖η‖ := real_inner_le_norm _ _
        _ = ‖g • (0 : E n)‖ := by rw [(mem_Sph_iff η).1 hηS, mul_one]
    have hlt : ‖g • (0 : E n)‖ < tpart (g • (0 : E n)) := by
      rw [tpart, Real.lt_sqrt (norm_nonneg _)]
      nlinarith [sq_nonneg ‖g • (0 : E n)‖]
    linarith
  rw [hdfun (bd g⁻¹ η) hb, hb']
  congr 1
  show ((tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) η)⁻¹) ^ (n - 1)
      = Real.exp (-((n : ℝ) - 1) * Real.log (tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) η))
  set a := tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) η with ha_def
  calc (a⁻¹) ^ (n - 1) = (a ^ (n - 1))⁻¹ := inv_pow a (n - 1)
    _ = (a ^ (((n - 1 : ℕ) : ℝ)))⁻¹ := by rw [Real.rpow_natCast]
    _ = a ^ (-(((n - 1 : ℕ) : ℝ))) := by rw [Real.rpow_neg (le_of_lt ha)]
    _ = a ^ (-((n : ℝ) - 1)) := by
          congr 1
          rw [Nat.cast_sub hn]; norm_num
    _ = (Real.exp (Real.log a)) ^ (-((n : ℝ) - 1)) := by rw [Real.exp_log ha]
    _ = Real.exp (Real.log a * (-((n : ℝ) - 1))) := by rw [Real.exp_mul]
    _ = Real.exp (-((n : ℝ) - 1) * Real.log a) := by rw [mul_comm]

/-- The transformation law for the visual measure at the origin. -/
theorem sigma_map_bd_core (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (g : PO n 1)
    (hsm : (sphMeas n).map (bd g)
      = (sphMeas n).withDensity (fun η => ENNReal.ofReal ((dfun g (bd g⁻¹ η)) ^ (n - 1))))
    (hdfun : ∀ ξ : E n, ξ ∈ Sph n →
        dfun g ξ = (tpart (g • (0 : E n)) - inner ℝ (g • (0 : E n)) (bd g ξ))⁻¹)
    (hdfun_pos : ∀ ξ : E n, ξ ∈ Sph n → 0 < dfun g ξ) :
    (sigma n).map (bd g) = visual n (g • (0 : E n)) := by
  have hnu : (sigma n) = (sphMeas n Set.univ)⁻¹ • sphMeas n := rfl
  have hae := dens_eq n hn hA g hdfun hdfun_pos
  calc (sigma n).map (bd g)
      = ((sphMeas n Set.univ)⁻¹ • sphMeas n).map (bd g) := by rw [hnu]
    _ = (sphMeas n Set.univ)⁻¹ • (sphMeas n).map (bd g) :=
          Measure.map_smul (c := (sphMeas n Set.univ)⁻¹) (μ := sphMeas n) (f := bd g)
            (bd_measurable hA g).aemeasurable
    _ = (sphMeas n Set.univ)⁻¹ • (sphMeas n).withDensity
          (fun η => ENNReal.ofReal ((dfun g (bd g⁻¹ η)) ^ (n - 1))) := by rw [hsm]
    _ = (sphMeas n Set.univ)⁻¹ • (sphMeas n).withDensity
          (fun ξ => ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ (g • (0 : E n))))) := by
          rw [withDensity_congr_ae hae]
    _ = ((sphMeas n Set.univ)⁻¹ • sphMeas n).withDensity
          (fun ξ => ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ (g • (0 : E n))))) := by
          rw [withDensity_smul_measure]
    _ = visual n (g • (0 : E n)) := by rw [visual, hnu]

/-- `VisualProp n` from the transformation law for the visual measure at the origin. -/
theorem visualProp_of_transLaw (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (htrans : ∀ h : PO n 1, (sigma n).map (bd h) = visual n (h • (0 : E n))) :
    VisualProp n := by
  have h2 : 2 ≤ n := by omega
  obtain ⟨hprob, hsupp0, hatom0, hpos0, -⟩ := visualBasic n h2
  intro u
  obtain ⟨h, hh⟩ := poTransitive n (by omega) hA u
  have hvisu : visual n u = (sigma n).map (bd h) := by rw [← hh, htrans h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hvisu]
    refine ⟨?_⟩
    rw [Measure.map_apply (bd_measurable hA h) MeasurableSet.univ, Set.preimage_univ]
    exact hprob.measure_univ
  · rw [hvisu, Measure.map_apply (bd_measurable hA h) (measurableSet_Sph n).compl]
    exact measure_mono_null (fun x hx hxS => hx (bd_sph hA h hxS)) hsupp0
  · intro ξ
    rw [hvisu, Measure.map_apply (bd_measurable hA h) (measurableSet_singleton ξ),
      measure_eq_measure_inter hsupp0]
    refine measure_mono_null ?_ (hatom0 (bd h⁻¹ ξ))
    intro x hx
    rw [Set.mem_singleton_iff]
    obtain ⟨hx1, hxS⟩ := hx
    rw [← hx1, bd_left hA h hxS]
  · intro U hU hne
    rw [hvisu, Measure.map_apply (bd_measurable hA h) hU.measurableSet]
    obtain ⟨ξ, hξU, hξS⟩ := hne
    have hx : bd h⁻¹ ξ ∈ Sph n := bd_sph hA h⁻¹ hξS
    have hxh : bd h (bd h⁻¹ ξ) = ξ := bd_right hA h hξS
    have hcont : ContinuousWithinAt (bd h) (Sph n) (bd h⁻¹ ξ) :=
      ((bd_cont hA h).continuousWithinAt) hx
    have hnhds : bd h ⁻¹' U ∈ 𝓝[Sph n] (bd h⁻¹ ξ) :=
      hcont.preimage_mem_nhdsWithin (hU.mem_nhds (by rw [hxh]; exact hξU))
    obtain ⟨V, hV, hVs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
    obtain ⟨V', hV'sub, hV'open, hxV'⟩ := mem_nhds_iff.mp hV
    have hVsph : V' ∩ Sph n ⊆ bd h ⁻¹' U := fun y hy => hVs ⟨hV'sub hy.1, hy.2⟩
    have hne' : (V' ∩ Sph n).Nonempty := ⟨bd h⁻¹ ξ, hxV', hx⟩
    calc 0 < sigma n (V' ∩ Sph n) := by
          rw [← measure_eq_measure_inter hsupp0 V']
          exact hpos0 V' hV'open hne'
      _ ≤ sigma n (bd h ⁻¹' U) := measure_mono hVsph
  · intro g
    have hmul : (g * h) • (0 : E n) = g • u := by
      rw [hmul_law hA g h (0 : E n), hh]
    have hae : (bd g ∘ bd h) =ᵐ[sigma n] bd (g * h) := by
      filter_upwards [(MeasureTheory.ae_iff).mpr
        (by rw [show {a : E n | ¬ a ∈ Sph n} = (Sph n)ᶜ from rfl]; exact hsupp0)] with ξ hξ
      exact (bd_mul' hA g h hξ).symm
    rw [hvisu, Measure.map_map (bd_measurable hA g) (bd_measurable hA h),
      Measure.map_congr hae, htrans (g * h), hmul]

/-- The transformation law for the visual measure at the origin (fully instantiated). -/
theorem sigma_map_bd (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (g : PO n 1) :
    (sigma n).map (bd g) = visual n (g • (0 : E n)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hnorm, hdir, hinj⟩ := homoExtGeom n hn1 hA g
  have hsm := sphMeas_map_bd_core n hn1 hA g
    (fun x hx => homoExtJac n hn1 g x hx)
    (fun x hx => homoExt_diff n hn1 g x hx)
    hnorm hdir hinj
    (fun B' hB' hBs' G hG => spherePolarv n hn1 B' hB' hBs' G hG)
    (fun ξ hξ => dfun_posv g ξ hξ)
  exact sigma_map_bd_core n hn1 hA g hsm (fun ξ hξ => dfun_formulav g ξ hξ)
    (fun ξ hξ => dfun_posv g ξ hξ)

end

end Work.Mostow
