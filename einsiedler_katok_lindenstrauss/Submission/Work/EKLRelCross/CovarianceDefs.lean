import Mathlib
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.covariant_shape
import Submission.Work.EKLComp.LeafAux

/-!
# Vocabulary for the `A`-covariance (U7)

* `conjDs t D` — the image of a set of matrices under `g ↦ aDiag t * g * (aDiag t)⁻¹`.
* `CovPt ν t x` — the pointwise `A`-covariance (EKL (4)) at a single point: `ν (aDiag t • x)`
  is proportional to `(ν x)` composed with the conjugation.
* `local_covariance_shape` — Pisa 7.17 in the orientation of the target, obtained from the
  already-proved `Work.EKLRelCross.covariant_shape` by reversing time (`t ↦ -t`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## Conjugation by the diagonal flow -/

/-- The image of a set of matrices under `g ↦ aDiag t * g * (aDiag t)⁻¹`. -/
def conjDs (t : Fin 3 → ℝ) (D : Set SL3) : Set SL3 :=
  (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) '' D

/-- The conjugation maps compose. -/
lemma conjFun_add (s t : Fin 3 → ℝ) :
    (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹) ∘
        (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)
      = (fun g : SL3 => aDiag (s + t) * g * (aDiag (s + t))⁻¹) := by
  funext g
  simp only [Function.comp_apply, ← aDiag_add s t]
  group

lemma conjDs_add (s t : Fin 3 → ℝ) (D : Set SL3) :
    conjDs s (conjDs t D) = conjDs (s + t) D := by
  unfold conjDs
  rw [Set.image_image]
  congr 1
  funext g
  simp only [Function.comp_apply, ← aDiag_add s t]
  group

lemma conjDs_zero (D : Set SL3) : conjDs 0 D = D := by
  unfold conjDs
  rw [aDiag_zero]
  ext g
  simp

lemma conjDs_neg_cancel (t : Fin 3 → ℝ) (D : Set SL3) : conjDs (-t) (conjDs t D) = D := by
  rw [conjDs_add]
  have h : (-t : Fin 3 → ℝ) + t = 0 := by funext i; simp
  rw [h, conjDs_zero]

lemma conjDs_add_neg_cancel (t : Fin 3 → ℝ) (D : Set SL3) : conjDs t (conjDs (-t) D) = D := by
  rw [conjDs_add]
  have h : (t : Fin 3 → ℝ) + -t = 0 := by funext i; simp
  rw [h, conjDs_zero]

lemma conjDs_mono (t : Fin 3 → ℝ) : Monotone (conjDs t) :=
  fun _ _ h => Set.image_mono h

/-- The preimage of `D` under conjugation by `aDiag (-t)` is `conjDs t D`. -/
lemma preimage_conjDs_neg (t : Fin 3 → ℝ) (D : Set SL3) :
    (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) ⁻¹' D = conjDs t D := by
  have hinv : aDiag (-t) = (aDiag t)⁻¹ := eq_inv_of_mul_eq_one_right (aDiag_mul_neg t)
  ext g
  simp only [Set.mem_preimage, conjDs, Set.mem_image]
  constructor
  · intro hg
    refine ⟨aDiag (-t) * g * (aDiag (-t))⁻¹, hg, ?_⟩
    rw [hinv]
    group
  · rintro ⟨h, hh, rfl⟩
    rw [hinv]
    have he : (aDiag t)⁻¹ * (aDiag t * h * (aDiag t)⁻¹) * ((aDiag t)⁻¹)⁻¹ = h := by group
    rw [he]
    exact hh

/-- Conjugation preserves measurability. -/
lemma measurableSet_conjDs (t : Fin 3 → ℝ) {D : Set SL3} (hD : MeasurableSet D) :
    MeasurableSet (conjDs t D) := by
  rw [← preimage_conjDs_neg t D]
  exact hD.preimage (((continuous_const.mul continuous_id).mul continuous_const).measurable)

/-- The conjugation map is measurable. -/
lemma measurable_conjFun (t : Fin 3 → ℝ) :
    Measurable (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

/-! ## The pointwise covariance -/

/-- **The pointwise covariance at `x` for the parameter `t`**: EKL (4) at a single point. -/
def CovPt (ν : X3 → Measure SL3) (t : Fin 3 → ℝ) (x : X3) : Prop :=
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ν (aDiag t • x) = c • (ν x).map (fun g => aDiag t * g * (aDiag t)⁻¹)

lemma CovPt_iff_test (ν : X3 → Measure SL3) (t : Fin 3 → ℝ) (x : X3) :
    CovPt ν t x ↔ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ D : Set SL3, MeasurableSet D →
      ν (aDiag t • x) D = c * (ν x).map (fun g => aDiag t * g * (aDiag t)⁻¹) D := by
  constructor
  · rintro ⟨c, h0, ht, hc⟩
    exact ⟨c, h0, ht, fun D _ => by rw [hc, Measure.smul_apply, smul_eq_mul]⟩
  · rintro ⟨c, h0, ht, hc⟩
    exact ⟨c, h0, ht, Measure.ext fun D hD => by
      rw [Measure.smul_apply, smul_eq_mul, hc D hD]⟩

/-- **Pisa 7.17 in the orientation of the target.**  For a plaque algebra `(Z, S.m)` of positive
`μ`-measure, `μ`-a.e. `x` with `x ∈ Z`, free `U`-orbit and `x`, `aDiag t • x ∈ X'` satisfies the
relative covariance on `conjDs t (shape S.m U x)`.

This is `Work.EKLRelCross.covariant_shape` with `t` replaced by `-t` and applied at the point
`aDiag t • x` (the two statements are equivalent because `aDiag t` is a measure-preserving
bijection of `X₃`, with inverse `aDiag (-t)`). -/
theorem local_covariance_shape {U : Subgroup SL3} (hU : IsHoro U)
    {μ : Measure X3} [IsProbabilityMeasure μ]
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (t : Fin 3 → ℝ) (ht : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {Z : Set X3} (S : MAlgX) (hpla : IsPlaqueAlgebra U Z S.m) (hμZ : μ Z ≠ 0) :
    ∀ᵐ x ∂μ, x ∈ X' → aDiag t • x ∈ X' → x ∈ Z →
      (∀ u ∈ U, u • x = x → u = 1) →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ D : Set SL3, MeasurableSet D →
        D ⊆ shape S.m U x → ν (aDiag t • x) (conjDs t D) = c * ν x D := by
  have htneg : MeasurePreserving (fun x : X3 => aDiag (-t) • x) μ μ := by
    refine ⟨(continuous_const_smul _).measurable, ?_⟩
    have hcomp : (fun x : X3 => aDiag (-t) • x) ∘ (fun x : X3 => aDiag t • x) = id := by
      funext x
      simp only [Function.comp_apply, id_eq]
      rw [aDiag_neg_smul]
    calc μ.map (fun x : X3 => aDiag (-t) • x)
        = (μ.map (fun x : X3 => aDiag t • x)).map (fun x : X3 => aDiag (-t) • x) := by
          rw [ht.map_eq]
      _ = μ.map ((fun x : X3 => aDiag (-t) • x) ∘ (fun x : X3 => aDiag t • x)) := by
          rw [Measure.map_map (continuous_const_smul _).measurable
            (continuous_const_smul _).measurable]
      _ = μ.map id := by rw [hcomp]
      _ = μ := Measure.map_id
  have hcs := covariant_shape (U := U) hU (μ := μ) (ν := ν) (X' := X') hL (-t) htneg hpla hμZ
  have hcs' : ∀ᵐ x ∂μ,
      ((fun y : X3 => y ∈ X' → aDiag (-t) • y ∈ X' → aDiag (-t) • y ∈ Z →
        (∀ u ∈ U, u • (aDiag (-t) • y) = aDiag (-t) • y → u = 1) →
        ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ C : Set SL3, MeasurableSet C →
          C ⊆ shape S.m U (aDiag (-t) • y) →
          ν (aDiag (-t) • y) C =
            c * (ν y).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) C)
        (aDiag t • x)) := ht.quasiMeasurePreserving.ae hcs
  filter_upwards [hcs'] with x hx
  intro hxX hxXt hxZ hfree
  have hx0 : aDiag (-t) • (aDiag t • x) = x := aDiag_neg_smul t x
  have h := hx hxXt (by rw [hx0]; exact hxX) (by rw [hx0]; exact hxZ) (by rw [hx0]; exact hfree)
  obtain ⟨c, hc0, hct, hcc⟩ := h
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  intro D hD hDsub
  have h1 := hcc D hD (by rw [hx0]; exact hDsub)
  rw [hx0] at h1
  have hmap : (ν (aDiag t • x)).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) D
      = ν (aDiag t • x) (conjDs t D) := by
    rw [Measure.map_apply (measurable_conjFun (-t)) hD, preimage_conjDs_neg]
  rw [hmap] at h1
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

end Work.EKLRelCross
