import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.GonLib

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open MeasureTheory Finset
open scoped Pointwise Topology

namespace Work.HP.BCS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Casts from `ℤ^ι` to `ℝ^ι` -/

theorem linearIndependent_toR_cast {κ : Type*} {b : κ → (ι → ℤ)}
    (hb : LinearIndependent ℤ b) : LinearIndependent ℝ (fun i => toR (b i)) := by
  have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := b)).mpr hb
  have h' : (fun i => toR (b i)) = fun i => algebraMap ℤ ℝ ∘ b i := by
    funext i j
    simp [toR]
  rw [h']
  exact h

theorem linearIndependent_toEr_cast {κ : Type*} {b : κ → (ι → ℤ)}
    (hb : LinearIndependent ℤ b) : LinearIndependent ℝ (fun i => toEr (b i)) := by
  have h := linearIndependent_toR_cast hb
  have h' : (fun i => toEr (b i)) = ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm) ∘
      (fun i => toR (b i)) := by
    funext i
    simp only [Function.comp_apply, toEr, toE, WithLp.linearEquiv_symm_apply, WithLp.addEquiv]
  rw [h']
  exact h.map' _ (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))

/-! ## Norms and inner products of `toE` -/

theorem dotR_comm (u v : ι → ℝ) : dotR u v = dotR v u := by
  rw [dotR, dotR]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem inner_toE_toE (u v : ι → ℝ) : inner ℝ (toE u) (toE v) = dotR v u := by
  rw [dotR, toE, toE, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, RCLike.inner_apply]
  simp

theorem norm_toE_eq_eNorm (v : ι → ℤ) : ‖toE (toR v)‖ = eNorm v := by
  show ‖WithLp.toLp 2 (fun k => (v k : ℝ))‖ = eNorm v
  exact norm_toLp v

theorem rNorm_eq_norm_toE (v : ι → ℝ) : rNorm v = ‖toE v‖ := by
  rw [rNorm, toE, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]

theorem norm_toEr (v : ι → ℤ) : ‖toEr v‖ = eNorm v := norm_toE_eq_eNorm v

theorem rNorm_toR (v : ι → ℤ) : rNorm (toR v) = eNorm v := by
  rw [rNorm_eq_norm_toE]
  exact norm_toEr v

theorem inner_toE_toEr (v : ι → ℝ) (a : ι → ℤ) :
    inner ℝ (toE v) (toEr a) = dotR v (toR a) := by
  rw [toEr, inner_toE_toE, dotR_comm]

/-! ## The cone condition in Euclidean space -/

theorem mem_Cgam_iff (v : ι → ℝ) (γ : ℝ) (a : ι → ℤ) :
    toR a ∈ Cgam v γ ↔ |inner ℝ (toE v) (toEr a)| ≤ ‖toE v‖ * ‖toEr a‖ / (2 * γ) := by
  have h1 : rNorm (toR a) = ‖toEr a‖ := by rw [rNorm_eq_norm_toE]; rfl
  rw [Cgam, Set.mem_ofPred_eq, inner_toE_toEr, h1, rNorm_eq_norm_toE]

/-! ## The coefficient map attached to a `ℤ`-basis -/

/-- `toR` as a `ℤ`-linear map. -/
def toRLin : (ι → ℤ) →ₗ[ℤ] (ι → ℝ) where
  toFun := toR
  map_add' a b := by ext i; simp [toR]
  map_smul' n a := by ext i; simp [toR]

@[simp] theorem toRLin_apply (a : ι → ℤ) : toRLin a = toR a := rfl

/-- The coefficient map of a family of integer vectors: `x ↦ Σ i, x i • toEr (v i)`. -/
def coeffMap {k : ℕ} (v : Fin k → (ι → ℤ)) : (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  phiOf v

theorem coeffMap_apply {k : ℕ} (v : Fin k → (ι → ℤ)) (x : Fin k → ℝ) :
    coeffMap v x = phiOf v x := rfl

theorem ofLp_sum_smul {k : ℕ} (v : Fin k → (ι → ℤ)) (x : Fin k → ℝ) (j : ι) :
    ((∑ i, x i • toEr (v i) : EuclideanSpace ℝ ι)).ofLp j = ∑ i, x i * ((v i) j : ℝ) := by
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, toEr, toE, toR]

theorem phiOf_ofLp {k : ℕ} (v : Fin k → (ι → ℤ)) (x : Fin k → ℝ) (j : ι) :
    (phiOf v x).ofLp j = ∑ i, x i * ((v i) j : ℝ) := by
  rw [phiOf_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem coeffMap_eq_sum {k : ℕ} (v : Fin k → (ι → ℤ)) (x : Fin k → ℝ) :
    coeffMap v x = ∑ i, x i • toEr (v i) := by
  apply WithLp.ofLp_injective (p := 2)
  funext j
  rw [coeffMap_apply, phiOf_ofLp, ofLp_sum_smul]

theorem coeffMap_single {k : ℕ} (v : Fin k → (ι → ℤ)) (i : Fin k) :
    coeffMap v (Pi.single i 1) = toEr (v i) := by
  rw [coeffMap_eq_sum, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_smul]
  · intro j _ hj
    rw [show (Pi.single i (1:ℝ) : Fin k → ℝ) j = 0 by simp [Pi.single_eq_of_ne, hj], zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

section transport

variable {k : ℕ}

/-- `toEr` as a `ℤ`-linear map. -/
def toErLin : (ι → ℤ) →ₗ[ℤ] EuclideanSpace ℝ ι :=
  ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.restrictScalars ℤ).comp toRLin

theorem toErLin_apply (a : ι → ℤ) : toErLin a = toEr a := rfl

theorem toErLin_image (S : Set (ι → ℤ)) : toErLin '' S = toEr '' S := by
  ext x
  constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩

/-- Evaluating the coefficient map at a standard basis vector. -/
theorem coeffMap_piSingle {k : ℕ} (v : Fin k → (ι → ℤ)) (i : Fin k) :
    coeffMap v (Pi.single i (1:ℝ)) = toEr (v i) := by
  rw [coeffMap_eq_sum, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_smul]
  · intro j _ hj
    rw [show (Pi.single i (1:ℝ) : Fin k → ℝ) j = 0 by simp [Pi.single_eq_of_ne, hj], zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The range of the coefficient map is the real span of the images of the vectors. -/
theorem range_coeffMap {k : ℕ} (v : Fin k → (ι → ℤ)) :
    (coeffMap v).range = Submodule.span ℝ (Set.range (fun i => toEr (v i))) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [coeffMap_eq_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact ⟨Pi.single i 1, coeffMap_piSingle v i⟩

/-- The `ℤ`-span of the coercions of the basis vectors of a `ℤ`-basis of `L` is `L`. -/
theorem span_range_coe {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Submodule.span ℤ (Set.range (fun i => ((b i : L) : ι → ℤ))) = L := by
  have h : Set.range (fun i => ((b i : L) : ι → ℤ)) = (Submodule.subtype L) '' Set.range b :=
    Set.range_comp' (Submodule.subtype L) b
  rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

/-- The image of an integer span under `toEr` lies in the real span of the images. -/
theorem toEr_mem_span (S : Set (ι → ℤ)) (a : ι → ℤ)
    (ha : a ∈ Submodule.span ℤ S) : toEr a ∈ Submodule.span ℝ (toErLin '' S) := by
  have hspan : Submodule.span ℤ (toErLin '' S) ≤
      (Submodule.span ℝ (toErLin '' S)).restrictScalars ℤ :=
    Submodule.span_le.mpr fun x hx => Submodule.subset_span hx
  have h' : toEr a ∈ Submodule.map toErLin (Submodule.span ℤ S) := ⟨a, ha, rfl⟩
  rw [Submodule.map_span] at h'
  exact hspan h'

/-- The real span of a lattice is the real span of the images of a `ℤ`-basis. -/
theorem spanE_eq_span_range {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    spanE L = Submodule.span ℝ (Set.range (fun i => toEr ((b i : L) : ι → ℤ))) := by
  rw [spanE]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro a ⟨a', ha', rfl⟩
    have ha : a' ∈ Submodule.span ℤ (Set.range (fun i => ((b i : L) : ι → ℤ))) := by
      rw [span_range_coe L b]; exact ha'
    have h := toEr_mem_span (Set.range (fun i => ((b i : L) : ι → ℤ))) a' ha
    simpa [Set.range_comp', toErLin_image] using h
  · rw [Submodule.span_le]
    rintro a ⟨i, rfl⟩
    exact Submodule.subset_span ⟨_, (b i).2, rfl⟩

/-- The range of the coefficient map of a `ℤ`-basis of `L` is the real span of `L`. -/
theorem coeffMap_range (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (coeffMap (fun i => (b i : ι → ℤ))).range = spanE L :=
  (range_coeffMap (fun i => (b i : ι → ℤ))).trans (spanE_eq_span_range L b).symm

/-- The coefficient map of a `ℤ`-basis of `L` is injective. -/
theorem coeffMap_injective (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Function.Injective (coeffMap (fun i => (b i : ι → ℤ))) := by
  have hb : LinearIndependent ℤ (fun i => (b i : ι → ℤ)) :=
    b.linearIndependent.map' (Submodule.subtype L) (by
      rw [LinearMap.ker_eq_bot]
      exact Subtype.val_injective)
  have h := linearIndependent_toEr_cast hb
  intro x y hxy
  have h0 : ∑ i, (x i - y i) • toEr ((b i : ι → ℤ)) = 0 := by
    have h1 : coeffMap (fun i => (b i : ι → ℤ)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [coeffMap_eq_sum] at h1
    simpa [Pi.sub_apply, sub_smul] using h1
  have hg := (Fintype.linearIndependent_iff.mp h) (fun i => x i - y i) h0
  funext i
  have := hg i
  linarith

/-- The real span of a rank-`k` lattice is `k`-dimensional. -/
theorem finrank_spanE (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Module.finrank ℝ (spanE L) = k := by
  have h := LinearMap.finrank_range_of_inj (coeffMap_injective L b)
  rw [coeffMap_range L b] at h
  exact h.trans (by simp)

end transport

end Work.HP.BCS
