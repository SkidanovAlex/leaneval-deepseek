import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.BCS.Defs
import Submission.Work.HP.BCS.Setup
import Submission.Work.HP.Lat.detL_basis_gram

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open MeasureTheory Finset
open scoped Pointwise Topology

namespace Work.HP.BCS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toEkEquiv (k : ℕ) : (Fin k → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm

@[simp] theorem toEkEquiv_apply (k : ℕ) (x : Fin k → ℝ) :
    toEkEquiv k x = WithLp.toLp 2 x := rfl

@[simp] theorem toEkEquiv_symm_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    (toEkEquiv k).symm x = x.ofLp := rfl

theorem toEk_eq {k : ℕ} (t : Fin k → ℤ) :
    toEk t = toEkEquiv k (fun i => (t i : ℝ)) := rfl

def coeffEquiv {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (Fin k → ℝ) ≃ₗ[ℝ] spanE L :=
  LinearEquiv.ofBijective
    ((coeffMap (fun i => (b i : ι → ℤ))).codRestrict (spanE L) (by
      intro x
      rw [← coeffMap_range L b]
      exact LinearMap.mem_range_self _ x))
    ⟨fun x y h => coeffMap_injective L b (congrArg Subtype.val h), fun y => by
      have hy : (y : EuclideanSpace ℝ ι) ∈ (coeffMap (fun i => (b i : ι → ℤ))).range := by
        rw [coeffMap_range L b]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

theorem coeffEquiv_coe {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (x : Fin k → ℝ) :
    ((coeffEquiv L b x : spanE L) : EuclideanSpace ℝ ι)
      = coeffMap (fun i => (b i : ι → ℤ)) x := rfl

def isomSpan {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    spanE L ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) := by
  have h : Module.finrank ℝ (spanE L) = k := finrank_spanE L b
  let e := (stdOrthonormalBasis ℝ (spanE L)).repr
  rw [h] at e
  exact e

def PsiOf {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (isomSpan L b).toLinearMap.comp
    ((coeffEquiv L b).toLinearMap.comp (toEkEquiv k).symm.toLinearMap)

theorem PsiOf_injective {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Function.Injective (PsiOf L b) := by
  intro x y h
  simp only [PsiOf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap] at h
  exact (toEkEquiv k).symm.injective ((coeffEquiv L b).injective ((isomSpan L b).injective h))

theorem cast_piSingle {k : ℕ} (i : Fin k) :
    (fun j => ((Pi.single i (1 : ℤ) : Fin k → ℤ) j : ℝ)) = (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [show (Pi.single i (1 : ℤ) : Fin k → ℤ) j = 0 by simp [Pi.single_eq_of_ne, h]]
    rw [show (Pi.single i (1 : ℝ) : Fin k → ℝ) j = 0 by simp [Pi.single_eq_of_ne, h]]
    simp

theorem toEk_single_eq_single {k : ℕ} (i : Fin k) :
    toEk (Pi.single i (1 : ℤ)) = EuclideanSpace.single i (1 : ℝ) := by
  rw [toEk, EuclideanSpace.single, cast_piSingle i, PiLp.single]

/-- The evaluation of the coordinate map on the standard basis, in `Function.update` form. -/
theorem toEkEquiv_symm_single {k : ℕ} (i : Fin k) :
    (toEkEquiv k).symm.toLinearMap (EuclideanSpace.single i 1)
      = Function.update (0 : Fin k → ℝ) i 1 := by
  change (toEkEquiv k).symm (EuclideanSpace.single i 1) = Function.update (0 : Fin k → ℝ) i 1
  funext j
  rw [toEkEquiv_symm_apply, EuclideanSpace.single, PiLp.single_apply, Function.update_apply]
  by_cases h : j = i <;> simp [h]

/-- The coefficient map at the `i`-th coordinate vector is the `i`-th basis vector. -/
theorem coeffMap_update {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i : Fin k) :
    coeffMap (fun i => (b i : ι → ℤ)) (Function.update (0 : Fin k → ℝ) i 1)
      = toEr ((b i : ι → ℤ)) := by
  rw [coeffMap_eq_sum, Finset.sum_eq_single i]
  · rw [Function.update_self, one_smul]
  · intro j _ hj
    have hupd : Function.update (0 : Fin k → ℝ) i 1 j = 0 :=
      Function.update_of_ne (a := j) (a' := i) hj (1 : ℝ) (0 : Fin k → ℝ)
    rw [hupd, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem PsiOf_single_eq {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i : Fin k) :
    PsiOf L b (EuclideanSpace.single i 1)
      = isomSpan L b ⟨toEr ((b i : ι → ℤ)),
          Submodule.subset_span ⟨_, (b i).2, rfl⟩⟩ := by
  rw [PsiOf, LinearMap.comp_apply, LinearMap.comp_apply, toEkEquiv_symm_single i]
  show (isomSpan L b) (coeffEquiv L b (Function.update (0 : Fin k → ℝ) i 1))
      = (isomSpan L b) ⟨toEr ((b i : ι → ℤ)), Submodule.subset_span ⟨_, (b i).2, rfl⟩⟩
  exact congrArg (isomSpan L b) (Subtype.ext (by
    simpa using (coeffEquiv_coe L b (Function.update (0 : Fin k → ℝ) i 1)).trans
      (coeffMap_update L b i)))

theorem norm_PsiOf_single {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i : Fin k) :
    ‖PsiOf L b (EuclideanSpace.single i 1)‖ = eNorm ((b i : ι → ℤ)) := by
  rw [PsiOf_single_eq L b i, LinearIsometryEquiv.norm_map]
  exact norm_toEr _

theorem cellRad_PsiOf {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    cellRad (PsiOf L b) = ∑ i, eNorm ((b i : ι → ℤ)) := by
  rw [cellRad]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toEk_single_eq_single i]
  exact norm_PsiOf_single L b i

def coneVec {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) : EuclideanSpace ℝ (Fin k) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
    ((innerSL ℝ (toE v)).comp
      ((Submodule.subtypeL (spanE L)).comp
        (((isomSpan L b).symm : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] spanE L).toContinuousLinearEquiv.toContinuousLinearMap)))

theorem inner_coneVec {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (coneVec L b v) y
      = inner ℝ (toE v) (((isomSpan L b).symm y : spanE L) : EuclideanSpace ℝ ι) := by
  rw [coneVec, InnerProductSpace.toDual_symm_apply]
  rfl

end Work.HP.BCS
