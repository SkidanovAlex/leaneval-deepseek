import Mathlib
import Submission.Subspace.NumberField

/-!
# Independence transfer from ℂ to a subfield K ⊂ ℂ

Stage A/B glue for the subspace theorem.  After the coefficients of `L` are
shown to lie in a number field `K : IntermediateField ℚ ℂ` (see
`NumberField.lean`), the rows of `L` — which are linearly independent over ℂ —
are also linearly independent over `K` (both as row vectors and as `K`-linear
forms on `K^σ`).  This is what lets the classical proof run inside `K`.

We state the transfer abstractly: whenever `K` is a field embedded in ℂ and
`Λ : σ → σ → K` has ℂ-independent rows, the rows / the dot-product forms
are `K`-independent.
-/

open scoped BigOperators

namespace Submission.Subspace

section Transfer

variable {σ : Type*} [Fintype σ]

/-- The dot product `K`-linear form on `σ → K` with coefficient vector `a`. -/
def kForm {K : Type*} [CommSemiring K] (a : σ → K) : (σ → K) →ₗ[K] K where
  toFun := fun x => ∑ j : σ, a j * x j
  map_add' := by
    intro x y
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro c x
    simp [Finset.mul_sum, mul_left_comm]

/-- If the images in ℂ of the rows `Λ i : σ → K` are ℂ-linearly independent,
then the rows themselves are `K`-linearly independent. -/
theorem row_indep_transfer {K : Type*} [Field K] [Algebra K ℂ] (Λ : σ → σ → K)
    (hind : LinearIndependent ℂ (fun i : σ => fun j : σ => algebraMap K ℂ (Λ i j))) :
    LinearIndependent K (fun i : σ => Λ i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let rC : σ → σ → ℂ := fun i j => algebraMap K ℂ (Λ i j)
  have hrel : (∑ i : σ, algebraMap K ℂ (g i) • rC i) = 0 := by
    funext j
    have hgj := congrFun hg j
    apply_fun (algebraMap K ℂ) at hgj
    change (∑ i : σ, algebraMap K ℂ (g i) • rC i) j = 0
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, rC, map_sum, map_mul,
      Pi.zero_apply, map_zero] at hgj ⊢
    exact hgj
  have hindg := (Fintype.linearIndependent_iff.mp hind) (fun i => algebraMap K ℂ (g i))
    (by simpa [rC] using hrel) i
  exact (injective_iff_map_eq_zero (algebraMap K ℂ)).mp
    (algebraMap K ℂ).injective (g i) hindg

/-- If the rows have ℂ-independent images, then the associated `K`-linear
dot-product forms are `K`-linearly independent. -/
theorem form_indep_transfer {K : Type*} [Field K] [Algebra K ℂ] (Λ : σ → σ → K)
    (hind : LinearIndependent ℂ (fun i : σ => fun j : σ => algebraMap K ℂ (Λ i j))) :
    LinearIndependent K (fun i : σ => kForm (Λ i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let rC : σ → σ → ℂ := fun i j => algebraMap K ℂ (Λ i j)
  have hrows : (∑ i : σ, algebraMap K ℂ (a i) • rC i) = 0 := by
    funext j0
    change (∑ i : σ, algebraMap K ℂ (a i) • rC i) j0 = 0
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, rC]
    let e : σ → K := fun j => if j = j0 then 1 else 0
    have he0 : (∑ i : σ, a i • kForm (Λ i)) e = 0 := by
      have hmap := congrArg (fun φ : (σ → K) →ₗ[K] K => φ e) ha
      simpa using hmap
    have hk (i : σ) : kForm (Λ i) e = Λ i j0 := by
      simp [kForm, e]
    have he0' : (∑ i : σ, a i * (Λ i j0)) = 0 := by
      have he1 : (∑ i : σ, a i • kForm (Λ i)) e = ∑ i : σ, a i * (kForm (Λ i) e) := by
        simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [he1] at he0
      convert he0 using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hk i]
    have hcast := congrArg (algebraMap K ℂ) he0'
    simpa [map_sum, map_mul] using hcast
  have hindg := (Fintype.linearIndependent_iff.mp hind) (fun i => algebraMap K ℂ (a i))
    (by simpa [rC] using hrows) i
  exact (injective_iff_map_eq_zero (algebraMap K ℂ)).mp
    (algebraMap K ℂ).injective (a i) hindg

/-- Wrapper: rows of `L` (values in ℂ, actually in `K`) are `K`-independent
once they are ℂ-independent. -/
theorem intermediateField_row_indep (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) (ind : LinearIndependent ℂ L) :
    LinearIndependent K (fun i : σ => fun j : σ => (⟨L i j, hLK i j⟩ : K)) := by
  simpa using (row_indep_transfer (K := K) (Λ := fun i j => (⟨L i j, hLK i j⟩ : K))
    (by simpa using ind))

/-- Wrapper: the `K`-linear forms `x ↦ ∑ⱼ Lᵢⱼ xⱼ` on `K^σ` are
`K`-linearly independent once the rows are ℂ-independent. -/
theorem intermediateField_form_indep (K : IntermediateField ℚ ℂ) (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) (ind : LinearIndependent ℂ L) :
    LinearIndependent K (fun i : σ => kForm (fun j : σ => (⟨L i j, hLK i j⟩ : K))) := by
  simpa using (form_indep_transfer (K := K) (Λ := fun i j => (⟨L i j, hLK i j⟩ : K))
    (by simpa using ind))

end Transfer

end Submission.Subspace
