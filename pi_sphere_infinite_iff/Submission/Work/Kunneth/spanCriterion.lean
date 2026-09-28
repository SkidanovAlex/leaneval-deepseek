import Mathlib
import Submission.Work.Cohomology.KroneckerH

/-!
# A criterion for three cohomology classes to span `Hⁿ`

Let `X` be a simplicial set for which the Kronecker pairing
`kronH : Hⁿ(X;ℤ) →ₗ (Hₙ(X;ℤ) →ₗ ℤ)` is injective (it is bijective as soon as the homology of `X`
is free, `Work.Cohomology.kronH_isIso`).  If `x₀ x₁ x₂ ∈ Hⁿ(X;ℤ)` and `z₀ z₁ z₂ ∈ Hₙ(X;ℤ)` are
such that

* the homology classes `z₀ z₁ z₂` span `Hₙ(X;ℤ)`, and
* the `3 × 3` pairing matrix `M_{ij} = ⟨x_i, z_j⟩` is invertible over `ℤ` (an explicit left
  inverse `d` is given: `∑_k d_{ik} M_{kj} = δ_{ij}`),

then `x₀ x₁ x₂` span `Hⁿ(X;ℤ)`.

Indeed, for any `y ∈ Hⁿ(X;ℤ)`, the linear functional `kronH y` agrees with the combination
`∑_i (∑_j ⟨y, z_j⟩ d_{ji}) ⟨x_i, ·⟩` on the spanning family `z₀ z₁ z₂`, hence everywhere;
injectivity of `kronH` then writes `y` as a `ℤ`-combination of `x₀ x₁ x₂`.

This is the algebraic core of the spanning statement `H⁴(ℂP² × ℂP²; ℤ) = ℤ⟨a², ab, b²⟩` (item 4 of
the Künneth subproject), where the `z_j` are the homology cross products of generators of
`H_*(ℂP²)`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Kunneth

/-- **Spanning criterion.**  Three cohomology classes pair unimodularly with a spanning family of
homology classes, so they span `Hⁿ(X;ℤ)`. -/
theorem spanCriterion (X : SSet) (n : ℕ)
    (hkr : Function.Injective (Work.Cohomology.kronH ℤ X n))
    (x : Fin 3 → ↥((Work.Cohomology.cochainC ℤ X).homology n))
    (z : Fin 3 → ↥((Work.Cohomology.chainC ℤ X).homology n))
    (hz : Submodule.span ℤ (Set.range z) = ⊤)
    (d : Fin 3 → Fin 3 → ℤ)
    (hd : ∀ i j, ∑ k, d i k * (Work.Cohomology.kronH ℤ X n (x k)) (z j)
      = if i = j then 1 else 0) :
    Submodule.span ℤ (Set.range x) = ⊤ := by
  -- two linear functionals on `Hₙ` agreeing on `z` agree everywhere
  have hspan : ∀ (g g' : ↥((Work.Cohomology.chainC ℤ X).homology n) →ₗ[ℤ] ℤ),
      (∀ j : Fin 3, g (z j) = g' (z j)) → g = g' := by
    intro g g' h
    have hle : (⊤ : Submodule ℤ ↥((Work.Cohomology.chainC ℤ X).homology n)) ≤ (g - g').ker := by
      rw [← hz]
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (h j))
    exact LinearMap.ext fun w => sub_eq_zero.mp (LinearMap.mem_ker.mp (hle trivial))
  rw [Submodule.eq_top_iff']
  intro y
  set a : Fin 3 → ℤ := fun i => ∑ j, (Work.Cohomology.kronH ℤ X n y) (z j) * d j i with ha
  have hkey : Work.Cohomology.kronH ℤ X n y
      = ∑ k : Fin 3, a k • Work.Cohomology.kronH ℤ X n (x k) := by
    refine hspan _ _ fun j => ?_
    have h1 : (∑ k : Fin 3, a k • Work.Cohomology.kronH ℤ X n (x k)) (z j)
        = ∑ k : Fin 3, a k * (Work.Cohomology.kronH ℤ X n (x k)) (z j) := by
      rw [LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [LinearMap.smul_apply, smul_eq_mul]
    rw [h1]
    have h2 : ∀ i : Fin 3, a i * (Work.Cohomology.kronH ℤ X n (x i)) (z j)
        = ∑ j' : Fin 3, (Work.Cohomology.kronH ℤ X n y) (z j')
            * (d j' i * (Work.Cohomology.kronH ℤ X n (x i)) (z j)) := by
      intro i
      rw [ha]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j' _ => by ring
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    rw [Finset.sum_comm]
    have h3 : ∀ j' : Fin 3, (∑ i : Fin 3, (Work.Cohomology.kronH ℤ X n y) (z j')
          * (d j' i * (Work.Cohomology.kronH ℤ X n (x i)) (z j)))
        = (Work.Cohomology.kronH ℤ X n y) (z j') * (if j' = j then 1 else 0) := by
      intro j'
      rw [← Finset.mul_sum]
      congr 1
      rw [← hd j' j]
    rw [Finset.sum_congr rfl fun j' _ => h3 j']
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      rw [if_neg hj', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hy : y = ∑ k : Fin 3, a k • x k := by
    apply hkr
    rw [hkey, map_sum]
    exact Finset.sum_congr rfl fun k _ => by
      simpa using (Work.Cohomology.kronH ℤ X n).map_smul' (a k) (x k)
  rw [hy]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← int_smul_eq_zsmul
    (inferInstance : Module ℤ ↥((Work.Cohomology.cochainC ℤ X).homology n)) (a k) (x k)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

end Work.Kunneth
