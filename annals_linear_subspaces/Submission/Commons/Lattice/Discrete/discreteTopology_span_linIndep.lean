import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Order.CompletePartialOrder

open scoped BigOperators

noncomputable section

namespace Commons.Lattice.Discrete

/-- The linear map `(Fin k → ℝ) →ₗ[ℝ] E` sending the `i`-th standard basis vector to `v i`.
It is injective because the `v i` are `ℝ`-linearly independent. -/
private lemma linearCombination_injective {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n))
    (hind : LinearIndependent ℝ v) : Function.Injective (Fintype.linearCombination ℝ v) := by
  intro a b hab
  have hco : ∀ g : Fin k → ℝ, (∑ i, g i • v i) = 0 → ∀ i, g i = 0 :=
    (Fintype.linearIndependent_iff.mp hind)
  apply funext
  intro i
  have hsum : (∑ j : Fin k, (a j - b j) • v j) = 0 := by
    have : Fintype.linearCombination ℝ v (a - b) = 0 := by
      calc
        Fintype.linearCombination ℝ v (a - b) = Fintype.linearCombination ℝ v a - Fintype.linearCombination ℝ v b := by simp
        _ = 0 := by simp [hab]
    simpa [Fintype.linearCombination_apply, sub_smul] using this
  have hi := hco (a - b) hsum i
  exact sub_eq_zero.mp hi

/-- `F (basisFun i) = v i`. -/
private lemma linearCombination_apply_basisFun {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n))
    (i : Fin k) : Fintype.linearCombination ℝ v (Pi.basisFun ℝ (Fin k) i) = v i := by
  rw [Pi.basisFun_apply, Fintype.linearCombination_apply_single]
  simp

/-- `F` maps a `ℤ`-linear combination of the standard basis of `(Fin k → ℝ)` to the same
`ℤ`-linear combination of the `v i`. -/
private lemma linearCombination_apply_zsmul_sum {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) (m : Fin k → ℤ) :
    Fintype.linearCombination ℝ v (∑ i, (m i : ℤ) • (Pi.basisFun ℝ (Fin k) i))
      = ∑ i, (m i : ℤ) • v i := by
  calc
    Fintype.linearCombination ℝ v (∑ i, (m i : ℤ) • (Pi.basisFun ℝ (Fin k) i))
        = ∑ i, (m i : ℤ) • Fintype.linearCombination ℝ v (Pi.basisFun ℝ (Fin k) i) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [map_zsmul]
    _ = ∑ i, (m i : ℤ) • v i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [linearCombination_apply_basisFun v i]

/-- The image under `Fintype.linearCombination ℝ v` of the `ℤ`-span of the standard basis of
`(Fin k → ℝ)` equals the `ℤ`-span of the `v i`. -/
private lemma image_span_eq_span {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    (Fintype.linearCombination ℝ v) '' (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k))) : Set (Fin k → ℝ))
      = (Submodule.span ℤ (Set.range v) : Set (EuclideanSpace ℝ (Fin n))) := by
  ext z
  constructor
  · rintro ⟨c, hcD, hcz⟩
    rw [← hcz]
    refine (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := v)
      (x := Fintype.linearCombination ℝ v c)).2 ?_
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := Pi.basisFun ℝ (Fin k))
      (x := c)).1 hcD with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [← hm]
    exact (linearCombination_apply_zsmul_sum v m).symm
  · intro hzL
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := v) (x := z)).1 hzL with ⟨m, hm⟩
    let c : Fin k → ℝ := ∑ i, (m i : ℤ) • (Pi.basisFun ℝ (Fin k) i)
    refine ⟨c, ?_, ?_⟩
    · exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := Pi.basisFun ℝ (Fin k))
        (x := c)).2 ⟨m, rfl⟩
    · calc
        Fintype.linearCombination ℝ v c = Fintype.linearCombination ℝ v
            (∑ i, (m i : ℤ) • (Pi.basisFun ℝ (Fin k) i)) := by rfl
        _ = ∑ i, (m i : ℤ) • v i := by exact linearCombination_apply_zsmul_sum v m
        _ = z := hm

/- The Z-span of finitely many R-linearly-independent vectors in a Euclidean space is a
discrete lattice.  Mathlib-only statement: if `v : Fin k → EuclideanSpace ℝ (Fin n)` with
`LinearIndependent ℝ v` (the `v i` are R-independent), then the Z-submodule they generate has
the discrete topology.

PROOF ROUTE: view the R-linear map `F : (Fin k → ℝ) → EuclideanSpace ℝ (Fin n)`,
`F c := ∑ i, (c i) • v i`, which is injective by linear independence.  Restrict to
`ℤ^k = {c : Fin k → ℤ}`, a discrete space (finite product of discrete spaces).  Since F is an
injective continuous linear map between finite-dimensional spaces it is a homeomorphism onto
its image `F '' ℤ^k`, which equals the Z-span of the `v i`: concretely, build an R-linear
left-inverse `G` of `F` on the image (complete `v` to a basis and take dual functionals; or
use the standard finite-dimensional linear algebra fact that injective linear maps between
finite-dimensional spaces split), `G` is continuous and `G (F c) = c`, so the induced bijection
`ℤ^k ≃ ℤ-span` is a homeomorphism.  Since `ℤ^k` is discrete, the span is discrete; return the
`DiscreteTopology` instance for `Submodule.span ℤ (Set.range v)` (its subtype topology is the
subspace topology from the Euclidean space).

ALTERNATIVE ROUTE that may be simpler in Lean: prove directly that every element of the span
is isolated.  For `w = F c` (with `c : Fin k → ℤ`) use `LinearIndependent` to find
`δ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin k → ℝ)` with `δ (v i) = e i` (the standard basis of
`(Fin k → ℝ)`; exists by completing `v` to an R-basis, or via `LinearIndependent.linearCombination`
/ dual basis constructions in Mathlib).  Then for `z` in the span with `z = F c'`, `c' = δ z`
has integer coordinates when `z` is a lattice point, and small perturbations change `δ z`
continuously, so a small open ball around `w` meets the span only at `w`.
Notes: `sum_univ`, `Finset.univ`; membership in the span means `z = F c` for some
`c : Fin k → ℤ` (finite sums of integer multiples of the `v i`).
-/
theorem discreteTopology_span_linIndep {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n))
    (hind : LinearIndependent ℝ v) :
    DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ι := Fin k
  let D : Submodule ℤ (ι → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  have hD : IsDiscrete (D : Set (ι → ℝ)) := by
    apply (SetLike.isDiscrete_iff_discreteTopology (s := D)).2
    infer_instance
  have hFemb : Topology.IsClosedEmbedding (Fintype.linearCombination ℝ v) := by
    have hFker : LinearMap.ker (Fintype.linearCombination ℝ v) = ⊥ :=
      (LinearMap.ker_eq_bot).mpr (linearCombination_injective v hind)
    apply LinearMap.isClosedEmbedding_of_injective (𝕜 := ℝ) (E := ι → ℝ) (F := E)
    exact hFker
  have hImg : IsDiscrete (Fintype.linearCombination ℝ v '' (D : Set (ι → ℝ))) := by
    exact IsDiscrete.image hD hFemb.toIsEmbedding.toIsInducing
  have hEq : (Fintype.linearCombination ℝ v '' (D : Set (ι → ℝ)) : Set E)
      = (Submodule.span ℤ (Set.range v) : Set E) := by
    simpa [D, ι] using (image_span_eq_span v)
  have hSub : (Submodule.span ℤ (Set.range v) : Set E) ⊆
      (Fintype.linearCombination ℝ v '' (D : Set (ι → ℝ))) := by
    rw [hEq]
  have hL : IsDiscrete (Submodule.span ℤ (Set.range v) : Set E) :=
    IsDiscrete.mono hImg hSub
  exact (SetLike.isDiscrete_iff_discreteTopology (s := Submodule.span ℤ (Set.range v))).1 hL

end Commons.Lattice.Discrete