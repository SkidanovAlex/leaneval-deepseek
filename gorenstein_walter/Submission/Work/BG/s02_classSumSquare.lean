import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge

/-!
# BG Lemma 2.2-a: the class-sum square identity

This file proves `Work.BG.ClassSumSquareProp`, the "pure" half of Bender–Glauberman
Lemma 2.2 (p. 205), which reads: for a finite group `K`, a conjugation-invariant subset
`X ⊆ K` (as a `Finset`) and `θ ∈ ±Irr(K)`,

`θ(1) · Σ_{x,y ∈ X} θ(xy) = (Σ_{x ∈ X} θ(x))²`.

The mathematics is the standard central-character argument: `z := Σ_{x ∈ X} x` is an element
of the centre of the group algebra `ℂ[K]` (this is exactly what conjugation-invariance of `X`
buys), so by Schur's lemma it acts on an irreducible module `V` with character `θ` as a scalar
`c`.  Taking traces of `ρ(z)` and of `ρ(z)²` gives

`Σ_{x ∈ X} θ(x) = c · θ(1)`,  `Σ_{x,y ∈ X} θ(xy) = c² · θ(1)`,

and eliminates `c`.  (Equivalently: `X` is a union of conjugacy classes and the corresponding
sum of class sums acts by the sum of central characters; we avoid the class decomposition.)

The route follows the observation in `OddOrder.RepresentationTheory` that central elements of
`ℂ[K]` act as scalars on irreducible representations
(`exists_central_scalar_asAlgebraHom`); the new ingredients are the centrality of the sum over
a conjugation-invariant *finset* (the library's `sum_ite_mem_center` is stated for a predicate
on the whole group) and the two trace evaluations.

## Main result

* `Work.BG.s02_classSumSquare` — `Work.BG.ClassSumSquareProp`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {K V : Type}

/-! ## Helper lemmas -/

/-- **The sum `Σ_{x ∈ X} x` of a conjugation-invariant finset is central in the group algebra.**

This is the finset form of `OddOrder.GroupTheory.CenterClassSum.sum_ite_mem_center`. -/
theorem finset_sum_single_mem_center [Group K] [Fintype K] (X : Finset K)
    (hX : ∀ g x : K, x ∈ X → g * x * g⁻¹ ∈ X) :
    (∑ x ∈ X, MonoidAlgebra.single x (1 : ℂ)) ∈
      Subalgebra.center ℂ (MonoidAlgebra ℂ K) := by
  classical
  have hS : ∀ u x : K, (u * x * u⁻¹ ∈ X) ↔ (x ∈ X) := by
    intro u x
    constructor
    · intro h
      have := hX u⁻¹ (u * x * u⁻¹) h
      rwa [show u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹ = x by group] at this
    · exact hX u x
  have h := OddOrder.GroupTheory.CenterClassSum.sum_ite_mem_center (k := ℂ) (G := K)
    (fun x => x ∈ X) hS
  have heq : (∑ g : K, if g ∈ X then MonoidAlgebra.of ℂ K g else 0)
      = ∑ x ∈ X, MonoidAlgebra.single x (1 : ℂ) := by
    rw [Finset.sum_congr rfl (fun g _ => by rw [MonoidAlgebra.of_apply])]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rwa [heq] at h

/-- The group-algebra element `Σ_{x ∈ X} x` acts on a representation as `Σ_{x ∈ X} ρ x`. -/
theorem asAlgebraHom_finset_sum_single [Group K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V) (X : Finset K) :
    ρ.asAlgebraHom (∑ x ∈ X, MonoidAlgebra.single x (1 : ℂ)) = ∑ x ∈ X, ρ x := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← MonoidAlgebra.of_apply, Representation.asAlgebraHom_of]

/-- The trace of a finite sum of endomorphisms is the sum of the traces; in particular
`trace (Σ_{x ∈ X} ρ x) = Σ_{x ∈ X} ρ.character x`. -/
theorem trace_finset_sum_representation [Group K] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ K V) (X : Finset K) :
    LinearMap.trace ℂ V (∑ x ∈ X, ρ x) = ∑ x ∈ X, ρ.character x := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => rfl

/-- The square of `Σ_{x ∈ X} x` in the group algebra, expanded. -/
theorem finset_sum_single_mul [Group K] (X : Finset K) :
    (∑ x ∈ X, MonoidAlgebra.single x (1 : ℂ)) * (∑ y ∈ X, MonoidAlgebra.single y (1 : ℂ))
      = ∑ x ∈ X, ∑ y ∈ X, MonoidAlgebra.single (x * y) (1 : ℂ) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [MonoidAlgebra.single_mul_single, mul_one]

/-! ## The main result -/

/-- **BG Lemma 2.2-a (pure form).**  For a conjugation-invariant `Finset` `X` of a finite group
`K` and `θ ∈ ±Irr(K)`, the sum of `θ` over the products of two elements of `X`, weighted by
`θ(1)`, is the square of the sum of `θ` over `X`.

The proof is the central-character argument described in the module docstring. -/
theorem s02_classSumSquare : Work.BG.ClassSumSquareProp := by
  intro K _ _ X hX θ hθ
  classical
  -- It suffices to treat irreducible `θ`, since the identity is invariant under `θ ↦ -θ`.
  have key : ∀ θ : ClassFunction K ℂ, IsIrreducibleCharacter θ →
      θ 1 * ∑ x ∈ X, ∑ y ∈ X, θ (x * y) = (∑ x ∈ X, θ x) ^ 2 := by
    intro θ hθ
    obtain ⟨V, _, _, _, ρ, hρ, hθchar⟩ := hθ
    have : Representation.IsIrreducible ρ := hρ
    -- `z = Σ_{x ∈ X} x ∈ ℂ[K]` is central.
    set z : MonoidAlgebra ℂ K := ∑ x ∈ X, MonoidAlgebra.single x (1 : ℂ) with hz
    have hzcenter : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ K) := by
      rw [hz]; exact finset_sum_single_mem_center X hX
    -- Schur: `z` acts on the irreducible module as a scalar `c`.
    obtain ⟨c, hc⟩ :=
      OddOrder.RepresentationTheory.exists_central_scalar_asAlgebraHom ρ hzcenter
    -- Trace of `ρ z`: `c · θ(1)`; trace of `ρ (z * z)`: `c² · θ(1)`.
    have ht1 : LinearMap.trace ℂ V (ρ.asAlgebraHom z) = c * (Module.finrank ℂ V : ℂ) := by
      rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul]
    have hzz : z * z = ∑ x ∈ X, ∑ y ∈ X, MonoidAlgebra.single (x * y) (1 : ℂ) := by
      rw [hz]; exact finset_sum_single_mul X
    have ht2 : LinearMap.trace ℂ V (ρ.asAlgebraHom (z * z)) =
        (c * c) * (Module.finrank ℂ V : ℂ) := by
      rw [map_mul, hc, smul_mul_smul_comm, Module.End.mul_eq_comp, LinearMap.id_comp,
        map_smul, LinearMap.trace_id, smul_eq_mul]
    -- The same traces computed from the character values.
    have hA : ρ.asAlgebraHom z = ∑ x ∈ X, ρ x := by
      rw [hz]; exact asAlgebraHom_finset_sum_single ρ X
    have hS : LinearMap.trace ℂ V (ρ.asAlgebraHom z) = ∑ x ∈ X, θ x := by
      rw [hA, trace_finset_sum_representation ρ X]
      exact Finset.sum_congr rfl fun x _ => (congrFun hθchar x).symm
    have hB : ρ.asAlgebraHom (z * z) = ∑ x ∈ X, ∑ y ∈ X, ρ (x * y) := by
      rw [hzz, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← MonoidAlgebra.of_apply, Representation.asAlgebraHom_of]
    have hT : LinearMap.trace ℂ V (ρ.asAlgebraHom (z * z)) = ∑ x ∈ X, ∑ y ∈ X, θ (x * y) := by
      rw [hB, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      exact (congrFun hθchar (x * y)).symm
    have hfrd : (Module.finrank ℂ V : ℂ) = θ 1 := by
      rw [← Representation.char_one ρ]
      exact (congrFun hθchar 1).symm
    have hT' : (∑ x ∈ X, ∑ y ∈ X, θ (x * y)) = c ^ 2 * θ 1 := by
      rw [← hT, ht2, hfrd]; ring
    have hS' : (∑ x ∈ X, θ x) = c * θ 1 := by
      rw [← hS, ht1, hfrd]
    rw [hT', hS']
    ring
  rcases hθ with h | h
  · exact key θ h
  · -- `-θ` irreducible: the identity is invariant under global negation.
    have h' := key (-θ) h
    have h'' : -(θ 1) * (-(∑ x ∈ X, ∑ y ∈ X, θ (x * y))) = (-(∑ x ∈ X, θ x)) ^ 2 := by
      simpa only [ClassFunction.neg_apply, Finset.sum_neg_distrib] using h'
    calc θ 1 * (∑ x ∈ X, ∑ y ∈ X, θ (x * y))
        = -(θ 1) * (-(∑ x ∈ X, ∑ y ∈ X, θ (x * y))) := by ring
      _ = (-(∑ x ∈ X, θ x)) ^ 2 := h''
      _ = (∑ x ∈ X, θ x) ^ 2 := by ring

end Work.BG
