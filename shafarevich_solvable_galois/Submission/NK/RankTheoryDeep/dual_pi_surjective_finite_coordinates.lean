import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Connected.Separation
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.RankTheoryDeep.exists_finset_support_of_dual_pi_of_cofinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Characters of a product with finitely many non-trivial coordinates

This file proves `NK.RankTheoryDeep.dual_pi_surjective_finite_coordinates`: if `S : Finset ι`
is a finite set of coordinates such that every coordinate *outside* `S` has trivial continuous
dual `Dual (A i) ℓ = Hom_cts(A i, ℤ_ℓ)`, then every continuous additive character of the product
`∏ᵢ Aᵢ` is the sum of its restrictions to the coordinates in `S`.  Equivalently the "sum of the
coordinate projections" map

  `∏_{i ∈ S} Dual (A i) ℓ ⟶ Dual (∏ᵢ A i)`,   `ψ ↦ ∑_{i ∈ S} ψ i ∘ proj_i`

is *surjective*.  (The dual of a product of compact groups is the direct sum of the duals of the
factors, when all but finitely many factors have trivial dual.)

The proof is the argument of `NK.RankTheoryDeep.exists_finset_support_of_dual_pi_of_cofinite`:
the difference of `χ : Dual (∏ A i) ℓ` and the sum of its coordinate components vanishes on every
coordinate subgroup, hence on the dense subgroup of finitely supported elements (a basic open
subset of a product constrains only finitely many coordinates), and `ℤ_ℓ` being Hausdorff we
conclude. -/

universe u

namespace NK.RankTheoryDeep

open NK.Reconstruct (Dual dualMap)

theorem dual_pi_surjective_finite_coordinates {ι : Type u} {A : ι → Type u} [DecidableEq ι]
    [∀ i, CommGroup (A i)] [∀ i, TopologicalSpace (A i)]
    {ℓ : ℕ} [Fact ℓ.Prime] (S : Finset ι)
    (hS : ∀ i ∉ S, Subsingleton (NK.Reconstruct.Dual (A i) ℓ)) :
    Function.Surjective (fun ψ : (i : {i // i ∈ S}) → NK.Reconstruct.Dual (A i) ℓ =>
      ∑ i : {i // i ∈ S}, (NK.Reconstruct.dualMap ℓ (Pi.evalMonoidHom A (i : ι))
        (continuous_apply (i : ι)) (ψ i) : NK.Reconstruct.Dual (∀ i, A i) ℓ)) := by
  classical
  intro χ
  -- The `i`-th coordinate of `χ` and its extension to the whole product.
  let χi : ∀ i, Dual (A i) ℓ := fun i =>
    dualMap ℓ (MonoidHom.mulSingle A i) (continuous_mulSingle i) χ
  let χc : ∀ i, Dual (∀ i, A i) ℓ := fun i =>
    dualMap ℓ (Pi.evalMonoidHom A i) (continuous_apply i) (χi i)
  refine ⟨fun i => χi (i : ι), ?_⟩
  change (∑ i : {i // i ∈ S}, χc (i : ι)) = χ
  have hkey : ∀ (i : ι) (z : ∀ j, A j),
      (χc i : Additive (∀ j, A j) →+ PadicInt ℓ) (Additive.ofMul z)
        = (χi i : Additive (A i) →+ PadicInt ℓ) (Additive.ofMul (z i)) :=
    fun i z => rfl
  have hkey2 : ∀ (i : ι) (a : A i),
      (χi i : Additive (A i) →+ PadicInt ℓ) (Additive.ofMul a)
        = (χ : Additive (∀ j, A j) →+ PadicInt ℓ)
            (Additive.ofMul (Pi.mulSingle (M := A) i a)) :=
    fun i a => rfl
  -- Coordinates outside `S` have trivial dual, so `χi i = 0` there.
  have hχi_zero : ∀ i, i ∉ S → ∀ a : A i,
      (χi i : Additive (A i) →+ PadicInt ℓ) (Additive.ofMul a) = 0 := by
    intro i hi a
    have h0 : χi i = (0 : Dual (A i) ℓ) :=
      @Subsingleton.elim (Dual (A i) ℓ) (hS i hi) _ _
    rw [h0]; rfl
  -- The difference `Ψ = χ - ∑_{i ∈ S} χc i`.
  let Ψ : Additive (∀ i, A i) →+ PadicInt ℓ :=
    (χ : Additive (∀ i, A i) →+ PadicInt ℓ)
      - ∑ i ∈ S, (χc i : Additive (∀ i, A i) →+ PadicInt ℓ)
  have hΨapply : ∀ y : Additive (∀ i, A i),
      Ψ y = (χ : Additive (∀ i, A i) →+ PadicInt ℓ) y
        - ∑ j ∈ S, (χc j : Additive (∀ i, A i) →+ PadicInt ℓ) y := by
    intro y
    rw [show Ψ = (χ : Additive (∀ i, A i) →+ PadicInt ℓ)
        - ∑ i ∈ S, (χc i : Additive (∀ i, A i) →+ PadicInt ℓ) from rfl]
    rw [AddMonoidHom.sub_apply, addHom_sum_apply]
  -- `Ψ` vanishes on every coordinate subgroup.
  have hcoord : ∀ (i : ι) (a : A i),
      Ψ (Additive.ofMul (Pi.mulSingle (M := A) i a)) = 0 := by
    intro i a
    rw [hΨapply]
    by_cases hi : i ∈ S
    · rw [Finset.sum_eq_single i]
      · rw [hkey i (Pi.mulSingle (M := A) i a), Pi.mulSingle_eq_same, hkey2 i a]
        exact sub_self _
      · intro j hj hji
        rw [hkey j (Pi.mulSingle (M := A) i a), Pi.mulSingle_eq_of_ne hji a]
        simp
      · intro hi'; exact absurd hi hi'
    · rw [Finset.sum_eq_zero]
      · rw [← hkey2 i a, hχi_zero i hi a, sub_zero]
      · intro j hj
        have hji : j ≠ i := fun he => hi (he ▸ hj)
        rw [hkey j (Pi.mulSingle (M := A) i a), Pi.mulSingle_eq_of_ne hji a]
        simp
  -- Hence, by additivity, on all finitely supported elements.
  have hvan : ∀ z : ∀ i, A i, {i | z i ≠ 1}.Finite → Ψ (Additive.ofMul z) = 0 := by
    intro z hz
    obtain ⟨T, hT⟩ := hz.exists_finset_coe
    have hz1 : ∀ i ∉ T, z i = 1 := by
      intro i hi
      by_contra hc
      have : i ∈ (T : Set ι) := by rw [hT]; exact hc
      exact hi (by simpa using this)
    have hprod : (∏ i ∈ T, Pi.mulSingle (M := A) i (z i)) = z :=
      prod_mulSingle_of_eq_one_off T z hz1
    have hsum : (∑ i ∈ T, Additive.ofMul (Pi.mulSingle (M := A) i (z i)))
        = Additive.ofMul z := by
      rw [← ofMul_prod, hprod]
    rw [← hsum, map_sum]
    exact Finset.sum_eq_zero (fun i _ => hcoord i (z i))
  -- `Ψ` is continuous, so it vanishes everywhere: finitely supported elements are dense.
  have hcont : Continuous (fun z : ∀ i, A i => Ψ (Additive.ofMul z)) := by
    have h1 : Continuous (fun z : ∀ i, A i =>
        (χ : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z)) := χ.2
    have h2 : Continuous (fun z : ∀ i, A i =>
        ∑ j ∈ S, (χc j : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z)) := by
      apply continuous_finsetSum
      intro j hj
      have hjj : (fun z : ∀ i, A i => (χc j : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z))
          = fun z => (χi j : Additive (A j) →+ PadicInt ℓ) (Additive.ofMul (z j)) := by
        funext z
        exact hkey j z
      rw [hjj]
      exact (χi j).2.comp (continuous_apply j)
    have hfun : (fun z : ∀ i, A i => Ψ (Additive.ofMul z))
        = fun z => (χ : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z)
            - ∑ j ∈ S, (χc j : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z) := by
      funext z
      exact hΨapply (Additive.ofMul z)
    rw [hfun]
    exact h1.sub h2
  have hmain : ∀ z : ∀ i, A i, Ψ (Additive.ofMul z) = 0 := by
    have heq := Continuous.ext_on (dense_setOf_finite_ne_one (X := A)) hcont continuous_const
      (fun z hz => hvan z hz)
    intro z
    exact congrFun heq z
  have hzero : ∀ z : ∀ i, A i,
      (χ : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z)
        = ∑ j ∈ S, (χc j : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z) := by
    intro z
    have h := hmain z
    rw [hΨapply] at h
    exact sub_eq_zero.mp h
  -- Conclusion: `∑_{i ∈ S} χc i = χ`.
  have hfin : (∑ i ∈ S, χc i) = χ := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro y
    have hy : y = Additive.ofMul (Additive.toMul y) := rfl
    rw [hy]
    rw [show (((∑ i ∈ S, χc i) : Dual (∀ i, A i) ℓ) : Additive (∀ i, A i) →+ PadicInt ℓ)
        = ∑ i ∈ S, (χc i : Additive (∀ i, A i) →+ PadicInt ℓ) from
          map_sum (AddSubgroup.subtype (NK.Reconstruct.dualCarrier (∀ i, A i) ℓ)) χc S]
    rw [addHom_sum_apply]
    exact (hzero (Additive.toMul y)).symm
  rw [show (∑ i : {i // i ∈ S}, χc (i : ι)) = ∑ i ∈ S, χc i from by
    rw [Finset.univ_eq_attach, Finset.sum_attach]]
  rw [hfin]

end NK.RankTheoryDeep
