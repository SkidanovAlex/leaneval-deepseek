import Mathlib
import Submission.Work.ORFP2.augIdeal_freeGroup_injective

set_option autoImplicit false

open MonoidAlgebra

namespace Work.ORFP2

/-- Injectivity of the `linearCombination` form of the free-group statement: the map
`c ↦ ∑_a c_a (x_a - 1)` on `K[F(α)]` has trivial kernel.  This is just a rephrasing of
`augIdeal_freeGroup_injective` in terms of `Finsupp.linearCombination`. -/
private lemma freeGroup_linearCombination_injective (K : Type*) [CommRing K]
    (α : Type*) [DecidableEq α] :
    Function.Injective (Finsupp.linearCombination (MonoidAlgebra K (FreeGroup α))
      (fun a : α => MonoidAlgebra.single (FreeGroup.of a) (1 : K) - 1)) := by
  intro c d hcd
  apply augIdeal_freeGroup_injective K α
  simpa only [Finsupp.linearCombination_apply, smul_eq_mul] using hcd

/-- The transport of the `linearCombination` map along the algebra equivalence
`MonoidAlgebra.domCongr K K e.symm : K[H] ≃ₐ[K] K[F(ι)]`.  Applying this equivalence to
`∑_i c_i (single (e (x_i)) 1 - 1)` gives `∑_i E(c_i) (single (x_i) 1 - 1)`, i.e. the free-group
`linearCombination` applied to the coefficient-wise image `c.mapRange E`. -/
private lemma domCongr_linearCombination {ι : Type*} [DecidableEq ι]
    {H : Type*} [Group H] (K : Type*) [CommRing K] (e : FreeGroup ι ≃* H)
    (c : ι →₀ MonoidAlgebra K H) :
    MonoidAlgebra.domCongr K K e.symm
      (Finsupp.linearCombination (MonoidAlgebra K H)
        (fun i : ι => MonoidAlgebra.single (e (FreeGroup.of i)) (1 : K) - 1) c)
      = Finsupp.linearCombination (MonoidAlgebra K (FreeGroup ι))
        (fun i : ι => MonoidAlgebra.single (FreeGroup.of i) (1 : K) - 1)
        (c.mapRange (MonoidAlgebra.domCongr K K e.symm) (map_zero _)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, map_add, hf, hg,
        Finsupp.mapRange_add (fun x y => map_add _ x y), map_add]
  | single i b =>
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
        Finsupp.mapRange_single,
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      rw [smul_eq_mul, smul_eq_mul, map_mul, map_sub, map_one,
        MonoidAlgebra.domCongr_single, MulEquiv.symm_apply_apply, MonoidAlgebra.one_def]

/-- **The augmentation ideal of `K[H]` is free on `{e(x_i) - 1}` for any group `H` isomorphic to a
free group `F(ι)`.**  The `K[H]`-linear map `c ↦ ∑_i c_i (single (e (x_i)) 1 - 1)` is injective. -/
theorem linearCombination_freeBasis_injective {ι : Type*} [DecidableEq ι]
    {H : Type*} [Group H] (K : Type*) [CommRing K] (e : FreeGroup ι ≃* H) :
    Function.Injective (Finsupp.linearCombination (MonoidAlgebra K H)
      (fun i : ι => MonoidAlgebra.single (e (FreeGroup.of i)) (1 : K) - 1)) := by
  intro c d hcd
  have h := congrArg (⇑(MonoidAlgebra.domCongr K K e.symm)) hcd
  rw [domCongr_linearCombination K e c, domCongr_linearCombination K e d] at h
  exact Finsupp.mapRange_injective _ (map_zero _) (AlgEquiv.injective _)
    (freeGroup_linearCombination_injective K ι h)

end Work.ORFP2
