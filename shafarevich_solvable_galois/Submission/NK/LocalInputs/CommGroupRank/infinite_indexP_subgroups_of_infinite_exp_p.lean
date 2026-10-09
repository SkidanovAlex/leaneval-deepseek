import Mathlib
import Submission.NK.ProfiniteP.LinearAlgebra.natCard_indexP_submodule_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Infinitely many index-`p` subgroups in an infinite group of exponent `p`

Let `C` be an infinite commutative group all of whose elements satisfy `c ^ p = 1`, with `p`
prime.  Then `C` is an elementary abelian `p`-group, i.e. a vector space over `𝔽_p = ZMod p`,
and a subgroup of index `p` is exactly a *hyperplane* (codimension-one subspace).  Since `C` is
infinite, this vector space is infinite dimensional, hence has infinitely many hyperplanes (the
kernels of the coordinate functionals of a basis), so there are infinitely many index-`p`
subgroups.

The additive/vector-space form of the statement is
`infinite_indexP_submodule_of_infinite`: an infinite `ZMod p`-module has infinitely many
submodules of index `p`.  The passage between `Subgroup C` and submodules of `Additive C` is
the order isomorphism `Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)`, under
which the subgroup index is preserved (`Subgroup.index_toAddSubgroup`).
-/

namespace NK.LocalInputs.CommGroupRank

open scoped Classical

universe u

/-- **An infinite `𝔽_p`-vector space (i.e. `ZMod p`-module) has infinitely many submodules of
index `p`.**

A subgroup of index `p` of a `ZMod p`-module is a hyperplane.  Since the module is infinite, it
is infinite dimensional, so its `ofVectorSpace` basis is infinite, and the kernels of the
coordinate functionals of distinct basis vectors are distinct submodules of index `p`. -/
lemma infinite_indexP_submodule_of_infinite {p : ℕ} (hp : p.Prime) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (hV : Infinite V) :
    Infinite {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p} := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Infinite V := hV
  -- An infinite module over the finite field `𝔽_p` is not finite dimensional.
  have hnotfin : ¬ FiniteDimensional (ZMod p) V := by
    intro hdim
    haveI hfin : Module.Finite (ZMod p) V := hdim
    have hcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rw [Nat.card_zmod] at h
      exact h
    have hne : Nat.card V ≠ 0 := by rw [hcard]; exact pow_ne_zero _ hp.ne_zero
    exact hne (Nat.card_eq_zero_of_infinite (α := V))
  have hrank : Cardinal.aleph0 ≤ Module.rank (ZMod p) V := by
    rw [← not_lt]
    intro hlt
    exact hnotfin ((Module.rank_lt_aleph0_iff).mp hlt)
  -- Hence the `ofVectorSpace` basis is indexed by an infinite type.
  haveI hInf : Infinite ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Finite ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V) := hfin
    exact hnotfin (Module.Finite.of_basis (Module.Basis.ofVectorSpace (ZMod p) V))
  -- The kernel of a coordinate functional is of index `p`.
  have hindex : ∀ i : ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V),
      (LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord i)).toAddSubgroup.index = p := by
    intro i
    have hsurj : Function.Surjective ((Module.Basis.ofVectorSpace (ZMod p) V).coord i) := by
      intro c
      refine ⟨c • (Module.Basis.ofVectorSpace (ZMod p) V) i, ?_⟩
      rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    have e := LinearMap.quotKerEquivOfSurjective
      ((Module.Basis.ofVectorSpace (ZMod p) V).coord i) hsurj
    rw [show (LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord i)).toAddSubgroup.index
          = Nat.card (V ⧸ LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord i)) from rfl,
      Nat.card_congr e.toEquiv, Nat.card_zmod]
  -- Distinct basis vectors give distinct coordinate functionals, hence distinct kernels.
  have hinj : Function.Injective
      (fun i : ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V) =>
        (⟨LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord i), hindex i⟩ :
          {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p})) := by
    intro i j hij
    by_contra hne
    have hker : LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord i)
        = LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord j) :=
      congrArg Subtype.val hij
    have hzero : (Module.Basis.ofVectorSpace (ZMod p) V).coord i
        ((Module.Basis.ofVectorSpace (ZMod p) V) j) = 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne]
    have hmem : (Module.Basis.ofVectorSpace (ZMod p) V) j
        ∈ LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord i) :=
      (LinearMap.mem_ker).mpr hzero
    rw [hker, LinearMap.mem_ker] at hmem
    have hone : (Module.Basis.ofVectorSpace (ZMod p) V).coord j
        ((Module.Basis.ofVectorSpace (ZMod p) V) j) = 1 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    rw [hone] at hmem
    exact one_ne_zero hmem
  exact Infinite.of_injective _ hinj

/-- **An infinite commutative group of exponent `p` has infinitely many subgroups of index `p`.**

Such a group is an `𝔽_p`-vector space, and its index-`p` subgroups are the hyperplanes; an
infinite vector space over a finite field has infinitely many of them
(`infinite_indexP_submodule_of_infinite`). -/
theorem infinite_indexP_subgroups_of_infinite_exp_p {C : Type*} [CommGroup C] {p : ℕ} (hp : p.Prime)
    (hC : Infinite C) (hexp : ∀ c : C, c ^ p = 1) :
    Infinite {K : Subgroup C // K.index = p} := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `C` is a `ZMod p`-module through its additive group.
  have hmod : Module (ZMod p) (Additive C) :=
    AddCommGroup.zmodModule (fun x => by
      apply Additive.toMul.injective
      simpa using hexp (Additive.toMul x))
  have hinC : Infinite (Additive C) := Infinite.of_injective Additive.ofMul Additive.ofMul.injective
  have hinf : Infinite {W : Submodule (ZMod p) (Additive C) // W.toAddSubgroup.index = p} :=
    infinite_indexP_submodule_of_infinite hp (V := Additive C) hinC
  -- Subgroups of `C` correspond to submodules of `Additive C`, preserving the index.
  let e : Subgroup C ≃o Submodule (ZMod p) (Additive C) :=
    (Subgroup.toAddSubgroup).trans (AddSubgroup.toZModSubmodule p)
  have he : ∀ K : Subgroup C, (e K).toAddSubgroup.index = K.index := by
    intro K
    show (AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup K)).toAddSubgroup.index = K.index
    rw [AddSubgroup.toZModSubmodule_toAddSubgroup, Subgroup.index_toAddSubgroup]
  exact Infinite.of_injective
    (fun W : {W : Submodule (ZMod p) (Additive C) // W.toAddSubgroup.index = p} =>
      (⟨e.symm W.1, by rw [← he (e.symm W.1), e.apply_symm_apply]; exact W.2⟩ :
        {K : Subgroup C // K.index = p}))
    (fun W W' h => Subtype.ext (e.symm.injective (Subtype.ext_iff.mp h)))

end NK.LocalInputs.CommGroupRank
