import Mathlib
import Submission.NK.ProfiniteP.Frattini
import Submission.NK.ProfiniteP.LinearAlgebra.natCard_submodule_finrank_quotient_eq_one

namespace NK.ProfiniteP.LinearAlgebra

/-- The number of subgroups of index `p` of an `𝔽_p`-vector space `V` is
`(p ^ dim V - 1) / (p - 1)` : the number of hyperplanes (codimension-one subspaces) of `V`.

Since `𝔽_p` is a field, every additive subgroup of index `p` is in fact a submodule
(`V / W ≅ 𝔽_p`), and conversely.  For finite-dimensional `V` we compare with
`natCard_submodule_finrank_quotient_eq_one`, using `W.toAddSubgroup.index = |V ⧸ W| =
p ^ finrank (V ⧸ W)`.  In infinite dimension both sides are `0`: the right-hand side
because `finrank` of an infinite-dimensional space is `0`, the left-hand side because
an infinite-dimensional space has infinitely many hyperplanes (the kernels of the
coordinate functionals of a basis). -/
theorem natCard_indexP_submodule_general {p : ℕ} [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] :
    Nat.card {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p} =
      (p ^ Module.finrank (ZMod p) V - 1) / (p - 1) := by
  have hp : p.Prime := Fact.out
  by_cases hdim : FiniteDimensional (ZMod p) V
  · -- Finite-dimensional case: index `p` means quotient of dimension one.
    haveI : FiniteDimensional (ZMod p) V := hdim
    have hoff : ∀ W : Submodule (ZMod p) V,
        W.toAddSubgroup.index = p ↔ Module.finrank (ZMod p) (V ⧸ W) = 1 := by
      intro W
      haveI : Module.Finite (ZMod p) (V ⧸ W) := inferInstance
      have hcard : W.toAddSubgroup.index = p ^ Module.finrank (ZMod p) (V ⧸ W) := by
        rw [show W.toAddSubgroup.index = Nat.card (V ⧸ W) from rfl,
          Module.natCard_eq_pow_finrank (K := ZMod p) (V := V ⧸ W), Nat.card_zmod]
      constructor
      · intro h
        have : p ^ Module.finrank (ZMod p) (V ⧸ W) = p ^ 1 := by rw [← hcard, h, pow_one]
        exact Nat.pow_right_injective hp.two_le this
      · intro h
        rw [hcard, h, pow_one]
    have heq : Nat.card {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p}
        = Nat.card {W : Submodule (ZMod p) V // Module.finrank (ZMod p) (V ⧸ W) = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight hoff)
    rw [heq]
    exact natCard_submodule_finrank_quotient_eq_one
  · -- Infinite-dimensional case: `finrank` is `0` and there are infinitely many hyperplanes.
    have hrank : Cardinal.aleph0 ≤ Module.rank (ZMod p) V := by
      rw [← not_lt]
      intro hlt
      exact hdim ((Module.rank_lt_aleph0_iff).mp hlt)
    haveI hInf : Infinite ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V) := by
      rw [← not_finite_iff_infinite]
      intro hfin
      haveI : Finite ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V) := hfin
      exact hdim (Module.Finite.of_basis (Module.Basis.ofVectorSpace (ZMod p) V))
    have hfinrank : Module.finrank (ZMod p) V = 0 :=
      (Cardinal.toNat_eq_zero).mpr (Or.inr hrank)
    -- the kernel of a coordinate functional has index `p`
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
    -- distinct basis vectors give distinct kernels, hence infinitely many hyperplanes
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
    haveI : Infinite {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p} :=
      Infinite.of_injective
        (fun i : ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V) =>
          (⟨LinearMap.ker ((Module.Basis.ofVectorSpace (ZMod p) V).coord i), hindex i⟩ :
            {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p}))
        hinj
    rw [Nat.card_eq_zero_of_infinite, hfinrank]
    simp

end NK.ProfiniteP.LinearAlgebra
