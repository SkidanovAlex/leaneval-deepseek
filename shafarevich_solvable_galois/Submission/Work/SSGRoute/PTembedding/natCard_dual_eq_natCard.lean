import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTembedding

/-- A module whose underlying type is finite is finitely generated: the whole
underlying set is a finite generating set. -/
private lemma module_finite_of_finite {K V : Type*} [Semiring K] [AddCommMonoid V]
    [Module K V] [Finite V] : Module.Finite K V := by
  rw [Module.finite_def, Submodule.fg_def]
  exact ⟨Set.univ, Set.finite_univ, Submodule.span_univ⟩

/-- Over a finite field `ZMod p`, a vector space and its linear dual have the same
cardinality (`Nat.card`, which is `0` for infinite types). -/
theorem natCard_dual_eq_natCard (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] : Nat.card (Module.Dual (ZMod p) V) = Nat.card V := by
  classical
  by_cases h : Module.Finite (ZMod p) V
  · -- Finite-dimensional case: a finite basis identifies `V` with its dual.
    haveI : Module.Free (ZMod p) V := Module.Free.of_divisionRing _ _
    exact (Nat.card_congr (Module.finBasis (ZMod p) V).toDualEquiv.toEquiv).symm
  · -- Infinite-dimensional case: both cardinalities are `0`.
    haveI hVinf : Infinite V := ⟨fun hfin => h (module_finite_of_finite (K := ZMod p))⟩
    haveI : Module.Free (ZMod p) V := Module.Free.of_divisionRing _ _
    haveI hDinf : Infinite (Module.Dual (ZMod p) V) := by
      rw [← not_finite_iff_infinite]
      intro hfin
      have hfin2 : Finite (Module.Dual (ZMod p) (Module.Dual (ZMod p) V)) :=
        Finite.of_injective (fun f => (f : Module.Dual (ZMod p) V → ZMod p))
          DFunLike.coe_injective
      exact hVinf.not_finite (Finite.of_injective (Module.Dual.eval (ZMod p) V)
        (Module.eval_apply_injective (ZMod p)))
    rw [Nat.card_eq_zero_of_infinite (α := V),
      Nat.card_eq_zero_of_infinite (α := Module.Dual (ZMod p) V)]

end Work.SSGRoute.PTembedding
