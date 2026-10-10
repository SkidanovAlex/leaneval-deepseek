import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.phi0_defs
import Submission.Work.SSGRoute.pt_char_pTorsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9b

/-- **The `p`-torsion of a level of degree divisible by `p` has `p` elements.**  If `p ∣ [L : k]`
then `H²(Gal(L/k), C_L)` is cyclic of order `[L : k]` (Hasse's fundamental class), so its
`p`-torsion subgroup has `p` elements. -/
theorem pTor_classLevel_card (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : Lvl k K Ω) (hp : p ∣ Module.finrank k ↥L.1) :
    Nat.card ↥(pTor p (ClassLevel (k := k) (K := K) L)) = p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- `Work.SSGRoute.pt_char_pTorsion` identifies the `p`-torsion of the level `H²(Gal(L/k), C_L)`
  -- as an additive subgroup `P` cut out by `p • v = 0` and additively isomorphic to `ZMod p`.
  obtain ⟨P, χ, hP, hχ⟩ := Work.SSGRoute.pt_char_pTorsion p k K ↥L.1 hp
  -- `P` is *the* `p`-torsion subgroup.
  have hPeq : P = pTor p (ClassLevel (k := k) (K := K) L) := by
    apply AddSubgroup.ext
    intro v
    rw [hP v]
    exact mem_pTor.symm
  -- hence it has `p` elements, being additively isomorphic to `ZMod p`.
  have hcard : Nat.card ↥P = p := by
    rw [Nat.card_congr (AddEquiv.ofBijective χ hχ).toEquiv, Nat.card_eq_fintype_card, ZMod.card]
  rw [← hPeq]
  exact hcard

end Work.SSGRoute.E9b
