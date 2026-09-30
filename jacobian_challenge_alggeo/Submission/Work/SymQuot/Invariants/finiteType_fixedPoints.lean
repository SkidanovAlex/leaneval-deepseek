import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

/-!
# Invariants of a finite group action are of finite type (Hilbert--Noether)

Let `K` be a field, `B` a commutative `K`-algebra on which a finite group `G` acts by
`K`-algebra automorphisms, and suppose that `B` is a finitely generated `K`-algebra.  Then the
subalgebra `B^G ⊆ B` of `G`-invariant elements is again a finitely generated `K`-algebra.

This is the classical finiteness theorem for invariants of a finite group (Emmy Noether), in the
form needed for the quotient `X/G` of a scheme by a finite group.

The proof is the Artin--Tate lemma (`fg_of_fg_of_fg`):

* `B` is integral over `B^G` (`Algebra.IsInvariant.isIntegral`), because every `b : B` is a root
  of the monic polynomial `∏_{g ∈ G} (X - g • b)` with coefficients in `B^G`;
* hence, as `B` is finitely generated as a `K`-algebra and a fortiori as a `B^G`-algebra, `B` is
  a finite `B^G`-module (`Algebra.FiniteType.of_restrictScalars_finiteType` and
  `Algebra.IsIntegral.finite`);
* the Artin--Tate lemma then says that `B^G` is a finitely generated `K`-algebra, because `K` is
  a field (hence Noetherian) and `B` is finitely generated as a `K`-algebra.

We do not assume that `|G|` is invertible in `K`: no averaging is involved.
-/

namespace Work.SymQuot.Invariants

/-- The fixed subalgebra `B^G` of a `G`-invariant extension `B/K` is an invariant extension in the
sense of `Algebra.IsInvariant`: every element of `B` fixed by `G` lies (by definition) in `B^G`. -/
theorem fixedPointsSubalgebra_isInvariant {K B G : Type*} [CommSemiring K] [CommRing B]
    [Algebra K B] [Group G] [MulSemiringAction G B] [SMulCommClass G K B] :
    Algebra.IsInvariant (FixedPoints.subalgebra K B G) B G :=
  ⟨fun _ hb => ⟨⟨_, hb⟩, rfl⟩⟩

/-- **Hilbert--Noether finiteness theorem.** For a finite group `G` acting on a finitely generated
commutative `K`-algebra `B` by `K`-algebra automorphisms, the subalgebra `B^G` of invariants is a
finitely generated `K`-algebra. -/
theorem finiteType_fixedPoints {K B G : Type*} [Field K] [CommRing B]
    [Algebra K B] [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G K B]
    [Algebra.FiniteType K B] : Algebra.FiniteType K (FixedPoints.subalgebra K B G) := by
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra K B G) B G :=
    fixedPointsSubalgebra_isInvariant
  -- `B` is integral over `B^G` ...
  haveI : Algebra.IsIntegral (FixedPoints.subalgebra K B G) B :=
    Algebra.IsInvariant.isIntegral (A := FixedPoints.subalgebra K B G) (B := B) (G := G)
  -- ... and finitely generated as a `B^G`-algebra (from the `K`-generators, since `K ⊆ B^G`),
  -- hence a finite `B^G`-module.
  haveI : Algebra.FiniteType (FixedPoints.subalgebra K B G) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (FixedPoints.subalgebra K B G) B
  haveI : Module.Finite (FixedPoints.subalgebra K B G) B := Algebra.IsIntegral.finite
  -- Artin--Tate with `K ⊆ B^G ⊆ B`.
  exact ⟨fg_of_fg_of_fg K (FixedPoints.subalgebra K B G) B
    Algebra.FiniteType.out Module.Finite.fg_top Subtype.coe_injective⟩

end Work.SymQuot.Invariants
