import Mathlib
import Submission.Work.QuadraticFields.RankTwo

/-!
# `rankTwo` of a multiplicative `𝔽₂`-module

The `2`-rank of a commutative group `A` is `dim_{𝔽₂} (A ⧸ A²)`, computed in `RankTwo.lean` as
`Module.finrank (ZMod 2) (ModN (Additive A) 2)`, where `ModN G n` is the quotient of `G` by the
multiples of `n`.

Here we record the basic consistency fact that this construction returns the obvious answer on an
elementary abelian `2`-group presented multiplicatively: for an additive `ZMod 2`-module `V`, the
multiplicative group `Multiplicative V` has `2`-rank `dim_{𝔽₂} V`.

The reason is that `Additive (Multiplicative V)` is definitionally `V`, and the subgroup `2 • ⊤`
of `V` is trivial because `V` is a module over `ZMod 2` (`2 • x = (2 : ZMod 2) • x = 0`).
Hence the quotient map `V → ModN V 2 = V ⧸ 2V` is the identity, and it is `ZMod 2`-linear by the
universal property `ModN.liftEquiv'` of `ModN`; being bijective it is a linear equivalence.
-/

namespace Work.QuadraticFields

theorem rankTwo_multiplicative_finrank (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] : rankTwo (Multiplicative V) = Module.finrank (ZMod 2) V := by
  -- in a `ZMod 2`-module the natural number `2` acts as `0`
  have htwo : ∀ g : V, (2 : ℕ) • g = 0 := by
    intro g
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 g]
    rw [show ((2 : ℕ) : ZMod 2) = 0 from by decide, zero_smul]
  -- the projection `V → V ⧸ 2V` is `ZMod 2`-linear, by the universal property of `ModN`
  let f : ModN V 2 →ₗ[ZMod 2] V :=
    (ModN.liftEquiv' (G := V) (H := V) (n := 2)).symm ⟨AddMonoidHom.id V, htwo⟩
  have hf : ∀ x : V, f (ModN.mkQ 2 x) = x := fun _ => rfl
  -- `f` is a two-sided inverse of the quotient map `ModN.mkQ 2`
  have hgf : ∀ y : ModN V 2, ModN.mkQ 2 (f y) = y := by
    intro y
    refine Submodule.Quotient.induction_on (LinearMap.range (LinearMap.lsmul ℤ V 2)) y ?_
    intro z
    exact congrArg (ModN.mkQ 2) (hf z)
  have hinj : Function.Injective f := by
    intro x y hxy
    rw [← hgf x, ← hgf y, hxy]
  have hsurj : Function.Surjective f := fun v => ⟨ModN.mkQ 2 v, hf v⟩
  have hfin : Module.finrank (ZMod 2) (ModN V 2) = Module.finrank (ZMod 2) V :=
    LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)
  -- `Additive (Multiplicative V)` is definitionally `V`, so this is the goal
  change Module.finrank (ZMod 2) (ModN V 2) = Module.finrank (ZMod 2) V
  exact hfin

end Work.QuadraticFields
