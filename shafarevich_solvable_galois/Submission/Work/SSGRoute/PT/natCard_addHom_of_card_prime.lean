import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- Over `ZMod p`, with `p` prime, the number of additive homomorphisms from a finite
`ZMod p`-module `B` to a `ZMod p`-module `D` of cardinality `p` equals the cardinality
of `B`.

Indeed `Nat.card D = p` forces `D` to be one-dimensional over `ZMod p`, so that
`D ≃ₗ[ZMod p] ZMod p` and `B →+ D ≃ B →ₗ[ZMod p] ZMod p = Module.Dual (ZMod p) B`;
the dual of `B` has the same cardinality as `B`. -/
theorem natCard_addHom_of_card_prime {p : ℕ} [Fact p.Prime] {B D : Type}
    [AddCommGroup B] [Module (ZMod p) B] [Finite B]
    [AddCommGroup D] [Module (ZMod p) D] (hD : Nat.card D = p) :
    Nat.card (B →+ D) = Nat.card B := by
  have hp : p.Prime := Fact.out
  have hDfin : Finite D := (Nat.card_ne_zero.mp (by rw [hD]; exact hp.ne_zero)).2
  -- `D` is a one-dimensional `ZMod p`-vector space, because `Nat.card D = p`.
  have h2 : Nat.card D = p ^ Module.finrank (ZMod p) D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := D), Nat.card_zmod]
  have h3 : p ^ Module.finrank (ZMod p) D = p ^ 1 := by
    rw [pow_one, ← h2]; exact hD
  have hf : Module.finrank (ZMod p) D = 1 := Nat.pow_right_injective hp.two_le h3
  have eD : D ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq D (ZMod p) (by rw [hf, Module.finrank_self])
  -- the dual of `B` is a `ZMod p`-vector space of the same cardinality as `B`
  have eB : B ≃ₗ[ZMod p] Module.Dual (ZMod p) B :=
    Module.Basis.toDualEquiv (Module.finBasis (ZMod p) B)
  calc Nat.card (B →+ D)
      = Nat.card (B →ₗ[ZMod p] D) :=
        Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv p).toEquiv
    _ = Nat.card (B →ₗ[ZMod p] ZMod p) :=
        Nat.card_congr (LinearEquiv.congrRight eD).toEquiv
    _ = Nat.card (Module.Dual (ZMod p) B) := rfl
    _ = Nat.card B := (Nat.card_congr eB.toEquiv).symm

end Work.SSGRoute.PT
