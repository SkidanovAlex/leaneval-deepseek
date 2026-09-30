import Mathlib
import Submission.Work.Pi6.K2Z.fgAbelianVanishes
import Submission.Work.Pi6.K2Z.zmodTensorSubsingleton
import Submission.Work.Pi6.K2Z.zmodTensorModuleFinite
import Submission.Work.Pi6.K2Z.fgAbelianDivisible
import Submission.Work.Pi6.EMZ.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# A finitely generated abelian group whose every mod-`p` reduction vanishes is trivial

Let `A` be a finitely generated abelian group and suppose that for every prime `p` the base change
`ZMod p ⊗[ℤ] A ≅ A ⧸ pA` is trivial (`finrank` zero over `ZMod p`).  Then `A = 0`.

The vanishing of the `ZMod p`-base change turns into the surjectivity of multiplication by `p` on
`A` (`Work.Pi6.K2Z.zmodTensorSubsingleton`), i.e. `A` is `p`-divisible for every prime `p`; a
finitely generated abelian group with that property is trivial (`Work.Pi6.K2Z.fgAbelianDivisible`).

This is the `ZMod p`-only form of `Work.Pi6.K2Z.fgAbelianVanishes`: the rational hypothesis there is
never used.
-/

set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.Pi6.K2Z

/-- **A finitely generated abelian group vanishing mod every prime is trivial.** -/
theorem fgAbelianVanishesZmod (A : Type) [AddCommGroup A] [Module.Finite ℤ A]
    (hp : ∀ p : ℕ, p.Prime → Module.finrank (ZMod p)
      ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) = 0) :
    Subsingleton A := by
  refine fgAbelianDivisible A fun p hpp => ?_
  rw [Work.Pi6.EMZ.subsingleton_quot_pH_iff]
  intro a
  haveI : Fact p.Prime := ⟨hpp⟩
  let V := ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A))
  haveI : Module.Finite (ZMod p) V := zmodTensorModuleFinite A p
  have hfr : Module.finrank (ZMod p) V = 0 := hp p hpp
  have hsub : Subsingleton V := by
    have h0 : ∀ x : V, x = 0 :=
      (finrank_zero_iff_forall_zero (K := ZMod p) (V := V)).mp hfr
    exact ⟨fun x y => by rw [h0 x, h0 y]⟩
  obtain ⟨b, hb⟩ := zmodTensorSubsingleton A p hsub a
  refine ⟨b, ?_⟩
  rw [Nat.cast_smul_eq_nsmul ℤ p b] at hb
  exact hb

end Work.Pi6.K2Z
