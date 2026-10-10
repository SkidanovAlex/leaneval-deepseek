import Mathlib.FieldTheory.Galois.Basic
import Submission.Commons.FieldTheory.Galois.div_mem_range_norm_of_prime_quotient_coprime_of_isGalois_tower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

/-- **The coprime-action mechanism.** Let `B ⊆ B₁ ⊆ E` be a tower of finite Galois extensions with `B₁/B` and `E/B` finite Galois. If the quotient `B₁ˣ ⧸ N_{E/B₁}(Eˣ)` has prime order `q` and `q - 1` is coprime to `#Gal(B₁/B)`, then the natural action of `Gal(B₁/B)` on that quotient is trivial: for every `σ : B₁ ≃ₐ[B] B₁` and every `x : B₁ˣ` the element `σ x / x` lies in `N_{E/B₁}(Eˣ)`. -/
lemma div_mem_range_norm_of_prime_quotient_coprime
    {B B₁ E : Type*} [Field B] [Field B₁] [Field E]
    [Algebra B B₁] [Algebra B E] [Algebra B₁ E] [IsScalarTower B B₁ E]
    [FiniteDimensional B B₁] [IsGalois B B₁] [FiniteDimensional B E] [IsGalois B E]
    (hprime : Nat.Prime (Nat.card (B₁ˣ ⧸
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)))))
    (hcop : (Nat.card (B₁ ≃ₐ[B] B₁)).Coprime
      (Nat.card (B₁ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁))) - 1))
    (σ : B₁ ≃ₐ[B] B₁) (x : B₁ˣ) :
    Units.map σ.toRingEquiv.toMonoidHom x / x ∈
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)) := by
  -- `E/B` finite and `B₁/B` finite (with the scalar tower `B → B₁ → E`) give `E/B₁` finite,
  -- which is exactly the tower hypothesis of the already-proven general form.
  haveI : FiniteDimensional B₁ E := Module.Finite.of_restrictScalars_finite B B₁ E
  exact div_mem_range_norm_of_prime_quotient_coprime_of_isGalois_tower hprime hcop σ x

end Commons.FieldTheory.Galois
