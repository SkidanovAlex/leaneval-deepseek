import Mathlib
import Submission.Commons.FieldTheory.Galois.div_mem_range_norm_of_prime_quotient_coprime_of_isGalois_tower
import Submission.Commons.FieldTheory.Galois.ker_norm_le_range_of_cyclic_of_div_mem_range_norm

namespace Commons.FieldTheory.Galois

/-- **The cyclic coprime kernel condition.** Let `B ⊆ B₁ ⊆ E` be a tower of finite Galois
extensions with `B₁/B` and `E/B` finite Galois. If `Gal(B₁/B)` is cyclic, the quotient
`B₁ˣ ⧸ N_{E/B₁}(Eˣ)` has prime order `q`, and `q - 1` is coprime to `#Gal(B₁/B)`, then the norm
kernel `ker(N_{B₁/B})` is contained in `N_{E/B₁}(Eˣ)`. -/
theorem kernel_condition_of_cyclic_middle_coprime
    {B B₁ E : Type*} [Field B] [Field B₁] [Field E]
    [Algebra B B₁] [Algebra B E] [Algebra B₁ E] [IsScalarTower B B₁ E]
    [FiniteDimensional B B₁] [IsGalois B B₁] [FiniteDimensional B₁ E] [IsGalois B E]
    (hcyc : IsCyclic (B₁ ≃ₐ[B] B₁))
    (hprime : Nat.Prime (Nat.card (B₁ˣ ⧸
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)))))
    (hcop : (Nat.card (B₁ ≃ₐ[B] B₁)).Coprime
      (Nat.card (B₁ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁))) - 1)) :
    MonoidHom.ker (Units.map (Algebra.norm B : B₁ →* B)) ≤
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)) :=
  ker_norm_le_range_of_cyclic_of_div_mem_range_norm hcyc
    (fun σ x =>
      div_mem_range_norm_of_prime_quotient_coprime_of_isGalois_tower hprime hcop σ x)

end Commons.FieldTheory.Galois
