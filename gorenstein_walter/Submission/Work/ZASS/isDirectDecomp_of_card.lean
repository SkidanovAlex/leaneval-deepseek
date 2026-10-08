import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

open scoped Pointwise

namespace Work.ZASS

/-- **Z2 (blueprint §ZASS).** With `H = G_{∞0}`, `|U| = q`, `|H| = h`, `|B| = q * h` and
`Nat.Coprime q h`, a normal `U ≤ B` together with `H` gives `B = U ⋊ H`: the intersection is
trivial by coprimality and `U ⊔ H` has order `q * h = |B|`. -/
theorem isDirectDecomp_of_card {G X : Type} [Group G] [Finite G] [MulAction G X]
    {q h : ℕ} {inf zero : X} {U : Subgroup G}
    (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hHB : Work.Zassenhaus.pairStab G inf zero ≤ Work.Zassenhaus.borel G inf)
    (hcardU : Nat.card U = q) (hcardH : Nat.card (Work.Zassenhaus.pairStab G inf zero) = h)
    (hB : Nat.card (Work.Zassenhaus.borel G inf) = q * h) (hcop : Nat.Coprime q h)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal) :
    Work.ZASS.IsDirectDecomp (Work.Zassenhaus.borel G inf) U
      (Work.Zassenhaus.pairStab G inf zero) := by
  classical
  set H := Work.Zassenhaus.pairStab G inf zero with hHdef
  set B := Work.Zassenhaus.borel G inf with hBdef
  -- The intersection is trivial: its order divides both `q` and `h`, hence divides `1`.
  have hinf : U ⊓ H = ⊥ := by
    have hdvdU : Nat.card ↥(U ⊓ H) ∣ q := by
      rw [← hcardU]; exact Subgroup.card_dvd_of_le inf_le_left
    have hdvdH : Nat.card ↥(U ⊓ H) ∣ h := by
      rw [← hcardH]; exact Subgroup.card_dvd_of_le inf_le_right
    have hg : Nat.card ↥(U ⊓ H) ∣ Nat.gcd q h := Nat.dvd_gcd hdvdU hdvdH
    rw [hcop.gcd_eq_one] at hg
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp hg)
  have hsup : U ⊔ H ≤ B := sup_le hUB hHB
  -- `U` is normal in `B` and `H ≤ B`, so `H` normalizes `U`: every element of the join is a
  -- product `u * h` with `u ∈ U`, `h ∈ H`.
  have hle_norm : H ≤ Subgroup.normalizer ↑U :=
    le_trans hHB ((Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hN)
  have hcoe : ((U ⊔ H : Subgroup G) : Set G) = (U : Set G) * (H : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U H hle_norm
  -- Counting: `|U ⊔ H| = |U × H| = q * h`.
  have hcard : Nat.card ↥(U ⊔ H) = q * h := by
    have hbij : Function.Bijective
        (fun p : U × H => (⟨(p.1 : G) * (p.2 : G),
          Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : (U ⊔ H : Subgroup G))) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨u₁, h₁⟩ ⟨u₂, h₂⟩ heq
        have he : (u₁ : G) * h₁ = (u₂ : G) * h₂ := congrArg Subtype.val heq
        have key : ((u₂ : G)⁻¹ * u₁) * h₁ = h₂ := by
          rw [mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]
        have hg : (u₂ : G)⁻¹ * u₁ = (h₂ : G) * (h₁ : G)⁻¹ := by
          have := congrArg (fun x => x * (h₁ : G)⁻¹) key
          simpa [mul_assoc] using this
        have hmem : (u₂ : G)⁻¹ * u₁ ∈ U ⊓ H :=
          ⟨U.mul_mem (U.inv_mem u₂.2) u₁.2, by rw [hg]; exact H.mul_mem h₂.2 (H.inv_mem h₁.2)⟩
        have hone : (u₂ : G)⁻¹ * u₁ = 1 := by
          rw [hinf] at hmem
          exact Subgroup.mem_bot.mp hmem
        have hone' : (h₂ : G) * (h₁ : G)⁻¹ = 1 := by rw [← hg]; exact hone
        have hu : u₁ = u₂ := Subtype.ext (inv_mul_eq_one.mp hone).symm
        have hh : h₁ = h₂ := Subtype.ext (mul_inv_eq_one.mp hone').symm
        rw [hu, hh]
      · intro x
        have hx : (x : G) ∈ (U : Set G) * (H : Set G) := by
          rw [← hcoe]; exact x.2
        obtain ⟨u, hu, hh, hhH, hux⟩ := hx
        exact ⟨(⟨u, hu⟩, ⟨hh, hhH⟩), Subtype.ext hux⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_prod, hcardU, hcardH]
  -- `U ⊔ H ≤ B` and the two sides have the same order `q * h`, so they are equal.
  have hEq : U ⊔ H = B :=
    Subgroup.eq_of_le_of_card_ge hsup (by simp [hcard, hB])
  exact ⟨hEq, hinf⟩

end Work.ZASS
