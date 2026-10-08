import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

theorem sylow_normalizer_le_centralizer_of_card_prime {D : Type} [Group D] [Finite D]
    {p : ℕ} [Fact p.Prime] (P : Sylow p D) (hP : Nat.card (P : Subgroup D) = p)
    (hcop : Nat.Coprime (p - 1) (Nat.card D)) :
    Subgroup.normalizer (P : Set D) ≤ Subgroup.centralizer (P : Set D) := by
  -- `P` has prime order `p`, hence is cyclic.
  have hcyc : IsCyclic P := isCyclic_of_prime_card hP
  -- The conjugation action `N_D(P) → Aut(P)` has kernel `C_D(P)`, so it induces an
  -- injection `N_D(P)/C_D(P) ↪ Aut(P)`; hence `[N_D(P) : C_D(P)] ∣ |Aut(P)|`.
  have key : (Subgroup.centralizer (P : Set D)).relIndex
      (Subgroup.normalizer (P : Set D)) ∣ Nat.card (MulAut P) := by
    have h := Subgroup.card_dvd_of_injective _
      (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
    rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex] at h
    exact h
  -- Since `P` is cyclic of order `p`, `|Aut(P)| = φ(p) = p - 1`.
  rw [@IsCyclic.card_mulAut P _ _ hcyc, hP, Nat.totient_prime Fact.out] at key
  -- `[N_D(P) : C_D(P)]` also divides `|D|`.
  have hdvd : (Subgroup.centralizer (P : Set D)).relIndex
      (Subgroup.normalizer (P : Set D)) ∣ Nat.card D :=
    (Subgroup.relIndex_dvd_card (Subgroup.centralizer (P : Set D))
        (Subgroup.normalizer (P : Set D))).trans
      (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (P : Set D)))
  -- Coprimality of `p - 1` and `|D|` forces `[N_D(P) : C_D(P)] = 1`, i.e. `N_D(P) ≤ C_D(P)`.
  refine Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  exact (hcop.coprime_dvd_right hdvd).symm

end Work.ThmF.ChV12
