import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThreePoints.ThmC

/-- A finite group `H` is the supremum of the images in the ambient group of a Sylow
`q`-subgroup of `H`, one for each prime `q` dividing `|H|`. -/
theorem eq_iSup_sylow {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (Q : (q : ℕ) → Sylow q ↥H) :
    H = ⨆ (q : ℕ) (_ : q ∈ (Nat.card ↥H).primeFactors),
      ((Q q : Subgroup ↥H).map H.subtype) := by
  -- `K` is the supremum of the images of the chosen Sylow subgroups.
  set K : Subgroup G := ⨆ (q : ℕ) (_ : q ∈ (Nat.card ↥H).primeFactors),
      ((Q q : Subgroup ↥H).map H.subtype) with hK
  -- Each image lies inside `H`, so `K ≤ H`.
  have hKH : K ≤ H := by
    rw [hK]
    refine iSup_le fun q => iSup_le fun _ => ?_
    rintro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, -, rfl⟩
    exact y.2
  -- The order of `H` divides the order of `K`: for every prime `p` and every
  -- `p ^ k ∣ |H|` we have `p ^ k ∣ |K|`, because `p ^ k` divides the order of the
  -- Sylow `p`-subgroup `Q p`, whose image is a subgroup of `K`.
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; simp
    haveI : Fact p.Prime := ⟨hp⟩
    have hH0 : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
    have hp_dvd : p ∣ Nat.card ↥H := dvd_trans (dvd_pow_self p hk) hpk
    have hpmem : p ∈ (Nat.card ↥H).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hH0⟩
    have hle : ((Q p : Subgroup ↥H).map H.subtype) ≤ K := by
      rw [hK]
      exact le_iSup₂ (f := fun (q : ℕ) (_ : q ∈ (Nat.card ↥H).primeFactors) =>
        ((Q q : Subgroup ↥H).map H.subtype)) p hpmem
    have h1 : p ^ k ∣ Nat.card ((Q p : Subgroup ↥H)) := by
      rw [Sylow.card_eq_multiplicity (Q p)]
      exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hH0).mp hpk)
    have h2 : Nat.card ((Q p : Subgroup ↥H)) ∣ Nat.card ↥K := by
      rw [← Subgroup.card_map_of_injective (K := (Q p : Subgroup ↥H)) H.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact dvd_trans h1 h2
  -- `K ≤ H` and `|H| ∣ |K|` force `K = H`, hence `H ≤ K`.
  have hEq : H = K := by
    have hcardH : Nat.card ↥H ≤ Nat.card ↥K := Nat.le_of_dvd Nat.card_pos hdvd
    exact (Subgroup.eq_of_le_of_card_ge (H := K) (K := H) hKH hcardH).symm
  exact hEq

end Work.ThreePoints.ThmC
