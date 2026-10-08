import Mathlib

/-!
# `C_G(P) = P` for the Sylow `5`-subgroup in the `|K| = 2` case (Bender 1974, §1)

Small group-theoretic step used in the structural analysis of the `|K| = 2` case of
the Gorenstein–Walter / Bender argument, at `q = 5`.

Setting: `P ≤ G` with `|P| = 5`, `|N_G(P)| = 10`, and every involution `w ∈ G` has
centralizer of order `4`.  Conclusion: `C_G(P) = P`.

Proof:

* `P` has prime order `5`, hence is commutative, so `P ≤ C_G(P)`
  (`Subgroup.le_centralizer_iff_isMulCommutative`); and `C_G(P) ≤ N_G(P)`
  (`Subgroup.centralizer_le_normalizer`).
* Hence `|P| = 5` divides `|C_G(P)|`, while `|C_G(P)|` divides `|N_G(P)| = 10`;
  so `|C_G(P)| ∈ {5, 10}`.
* If `|C_G(P)| = 10` then `C_G(P) = N_G(P)`, so `P` is central in `N_G(P)`.  By
  Cauchy's theorem `N_G(P)` contains an involution `w`; since `w ∈ C_G(P)` it
  centralizes `P`, so `P ≤ C_G(w)`, contradicting `|C_G(w)| = 4 < 5`.
* Therefore `|C_G(P)| = 5 = |P|`, and with `P ≤ C_G(P)` this forces `C_G(P) = P`.
-/

namespace Work.BSW.Cases

theorem bswK2CentralizerSylowFive {G : Type} [Group G] [Finite G] (P : Subgroup G)
    (hcard : Nat.card ↥P = 5) (hN : Nat.card ↥(Subgroup.normalizer (P : Set G)) = 10)
    (hinv : ∀ w : G, orderOf w = 2 → Nat.card ↥(Subgroup.centralizer ({w} : Set G)) = 4) :
    Subgroup.centralizer (P : Set G) = P := by
  set C := Subgroup.centralizer (P : Set G)
  set N := Subgroup.normalizer (P : Set G)
  -- `P` has prime order, hence is commutative, hence lies in its own centralizer.
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcyc : IsCyclic ↥P := isCyclic_of_prime_card hcard
  have hPleC : P ≤ C := Subgroup.le_centralizer_iff_isMulCommutative.mpr (by infer_instance)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (P : Set G)
  -- Cardinality of `C_G(P)`: it is a multiple of `5` and a divisor of `10`.
  have hdvd5 : 5 ∣ Nat.card ↥C := by
    have h := Subgroup.card_dvd_of_le hPleC
    rw [hcard] at h
    exact h
  have hdvd10 : Nat.card ↥C ∣ 10 := by
    have h := Subgroup.card_dvd_of_le hCN
    rw [hN] at h
    exact h
  have hcases : Nat.card ↥C = 5 ∨ Nat.card ↥C = 10 := by
    obtain ⟨k, hk⟩ := hdvd5
    have hk2 : k ∣ 2 := by
      have h : 5 * k ∣ 5 * 2 := by rw [← hk]; simpa using hdvd10
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 5)).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h | h
    · left; rw [hk, h]
    · right; rw [hk, h]
  rcases hcases with h5 | h10
  · -- `|C_G(P)| = 5 = |P|` with `P ≤ C_G(P)` gives equality.
    exact (Subgroup.eq_of_le_of_card_ge (H := P) (K := C) hPleC (by omega)).symm
  · -- `|C_G(P)| = 10 = |N_G(P)|` forces `C_G(P) = N_G(P)`, which is impossible.
    exfalso
    have hCN_eq : C = N := Subgroup.eq_of_le_of_card_ge hCN (by omega)
    -- An involution in `N_G(P)` (Cauchy, since `2 ∣ 10`).
    have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    have h2dvd : 2 ∣ Nat.card ↥N := by rw [hN]; norm_num
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2dvd
    have hwG : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe, hw]
    have hcent : Nat.card ↥(Subgroup.centralizer ({(w : G)} : Set G)) = 4 := hinv (w : G) hwG
    -- Since `w ∈ C_G(P)`, it centralizes `P`, so `P ≤ C_G(w)`.
    have hPle : P ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hwC : (w : G) ∈ C := by rw [hCN_eq]; exact w.2
      exact ((Subgroup.mem_centralizer_iff.mp hwC) p hp).symm
    have hle : Nat.card ↥P ≤ Nat.card ↥(Subgroup.centralizer ({(w : G)} : Set G)) :=
      Subgroup.card_le_of_le hPle
    rw [hcard, hcent] at hle
    omega

end Work.BSW.Cases
