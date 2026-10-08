import Mathlib
import Submission.Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- In the simple nonabelian group `G` of order `360` with `n₅ = 6` (so that every Sylow
`5`-subgroup `P` has normalizer of order `60`), the centralizer of a Sylow `5`-subgroup has order
at most `30`.

`P ≤ C_G(P) ≤ N_G(P)`, so `|C_G(P)|` divides `60` and is divisible by `5`; if `|C_G(P)| = 60` then
`C_G(P) = N_G(P)`, i.e. `N_G(P) ≤ C_G(P)`, and Burnside's normal `p`-complement theorem
(`Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup`) then produces `g ∈ N_G(P)` with
`g ∉ C_G(P)`, a contradiction.  Hence `|C_G(P)|` is a proper divisor of `60`, so `≤ 30`. -/
theorem card_centralizer_sylow_five_le {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hG : Nat.card G = 360)
    (h5 : Nat.card (Sylow 5 G) = 6) (P : Sylow 5 G) :
    Nat.card ↥(Subgroup.centralizer ((P : Subgroup G) : Set G)) ≤ 30 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5dvd : 5 ∣ Nat.card G := by rw [hG]; norm_num
  -- The number of Sylow `5`-subgroups is the index of the normalizer, so `|N_G(P)| = 60`.
  have hNidx : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 6 := by
    have h := Sylow.card_eq_index_normalizer P
    rw [h5] at h
    exact h.symm
  have hN60 : Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) = 60 := by
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup G) : Set G))
    rw [hNidx, hG] at hmul
    omega
  -- `C_G(P) ≤ N_G(P)`.
  have hCN : Subgroup.centralizer ((P : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  -- Burnside: `N_G(P) ⊄ C_G(P)` in a non-abelian simple group.
  have hex : ∃ g : G, g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
      g ∉ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
    exists_not_mem_centralizer_of_isPGroup (G := G) hnab (p := 5) (P := (P : Subgroup G))
      (Sylow.isPGroup' P) (Sylow.not_dvd_index P) h5dvd
  have hne : Subgroup.centralizer ((P : Subgroup G) : Set G) ≠
      Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    obtain ⟨g, hgN, hgC⟩ := hex
    exact fun h => hgC (h ▸ hgN)
  -- So `|C_G(P)|` is a divisor of `60` different from `60`, hence at most `30`.
  have hCne : Nat.card ↥(Subgroup.centralizer ((P : Subgroup G) : Set G)) ≠ 60 := by
    intro hcard
    have hc : Nat.card ↥(Subgroup.centralizer ((P : Subgroup G) : Set G)) =
        Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) := by rw [hcard, hN60]
    exact hne (Subgroup.eq_of_le_of_card_ge hCN (le_of_eq hc.symm))
  have hdvd : Nat.card ↥(Subgroup.centralizer ((P : Subgroup G) : Set G)) ∣ 60 := by
    rw [← hN60]
    exact Subgroup.card_dvd_of_le hCN
  obtain ⟨k, hk⟩ := hdvd
  have hk_ne1 : k ≠ 1 := by
    rintro rfl
    exact hCne (by simpa using hk.symm)
  have hk_ne0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hk2 : 2 ≤ k := by omega
  have h2 : 2 * Nat.card ↥(Subgroup.centralizer ((P : Subgroup G) : Set G)) ≤ 60 := by
    calc 2 * Nat.card ↥(Subgroup.centralizer ((P : Subgroup G) : Set G))
        ≤ k * Nat.card ↥(Subgroup.centralizer ((P : Subgroup G) : Set G)) :=
          Nat.mul_le_mul_right _ hk2
      _ = 60 := by rw [mul_comm, ← hk]
  omega

end Work.BSW.Cases.K4
