import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.PSL2.Card

open scoped MatrixGroups
open Matrix

namespace Work.DSTR.L2CentAux

/-- For an odd prime `p` the field `GF(p,k)` has characteristic `p ≠ 2`, so `2 ≠ 0`. -/
private lemma two_ne_zero_galois (p k : ℕ) [Fact p.Prime] (hp : Odd p) :
    (2 : GaloisField p k) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp2 : p = 2 := le_antisymm hle hge
  obtain ⟨m, hm⟩ := hp
  omega

/-- The index of the image in `PSL(2,q)` of the upper unipotent subgroup is `(q²-1)/2`, `q = p^k`;
in particular it is prime to `p`.  Proof: `|pslUnipotent| = q` (`PSL.pslUnipotent_card`) and
`2 * |PSL(2,q)| = q(q²-1)` (`PSL2.card_PSL2_galoisField`); the index relation
`|H| * H.index = |G|` gives `2 * H.index = q² - 1`.  If `p` divided the index then `p` would
divide both `q² = p^(2k)` and `q² - 1`, hence `p ∣ 1`, absurd. -/
theorem not_dvd_index_pslUnipotent {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    ¬ p ∣ (Work.L2F.pslUnipotent (GaloisField p k)).index := by
  -- `5 ≤ p^k` forces `k ≠ 0`, so that `p ∣ p^(2k)`.
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  set G := PSL(2, GaloisField p k) with hGdef
  set U : Subgroup G := Work.L2F.pslUnipotent (GaloisField p k) with hUdef
  -- Order of the unipotent subgroup: `|U| = p^k`.
  have hUcard : Nat.card U = p ^ k := by
    rw [hUdef, Work.L2F.PSL.pslUnipotent_card (GaloisField p k) (two_ne_zero_galois p k hp),
      GaloisField.card p k hk0]
  -- Order of `PSL(2,GF(p,k))`: `2 * |G| = p^k (p^(2k) - 1)`.
  have hGcard : 2 * Nat.card G = p ^ k * (p ^ (2 * k) - 1) := by
    rw [hGdef]
    exact Work.PSL2.card_PSL2_galoisField p k hp hk0
  -- The index relation `|U| * U.index = |G|`.
  have hidx := Subgroup.card_mul_index U
  -- Numerical consequence: `2 * U.index = p^(2k) - 1`.
  have hmain : 2 * U.index = p ^ (2 * k) - 1 := by
    have h1 : p ^ k * (2 * U.index) = p ^ k * (p ^ (2 * k) - 1) :=
      calc p ^ k * (2 * U.index) = 2 * (Nat.card U * U.index) := by rw [hUcard]; ring
        _ = 2 * Nat.card G := by rw [hidx]
        _ = p ^ k * (p ^ (2 * k) - 1) := hGcard
    exact Nat.mul_left_cancel (pow_pos (Fact.out : p.Prime).pos k) h1
  intro hpdvd
  -- `p` divides `p^(2k) - 1 = 2 * U.index`.
  have h1 : p ∣ p ^ (2 * k) - 1 := by
    rw [← hmain]
    exact dvd_mul_of_dvd_right hpdvd 2
  -- `p` divides `p^(2k)`.
  have h2 : p ∣ p ^ (2 * k) := dvd_pow_self p (by omega)
  -- Hence `p` divides the difference, which is `1`.
  have h3 : p ∣ p ^ (2 * k) - (p ^ (2 * k) - 1) := Nat.dvd_sub h2 h1
  rw [Nat.sub_sub_self (Nat.one_le_pow (2 * k) p (Fact.out : p.Prime).pos)] at h3
  exact (Fact.out : p.Prime).not_dvd_one h3

end Work.DSTR.L2CentAux
