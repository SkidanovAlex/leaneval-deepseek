import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.PSL2.Card

namespace Work.L2F.PSL

open scoped MatrixGroups
open Matrix

/-! ## The `p`-part of `|PSL(2, GF(p,k))|`

For `p` an odd prime and `5 ≤ p ^ k`, the order of `PSL(2, GF(p,k))` is
`p ^ k * (p ^ (2 * k) - 1) / 2` (`Work.PSL2.card_PSL2_galoisField`), and since `p` is odd and
`p ∤ p ^ (2 * k) - 1`, the exponent of `p` in that order is exactly `k`. -/

/-- `k ≠ 0` follows from `5 ≤ p ^ k`. -/
theorem ne_zero_of_five_le {p k : ℕ} (hk : 5 ≤ p ^ k) : k ≠ 0 := by
  rintro rfl
  simp at hk

/-- `2 ≠ 0` in `GF(p,k)` for `p` an odd prime. -/
theorem two_ne_zero_galois {p k : ℕ} [Fact p.Prime] (hp : Odd p) :
    (2 : GaloisField p k) ≠ 0 := by
  haveI : CharP (GaloisField p k) p := inferInstance
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp2 : p = 2 := le_antisymm hle hge
  obtain ⟨m, hm⟩ := hp
  omega

/-- The cardinality of `GF(p,k)`. -/
theorem card_galois {p k : ℕ} [Fact p.Prime] (hk : 5 ≤ p ^ k) :
    Nat.card (GaloisField p k) = p ^ k :=
  GaloisField.card p k (ne_zero_of_five_le hk)

/-- The exponent of `p` in `|PSL(2, GF(p,k))|` is `k`, for `p` an odd prime and `5 ≤ p ^ k`. -/
theorem pslCard_factorization {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization p =
      k := by
  have hpp : Nat.Prime p := Fact.out
  have hk0 : k ≠ 0 := ne_zero_of_five_le hk
  set N : ℕ := Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) with hN
  have hmain : 2 * N = p ^ k * (p ^ (2 * k) - 1) := by
    rw [hN]
    exact Work.PSL2.card_PSL2_galoisField p k hp hk0
  have hNne : N ≠ 0 := by
    rw [hN]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  -- `p` does not divide `2`
  have hp2 : ¬ p ∣ 2 := by
    intro hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hpp.two_le
    have hp_eq : p = 2 := le_antisymm hle hge
    obtain ⟨m, hm⟩ := hp
    omega
  have hcop : Nat.Coprime (p ^ k) 2 := Nat.Coprime.pow_left k ((hpp.coprime_iff_not_dvd).mpr hp2)
  -- `p ^ k` divides `N`
  have hdvdN : p ^ k ∣ N := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [hmain]
    exact dvd_mul_right _ _
  -- `p ^ (k+1)` does not divide `N`
  have hnotdvd : ¬ p ^ (k + 1) ∣ N := by
    intro hB
    have hB' : p ^ (k + 1) ∣ p ^ k * (p ^ (2 * k) - 1) := by
      have h := dvd_mul_of_dvd_right hB 2
      rwa [hmain] at h
    rw [pow_succ] at hB'
    have hpdvd : p ∣ p ^ (2 * k) - 1 :=
      (Nat.mul_dvd_mul_iff_left (pow_pos hpp.pos k)).mp hB'
    have hpdpow : p ∣ p ^ (2 * k) := dvd_pow_self p (by omega)
    have hsub : p ∣ p ^ (2 * k) - (p ^ (2 * k) - 1) := Nat.dvd_sub hpdpow hpdvd
    have hge1 : 1 ≤ p ^ (2 * k) := by
      have := pow_pos hpp.pos (2 * k)
      omega
    rw [Nat.sub_sub_self hge1] at hsub
    exact hpp.not_dvd_one hsub
  refine le_antisymm ?_ ((hpp.pow_dvd_iff_le_factorization hNne).mp hdvdN)
  by_contra hle
  exact hnotdvd ((hpp.pow_dvd_iff_le_factorization hNne).mpr
    (Nat.succ_le_of_lt (not_le.mp hle)))

/-- `pslUnipotent (GF(p,k))` — the image in `PSL(2,GF(p,k))` of the upper unipotent subgroup of
`SL(2,GF(p,k))` — is a Sylow `p`-subgroup, for `p` an odd prime and `5 ≤ p^k`. -/
theorem pslUnipotent_sylow {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    ∃ Q : Sylow p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)),
      (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) =
        Work.L2F.pslUnipotent (GaloisField p k) := by
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2 : (2 : GaloisField p k) ≠ 0 := two_ne_zero_galois hp
  have hcard : Nat.card (Work.L2F.pslUnipotent (GaloisField p k)) =
      p ^ (Nat.card
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization p := by
    rw [pslUnipotent_card (GaloisField p k) h2, card_galois (p := p) (k := k) hk,
      pslCard_factorization (p := p) (k := k) hp hk]
  exact ⟨Sylow.ofCard (Work.L2F.pslUnipotent (GaloisField p k)) hcard, rfl⟩

end Work.L2F.PSL
