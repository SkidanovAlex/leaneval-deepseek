import Mathlib
import Submission.Work.L2F.Props.L2Free.Defs
import Submission.Work.PSL2.Card
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.L2F.PSL.exists_map_conj_eq_of_sylow

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.L2Free

/-- For a finite field `F` of odd characteristic with `Nat.card F = p ^ k` (`p` an odd prime),
the exponent of `p` in `|PSL(2,F)|` is exactly `k`.

Indeed `2 * |PSL(2,F)| = q (q²-1)` with `q = p ^ k`, so `p ^ k ∣ |PSL(2,F)|` (as `p ∤ 2`) while
`p ^ (k+1) ∤ |PSL(2,F)|` (as `p ∤ p ^ (2k) - 1`).  This is the `AUTL2`-free analogue of
`Work.L2F.PSL.pslCard_factorization`. -/
theorem pslCard_factorization_of_card (F : Type*) [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hcard : Nat.card F = p ^ k) :
    (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).factorization p = k := by
  have hpp : Nat.Prime p := Fact.out
  have hchar : ringChar F ≠ 2 := by
    intro h
    exact h2 ((ringChar.spec F 2).mpr (by rw [h]))
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    have := Fintype.one_lt_card (α := F)
    rw [Nat.card_eq_fintype_card] at hcard
    omega
  set N : ℕ := Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) with hN
  have hmain : 2 * N = p ^ k * (p ^ (2 * k) - 1) := by
    have h := Work.PSL2.card_PSL2_of_odd F hchar
    rw [← Nat.card_eq_fintype_card, hcard, ← hN] at h
    have h2' : (p ^ k) ^ 2 = p ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm k 2]
    rwa [h2'] at h
  have hNne : N ≠ 0 := by
    rw [hN]; exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hp2 : ¬ p ∣ 2 := by
    intro hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hpp.two_le
    have hp_eq : p = 2 := le_antisymm hle hge
    obtain ⟨m, hm⟩ := hp
    omega
  -- `p ^ k` divides `|PSL(2,F)|`
  have hdvdN : p ^ k ∣ N := by
    have h : p ^ k ∣ N * 2 := by rw [mul_comm]; rw [hmain]; exact dvd_mul_right _ _
    exact (Nat.Coprime.pow_left k ((hpp.coprime_iff_not_dvd).mpr hp2)).dvd_of_dvd_mul_right h
  -- `p ^ (k+1)` does not
  have hnotdvd : ¬ p ^ (k + 1) ∣ N := by
    intro hB
    have hB' : p ^ (k + 1) ∣ p ^ k * (p ^ (2 * k) - 1) := by
      have := dvd_mul_of_dvd_right hB 2
      rwa [hmain] at this
    rw [pow_succ] at hB'
    have hpdvd : p ∣ p ^ (2 * k) - 1 :=
      (Nat.mul_dvd_mul_iff_left (pow_pos hpp.pos k)).mp hB'
    have hpdpow : p ∣ p ^ (2 * k) := dvd_pow_self p (by omega)
    have hge1 : 1 ≤ p ^ (2 * k) := by have := pow_pos hpp.pos (2 * k); omega
    have hsub : p ∣ p ^ (2 * k) - (p ^ (2 * k) - 1) := Nat.dvd_sub hpdpow hpdvd
    rw [Nat.sub_sub_self hge1] at hsub
    exact hpp.not_dvd_one hsub
  refine le_antisymm ?_ ((hpp.pow_dvd_iff_le_factorization hNne).mp hdvdN)
  by_contra hle
  exact hnotdvd ((hpp.pow_dvd_iff_le_factorization hNne).mpr (Nat.succ_le_of_lt (not_le.mp hle)))

/-- Every subgroup of `PSL(2,F)` of order `p ^ k` (`|F| = p ^ k`, `p` odd) is a conjugate of the
image of the upper unipotent subgroup.  Sylow theory suffices: `p ^ k` is the full `p`-part of
`|PSL(2,F)| = q(q²-1)/2`.  Do not import `Work.AUTL2` or `Props/TwoSylow`. -/
theorem exists_conj_eq_pslUnipotent (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hcard : Nat.card F = p ^ k)
    (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (hQ : Nat.card Q = p ^ k) :
    ∃ h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      Q = (Work.L2F.pslUnipotent F).map (MulAut.conj h).toMonoidHom := by
  classical
  have hfac : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).factorization p = k :=
    pslCard_factorization_of_card F h2 p k hp hcard
  -- `pslUnipotent F` has order `p ^ k = p ^ (exponent of p in |PSL(2,F)|)`:
  have hP : Nat.card (Work.L2F.pslUnipotent F) =
      p ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).factorization p := by
    rw [Work.L2F.PSL.pslUnipotent_card F h2, hcard, hfac]
  -- and so does `Q`:
  have hQ' : Nat.card Q =
      p ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).factorization p := by
    rw [hQ, hfac]
  let P : Sylow p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Sylow.ofCard (Work.L2F.pslUnipotent F) hP
  let Qs : Sylow p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := Sylow.ofCard Q hQ'
  -- Sylow conjugacy, with the two Sylow subgroups that `ofCard` identifies with `pslUnipotent F`
  -- and with `Q` respectively.
  obtain ⟨g, hg⟩ := Work.L2F.PSL.exists_map_conj_eq_of_sylow P Qs
  exact ⟨g, by simpa only [P, Qs, Sylow.coe_ofCard] using hg⟩

end Work.L2F.Props.L2Free
