import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.letterAction

namespace Work.PTCert.codeFactsAux

/-- The letter action never leaves the range `1 .. NB1 5 = 81`.
`actL r pc sc k = 1 + 4 * pairIndex r (pdig pc i) (pdig pc j) + kind'` for `k ≠ 0`, where
`(i,j) = pairOf r ((k-1)/4)`, `kind' = 2*lf + nf < 4`, and `actL r pc sc 0 = 0`.
For `k < NB1 r` we have `(k-1)/4 < r*(r-1)`, so `pairOfValid` gives `i,j < r`, `i ≠ j`;
`validPC` gives `pdig pc i < r`, `pdig pc j < r` and `pdig pc i ≠ pdig pc j`, so
`pairIndex_lt` gives `pairIndex r (pdig pc i) (pdig pc j) < r*(r-1)`.
`NB1_eq r : NB1 r = 1 + 4 * (r * (r - 1))`.
Useful existing lemmas (all in `Submission.Work.PTCert.letterAction` or `letterDefs`):
`Work.PTCert.actL_eq`, `Work.PTCert.NB1_eq`, `Work.PTCert.pairIndex_lt`, `Work.PTCert.pairOfValid`,
`Work.PTCert.validPC_pdig_lt`, `Work.PTCert.validPC_pdig_inj`. -/
theorem actLBound (pc sc : ℕ) (h : Submission.PTCert.validPC 5 pc = true) :
    ∀ k < 81, Submission.PTCert.actL 5 pc sc k < 81 := by
  intro k hk
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0; simp [Submission.PTCert.actL]
  -- `(k-1)/4` stays below `5 * (5 - 1) = 20` because `k < 81`.
  have hq : (k - 1) / 4 < 5 * (5 - 1) := by omega
  obtain ⟨hiv, hjv, hij⟩ := Work.PTCert.pairOfValid 5 ((k - 1) / 4) (by norm_num) hq
  have hpiv : Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).1 < 5 :=
    Work.PTCert.validPC_pdig_lt 5 pc h _ hiv
  have hpjv : Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).2 < 5 :=
    Work.PTCert.validPC_pdig_lt 5 pc h _ hjv
  have hpij : Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).1 ≠
      Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).2 :=
    fun he => hij (Work.PTCert.validPC_pdig_inj 5 pc h _ _ hiv hjv he)
  have hPI : Submission.PTCert.pairIndex 5
      (Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).1)
      (Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).2) < 5 * (5 - 1) :=
    Work.PTCert.pairIndex_lt 5 _ _ (by norm_num) hpiv hpjv hpij
  have hti : Submission.PTCert.sbit sc
      (Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).1) < 2 :=
    Nat.mod_lt _ (by norm_num)
  have htj : Submission.PTCert.sbit sc
      (Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).2) < 2 :=
    Nat.mod_lt _ (by norm_num)
  have hK : (k - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hlf : ((k - 1) % 4 / 2) ^^^ Submission.PTCert.sbit sc
      (Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).1) < 2 :=
    Nat.xor_lt_two_pow (n := 1) (by omega) hti
  have hnf : ((k - 1) % 4 % 2) ^^^ Submission.PTCert.sbit sc
      (Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).1) ^^^
      Submission.PTCert.sbit sc
      (Submission.PTCert.pdig pc (Submission.PTCert.pairOf 5 ((k - 1) / 4)).2) < 2 :=
    Nat.xor_lt_two_pow (n := 1) (Nat.xor_lt_two_pow (n := 1) (by omega) hti) htj
  rw [Work.PTCert.actL_eq 5 pc sc k hk0]
  omega

end Work.PTCert.codeFactsAux
