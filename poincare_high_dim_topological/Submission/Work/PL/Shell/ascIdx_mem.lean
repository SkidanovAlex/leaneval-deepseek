import Mathlib
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

open Finset

variable {N : ℕ}

/-- Membership in `ascIdxAux`: the ascent positions of a list of consecutive pairs
`ps`, shifted by `i`, are exactly the indices `i + j` with `j < ps.length` at which
the rank strictly increases. -/
theorem ascIdxAux_mem {rk : PL.E N → ℕ} (ps : List (PL.E N × PL.E N)) (i s : ℕ) :
    s ∈ ascIdxAux rk ps i ↔ ∃ (j : ℕ) (hj : j < ps.length),
      s = i + j ∧ rk (ps[j]'hj).1 < rk (ps[j]'hj).2 := by
  induction ps generalizing i with
  | nil => simp [ascIdxAux]
  | cons p ps ih =>
    rw [ascIdxAux]
    by_cases hc : rk p.1 < rk p.2
    · rw [ite_eq_left hc, Finset.mem_insert, ih]
      constructor
      · rintro (rfl | ⟨j, hj, he, hlt⟩)
        · exact ⟨0, by simp, by omega, by simpa using hc⟩
        · exact ⟨j + 1, by simpa using hj, by omega, by simpa using hlt⟩
      · rintro ⟨j, hj, he, hlt⟩
        cases j with
        | zero => left; omega
        | succ k => right; exact ⟨k, by simpa using hj, by omega, by simpa using hlt⟩
    · rw [ite_eq_right hc, ih]
      constructor
      · rintro ⟨j, hj, he, hlt⟩
        exact ⟨j + 1, by simpa using hj, by omega, by simpa using hlt⟩
      · rintro ⟨j, hj, he, hlt⟩
        cases j with
        | zero => exact absurd (by simpa using hlt) hc
        | succ k => exact ⟨k, by simpa using hj, by omega, by simpa using hlt⟩

theorem ascIdx_mem {rk : PL.E N → ℕ} {l : List (PL.E N)} {s : ℕ} :
    s ∈ Work.PL.Shell.ascIdx rk l ↔ ∃ (h : s + 1 < l.length),
      rk (l[s]'(Nat.lt_of_succ_lt h)) < rk (l[s + 1]'h) := by
  simp only [ascIdx]
  rw [ascIdxAux_mem]
  constructor
  · rintro ⟨j, hj, he, hlt⟩
    have hs : s = j := by omega
    subst hs
    have hlen : s + 1 < l.length := by
      simp only [List.length_zip, List.length_tail] at hj
      omega
    have h1 : ((l.zip l.tail)[s]'hj).1 = l[s]'(Nat.lt_of_succ_lt hlen) := by
      rw [List.getElem_zip]
    have h2 : ((l.zip l.tail)[s]'hj).2 = l[s+1]'hlen := by
      rw [List.getElem_zip, List.getElem_tail]
    exact ⟨hlen, by rw [← h1, ← h2]; exact hlt⟩
  · rintro ⟨h, hlt⟩
    have hslen : s < (l.zip l.tail).length := by
      simp only [List.length_zip, List.length_tail]
      omega
    refine ⟨s, hslen, by omega, ?_⟩
    have h1 : ((l.zip l.tail)[s]'hslen).1 = l[s]'(Nat.lt_of_succ_lt h) := by
      rw [List.getElem_zip]
    have h2 : ((l.zip l.tail)[s]'hslen).2 = l[s+1]'h := by
      rw [List.getElem_zip, List.getElem_tail]
    rw [h1, h2]
    exact hlt

end Work.PL.Shell
