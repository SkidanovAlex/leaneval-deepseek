import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.LadderP

theorem card_filter_symIcc_mod_pos {c : ℤ} (hc : 0 < c) {N : ℕ}
    (hcN : c ≤ 2 * (N : ℤ) + 1) {r : ℕ} (hr : r < c.natAbs) :
    0 < ((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card := by
  -- `r` is a genuine residue mod `c`: `(r : ℤ) ∈ [0, c)`.
  have hrc : (r : ℤ) < c := by
    have h1 : (r : ℤ) < (c.natAbs : ℤ) := by exact_mod_cast hr
    rwa [Int.natCast_natAbs, abs_of_pos hc] at h1
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := by positivity
  -- It suffices to exhibit one element of `symIcc N` in the residue class.
  rw [Finset.card_pos]
  by_cases h : (r : ℤ) ≤ (N : ℤ)
  · -- The residue `r` itself already lies in `[-N, N]`.
    refine ⟨(r : ℤ), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Work.Peluse.symIcc, Finset.mem_Icc]
      exact ⟨by linarith, h⟩
    · exact Int.emod_eq_of_lt hr0 hrc
  · -- Otherwise `r > N`, and `c ≤ 2N+1` forces `r - c ∈ [-N, N]`.
    rw [not_le] at h
    refine ⟨(r : ℤ) - c, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Work.Peluse.symIcc, Finset.mem_Icc]
      exact ⟨by linarith, by linarith⟩
    · have heq : (r : ℤ) - c = (r : ℤ) + (-1) * c := by ring
      calc ((r : ℤ) - c) % c = ((r : ℤ) + (-1) * c) % c := by rw [heq]
        _ = (r : ℤ) % c := Int.add_mul_emod_self_right (r : ℤ) (-1) c
        _ = (r : ℤ) := Int.emod_eq_of_lt hr0 hrc

end Work.Peluse.LadderP
