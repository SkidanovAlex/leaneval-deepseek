import Mathlib
import Submission.Work.PTCert.eAux

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.D Submission.PTCert.G Submission.PTCert.C

/-- A `Bool` is `false` exactly when it is not `true` (usable `rewrite` form). -/
theorem bool_eq_false_iff_not_true (b : Bool) : (b = false) ↔ ¬(b = true) := by
  cases b <;> simp

/-- `!(Nat.beq n 0) = true` says `n ≠ 0`. -/
theorem not_beq_zero_true_iff (n : ℕ) : ((!(Nat.beq n 0)) = true) ↔ n ≠ 0 := by
  rw [Bool.not_eq_true', bool_eq_false_iff_not_true, Nat.beq_eq]

/-- Consequences of `eExactOK eM eAll = true` (use `Submission.PTCert.C.eexact_ok` for the
concrete data): `eAll` has no repetitions, and for `z < 10368` membership in `eAll` is exactly
non-vanishing of the positive membership-tree entry `em z = eG eM z`.
Recipe: `Bool.and_eq_true` splits the check into `eqL ((List.range 10368).filter (fun c => !(Nat.beq (eG eM c) 0))) (msortK 40 eAll) = true`
and `strictInc (msortK 40 eAll) = true`.  Use `Work.PTCert.eqL_iff_eAux`, `Work.PTCert.msortK_perm`
(`(msortK 40 eAll).Perm eAll`), `List.Perm.nodup_iff`, `Work.PTCert.strictInc_nodup`,
`List.mem_filter`, `List.mem_range`, `List.Perm.mem_iff`, and `Nat.beq_eq` /
`Bool.not_eq_true` to turn `!(Nat.beq (eG eM z) 0) = true` into `eG eM z ≠ 0`. -/
theorem eExactFacts
    (h : Submission.PTCert.eExactOK Submission.PTCert.D.eM Submission.PTCert.D.eAll = true) :
    Submission.PTCert.D.eAll.Nodup ∧
      (∀ z < 10368, z ∈ Submission.PTCert.D.eAll ↔ Submission.PTCert.G.em z ≠ 0) := by
  -- unfold the check: it is a conjunction of two `Bool`s
  have hh := h
  unfold Submission.PTCert.eExactOK at hh
  rw [Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  -- `h1` identifies the support of `eM` on `[0, 10368)` with the sorted `eAll`
  have hlist : (List.range 10368).filter (fun c => !(Nat.beq (eG eM c) 0)) = msortK 40 eAll :=
    (eqL_iff_eAux _ _).mp h1
  refine ⟨?_, ?_⟩
  · -- `strictInc` gives `Nodup` of the sorted list, and `msortK` is a permutation
    exact (List.Perm.nodup_iff (msortK_perm 40 eAll)).mp (strictInc_nodup _ h2)
  · intro z hz
    -- membership in the sorted list is the filtered membership, on `z < 10368`
    have key : z ∈ msortK 40 eAll ↔ (!(Nat.beq (eG eM z) 0)) = true := by
      rw [← hlist, List.mem_filter, List.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
    rw [← (msortK_perm 40 eAll).mem_iff, key]
    show ((!(Nat.beq (eG eM z) 0)) = true) ↔ eG eM z ≠ 0
    exact not_beq_zero_true_iff (eG eM z)

end Work.PTCert
