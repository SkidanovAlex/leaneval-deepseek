import Mathlib

/-!
# Zero sets of multivariate polynomials over finite fields

A direct corollary of the Schwartz--Zippel lemma
(`Mathlib.Algebra.MvPolynomial.SchwartzZippel`): a nonzero multivariate
polynomial in `m` variables over a finite field `F` vanishes on at most
`totalDegree · |F|^(m-1)` points of `F^m`.

This is the engine behind every "count the degenerate coefficient tuples"
step in the geometric sieve arguments (Case III of Bhargava's proof of van
der Waerden's conjecture, discriminant-mod-`p` root counts, ...): for a fixed
nonzero integer polynomial `P` (e.g. the degree-`2n-2` discriminant, viewed
as a polynomial in the `n` non-leading coefficients of a monic degree-`n`
polynomial), the number of monic degree-`n` polynomials over `𝔽_q` whose
coefficient tuple is a root of `P` mod `q` is `O(q^(n-1))`.

All statements are in `namespace Submission.Vdw`.
-/

namespace Submission.Vdw

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

/-- **Schwartz–Zippel over a finite field.**  A nonzero
`h : MvPolynomial (Fin m) F` over a finite field `F` vanishes on at most
`h.totalDegree · |F|^(m-1)` points of `F^m`. -/
theorem eval_zero_card_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] (m : ℕ)
    (h : MvPolynomial (Fin m) F) (hh : h ≠ 0) :
    Fintype.card {x : Fin m → F // eval x h = 0} ≤ h.totalDegree * (Fintype.card F) ^ (m - 1) := by
  classical
  let q : ℕ := Fintype.card F
  have hqpos : 0 < q := by
    dsimp [q]
    exact Fintype.card_pos (α := F)
  have hs := MvPolynomial.schwartz_zippel_totalDegree (p := h) hh (Finset.univ : Finset F)
  have hnum : ((Finset.univ : Finset (Fin m → F)).filter (fun f => eval f h = 0)).card =
      Fintype.card {x : Fin m → F // eval x h = 0} := by
    rw [Fintype.card_subtype (α := Fin m → F) (p := fun x => eval x h = 0)]
  have hden : ((Finset.univ : Finset F).card ^ m : ℕ) = q ^ m := by simp [q]
  have htd : (h.totalDegree : ℚ≥0) / (Finset.univ : Finset F).card = (h.totalDegree : ℚ≥0) / q := by
    simp [q]
  have hpi : Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset F)) =
      (Finset.univ : Finset (Fin m → F)) := by
    ext f; simp
  have hsQ : (Fintype.card {x : Fin m → F // eval x h = 0} : ℚ≥0) / (q : ℚ≥0) ^ m
      ≤ (h.totalDegree : ℚ≥0) / (q : ℚ≥0) := by
    simpa [hpi, hden, htd, hnum] using hs
  rcases m with _ | m'
  · have hq1 : (1 : ℚ≥0) ≤ (q : ℚ≥0) := by exact_mod_cast (Nat.succ_le_of_lt hqpos)
    have hs0 : ((Fintype.card {x : Fin 0 → F // eval x h = 0} : ℚ≥0)) ≤
        (h.totalDegree : ℚ≥0) / (q : ℚ≥0) := by
      simpa using hsQ
    have htddiv : (h.totalDegree : ℚ≥0) / (q : ℚ≥0) ≤ (h.totalDegree : ℚ≥0) := by
      rw [div_le_iff₀]
      · exact le_mul_of_one_le_right (by positivity) hq1
      · positivity
    have hcard : Fintype.card {x : Fin 0 → F // eval x h = 0} ≤ h.totalDegree := by
      exact_mod_cast (hs0.trans htddiv)
    simpa using hcard
  · have hqNN : (q : ℚ≥0) ^ (m' + 1) ≠ 0 := by positivity
    have hstep : (Fintype.card {x : Fin (m' + 1) → F // eval x h = 0} : ℚ≥0) ≤
        (h.totalDegree * q ^ m' : ℕ) := by
      calc
        (Fintype.card {x : Fin (m' + 1) → F // eval x h = 0} : ℚ≥0)
            = ((Fintype.card {x : Fin (m' + 1) → F // eval x h = 0} : ℚ≥0) /
                (q : ℚ≥0) ^ (m' + 1)) * (q : ℚ≥0) ^ (m' + 1) := by
                rw [div_mul_cancel₀ _ hqNN]
        _ ≤ ((h.totalDegree : ℚ≥0) / (q : ℚ≥0)) * (q : ℚ≥0) ^ (m' + 1) := by gcongr
        _ = (h.totalDegree * q ^ m' : ℕ) := by
                have hq0 : (q : ℚ≥0) ≠ 0 := by positivity
                field_simp [hq0]
                rw [pow_succ, Nat.cast_mul, Nat.cast_pow]
                ring
    exact_mod_cast hstep

end

end Submission.Vdw
