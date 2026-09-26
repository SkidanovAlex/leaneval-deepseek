import Mathlib
import Submission.Work.PTCert.letterDefs
import Submission.Work.PTCert.sigmaGroupFacts

/-!
# Sign-flip conjugation of a Nielsen letter

For a sign flip `signAut s` (`a_k ↦ a_k⁻¹` for the indices `k` with `s k = true`) and a
Nielsen letter `kindAutNat i j hij b0 b1` (`rho`/`rhoNeg`/`lam`/`lamNeg`, with `b0` the
left/right flag and `b1` the exponent flag), conjugation by the sign flip sends the letter
to the letter with the same ordered pair `(i,j)` but flags

* `b0' = b0 ^^^ [s i]` (the left/right flag is flipped exactly when `a_i` is inverted),
* `b1' = b1 ^^^ [s i] ^^^ [s j]` (the exponent flag is flipped exactly when an odd number of
  `a_i`, `a_j` is inverted).

This is the generator-level computation used by `SignCodes`/`LetterAction`: the sign flips
generate the elementary abelian group of the `2^r` sign changes, and on the letters they act
by the flag arithmetic above.

The proof checks both automorphisms on the free generators (`RouteB.mulAut_eq_iff`).  For a
generator `a_k` with `k ≠ i` the letter fixes it; for `k = i` one computes
`(signAut s) (X ((signAut s) a_i))` by the four cases `s i`, `s j ∈ {true,false}`.
-/

namespace Work.PTCert

open Submission.PTCert Submission.FreeGroupAut

variable {r : ℕ}

/-- A Nielsen letter `kindAutNat i j hij b0 b1` fixes every generator except the `i`-th. -/
lemma kindAutNat_apply_of_ne {i j : Fin r} (hij : i ≠ j) (b0 b1 : ℕ) (k : Fin r)
    (hk : k ≠ i) :
    (kindAutNat i j hij b0 b1) (FreeGroup.of k) = FreeGroup.of k := by
  unfold kindAutNat
  split_ifs <;> simp [rho_apply_other, rhoNeg_apply_other, lam_apply_other,
    lamNeg_apply_other, hk]

/-- A Nielsen letter fixes `signAut s (of k)` when `k ≠ i`. -/
lemma kindAutNat_apply_signAut_of_ne {i j : Fin r} (hij : i ≠ j) (b0 b1 : ℕ)
    (s : Fin r → Bool) (k : Fin r) (hk : k ≠ i) :
    (kindAutNat i j hij b0 b1) (signAut s (FreeGroup.of k)) = signAut s (FreeGroup.of k) := by
  rw [SigmaFacts.signAut_apply s k]
  by_cases hsk : s k
  · rw [if_pos hsk, map_inv, kindAutNat_apply_of_ne hij b0 b1 k hk]
  · rw [if_neg hsk, kindAutNat_apply_of_ne hij b0 b1 k hk]

/-- `signAut s` is an involution. -/
lemma signAut_invol (s : Fin r → Bool) (x : FreeGroup (Fin r)) :
    signAut s (signAut s x) = x := by
  have h : signAut s * signAut s = (1 : MulAut (FreeGroup (Fin r))) := by
    rw [← mul_inv_cancel (signAut s), SigmaFacts.signAut_inv]
  have := congrArg (fun f : MulAut (FreeGroup (Fin r)) => f x) h
  exact this

theorem signAutConj (r : ℕ) (s : Fin r → Bool) (i j : Fin r) (hij : i ≠ j)
    (b0 b1 : ℕ) (hb0 : b0 < 2) (hb1 : b1 < 2) :
    Submission.PTCert.signAut s * Submission.PTCert.kindAutNat i j hij b0 b1 *
        (Submission.PTCert.signAut s)⁻¹ =
      Submission.PTCert.kindAutNat i j hij (b0 ^^^ (if s i then 1 else 0))
        (b1 ^^^ (if s i then 1 else 0) ^^^ (if s j then 1 else 0)) := by
  rw [Submission.RouteB.mulAut_eq_iff]
  intro k
  have hL : (signAut s * kindAutNat i j hij b0 b1 * (signAut s)⁻¹) (FreeGroup.of k)
      = signAut s (kindAutNat i j hij b0 b1 (signAut s (FreeGroup.of k))) := by
    rw [SigmaFacts.signAut_inv]; rfl
  rw [hL]
  by_cases hki : k = i
  · interval_cases b0 <;> interval_cases b1 <;>
      by_cases hi : s i <;> by_cases hj : s j <;>
      (subst hki; simp [kindAutNat, hi, hj, SigmaFacts.signAut_apply,
         rho_apply_self, rhoNeg_apply_self, lam_apply_self, lamNeg_apply_self,
         map_inv, map_mul])
  · rw [kindAutNat_apply_signAut_of_ne hij b0 b1 s k hki, signAut_invol s (FreeGroup.of k)]
    exact (kindAutNat_apply_of_ne hij _ _ k hki).symm

end Work.PTCert
