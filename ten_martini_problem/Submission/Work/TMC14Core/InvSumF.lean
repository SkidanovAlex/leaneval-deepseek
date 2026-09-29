import Mathlib
import Submission.Work.TMC14Core.InvSumAux
import Submission.Work.TMC14Core.wordSum_rec
import Submission.Work.TMC14Core.wordSum_zero
import Submission.Work.TMC14Core.wordSum_self
import Submission.Work.TMC14Core.Qprod_rec
import Submission.Work.TMC14Core.Qprod_diag
import Submission.Work.TMC14Core.pow_inv_eq

/-!
# `TMC14Core.InvSumF`

The word-inversion sum identity used in the trace computation of the Bloch matrix

`∑_f ω ^ (invCount (2m) f) = (-1)^m ω ^ (m*(3m+1)/2)`

where `f` runs over the `2m`-long words over `{(true,true),(false,true)} = {U,V}`
with exactly `m` letters `U`, and `ω` is a primitive `(2m+1)`-st root of unity.

The proof is a two-parameter recursion: writing `H(a,b) = Dprod ω a * wordSum ω (a+b) a`
with `Dprod ω a = ∏_{k=1}^a (1-ω^k)`, the first-letter decomposition
(`wordSum_rec`) gives `H(a,b) = H(a,b-1) + ω^b (1-ω^a) H(a-1,b)`, the same
recursion as `Qprod ω a b = ∏_{k=1}^a (1-ω^{b+k})` (`Qprod_rec`); both have the
same base cases (`wordSum_zero`, `wordSum_self`), so `H = Qprod`. At `(m,m)` this
is `Dprod ω m · wordSum ω (2m) m = Qprod ω m m`, and `Qprod_diag` evaluates the
right-hand side, `Dprod ω m ≠ 0` (primitivity, `hω2`) cancels it, and `pow_inv_eq`
converts `(ω^{m(m+1)/2})⁻¹` into `ω^{m(3m+1)/2}`.
-/

namespace Work.TMC14Core

theorem Dprod_succ (ω : ℂ) (a : ℕ) : Dprod ω (a+1) = (1 - ω^(a+1)) * Dprod ω a := by
  rw [Dprod, Dprod, Finset.prod_Icc_succ_top (by omega : 1 ≤ a + 1)]
  ring

/-- The key two-parameter identity: `Dprod ω a · wordSum ω (a+b) a = Qprod ω a b`. -/
theorem Hh_eq (ω : ℂ) :
    ∀ a b : ℕ, Dprod ω a * wordSum ω (a + b) a = Qprod ω a b := by
  intro a
  induction a with
  | zero =>
    intro b
    rw [Nat.zero_add, wordSum_zero]
    simp [Dprod, Qprod]
  | succ a ih =>
    intro b
    induction b with
    | zero =>
      rw [show a + 1 + 0 = a + 1 from by omega, wordSum_self (ω := ω), mul_one]
      simp [Dprod, Qprod]
    | succ b ihb =>
      have hrec := wordSum_rec ω (a+1+b) (a+1) (by omega)
      rw [show a + 1 + (b + 1) = (a + 1 + b) + 1 from by omega, hrec, mul_add]
      rw [show a + 1 - 1 = a from by omega]
      have hQA : Dprod ω a * wordSum ω (a + (b + 1)) a = Qprod ω a (b + 1) := ih (b+1)
      rw [show Dprod ω (a+1) * (ω ^ (a + 1 + b + 1 - (a + 1)) * wordSum ω (a + 1 + b) a)
            = ω ^ (b+1) * (1 - ω ^ (a+1)) * (Dprod ω a * wordSum ω (a + (b+1)) a) from by
            have hexp : a + 1 + b + 1 - (a + 1) = b + 1 := by omega
            have hidx2 : a + 1 + b = a + (b + 1) := by omega
            rw [Dprod_succ, hexp, hidx2]; ring]
      rw [hQA, ihb]
      have hqr' : Qprod ω (a+1) (b+1)
          = Qprod ω (a+1) b + ω ^ (b+1) * (1 - ω ^ (a+1)) * Qprod ω a (b+1) := by
        simpa using Qprod_rec ω (a+1) (b+1) (by omega) (by omega)
      rw [← hqr']

theorem InvSumF (ω : ℂ) (m : ℕ) (hω1 : ω ^ (2 * m + 1) = 1)
    (hω2 : ∀ j : ℕ, 0 < j → j ≤ 2 * m → ω ^ j ≠ 1) :
    ∑ f ∈ (Finset.univ : Finset (Fin (2 * m) → Bool × Bool)).filter
        (fun f => (∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
          (Finset.univ.filter (fun i => f i = (true, true))).card = m),
      ω ^ (invCount (2 * m) f) = (-1) ^ m * ω ^ (m * (3 * m + 1) / 2) := by
  have hH := Hh_eq ω m m
  rw [show m + m = 2*m from by omega] at hH
  rw [Qprod_diag ω m hω1] at hH
  have hDne : Dprod ω m ≠ 0 := by
    rw [Dprod, Finset.prod_ne_zero_iff]
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact sub_ne_zero.mpr (Ne.symm (hω2 k (by omega) (by omega)))
  have hH' : Dprod ω m * wordSum ω (2*m) m = Dprod ω m * ((-1)^m * (ω^(m*(m+1)/2))⁻¹) := by
    rw [hH]; ring
  have hW := mul_left_cancel₀ hDne hH'
  change wordSum ω (2 * m) m = (-1) ^ m * ω ^ (m * (3 * m + 1) / 2)
  rw [hW, pow_inv_eq ω m hω1]

end Work.TMC14Core
