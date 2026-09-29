import Submission.CDT.InfinityBound

/-!
# The reduction of the ansatz to a divisibility condition

Two structural facts used in the final step of Lemma `14functions`:

* `dnum` is linear in its first argument (`dnum_add`, `dnum_smul`), so the
  cascaded numerator `POLYq Q` for a general `Q = q₀ + q₁y + q₂y²` is the
  corresponding linear combination of the three specialised numerators;
* `cub⁵ ∣ POLYq Q` whenever the cleared identity
  `POLYq Q · y² = w⁴·cub⁵·Rnum` holds (`cub_pow_five_dvd_POLYq`), because
  `cub` is a unit modulo `X` (`cub_bezout_X`, `IsCoprime cub X`).

This reduces the final contradiction to a *linear-algebra* statement about
`POLYq (y^k) %ₘ cub⁵` (`k ≤ 2`): their remainders are linearly independent, so
`q₀ = q₁ = q₂ = 0` and hence `Rnum = 0`.
-/

open Classical

noncomputable section
namespace Submission.CDT

open Polynomial

namespace FrobeniusApply
open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC
set_option maxHeartbeats 1600000

/-- `dnum` is additive in its first argument. -/
lemma dnum_add (p₁ p₂ q : Polynomial ℂ) (j : ℕ) :
    dnum (p₁ + p₂) q j = dnum p₁ q j + dnum p₂ q j := by
  induction j with
  | zero => simp [dnum]
  | succ j ih =>
    rw [dnum_succ, dnum_succ, dnum_succ, ih]
    simp only [Polynomial.derivative_add]
    ring

/-- `dnum` is `ℂ`-homogeneous in its first argument. -/
lemma dnum_smul (c : ℂ) (p q : Polynomial ℂ) (j : ℕ) :
    dnum (Polynomial.C c * p) q j = Polynomial.C c * dnum p q j := by
  induction j with
  | zero => simp [dnum]
  | succ j ih =>
    rw [dnum_succ, dnum_succ, ih]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
    ring

/-- The Bezout identity `−cub + (144X² − 122X + 118)·X = 1`. -/
lemma cub_bezout_X : (-1 : Polynomial ℂ) * cub
    + (144 * Polynomial.X ^ 2 - 122 * Polynomial.X + 118) * Polynomial.X = 1 := by
  unfold cub y; ring

/-- `IsCoprime cub X`: the cubic is a unit modulo `X` since `cub(0) = −1`. -/
lemma isCoprime_cub_X : IsCoprime cub (Polynomial.X : Polynomial ℂ) :=
  ⟨-1, 144 * Polynomial.X ^ 2 - 122 * Polynomial.X + 118, cub_bezout_X⟩

/-- `cub⁵` divides the cascaded numerator `POLYq Q` whenever the identity
`POLYq Q · y² = w⁴·cub⁵·Rnum` holds. -/
lemma cub_pow_five_dvd_POLYq (Q Rnum : Polynomial ℂ)
    (h : POLYq Q * Polynomial.X ^ 2 = w ^ 4 * cub ^ 5 * Rnum) :
    cub ^ 5 ∣ POLYq Q := by
  have hdvd : cub ^ 5 ∣ POLYq Q * Polynomial.X ^ 2 :=
    ⟨w ^ 4 * Rnum, by rw [h]; ring⟩
  have hcop : IsCoprime (cub ^ 5) ((Polynomial.X : Polynomial ℂ) ^ 2) :=
    isCoprime_cub_X.pow (m := 5) (n := 2)
  exact hcop.dvd_of_dvd_mul_right hdvd

end FrobeniusApply
end Submission.CDT
