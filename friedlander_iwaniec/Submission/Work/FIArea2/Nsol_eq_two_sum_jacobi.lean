import Mathlib
import Submission.Work.FIArea2.NsolDefs
import Submission.Work.FIArea2.Nsol_mul
import Submission.Work.FIArea2.card_solutions_two_power
import Submission.Work.FIArea2.card_solutions_eight_thirteen
import Submission.Work.FIArea2.two_mul_sum_four_dvd_eq

namespace Work.FIArea2

/-- **(*FI* Lemma 8.2, Corollary 8.3, (8.11) and (8.16))**: for `m ≠ 0`, `4 ∣ m`, `a ≡ 1 (mod 8)` and `(a,m) = 1`, the solution count `N(a;m)` of (8.8) equals `m · 2 ∑_{4d ∣ m} (φ(d)/d)(a/d)`.  This is the *correct* form of (8.16): the count `|Δ|G₀(z₁,z₂)` with the residue `a` of `z₂/z₁` (see `Cnt_eq_Nsol`), not with the symbol of `Re(z̄₁z₂)` — the frozen `Work.FIPlan.G0` uses the latter and is therefore not the count (`G0_defect`).

Proof sketch: `m = 2^ν m'` with `m'` odd; by CRT `N(a;m) = N(a;2^ν)·N(a;m')`; `N(a;2^ν) = ν·2^ν` is (8.11) (`card_solutions_two_power`); `N(a;m') = m' ∑_{d|m'}(φ(d)/d)(a/d)` is Corollary 8.3 (`card_solutions_eight_thirteen`); and `2 ∑_{4d|m}(φ(d)/d)(a/d) = ν ∑_{d|m'}(φ(d)/d)(a/d)`, an elementary regrouping which uses that Mathlib's `jacobiSym` ignores the power of two in its modulus (the extension (8.15)). -/
theorem Nsol_eq_two_sum_jacobi {m a : ℕ}
    (hm : m ≠ 0) (h4 : 4 ∣ m) (ha8 : a % 8 = 1) (hcop : Nat.Coprime a m) :
    (Nsol m a : ℝ) = (m : ℝ) * (2 *
      ∑ d ∈ (Finset.Icc 1 (m / 4 + 1)).filter (fun d => 4 * d ∣ m),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ)) := by
  -- factor `m = 2^ν · m'` with `m'` odd
  obtain ⟨ν, m', hm'odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have hν2 : 2 ≤ ν := by
    by_contra h
    have hlt : ν < 2 := by omega
    interval_cases ν
    · rw [pow_zero, one_mul] at hm_eq
      obtain ⟨t, ht⟩ := h4
      obtain ⟨k, hk⟩ := hm'odd
      omega
    · rw [pow_one] at hm_eq
      obtain ⟨t, ht⟩ := h4
      obtain ⟨k, hk⟩ := hm'odd
      omega
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm_eq
    exact hm hm_eq
  -- coprimality of `a` with the two factors
  have hdvd2 : 2 ^ ν ∣ m := by rw [hm_eq]; exact dvd_mul_right _ _
  have hdvdm' : m' ∣ m := by rw [hm_eq]; exact dvd_mul_left _ _
  have hcop2 : Nat.Coprime a (2 ^ ν) := hcop.coprime_dvd_right hdvd2
  have hcopm' : Nat.Coprime a m' := hcop.coprime_dvd_right hdvdm'
  have hcop2m' : Nat.Coprime (2 ^ ν) m' := ((Nat.coprime_two_left).mpr hm'odd).pow_left ν
  -- the two local factors: (8.11) and Corollary 8.3
  have hNsol2 : (Nsol (2 ^ ν) a : ℝ) = (ν : ℝ) * (2 : ℝ) ^ ν := by
    haveI : NeZero (2 ^ ν) := ⟨pow_ne_zero _ (by norm_num)⟩
    rw [Nsol_eq_filter (2 ^ ν) a]
    exact card_solutions_two_power ν a (by omega) ha8
  have hNsolm' : (Nsol m' a : ℝ) = Jsum m' (a : ℤ) := by
    haveI : NeZero m' := ⟨hm'0⟩
    rw [Nsol_eq_filter m' a]
    unfold Jsum
    exact card_solutions_eight_thirteen m' hm'odd a hcopm'
  -- the regrouping identity, `2 Σ_{4d|m} = ν Σ_{d|m'}`
  have hkey := two_mul_sum_four_dvd_eq hm_eq hm'odd hν2 ha8
  -- assemble
  have hNsolEq : (Nsol m a : ℝ) = (ν : ℝ) * (2 : ℝ) ^ ν *
      ((m' : ℝ) * ∑ d ∈ m'.divisors,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ)) := by
    rw [hm_eq, Nsol_mul a (2 ^ ν) m' hcop2m']
    push_cast
    rw [hNsol2, hNsolm']
    unfold Jsum
    ring
  have hmR : (m : ℝ) = (2 : ℝ) ^ ν * (m' : ℝ) := by rw [hm_eq]; push_cast; ring
  rw [hNsolEq, hmR, hkey]
  ring

end Work.FIArea2
