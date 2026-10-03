/-
# `Work.FIChain.remainder_all_at_07` — `(R′)` for `ã` at the cutoff `⌈x^{7/10}⌉`

The companion of `Work.FIChain.remainder_all`: the `(R′)`-estimate for the honest remainder
`r̃_full` of the squarefree-supported sequence `ã` at the **larger** modulus cutoff
`D₇(x) = ⌈x^{7/10}⌉` instead of `Rcut x = ⌊x^{11/16}⌋`.

Since `RemainderSum r D m` is monotone in `D`, this is strictly stronger than `remainder_all`,
so the proof cannot reuse the `(R′)`-input at `Rcut`: one needs the `τ⁰`-weighted `(R)` for `ã`
at the bigger modulus.  The route is the paper's §9:

* the §9 split point is a *polylogarithmic* `L = ⌈(log x)^N⌉`, chosen so that
  (i) `D₇·L² ≤ x^{141/200}` stays below the `x^{3/4}`-barrier where Proposition 3.5 and the
  `4 ∣ d` estimates of `Submission.ASP.S21` still give an `x`-power saving, and
  (ii) `(log x)^{8λ+100} ≤ L` holds for the (fixed, arbitrary) `λ` needed by the Hölder step;
* the `E₁`-part of §9 is bounded by the `x`-power-saving cubefree bounds
  `Submission.Work.FIChain.{rMain_cubefree_not4_le, rMain_cubefree_four_dvd_le,
  cubefree_tau_sq_FIr_le, Eone_le_at_07}`, and the `E₂`-part by `Etwo_le_at_07`;
* the Hölder step `τ⁵ = (τ^{20/3})^{3/4}·1^{1/4}` against `(2.3)` and `(R)`-for-`ã` is
  `Submission.Work.FIChain.{rtildeFull_D7_le, RemainderSum_large_at_07}`;
* the scales `m < D₇` are handled crudely by `Submission.Work.FIChain.small_m_at_07`.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40
import Submission.ASP.S31
import Submission.ASP.S22
import Submission.ASP.S21
import Submission.ASP.S35
import Submission.ASP.S36
import Submission.ASP.S34
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.ASP.S9d
import Submission.ASP.S37
import Submission.ASP_R3
import Submission.Work.FIChain.rMain_cubefree_not4_le
import Submission.Work.FIChain.rMain_cubefree_four_dvd_le
import Submission.Work.FIChain.cubefree_tau_sq_FIr_le
import Submission.Work.FIChain.Eone_le_at_07
import Submission.Work.FIChain.Etwo_le_at_07
import Submission.Work.FIChain.rtildeFull_D7_le
import Submission.Work.FIChain.RemainderSum_large_at_07
import Submission.Work.FIChain.small_m_at_07

set_option maxHeartbeats 4000000

namespace Work.FIChain

open Finset Filter
open Submission.ASP
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The cutoff `D₇(x) = ⌈x^{7/10}⌉` of the present chapter. -/
def D7 (x : ℕ) : ℕ := ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊

theorem remainder_all_at_07 :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, m ≤ x →
      Submission.ASP.RemainderSum (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
          Submission.ASP.FIgtil Submission.ASP.FIa) (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) m
        ≤ Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
  obtain ⟨C23, B23, X23, hC23, h23⟩ := Submission.ASP.Atil_tau_pow_remainder_le
  set lam : ℝ := 3 * max B23 0 + 13 with hlamdef
  obtain ⟨Xr, CR, hCR, hR⟩ := rtildeFull_D7_le lam
  have h23' : ∀ x : ℕ, ⌈X23⌉₊ ≤ x → ∀ m : ℕ, 2 ≤ m → m ≤ x → ∀ D : ℕ, D ≤ m →
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
          * |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa d m|)
        ≤ C23 * ((Submission.Aseq x : ℝ)
            + Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (x : ℝ))
          * (Real.log (x : ℝ)) ^ B23 := by
    intro x hx m hm2 hmx D hD
    exact h23 x (le_trans (Nat.le_ceil X23) (by exact_mod_cast hx)) m hm2 hmx D hD
  obtain ⟨Xl, hl⟩ := RemainderSum_large_at_07 C23 B23 CR lam hC23 hCR ⌈X23⌉₊ Xr h23' hR hlamdef
  have hlarge : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ,
      ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ m → m ≤ x →
      Submission.ASP.RemainderSum (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
          Submission.ASP.FIgtil Submission.ASP.FIa) (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) m
        ≤ Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (x : ℝ)
            * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) :=
    ⟨Xl, fun x hx m hmD hmx => hl x hx m hmD hmx⟩
  exact small_m_at_07 hlarge

end

end Work.FIChain
