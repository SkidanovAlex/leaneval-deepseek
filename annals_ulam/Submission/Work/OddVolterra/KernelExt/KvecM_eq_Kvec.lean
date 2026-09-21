import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.JM_eq_J
import Submission.Work.OddVolterra.KernelExt.Rnu_spec
import Submission.Work.OddVolterra.KernelExt.JM_diag

/-!
# The manifest kernel `KvecM` agrees with the paper's kernel `Kvec`

`Work.OddVolterra.KvecM` is `Work.OddVolterra.Kvec` with the two Abel numerators `J₁`, `J₂`
replaced by their manifest polynomial representatives `J1M`, `J2M` (the Bell recursion `Rnu`),
and `Kvec` uses the paper's numerators `J1`, `J2`, which on the diagonal `σ = s` are *defined* to
be the limit values and off the diagonal are the differentiated moment integrands.

The present file assembles the two halves already proved elsewhere:

* on the diagonal `σ = s`, `J1M = J1` and `J2M = J2` (`Work.OddVolterra.KernelExt.JM_diag`);
* off the diagonal `s < σ`, the same holds as soon as the radicand
  `Z = (σ-s)·(t+H(s,σ))·(L_σ(t)+L_s(t))` is positive (`Work.OddVolterra.KernelExt.JM_eq_J`, whose engine is
  `Work.OddVolterra.KernelExt.Rnu_spec`, plus the pointwise identity `Z^{n+1/2} = Z^n√Z` on `{Z > 0}`).

Since the common denominator `Kden` is the same in `K1M/K1` and `K2M/K2`, dividing the numerator
identity by `Kden` gives `K1M = K1` and `K2M = K2`; the two components of the vectors
`![- (K₁(-x)x' + K₁(y)y'), - (K₂(-x)x' + K₂(y)y')]` then match term by term.  The hypotheses
`hR1`, `hR2` are exactly the paper's positivity requirements at the two endpoints `t = y` and
`t = -x`, and they are what rules out the degenerate `σ < s` case (where `Z < 0` and the paper's
numerators would be `0` while the manifest ones are not).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.KernelExt

open Work.OddVolterra

noncomputable section

/-- If the paper's last factor is positive, the manifest and the paper's first kernel agree.
On the diagonal this is vacuous (`JM_diag`); off the diagonal it is the numerator identity
`J1M = J1` divided by the common denominator `Kden`. -/
lemma K1M_eq_K1_of_le (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ}
    (hsσ : s ≤ σ) (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    K1M n h s σ t = K1 n h s σ t := by
  rcases eq_or_lt_of_le hsσ with heq | hlt
  · subst heq
    rw [K1M, K1, (Work.OddVolterra.KernelExt.JM_diag n hh s t).1]
  · rw [K1M, K1, J1M_eq_J1 n hh hlt hR]

/-- If the paper's last factor is positive, the manifest and the paper's second kernel agree.
Off the diagonal the hypothesis `1 ≤ n` is needed, see `Work.OddVolterra.KernelExt.J2M_eq_J2`. -/
lemma K2M_eq_K2_of_le (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ}
    (hsσ : s ≤ σ) (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    K2M n h s σ t = K2 n h s σ t := by
  rcases eq_or_lt_of_le hsσ with heq | hlt
  · subst heq
    rw [K2M, K2, (Work.OddVolterra.KernelExt.JM_diag n hh s t).2]
  · rw [K2M, K2, J2M_eq_J2 n hn hh hlt hR]

theorem KvecM_eq_Kvec (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ : ℝ}
    (hsσ : s ≤ σ) (x y x' y' : ℝ)
    (hR1 : 0 < (y + Work.OddVolterra.hquot h s σ) *
      (Work.OddVolterra.line h σ y + Work.OddVolterra.line h s y))
    (hR2 : 0 < (-x + Work.OddVolterra.hquot h s σ) *
      (Work.OddVolterra.line h σ (-x) + Work.OddVolterra.line h s (-x))) :
    Work.OddVolterra.KernelExt.KvecM n h s σ x y x' y' =
      Work.OddVolterra.Kvec n h s σ x y x' y' := by
  have h1y : K1M n h s σ y = K1 n h s σ y := K1M_eq_K1_of_le n hh hsσ hR1
  have h1x : K1M n h s σ (-x) = K1 n h s σ (-x) := K1M_eq_K1_of_le n hh hsσ hR2
  have h2y : K2M n h s σ y = K2 n h s σ y := K2M_eq_K2_of_le n hn hh hsσ hR1
  have h2x : K2M n h s σ (-x) = K2 n h s σ (-x) := K2M_eq_K2_of_le n hn hh hsσ hR2
  simp only [KvecM, Kvec, h1y, h1x, h2y, h2x]

end

end Work.OddVolterra.KernelExt
