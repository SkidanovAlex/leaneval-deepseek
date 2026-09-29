import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.lc_defs
import Submission.Work.C17I.subst_eval_abs
import Submission.Work.C17I.seventeen_subst_eval
import Submission.Work.C17I.sympSym_deriv_coeff_bound
import Submission.Work.C17I.pureB_coeff_bound
import Submission.Work.C17I.seventeen_coeff_bounds

namespace Work.C17I

open PowerSeries

noncomputable section

/-!
# The seventeen substituted series on the disc `‖z‖ ≤ 34/100`

`Work.C17I.seventeen_subst_eval` proves, for each of the seventeen series of Theorem C, that the
substituted series converges at the safe harbour point `p₀ = 1/4 + i/5` (whose norm is at most
`33/100`) to the `y`-series evaluated at `yC p₀`.

Here we need the *uniform* statement on the whole disc `‖z‖ ≤ 34/100`: the same proof goes
through with `ρ = 34/100` in place of `33/100`, because
`Σ_k ‖coeff_k sympY‖ ρ^k = ρ²/(1-ρ) = (34/100)²/(1 - 34/100) = 1156/6600 < 1/5`,
and the coefficient bounds for the seventeen entries hold at rate `R = 1/5`
(`Work.C17I.seventeen_coeff_bounds`).
-/

/-- The absolute series of `sympY` at radius `ρ = 34/100` sums to `(34/100)²/(1-34/100) < 1/5`. -/
private lemma sympY_abs_lt_fifth :
    (∑' k : ℕ, ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k)
      < 1 / 5 := by
  have hsum := sympY_norm_hasSum (ρ := 34 / 100) (by norm_num) (by norm_num)
  rw [hsum.tsum_eq]
  norm_num

theorem seventeen_subst_eval_disc (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) (ra rb rab r0 : ℤ) {C : ℝ} (hC : 0 < C)
    (hP : ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k) :
    ∀ i : Fin 17, ∀ z : ℂ, ‖z‖ ≤ (34 : ℝ) / 100 →
      HasSum (fun k : ℕ =>
          ((PowerSeries.coeff k
            ((Submission.CDTPlan.seventeen m n ra rb rab r0 i).subst Submission.CDT.sympY) : ℚ) : ℂ)
            * z ^ k)
        (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)
          * (Work.C17.yC z) ^ k) := by
  intro i z hz
  obtain ⟨C', hC', hb⟩ := seventeen_coeff_bounds m n ra rb rab r0 hC hP i
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hsum : HasSum
      (fun k : ℕ => ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k)
      (((34 : ℝ) / 100) ^ 2 / (1 - 34 / 100)) := sympY_norm_hasSum (by norm_num) (by norm_num)
  have hgS : Summable
      (fun k : ℕ => ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k) :=
    hsum.summable
  have hgR : (∑' k : ℕ,
      ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k) < 1 / 5 :=
    sympY_abs_lt_fifth
  have hg0 : PowerSeries.constantCoeff Submission.CDT.sympY = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Submission.CDT.coeff_sympY_zero
  have hkey := Work.C17I.subst_eval_abs
    (f := Submission.CDTPlan.seventeen m n ra rb rab r0 i) (g := Submission.CDT.sympY)
    (C := C') (R := 1 / 5) (ρ := 34 / 100) (z := z)
    hC'.le (by norm_num) (by norm_num) hg0 hb hgS hgR hz
  have hsymp : (∑' m : ℕ, ((PowerSeries.coeff m Submission.CDT.sympY : ℚ) : ℂ) * z ^ m)
      = Work.C17.yC z := (sympY_hasSum z hzlt).tsum_eq
  rw [hsymp] at hkey
  exact hkey

end

end Work.C17I
