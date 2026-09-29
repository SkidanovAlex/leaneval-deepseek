import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMComp.RedC7T.conv_chain
import Submission.Work.TMC7Core.Scale.dens_succ_strictMono
import Submission.Work.TMC7Core.Scale.gap_of_dioph
import Submission.Work.TMC7Core.Scale.conv_cross_bound

namespace Work.TMC7Core.Scale

open GenContFract Finset

/-- **S2** of the lead C7 design (see `Submission/Work/TMC7Core/Scale/S2_GUIDE.md`):
continued-fraction convergents of a Diophantine `α`, dropped by one index.

The convergents `pₙ/qₙ` of `GenContFract.of α` are used, dropping index `0` so that the
denominators become strictly increasing (`dens_succ_strictMono`). Coprimality, the strict
approximation bound `< 1/q²` and the cross bound `|p_k/q_k - p_i/q_i| < 1/q_i²` come from the
determinant identity and the Leibniz alternating-series estimate (`conv_cross_bound`), while the
eventual denominator gap `q_{n+1} ≤ exp (b · q_n)` is `gap_of_dioph` applied to `DiophBelow α b`. -/
theorem conv_chain_rational (α : ℝ) (hα : Irrational α) (b : ℝ) (hb : 0 < b)
    (hD : Work.TMC7Core.DiophBelow α b) :
    ∃ (a : ℕ → ℤ) (q : ℕ → ℕ) (n₀ : ℕ), (∀ n, 1 ≤ q n) ∧ StrictMono q ∧
      (∀ n, Nat.Coprime (Int.natAbs (a n)) (q n)) ∧
      (∀ n, |α - (a n : ℝ) / (q n)| < 1 / ((q n : ℝ) ^ 2)) ∧
      (∀ i k, i < k → |(a k : ℝ) / (q k) - (a i : ℝ) / (q i)| < 1 / ((q i : ℝ) ^ 2)) ∧
      (∀ n, n₀ ≤ n → (q (n + 1) : ℝ) ≤ Real.exp (b * (q n : ℝ))) := by
  -- `α` irrational means its continued fraction never terminates
  have hterm : ¬ (GenContFract.of α).Terminates := by
    rw [GenContFract.terminates_iff_rat]
    rintro ⟨q, hq⟩
    exact hα ⟨q, hq.symm⟩
  have hv : ∀ n, ¬ (GenContFract.of α).TerminatedAt n := fun n hn => hterm ⟨n, hn⟩
  -- integral numerator/denominator sequences of the convergents
  obtain ⟨A, B, hA, hB, hB1⟩ := Work.TMComp.RedC7T.cf_num_den_integral α hv
  -- the shifted denominators are strictly increasing
  have hRmono : StrictMono (fun n => (B (n + 1) : ℝ)) := by
    intro a b hab
    simpa only [hB] using dens_succ_strictMono α hv hab
  have hBmono : StrictMono (fun n => B (n + 1)) := fun a b hab => Nat.cast_lt.mp (hRmono hab)
  -- the weak approximation bound, in the shape required by `gap_of_dioph`
  have hbd : ∀ m, |α - (A (m+1) : ℝ) / (B (m+1) : ℝ)|
      ≤ 1 / ((B (m+1) : ℝ) * (B (m+2) : ℝ)) := by
    intro m
    have h := GenContFract.abs_sub_convs_le (v := α) (n := m+1) (hv (m+1))
    rw [GenContFract.conv_eq_num_div_den, hA (m+1), hB (m+1), hB (m+2)] at h
    exact h
  -- the eventual gap between denominators
  obtain ⟨m₀, hm₀⟩ := gap_of_dioph α b hb (fun m => B (m+1)) (fun m => A (m+1))
    (fun m => hB1 (m+1)) hBmono hbd hD
  refine ⟨fun n => A (n+1), fun n => B (n+1), m₀, ?_, hBmono, ?_, ?_, ?_, ?_⟩
  · intro n; exact hB1 (n+1)
  · intro n; exact Work.TMComp.RedC7T.cf_num_den_coprime α hv A B hA hB (n+1)
  · intro n
    have h := Work.TMComp.RedC7T.cf_convs_lt_inv_dens_sq α hv (n+1)
    rw [GenContFract.conv_eq_num_div_den, hA (n+1), hB (n+1)] at h
    exact h
  · intro i k hik
    have h := conv_cross_bound α hv (i+1) (k+1) (by omega)
    rw [GenContFract.conv_eq_num_div_den (g := GenContFract.of α) (n := k+1),
        GenContFract.conv_eq_num_div_den (g := GenContFract.of α) (n := i+1),
        hA (k+1), hB (k+1), hA (i+1), hB (i+1), hB (i+1+1)] at h
    have hBpos : (0:ℝ) < (B (i+1) : ℝ) := by
      have := hB1 (i+1); exact_mod_cast (by omega : 0 < B (i+1))
    have hlt : (B (i+1) : ℝ) < (B (i+1+1) : ℝ) := hRmono (by omega)
    have h2 : 1 / ((B (i+1) : ℝ) * (B (i+1+1) : ℝ)) < 1 / ((B (i+1) : ℝ))^2 := by
      apply one_div_lt_one_div_of_lt
      · positivity
      · nlinarith [hBpos, hlt]
    exact lt_of_le_of_lt h h2
  · intro n hn; exact hm₀ n hn

end Work.TMC7Core.Scale
