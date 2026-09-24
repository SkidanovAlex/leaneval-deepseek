/-
# Monotonicity and continuity of the Rosser–Iwaniec profile pair `riPhi`, `riPsi`

`APSwitchUpper.riPhi s = F(s) − 1 = Σ_j profC (2j) s` and
`APSwitchUpper.riPsi s = 1 − f(s) = Σ_j profC (2j+1) s` are the two infinite sums of the
delay-difference family `profC j = f_{j+1}` of the sharp linear sieve.

The two structural facts needed downstream are

* `riPhi` is non-increasing on `[1, ∞)` and `riPsi` on `[2, ∞)`
  (`profC_antitone_even` / `profC_antitone` for each summand, then a limit argument);
* `riPhi` is continuous on `[1, ∞)` and `riPsi` on `[2, ∞)`.

Both are proved here from two inputs the bookkeeping of the sieve already supplies:

* `ApSumTenth.profC_continuousOn`: continuity of each summand on the parity-correct half-line;
* `APSwitchUpper.profC_le_decay`: the uniform geometric bound
  `profC j σ ≤ 20 · (97/100)^j · errH σ` for `σ ≥ 1`, together with `errH σ ≤ e^{−2}`.

The geometric bound is summable, so Weierstrass' M-test (`continuousOn_tsum`) gives continuity;
monotonicity of the sum follows from monotonicity of the (nonnegative) partial sums together
with convergence of all the sums involved.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_antitone
import Submission.Work.NumberTheory.Chen.ApSumTenth.profC_continuousOn
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay

namespace Work.NumberTheory.Chen.BTermCount

open Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-! ## §1  An elementary bound on the error profile -/

/-- `errH` never exceeds its value `e^{−2}` at the left end of the range. -/
private lemma errH_le_exp_neg_two (s : ℝ) : errH s ≤ Real.exp (-2) := by
  by_cases h : s ≤ 2
  · rw [errH_of_le_two h]
  · rw [not_le] at h
    by_cases h3 : s ≤ 3
    · rw [errH_of_between h h3]
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [not_le] at h3
      rw [errH_of_three_lt h3]
      have hspos : 0 < s := by linarith
      have h1 : 3 / s ≤ 1 := by
        rw [div_le_one hspos]; linarith
      calc 3 * Real.exp (-s) / s = (3 / s) * Real.exp (-s) := by ring
        _ ≤ 1 * Real.exp (-s) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = Real.exp (-s) := one_mul _
        _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)

/-! ## §2  The geometric majorant and the pointwise bounds -/

/-- The summable majorant of the family on the half-lines at issue. -/
private lemma summable_major :
    Summable (fun n : ℕ => 20 * (((97:ℝ)/100)^2)^n * Real.exp (-2)) := by
  have h2 : Summable (fun n : ℕ => (((97:ℝ)/100)^2)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h3 := h2.mul_left (20 * Real.exp (-2))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h3

private lemma major_nonneg (n : ℕ) : (0:ℝ) ≤ 20 * (((97:ℝ)/100)^2)^n * Real.exp (-2) := by
  positivity

/-- Even-indexed summand bound: `profC (2n) σ ≤ 20·(97/100)^{2n}·e^{−2}` on `[1, ∞)`. -/
private lemma profC_even_le (n : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    profC (2 * n) x ≤ 20 * (((97:ℝ)/100)^2)^n * Real.exp (-2) := by
  have h := profC_le_decay (2 * n) x hx
  rw [pow_mul] at h
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_left (errH_le_exp_neg_two x) (by positivity)

/-- Odd-indexed summand bound: `profC (2n+1) σ ≤ 20·(97/100)^{2n}·e^{−2}` on `[1, ∞)`
(the odd summands are dominated by the even ones because `97/100 ≤ 1`). -/
private lemma profC_odd_le (n : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    profC (2 * n + 1) x ≤ 20 * (((97:ℝ)/100)^2)^n * Real.exp (-2) := by
  have h := profC_le_decay (2 * n + 1) x hx
  have hpow : ((97:ℝ)/100)^(2 * n + 1) ≤ (((97:ℝ)/100)^2)^n := by
    have hstep : ((97:ℝ)/100)^(2 * n + 1) ≤ ((97:ℝ)/100)^(2 * n) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ (2 * n))
    rwa [pow_mul] at hstep
  refine le_trans h ?_
  calc 20 * ((97:ℝ)/100)^(2 * n + 1) * errH x
      ≤ 20 * (((97:ℝ)/100)^2)^n * errH x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (errH_nonneg x)
    _ ≤ 20 * (((97:ℝ)/100)^2)^n * Real.exp (-2) :=
        mul_le_mul_of_nonneg_left (errH_le_exp_neg_two x) (by positivity)

/-! ## §3  Summability of the two profiles -/

private lemma summable_profC_even (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun i : ℕ => profC (2 * i) x) :=
  Summable.of_nonneg_of_le (fun i => profC_nonneg (2 * i) x)
    (fun i => profC_even_le i x hx) summable_major

private lemma summable_profC_odd (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun i : ℕ => profC (2 * i + 1) x) :=
  Summable.of_nonneg_of_le (fun i => profC_nonneg (2 * i + 1) x)
    (fun i => profC_odd_le i x hx) summable_major

/-! ## §4  Monotonicity of a nonnegative sum of monotone functions -/

private lemma antitoneOn_tsum {f : ℕ → ℝ → ℝ} {s : Set ℝ}
    (hanti : ∀ i, AntitoneOn (f i) s)
    (hnn : ∀ i x, 0 ≤ f i x)
    (hsum : ∀ x ∈ s, Summable (fun i => f i x)) :
    AntitoneOn (fun x => ∑' i, f i x) s := by
  intro a ha b hb hab
  show (∑' i, f i b) ≤ ∑' i, f i a
  refine le_of_tendsto' (hsum b hb).hasSum.tendsto_sum_nat (fun N => ?_)
  calc ∑ i ∈ Finset.range N, f i b ≤ ∑ i ∈ Finset.range N, f i a :=
        Finset.sum_le_sum (fun i _ => hanti i ha hb hab)
    _ ≤ ∑' i, f i a := Summable.sum_le_tsum _ (fun i _ => hnn i a) (hsum a ha)

/-! ## §5  The four statements -/

theorem riPhi_antitone : AntitoneOn riPhi (Set.Ici (1 : ℝ)) :=
  antitoneOn_tsum (f := fun i : ℕ => fun x : ℝ => profC (2 * i) x)
    (fun i => profC_antitone_even (2 * i) (by omega))
    (fun i x => profC_nonneg (2 * i) x)
    (fun x hx => summable_profC_even x (Set.mem_Ici.mp hx))

theorem riPsi_antitone : AntitoneOn riPsi (Set.Ici (2 : ℝ)) :=
  antitoneOn_tsum (f := fun i : ℕ => fun x : ℝ => profC (2 * i + 1) x)
    (fun i => profC_antitone (2 * i + 1))
    (fun i x => profC_nonneg (2 * i + 1) x)
    (fun x hx => summable_profC_odd x (le_trans (by norm_num) (Set.mem_Ici.mp hx)))

theorem riPhi_continuousOn : ContinuousOn riPhi (Set.Ici (1 : ℝ)) :=
  continuousOn_tsum
    (f := fun i : ℕ => fun x : ℝ => profC (2 * i) x)
    (u := fun n : ℕ => 20 * (((97:ℝ)/100)^2)^n * Real.exp (-2))
    (fun i => Work.NumberTheory.Chen.ApSumTenth.profC_continuousOn.1 (2 * i) (by omega))
    summable_major
    (fun n x hx => by
      rw [Real.norm_of_nonneg (profC_nonneg (2 * n) x)]
      exact profC_even_le n x (Set.mem_Ici.mp hx))

theorem riPsi_continuousOn : ContinuousOn riPsi (Set.Ici (2 : ℝ)) :=
  continuousOn_tsum
    (s := Set.Ici (2 : ℝ))
    (f := fun i : ℕ => fun x : ℝ => profC (2 * i + 1) x)
    (u := fun n : ℕ => 20 * (((97:ℝ)/100)^2)^n * Real.exp (-2))
    (fun i => Work.NumberTheory.Chen.ApSumTenth.profC_continuousOn.2 (2 * i + 1) (by omega))
    summable_major
    (fun n x hx => by
      rw [Real.norm_of_nonneg (profC_nonneg (2 * n + 1) x)]
      exact profC_odd_le n x (le_trans (by norm_num) (Set.mem_Ici.mp hx)))

theorem riSys_antitone_continuous :
    AntitoneOn Work.NumberTheory.Chen.APSwitchUpper.riPhi (Set.Ici (1 : ℝ))
      ∧ AntitoneOn Work.NumberTheory.Chen.APSwitchUpper.riPsi (Set.Ici (2 : ℝ))
      ∧ ContinuousOn Work.NumberTheory.Chen.APSwitchUpper.riPhi (Set.Ici (1 : ℝ))
      ∧ ContinuousOn Work.NumberTheory.Chen.APSwitchUpper.riPsi (Set.Ici (2 : ℝ)) :=
  ⟨riPhi_antitone, riPsi_antitone, riPhi_continuousOn, riPsi_continuousOn⟩

end

end Work.NumberTheory.Chen.BTermCount
