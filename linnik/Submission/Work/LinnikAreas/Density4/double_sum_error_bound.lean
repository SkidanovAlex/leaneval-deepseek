import Mathlib
import Submission.Work.LinnikAreas.Density4.DoubleSumDefs
import Submission.Work.LinnikAreas.Density4.main_term_eq_double_sum
import Submission.Work.LinnikAreas.Density4.tsum_tail_bound
import Submission.Work.LinnikAreas.Density4.sum_tail_inv_sq_le

/-!
# The double-sum error bound (Linnik, `Density4`)

Error term for the double sum
`∑_{a ≤ Q} ∑_{b ∣ r} [a ⟂ r] μ(a) μ(b) ⌊Q/(a²b)⌋`
against its "main term" `Q · (∑'_a [a ⟂ r] μ(a)/a²) · (∑_{b ∣ r} μ(b)/b)`.

The three ingredients are proved in separate modules and imported here:

* `main_term_eq_double_sum` — the pure distributivity identity relating the main term to the
  double sum with the floor removed;
* `tsum_tail_bound` — summability of the infinite series and the tail estimate `≤ 1/Q`;
* `sum_tail_inv_sq_le` — the analytic bound `∑_{a > t} 1/a² ≤ 2/t` used for the floor error.
-/

namespace Work.LinnikAreas.Density4

open Finset

noncomputable section

lemma dseb_abs_floor_sub_le_one (x : ℝ) (hx : 0 ≤ x) : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma dseb_abs_floor_sub_le_self (x : ℝ) (hx : 0 ≤ x) : |(⌊x⌋₊ : ℝ) - x| ≤ x := by
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h2 : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma dseb_floor_cast_div_eq (Q b a : ℕ) :
    (((Q / (a ^ 2 * b) : ℕ)) : ℝ) = (⌊(Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))⌋₊ : ℝ) := by
  have h1 : (⌊(Q : ℝ) / (((a ^ 2 * b : ℕ)) : ℝ)⌋₊) = Q / (a ^ 2 * b) :=
    Nat.floor_div_eq_div Q (a ^ 2 * b)
  have h2 : (((a ^ 2 * b : ℕ)) : ℝ) = (a : ℝ) ^ 2 * (b : ℝ) := by push_cast; ring
  rw [h2] at h1
  exact (congrArg (fun n : ℕ => (n : ℝ)) h1).symm

lemma dseb_floor_error_sum_le (Q b : ℕ) (hQ : 1 ≤ Q) (hb : 1 ≤ b) :
    (∑ a ∈ Finset.Icc 1 Q,
        |(((Q / (a ^ 2 * b) : ℕ)) : ℝ) - (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))|)
      ≤ 3 * Real.sqrt (Q : ℝ) / Real.sqrt (b : ℝ) := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  set s : ℝ := Real.sqrt (Q : ℝ) / Real.sqrt (b : ℝ) with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    exact div_pos (Real.sqrt_pos_of_pos hQpos) (Real.sqrt_pos_of_pos hbpos)
  have hs2 : s ^ 2 = (Q : ℝ) / (b : ℝ) := by
    rw [hsdef, div_pow, Real.sq_sqrt hQpos.le, Real.sq_sqrt hbpos.le]
  have hkey : ∀ a : ℕ, (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ)) = (s / (a : ℝ)) ^ 2 := by
    intro a
    rw [div_pow, hs2, div_div]
    ring
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Q) (fun a : ℕ => s < (a : ℝ))]
  have hsmall : ∀ a ∈ (Finset.Icc 1 Q).filter (fun a : ℕ => ¬ s < (a : ℝ)),
      |(((Q / (a ^ 2 * b) : ℕ)) : ℝ) - (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))| ≤ 1 := by
    intro a _
    rw [dseb_floor_cast_div_eq Q b a]
    exact dseb_abs_floor_sub_le_one _ (by positivity)
  have hbig : ∀ a ∈ (Finset.Icc 1 Q).filter (fun a : ℕ => s < (a : ℝ)),
      |(((Q / (a ^ 2 * b) : ℕ)) : ℝ) - (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))| ≤ (s / (a : ℝ)) ^ 2 := by
    intro a _
    rw [dseb_floor_cast_div_eq Q b a, hkey a]
    exact dseb_abs_floor_sub_le_self _ (by positivity)
  have hcard : (((Finset.Icc 1 Q).filter (fun a : ℕ => ¬ s < (a : ℝ))).card : ℝ) ≤ s := by
    have hsub : (Finset.Icc 1 Q).filter (fun a : ℕ => ¬ s < (a : ℝ)) ⊆ Finset.Icc 1 ⌊s⌋₊ := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      obtain ⟨⟨ha1, _⟩, has⟩ := ha
      simp only [Finset.mem_Icc]
      refine ⟨ha1, ?_⟩
      have has' : (a : ℝ) ≤ s := not_lt.mp has
      have hlt : (a : ℝ) < (⌊s⌋₊ : ℝ) + 1 := lt_of_le_of_lt has' (Nat.lt_floor_add_one s)
      have hlt' : a < ⌊s⌋₊ + 1 := by exact_mod_cast hlt
      omega
    calc (((Finset.Icc 1 Q).filter (fun a : ℕ => ¬ s < (a : ℝ))).card : ℝ)
        ≤ ((Finset.Icc 1 ⌊s⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (⌊s⌋₊ : ℝ) := by rw [Nat.card_Icc]; simp
      _ ≤ s := Nat.floor_le hspos.le
  have htail := sum_tail_inv_sq_le Q hspos
  calc (∑ a ∈ (Finset.Icc 1 Q).filter (fun a : ℕ => s < (a : ℝ)),
          |(((Q / (a ^ 2 * b) : ℕ)) : ℝ) - (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))|)
        + ∑ a ∈ (Finset.Icc 1 Q).filter (fun a : ℕ => ¬ s < (a : ℝ)),
          |(((Q / (a ^ 2 * b) : ℕ)) : ℝ) - (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))|
      ≤ ∑ a ∈ (Finset.Icc 1 Q).filter (fun a : ℕ => s < (a : ℝ)), (s / (a : ℝ)) ^ 2
        + ∑ _a ∈ (Finset.Icc 1 Q).filter (fun a : ℕ => ¬ s < (a : ℝ)), (1 : ℝ) :=
        add_le_add (Finset.sum_le_sum hbig) (Finset.sum_le_sum hsmall)
    _ = s ^ 2 * ∑ a ∈ (Finset.Icc 1 Q).filter (fun a : ℕ => s < (a : ℝ)), 1 / (a : ℝ) ^ 2
        + (((Finset.Icc 1 Q).filter (fun a : ℕ => ¬ s < (a : ℝ))).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [div_pow, one_div, div_eq_mul_inv]
    _ ≤ s ^ 2 * (2 / s) + s := by
        refine add_le_add ?_ hcard
        exact mul_le_mul_of_nonneg_left htail (sq_nonneg s)
    _ = 3 * s := by
        field_simp
        ring
    _ = 3 * Real.sqrt (Q : ℝ) / Real.sqrt (b : ℝ) := by rw [hsdef]; ring

lemma abs_moebius_cast_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  have h2 : ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  rwa [Int.cast_abs, Int.cast_one] at h2

lemma abs_Bsum_le_SigHalf (r : ℕ) : |Bsum r| ≤ SigHalf r := by
  rw [Bsum, SigHalf]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun b hb => ?_
  have hb1 : 1 ≤ b := Nat.pos_of_mem_divisors hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have h1 : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := abs_moebius_cast_le_one b
  have hs : (1 : ℝ) ≤ Real.sqrt (b : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hb1
  have hsqrt_le : Real.sqrt (b : ℝ) ≤ (b : ℝ) := by
    nlinarith [Real.sq_sqrt hbpos.le, Real.sqrt_nonneg (b : ℝ), hs]
  calc |(ArithmeticFunction.moebius b : ℝ) / (b : ℝ)|
      = |(ArithmeticFunction.moebius b : ℝ)| / (b : ℝ) := by rw [abs_div, abs_of_pos hbpos]
    _ ≤ 1 / (b : ℝ) := div_le_div_of_nonneg_right h1 hbpos.le
    _ ≤ 1 / Real.sqrt (b : ℝ) := one_div_le_one_div_of_le (Real.sqrt_pos_of_pos hbpos) hsqrt_le

lemma dsebF_sub_dsebM_abs_le (Q r a b : ℕ) :
    |dsebF Q r a b - dsebM Q r a b| ≤
      |((Q / (a ^ 2 * b) : ℕ) : ℝ) - (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))| := by
  by_cases h : Nat.Coprime a r
  · simp only [dsebF, dsebM, if_pos h]
    rw [← mul_sub, abs_mul]
    have h3 : |(ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_moebius_cast_le_one a, abs_moebius_cast_le_one b,
        abs_nonneg (ArithmeticFunction.moebius a : ℝ),
        abs_nonneg (ArithmeticFunction.moebius b : ℝ)]
    exact le_trans (mul_le_mul_of_nonneg_right h3 (abs_nonneg _)) (le_of_eq (one_mul _))
  · simp only [dsebF, dsebM, if_neg h]
    simp

theorem double_sum_error_bound (Q r : ℕ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) :
    |(∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors,
        (if Nat.Coprime a r then
          (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ)
            * ((Q / (a ^ 2 * b) : ℕ) : ℝ)
         else 0))
      - (Q : ℝ) * ((∑' a : ℕ,
            if Nat.Coprime a r then (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2 else 0)
          * (∑ b ∈ r.divisors, (ArithmeticFunction.moebius b : ℝ) / (b : ℝ)))|
    ≤ 4 * Real.sqrt (Q : ℝ) * (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) := by
  have hmain : |(∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
      - (Q : ℝ) * ((∑' a : ℕ, dsebG r a) * Bsum r)|
      ≤ 4 * Real.sqrt (Q : ℝ) * SigHalf r := by
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
    have hsqQ : (1 : ℝ) ≤ Real.sqrt (Q : ℝ) := by
      rw [Real.one_le_sqrt]; exact_mod_cast hQ
    have hg : ∀ n : ℕ, |dsebG r n| ≤ 1 / (n : ℝ) ^ 2 := by
      intro n
      rw [dsebG]
      by_cases h : Nat.Coprime n r
      · rw [if_pos h, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
        exact div_le_div_of_nonneg_right (abs_moebius_cast_le_one n) (sq_nonneg (n : ℝ))
      · rw [if_neg h, abs_zero]
        positivity
    obtain ⟨-, htail⟩ := tsum_tail_bound Q hQ (dsebG r) hg
    have hB : |Bsum r| ≤ SigHalf r := abs_Bsum_le_SigHalf r
    have hSig : 0 ≤ SigHalf r := le_trans (abs_nonneg _) hB
    have hM := main_term_eq_double_sum Q r
    have hE : |(∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
          - (Q : ℝ) * ((∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r)|
        ≤ 3 * Real.sqrt (Q : ℝ) * SigHalf r := by
      rw [hM, ← Finset.sum_sub_distrib]
      have hinner : ∀ a ∈ Finset.Icc 1 Q,
          (∑ b ∈ r.divisors, dsebF Q r a b) - (∑ b ∈ r.divisors, dsebM Q r a b)
            = ∑ b ∈ r.divisors, (dsebF Q r a b - dsebM Q r a b) :=
        fun a _ => (Finset.sum_sub_distrib _ _).symm
      rw [Finset.sum_congr rfl hinner]
      calc |∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, (dsebF Q r a b - dsebM Q r a b)|
          ≤ ∑ a ∈ Finset.Icc 1 Q, |∑ b ∈ r.divisors, (dsebF Q r a b - dsebM Q r a b)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, |dsebF Q r a b - dsebM Q r a b| :=
            Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
        _ = ∑ b ∈ r.divisors, ∑ a ∈ Finset.Icc 1 Q, |dsebF Q r a b - dsebM Q r a b| :=
            Finset.sum_comm
        _ ≤ ∑ b ∈ r.divisors, 3 * Real.sqrt (Q : ℝ) / Real.sqrt (b : ℝ) := by
            refine Finset.sum_le_sum fun b hb => ?_
            calc ∑ a ∈ Finset.Icc 1 Q, |dsebF Q r a b - dsebM Q r a b|
                ≤ ∑ a ∈ Finset.Icc 1 Q,
                    |((Q / (a ^ 2 * b) : ℕ) : ℝ) - (Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ))| :=
                  Finset.sum_le_sum fun a _ => dsebF_sub_dsebM_abs_le Q r a b
              _ ≤ 3 * Real.sqrt (Q : ℝ) / Real.sqrt (b : ℝ) :=
                  dseb_floor_error_sum_le Q b hQ (Nat.pos_of_mem_divisors hb)
        _ = 3 * Real.sqrt (Q : ℝ) * SigHalf r := by
            rw [SigHalf, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b hb => ?_
            rw [one_div]
            ring
    have hT : (Q : ℝ) * |(∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a|
          * |Bsum r| ≤ SigHalf r := by
      calc (Q : ℝ) * |(∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a| * |Bsum r|
          ≤ (Q : ℝ) * (1 / (Q : ℝ)) * SigHalf r :=
            mul_le_mul (mul_le_mul_of_nonneg_left htail hQpos.le) hB (abs_nonneg _)
              (by positivity)
        _ = SigHalf r := by rw [mul_one_div, div_self (ne_of_gt hQpos), one_mul]
    have hdecomp : (∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
          - (Q : ℝ) * ((∑' n : ℕ, dsebG r n) * Bsum r)
        = ((∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
            - (Q : ℝ) * ((∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r))
          - (Q : ℝ) * (((∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a)
              * Bsum r) := by ring
    have hy : |(Q : ℝ) * (((∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a)
          * Bsum r)|
        = (Q : ℝ) * |(∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a| * |Bsum r| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hQpos.le]; ring
    rw [hdecomp]
    calc |((∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
            - (Q : ℝ) * ((∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r))
          - (Q : ℝ) * (((∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r)|
        ≤ |(∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
            - (Q : ℝ) * ((∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r)|
          + |(Q : ℝ) * (((∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r)| := by
          have hh := abs_sub_le ((∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
              - (Q : ℝ) * ((∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r)) 0
            ((Q : ℝ) * (((∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r))
          simpa using hh
      _ = |(∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebF Q r a b)
            - (Q : ℝ) * ((∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r)|
          + (Q : ℝ) * |(∑' n : ℕ, dsebG r n) - ∑ a ∈ Finset.Icc 1 Q, dsebG r a| * |Bsum r| := by
          rw [hy]
      _ ≤ 3 * Real.sqrt (Q : ℝ) * SigHalf r + SigHalf r := add_le_add hE hT
      _ ≤ 4 * Real.sqrt (Q : ℝ) * SigHalf r := by
          nlinarith [hSig, hsqQ, Real.sqrt_nonneg (Q : ℝ)]
  simpa only [dsebF, dsebG, Bsum, SigHalf] using hmain

end

end Work.LinnikAreas.Density4
