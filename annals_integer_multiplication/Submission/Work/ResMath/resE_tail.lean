import Mathlib
import Submission.Work.ResMath.summable_exp_neg_affine_sq

/-!
# The Gaussian tail bound of paper Lemma 4.6

`Work.ResMath.killedGaussTail_le`: for `x ≥ 1`,

`∑_{n ∈ ℤ, n ≠ 0} e^{-2πx(|n| - 1/2)²} ≤ 2.000008 · e^{-πx/2}`.

This is the numerical estimate at the end of the proof of Lemma 4.6 of Harvey–van der Hoeven,
*Integer multiplication in time* `O(n log n)`: the series equals
`2 e^{-πx/2} ∑_{m ≥ 1} e^{-2πx m(m-1)} = 2 e^{-πx/2} (1 + O(e^{-4π}))`, and `e^{-4π} ≤ 1/260000`.
-/

set_option maxHeartbeats 800000

namespace Work.ResMath

/-- `e^{-4π} ≤ 1/260000`.  Proof: `4π ≥ 12.5`, `e^{-12} = (e^{-3})^4 ≤ (1/20)^4` and
`e^{-1/2} ≤ 8/13`; `(1/20)^4 · 8/13 = 1/260000`. -/
lemma exp_neg_four_pi_le : Real.exp (-4 * Real.pi) ≤ 1 / 260000 := by
  have hπ : (12.5 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_d20]
  have h1 : Real.exp (-4 * Real.pi) ≤ Real.exp (-12.5 : ℝ) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-12.5 : ℝ) = Real.exp (-12) * Real.exp (-(1 / 2) : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  have h3 : Real.exp (-12 : ℝ) = (Real.exp (-3)) ^ 4 := by
    rw [show (-12 : ℝ) = (4 : ℕ) * (-3) by norm_num, Real.exp_nat_mul]
  have h4 : Real.exp (-3 : ℝ) ≤ 1 / 20 := by
    have h : (20 : ℝ) ≤ Real.exp 3 := by
      have hh := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 9
      norm_num at hh
      linarith [hh]
    calc Real.exp (-3 : ℝ) = 1 / Real.exp 3 := by rw [Real.exp_neg]; ring
      _ ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) h
  have h5 : Real.exp (-(1 / 2) : ℝ) ≤ 8 / 13 := by
    have h : (13 / 8 : ℝ) ≤ Real.exp (1 / 2) := by
      have hh := Real.sum_le_exp_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num) 3
      norm_num at hh
      linarith [hh]
    calc Real.exp (-(1 / 2) : ℝ) = 1 / Real.exp (1 / 2) := by rw [Real.exp_neg]; ring
      _ ≤ 1 / (13 / 8) := one_div_le_one_div_of_le (by norm_num) h
      _ = 8 / 13 := by norm_num
  calc Real.exp (-4 * Real.pi) ≤ Real.exp (-12.5 : ℝ) := h1
    _ = Real.exp (-12) * Real.exp (-(1 / 2) : ℝ) := h2
    _ = (Real.exp (-3)) ^ 4 * Real.exp (-(1 / 2) : ℝ) := by rw [h3]
    _ ≤ (1 / 20) ^ 4 * (8 / 13) := by
        refine mul_le_mul (pow_le_pow_left₀ (Real.exp_nonneg _) h4 4) h5
          (Real.exp_nonneg _) (by norm_num)
    _ = 1 / 260000 := by norm_num

/-- **Lemma 4.6**, tail estimate: for `x ≥ 1`, `∑_{n ≠ 0} e^{-2πx(|n|-1/2)²} ≤ 2.000008 e^{-πx/2}`. -/
theorem killedGaussTail_le (x : ℝ) (hx : 1 ≤ x) :
    (∑' n : ℤ, if n = 0 then 0 else Real.exp (-(2 * Real.pi * x) * (|(n : ℝ)| - 1 / 2) ^ 2))
      ≤ 2.000008 * Real.exp (-(Real.pi * x / 2)) := by
  have hx0 : 0 < x := by linarith
  set F : ℤ → ℝ := fun n =>
    if n = 0 then 0 else Real.exp (-(2 * Real.pi * x) * (|(n : ℝ)| - 1 / 2) ^ 2) with hF
  -- summability of `F`
  have hsumm : Summable F := by
    rw [hF]
    have hmaj : Summable (fun n : ℤ => Real.exp (-(Real.pi * x / 2) * (n : ℝ) ^ 2)) := by
      have h := summable_exp_neg_affine_sq (Real.pi * x / 2) 0 (by positivity) (Nat.one_pos)
      simpa using h
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
    · by_cases hn : n = 0 <;> simp only [hn, ↓reduceIte] <;> positivity
    · by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        apply Real.exp_le_exp.mpr
        have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
          have h2 : (1 : ℤ) ≤ |n| := by
            have : 0 < |n| := abs_pos.mpr hn
            omega
          have h3 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h2
          simpa only [Int.cast_abs, Int.cast_one] using h3
        have hpoly : (n : ℝ) ^ 2 ≤ 4 * (|(n : ℝ)| - 1 / 2) ^ 2 := by
          have hsq : (|(n : ℝ)|) ^ 2 = (n : ℝ) ^ 2 := sq_abs _
          nlinarith [hsq, habs]
        have hstep := mul_le_mul_of_nonneg_left hpoly
          (by positivity : (0 : ℝ) ≤ Real.pi * x / 2)
        nlinarith [hstep]
  -- `F` is even
  have heven : Function.Even F := by
    intro n
    rw [hF]
    by_cases hn : n = 0
    · simp [hn]
    · have hneg : -n ≠ 0 := by omega
      simp only [hn, hneg, ↓reduceIte]
      congr 1
      push_cast
      rw [abs_neg]
  -- split off the two half-lines: `∑ F = 2 ∑_{n ≥ 1} F n`
  have hpair : (∑' n : ℤ, F n) = 2 * (∑' n : ℕ, F (((n + 1 : ℕ)) : ℤ)) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsumm,
      tsum_pnat_eq_tsum_succ (f := fun m : ℕ => F ((m : ℕ) : ℤ))]
    have h0 : F 0 = 0 := by rw [hF]; simp
    rw [h0]
    norm_num
  -- evaluation of the half-line terms
  have hterm : ∀ n : ℕ, F (((n + 1 : ℕ)) : ℤ) =
      Real.exp (-(Real.pi * x / 2)) *
        Real.exp (-(2 * Real.pi * x) * ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n
    have h1 : (((n + 1 : ℕ)) : ℤ) ≠ 0 := by omega
    rw [hF]
    simp only [h1, ↓reduceIte]
    have hcast : ((((n + 1 : ℕ)) : ℤ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    rw [← Real.exp_add]
    congr 1
    ring
  -- summability of the `ℕ`-indexed Gaussian tail
  have hg : Summable (fun n : ℕ =>
      Real.exp (-(2 * Real.pi * x) * ((n : ℝ) * ((n : ℝ) + 1)))) := by
    have hr1 : Real.exp (-4 * Real.pi * x) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos, hx0]
    refine Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (Real.exp_nonneg _) hr1)
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; norm_num
    · have hprod : 0 ≤ (2 * Real.pi * x) * (n : ℝ) * ((n : ℝ) - 1) :=
        mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg n)) (by
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith)
      nlinarith [hprod]
  -- the geometric tail bound
  have hgeom : (∑' n : ℕ, Real.exp (-(2 * Real.pi * x) * ((n : ℝ) * ((n : ℝ) + 1))))
      ≤ 1 + Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi)) := by
    rw [Summable.tsum_eq_zero_add hg]
    have hg0 : Real.exp (-(2 * Real.pi * x) * (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 1))) = 1 := by
      norm_num
    rw [hg0]
    have hr0 : (0 : ℝ) ≤ Real.exp (-4 * Real.pi) := Real.exp_nonneg _
    have hr1 : Real.exp (-4 * Real.pi) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    -- the geometric comparison
    have hgeosum : (∑' n : ℕ, (Real.exp (-4 * Real.pi)) ^ (n + 1))
        = Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi)) := by
      calc (∑' n : ℕ, (Real.exp (-4 * Real.pi)) ^ (n + 1))
          = ∑' n : ℕ, Real.exp (-4 * Real.pi) * (Real.exp (-4 * Real.pi)) ^ n :=
            tsum_congr (fun n => pow_succ' _ n)
        _ = Real.exp (-4 * Real.pi) * (∑' n : ℕ, (Real.exp (-4 * Real.pi)) ^ n) :=
            Summable.tsum_mul_left _ (summable_geometric_of_lt_one hr0 hr1)
        _ = Real.exp (-4 * Real.pi) * (1 - Real.exp (-4 * Real.pi))⁻¹ := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
        _ = Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi)) := by rw [div_eq_mul_inv]
    have hgj : Summable (fun n : ℕ => Real.exp (-(2 * Real.pi * x) *
        (((↑(n + 1) : ℝ)) * (((↑(n + 1) : ℝ)) + 1)))) :=
      hg.comp_injective (i := fun n : ℕ => n + 1) (hi := by intro a b hab; exact Nat.succ.inj hab)
    have htail : (∑' n : ℕ, Real.exp (-(2 * Real.pi * x) *
          (((↑(n + 1) : ℝ)) * (((↑(n + 1) : ℝ)) + 1))))
        ≤ ∑' n : ℕ, (Real.exp (-4 * Real.pi)) ^ (n + 1) := by
      have hgeo2 : Summable (fun n : ℕ => (Real.exp (-4 * Real.pi)) ^ (n + 1)) :=
        (summable_geometric_of_lt_one hr0 hr1).comp_injective
          (i := fun n : ℕ => n + 1) (hi := by intro a b hab; exact Nat.succ.inj hab)
      refine hgj.tsum_le_tsum (fun n => ?_) hgeo2
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h3 : (2 : ℝ) ≤ x * ((n : ℝ) + 2) := by nlinarith [hx, hnn]
      have h5 : 4 * Real.pi * ((n : ℝ) + 1)
          ≤ 2 * Real.pi * ((n : ℝ) + 1) * (x * ((n : ℝ) + 2)) := by
        have hc : (0 : ℝ) ≤ 2 * Real.pi * ((n : ℝ) + 1) := by positivity
        have hh := mul_le_mul_of_nonneg_left h3 hc
        linarith [hh]
      linarith [h5]
    rw [← hgeosum]
    linarith [htail]
  -- numerics: `2 (1 + r/(1-r)) ≤ 2.000008`
  have hnum : 2 * (1 + Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi))) ≤ 2.000008 := by
    have hr := exp_neg_four_pi_le
    have hr0 : (0 : ℝ) ≤ Real.exp (-4 * Real.pi) := Real.exp_nonneg _
    have hfrac : Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi)) ≤ 1 / 250000 := by
      rw [div_le_iff₀ (by linarith [hr] : (0 : ℝ) < 1 - Real.exp (-4 * Real.pi))]
      nlinarith [hr, hr0]
    linarith
  -- assembling
  have hhalf : (∑' n : ℕ, F (((n + 1 : ℕ)) : ℤ))
      ≤ Real.exp (-(Real.pi * x / 2)) * (1 + Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi))) := by
    calc (∑' n : ℕ, F (((n + 1 : ℕ)) : ℤ))
        = ∑' n : ℕ, Real.exp (-(Real.pi * x / 2)) *
            Real.exp (-(2 * Real.pi * x) * ((n : ℝ) * ((n : ℝ) + 1))) :=
          tsum_congr (fun n => hterm n)
      _ = Real.exp (-(Real.pi * x / 2)) *
            (∑' n : ℕ, Real.exp (-(2 * Real.pi * x) * ((n : ℝ) * ((n : ℝ) + 1)))) :=
          Summable.tsum_mul_left _ hg
      _ ≤ Real.exp (-(Real.pi * x / 2)) *
            (1 + Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi))) :=
          mul_le_mul_of_nonneg_left hgeom (Real.exp_nonneg _)
  rw [hpair]
  calc 2 * (∑' n : ℕ, F (((n + 1 : ℕ)) : ℤ))
      ≤ 2 * (Real.exp (-(Real.pi * x / 2)) *
            (1 + Real.exp (-4 * Real.pi) / (1 - Real.exp (-4 * Real.pi)))) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ ≤ 2 * (Real.exp (-(Real.pi * x / 2)) * (1 + 1 / 250000)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        linarith [exp_neg_four_pi_le, Real.exp_nonneg (-4 * Real.pi)]
    _ = 2.000008 * Real.exp (-(Real.pi * x / 2)) := by ring

end Work.ResMath
