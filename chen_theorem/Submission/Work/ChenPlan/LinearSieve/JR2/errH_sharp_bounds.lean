import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Work.NumberTheory.Chen.APSwitchUpper.errH_transport

namespace Work.ChenPlan.LinearSieve.JR2

open MeasureTheory Set
open Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-! ## §1  Elementary pointwise facts about `errH` -/

/-- The profile is dominated by the pure exponential `e^{-u}` everywhere. -/
private lemma errH_le_exp_neg_aux (u : ℝ) : errH u ≤ Real.exp (-u) := by
  rcases le_or_gt u 2 with h | h
  · rw [errH_of_le_two h]; exact Real.exp_le_exp.mpr (by linarith)
  · rcases le_or_gt u 3 with h3 | h3
    · rw [errH_of_between h h3]
    · rw [errH_of_three_lt h3, div_le_iff₀ (by linarith : (0:ℝ) < u)]
      nlinarith [Real.exp_pos (-u)]

/-- `errH u ≤ e^{-2}` for every `u`: on `(-∞,2]` this is an equality, on `[2,3]` it is
`e^{-u} ≤ e^{-2}`, and for `u ≥ 3` it is `3/u ≤ e^{u-2}`, true because `3/u ≤ 1 ≤ e^{u-2}`. -/
private lemma errH_le_exp_neg_two_aux (u : ℝ) : errH u ≤ Real.exp (-2) := by
  rcases le_or_gt u 2 with h | h
  · rw [errH_of_le_two h]
  · rcases le_or_gt u 3 with h3 | h3
    · rw [errH_of_between h h3]; exact Real.exp_le_exp.mpr (by linarith)
    · rw [errH_of_three_lt h3, div_le_iff₀ (by linarith : (0:ℝ) < u)]
      have h1 : Real.exp (-u) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-3) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.exp_pos (-u), Real.exp_pos (-3), Real.exp_pos (-2), h1, h2]

/-- `e^{-3} ≤ errH s` for `s ≤ 3`. -/
private lemma exp_neg_three_le_errH_aux {s : ℝ} (hs : s ≤ 3) : Real.exp (-3) ≤ errH s := by
  rcases le_or_gt s 2 with h | h
  · rw [errH_of_le_two h]; exact Real.exp_le_exp.mpr (by linarith)
  · rw [errH_of_between h hs]; exact Real.exp_le_exp.mpr (by linarith)

/-! ## §2  `errH` is non-increasing on the whole line -/

/-- `errH` is non-increasing on `[2,∞)`. -/
private lemma errH_antitone_ge_two_aux :
    ∀ a b : ℝ, 2 ≤ a → a ≤ b → errH b ≤ errH a := by
  intro a b ha hab
  rcases le_or_gt b 3 with hb3 | hb3
  · rw [errH_eq_exp_neg ha (le_trans hab hb3), errH_eq_exp_neg (le_trans ha hab) hb3]
    exact Real.exp_le_exp.mpr (by linarith)
  · rcases le_or_gt a 3 with ha3 | ha3
    · -- `errH b = 3e^{-b}/b ≤ e^{-b} ≤ e^{-3} ≤ errH a`
      have hb3' : (3:ℝ) ≤ b := le_of_lt hb3
      have hkey : errH b ≤ Real.exp (-3) := by
        rw [errH_of_three_lt hb3]
        have hb0 : (0:ℝ) < b := by linarith
        rw [div_le_iff₀ hb0]
        have h1 : Real.exp (-b) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
        nlinarith [Real.exp_pos (-b), Real.exp_pos (-3), h1, hb3']
      exact le_trans hkey (exp_neg_three_le_errH_aux ha3)
    · -- both arguments are `≥ 3`: multiply through by `a·b > 0`
      have ha3' : (3:ℝ) < a := ha3
      rw [errH_of_three_lt ha3', errH_of_three_lt hb3]
      have hap : (0:ℝ) < a := by linarith
      have hbp : (0:ℝ) < b := by linarith
      have h1 : a * Real.exp (-b) ≤ b * Real.exp (-b) :=
        mul_le_mul_of_nonneg_right hab (Real.exp_pos (-b)).le
      have h2 : b * Real.exp (-b) ≤ b * Real.exp (-a) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hbp.le
      have h3 : a * Real.exp (-b) ≤ b * Real.exp (-a) := le_trans h1 h2
      rw [div_le_div_iff₀ hbp hap]
      nlinarith [h3]

/-- `errH` is non-increasing on all of `ℝ`. -/
private lemma errH_antitone_aux : ∀ a b : ℝ, a ≤ b → errH b ≤ errH a := by
  intro a b hab
  rcases le_or_gt 2 a with ha | ha
  · exact errH_antitone_ge_two_aux a b ha hab
  · rcases le_or_gt 2 b with hb | hb
    · rw [errH_of_le_two (by linarith : a ≤ 2)]
      exact errH_le_exp_neg_two_aux b
    · rw [errH_of_le_two (le_trans hab hb.le), errH_of_le_two hb.le]

/-! ## §3  The left-end sharp bound `∫_2^∞ errH ≤ (47/50) e^{-2}` -/

private lemma integral_Ioi_two_errH_le_aux :
    (∫ u in Set.Ioi (2:ℝ), errH u) ≤ (47/50) * Real.exp (-2) := by
  have hInt2 : IntegrableOn errH (Set.Ioi (2:ℝ)) := integrableOn_errH_Ioi (by norm_num)
  have hsplit : (∫ u in Set.Ioi (2:ℝ), errH u) - (∫ u in Set.Ioi (3:ℝ), errH u)
      = ∫ u in (2:ℝ)..3, errH u :=
    intervalIntegral.integral_Ioi_sub_Ioi hInt2 (by norm_num)
  have h23 : (∫ u in (2:ℝ)..3, errH u) = Real.exp (-2) - Real.exp (-3) := by
    have hcong : (∫ u in (2:ℝ)..3, errH u) = ∫ u in (2:ℝ)..3, Real.exp (-u) := by
      refine intervalIntegral.integral_congr ?_
      intro u hu
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] at hu
      exact errH_eq_exp_neg hu.1 hu.2
    rw [hcong]
    have h := intervalIntegral.integral_Ioi_sub_Ioi
      (f := fun u : ℝ => Real.exp (-u)) (a := (2:ℝ)) (b := (3:ℝ))
      (integrableOn_exp_neg_Ioi 2) (by norm_num)
    rw [integral_exp_neg_Ioi, integral_exp_neg_Ioi] at h
    linarith
  have hI3 : (∫ u in Set.Ioi (3:ℝ), errH u) ≤ Real.exp (-3) - (3/50) * Real.exp (-2) := by
    have hcong : (∫ u in Set.Ioi (3:ℝ), errH u)
        = ∫ u in Set.Ioi (3:ℝ), 3 * Real.exp (-u) / u :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => errH_of_three_lt hu)
    rw [hcong]
    exact tail3_le
  linarith [hsplit, h23, hI3]

/-! ## §4  The transport bounds on the three regions -/

/-- On `[2,3]` the sharp bound used by the layer induction: `∫_{s-1}^∞ errH ≤ e^{-2}(3.94 - s)`. -/
private lemma integral_Ioi_sub_one_le_lin (s : ℝ) (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    (∫ u in Set.Ioi (s - 1), errH u) ≤ Real.exp (-2) * (3.94 - s) := by
  have hInt : IntegrableOn errH (Set.Ioi (s - 1)) := integrableOn_errH_Ioi (by linarith)
  have hsplit : (∫ u in Set.Ioi (s - 1), errH u) - (∫ u in Set.Ioi (2:ℝ), errH u)
      = ∫ u in (s - 1)..2, errH u :=
    intervalIntegral.integral_Ioi_sub_Ioi hInt (by linarith)
  have h12 : (∫ u in (s - 1)..2, errH u) = (3 - s) * Real.exp (-2) := by
    have hcong : (∫ u in (s - 1)..2, errH u) = ∫ u in (s - 1)..2, Real.exp (-2) := by
      refine intervalIntegral.integral_congr ?_
      intro u hu
      rw [Set.uIcc_of_le (by linarith : s - 1 ≤ 2)] at hu
      exact errH_of_le_two hu.2
    rw [hcong, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  linarith [hsplit, h12, integral_Ioi_two_errH_le_aux, Real.exp_pos (-2)]

/-- On `[3,∞)` the profile is dominated by the pure exponential: `∫_{s-1}^∞ errH ≤ e^{-(s-1)}`. -/
private lemma integral_Ioi_sub_one_le_exp (s : ℝ) (hs : 2 ≤ s) :
    (∫ u in Set.Ioi (s - 1), errH u) ≤ Real.exp (-(s - 1)) := by
  have h1 : IntegrableOn errH (Set.Ioi (s - 1)) := integrableOn_errH_Ioi (by linarith)
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi (s - 1)) :=
    integrableOn_exp_neg_Ioi (s - 1)
  calc (∫ u in Set.Ioi (s - 1), errH u)
      ≤ ∫ u in Set.Ioi (s - 1), Real.exp (-u) :=
        setIntegral_mono_on h1 h2 measurableSet_Ioi (fun u _ => errH_le_exp_neg_aux u)
    _ = Real.exp (-(s - 1)) := integral_exp_neg_Ioi (s - 1)

/-- On `[4,∞)` the profile is `3e^{-u}/u`, and `1/u ≤ 1/(s-1)`: `∫_{s-1}^∞ errH ≤ 3e^{-(s-1)}/(s-1)`. -/
private lemma integral_Ioi_sub_one_le_div (s : ℝ) (hs : 4 ≤ s) :
    (∫ u in Set.Ioi (s - 1), errH u) ≤ 3 * Real.exp (-(s - 1)) / (s - 1) := by
  have hD : (0:ℝ) < s - 1 := by linarith
  have hcong : (∫ u in Set.Ioi (s - 1), errH u)
      = ∫ u in Set.Ioi (s - 1), 3 * Real.exp (-u) / u :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => errH_of_three_lt (by linarith [Set.mem_Ioi.mp hu]))
  rw [hcong]
  have hfF : IntegrableOn (fun u : ℝ => 3 * Real.exp (-u) / u) (Set.Ioi (s - 1)) := by
    refine Integrable.mono' (g := fun u : ℝ => 3 * Real.exp (-u) / 3) ?_ ?_ ?_
    · exact ((integrableOn_exp_neg_Ioi (s - 1)).integrable.const_mul 3).div_const 3
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro u hu
        exact ne_of_gt (by linarith [Set.mem_Ioi.mp hu] : (0:ℝ) < u)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have hu3 : (3:ℝ) < u := by linarith [Set.mem_Ioi.mp hu]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * Real.exp (-u) / u)]
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < u) (by norm_num : (0:ℝ) < 3)]
      nlinarith [Real.exp_pos (-u)]
  have hgF : IntegrableOn (fun u : ℝ => 3 * Real.exp (-u) / (s - 1)) (Set.Ioi (s - 1)) :=
    ((integrableOn_exp_neg_Ioi (s - 1)).integrable.const_mul 3).div_const (s - 1)
  have hmono : (∫ u in Set.Ioi (s - 1), 3 * Real.exp (-u) / u)
      ≤ ∫ u in Set.Ioi (s - 1), 3 * Real.exp (-u) / (s - 1) := by
    refine setIntegral_mono_on hfF hgF measurableSet_Ioi (fun u hu => ?_)
    exact div_le_div_of_nonneg_left (by positivity) hD (by linarith [Set.mem_Ioi.mp hu])
  have hval : (∫ u in Set.Ioi (s - 1), 3 * Real.exp (-u) / (s - 1))
      = 3 * Real.exp (-(s - 1)) / (s - 1) := by
    rw [MeasureTheory.integral_div]
    congr 1
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
  linarith [hmono, hval]

/-! ## §5  The shift inequality down to `s ≥ 2` -/

private lemma errH_sub_one_le_aux (s : ℝ) (_hs2 : 2 ≤ s) :
    errH (s - 1) ≤ (4 * Real.exp 1 / 3) * errH s := by
  rcases le_or_gt s 3 with hs3 | hs3
  · have h1 : errH (s - 1) = Real.exp (-2) := errH_of_le_two (by linarith)
    have h2 : Real.exp (-3) ≤ errH s := exp_neg_three_le_errH_aux hs3
    have hkey : (4 * Real.exp 1 / 3) * Real.exp (-3) = (4/3) * Real.exp (-2) := by
      have he : Real.exp 1 * Real.exp (-3) = Real.exp (-2) := by
        rw [← Real.exp_add]; norm_num
      calc (4 * Real.exp 1 / 3) * Real.exp (-3) = (4/3) * (Real.exp 1 * Real.exp (-3)) := by
            ring
        _ = (4/3) * Real.exp (-2) := by rw [he]
    rw [h1]
    calc Real.exp (-2) ≤ (4/3) * Real.exp (-2) := by linarith [Real.exp_pos (-2)]
      _ = (4 * Real.exp 1 / 3) * Real.exp (-3) := hkey.symm
      _ ≤ (4 * Real.exp 1 / 3) * errH s := mul_le_mul_of_nonneg_left h2 (by positivity)
  · exact errH_transport.2.1 s (le_of_lt hs3)

/-! ## §6  The assembled statement -/

/-- **Sharp transport inequalities for the exponential error profile `errH`** (`errH s = e^{-2}`
for `s ≤ 2`, `e^{-s}` for `2 ≤ s ≤ 3`, `3e^{-s}/s` for `s ≥ 3`), in the region-dependent
quantitative form consumed by the sharp layer induction.

All six claims are provable from the same elementary inputs as the workspace's `errH_transport`
(`tail3_le : ∫_3^∞ 3e^{-u}/u du ≤ e^{-3} - (3/50)e^{-2}`, evaluations of `∫_a^b e^{-u}du`, and
`Real.exp_one_lt_d9`); the region splittings are exactly those already carried out *inside* the
proof of `errH_transport` (its private steps `hstep` for `2 ≤ s ≤ 3` and the `s > 4` estimate),
exported here as separate claims.

Do NOT weaken the first region's bound `e^{-2}·(3.94 - s)` — at `s ∈ (2.03, 3]` the cruder
transport form `∫ ≤ (97/100)·s·errH s` is *ineffective* (it overshoots the target of the
induction), while `e^{-2}(3.94-s)/s` is exactly what closes it; same for the `e^{-(s-1)}` form on
`[3,4]` and the `3e^{-(s-1)}/(s-1)` form on `[4,∞)`.  The last claim extends
`errH_transport.2.1` (which is stated for `s ≥ 3`) down to `s ≥ 2`. -/
theorem errH_sharp_bounds :
    (∀ a b : ℝ, a ≤ b → Work.NumberTheory.Chen.APSwitchUpper.errH b ≤ Work.NumberTheory.Chen.APSwitchUpper.errH a)
  ∧ (∀ s : ℝ, 2 ≤ s → s ≤ 3 →
      (∫ u in Set.Ioi (s - 1), Work.NumberTheory.Chen.APSwitchUpper.errH u)
        ≤ Real.exp (-2) * (3.94 - s))
  ∧ (∀ s : ℝ, 3 ≤ s → s ≤ 4 →
      (∫ u in Set.Ioi (s - 1), Work.NumberTheory.Chen.APSwitchUpper.errH u) ≤ Real.exp (-(s - 1)))
  ∧ (∀ s : ℝ, 4 ≤ s →
      (∫ u in Set.Ioi (s - 1), Work.NumberTheory.Chen.APSwitchUpper.errH u)
        ≤ 3 * Real.exp (-(s - 1)) / (s - 1))
  ∧ ((∫ u in Set.Ioi (2:ℝ), Work.NumberTheory.Chen.APSwitchUpper.errH u) ≤ (47/50) * Real.exp (-2))
  ∧ (∀ s : ℝ, 2 ≤ s →
      Work.NumberTheory.Chen.APSwitchUpper.errH (s - 1)
        ≤ (4 * Real.exp 1 / 3) * Work.NumberTheory.Chen.APSwitchUpper.errH s) := by
  refine ⟨errH_antitone_aux, ?_, ?_, ?_, integral_Ioi_two_errH_le_aux, errH_sub_one_le_aux⟩
  · exact fun s hs2 hs3 => integral_Ioi_sub_one_le_lin s hs2 hs3
  · exact fun s hs3 _ => integral_Ioi_sub_one_le_exp s (by linarith)
  · exact fun s hs4 => integral_Ioi_sub_one_le_div s hs4

end

end Work.ChenPlan.LinearSieve.JR2
