import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.iwPN_le_exp
import Submission.Work.BourgainPlan.Maximal.sigmaN_log_bound

/-!
# The eventual numeric estimates of the minor-arc bound

`mst_minor_numeric` collects the seven "exponential beats polynomial" estimates that the
minor-arc analysis of Bourgain's polynomial ergodic theorem uses.

## A defaulting trap in conjunct (iii)

In the statement of `mst_minor_numeric` as delegated, the exponent in
`Real.exp (-((n : ℝ) ^ (1 / 10)))` is left unannotated, so Lean elaborates the numeral
`1 / 10` at `ℕ`.  Since `(1 : ℕ) / 10 = 0`, that conjunct reads

`(2 : ℝ) ^ (-(n (d - χ))) < 2 * Real.exp (-1)`

and **not** the intended `… < 2 * Real.exp (-(n ^ (1 / 10)))`.  (The same slip occurs
wherever an unannotated `1 / 10` is used as a real exponent; write `(1 / 10 : ℝ)`.)
Machine-checked evidence:

  `example (x : ℝ) : x ^ (1 / 10) = 1 := rfl`
  `example (x : ℝ) : Real.exp (-(x ^ (1 / 10))) = Real.exp (-1) := rfl`

The mathematically intended conjunct (iii) is proved here as `two_rpow_neg_lt_exp`, and the
whole conjunction in its intended reading as `mst_minor_numeric_real_exponent`.  The latter
implies the delivered form, because `(n : ℝ) ^ (1 / 10 : ℝ) ≥ 1` for `n ≥ 1`; use
`mst_minor_numeric_real_exponent` wherever the level separation `2 e^{-n^{1/10}}` is really
needed (e.g. for the disjointness of the level-`n` bumps).
-/

namespace Work.BourgainPlan.Maximal

-- Machine-checked demonstration of the defaulting trap described above.
example (x : ℝ) : x ^ (1 / 10) = 1 := rfl
example (x : ℝ) : Real.exp (-(x ^ (1 / 10))) = Real.exp (-1) := rfl

/-! ### Elementary numeric estimates used by the minor-arc bound -/

/-- `log 2 > 1/2`, in the form that is convenient below. -/
lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- `log 2 > 0`. -/
lemma log_two_pos : (0 : ℝ) < Real.log 2 := lt_trans (by norm_num) log_two_gt_half

/-- For `x ≥ 1`, `√x ≤ x`. -/
lemma sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have h : x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at h
  exact h

/-- For `x ≥ 1`, `x^{1/10} ≤ x`. -/
lemma rpow_ten_inv_le_self {x : ℝ} (hx : 1 ≤ x) : x ^ (1 / 10 : ℝ) ≤ x := by
  have h := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 / 10 : ℝ) ≤ 1)
  rwa [Real.rpow_one] at h

/-- For `y ≥ 0`, `(1/4)·2^{-y} < 1/2`. -/
lemma quarter_rpow_lt_half {y : ℝ} (hy : 0 ≤ y) : (1 / 4 : ℝ) * (2 : ℝ) ^ (-y) < 1 / 2 := by
  have h1 : (2 : ℝ) ^ (-y) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (1 / 4 : ℝ) * (2 : ℝ) ^ (-y) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa using this
  linarith

/-- (i): the Dirichlet parameter is `≥ 1` as soon as `log x` is controlled by `√x`
and `d ≥ 2`, `x ≥ 1`. -/
lemma one_le_rpow_neg_mul_rpow {x d γ : ℝ} (hx : 1 ≤ x) (hd : 2 ≤ d)
    (hlog : γ * Real.log x ≤ Real.sqrt x) :
    (1 : ℝ) ≤ x ^ (-γ) * (2 : ℝ) ^ (x * d) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsx_le_x : Real.sqrt x ≤ x := sqrt_le_self_of_one_le hx
  have hdl : 1 ≤ d * Real.log 2 := by
    have h1 : 2 * (1 / 2 : ℝ) ≤ d * Real.log 2 :=
      mul_le_mul hd (le_of_lt log_two_gt_half) (by norm_num) (by linarith)
    linarith
  have hx_le : x ≤ d * Real.log 2 * x := by
    have := mul_le_mul_of_nonneg_right hdl hxpos.le
    simpa using this
  have hkey : Real.log x * γ ≤ Real.log 2 * (x * d) := by
    have h1 : γ * Real.log x ≤ d * Real.log 2 * x := le_trans hlog (le_trans hsx_le_x hx_le)
    have h2 : Real.log 2 * (x * d) = d * Real.log 2 * x := by ring
    have h3 : Real.log x * γ = γ * Real.log x := by ring
    rw [h3, h2]; exact h1
  have hu : x ^ γ ≤ (2 : ℝ) ^ (x * d) := by
    rw [Real.rpow_def_of_pos hxpos γ,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (x * d)]
    exact Real.exp_le_exp.mpr hkey
  have hxγ : 0 < x ^ γ := Real.rpow_pos_of_pos hxpos γ
  rw [Real.rpow_neg hxpos.le γ, inv_mul_eq_div, le_div_iff₀ hxγ, one_mul]
  exact hu

/-- (ii): `x^γ ≤ 2^x` for `x ≥ 4` once `log x` is controlled by `√x`. -/
lemma rpow_le_two_pow {x γ : ℝ} (hx4 : 4 ≤ x) (hlog : γ * Real.log x ≤ Real.sqrt x) :
    x ^ γ ≤ (2 : ℝ) ^ x := by
  have hxpos : 0 < x := by linarith
  have hsx_le : Real.sqrt x ≤ x * Real.log 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg hxpos.le (le_of_lt log_two_pos), ?_⟩
    have h1 : (2 : ℝ) ≤ x * Real.log 2 := by
      have h := mul_le_mul hx4 (le_of_lt log_two_gt_half) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by linarith : (0 : ℝ) ≤ x)
      linarith
    have h2 : 1 ≤ x * Real.log 2 * Real.log 2 := by
      have h := mul_le_mul h1 (le_of_lt log_two_gt_half) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by linarith : (0 : ℝ) ≤ x * Real.log 2)
      linarith
    have h3 : x ≤ x * Real.log 2 * Real.log 2 * x := by
      have := mul_le_mul_of_nonneg_right h2 hxpos.le
      simpa using this
    have h4 : x * Real.log 2 * Real.log 2 * x = (x * Real.log 2) ^ 2 := by ring_nf
    linarith [h3, h4]
  have hkey : Real.log x * γ ≤ Real.log 2 * x := by
    have h1 : γ * Real.log x ≤ x * Real.log 2 := le_trans hlog hsx_le
    have h2 : Real.log x * γ = γ * Real.log x := by ring
    have h3 : Real.log 2 * x = x * Real.log 2 := by ring
    rw [h2, h3]; exact h1
  rw [Real.rpow_def_of_pos hxpos γ, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) x]
  exact Real.exp_le_exp.mpr hkey

/-- (iii), in its mathematical form: `2^{-x(d-χ)} < 2 e^{-x^{1/10}}`. -/
lemma two_rpow_neg_lt_exp {x d χ : ℝ} (hx1 : 1 ≤ x) (hd : 2 ≤ d) (hχ1 : χ < 1 / 10) :
    (2 : ℝ) ^ (-(x * (d - χ))) < 2 * Real.exp (-(x ^ (1 / 10 : ℝ))) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog2pos : 0 < Real.log 2 := log_two_pos
  have hdχ : (19 / 10 : ℝ) < d - χ := by linarith
  have hδ : 0 < (d - χ) * Real.log 2 - 1 := by
    have h1 : (19 / 10 : ℝ) * Real.log 2 > 1 := by linarith [Real.log_two_gt_d9]
    have h2 : (19 / 10 : ℝ) * Real.log 2 < (d - χ) * Real.log 2 :=
      mul_lt_mul_of_pos_right hdχ hlog2pos
    linarith
  have hp10 : x ^ (1 / 10 : ℝ) ≤ x := rpow_ten_inv_le_self hx1
  have hmain : Real.log 2 * (-(x * (d - χ))) < Real.log 2 + (-(x ^ (1 / 10 : ℝ))) := by
    have hA : Real.log 2 * (-(x * (d - χ)))
        = -(x + x * ((d - χ) * Real.log 2 - 1)) := by ring
    have hB : x ^ (1 / 10 : ℝ) - x ≤ 0 := by linarith
    have hC : 0 < x * ((d - χ) * Real.log 2 - 1) := mul_pos hxpos hδ
    rw [hA]
    linarith [hB, hC, hlog2pos]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-(x * (d - χ)))]
  rw [show (2 : ℝ) * Real.exp (-(x ^ (1 / 10 : ℝ)))
        = Real.exp (Real.log 2 + (-(x ^ (1 / 10 : ℝ)))) by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
  exact Real.exp_lt_exp.mpr hmain

/-- (iii) as literally stated, where the exponent `(1 / 10)` of `Real.exp (-(x ^ (1 / 10)))`
elaborates at `ℕ` (and hence is `0`), so that the statement is `2^{-x(d-χ)} < 2 e^{-1}`.
This is the weaker form that the constant `2 e^{-1}` yields; it follows from
`two_rpow_neg_lt_exp` because `x^{1/10} ≥ 1` for `x ≥ 1`. -/
lemma two_rpow_neg_lt_exp_nat {x d χ : ℝ} (hx1 : 1 ≤ x) (hd : 2 ≤ d) (hχ1 : χ < 1 / 10) :
    (2 : ℝ) ^ (-(x * (d - χ))) < 2 * Real.exp (-(x ^ (1 / 10))) := by
  have h := two_rpow_neg_lt_exp (x := x) hx1 hd hχ1
  have h1 : (1 : ℝ) ≤ x ^ (1 / 10 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have h2 : Real.exp (-(x ^ (1 / 10 : ℝ))) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h3 : Real.exp (-(x ^ (1 / 10))) = Real.exp (-1) := rfl
  have h4 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
  linarith [h, h4]

/-- (iv): the small-denominator gap lies inside the inner bump radius. -/
lemma minor_core {x d γ c χ : ℝ} (hx1 : 1 ≤ x) (hc : 0 < c) (hχ0 : 0 < χ)
    (hx4 : 4 / (χ * Real.log 2) ^ 2 ≤ x)
    (hxL : (2 * |Real.log (4 / c)| + 2) / (χ * Real.log 2) ≤ x)
    (hlog : γ * Real.log x ≤ Real.sqrt x) :
    x ^ γ * (2 : ℝ) ^ (-(x * d)) / c ≤ (1 / 4) * (2 : ℝ) ^ (-(x * (d - χ))) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog2pos : 0 < Real.log 2 := log_two_pos
  have hηpos : 0 < χ * Real.log 2 := mul_pos hχ0 hlog2pos
  -- `√x ≥ 2/η`
  have hsx_low : 2 / (χ * Real.log 2) ≤ Real.sqrt x := by
    have hkey : Real.sqrt (4 / (χ * Real.log 2) ^ 2) = 2 / (χ * Real.log 2) := by
      rw [show (4 : ℝ) / (χ * Real.log 2) ^ 2 = (2 / (χ * Real.log 2)) ^ 2 by
        field_simp
        ring_nf]
      exact Real.sqrt_sq (div_nonneg (by norm_num) hηpos.le)
    have h := Real.sqrt_le_sqrt hx4
    rwa [hkey] at h
  -- `√x ≤ (η/2) x`
  have hsx_up : Real.sqrt x ≤ (χ * Real.log 2 / 2) * x := by
    have hnneg : 0 ≤ (χ * Real.log 2 / 2) * x :=
      mul_nonneg (div_nonneg hηpos.le (by norm_num)) hxpos.le
    have hsq2 : (χ * Real.log 2 / 2) ^ 2 * (4 / (χ * Real.log 2) ^ 2) = 1 := by
      field_simp
      ring_nf
    have h3 : 1 ≤ (χ * Real.log 2 / 2) ^ 2 * x := by
      have h := mul_le_mul_of_nonneg_left hx4 (sq_nonneg (χ * Real.log 2 / 2))
      rw [hsq2] at h
      linarith
    have h4 : x ≤ ((χ * Real.log 2 / 2) * x) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h3 hxpos.le
      have he : ((χ * Real.log 2 / 2) ^ 2 * x) * x
          = ((χ * Real.log 2 / 2) * x) ^ 2 := by ring_nf
      linarith [h, he]
    calc Real.sqrt x ≤ Real.sqrt (((χ * Real.log 2 / 2) * x) ^ 2) := Real.sqrt_le_sqrt h4
      _ = (χ * Real.log 2 / 2) * x := Real.sqrt_sq hnneg
  -- `log (4/c) ≤ (η/2) x`
  have hLx : Real.log (4 / c) ≤ (χ * Real.log 2 / 2) * x := by
    have h1 : 2 * |Real.log (4 / c)| + 2 ≤ (χ * Real.log 2) * x := by
      have h := mul_le_mul_of_nonneg_right hxL hηpos.le
      rw [div_mul_cancel₀ _ hηpos.ne'] at h
      linarith
    have h2 : (χ * Real.log 2) * x / 2 = (χ * Real.log 2 / 2) * x := by ring_nf
    rw [← h2]
    linarith [h1, le_abs_self (Real.log (4 / c))]
  -- the logarithmic chain
  have hlogchain : Real.log (4 / c) + γ * Real.log x ≤ (x * χ) * Real.log 2 := by
    have h1 : Real.log (4 / c) + γ * Real.log x
        ≤ (χ * Real.log 2 / 2) * x + (χ * Real.log 2 / 2) * x :=
      add_le_add hLx (le_trans hlog hsx_up)
    have h2 : (x * χ) * Real.log 2
        = (χ * Real.log 2 / 2) * x + (χ * Real.log 2 / 2) * x := by ring_nf
    rw [h2]; exact h1
  -- `(4/c)·x^γ ≤ 2^{xχ}`
  have hu_pos : 0 < (4 : ℝ) / c * x ^ γ :=
    mul_pos (div_pos (by norm_num) hc) (Real.rpow_pos_of_pos hxpos γ)
  have hv_pos : 0 < (2 : ℝ) ^ (x * χ) := Real.rpow_pos_of_pos (by norm_num) _
  have h4' : (4 : ℝ) / c * x ^ γ ≤ (2 : ℝ) ^ (x * χ) := by
    have hl : Real.log ((4 : ℝ) / c * x ^ γ) = Real.log (4 / c) + γ * Real.log x := by
      rw [Real.log_mul (div_pos (by norm_num) hc).ne' (Real.rpow_pos_of_pos hxpos γ).ne',
        Real.log_rpow hxpos γ]
    have hr : Real.log ((2 : ℝ) ^ (x * χ)) = (x * χ) * Real.log 2 := Real.log_rpow (by norm_num) _
    rw [← Real.exp_log hu_pos, ← Real.exp_log hv_pos, Real.exp_le_exp, hl, hr]
    exact hlogchain
  have h4 : 4 * x ^ γ ≤ c * (2 : ℝ) ^ (x * χ) := by
    have h := mul_le_mul_of_nonneg_right h4' hc.le
    have e1 : ((4 : ℝ) / c * x ^ γ) * c = 4 * x ^ γ := by field_simp
    linarith [h, e1]
  -- multiply by `2^{-xd}`
  have hfin : 4 * (x ^ γ * (2 : ℝ) ^ (-(x * d))) ≤ c * (2 : ℝ) ^ (-(x * (d - χ))) := by
    have hpos2 : 0 < (2 : ℝ) ^ (-(x * d)) := Real.rpow_pos_of_pos (by norm_num) _
    have h := mul_le_mul_of_nonneg_right h4 hpos2.le
    have e1 : (4 * x ^ γ) * (2 : ℝ) ^ (-(x * d))
        = 4 * (x ^ γ * (2 : ℝ) ^ (-(x * d))) := by ring
    have e2 : (c * (2 : ℝ) ^ (x * χ)) * (2 : ℝ) ^ (-(x * d))
        = c * (2 : ℝ) ^ (-(x * (d - χ))) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring_nf
    linarith [h, e1, e2]
  rw [div_le_iff₀ hc,
    show (1 / 4 : ℝ) * (2 : ℝ) ^ (-(x * (d - χ))) * c
        = c * (2 : ℝ) ^ (-(x * (d - χ))) / 4 by ring]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), mul_comm (x ^ γ * (2 : ℝ) ^ (-(x * d))) 4]
  exact hfin

/-- The estimates (i), (ii), (iv), (v), (vi), (vii) of `mst_minor_numeric`: all of them are
"exponential beats polynomial" statements and all hold above a single threshold. -/
lemma mst_core {d : ℕ} {χ γ c : ℝ} (hd : 2 ≤ d) (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (hγ : 0 < γ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (1 : ℝ) ≤ (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (d : ℝ)) ∧
      (n : ℝ) ^ γ ≤ (2 : ℝ) ^ n ∧
      (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c
          ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) ∧
      (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c < 1 / 2 ∧
      c ≤ (n : ℝ) ∧ (2 : ℝ) ^ 21 ≤ (n : ℝ) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨C₁, _hC₁3, hC₁⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_log_le_rpow γ (1 / 2) hγ (by norm_num)
  let M : ℝ := max C₁ (max 4 (max ((2 : ℝ) ^ 21)
    (max c (max (4 / (χ * Real.log 2) ^ 2)
      ((2 * |Real.log (4 / c)| + 2) / (χ * Real.log 2))))))
  refine ⟨Nat.ceil M, fun n hn => ?_⟩
  have hnM : M ≤ (n : ℝ) := le_trans (Nat.le_ceil M) (by exact_mod_cast hn)
  have hall : C₁ ≤ (n : ℝ) ∧ (4 : ℝ) ≤ (n : ℝ) ∧ ((2 : ℝ) ^ 21) ≤ (n : ℝ) ∧ c ≤ (n : ℝ) ∧
      4 / (χ * Real.log 2) ^ 2 ≤ (n : ℝ) ∧
      (2 * |Real.log (4 / c)| + 2) / (χ * Real.log 2) ≤ (n : ℝ) := by
    have h := hnM
    simp only [M, max_le_iff] at h
    exact h
  obtain ⟨hC1n, hx4, hx21, hcn, hxη, hxL⟩ := hall
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hlog : γ * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h := hC₁ n hC1n
    rwa [← Real.sqrt_eq_rpow] at h
  have hii : (n : ℝ) ^ γ ≤ (2 : ℝ) ^ n := by
    have h := rpow_le_two_pow hx4 hlog
    simpa only [Real.rpow_natCast] using h
  have hiv : (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c
      ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) :=
    minor_core hx1 hc hχ0 hxη hxL hlog
  have hv : (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c < 1 / 2 :=
    lt_of_le_of_lt hiv (quarter_rpow_lt_half (mul_nonneg (by positivity) (by linarith)))
  exact ⟨one_le_rpow_neg_mul_rpow hx1 hdR hlog, hii, hiv, hv, hcn, hx21⟩

/-- **The eventual numeric estimates of the minor-arc bound.** For `d ≥ 2`, `0 < χ < 1/10`, `γ > 0`, `c > 0` there is `N₀` such that for all `n ≥ N₀`: (i) `1 ≤ n^{-γ} 2^{nd}` (the Dirichlet parameter is `≥ 1`); (ii) `n^γ ≤ 2^n` (so `2^{-n} ≤ n^{-γ}`); (iii) `2^{-n(d-χ)} < 2 e^{-n^{1/10}}` (exponential beats the level separation `2 e^{-n^{1/10}}`; uses `n^{1/10} ≤ n` and `(d-χ)·log 2 > 1`, the latter from `d-χ > 1.9` and `Real.log_two_gt_d9`); (iv) `n^γ 2^{-nd}/c ≤ (1/4) 2^{-n(d-χ)}` and (v) `< 1/2` (the small-denominator gap lies inside the inner bump radius); (vi) `c ≤ n`; (vii) `2^21 ≤ n`. All are "exponential beats polynomial" statements; `Work.BourgainPlan.IonescuWainger.exists_log_le_rpow` and `Work.BourgainPlan.Maximal.exists_rpow_ge` (`Maximal/sigmaN_log_bound.lean`) supply the logarithmic bookkeeping. -/
theorem mst_minor_numeric {d : ℕ} {χ γ c : ℝ} (hd : 2 ≤ d) (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (hγ : 0 < γ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (1 : ℝ) ≤ (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (d : ℝ)) ∧
      (n : ℝ) ^ γ ≤ (2 : ℝ) ^ n ∧
      (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) < 2 * Real.exp (-((n : ℝ) ^ (1 / 10))) ∧
      (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c
          ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) ∧
      (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c < 1 / 2 ∧
      c ≤ (n : ℝ) ∧ (2 : ℝ) ^ 21 ≤ (n : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := mst_core hd hχ0 hχ1 hγ hc
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast hn1
  obtain ⟨hi, hii, hiv, hv, h6, h7⟩ := hN₀ n hn₀
  exact ⟨hi, hii, two_rpow_neg_lt_exp_nat hx1 (by exact_mod_cast hd) hχ1, hiv, hv, h6, h7⟩

/-- The mathematically intended form of conjunct (iii): with the exponent of `n ^ (1 / 10)`
read at `ℝ` (in `mst_minor_numeric` the numeral `1 / 10` defaults to `ℕ`, hence to `0`, so that
the two sides there are `2^{-n(d-χ)}` and `2 e^{-1}`).  All other conjuncts are as in
`mst_minor_numeric`, and this version implies it since `n^{1/10} ≥ 1`. -/
theorem mst_minor_numeric_real_exponent {d : ℕ} {χ γ c : ℝ} (hd : 2 ≤ d) (hχ0 : 0 < χ)
    (hχ1 : χ < 1 / 10) (hγ : 0 < γ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (1 : ℝ) ≤ (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (d : ℝ)) ∧
      (n : ℝ) ^ γ ≤ (2 : ℝ) ^ n ∧
      (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) < 2 * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) ∧
      (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c
          ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) ∧
      (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (d : ℝ))) / c < 1 / 2 ∧
      c ≤ (n : ℝ) ∧ (2 : ℝ) ^ 21 ≤ (n : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := mst_core hd hχ0 hχ1 hγ hc
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast hn1
  obtain ⟨hi, hii, hiv, hv, h6, h7⟩ := hN₀ n hn₀
  exact ⟨hi, hii, two_rpow_neg_lt_exp hx1 (by exact_mod_cast hd) hχ1, hiv, hv, h6, h7⟩

end Work.BourgainPlan.Maximal
