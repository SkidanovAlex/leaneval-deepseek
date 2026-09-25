import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums

/-!
# Elementary numeric helpers for the decay of the polynomial profile at the origin

`polyProfile_decay_sharp` gives the van der Corput decay `‖Φ_N(β)‖ ≤ C (|β| N^d)^{-1/d}` in the
range `|β| N^d ≥ 1`; near the origin `polyProfile_sub_one_le` gives the Lipschitz bound
`‖Φ_N(β) - 1‖ ≤ 4π(Σ|c_i|)|β| N^d`.  `mstProf_scale_decay` combines the two into the single
estimate `‖ζ‖ ‖Φ_{2^n}(ζ)‖ ≲ 2^{-n/d}` valid on the whole circle.  The lemmas below are the
numeric bookkeeping of that combination.
-/

/-- `((2:ℝ)^n)^{-1} = 2^{-n}` (a natural power versus a real power). -/
lemma mstScale_two_pow_neg_eq_inv (n : ℕ) : ((2:ℝ)^n)⁻¹ = (2:ℝ)^(-(n:ℝ)) := by
  rw [← Real.rpow_natCast (2:ℝ) n]
  exact (Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (n:ℝ)).symm

/-- The dyadic dilation `polyDil P n = (2^n)^d` is the real power `2^{n d}`. -/
lemma mstScale_polyDil_eq_rpow (P : Polynomial ℤ) (n : ℕ) :
    polyDil P n = (2:ℝ) ^ ((n:ℝ) * (P.natDegree:ℝ)) := by
  rw [polyDil, powDil, ← Real.rpow_natCast (2:ℝ) n,
    ← Real.rpow_natCast ((2:ℝ)^(n:ℝ)) P.natDegree,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- `(polyDil P n)^{-1} = 2^{-n d}`. -/
lemma mstScale_polyDil_inv_eq (P : Polynomial ℤ) (n : ℕ) :
    (polyDil P n)⁻¹ = (2:ℝ) ^ (-((n:ℝ) * (P.natDegree:ℝ))) := by
  rw [mstScale_polyDil_eq_rpow]
  exact (Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((n:ℝ) * (P.natDegree:ℝ))).symm

/-- `(polyDil P n)^{-1/d} = 2^{-n}`. -/
lemma mstScale_polyDil_rpow_neg (P : Polynomial ℤ) (n : ℕ) (hd : 1 ≤ P.natDegree) :
    (polyDil P n) ^ (-(1 / (P.natDegree:ℝ))) = (2:ℝ) ^ (-(n:ℝ)) := by
  have hD : polyDil P n ^ ((1:ℝ)/(P.natDegree:ℝ)) = (2:ℝ)^n := powDil_rpow P.natDegree hd n
  rw [Real.rpow_neg (le_of_lt (polyDil_pos P n)) (1/(P.natDegree:ℝ)), hD]
  exact mstScale_two_pow_neg_eq_inv n

/-- `2^{-n d} ≤ 2^{-n/d}` for `d ≥ 1`. -/
lemma mstScale_two_rpow_scale_I (d n : ℕ) (hd : 1 ≤ d) :
    (2:ℝ) ^ (-((n:ℝ)*(d:ℝ))) ≤ (2:ℝ) ^ (-(n:ℝ)/(d:ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have h2 : (n:ℝ) ≤ (n:ℝ)*(d:ℝ) := le_mul_of_one_le_right hn0 hdR
  have h1 : (n:ℝ)/(d:ℝ) ≤ (n:ℝ) := (div_le_iff₀ hdpos).mpr h2
  have h3 : (n:ℝ)/(d:ℝ) ≤ (n:ℝ)*(d:ℝ) := le_trans h1 h2
  rw [neg_div]
  exact neg_le_neg h3

/-- `2^{-n} ≤ 2^{-n/d}` for `d ≥ 1`. -/
lemma mstScale_two_rpow_scale_II (d n : ℕ) (hd : 1 ≤ d) :
    (2:ℝ) ^ (-(n:ℝ)) ≤ (2:ℝ) ^ (-(n:ℝ)/(d:ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  rw [neg_div]
  apply neg_le_neg
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  exact (div_le_iff₀ hdpos).mpr (le_mul_of_one_le_right hn0 hdR)

/-- **The decay of the polynomial profile at the origin (the only analytic gain of the freezing estimate).**  For `‖ζ‖ ≤ 1/2` (always true on the circle, so the first factor below is just `‖ζ‖`), `‖ζ‖·‖Φ_{2^n}(ζ)‖ ≲ 2^{−n/d}` with `d = P.natDegree ≥ 2`.
Route.  Write `w = iwRep ζ ∈ Ioc (−1/2, 1/2]`, so `‖ζ‖ = |w|` (`norm_eq_abs_iwRep`, `memLp_scaled_bump.lean`) and `mstProf P (2^n) ζ = polyProfile P (2^n) w` (`mstProf_apply`).  Let `polyDil P n = 2^{nd}` (`poly_block_core_defs.lean`).  Two cases:
* `|w| ≤ (polyDil P n)^{-1}`: `polyProfile_sub_one_le` (needs `N = 2^n ≥ 1`) gives `‖Φ(w) − 1‖ ≤ 4π(Σ_i|c_i|)·|w|·2^{nd}`, hence `|w|‖Φ(w)‖ ≤ |w|(1 + A|w|2^{nd}) ≤ (1+A)2^{−nd}`, and `2^{−nd} ≤ 2^{−n/d}` because `d ≥ 1`.
* `(polyDil P n)^{-1} < |w|`: then `1 ≤ |w|·polyDil P n` (`|w| > 0`) and `polyProfile_decay_sharp` gives `‖Φ(w)‖ ≤ C (|w|2^{nd})^{−1/d} = C|w|^{−1/d}2^{−n}` (use `Real.mul_rpow`, `Real.rpow_mul`); so `|w|‖Φ(w)‖ ≤ C|w|^{1−1/d}2^{−n} ≤ C(1/2)^{1−1/d}2^{−n} ≤ C(1/2)^{1−1/d}2^{−n/d}` since `2^{−n} ≤ 2^{−n/d}` (`d ≥ 1`).
The constant is any `C ≥ 1 + 4πΣ|c_i| + C'·(1/2)^{1−1/d}` (`C'` from `polyProfile_decay_sharp`); the hypothesis `1 ≤ n` is not needed but harmless. -/
theorem mstProf_scale_decay (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ ζ : Work.BourgainPlan.IonescuWainger.Circle,
      ‖ζ‖ * ‖Work.BourgainPlan.Maximal.mstProf P (2 ^ n) ζ‖
        ≤ C * (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)) := by
  obtain ⟨C', hC'pos, hC'⟩ := polyProfile_decay_sharp P hd
  have hd1 : 1 ≤ P.natDegree := by omega
  set A : ℝ := 4 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  refine ⟨max (1 + A) C', ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : (0:ℝ) < 1 + A) (le_max_left _ _)
  · intro n hn ζ
    rw [norm_eq_abs_iwRep, mstProf_apply]
    set w : ℝ := iwRep ζ with hwdef
    have hwle : |w| ≤ 1/2 := by rw [hwdef]; exact abs_iwRep_le ζ
    set D : ℝ := polyDil P n with hDdef
    have hDpos : 0 < D := by rw [hDdef]; exact polyDil_pos P n
    set Φ : ℂ := polyProfile P (2^n) w with hΦdef
    have hgoal : |w| * ‖Φ‖ ≤ max (1+A) C' * (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) := by
      rcases le_or_gt |w| D⁻¹ with hcase | hcase
      · -- Case 1: `|w| ≤ D⁻¹`, the Lipschitz regime at the origin.
        have hN : 1 ≤ 2^n := Nat.one_le_pow n 2 (by norm_num)
        have hsub0 := polyProfile_sub_one_le P (2^n) hN w
        have hbad : (((2^n : ℕ) : ℝ)) ^ P.natDegree = D := by
          rw [hDdef]; push_cast; rfl
        rw [← hAdef, hbad] at hsub0
        have hsub' : ‖Φ - 1‖ ≤ A * (|w| * D) := by rw [hΦdef]; exact hsub0
        have hwD : |w| * D ≤ 1 := by
          have h := mul_le_mul_of_nonneg_right hcase hDpos.le
          rwa [inv_mul_cancel₀ (ne_of_gt hDpos)] at h
        have hΦle : ‖Φ‖ ≤ A + 1 := by
          have h1 : ‖Φ‖ ≤ ‖Φ - 1‖ + 1 := by
            calc ‖Φ‖ = ‖(Φ - 1) + 1‖ := by rw [sub_add_cancel]
              _ ≤ ‖Φ - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
              _ = ‖Φ - 1‖ + 1 := by rw [norm_one]
          have h2 : A * (|w| * D) ≤ A := by
            have := mul_le_mul_of_nonneg_left hwD hA0
            rwa [mul_one] at this
          linarith
        have hfin : |w| * ‖Φ‖ ≤ (A+1) * D⁻¹ := by
          have h3 : |w| * ‖Φ‖ ≤ |w| * (A+1) := mul_le_mul_of_nonneg_left hΦle (abs_nonneg w)
          have h4 : |w| * (A+1) ≤ D⁻¹ * (A+1) := mul_le_mul_of_nonneg_right hcase (by linarith)
          linarith
        have hscale : D⁻¹ ≤ (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) := by
          rw [hDdef, mstScale_polyDil_inv_eq]
          exact mstScale_two_rpow_scale_I P.natDegree n hd1
        have hX0 : (0:ℝ) ≤ (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) := Real.rpow_nonneg (by norm_num) _
        have hmax : (A+1) ≤ max (1+A) C' := by
          rw [show A + 1 = 1 + A by ring]; exact le_max_left _ _
        calc |w| * ‖Φ‖ ≤ (A+1) * D⁻¹ := hfin
          _ ≤ (A+1) * (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) := mul_le_mul_of_nonneg_left hscale (by linarith)
          _ ≤ max (1+A) C' * (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) := mul_le_mul_of_nonneg_right hmax hX0
      · -- Case 2: `D⁻¹ < |w|`, the van der Corput decay regime.
        have hwpos : 0 < |w| := lt_trans (inv_pos.mpr hDpos) hcase
        have hwne : w ≠ 0 := by
          intro h; rw [h, abs_zero] at hwpos; exact lt_irrefl 0 hwpos
        have hge : 1 ≤ |w| * D := by
          have h := mul_lt_mul_of_pos_right hcase hDpos
          rw [inv_mul_cancel₀ (ne_of_gt hDpos)] at h
          exact le_of_lt h
        have hdec := hC' w hwne n (by rw [← hDdef]; exact hge)
        have hdec' : ‖Φ‖ ≤ C' * (|w| * D)^(-(1/(P.natDegree:ℝ))) := by
          rw [hΦdef, hDdef]; exact hdec
        have hpow : (|w| * D)^(-(1/(P.natDegree:ℝ)))
            = |w|^(-(1/(P.natDegree:ℝ))) * (2:ℝ)^(-(n:ℝ)) := by
          rw [Real.mul_rpow (abs_nonneg w) hDpos.le]
          congr 1
          rw [hDdef]; exact mstScale_polyDil_rpow_neg P n hd1
        have hwd : |w| * |w|^(-(1/(P.natDegree:ℝ))) = |w|^(1 - 1/(P.natDegree:ℝ)) := by
          have h := Real.rpow_add (abs_pos.mpr hwne) (1:ℝ) (-(1/(P.natDegree:ℝ)))
          rw [Real.rpow_one] at h
          rw [show (1:ℝ) + -(1/(P.natDegree:ℝ)) = 1 - 1/(P.natDegree:ℝ) by ring] at h
          exact h.symm
        have hle1 : |w|^(1 - 1/(P.natDegree:ℝ)) ≤ 1 := by
          apply Real.rpow_le_one (abs_nonneg w) (by linarith [hwle])
          have hdiv : (1:ℝ)/(P.natDegree:ℝ) ≤ 1 := by
            rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < P.natDegree)), one_mul]
            exact_mod_cast hd1
          linarith
        have hfin2 : |w| * ‖Φ‖ ≤ C' * (2:ℝ)^(-(n:ℝ)) := by
          have hX0 : 0 ≤ (2:ℝ)^(-(n:ℝ)) := Real.rpow_nonneg (by norm_num) _
          calc |w| * ‖Φ‖ ≤ |w| * (C' * (|w| * D)^(-(1/(P.natDegree:ℝ)))) :=
                mul_le_mul_of_nonneg_left hdec' (abs_nonneg w)
            _ = C' * (|w| * |w|^(-(1/(P.natDegree:ℝ)))) * (2:ℝ)^(-(n:ℝ)) := by rw [hpow]; ring
            _ = C' * |w|^(1 - 1/(P.natDegree:ℝ)) * (2:ℝ)^(-(n:ℝ)) := by rw [hwd]
            _ ≤ C' * 1 * (2:ℝ)^(-(n:ℝ)) := by
                have h5 := mul_le_mul_of_nonneg_left hle1 hC'pos.le
                exact mul_le_mul_of_nonneg_right h5 hX0
            _ = C' * (2:ℝ)^(-(n:ℝ)) := by ring
        have hscale2 : (2:ℝ)^(-(n:ℝ)) ≤ (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) :=
          mstScale_two_rpow_scale_II P.natDegree n hd1
        have hX0 : 0 ≤ (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) := Real.rpow_nonneg (by norm_num) _
        calc |w| * ‖Φ‖ ≤ C' * (2:ℝ)^(-(n:ℝ)) := hfin2
          _ ≤ C' * (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) :=
              mul_le_mul_of_nonneg_left hscale2 hC'pos.le
          _ ≤ max (1+A) C' * (2:ℝ)^(-(n:ℝ)/(P.natDegree:ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hX0
    exact hgoal

end Work.BourgainPlan.Maximal
