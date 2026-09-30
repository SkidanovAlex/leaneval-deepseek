import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Packaging of the left-edge bound (`Work.BMF.liouville.zetaTwLeft_near_far_le`): with
`1 - σ₁ = c/(4V)`, `V ≤ L^{9/10}`, `1/2 ≤ σ₁`, `T ≥ L² exp(L^{1/10})`, `y = exp L`,
`log(2T+3) ≤ 2L^{5/4}` and `log(|u|+T+3) ≤ 2L^{5/4}`, the raw bound
`(B + C₅ + 1/(1-σ₁) + 1) log²(|u|+T+3) y^{σ₁} (2√2 log(1 + T/σ₁))`
is at most `24√2 (B + C₅ + 1 + 4/c) L^10 y exp(-(c/8) L^{1/10})`.  Pure real inequality:
`1/(1-σ₁) = 4V/c ≤ 4L^{9/10}/c`, `log² ≤ 4L^{5/2}`, `y^{σ₁} = y exp(-(1-σ₁)L) ≤ y exp(-(c/4)L^{1/10})`
(because `1-σ₁ ≥ c/(4L^{9/10})`), `log(1 + T/σ₁) ≤ 1 + log T ≤ 3L^{5/4}`, and
`L^{9/10}·L^{15/4} = L^{93/20} ≤ L^10`. -/
lemma zetaTwLeftEdge_absorb {c V B C₅ L T y σ₁ u : ℝ} (hc : 0 < c) (hV : 0 < V) (hB : 0 ≤ B)
    (hC₅ : 0 ≤ C₅) (hL1 : 1 ≤ L) (hT : 0 < T)
    (hTge : L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) ≤ T) (hy : y = Real.exp L)
    (hsig : 1 - σ₁ = c / (4 * V)) (hVle : V ≤ L ^ (9 / 10 : ℝ)) (hhalf : 1 / 2 ≤ σ₁)
    (hlogT : Real.log (2 * T + 3) ≤ 2 * L ^ (5 / 4 : ℝ))
    (hlog : Real.log (|u| + T + 3) ≤ 2 * L ^ (5 / 4 : ℝ)) :
    (B + C₅ + 1 / (1 - σ₁) + 1) * (Real.log (|u| + T + 3)) ^ 2 * y ^ σ₁ *
        (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))
      ≤ 24 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * L ^ (10 : ℝ) * y *
          Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have h1msig_pos : 0 < 1 - σ₁ := by rw [hsig]; positivity
  have hsigpos : 0 < σ₁ := by linarith
  have hypos : 0 < y := by rw [hy]; exact Real.exp_pos L
  have hynn : 0 ≤ y := le_of_lt hypos
  -- `P9 = L^{9/10} ≥ 1`
  have hP9_1 : (1 : ℝ) ≤ L ^ (9 / 10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hP9nn : (0 : ℝ) ≤ L ^ (9 / 10 : ℝ) := le_trans zero_le_one hP9_1
  -- (1) `1/(1-σ₁) = 4V/c ≤ 4L^{9/10}/c`
  have hinv : 1 / (1 - σ₁) = 4 * V / c := by
    rw [hsig, one_div_div]
  have hIP : 1 / (1 - σ₁) ≤ 4 * L ^ (9 / 10 : ℝ) / c := by
    rw [hinv]
    exact div_le_div_of_nonneg_right (by linarith : 4 * V ≤ 4 * L ^ (9 / 10 : ℝ)) hc.le
  -- (2) the additive factor collapses into `L^{9/10}`
  have hSnn : 0 ≤ B + C₅ + 1 + 4 / c := by
    have h4c : 0 < 4 / c := div_pos (by norm_num) hc
    linarith
  have hA_le : B + C₅ + 1 / (1 - σ₁) + 1 ≤ (B + C₅ + 1 + 4 / c) * L ^ (9 / 10 : ℝ) := by
    have hSb : 0 ≤ B + C₅ + 1 := by linarith
    have h1 : B + C₅ + 1 ≤ (B + C₅ + 1) * L ^ (9 / 10 : ℝ) :=
      le_mul_of_one_le_right hSb hP9_1
    have h2 : 1 / (1 - σ₁) ≤ (4 / c) * L ^ (9 / 10 : ℝ) := by
      have h4 : 4 * L ^ (9 / 10 : ℝ) / c = (4 / c) * L ^ (9 / 10 : ℝ) := by ring
      linarith [hIP]
    calc B + C₅ + 1 / (1 - σ₁) + 1 = (B + C₅ + 1) + 1 / (1 - σ₁) := by ring
      _ ≤ (B + C₅ + 1) * L ^ (9 / 10 : ℝ) + (4 / c) * L ^ (9 / 10 : ℝ) :=
          add_le_add h1 h2
      _ = (B + C₅ + 1 + 4 / c) * L ^ (9 / 10 : ℝ) := by ring
  -- (3) `log²(|u|+T+3) ≤ 4 L^{5/2}`
  have hℓnn : 0 ≤ Real.log (|u| + T + 3) := by
    apply Real.log_nonneg
    have := abs_nonneg u; linarith
  have hℓ2 : (Real.log (|u| + T + 3)) ^ 2 ≤ 4 * L ^ (5 / 2 : ℝ) := by
    have h45 : (0 : ℝ) ≤ L ^ (5 / 4 : ℝ) := Real.rpow_nonneg hLnn _
    have hb : 0 ≤ 2 * L ^ (5 / 4 : ℝ) := by linarith
    have h1 : (Real.log (|u| + T + 3)) ^ 2 ≤ (2 * L ^ (5 / 4 : ℝ)) ^ 2 := by
      nlinarith [hlog, hℓnn, hb]
    have h2 : (2 * L ^ (5 / 4 : ℝ)) ^ 2 = 4 * L ^ (5 / 2 : ℝ) := by
      have hx : (L ^ (5 / 4 : ℝ)) ^ 2 = L ^ (5 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (L ^ (5 / 4 : ℝ)) 2, ← Real.rpow_mul hLnn]
        norm_num
      rw [mul_pow, hx]; norm_num
    linarith
  -- (4) `y^{σ₁} ≤ y exp(-(c/4) L^{1/10})`
  have hbase : (c / 4) * L ^ (1 / 10 : ℝ) ≤ (1 - σ₁) * L := by
    have h1 : c * L / (4 * L ^ (9 / 10 : ℝ)) ≤ c * L / (4 * V) :=
      div_le_div_of_nonneg_left (mul_nonneg hc.le hLnn) (by linarith : (0 : ℝ) < 4 * V)
        (by linarith : 4 * V ≤ 4 * L ^ (9 / 10 : ℝ))
    have h2 : c * L / (4 * V) = (1 - σ₁) * L := by rw [hsig]; ring
    have hdiv : L / L ^ (9 / 10 : ℝ) = L ^ (1 / 10 : ℝ) := by
      have h := Real.rpow_sub hLpos (1 : ℝ) (9 / 10 : ℝ)
      rw [Real.rpow_one, show (1 : ℝ) - 9 / 10 = 1 / 10 from by norm_num] at h
      exact h.symm
    have h3 : c * L / (4 * L ^ (9 / 10 : ℝ)) = (c / 4) * L ^ (1 / 10 : ℝ) := by
      rw [show c * L / (4 * L ^ (9 / 10 : ℝ)) = (c / 4) * (L / L ^ (9 / 10 : ℝ)) by ring,
        hdiv]
    rw [← h3, ← h2]; exact h1
  have hy_sig : y ^ σ₁ ≤ y * Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) := by
    have hy1 : y ^ σ₁ = Real.exp (σ₁ * L) := by
      rw [hy, Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp]
      congr 1; ring
    have hy2 : y * Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) =
        Real.exp (L - (c / 4) * L ^ (1 / 10 : ℝ)) := by
      rw [hy, ← Real.exp_add]; congr 1; ring
    rw [hy1, hy2]
    apply Real.exp_le_exp.mpr
    linarith [hbase]
  -- (5) `log(1 + T/σ₁) ≤ 2 L^{5/4}`
  have hTσnn : 0 ≤ T / σ₁ := div_nonneg hT.le hsigpos.le
  have hDnn : 0 ≤ Real.log (1 + T / σ₁) := Real.log_nonneg (by linarith)
  have hD : Real.log (1 + T / σ₁) ≤ 2 * L ^ (5 / 4 : ℝ) := by
    have hTsig : T / σ₁ ≤ 2 * T := by
      rw [div_le_iff₀ hsigpos]
      nlinarith [hhalf, hT]
    have harg : 1 + T / σ₁ ≤ 2 * T + 3 := by linarith
    exact le_trans (Real.log_le_log (by linarith : (0 : ℝ) < 1 + T / σ₁) harg) hlogT
  -- (6) assemble
  have hSnn' : 0 ≤ B + C₅ + 1 + 4 / c := hSnn
  have hA'nn : 0 ≤ (B + C₅ + 1 + 4 / c) * L ^ (9 / 10 : ℝ) := mul_nonneg hSnn hP9nn
  have hL52nn : 0 ≤ 4 * L ^ (5 / 2 : ℝ) := by
    have : 0 ≤ L ^ (5 / 2 : ℝ) := Real.rpow_nonneg hLnn _
    linarith
  have hexp4nn : 0 ≤ Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) := (Real.exp_pos _).le
  have hD' : 2 * Real.sqrt 2 * Real.log (1 + T / σ₁) ≤ 2 * Real.sqrt 2 * (2 * L ^ (5 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have hD2nn : 0 ≤ 2 * Real.sqrt 2 * Real.log (1 + T / σ₁) :=
    mul_nonneg (by positivity) hDnn
  have step1 : (B + C₅ + 1 / (1 - σ₁) + 1) * (Real.log (|u| + T + 3)) ^ 2
      ≤ (B + C₅ + 1 + 4 / c) * L ^ (9 / 10 : ℝ) * (4 * L ^ (5 / 2 : ℝ)) :=
    mul_le_mul hA_le hℓ2 (sq_nonneg _) hA'nn
  have step2 : (B + C₅ + 1 / (1 - σ₁) + 1) * (Real.log (|u| + T + 3)) ^ 2 * y ^ σ₁
      ≤ (B + C₅ + 1 + 4 / c) * L ^ (9 / 10 : ℝ) * (4 * L ^ (5 / 2 : ℝ)) *
          (y * Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))) :=
    mul_le_mul step1 hy_sig (le_of_lt (Real.rpow_pos_of_pos hypos σ₁))
      (mul_nonneg hA'nn hL52nn)
  have step3 : (B + C₅ + 1 / (1 - σ₁) + 1) * (Real.log (|u| + T + 3)) ^ 2 * y ^ σ₁ *
        (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))
      ≤ (B + C₅ + 1 + 4 / c) * L ^ (9 / 10 : ℝ) * (4 * L ^ (5 / 2 : ℝ)) *
          (y * Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))) *
          (2 * Real.sqrt 2 * (2 * L ^ (5 / 4 : ℝ))) :=
    mul_le_mul step2 hD' hD2nn (mul_nonneg (mul_nonneg hA'nn hL52nn)
      (mul_nonneg hynn hexp4nn))
  have hcomb : (B + C₅ + 1 + 4 / c) * L ^ (9 / 10 : ℝ) * (4 * L ^ (5 / 2 : ℝ)) *
        (y * Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))) * (2 * Real.sqrt 2 * (2 * L ^ (5 / 4 : ℝ)))
      = 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (93 / 20 : ℝ) *
          Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) := by
    have hP : L ^ (9 / 10 : ℝ) * L ^ (5 / 2 : ℝ) * L ^ (5 / 4 : ℝ) = L ^ (93 / 20 : ℝ) := by
      rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos,
        show (9 / 10 : ℝ) + 5 / 2 + 5 / 4 = 93 / 20 from by norm_num]
    rw [← hP]; ring
  have hLpow : L ^ (93 / 20 : ℝ) ≤ L ^ (10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hexp_le : Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) ≤
      Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hx : 0 ≤ L ^ (1 / 10 : ℝ) := Real.rpow_nonneg hLnn _
    have hcc : c / 8 ≤ c / 4 := by linarith
    calc -(c / 4) * L ^ (1 / 10 : ℝ) = -((c / 4) * L ^ (1 / 10 : ℝ)) := by ring
      _ ≤ -((c / 8) * L ^ (1 / 10 : ℝ)) := neg_le_neg (mul_le_mul_of_nonneg_right hcc hx)
      _ = -(c / 8) * L ^ (1 / 10 : ℝ) := by ring
  have hC1nn : 0 ≤ 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y *
      Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hSnn)
      hynn) hexp4nn
  have hC2nn : 0 ≤ 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hSnn)
      hynn) (Real.rpow_nonneg hLnn 10)
  have hstepA : 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (93 / 20 : ℝ) *
        Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))
      ≤ 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
          Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) := by
    calc 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (93 / 20 : ℝ) *
          Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))
        = (16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y *
            Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))) * L ^ (93 / 20 : ℝ) := by ring
      _ ≤ (16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y *
            Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))) * L ^ (10 : ℝ) :=
          mul_le_mul_of_nonneg_left hLpow hC1nn
      _ = 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
            Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) := by ring
  have hstepB : 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
        Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))
      ≤ 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
          Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) := by
    calc 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
          Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ))
        = (16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ)) *
            Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) := by ring
      _ ≤ (16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ)) *
            Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp_le hC2nn
      _ = 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
            Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) := by ring
  have hMnn : 0 ≤ Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * L ^ (10 : ℝ) * y *
      Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hSnn)
      (Real.rpow_nonneg hLnn 10)) hynn) (Real.exp_pos _).le
  have hstepC : 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
        Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ))
      ≤ 24 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * L ^ (10 : ℝ) * y *
          Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) := by
    calc 16 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * y * L ^ (10 : ℝ) *
          Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ))
        = 16 * (Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * L ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ))) := by ring
      _ ≤ 24 * (Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * L ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ))) := by linarith
      _ = 24 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * L ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * L ^ (1 / 10 : ℝ)) := by ring
  exact le_trans step3 (le_trans (le_of_eq hcomb) (le_trans hstepA (le_trans hstepB hstepC)))

end Work.BMF.liouville
