import Mathlib
import Submission.Work.A7.osc_deriv_bounds
import Submission.Work.KMTAreas.A7.M0PolyDerivBound

namespace Work.KMTAreas.A7

/-- **First-derivative bound for the oscillatory phase `momFun` in the frequency window
`|ξ₁| ≤ X₁/N`, `|ξ₂| ≤ X₂/N^d`.**  From the growth bound `|P'| ≤ A N^d/N` on `[0,N]` and `N ≥ 1`,
the chain-rule formula `(momFun)' = momFun · 2πi(ξ₁ + ξ₂P')` gives
`‖(momFun)' u‖ ≤ 2π max(1,A) (X₁+X₂+1)/N` for every `u ∈ [0,N]`. -/
lemma momFun_deriv_window_bound (P : Polynomial ℤ) {A : ℝ} (hA : 0 ≤ A)
    (hder : ∀ (N : ℕ), 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (X₁ X₂ ξ₁ ξ₂ : ℝ), 1 ≤ N → 0 ≤ X₁ → 0 ≤ X₂ →
      |ξ₁| ≤ X₁ / (N : ℝ) → |ξ₂| ≤ X₂ / ((N : ℝ) ^ P.natDegree) →
      ∀ u ∈ Set.Icc (0 : ℝ) (N : ℝ),
        ‖deriv (Work.A7.momFun P ξ₁ ξ₂) u‖ ≤ C * (X₁ + X₂ + 1) / (N : ℝ) := by
  refine ⟨2 * Real.pi * max 1 A, by positivity, ?_⟩
  intro N X₁ X₂ ξ₁ ξ₂ hN hX₁ hX₂ hξ₁ hξ₂ u hu
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  -- the growth bound on `P'` (which is `deriv (PevalR P)`)
  have hP' : |Work.KMTPlan.A6.PderivR P u| ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ) := by
    have h1 : Work.KMTPlan.A6.PderivR P u
        = (P.derivative.map (Int.castRingHom ℝ)).eval u := rfl
    rw [h1, ← Work.A7.Pev.deriv_PevalR]
    exact hder N hN u hu
  -- the `ξ₂ P'` term
  have h2 : |ξ₂| * |Work.KMTPlan.A6.PderivR P u| ≤ A * X₂ / (N : ℝ) := by
    calc |ξ₂| * |Work.KMTPlan.A6.PderivR P u|
        ≤ (X₂ / (N : ℝ) ^ P.natDegree) * (A * (N : ℝ) ^ P.natDegree / (N : ℝ)) :=
          mul_le_mul hξ₂ hP' (abs_nonneg _) (by positivity)
      _ = A * X₂ / (N : ℝ) := by
          field_simp (disch := positivity)
  -- the frequency factor
  have hsum : |ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P u|
      ≤ (max 1 A) * (X₁ + X₂ + 1) / (N : ℝ) := by
    have hstep1 : |ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P u|
        ≤ X₁ / (N : ℝ) + A * X₂ / (N : ℝ) := by
      calc |ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P u|
          ≤ |ξ₁| + |ξ₂ * Work.KMTPlan.A6.PderivR P u| := abs_add_le _ _
        _ = |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P u| := by rw [abs_mul]
        _ ≤ X₁ / (N : ℝ) + A * X₂ / (N : ℝ) := add_le_add hξ₁ h2
    refine hstep1.trans ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hN0
    have hM1 : (1 : ℝ) ≤ max 1 A := le_max_left _ _
    have hMA : A ≤ max 1 A := le_max_right _ _
    have hX₁' : X₁ ≤ max 1 A * X₁ := by
      calc X₁ = 1 * X₁ := by ring
        _ ≤ max 1 A * X₁ := mul_le_mul_of_nonneg_right hM1 hX₁
    have hX₂' : A * X₂ ≤ max 1 A * X₂ := mul_le_mul_of_nonneg_right hMA hX₂
    have h3 : max 1 A * X₁ + max 1 A * X₂ ≤ max 1 A * (X₁ + X₂ + 1) := by
      nlinarith [hX₁, hX₂, hM1, hA]
    linarith
  -- the norm of the frequency factor
  have hnorm : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I
      * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P u : ℝ) : ℂ))‖
      = 2 * Real.pi * |ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P u| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
      rw [Work.A7.norm_ofReal_eq_abs, abs_of_pos Real.pi_pos]
    have hcast : (ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P u : ℝ) : ℂ)
        = ((ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P u : ℝ) : ℂ) := by push_cast; ring
    rw [htwo, hpi, hcast, Work.A7.norm_ofReal_eq_abs]
  rw [Work.A7.momFun_deriv_formula, norm_mul, Work.A7.momFun_norm_eq_one, one_mul, hnorm]
  calc 2 * Real.pi * |ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P u|
      ≤ 2 * Real.pi * ((max 1 A) * (X₁ + X₂ + 1) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * Real.pi * max 1 A * (X₁ + X₂ + 1) / (N : ℝ) := by ring

/-- Pointwise bound for the differentiated oscillatory weight
`m0w P ξ₁ ξ₂ j₁ j₂ u = (2πiu)^{j₁}(2πiP(u))^{j₂} e(ξ₁u+ξ₂P(u))` of the §6 model approximation,
on the physical window `u ∈ [0,N]`, under the frequency constraints `|ξ₁| ≤ X₁/N`,
`|ξ₂| ≤ X₂/N^d` (`d = P.natDegree`) and `j₁,j₂ ≤ 2`: the value is `≲ N^{j₁+dj₂}` and the
derivative is `≲ (X₁+X₂+1) N^{j₁+dj₂-1}`. -/
theorem M0WDerivBound (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (ξ₁ ξ₂ X₁ X₂ : ℝ) (j₁ j₂ : ℕ),
        1 ≤ N → j₁ ≤ 2 → j₂ ≤ 2 → 1 ≤ X₁ → 1 ≤ X₂ →
        |ξ₁| ≤ X₁ / (N : ℝ) → |ξ₂| ≤ X₂ / ((N : ℝ) ^ P.natDegree) →
        ∀ u ∈ Set.Icc (0 : ℝ) (N : ℝ),
          ‖Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u‖
              ≤ C * (N : ℝ) ^ (((j₁ + P.natDegree * j₂ : ℕ) : ℝ)) ∧
          ‖deriv (Work.A7.m0w P ξ₁ ξ₂ j₁ j₂) u‖
              ≤ C * (X₁ + X₂ + 1) * (N : ℝ) ^ ((((j₁ + P.natDegree * j₂ : ℕ) : ℝ)) - 1) := by
  -- the polynomial growth bounds on `PevalR P` (value, first and second derivative), with a
  -- single constant `A`
  obtain ⟨A, hApos, hA⟩ := Work.A7.Pev.PevalR_deriv_bounds P
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hApos
  -- the value and first-derivative bounds for `m0poly`, with a single constant `B`
  obtain ⟨B, hBpos, hB⟩ := M0PolyDerivBound P hA0
    (fun N hN t ht => (hA N hN t ht).1) (fun N hN t ht => (hA N hN t ht).2.1)
  -- the first-derivative bound for the oscillatory phase `momFun`, with a single constant `C₁`
  obtain ⟨C₁, hC₁pos, hC₁⟩ := momFun_deriv_window_bound P hA0
    (fun N hN t ht => (hA N hN t ht).2.1)
  refine ⟨max 1 (B * (1 + C₁)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro N ξ₁ ξ₂ X₁ X₂ j₁ j₂ hN hj₁ hj₂ hX₁ hX₂ hξ₁ hξ₂ u hu
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  have hBC : B ≤ max 1 (B * (1 + C₁)) := by
    refine le_trans ?_ (le_max_right _ _)
    nlinarith [hBpos, hC₁pos]
  have hX1nn : (0 : ℝ) ≤ X₁ := by linarith
  have hX2nn : (0 : ℝ) ≤ X₂ := by linarith
  have hBval : ‖Work.A7.m0poly P j₁ j₂ u‖ ≤ B * (N : ℝ) ^ (j₁ + P.natDegree * j₂) :=
    (hB N hN u hu j₁ j₂ hj₁ hj₂).1
  have hBder : ‖deriv (Work.A7.m0poly P j₁ j₂) u‖
      ≤ B * (N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ) :=
    (hB N hN u hu j₁ j₂ hj₁ hj₂).2
  have hMval : ‖deriv (Work.A7.momFun P ξ₁ ξ₂) u‖ ≤ C₁ * (X₁ + X₂ + 1) / (N : ℝ) :=
    hC₁ N X₁ X₂ ξ₁ ξ₂ hN hX1nn hX2nn hξ₁ hξ₂ u hu
  constructor
  · -- the value bound: `‖m0w‖ = ‖m0poly‖ · ‖momFun‖ = ‖m0poly‖`
    rw [show Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u
          = Work.A7.m0poly P j₁ j₂ u * Work.A7.momFun P ξ₁ ξ₂ u from rfl,
      norm_mul, Work.A7.momFun_norm_eq_one, mul_one, Real.rpow_natCast]
    exact hBval.trans (mul_le_mul_of_nonneg_right hBC (by positivity))
  · -- the derivative bound: product rule for `m0w = m0poly · momFun`
    have hd1 : DifferentiableAt ℝ (Work.A7.m0poly P j₁ j₂) u :=
      ((Work.A7.contDiff_m0poly P j₁ j₂).differentiable (by simp)).differentiableAt
    have hd2 : DifferentiableAt ℝ (Work.A7.momFun P ξ₁ ξ₂) u :=
      ((Work.A7.momFun_contDiff P ξ₁ ξ₂).differentiable (by norm_num)).differentiableAt
    have hdmul : deriv (Work.A7.m0w P ξ₁ ξ₂ j₁ j₂) u
        = deriv (Work.A7.m0poly P j₁ j₂) u * Work.A7.momFun P ξ₁ ξ₂ u
          + Work.A7.m0poly P j₁ j₂ u * deriv (Work.A7.momFun P ξ₁ ξ₂) u := by
      rw [show Work.A7.m0w P ξ₁ ξ₂ j₁ j₂
            = Work.A7.m0poly P j₁ j₂ * Work.A7.momFun P ξ₁ ξ₂ from rfl,
        deriv_mul hd1 hd2]
    have hstep : B * (1 + C₁ * (X₁ + X₂ + 1))
          * ((N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ))
        ≤ max 1 (B * (1 + C₁)) * (X₁ + X₂ + 1)
          * ((N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ)) := by
      have h2 : B * (1 + C₁ * (X₁ + X₂ + 1)) ≤ B * (1 + C₁) * (X₁ + X₂ + 1) := by
        have hthis : 1 + C₁ * (X₁ + X₂ + 1) ≤ (1 + C₁) * (X₁ + X₂ + 1) := by
          nlinarith [hC₁pos, hX1nn, hX2nn]
        calc B * (1 + C₁ * (X₁ + X₂ + 1)) ≤ B * ((1 + C₁) * (X₁ + X₂ + 1)) :=
              mul_le_mul_of_nonneg_left hthis hBpos.le
          _ = B * (1 + C₁) * (X₁ + X₂ + 1) := by ring
      have h3 : B * (1 + C₁) * (X₁ + X₂ + 1) ≤ max 1 (B * (1 + C₁)) * (X₁ + X₂ + 1) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith [hX1nn, hX2nn])
      exact mul_le_mul_of_nonneg_right (le_trans h2 h3) (div_nonneg (by positivity) hN0)
    rw [hdmul]
    calc ‖deriv (Work.A7.m0poly P j₁ j₂) u * Work.A7.momFun P ξ₁ ξ₂ u
            + Work.A7.m0poly P j₁ j₂ u * deriv (Work.A7.momFun P ξ₁ ξ₂) u‖
        ≤ ‖deriv (Work.A7.m0poly P j₁ j₂) u * Work.A7.momFun P ξ₁ ξ₂ u‖
            + ‖Work.A7.m0poly P j₁ j₂ u * deriv (Work.A7.momFun P ξ₁ ξ₂) u‖ :=
          norm_add_le _ _
      _ = ‖deriv (Work.A7.m0poly P j₁ j₂) u‖
            + ‖Work.A7.m0poly P j₁ j₂ u‖ * ‖deriv (Work.A7.momFun P ξ₁ ξ₂) u‖ := by
          rw [norm_mul, norm_mul, Work.A7.momFun_norm_eq_one, mul_one]
      _ ≤ B * (N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ)
            + (B * (N : ℝ) ^ (j₁ + P.natDegree * j₂))
              * (C₁ * (X₁ + X₂ + 1) / (N : ℝ)) :=
          add_le_add hBder (mul_le_mul hBval hMval (norm_nonneg _) (by positivity))
      _ = B * (1 + C₁ * (X₁ + X₂ + 1))
            * ((N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ)) := by
          field_simp [ne_of_gt hNpos]
      _ ≤ max 1 (B * (1 + C₁)) * (X₁ + X₂ + 1)
            * ((N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ)) := hstep
      _ = max 1 (B * (1 + C₁)) * (X₁ + X₂ + 1)
            * ((N : ℝ) ^ (((j₁ + P.natDegree * j₂ : ℕ) : ℝ) - 1)) := by
          rw [Real.rpow_sub hNpos, Real.rpow_natCast, Real.rpow_one]

end Work.KMTAreas.A7
