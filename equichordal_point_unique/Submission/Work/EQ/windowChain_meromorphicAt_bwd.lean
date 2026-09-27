import Mathlib
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.meromorphicAt_punctured_bounded

namespace Work.EQ

/-- The multiplier `λ = (1-a)/(1+a) ∈ (0,1)` satisfies `λ^j ≤ λ` for every integer `j ≥ 1`. -/
theorem windowChain_eqLam_zpow_le_self {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {j : ℤ}
    (hj : 1 ≤ j) : eqLam a ^ j ≤ eqLam a := by
  have hne : eqLam a ≠ 0 := ne_of_gt (win_eqLam_pos ha0 ha1)
  rw [show j = 1 + (j - 1) by ring, zpow_add₀ hne]
  have h2 : 0 ≤ j - 1 := by omega
  have h3 : eqLam a ^ (j - 1) ≤ 1 := win_eqLam_zpow_le_one ha0 ha1 h2
  have h4 : 0 ≤ eqLam a ^ (1 : ℤ) := by
    rw [zpow_one]; exact le_of_lt (win_eqLam_pos ha0 ha1)
  calc eqLam a ^ (1 : ℤ) * eqLam a ^ (j - 1) ≤ eqLam a ^ (1 : ℤ) * 1 :=
        mul_le_mul_of_nonneg_left h3 h4
    _ = eqLam a ^ (1 : ℤ) := mul_one _
    _ = eqLam a := by rw [zpow_one]

/-- Backward-tail case of the meromorphy of the window chain: for `n < -m₁` the `n`-th entry of
`windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t` is `ugermC a h (λ^{-n} ψ₂ t)`, and both of its
coordinates are meromorphic at `0`. -/
theorem windowChain_meromorphicAt_bwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {n₁ m₁ : ℕ} {u κ : ℂ} {k : ℕ} {ρ ρg ρY : ℝ} (hρ : 0 < ρ) (hρg : 0 < ρg)
    (hρY : 0 < ρY) (hρYg : ρY ≤ ρg) {Yinv : ℂ → ℂ}
    {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}
    (hgerm_an : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hβan : ∀ j : Fin (n₁ + m₁ + 1), AnalyticOnNhd ℂ (fun t => β t j)
      (Metric.ball (0 : ℂ) ρ \ {0}))
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    {n : ℤ} (hn : n < -((m₁ : ℤ))) :
    MeromorphicAt (fun t => (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).1) 0 ∧
    MeromorphicAt (fun t => (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).2) 0 := by
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  have hlamPos : 0 < eqLam a := win_eqLam_pos ha0 ha1
  have hlamLt : eqLam a < 1 := win_eqLam_lt_one ha0 ha1
  -- the arguments of `germC` stay in the closed ball of radius `λ ρY`, which is inside `ρg`
  have hR : eqLam a * ρY < ρg := by
    have h1 : eqLam a * ρY ≤ eqLam a * ρg := mul_le_mul_of_nonneg_left hρYg (le_of_lt hlamPos)
    have h2 : eqLam a * ρg < 1 * ρg := mul_lt_mul_of_pos_right hlamLt hρg
    linarith
  -- analyticity of the pair-valued backward entry on the punctured disc
  have hpair := windowChain_analyticOnNhd_ugermC_zpow_mul_psi2 (n := n) ha0 ha1 hlam hYan
      (hβan (0 : Fin (n₁ + m₁ + 1))) hY3 hYim hβcurve hρYg hgerm_an hn
  -- the uniform bound `‖λ^{-n} ψ₂ t‖ ≤ λ ρY`
  have harg : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ‖((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t‖ ≤ eqLam a * ρY := by
    intro t ht
    obtain ⟨w, hw, hwne, hmul, -, -⟩ := windowChain_psi2_witness hlam hY3 hβcurve ht
    have hwlt : ‖w‖ < ρY := by simpa [Metric.mem_ball, dist_zero_right] using hw
    have hψ : psi2 a Yinv β t = w / ((eqLam a : ℝ) : ℂ) ^ m₁ := by
      rw [← hmul, eq_comm, div_eq_iff (pow_ne_zero _ hlam), mul_comm]
    rw [hψ, show ((eqLam a : ℝ) : ℂ) ^ m₁ = ((eqLam a : ℝ) : ℂ) ^ ((m₁ : ℕ) : ℤ) by simp,
      zpow_mul_div_eq _ _ hlam, norm_mul, norm_zpow, win_norm_eqLamC ha0 ha1]
    have hk : (1 : ℤ) ≤ -n - ((m₁ : ℕ) : ℤ) := by omega
    calc eqLam a ^ (-n - ((m₁ : ℕ) : ℤ)) * ‖w‖ ≤ eqLam a * ‖w‖ :=
          mul_le_mul_of_nonneg_right (windowChain_eqLam_zpow_le_self ha0 ha1 hk) (norm_nonneg w)
      _ ≤ eqLam a * ρY := mul_le_mul_of_nonneg_left (le_of_lt hwlt) (le_of_lt hlamPos)
  -- `germC a h` is bounded on the closed ball of radius `λ ρY`
  obtain ⟨M, hM⟩ :=
    exists_norm_bound_germC (a := a) (h := h) (ρg := ρg) (R := eqLam a * ρY) hR hgerm_an
  -- analyticity of the two coordinates on the punctured disc
  have han1 : AnalyticOnNhd ℂ
      (fun t => (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).1)
      (Metric.ball (0 : ℂ) ρ \ {0}) :=
    fun t ht => AnalyticAt.comp
      (f := fun s => ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β s))
      (g := fun p : ℂ × ℂ => p.1)
      (ContinuousLinearMap.analyticAt (ContinuousLinearMap.fst ℂ ℂ ℂ)
        (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)))
      (hpair t ht)
  have han2 : AnalyticOnNhd ℂ
      (fun t => (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).2)
      (Metric.ball (0 : ℂ) ρ \ {0}) :=
    fun t ht => AnalyticAt.comp
      (f := fun s => ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β s))
      (g := fun p : ℂ × ℂ => p.2)
      (ContinuousLinearMap.analyticAt (ContinuousLinearMap.snd ℂ ℂ ℂ)
        (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)))
      (hpair t ht)
  -- and both are bounded there by `M`
  have hb1 : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ‖(ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).1‖ ≤ M := by
    intro t ht
    have hg : ‖germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)‖ ≤ M := hM _ (harg t ht)
    calc ‖(ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).1‖
        = ‖(germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).1‖ := by
          simp [ugermC, eqMirror]
      _ ≤ ‖germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)‖ := norm_fst_le _
      _ ≤ M := hg
  have hb2 : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ‖(ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).2‖ ≤ M := by
    intro t ht
    have hg : ‖germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)‖ ≤ M := hM _ (harg t ht)
    calc ‖(ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).2‖
        = ‖(germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)).2‖ := by
          simp [ugermC, eqMirror]
      _ ≤ ‖germC a h (((eqLam a : ℝ) : ℂ) ^ (-n) * psi2 a Yinv β t)‖ := norm_snd_le _
      _ ≤ M := hg
  exact ⟨meromorphicAt_punctured_bounded hρ han1 hb1, meromorphicAt_punctured_bounded hρ han2 hb2⟩

end Work.EQ
