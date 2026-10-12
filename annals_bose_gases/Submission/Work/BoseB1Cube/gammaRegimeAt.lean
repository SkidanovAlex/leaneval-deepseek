import ChallengeDeps
import Submission.Work.BoseFixB1B.PerBoxSectorResidual
import Submission.Work.BoseFixB1B.RsbSide_sq_le_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.gammaRegimeAt` — the dilute-regime size bundle

Every one of the six size conditions that the cube chapter needs of an admissible
chemical potential holds for all sufficiently small diluteness `μ(a v)³`:

* `R ≤ ℓ d / 16` and `R ≤ ℓ·chiR0` — the support-radius conditions of the
  `C`-node and of the small-box subdivision, proved in
  `Work.BoseFixB1.regime_sideAt_ge` (both sides are closed monomials in
  `t = μ(a v)³` with negative exponents, so they blow up as `t → 0⁺`);
* `d ≤ 1/8` — `d = t^{6/323}`;
* `0 < 2Γ ≤ 1/2` — `Γ = K_B³(μ(a v)³)^{1/2} = t^{287/646}`, a fixed power of `t`;
* `128 R² ≤ 2Γ(ℓ d)²` — FS `eq:appRassumption`: with `ℓ d = a·t^{-157/323}` and
  `Γ = t^{287/646}`, the right-hand side is `2a²t^{-341/646}`, hence dominates the
  fixed `128R²`; this is `Work.BoseFixB1B.RsbSide_sq_le_holds` at the radius `8R`.

All six are monotone-`t` statements: each holds below an explicit positive
threshold, so the minimum of the finitely many thresholds works, and it may
depend on the fixed data `a v` and `R` only.
-/

namespace Work.BoseB1Cube

open scoped Real Topology BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- `t ^ p ≤ C` from `t ≤ C ^ q` when `q * p = 1` (`C ≥ 0`, `p ≥ 0`, `t > 0`):
raise the hypothesis to the power `p`. -/
lemma rpow_le_of_le_mul_eq_one {t p q C : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hpq : q * p = 1) (h : t ≤ C ^ q) : t ^ p ≤ C := by
  calc t ^ p ≤ (C ^ q) ^ p := Real.rpow_le_rpow ht.le h hp
    _ = C ^ (q * p) := (Real.rpow_mul hC q p).symm
    _ = C := by rw [hpq, Real.rpow_one]

/-- The four parameter-size conditions at small diluteness `t = μ a³`, for a bare
scattering length `a`:

    d ≤ 1/8,   0 < 2Γ ≤ 1/2,   128 R² ≤ 2Γ (ℓ d)²,      Γ = K_B³(μa³)^{1/2}.

The thresholds are `(1/8)^{323/6}`, `(1/4)^{646/287}` and `(a²/(8R)²)^{646/341}`. -/
private lemma gammaTail {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε →
      (Work.BoseBox.paramsAt μ a).d ≤ 1 / 8 ∧
      0 < 2 * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) ∧
      2 * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) ≤ 1 / 2 ∧
      128 * R ^ 2 ≤ 2 * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))
          * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 2 := by
  have hR8 : (0 : ℝ) < 8 * R := by linarith
  refine ⟨min (min ((1 / 8) ^ (323 / 6 : ℝ)) ((1 / 4) ^ (646 / 287 : ℝ)))
    ((a ^ 2 / (8 * R) ^ 2) ^ (646 / 341 : ℝ)), ?_, ?_⟩
  · refine lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  · intro μ hμ ht
    have ht0 : (0 : ℝ) < μ * a ^ 3 := mul_pos hμ (by positivity)
    have htd : μ * a ^ 3 ≤ (1 / 8) ^ (323 / 6 : ℝ) :=
      le_trans ht (le_trans (min_le_left _ _) (min_le_left _ _))
    have htg : μ * a ^ 3 ≤ (1 / 4) ^ (646 / 287 : ℝ) :=
      le_trans ht (le_trans (min_le_left _ _) (min_le_right _ _))
    have htR : μ * a ^ 3 ≤ (a ^ 2 / (8 * R) ^ 2) ^ (646 / 341 : ℝ) :=
      le_trans ht (min_le_right _ _)
    -- closed forms: `d = t^{6/323}`, `K_B³t^{1/2} = t^{287/646}`
    have hd_eq : (Work.BoseBox.paramsAt μ a).d = (μ * a ^ 3) ^ (6 / 323 : ℝ) := by
      rw [Work.BoseFixB1.d_eq_fsXp]
      rfl
    have hG_eq : (Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)
        = (μ * a ^ 3) ^ (287 / 646 : ℝ) := by
      rw [Work.BoseFixB1.KB3_half_eq ha hμ]
      simp only [Work.BoseBox.fsXp]
      norm_num
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hd_eq]
      exact rpow_le_of_le_mul_eq_one ht0 (by norm_num) (by norm_num) (by norm_num) htd
    · rw [hG_eq]
      positivity
    · rw [hG_eq]
      have h := rpow_le_of_le_mul_eq_one ht0 (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
        (by norm_num : (646 / 287 : ℝ) * (287 / 646) = 1) htg
      linarith
    · -- FS `eq:appRassumption` at the radius `8R`: `(8R/(ℓd))² ≤ Γ`
      set D : ℝ := (Work.BoseBox.paramsAt μ a).d * Work.BoseBox.sideAt μ a with hD
      have hDpos : 0 < D := by
        rw [hD]
        exact mul_pos (by rw [Work.BoseFixB1.d_eq_fsXp]; exact Work.BoseBox.fsXp_pos ht0)
          (Work.BoseBox.sideAt_pos hμ ha)
      have hRsb := Work.BoseFixB1B.RsbSide_sq_le_holds (A := a) (R := 8 * R) (μ := μ)
        ha hR8 hμ htR
      rw [← hD] at hRsb
      have hmul := mul_le_mul_of_nonneg_right hRsb (le_of_lt (pow_pos hDpos 2))
      have hstep : ((8 * R) / D) ^ 2 * D ^ 2 = (8 * R) ^ 2 := by
        rw [div_pow]
        field_simp
      rw [hstep] at hmul
      have hD2 : D ^ 2
          = (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 2 := by
        rw [hD]
        ring
      calc 128 * R ^ 2 = 2 * (8 * R) ^ 2 := by ring
        _ ≤ 2 * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ) * D ^ 2) := by
            linarith
        _ = 2 * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))
              * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 2 := by
            rw [hD2]
            ring

theorem gammaRegimeAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {μ : ℝ}, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 ∧
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 / 8 ∧
      0 < 2 * Work.BoseFixB1B.PBΓ v μ ∧ 2 * Work.BoseFixB1B.PBΓ v μ ≤ 1 / 2 ∧
      128 * R ^ 2 ≤ (2 * Work.BoseFixB1B.PBΓ v μ)
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 := by
  obtain ⟨ε₁, hε₁, hFS⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨ε₂, hε₂, htail⟩ := gammaTail (a := _root_.BoseGases.a v) hav hR
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro μ hAdm
  obtain ⟨hμ, ht, _⟩ := hAdm
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ := le_trans ht (min_le_left _ _)
  have ht2 : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₂ := le_trans ht (min_le_right _ _)
  obtain ⟨h1, h2⟩ := hFS μ hμ ht1
  obtain ⟨h3, h4, h5, h6⟩ := htail μ hμ ht2
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Work.BoseB1Cube
