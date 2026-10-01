import Mathlib
import Submission.Work.ZeroDensity.Jutila.jutilaNonPrincipal
import Submission.Work.ZeroDensity.Jutila.boxMass_le_linnikLocal

namespace Work.ZeroDensity.LogFree

open scoped Classical BigOperators

/-- `boxIdx Δ ρ` is by definition `⌊Im ρ / Δ⌋`. -/
lemma boxIdx_eq_floor (Δ : ℝ) (ρ : ℂ) :
    Work.ZeroDensity.Jutila.boxIdx Δ ρ = ⌊ρ.im / Δ⌋ := rfl

/-!
# The per-box mass bound, uniformly for a threshold `σL ≤ σ`

This is the generalisation of `Work.ZeroDensity.Jutila.boxMass_le_linnik_real` needed by the
box-upgrade step of the log-free non-principal zero-density estimate (`LogFree/boxUpgradeOfParams`).

The point of the statement is that the *threshold* entering the zero-density square
(`σL ≤ Re ρ`) and the width of the square (`1 - σL`) may both be smaller than the threshold `σ`
of the box (`σ ≤ Re ρ ≤ 1`).  Since `σL ≤ σ`, the box `σ ≤ Re ρ ≤ 1`, `⌊Im ρ/Δ⌋ = k` is contained
in the square `σL ≤ Re ρ ≤ 1`, `|Im ρ - τ| ≤ (1-σL)/2` for the centre `τ = max(kΔ,-T) + (1-σL)/2`,
because `Δ ≤ 1 - σL`; Linnik's density lemma at an arbitrary real height
(`Work.ZeroDensity.Jutila.linnikDensityRealGen`, valid for every `0 ≤ σL ≤ 1`) then bounds the
mass of that square by `≪ (1-σL)·log(q(|τ|+2)) + 1`, and `|τ| ≤ T + 1/2` in the only case where
the box is non-empty.
-/

theorem boxMassGeneral_aux :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σL σ T Δ : ℝ, 0 ≤ σL → σL ≤ σ → σ ≤ 1 → 1 ≤ T → 0 < Δ → Δ ≤ 1 - σL → ∀ k : ℤ,
        (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧
            ⌊ρ.im / Δ⌋ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ C₀ * ((1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
  obtain ⟨C, hC, hbnd⟩ := Work.ZeroDensity.Jutila.linnikDensityRealGen
  refine ⟨3 * C, by linarith, ?_⟩
  intro q hq _inst χ hχ σL σ T Δ hσL0 hσLσ hσ1 hT hΔpos hΔle k
  have hσL1 : σL ≤ 1 := le_trans hσLσ hσ1
  have hF : (0 : ℝ) ≤ 1 - σL := by linarith
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by linarith
  -- the centre of the enclosing square
  set a : ℝ := max ((k : ℝ) * Δ) (-T) with ha
  set τ : ℝ := a + (1 - σL) / 2 with hτ
  -- the box is contained in the square of half width `(1-σL)/2` centred at `τ`
  have hcont : ∀ ρ : ℂ, σ ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T → ⌊ρ.im / Δ⌋ = k →
      |ρ.im - τ| ≤ (1 - σL) / 2 := by
    intro ρ _ _ him hfl
    obtain ⟨hlb, hub⟩ := Work.ZeroDensity.Jutila.im_box_bounds hΔpos hfl
    have hge : a ≤ ρ.im := by
      rw [ha]
      exact max_le hlb (abs_le.mp him).1
    have hlt : ρ.im < a + (1 - σL) := by
      rw [ha]
      rcases le_total ((k : ℝ) * Δ) (-T) with hle | hle
      · rw [max_eq_right hle]; nlinarith [hub, hΔle]
      · rw [max_eq_left hle]; nlinarith [hub, hΔle]
    rw [hτ, abs_le]
    constructor <;> linarith
  -- finiteness of the two supports
  have hfinL : Function.HasFiniteSupport (fun ρ : ℂ =>
      if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    rw [Function.HasFiniteSupport]
    refine (Work.ZeroDensity.Jutila.zeroSupport_finite' χ σ T).subset ?_
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
    · rw [if_pos hc] at hρ
      rw [Function.mem_support, if_pos ⟨hc.1, hc.2.1, hc.2.2.1⟩]
      exact hρ
    · rw [if_neg hc] at hρ
      exact absurd rfl hρ
  have hfinR : Function.HasFiniteSupport (fun ρ : ℂ =>
      if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σL ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - τ| ≤ (1 - σL) / 2
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) :=
    Work.ZeroDensity.Jutila.zeroMult_boxSupport_finite χ σL τ ((1 - σL) / 2)
  -- pointwise domination
  have hpoint : ∀ ρ : ℂ,
      (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      ≤ (if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σL ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - τ| ≤ (1 - σL) / 2
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    intro ρ
    by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
    · rw [if_pos hc]
      by_cases hz : Work.LinnikContract.zeroMult χ ρ = 0
      · rw [hz]; simp
      · rw [if_pos ⟨hz, le_trans hσLσ hc.1, hc.2.1, hcont ρ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2⟩]
    · rw [if_neg hc]
      by_cases hd : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σL ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - τ| ≤ (1 - σL) / 2
      · rw [if_pos hd]; exact Nat.cast_nonneg _
      · rw [if_neg hd]
  have hle1 := finsum_le_finsum' hfinL hfinR hpoint
  rcases lt_or_ge T a with hbig | hsmall
  · -- the box lies strictly above `T`: it is empty
    have hzero : (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) = 0 := by
      rw [show (∑ᶠ ρ : ℂ, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
            then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)) = ∑ᶠ _ : ℂ, (0 : ℝ) from
        finsum_congr (fun ρ => by
          refine if_neg ?_
          rintro ⟨-, -, him, hfl⟩
          have hlb := (Work.ZeroDensity.Jutila.im_box_bounds hΔpos hfl).1
          have hge : a ≤ ρ.im := by
            rw [ha]
            exact max_le hlb (abs_le.mp him).1
          have hle : ρ.im ≤ T := (abs_le.mp him).2
          linarith)]
      simp
    rw [hzero]
    have hL : (0 : ℝ) ≤ Real.log ((q : ℝ) * (T + 1)) :=
      Real.log_nonneg (by nlinarith)
    have hpos : (0 : ℝ) ≤ (1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 1 := by nlinarith
    exact mul_nonneg (by linarith) hpos
  · -- `a ≤ T`, so `|τ| ≤ T + 1/2`
    have ha_abs : |a| ≤ T := abs_le.mpr ⟨by rw [ha]; exact le_max_right _ _, hsmall⟩
    have htau : |τ| ≤ T + 1 / 2 := by
      rw [hτ]
      calc |a + (1 - σL) / 2| ≤ |a| + |(1 - σL) / 2| := abs_add_le _ _
        _ = |a| + (1 - σL) / 2 := by
            rw [abs_of_nonneg (show (0 : ℝ) ≤ (1 - σL) / 2 by linarith)]
        _ ≤ T + 1 / 2 := by linarith
    -- Linnik's density lemma at the threshold `σL` and the centre `τ`
    refine le_trans hle1 (le_trans (hbnd q χ hχ σL τ hσL0 hσL1) ?_)
    have hqT : (0 : ℝ) < (q : ℝ) * (T + 1) := by nlinarith
    have hlog : Real.log ((q : ℝ) * (|τ| + 2)) ≤ Real.log ((q : ℝ) * (T + 1)) + 1 := by
      have h1 : |τ| + 2 ≤ (7 / 4) * (T + 1) := by linarith
      have h2 : (q : ℝ) * (|τ| + 2) ≤ (7 / 4) * ((q : ℝ) * (T + 1)) := by
        calc (q : ℝ) * (|τ| + 2) ≤ (q : ℝ) * ((7 / 4) * (T + 1)) :=
              mul_le_mul_of_nonneg_left h1 hq0
          _ = (7 / 4) * ((q : ℝ) * (T + 1)) := by ring
      have h3 : (0 : ℝ) < (q : ℝ) * (|τ| + 2) := by nlinarith [abs_nonneg τ]
      have hA : Real.log ((q : ℝ) * (|τ| + 2)) ≤ Real.log ((7 / 4) * ((q : ℝ) * (T + 1))) :=
        Real.log_le_log h3 h2
      have hB : Real.log ((7 : ℝ) / 4 * ((q : ℝ) * (T + 1)))
          = Real.log (7 / 4) + Real.log ((q : ℝ) * (T + 1)) :=
        Real.log_mul (by norm_num) (ne_of_gt hqT)
      have h74 : Real.log (7 / 4) ≤ 3 / 4 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 4 by norm_num)
        linarith
      linarith
    have hL0 : (0 : ℝ) ≤ Real.log ((q : ℝ) * (T + 1)) := Real.log_nonneg (by nlinarith)
    have hstep : (1 - σL) * Real.log ((q : ℝ) * (|τ| + 2))
        ≤ (1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 1 := by
      have := mul_le_mul_of_nonneg_left hlog hF
      linarith
    have hY : (0 : ℝ) ≤ (1 - σL) * Real.log ((q : ℝ) * (T + 1)) := mul_nonneg hF hL0
    have hCX : C * ((1 - σL) * Real.log ((q : ℝ) * (|τ| + 2)) + 1)
        ≤ C * ((1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 2) := by
      have h := mul_le_mul_of_nonneg_left hstep hC.le
      linarith
    have hCY : C * ((1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 2)
        ≤ 3 * C * ((1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
      nlinarith [hY, hC]
    linarith [hCX, hCY]

theorem boxMassGeneral :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σL σ T Δ : ℝ, 0 ≤ σL → σL ≤ σ → σ ≤ 1 → 1 ≤ T → 0 < Δ → Δ ≤ 1 - σL → ∀ k : ℤ,
        (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧
            Work.ZeroDensity.Jutila.boxIdx Δ ρ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ C₀ * ((1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
  obtain ⟨C₀, hC₀, h⟩ := boxMassGeneral_aux
  exact ⟨C₀, hC₀, h⟩

end Work.ZeroDensity.LogFree
