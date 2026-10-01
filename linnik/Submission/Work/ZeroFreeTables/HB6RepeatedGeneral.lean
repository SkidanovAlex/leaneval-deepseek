/-
# ZeroFreeTables — HB6RepeatedGeneral

**The §6 repeated-zero inequality for a possibly complex doubled zero** — the general form of
`hb6Repeated` that `HBRepZeroStrict.lean` calls.  See `NOTE_HB6RepeatedGeneral_repair.md` for the
derivation; in brief, with `β = Re ρ₁`, `γ = Im ρ₁`:

* `Ksum_positivity` (`Commons/NumberTheory/Linnik/Ksum_positivity.lean`) at `χ₂ = 1`, `γ₂ = 0`
  gives the **pair** positivity `0 ≤ 2·K(β,χ₀) + 2·K(β+iγ,χ₁)` — the `χ₂ = 1` case needs no
  reality hypothesis on `χ₁` and brings in no `χ₁²` term;
* HB Lemma 5.2 at `s = ρ₁` together with the window bound `2F(0) ≤ winSum(ρ₁)`
  (`winSum_two_mul_complex`, the doubled zero lies in its own window by `hw`) gives
  `K(ρ₁,χ₁) ≤ −2L·F(0) + f(0)(c+ε)L`;
* HB Lemma 5.3 (`principalKsumWide`) at the *real* point `β` gives
  `K(β,χ₀) ≤ L·F(−λ₁) + f(0)(ε/2)L` (no `cos` factor: the principal bound sees only `Re s`).

Summing with the weights `2, 2` and dividing by `L > 0` yields the conclusion.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l63
import Submission.Work.NumberTheory.Linnik.scratch_l52phi_imprim
import Submission.Work.LinnikAreas.principalKsumWide
import Submission.Work.ZeroFreeTables.winSum_two_mul_complex
import Submission.Commons.NumberTheory.Linnik.Ksum_positivity

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

theorem HB6RepeatedGeneral {x₀ B c ε δ : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] {ρ₁ : ℂ} (hχ1 : χ₁ ≠ 1)
        (hmult : 2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁)
        (him1 : |ρ₁.im| ≤ 1)
        (hpt : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hw : |1 - ρ₁.re| ≤ δ)
        (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 10 → u.re ≤ ρ₁.re)
        (H : Commons.NumberTheory.Linnik.L52Hyp χ₁ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - ρ₁.re)) * t) * f t)
          - 4 * (∫ t in (0:ℝ)..x₀, f t)
          + f 0 * (2 * c + 3 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn
  obtain ⟨q₀p, hq₀p⟩ := (Work.LinnikAreas.principalKsumWide x₀ B hx₀ hB)
    hcont hsupp hf2 hBnd (show (0:ℝ) < ε/2 by linarith) hf0
  obtain ⟨q₀χ, hq₀χ⟩ :=
    (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
      hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨max (max q₀p q₀χ) 6, ?_⟩
  intro q _inst hq χ₁ _ic ρ₁ hχ1 hmult him1 hpt hw hmin H
  have hq6 : 6 ≤ q := le_trans (le_max_right _ _) hq
  have hqp : q₀p ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqχ : q₀χ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hlogq : (0 : ℝ) < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := le_of_lt hlogq
  have hlogq10 : |ρ₁.im| ≤ 10 * Real.log (q : ℝ) := by
    have h6 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 3 ≤ q)
      linarith [Real.exp_one_lt_three]
    calc |ρ₁.im| ≤ 1 := him1
      _ ≤ 10 * Real.log (q : ℝ) := by linarith
  have Hraw : ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
      (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
        ≤ (c + ε/4) * Real.log (q : ℝ) := H
  -- #### the pair positivity (Ksum_positivity at χ₂ = 1, γ₂ = 0)
  have hpos := Commons.NumberTheory.Linnik.Ksum_positivity (f := f) hfnn hx₀ hlogq hsupp
    (χ₁ := χ₁) (χ₂ := (1 : DirichletCharacter ℂ q)) (β := ρ₁.re) (γ₁ := ρ₁.im) (γ₂ := 0)
    (L := Real.log (q : ℝ))
  simp only [mul_one, inv_one, Complex.ofReal_zero, add_zero, sub_zero, zero_mul] at hpos
  rw [Complex.re_add_im ρ₁] at hpos
  -- #### HB Lemma 5.2 at `s = ρ₁`, with the doubled zero in the window
  have hsmall : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 →
      ‖(1:ℂ) + (ρ₁.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ρ₁.re := by
    intro u hu huw
    have h1 : ((1:ℂ) + (ρ₁.im : ℂ) * Complex.I - u).im = ρ₁.im - u.im := by
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im, Complex.one_re,
        mul_zero, mul_one, add_zero, zero_add, sub_zero]
    have h2 : |ρ₁.im - u.im| ≤ δ := by
      rw [← h1]
      exact le_trans (Complex.abs_im_le_norm _) huw
    have h3 : |u.im| ≤ |ρ₁.im| + δ := by
      have h5 := abs_le.mp h2
      rw [abs_le]
      exact ⟨by linarith [h5.1, h5.2, neg_abs_le ρ₁.im], by linarith [h5.1, h5.2, le_abs_self ρ₁.im]⟩
    exact hmin u hu (by linarith [h3, him1, hδ1])
  have hwin_norm : ‖(1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
    have : (1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hw
  have hwinn : 2 * (∫ t in (0:ℝ)..x₀, f t)
      ≤ Commons.NumberTheory.Linnik.winSum χ₁.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ ρ₁ :=
    winSum_two_mul_complex (q := q) χ₁ hχ1 (f := f) (x₀ := x₀) (L := Real.log (q : ℝ))
      (δ := δ) (s := ρ₁) hLnn hδ1 (fun z hz => hFnn z hz) hwin_norm hmult hsmall
  have hbχ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ (n : ZMod q) / (n : ℂ) ^ (ρ₁)).re) * f (Real.log n / Real.log (q : ℝ)))
      ≤ -(Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
        + f 0 * (c + ε) * Real.log (q : ℝ) := by
    have h := hq₀χ hqχ χ₁ hχ1 Hraw ρ₁ (by simpa using hpt) hlogq10
      (by have := (abs_le.mp hpt).1; linarith)
    simp only [Commons.NumberTheory.Linnik.winSum] at hwinn
    linarith only [h, mul_le_mul_of_nonneg_left hwinn hLnn]
  -- #### HB Lemma 5.3 at the real point `Re ρ₁` (kept in its raw complex-integral form)
  have hp : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ ((ρ₁.re : ℝ) : ℂ)).re *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ (Real.log (q : ℝ)) * (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((((ρ₁.re : ℝ) : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re
        + f 0 * (ε/2) * Real.log (q : ℝ) := by
    have h := hq₀p hqp (β := ρ₁.re) (γ := 0) (by simpa using hpt)
      (by simp only [abs_zero]; linarith)
    simpa using h
  -- the Laplace integral at the real point `Re ρ₁` is `∫ e^{λ₁t} f`
  have hintF : ∀ z : ℂ, IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)) MeasureTheory.volume
        (0:ℝ) x₀ := by
    intro z
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx₀.le]
    have h1 : Continuous (fun t : ℝ => Complex.exp (-(z * (t : ℂ)))) :=
      Complex.continuous_exp.comp (((continuous_const : Continuous fun _ : ℝ => z).mul
        Complex.continuous_ofReal).neg)
    have h2 : ContinuousOn (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Icc 0 x₀) :=
      Complex.continuous_ofReal.comp_continuousOn (hcont.mono Set.Icc_subset_Ici_self)
    exact h1.continuousOn.mul h2
  have hAeq : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((ρ₁.re : ℝ) : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      = (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - ρ₁.re)) * t) * f t) := by
    rw [Commons.NumberTheory.Linnik.re_laplace_eq
      (hintF ((((ρ₁.re : ℝ) : ℂ) - 1) * (Real.log (q : ℝ))))]
    apply intervalIntegral.integral_congr
    intro t _
    have ha : ((((ρ₁.re : ℝ) : ℂ) - 1)).im = 0 := by simp
    have hr : ((((ρ₁.re : ℝ) : ℂ) - 1)).re = ρ₁.re - 1 := by simp
    rw [Commons.NumberTheory.Linnik.re_mul_log (((ρ₁.re : ℝ) : ℂ) - 1) q,
      Commons.NumberTheory.Linnik.im_mul_log (((ρ₁.re : ℝ) : ℂ) - 1) q, hr, ha]
    simp only [zero_mul, Real.cos_zero, mul_one]
    congr 1
    ring
  -- #### combine
  have hsum : 0 ≤ (Real.log (q : ℝ)) *
      (2 * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - ρ₁.re)) * t) * f t)
        - 4 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (2 * c + 3 * ε)) := by
    have key : 0 ≤ 2 * ((Real.log (q : ℝ)) *
          (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((ρ₁.re : ℝ) : ℂ) - 1) * (Real.log (q : ℝ))) * (t : ℂ))) *
              ((f t : ℝ) : ℂ)).re
          + f 0 * (ε/2) * Real.log (q : ℝ))
        + 2 * (-(Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
          + f 0 * (c + ε) * Real.log (q : ℝ)) := by
      linarith only [hpos, hp, hbχ]
    rw [hAeq] at key
    have hfac : 2 * ((Real.log (q : ℝ)) *
          (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - ρ₁.re)) * t) * f t)
          + f 0 * (ε/2) * Real.log (q : ℝ))
        + 2 * (-(Real.log (q : ℝ)) * (2 * (∫ t in (0:ℝ)..x₀, f t))
          + f 0 * (c + ε) * Real.log (q : ℝ))
        = (Real.log (q : ℝ)) *
          (2 * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - ρ₁.re)) * t) * f t)
            - 4 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (2 * c + 3 * ε)) := by
      ring
    rw [hfac] at key
    exact key
  exact (mul_nonneg_iff_of_pos_left hlogq).mp hsum

end Work.ZeroFreeTables
