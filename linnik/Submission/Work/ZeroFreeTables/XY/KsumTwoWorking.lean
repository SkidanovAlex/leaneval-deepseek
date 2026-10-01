import Mathlib
import Submission.Work.ZeroFreeTables.XY.KsumChiTwoZerosWindow
import Submission.Work.ZeroFreeTables.XY.WindowSumTwoWeak
import Submission.Work.ZeroFreeTables.XY.FarZeroSmall

namespace Work.ZeroFreeTables.XY

/-- **Xylouris's Lemma 3.4 (the "working form" of HB Lemma 5.2), two retained zeros, `A₂ = ∅`.**

This is the `F`-method consumer that the `XY` derivation needs and that
`KsumChiTwoZerosWindow` cannot supply: the two retained zeros `ρ`, `ρ'` need **not** lie in the
`δ`-window `‖1 + i·Im s - u‖ ≤ δ` (in the application `ρ' = conj ρ₁` sits at distance `2|Im ρ₁|`
from the window centre, which is far bigger than the window radius that HB Lemma 3.1 produces).
The price is the `o(L)` loss of the zeros outside the window, absorbed in the slack `ε`:
HB's own proof of Lemma 3.4 discards such terms by an integration-by-parts decay estimate.

Route, following the proof of `KsumChiTwoZerosWindow` (same file, same statement shape) and
`windowSum_ge_two`:
* start from `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim` (at `ε/2`),
  which bounds the `K`-sum by `-L · (window sum) + f(0)(c + ε/2)L`;
* drop from the window sum every zero with `Re u ≤ Re s` (Condition 2 makes its term `≥ 0`), so
  only the window zeros with `Re u > s.re` survive; by the last hypothesis these are `ρ`, `ρ'`;
* for each of `ρ`, `ρ'` that is *outside* the window, the term must be added back: it is
  bounded by `L · ord · ‖F((s-u)L)‖`, and `Commons.NumberTheory.Linnik.laplace_far_le`
  (integration by parts, with `|Im((s-u)L)| ≥ δL/2`, which follows from `u` being outside the
  window and `1 - u.re ≤ 1 - s.re ≤ √(log log q)/log q`) makes it `O(1/δ)` — bounded by
  `f(0)·(ε/2)·L` for `q ≥ q₀`, using the hypotheses `ord u ≤ 10` and `|Re((s-u)L)| ≤ 1`.
-/
theorem KsumTwoWorking (x₀ B c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {s ρ ρ' : ℂ},
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ 10 * Real.log (q : ℝ) →
        1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re →
        Commons.NumberTheory.Linnik.L52Hyp χ c (ε/2) δ →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0 →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ' ≠ 0 →
        ρ ≠ ρ' →
        s.re < ρ.re → s.re < ρ'.re →
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ ≤ 10) →
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ' ≤ 10) →
        |((s - ρ) * ((Real.log (q:ℝ) : ℝ) : ℂ)).re| ≤ 1 →
        |((s - ρ') * ((Real.log (q:ℝ) : ℝ) : ℂ)).re| ≤ 1 →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → s.re < u.re → u = ρ ∨ u = ρ') →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q : ℝ)))
          ≤ -(Real.log (q : ℝ)) *
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
                (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * ((Real.log q : ℝ) : ℂ)) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re)
            - (Real.log (q : ℝ)) *
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
                (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * ((Real.log q : ℝ) : ℂ)) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re)
            + f 0 * (c + ε) * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₁, h₁⟩ := (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim
      x₀ B c hx₀ hB) hcont hsupp hf2 hBnd hf0 (show (0:ℝ) < ε/2 by linarith) hδ0 hδ1
  obtain ⟨q₂, h₂⟩ := FarZeroSmall x₀ B hx₀ hB hcont hsupp hf2 hBnd hf0 hε hδ0
  refine ⟨max q₁ q₂, ?_⟩
  intro q _inst hq χ _instc hχ s ρ ρ' hsre hsim hs1 hH hdiv hdiv' hne hρ hρ' hord hord' hsh hsh' hzw
  have hq₁ : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq₂ : q₂ ≤ q := le_trans (le_max_right _ _) hq
  have hLnn : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg (by
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h1)
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
  have hDnn : ∀ u : ℂ, (0:ℤ) ≤ (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) u :=
    fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn) u
  have hKraw := h₁ hq₁ χ hχ hH s hsre hsim hs1
  set W : ℝ := (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * ((Real.log (q:ℝ) : ℝ) : ℂ)) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re) else 0)) with hWdef
  set Fρ : ℝ := (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ρ) * ((Real.log (q:ℝ) : ℝ) : ℂ)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re with hFρdef
  set Fρ' : ℝ := (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ρ') * ((Real.log (q:ℝ) : ℝ) : ℂ)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re with hFρ'def
  set dρ : ℝ := (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) with hdρdef
  set dρ' : ℝ := (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) with hdρ'def
  have hK : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q:ℝ)))
      ≤ -(Real.log (q:ℝ)) * W + f 0 * (c + ε/2) * Real.log (q:ℝ) := by
    simpa only [← hWdef] using hKraw
  have hlow : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then dρ * Fρ else 0)
      + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then dρ' * Fρ' else 0) ≤ W := by
    have hweak := WindowSumTwoWeak x₀ (Real.log (q:ℝ)) χ.primitiveCharacter hχ'
      (f := f) (s := s) (ρ := ρ) (ρ' := ρ') (δ := δ) hLnn hF hdiv hdiv' hne hρ hρ' hzw
    simpa only [← hWdef, ← hFρdef, ← hFρ'def, ← hdρdef, ← hdρ'def] using hweak
  have hfarρ : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then 0 else dρ * Fρ)
      ≤ f 0 * ε / 4 := by
    by_cases hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ
    · rw [if_pos hwin]; positivity
    · rw [if_neg hwin]
      have hbound : Fρ ≤ f 0 * ε / 40 := by
        have hb := h₂ hq₂ hsre hsh (not_le.mp hwin)
        simpa only [← hFρdef] using hb
      have hd1 : (1:ℝ) ≤ dρ := by
        rw [hdρdef]
        have hD1 : (1:ℤ) ≤ (MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ := by
          have := hDnn ρ; omega
        exact_mod_cast hD1
      have hd10 : dρ ≤ 10 := by rw [hdρdef]; exact_mod_cast hord
      have hmax : dρ * Fρ ≤ 10 * max Fρ 0 := by
        rcases le_total 0 Fρ with h | h
        · rw [max_eq_left h]; exact mul_le_mul_of_nonneg_right hd10 h
        · rw [max_eq_right h]; nlinarith [hd1, h]
      calc dρ * Fρ ≤ 10 * max Fρ 0 := hmax
        _ ≤ 10 * (f 0 * ε / 40) :=
            mul_le_mul_of_nonneg_left (max_le hbound (by positivity)) (by norm_num)
        _ = f 0 * ε / 4 := by ring
  have hfarρ' : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then 0 else dρ' * Fρ')
      ≤ f 0 * ε / 4 := by
    by_cases hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ
    · rw [if_pos hwin]; positivity
    · rw [if_neg hwin]
      have hbound : Fρ' ≤ f 0 * ε / 40 := by
        have hb := h₂ hq₂ hsre hsh' (not_le.mp hwin)
        simpa only [← hFρ'def] using hb
      have hd1 : (1:ℝ) ≤ dρ' := by
        rw [hdρ'def]
        have hD1 : (1:ℤ) ≤ (MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ' := by
          have := hDnn ρ'; omega
        exact_mod_cast hD1
      have hd10 : dρ' ≤ 10 := by rw [hdρ'def]; exact_mod_cast hord'
      have hmax : dρ' * Fρ' ≤ 10 * max Fρ' 0 := by
        rcases le_total 0 Fρ' with h | h
        · rw [max_eq_left h]; exact mul_le_mul_of_nonneg_right hd10 h
        · rw [max_eq_right h]; nlinarith [hd1, h]
      calc dρ' * Fρ' ≤ 10 * max Fρ' 0 := hmax
        _ ≤ 10 * (f 0 * ε / 40) :=
            mul_le_mul_of_nonneg_left (max_le hbound (by positivity)) (by norm_num)
        _ = f 0 * ε / 4 := by ring
  have hfar : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then 0 else dρ * Fρ)
      + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then 0 else dρ' * Fρ')
      ≤ f 0 * ε / 2 := by linarith only [hfarρ, hfarρ']
  have hA' : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then dρ * Fρ else 0)
      = dρ * Fρ - (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then 0 else dρ * Fρ) := by
    by_cases hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ
    · rw [if_pos hwin, if_pos hwin]; ring
    · rw [if_neg hwin, if_neg hwin]; ring
  have hB' : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then dρ' * Fρ' else 0)
      = dρ' * Fρ' - (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then 0 else dρ' * Fρ') := by
    by_cases hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ
    · rw [if_pos hwin, if_pos hwin]; ring
    · rw [if_neg hwin, if_neg hwin]; ring
  have hstep1 : -(Real.log (q:ℝ)) * W + f 0 * (c + ε/2) * Real.log (q:ℝ)
      ≤ -(Real.log (q:ℝ)) * ((if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then dρ * Fρ else 0)
          + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then dρ' * Fρ' else 0))
        + f 0 * (c + ε/2) * Real.log (q:ℝ) := by
    have hmul : -(Real.log (q:ℝ)) * W ≤ -(Real.log (q:ℝ)) *
        ((if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then dρ * Fρ else 0)
          + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then dρ' * Fρ' else 0)) :=
      mul_le_mul_of_nonpos_left hlow (neg_nonpos.mpr hLnn)
    exact add_le_add hmul le_rfl
  have hdec : -(Real.log (q:ℝ)) * ((if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then dρ * Fρ else 0)
          + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then dρ' * Fρ' else 0))
        + f 0 * (c + ε/2) * Real.log (q:ℝ)
      = -(Real.log (q:ℝ)) * (dρ * Fρ) - (Real.log (q:ℝ)) * (dρ' * Fρ')
        + (Real.log (q:ℝ)) * ((if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then 0 else dρ * Fρ)
          + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then 0 else dρ' * Fρ'))
        + f 0 * (c + ε/2) * Real.log (q:ℝ) := by
    rw [hA', hB']; ring
  have hstep2 : -(Real.log (q:ℝ)) * (dρ * Fρ) - (Real.log (q:ℝ)) * (dρ' * Fρ')
        + (Real.log (q:ℝ)) * ((if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then 0 else dρ * Fρ)
          + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then 0 else dρ' * Fρ'))
        + f 0 * (c + ε/2) * Real.log (q:ℝ)
      ≤ -(Real.log (q:ℝ)) * (dρ * Fρ) - (Real.log (q:ℝ)) * (dρ' * Fρ')
        + (Real.log (q:ℝ)) * (f 0 * ε / 2) + f 0 * (c + ε/2) * Real.log (q:ℝ) := by
    have hmul : (Real.log (q:ℝ)) *
          ((if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then 0 else dρ * Fρ)
            + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then 0 else dρ' * Fρ'))
        ≤ (Real.log (q:ℝ)) * (f 0 * ε / 2) := mul_le_mul_of_nonneg_left hfar hLnn
    exact add_le_add (add_le_add le_rfl hmul) le_rfl
  have htail : -(Real.log (q:ℝ)) * (dρ * Fρ) - (Real.log (q:ℝ)) * (dρ' * Fρ')
        + (Real.log (q:ℝ)) * (f 0 * ε / 2) + f 0 * (c + ε/2) * Real.log (q:ℝ)
      = -(Real.log (q:ℝ)) * (dρ * Fρ) - (Real.log (q:ℝ)) * (dρ' * Fρ')
        + f 0 * (c + ε) * Real.log (q:ℝ) := by ring
  exact hK.trans (hstep1.trans (hdec.le.trans (hstep2.trans htail.le)))

end Work.ZeroFreeTables.XY
