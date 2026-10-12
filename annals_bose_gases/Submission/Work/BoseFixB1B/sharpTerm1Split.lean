import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.SmallBoxBogolubovKinetic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.sharpTerm1Split` — the sharp first-term split of the sliding Bogoliubov chain

Holder: the holder of `Submission/Work/BoseFixB1B/slidingBogPortPrescribedEps.lean`.

FS's `lm:appbogolubov` (`final_v2.tex` l.3762–3822) splits the |q|-integral of the Bogoliubov
coefficient `(𝒜−√(𝒜²−ℬ²))/2` (`eq:simpleaprioribog`'s "main term against the sharp ∫Ŵ₁²/p²,
the complementary piece paid in C_ε").  Where the corpus's proved chain (`term1IntegralBound`)
uses the crude `[|q|−c]₊² ≥ ‖q‖²/4` (a factor 4) and the *crude* Newtonian constant `K_s`, this
module gives the SHARP version:

* `bogCoeff_le` — the pointwise improvement `(A−√(A²−B²))/2 ≤ (1+τ²)B²/(4A)` for `|B| ≤ τA`,
  `τ ≤ 1` (the exact Bogoliubov coefficient is `B²/(2(A+√(A²−B²)))`, and
  `1/(1+√(1−τ²)) ≤ (1+τ²)/2`);
* `inv_sq_sub_le` — the elementary comparison `1/(r−c)² ≤ (1+8δ)/r²` for `c/δ ≤ r`, `δ ≤ 1/2`;
* `sharpTerm1Bound` — the resulting split bound

      (2π)⁻³∫ (A−√(A²−B²))/2 ≤ (1+τ²)[ Kc²av·c³/(48π²K_sVδ³)
                                    + (1+8δ)(N+2)/(4V²)·(2π)⁻³∫g²/‖q‖² ]

  with `τ = Kc/(2K_s)`, `A q = fsKinCoeff c ‖q‖/(N+2) + 2K_s·av/V`, `B q = g q/V`,
  `|g| ≤ Kc·av`: the low band `‖q‖ < c/δ` is bounded by the constant `(1+τ²)Kc²av/(8K_sV)`, and
  on `‖q‖ ≥ c/δ` one has `A ≥ [‖q‖−c]₊²/(N+2)` and the sharp `1/(‖q‖−c)² ≤ (1+8δ)/‖q‖²`.

All three are `sorry`-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Volume of a `ℝ³`-ball, `toReal` form. -/
theorem ballVol_toReal (r : ℝ) (hr : 0 ≤ r) :
    ((volume : Measure E3) (Metric.ball (0 : E3) r)).toReal = 4 / 3 * Real.pi * r ^ 3 := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **The improved one-mode Bogoliubov coefficient bound.**  For `0 < A`, `0 ≤ τ ≤ 1`,
`|B| ≤ τ·A`,

    (A − √(A²−B²))/2 ≤ (1+τ²)·B²/(4A) .

The exact coefficient satisfies `(A−√(A²−B²))/2 = B²/(2(A+√(A²−B²)))`, and with
`t := B²/A² ≤ τ²` one has `1/(1+√(1−t)) ≤ 1/(1+√(1−τ²)) ≤ (1+τ²)/2`, the last because
`(1+τ²)(1+√(1−τ²)) ≥ (1+τ²)(2−τ²) ≥ 2` when `0 ≤ τ ≤ 1`. -/
theorem bogCoeff_le {A B τ : ℝ} (hA : 0 < A) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hB : |B| ≤ τ * A) :
    (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 ≤ (1 + τ ^ 2) * B ^ 2 / (4 * A) := by
  have hAB : B ^ 2 ≤ τ ^ 2 * A ^ 2 := by
    have h := abs_le.mp hB
    nlinarith [h.1, h.2, hτ0, hA, sq_nonneg (τ * A - B), sq_nonneg (τ * A + B)]
  have hτsq : τ ^ 2 ≤ 1 := by nlinarith [hτ0, hτ1]
  have hA2pos : 0 < A ^ 2 := pow_pos hA 2
  have hsqnonneg : 0 ≤ A ^ 2 - B ^ 2 := by nlinarith [hAB, hA2pos, hτsq]
  set s := Real.sqrt (A ^ 2 - B ^ 2) with hs
  have hs2 : s ^ 2 = A ^ 2 - B ^ 2 := Real.sq_sqrt hsqnonneg
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsA : s ≤ A := by
    have h1 : s ^ 2 ≤ A ^ 2 := by nlinarith [hs2, sq_nonneg B]
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_nonneg hs0, abs_of_pos hA] at h2
  have hden : 0 < A + s := by linarith
  have hkey : (A - s) * (A + s) = B ^ 2 := by nlinarith [hs2]
  have hcoeff : (A - s) / 2 = B ^ 2 / (2 * (A + s)) := by
    rw [eq_div_iff (by positivity : (2 : ℝ) * (A + s) ≠ 0)]
    nlinarith [hkey]
  have hsq1 : 0 ≤ 1 - τ ^ 2 := by linarith
  have hs1 : A * Real.sqrt (1 - τ ^ 2) ≤ s := by
    have h1 : A ^ 2 * (1 - τ ^ 2) ≤ A ^ 2 - B ^ 2 := by nlinarith [hAB]
    have h3 : Real.sqrt (A ^ 2 * (1 - τ ^ 2)) ≤ Real.sqrt (A ^ 2 - B ^ 2) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul (le_of_lt hA2pos), Real.sqrt_sq hA.le] at h3
    exact h3
  have hsq1' : Real.sqrt (1 - τ ^ 2) ≥ 1 - τ ^ 2 := by
    nlinarith [Real.sq_sqrt hsq1, Real.sqrt_nonneg (1 - τ ^ 2), hsq1]
  have hden2 : A * (1 + Real.sqrt (1 - τ ^ 2)) ≤ A + s := by nlinarith [hs1]
  have hfac : 1 / (A + s) ≤ (1 + τ ^ 2) / (2 * A) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have h2 : (1 + τ ^ 2) * (A + s) ≥ (1 + τ ^ 2) * (A * (1 + Real.sqrt (1 - τ ^ 2))) := by
      nlinarith [hden2, le_of_lt hden]
    have h3 : (1 + τ ^ 2) * (1 + Real.sqrt (1 - τ ^ 2)) ≥ 2 := by
      have h4 : 1 + Real.sqrt (1 - τ ^ 2) ≥ 2 - τ ^ 2 := by linarith
      have h5 : 0 ≤ 1 + τ ^ 2 := by positivity
      have h6 := mul_le_mul_of_nonneg_left h4 h5
      nlinarith [h6, hτsq]
    have h7 := mul_le_mul_of_nonneg_left h3 (le_of_lt hA)
    nlinarith [h2, h7]
  rw [hcoeff]
  calc B ^ 2 / (2 * (A + s)) = B ^ 2 / 2 * (1 / (A + s)) := by field_simp
    _ ≤ B ^ 2 / 2 * ((1 + τ ^ 2) / (2 * A)) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (1 + τ ^ 2) * B ^ 2 / (4 * A) := by field_simp; ring

/-- **Elementary comparison.** For `0 < δ ≤ 1/2` and `c/δ ≤ r`, `1/(r−c)² ≤ (1+8δ)/r²`. -/
theorem inv_sq_sub_le {c r δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hr : c / δ ≤ r) : 1 / (r - c) ^ 2 ≤ (1 + 8 * δ) / r ^ 2 := by
  have h2c : 2 * c ≤ c / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith [hδ1, hc, hδ]
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity : 0 < c / δ) hr
  have hrc : 0 < r - c := by linarith [hr, h2c]
  have hu0 : 0 ≤ c / r := by positivity
  have huδ : c / r ≤ δ := by
    rw [div_le_iff₀ hr0]
    calc c ≤ r * δ := (div_le_iff₀ hδ).mp hr
      _ = δ * r := by ring
  have hu2 : c / r ≤ 1 / 2 := le_trans huδ hδ1
  have hkey : 1 ≤ (1 + 8 * (c / r)) * (1 - c / r) ^ 2 := by
    have hu0' : 1 - c / r ≥ 0 := by linarith
    nlinarith [hu0, hu2, sq_nonneg (1 - c / r), sq_nonneg (c / r),
      mul_nonneg hu0 (sq_nonneg (1 - c / r))]
  have h8 : (1 + 8 * (c / r)) * (1 - c / r) ^ 2 ≤ (1 + 8 * δ) * (1 - c / r) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hmain : 1 ≤ (1 + 8 * δ) * (1 - c / r) ^ 2 := le_trans hkey h8
  have h1 : 1 - c / r = (r - c) / r := by field_simp
  rw [h1, div_pow] at hmain
  rw [div_le_div_iff₀ (pow_pos hrc 2) (pow_pos hr0 2)]
  have hexp : (1 + 8 * δ) * ((r - c) ^ 2 / r ^ 2) * r ^ 2 = (1 + 8 * δ) * (r - c) ^ 2 := by
    field_simp
  nlinarith [hmain, hexp, sq_nonneg r]

/-- **The sharp first-term split of the sliding Bogoliubov chain.**  With
`A q := fsKinCoeff c ‖q‖/(N+2) + 2K_s·(a v)/V` and `|g q| ≤ Kc·(a v)`,

    (2π)⁻³∫ (A − √(A² − B²))/2 dq  ≤  (1+τ²)·[ Kc²av·c³/(48π²K_sVδ³)
        + (1+8δ)(N+2)/(4V²)·(2π)⁻³∫ g²/‖q‖² ]

for `τ = Kc/(2K_s)`, `Kc ≤ 2K_s`, `0 < δ ≤ 1/2`, `B q = g q/V` and
`(2π)⁻³∫g²/‖q‖² < ∞`.  The two pieces are the low band `‖q‖ < c/δ` (where
`(A−√(A²−B²))/2 ≤ (1+τ²)Kc²av/(8K_sV)`) and its complement (where `A ≥ [‖q‖−c]₊²/(N+2)`
and `1/(‖q‖−c)² ≤ (1+8δ)/‖q‖²`). -/
theorem sharpTerm1Bound {N : ℕ} {V c Kc Ks av δ : ℝ} {g : E3 → ℝ}
    (hV : 0 < V) (hc : 0 < c) (hKs : 0 < Ks) (hav : 0 < av) (hKc : 0 ≤ Kc)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hKsKc : Kc ≤ 2 * Ks)
    (hsup : ∀ q : E3, |g q| ≤ Kc * av)
    (hfin : MeasureTheory.Integrable (fun q : E3 => g q ^ 2 / ‖q‖ ^ 2))
    (hIntQ : MeasureTheory.Integrable (fun q : E3 =>
      (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V
        - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V) ^ 2
            - (g q / V) ^ 2)) / 2)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
        (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V
          - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V) ^ 2
              - (g q / V) ^ 2)) / 2
      ≤ (1 + Kc ^ 2 / (4 * Ks ^ 2)) *
          ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
            + (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2) *
                ( ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) ) ) := by
  set A : E3 → ℝ := fun q => 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
    + 2 * Ks * av / V with hA
  set B : E3 → ℝ := fun q => g q / V with hB
  set Φ : E3 → ℝ := fun q => (A q - Real.sqrt (A q ^ 2 - B q ^ 2)) / 2 with hΦ
  have hApos : ∀ q : E3, 0 < A q := by
    intro q
    rw [hA]
    have h1 : 0 ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
      mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
    have h2 : 0 < 2 * Ks * av / V := by positivity
    linarith
  have hAge : ∀ q : E3, 2 * Ks * av / V ≤ A q := by
    intro q; rw [hA]
    have h1 : 0 ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
      mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
    linarith
  have hAle : ∀ q : E3, 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ ≤ A q := by
    intro q; rw [hA]
    have h2 : 0 ≤ 2 * Ks * av / V := by positivity
    linarith
  have hτ0 : 0 ≤ Kc / (2 * Ks) := by positivity
  have hτ1 : Kc / (2 * Ks) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hBle : ∀ q : E3, |B q| ≤ (Kc / (2 * Ks)) * A q := by
    intro q
    have h1 : |B q| ≤ Kc * av / V := by
      rw [hB, abs_div, abs_of_pos hV]
      exact div_le_div_of_nonneg_right (hsup q) hV.le
    have h2 : Kc * av / V ≤ (Kc / (2 * Ks)) * A q := by
      have h3 : (Kc / (2 * Ks)) * (2 * Ks * av / V) ≤ (Kc / (2 * Ks)) * A q :=
        mul_le_mul_of_nonneg_left (hAge q) hτ0
      have h4 : (Kc / (2 * Ks)) * (2 * Ks * av / V) = Kc * av / V := by field_simp
      rw [h4] at h3
      exact h3
    linarith
  have hΦle : ∀ q : E3, Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * B q ^ 2 / (4 * A q) := by
    intro q
    rw [hΦ]
    exact bogCoeff_le (hApos q) hτ0 hτ1 (hBle q)
  set s : Set E3 := Metric.ball (0 : E3) (c / δ) with hs
  have hsmeas : MeasurableSet s := measurableSet_ball
  have hsvol : ((volume : Measure E3) s).toReal = 4 / 3 * Real.pi * (c / δ) ^ 3 := by
    rw [hs]
    exact ballVol_toReal (c / δ) (by positivity)
  have hsplit := MeasureTheory.integral_add_compl hsmeas hIntQ
  -- ### the ball piece
  have hball : ∫ q in s, Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V))
      * ((volume : Measure E3) s).toReal := by
    have hpt : ∀ q ∈ s, Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V)) := by
      intro q _
      have h1 := hΦle q
      have hB2 : B q ^ 2 ≤ (Kc * av / V) ^ 2 := by
        rw [hB]
        have h3 : |g q / V| ≤ Kc * av / V := by
          rw [abs_div, abs_of_pos hV]
          exact div_le_div_of_nonneg_right (hsup q) hV.le
        have h4 : (0:ℝ) ≤ Kc * av / V := by positivity
        nlinarith [h3, h4, abs_nonneg (g q / V), sq_abs (g q / V)]
      have hAgeq := hAge q
      have h5 : B q ^ 2 / (4 * A q) ≤ (Kc * av / V) ^ 2 / (4 * (2 * Ks * av / V)) := by
        have hAg : (0:ℝ) < 2 * Ks * av / V := by positivity
        rw [div_le_div_iff₀ (by linarith [hApos q]) (by linarith)]
        nlinarith [hB2, hAgeq, sq_nonneg (B q), le_of_lt hAg, le_of_lt (hApos q)]
      have h6 : (Kc * av / V) ^ 2 / (4 * (2 * Ks * av / V)) = Kc ^ 2 * av / (8 * Ks * V) := by
        field_simp <;> ring
      have h7 : 0 ≤ 1 + (Kc / (2 * Ks)) ^ 2 := by positivity
      calc Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * B q ^ 2 / (4 * A q) := h1
        _ = (1 + (Kc / (2 * Ks)) ^ 2) * (B q ^ 2 / (4 * A q)) := by ring
        _ ≤ (1 + (Kc / (2 * Ks)) ^ 2) * ((Kc * av / V) ^ 2 / (4 * (2 * Ks * av / V))) :=
            mul_le_mul_of_nonneg_left h5 h7
        _ = (1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V)) := by rw [h6]
    have hposv : (0:ℝ) < 4 / 3 * Real.pi * (c / δ) ^ 3 := by positivity
    have hvolne : (volume : Measure E3) s ≠ ⊤ := by
      intro h
      rw [h] at hsvol
      simp only [ENNReal.toReal_top] at hsvol
      linarith
    have hmono : ∫ q in s, Φ q
        ≤ ∫ q in s, (fun _ : E3 => (1 + (Kc / (2 * Ks)) ^ 2)
            * (Kc ^ 2 * av / (8 * Ks * V))) q :=
      MeasureTheory.setIntegral_mono_on hIntQ.integrableOn
        (MeasureTheory.integrableOn_const hvolne) hsmeas hpt
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real_def,
      mul_comm] at hmono
    exact hmono
  -- ### the complement piece
  have hcomp : ∫ q in sᶜ, Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
      * ((N : ℝ) + 2) / (4 * V ^ 2) * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) := by
    have hpt : ∀ q ∈ sᶜ, Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
        * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2) := by
      intro q hq
      have hq' : c / δ ≤ ‖q‖ := by
        rw [hs, Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_zero_right] at hq
        exact hq
      have hcδ : c < c / δ := by
        rw [lt_div_iff₀ hδ]
        nlinarith [hδ1, hc, hδ]
      have hqc : c < ‖q‖ := lt_of_lt_of_le hcδ hq'
      have hkin : Submission.BoseGases.fsKinCoeff c ‖q‖ = (‖q‖ - c) ^ 2 := by
        rw [Submission.BoseGases.fsKinCoeff, max_eq_left]
        linarith
      have hstep1 : B q ^ 2 / (4 * A q)
          ≤ g q ^ 2 / V ^ 2 / (4 * (1 / ((N : ℝ) + 2) * (‖q‖ - c) ^ 2)) := by
        rw [hB]
        have hle : 1 / ((N : ℝ) + 2) * (‖q‖ - c) ^ 2 ≤ A q := by
          have h := hAle q
          rw [hkin] at h
          exact h
        have hpos : (0:ℝ) < 4 * (1 / ((N : ℝ) + 2) * (‖q‖ - c) ^ 2) := by positivity
        have hstep : 4 * (1 / ((N : ℝ) + 2) * (‖q‖ - c) ^ 2) ≤ 4 * A q := by linarith
        have hgoal : (g q / V) ^ 2 * (4 * (1 / ((N : ℝ) + 2) * (‖q‖ - c) ^ 2))
            ≤ (g q / V) ^ 2 * (4 * A q) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        rw [div_le_div_iff₀ (by linarith [hApos q]) hpos]
        simpa [div_pow] using hgoal
      have hstep2 : g q ^ 2 / V ^ 2 / (4 * (1 / ((N : ℝ) + 2) * (‖q‖ - c) ^ 2))
          ≤ (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2) := by
        have hinv := inv_sq_sub_le hc hδ hδ1 hq'
        have heq : g q ^ 2 / V ^ 2 / (4 * (1 / ((N : ℝ) + 2) * (‖q‖ - c) ^ 2))
            = ((N : ℝ) + 2) * g q ^ 2 / (4 * V ^ 2) * (1 / (‖q‖ - c) ^ 2) := by
          field_simp <;> ring
        rw [heq]
        have h2 : ((N : ℝ) + 2) * g q ^ 2 / (4 * V ^ 2) * (1 / (‖q‖ - c) ^ 2)
            ≤ ((N : ℝ) + 2) * g q ^ 2 / (4 * V ^ 2) * ((1 + 8 * δ) / ‖q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        have h3 : ((N : ℝ) + 2) * g q ^ 2 / (4 * V ^ 2) * ((1 + 8 * δ) / ‖q‖ ^ 2)
            = (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2) := by
          field_simp <;> ring
        linarith [h2, h3.le, h3.ge]
      have h7 : 0 ≤ 1 + (Kc / (2 * Ks)) ^ 2 := by positivity
      calc Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * B q ^ 2 / (4 * A q) := hΦle q
        _ = (1 + (Kc / (2 * Ks)) ^ 2) * (B q ^ 2 / (4 * A q)) := by ring
        _ ≤ (1 + (Kc / (2 * Ks)) ^ 2) *
              ((1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) h7
        _ = (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
              * (g q ^ 2 / ‖q‖ ^ 2) := by ring
    have hthis : IntegrableOn (fun q : E3 => (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
        * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)) sᶜ :=
      (hfin.const_mul _).integrableOn
    have hmono : ∫ q in sᶜ, Φ q ≤ ∫ q in sᶜ, (fun q : E3 => (1 + (Kc / (2 * Ks)) ^ 2)
        * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)) q :=
      MeasureTheory.setIntegral_mono_on hIntQ.integrableOn hthis hsmeas.compl hpt
    have hle : ∫ q in sᶜ, (fun q : E3 => (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
        * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)) q
        ≤ ∫ q : E3, (fun q : E3 => (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
        * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)) q :=
      MeasureTheory.setIntegral_le_integral ((hfin.const_mul _))
        (Filter.Eventually.of_forall fun q => by positivity)
    have hrew : ∫ q : E3, (fun q : E3 => (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
        * ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)) q
        = (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
          * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    rw [hrew] at hle
    have hshape : (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
        = (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2) := by ring
    linarith [hmono, hle, hshape.le, hshape.ge]
  -- ### combine
  have hsum : ∫ q : E3, Φ q ≤ (1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V))
        * ((volume : Measure E3) s).toReal
      + (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
        * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) := by
    linarith [hsplit, hball, hcomp]
  have hτsq : (Kc / (2 * Ks)) ^ 2 = Kc ^ 2 / (4 * Ks ^ 2) := by ring
  have hc0 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  have hfinal : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3, Φ q
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V))
          * ((volume : Measure E3) s).toReal
        + (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
          * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum hc0
  rw [hsvol] at hfinal
  rw [hΦ] at hfinal
  refine le_trans hfinal ?_
  have hP : ((2 * Real.pi) ^ 3)⁻¹ * ((1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V))
        * (4 / 3 * Real.pi * (c / δ) ^ 3))
      = (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)) := by
    rw [← hτsq]
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp <;> ring
  have hQ : ((2 * Real.pi) ^ 3)⁻¹ * ((1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
        * ((N : ℝ) + 2) / (4 * V ^ 2) * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2))
      = (1 + Kc ^ 2 / (4 * Ks ^ 2)) * ((1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
        * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2))) := by
    rw [← hτsq]
    field_simp <;> ring
  calc ((2 * Real.pi) ^ 3)⁻¹ * ((1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V))
          * (4 / 3 * Real.pi * (c / δ) ^ 3)
        + (1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
          * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2))
      = ((2 * Real.pi) ^ 3)⁻¹ * ((1 + (Kc / (2 * Ks)) ^ 2) * (Kc ^ 2 * av / (8 * Ks * V))
          * (4 / 3 * Real.pi * (c / δ) ^ 3))
        + ((2 * Real.pi) ^ 3)⁻¹ * ((1 + (Kc / (2 * Ks)) ^ 2) * (1 + 8 * δ)
          * ((N : ℝ) + 2) / (4 * V ^ 2) * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2)) := by
        rw [mul_add]
    _ = (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3))
        + (1 + Kc ^ 2 / (4 * Ks ^ 2)) * ((1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
          * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2))) := by
        rw [hP, hQ]
    _ = (1 + Kc ^ 2 / (4 * Ks ^ 2)) *
          ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
            + (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * V ^ 2)
                * ( ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) ) ) := by
        ring
  exact le_rfl

end Work.BoseFixB1B
