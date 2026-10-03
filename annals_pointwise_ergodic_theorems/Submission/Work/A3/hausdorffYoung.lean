import Mathlib
import Submission.Work.A3.kmtSum_eLpNorm_two_le
import Submission.Work.A3.kmtPair_le_one
import Submission.Work.A3.exists_simpleFunc_eq_of_vanishes_off
import Submission.Work.A3.kmtPair_decomposition

/-!
# Hausdorff--Young on `ℤ`

For `1 < p ≤ 2` and a finitely supported `f : ℤ → ℂ`,

`‖f̂‖_{L^{p'}([0,1])} ≤ ‖f‖_{ℓ^p(ℤ)}`,  `p' = p/(p-1)`,

where `f̂(θ) = ∑_x f(x) e(-xθ)` (`Work.A3.kmtFhat`), the measure on `[0,1]` is Lebesgue measure
and the measure on `ℤ` is counting measure.

This is the classical proof: `f̂` is the trigonometric polynomial `kmtSum s f` (with `s` a finite
support of `f`), and one interpolates the two endpoint estimates for the pairing

`kmtPair s u v = ∫₀¹ (∑_{x∈s} u x e(-xθ)) v(θ) dθ`

— the `(ℓ¹, L¹)` estimate `‖kmtPair s u v‖ ≤ ‖u‖_{ℓ¹}‖v‖_{L¹}` (`kmtPair_le_one`) and the
`(ℓ², L²)` estimate `‖kmtPair s u v‖ ≤ ‖u‖_{ℓ²}‖v‖_{L²}` (`kmtPair_le_two`, from Cauchy--Schwarz
and Parseval/Plancherel for trigonometric polynomials) — by Stein's bilinear interpolation
(`Work.Analysis.Interpolation.stein_bilinear_of_decomposition`), and then dualises the resulting
`ℓ^p × L^p → ℂ` estimate with `eLpNorm_eq_iSup_simpleFunc_integral` to obtain the `L^{p'}`
bound on `f̂`.  The endpoint `p = 2` is Plancherel itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.A3

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-! ## The `(ℓ², L²)` endpoint estimate for the pairing -/

/-- The `(ℓ², L²)` endpoint estimate for the pairing: Cauchy--Schwarz together with
Parseval/Plancherel for the truncated Fourier sum. -/
theorem kmtPair_le_two (s : Finset ℤ) (u : ℤ → ℂ) (v : ℝ → ℂ) :
    ‖kmtPair s u v‖ₑ ≤ eLpNorm u 2 Measure.count * eLpNorm v 2 kmtNu := by
  by_cases hv : AEMeasurable v kmtNu
  · rw [kmtPair_of_aemeasurable hv]
    refine (Work.Analysis.Interpolation.enorm_integral_mul_le (ν := kmtNu) (q := 2) one_lt_two
      (aemeasurable_kmtSum s u) hv).trans ?_
    have h2a : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
    have h2b : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
    rw [h2a, h2b]
    exact mul_le_mul_of_nonneg_right (kmtSum_eLpNorm_two_le s u) zero_le
  · rw [kmtPair_of_not_aemeasurable hv]
    simp

theorem hausdorffYoung (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) (s : Finset ℤ) (g : ℤ → ℂ) : MeasureTheory.eLpNorm (fun θ : ℝ => Work.A3.kmtFhat (fun x : ℤ => if x ∈ s then g x else 0) θ) (ENNReal.ofReal (p / (p - 1))) (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ MeasureTheory.eLpNorm (fun x : ℤ => if x ∈ s then g x else 0) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  set f : ℤ → ℂ := fun x => if x ∈ s then g x else 0 with hfdef
  have hfsupp : ∀ x ∉ s, f x = 0 := by
    intro x hx
    rw [hfdef]
    simp [hx]
  change eLpNorm (fun θ : ℝ => kmtFhat f θ) (ENNReal.ofReal (p / (p - 1))) kmtNu
    ≤ eLpNorm f (ENNReal.ofReal p) Measure.count
  rcases lt_or_eq_of_le hp2 with hp2lt | hp2eq
  · -- the case `1 < p < 2`: interpolation plus duality
    have hp_pos : 0 < p := lt_trans zero_lt_one hp1
    have hp1' : 0 < p - 1 := by linarith
    set θ : ℝ := 2 * (p - 1) / p with hθdef
    have hθ_pos : 0 < θ := by rw [hθdef]; positivity
    have hθ_lt : θ < 1 := by
      rw [hθdef, div_lt_one hp_pos]
      linarith
    have hpθ : 1 / p = (1 - θ) / 1 + θ / 2 := by
      rw [hθdef]
      field_simp
      ring
    have hq : 1 < p / (p - 1) := by
      rw [one_lt_div hp1']
      linarith
    have hconj : p / (p - 1) / (p / (p - 1) - 1) = p := by
      field_simp
      ring
    obtain ⟨F, hF⟩ := exists_simpleFunc_eq_of_vanishes_off s f hfsupp
    -- the two endpoint estimates for the pairing
    have h0 : ∀ u : ℤ → ℂ, ∀ v : ℝ → ℂ,
        ‖kmtPair s u v‖ₑ ≤ (1 : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal 1) Measure.count
          * eLpNorm v (ENNReal.ofReal 1) kmtNu := by
      intro u v
      simpa using kmtPair_le_one s u v
    have h1 : ∀ u : ℤ → ℂ, ∀ v : ℝ → ℂ,
        ‖kmtPair s u v‖ₑ ≤ (1 : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal 2) Measure.count
          * eLpNorm v (ENNReal.ofReal 2) kmtNu := by
      intro u v
      simpa using kmtPair_le_two s u v
    -- Stein interpolation for each simple test function
    have hstein : ∀ h : SimpleFunc ℝ ℂ, eLpNorm (h : ℝ → ℂ) (ENNReal.ofReal p) kmtNu ≤ 1 →
        ‖kmtPair s (F : ℤ → ℂ) (h : ℝ → ℂ)‖ₑ
          ≤ eLpNorm (F : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
      intro h hh
      have hdec : ∀ z : ℂ,
          Work.Analysis.Interpolation.bilinearFamily (kmtPair s) (F : ℤ → ℂ) (h : ℝ → ℂ)
              ((p / 1 : ℝ) : ℂ) ((p / 2 : ℝ) : ℂ) ((p / 1 : ℝ) : ℂ) ((p / 2 : ℝ) : ℂ) z
            = ∑ c ∈ F.range, ∑ d ∈ h.range,
                (Work.Analysis.Interpolation.phasePow c
                    (Work.Analysis.Interpolation.expFamily ((p / 1 : ℝ) : ℂ) ((p / 2 : ℝ) : ℂ) z)
                  * Work.Analysis.Interpolation.phasePow d
                      (Work.Analysis.Interpolation.expFamily ((p / 1 : ℝ) : ℂ)
                        ((p / 2 : ℝ) : ℂ) z))
                * (kmtPair s (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
                    (Set.indicator (h ⁻¹' {d}) (fun _ => (1 : ℂ)))) := by
        intro z
        rw [Work.Analysis.Interpolation.bilinearFamily_apply]
        exact kmtPair_decomposition s F h (p / 1) (p / 2) (p / 1) (p / 2) z
      have hB : BddAbove ((norm ∘ Work.Analysis.Interpolation.bilinearFamily (kmtPair s) (F : ℤ → ℂ)
            (h : ℝ → ℂ) ((p / 1 : ℝ) : ℂ) ((p / 2 : ℝ) : ℂ) ((p / 1 : ℝ) : ℂ)
            ((p / 2 : ℝ) : ℂ)) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
        Work.Analysis.Interpolation.bddAbove_bilinear_family (kmtPair s) F h (p / 1) (p / 2) (p / 1)
          (p / 2) hdec
      have hmain := Work.Analysis.Interpolation.stein_bilinear_of_decomposition
        (μ := Measure.count) (ν := kmtNu) (kmtPair s) F h
        (p₀ := 1) (p₁ := 2) (q₀ := 1) (q₁ := 2) (p := p) (q := p) (θ := θ)
        one_pos (by norm_num) one_pos (by norm_num) hp_pos hp_pos hθ_pos hθ_lt hpθ hpθ
        (M₀ := 1) (M₁ := 1) h0 h1 hdec hB
      simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hmain
      exact hmain.trans (mul_le_of_le_one_right zero_le hh)
    -- duality: the `L^{p'}` seminorm of `f̂` against the simple test functions
    have hae : AEMeasurable (fun θ : ℝ => kmtFhat f θ) kmtNu := by
      rw [show (fun θ : ℝ => kmtFhat f θ) = fun θ : ℝ => kmtSum s f θ from
        funext fun θ => kmtFhat_eq_kmtSum hfsupp θ]
      exact aemeasurable_kmtSum s f
    have heq : ∀ h : SimpleFunc ℝ ℂ,
        ‖∫ y, kmtFhat f y * (h : ℝ → ℂ) y ∂kmtNu‖ₑ
          = ‖kmtPair s (F : ℤ → ℂ) (h : ℝ → ℂ)‖ₑ := by
      intro h
      rw [kmtPair_of_aemeasurable h.aemeasurable]
      have : (fun y : ℝ => kmtFhat f y * (h : ℝ → ℂ) y)
          = fun y : ℝ => kmtSum s (F : ℤ → ℂ) y * (h : ℝ → ℂ) y := by
        funext y
        rw [kmtFhat_eq_kmtSum hfsupp y, hF]
      rw [this]
    rw [Work.Analysis.Interpolation.eLpNorm_eq_iSup_simpleFunc_integral (ν := kmtNu) (q := p / (p - 1)) hq hae]
    refine iSup_le fun h => iSup_le fun hh => ?_
    rw [heq h]
    have hh' : eLpNorm (h : ℝ → ℂ) (ENNReal.ofReal p) kmtNu ≤ 1 := by
      rw [hconj] at hh
      exact hh
    have hfin := hstein h hh'
    simp only [hF] at hfin ⊢
    exact hfin
  · -- the endpoint `p = 2`: Plancherel
    subst hp2eq
    rw [eLpNorm_congr_ae (Filter.Eventually.of_forall fun θ => kmtFhat_eq_kmtSum hfsupp θ)]
    have h2a : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = 2 := by norm_num
    have h2b : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
    rw [h2a, h2b]
    exact kmtSum_eLpNorm_two_le s f

end

end Work.A3
