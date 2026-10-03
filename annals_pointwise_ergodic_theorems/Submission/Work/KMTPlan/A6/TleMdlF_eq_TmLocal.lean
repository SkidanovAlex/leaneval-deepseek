/-
# The model-side functional calculus `Tle ρ l (φ_{N,t}) (mdlF ρ u l f) = Tm ρ l (φ_{N,t}) f`

This is a *local* re-proof of `Work.KMTPlan.A6.Tle_mdlF_eq_Tm`
(`Submission/Work/KMTPlan/A6/Tle_mdlF_eq_Tm.lean`).  The original module is correct but its *import
closure* is currently broken by a colleague's file (`Submission/Work/KMTAreas/A7Hi/FiberVarSampling.lean`,
which fails to compile), so nothing can import it.  The two ingredients of the proof are both
available and build:

* `Work.KMTPlan.A6.Tle_mdlF_eq_iwConv` (module builds): the non-aliasing functional calculus
  `Tle ρ l (φ) (mdlF ρ u l f) = iwConv (diffFreqs ρ l) (periodize φ · periodize (etaCut kmtEta (-u))) f`
  under `NonAliasing (-(u:ℤ)) (iwArithFreqs ρ l)` and `SupportedInArc (-(u:ℤ)) (periodize φ)`;
* `Work.KMTPlan.A6.Phi_eq_one_of_small` (`projVanishingG.lean`): the cutoff
  `periodize (etaCut kmtEta k)` is identically `1` on the arc `|θ| ≤ 2^k/2`.

The conclusion identifies the composite with the *exact-height* multiplier `Tm ρ l (φ_{N,t})` applied
to the unprojected `f`, which is what turns the A6 packet family `n ↦ Tle ρ l₁ (φ_{⌊a n⌋,k₁,j₁,t}) (mdlF ρ u l₁ f)`
into the A7 `Hcl` family.  It needs the narrowness of the bump:

  `SupportedInArc (-(u:ℤ) - 1) (periodize (varphiNt N k t))`   (i.e. bump width `≲ 2^{-u-1}`),

which in the A6 core follows from `N > splitCut ρ L = 2^{2^{uScale ρ L}}`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Tle_mdlF_eq_iwConv

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators ENNReal NNReal
open Work.Analysis.IonescuWainger
open Work.Analysis.EndVar
open Work.Analysis.IWMultiplier
open Work.KMTAreas.A7
open Work.KMTContract

noncomputable section

/-- Monotonicity of `SupportedInArc` in the scale. -/
lemma supportedInArc_mono_local {k k' : ℤ} (h : k ≤ k') {Φ : Circle → ℂ}
    (hΦ : SupportedInArc k Φ) : SupportedInArc k' Φ :=
  fun ξ hξ => let ⟨θ, hθ, hθ'⟩ := hΦ ξ hξ; ⟨θ, realArc_mono h hθ, hθ'⟩

/-- **The model-side functional calculus in its final form** (local re-proof).  If the support of
the modulated bump `periodize (varphiNt N k t)` sits inside the plateau `ℝ_{≤-u-1}` of
`periodize (etaCut kmtEta (-u))` and the arithmetic frequencies of height `≤ l` are non-aliasing at
scale `-u`, then `Tle ρ l (φ_{N,t}) (mdlF ρ u l f) = Tm ρ l (φ_{N,t}) f`. -/
theorem Tle_mdlF_eq_Tm_local (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (u l N k : ℕ) (hu : 1 ≤ u)
    (t : ℝ) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count)
    (hnA : NonAliasing (-(u : ℤ)) (iwArithFreqs ρ l))
    (hΦ : SupportedInArc (-(u : ℤ) - 1) (periodize (varphiNt N k t))) :
    Tle ρ l (varphiNt N k t) (mdlF ρ u l f) = Tm ρ l (varphiNt N k t) f := by
  have hle : -(u : ℤ) - 1 ≤ -(u : ℤ) := by omega
  have hC1 := Tle_mdlF_eq_iwConv ρ hρ hρ1 u l N k t hf hnA (supportedInArc_mono_local hle hΦ)
  have hfun : (fun ξ : Circle => periodize (varphiNt N k t) ξ
        * periodize (etaCut Work.KMTContract.kmtEta (-(u : ℤ))) ξ)
      = periodize (varphiNt N k t) := by
    funext ξ
    by_cases hξ : periodize (varphiNt N k t) ξ = 0
    · rw [hξ, zero_mul]
    · obtain ⟨θ, hθ, rfl⟩ := hΦ ξ hξ
      have hk : (2 : ℝ) ^ (-(u : ℤ)) ≤ 1 / 2 := by
        rw [zpow_neg, zpow_natCast]
        have h2u : (2 : ℝ) ≤ (2 : ℝ) ^ u := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hu
        simpa [one_div] using
          one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) h2u
      have hθ' : |θ| ≤ (2 : ℝ) ^ (-(u : ℤ)) / 2 := by
        have h2 : |θ| ≤ (2 : ℝ) ^ (-(u : ℤ) - 1) := by
          have hθ'' := hθ
          rw [realArc, Set.mem_Icc] at hθ''
          rw [abs_le]
          exact ⟨by linarith [hθ''.1], by linarith [hθ''.2]⟩
        have he : (2 : ℝ) ^ (-(u : ℤ) - 1) = (2 : ℝ) ^ (-(u : ℤ)) / 2 := by
          rw [zpow_sub₀ (show (2 : ℝ) ≠ 0 by norm_num), zpow_one]
        rwa [he] at h2
      rw [Phi_eq_one_of_small hk hθ', mul_one]
  rw [hC1, hfun]
  rfl

end

end Work.KMTPlan.A6
