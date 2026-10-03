/-
# The height-`0` composite identity via the *singleton* gate (no non-aliasing)

At height `l = 0` the Ionescu--Wainger frequency set is `iwArithFreqs ρ 0 = {0}`, so the functional
calculus `Tle ρ 0 (φ) (mdlF ρ u 0 f) = Tle ρ 0 (φ) f` is a *multiplier* identity at a single
frequency: the composite symbol is `periodize φ · periodize (etaCut kmtEta (-u))`, and the narrowness
of the bump (its support lies in `realArc (-u-1)`, the plateau of the cutoff) makes the second
factor `1` there.

This file proves it through `Work.KMTAreas.A7Hi.iwConv_comp` with the **trivial** gate
`Φ₁ · Φ₂ = Φ₁`, i.e. *without* the non-aliasing hypothesis that
`Work.KMTPlan.A6.Tle_mdlF_eq_iwConv` (and hence `Tle_mdlF_eq_Tm_local`) carries.  This matters:
`uScale ρ L = ⌊2^{2ρL}⌋ = 1` whenever `2ρL < 1` (the generic regime of the A6 core for small `ρ`),
and `NonAliasing (-1) (iwArithFreqs ρ l)` is **false** whenever `0 ∈ iwArithFreqs ρ l`, because
`±1/2` are two distinct representatives of the same circle point in `realArc (-1)`.  So the
non-aliasing-based calculus is inapplicable exactly where it is needed, while the singleton gate
works unconditionally.

Ingredient list (all in the tree): `iwSymbolSet_singleton_zero` (`iwSymbolSet {0} Φ = Φ`),
`integrable_iwSymbolSet_periodize`, `summable_fourierCoeff_periodize` (with
`contDiff_varphiNt`, `hasCompactSupport_varphiNt`), `varphiNtSch_apply`, `etaCutSchwartz_coe`,
`Phi_eq_one_of_small` and `exists_norm_bound_of_memLp`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.TleMdlF_eq_TmLocal
import Submission.Work.KMTAreas.A7Hi.fiberOp_Tex_eq_twisted
import Submission.Work.KMTAreas.A7Hi.lacunaryMaxPieceRep

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators ENNReal NNReal
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.KMTAreas.A7 Work.KMTAreas.A7Hi
open Work.KMTContract

noncomputable section

/-- **The height-`0` composite identity, unconditionally** (singleton gate, no non-aliasing):
`Tle ρ 0 (varphiNt N 0 t) (mdlF ρ u 0 f) = Tle ρ 0 (varphiNt N 0 t) f`, for `f ∈ ℓ²` and a bump
supported in `realArc (-u-1)`. -/
theorem Tle_mdlF_eq_Tle_atZero_singleton (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (u N : ℕ)
    (hu : 1 ≤ u) (t : ℝ) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count)
    (hΦ : SupportedInArc (-(u : ℤ) - 1) (periodize (varphiNt N 0 t))) :
    Tle ρ 0 (varphiNt N 0 t) (mdlF ρ u 0 f) = Tle ρ 0 (varphiNt N 0 t) f := by
  set Φ₁ : Circle → ℂ := periodize (varphiNt N 0 t) with hΦ₁def
  set Φ₂ : Circle → ℂ := periodize (etaCut Work.KMTContract.kmtEta (-(u : ℤ))) with hΦ₂def
  -- ## the plateau: `Φ₁ · Φ₂ = Φ₁`
  have hplateau : ∀ ζ : Circle, Φ₁ ζ * Φ₂ ζ = Φ₁ ζ := by
    intro ξ
    by_cases hξ : Φ₁ ξ = 0
    · rw [hξ, zero_mul]
    · obtain ⟨θ, hθmem, rfl⟩ := hΦ ξ hξ
      have hk : (2 : ℝ) ^ (-(u : ℤ)) ≤ 1 / 2 := by
        rw [zpow_neg, zpow_natCast]
        have h2u : (2 : ℝ) ≤ (2 : ℝ) ^ u := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hu
        simpa [one_div] using
          one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) h2u
      have hθ' : |θ| ≤ (2 : ℝ) ^ (-(u : ℤ)) / 2 := by
        have h2 : |θ| ≤ (2 : ℝ) ^ (-(u : ℤ) - 1) := by
          have hθ'' := hθmem
          rw [realArc, Set.mem_Icc] at hθ''
          rw [abs_le]
          exact ⟨by linarith [hθ''.1], by linarith [hθ''.2]⟩
        have he : (2 : ℝ) ^ (-(u : ℤ) - 1) = (2 : ℝ) ^ (-(u : ℤ)) / 2 := by
          rw [zpow_sub₀ (show (2 : ℝ) ≠ 0 by norm_num), zpow_one]
        rwa [he] at h2
      show Φ₁ (θ : Circle) * Φ₂ (θ : Circle) = Φ₁ (θ : Circle)
      rw [hΦ₂def, Phi_eq_one_of_small hk hθ', mul_one]
  -- ## integrability of the two symbols
  have hcoe₁ : ((Work.KMTAreas.A7.varphiNtSch N 0 t : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = varphiNt N 0 t := funext fun ξ => Work.KMTAreas.A7.varphiNtSch_apply N 0 t ξ
  have hint1 : Integrable (iwSymbolSet ({0} : Finset Circle) Φ₁) circleMeasure := by
    have h := Work.KMTAreas.integrable_iwSymbolSet_periodize ({0} : Finset Circle)
      (Work.KMTAreas.A7.varphiNtSch N 0 t)
    rwa [hcoe₁] at h
  have hint2 : Integrable (iwSymbolSet ({0} : Finset Circle) Φ₂) circleMeasure := by
    have h := Work.KMTAreas.integrable_iwSymbolSet_periodize ({0} : Finset Circle)
      (Work.KMTAreas.A7.etaCutSchwartz (-(u : ℤ)))
    rwa [Work.KMTAreas.A7.etaCutSchwartz_coe] at h
  -- ## summability of the Fourier coefficients of the two symbols
  have hsym1 : iwSymbolSet ({0} : Finset Circle) Φ₁ = periodize (varphiNt N 0 t) := by
    rw [iwSymbolSet_singleton_zero]
  have hsym2 : iwSymbolSet ({0} : Finset Circle) Φ₂
      = periodize (etaCut Work.KMTContract.kmtEta (-(u : ℤ))) := by
    rw [iwSymbolSet_singleton_zero]
  have hs1 : Summable (fun j : ℤ => fourierCoeff (iwSymbolSet ({0} : Finset Circle) Φ₁) j) := by
    rw [hsym1]
    exact Work.KMTAreas.A7.summable_fourierCoeff_periodize
      (contDiff_varphiNt N 0 t) (hasCompactSupport_varphiNt N 0 t)
  have hs2 : Summable (fun j : ℤ => fourierCoeff (iwSymbolSet ({0} : Finset Circle) Φ₂) j) := by
    rw [hsym2]
    exact Work.KMTAreas.A7.summable_fourierCoeff_periodize
      ((Work.KMTAreas.A7.contDiff_etaCut (-(u : ℤ))).of_le (WithTop.coe_le_coe.mpr le_top))
      (Work.KMTAreas.A7.hasCompactSupport_etaCut (-(u : ℤ)))
  -- ## the singleton composition
  obtain ⟨B, _hBnn, hB⟩ := Work.KMTAreas.A7Hi.exists_norm_bound_of_memLp
    (p := 2) (by norm_num) (by norm_num) hf
  have hcomp := Work.KMTAreas.A7Hi.iwConv_comp ({0} : Finset Circle) Φ₁ Φ₂ Φ₁
    hint1 hint2 hint1 hs1 hs2
    (fun ζ => by simpa only [iwSymbolSet_singleton_zero] using hplateau ζ) f hB
  -- ## identification of the two sides
  have hmdlF : mdlF ρ u 0 f = iwConv ({0} : Finset Circle) Φ₂ f := by
    show Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) 0 (-(u : ℤ)) f = _
    rw [Work.Analysis.EndVar.piExact, if_pos rfl]
    show Work.KMTContract.kmtProj ρ 0 (-(u : ℤ)) f = _
    show iwConv (iwArithFreqs ρ 0) Φ₂ f = iwConv ({0} : Finset Circle) Φ₂ f
    rw [Work.KMTAreas.A7.iwArithFreqs_zero]
  have hTle : Tle ρ 0 (varphiNt N 0 t) = iwConv ({0} : Finset Circle) Φ₁ := by
    funext g n
    show iwConv (iwArithFreqs ρ 0) Φ₁ g n = iwConv ({0} : Finset Circle) Φ₁ g n
    rw [Work.KMTAreas.A7.iwArithFreqs_zero]
  rw [hmdlF, hTle]
  exact hcomp

end

end Work.KMTPlan.A6
