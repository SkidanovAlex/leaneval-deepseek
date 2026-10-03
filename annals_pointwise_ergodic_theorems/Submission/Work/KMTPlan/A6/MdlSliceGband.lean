/-
# Band-limitation of the `g`-side packet family of the frozen slice

`mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n` (defined in `MdlSliceCoreGainBig`) is, on the core
scales, the Ionescu--Wainger multiplier `T^{≤ l₂}_{φ̃_{N,t,j₂}}` applied to the exact-height shell
`mdlG ρ P (uScale ρ L) l₂ g` of `g`, `N = ⌊a n⌋`.

This module proves that this family is square summable and band-limited to the union of the
major arcs of radius `2^{d(k₂ - Log N)}` around the arithmetic frequencies
`α ∈ (ℚ/ℤ)_{≤ l₂}`, `d = P.natDegree` — the band statement `(S1)` of the adelic-packet
programme for the `g`-side packet family (the `f`-side twin is `MdlSliceFband`).

The route is the `ℓ²`-dictionary of `Submission/Work/BourgainPlan/IonescuWainger/FourierL2Defs`:

* `Tle_hasFreqSupport_of_memℓp` (proved here, the generic brick): for any window `φ` which is
  integrable with summable Fourier coefficients and whose periodisation is supported in the `δ`-arc
  around `0`, and every `f ∈ ℓ²(ℤ)`, the multiplier `Tle ρ l φ f` is square summable with Fourier
  support in `⋃_{α ∈ (ℚ/ℤ)_{≤l}} arcSet α δ`.  This is the `Tle` version of the proved
  `Work.KMTAreas.A7.hasFreqSupport_Tex_of_memℓp` (which is stated for the *exact-height* frequency
  set `iwArithFreqsNew`); the proof is the same symbol computation
  `𝓕(Tle ρ l φ f) = (Σ_{α∈A} periodize φ(·-α)) · 𝓕f` via `iwConvEqIwOpSetMemlp` and
  `fourierZ_multiplierOf`, followed by `iwSymbolSet_eq_zero_of_forall_not_mem_arcSet`.
* the window is `φ = varphitildeNtj P N k₂ j₂ t`: smooth (`contDiff_varphitildeNtj_all`) and
  compactly supported (`hasCompactSupport_varphitildeNtj_all`) — so integrable with summable
  Fourier coefficients (`integrable_varphitildeNtj`, `summable_cw_varphitildeNtj`) — and supported
  in `[-2^{d(k₂-Log N)}, 2^{d(k₂-Log N)}]` (`varphitildeNtj_abs_le`, from
  `Work.KMTAreas.A7.varphitildeNt_support_all`), whence `periodize` is supported in the
  corresponding arc (`fiberOpTex_periodize_ne_zero_mem_arcSet`);
* the input `mdlG ρ P U l₂ g = piExact (kmtPj ρ) l₂ (-dU) g` is square summable whenever `g` is
  (`memℓp_mdlG`, from the proved `Work.A7HiRep.exists_hasFreqSupport_kmtProj`);
* off the core scales the slice is `0` (`zero_hasFreqSupport`).
-/
import Mathlib
import Submission.Work.A6Big.Defs
import Submission.Work.KMTPlan.A6.HHAux
import Submission.Work.A7HiRep.incFamBandLimitedL2
import Submission.Work.KMTPlan.A6.MdlPktG_fareyPart
import Submission.Work.KMTAreas.A7.SmallKernMassBasics
import Submission.Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd
import Submission.Work.Analysis.RubioDeFrancia.tsum_inv_one_add_abs_sq_le
-- (2026-10-03) The import of `Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig` was replaced by
-- `Submission.Work.A6Big.Defs`: the definitions `mdlSliceF`, `mdlSliceG` (and
-- `MdlSliceCoreGainMemLp`, `MdlSliceCoreGain_of_memLp`) moved to the latter, while the former now
-- re-exports the copied §8 chain of `Submission/Work/A6Big/`, whose declarations carry the same
-- names as this file's own — pulling it in made this module (and the whole A6 lane downstream of
-- it) unbuildable with `… has already been declared`.  Nothing here uses `MdlSliceCoreGain*`.

namespace Work.KMTPlan.A6

/-! ## The generic band-limitation lemma for `Tle` -/

open MeasureTheory in
/-- **The Fourier transform of the Ionescu--Wainger multiplier `Tle ρ l φ` lies in the union of the
`δ`-arcs around the arithmetic frequencies of height `≤ 2^l`.**

If `φ : ℝ → ℂ` is integrable with summable Fourier coefficients `cw φ` and its periodisation
vanishes off the `δ`-arc around `0`, then for every `f ∈ ℓ²(ℤ)` the sequence `Tle ρ l φ f` is in
`ℓ²(ℤ)` and its Fourier transform vanishes off `⋃_{α ∈ (ℚ/ℤ)_{≤l}} (α + [-δ,δ])`.

This is the `Tle` analogue of the proved `Work.KMTAreas.A7.hasFreqSupport_Tex_of_memℓp` (the
exact-height version); the symbol of the multiplier is
`ξ ↦ Σ_{α ∈ (ℚ/ℤ)_{≤l}} periodize φ (ξ - α)`, which vanishes off the union of the arcs because
every non-zero term exhibits a point of the support of `periodize φ`. -/
theorem Tle_hasFreqSupport_of_memℓp (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (δ : ℝ)
    (hm : MeasureTheory.Integrable φ)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖))
    (hmsupp : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize φ θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∃ hw : Memℓp (Work.KMTAreas.A7.Tle ρ l φ f) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (Work.KMTAreas.A7.Tle ρ l φ f) hw
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          Work.BourgainPlan.IonescuWainger.arcSet α δ) := by
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  set σ : Work.Analysis.IonescuWainger.Circle → ℂ :=
    Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize φ) with hσdef
  have hΨ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7Hi.periodizeMemLpTop hm hmsum
  have hsym : MeasureTheory.MemLp σ ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet A hΨ
  set F : Work.Analysis.IonescuWainger.L2Z := ⟨f, hf⟩ with hF
  set F' : Work.Analysis.IonescuWainger.L2Z :=
    Work.Analysis.IonescuWainger.iwOpSet A (Work.Analysis.IonescuWainger.periodize φ) hsym F
    with hF'
  have hweq : Work.KMTAreas.A7.Tle ρ l φ f = ⇑F' := by
    rw [← Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hsym F]
    rfl
  have hw : Memℓp (Work.KMTAreas.A7.Tle ρ l φ f) 2 := hweq ▸ F'.2
  refine ⟨hw, ?_⟩
  -- the Fourier transform of the multiplier is the product with the symbol
  have hft : Work.Analysis.IonescuWainger.fourierZ F'
      = hsym.toLp σ • Work.BourgainPlan.IonescuWainger.ftLp f hf := by
    rw [hF']
    exact Work.Analysis.IonescuWainger.fourierZ_multiplierOf σ hsym F
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport]
  rw [show Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7.Tle ρ l φ f) hw
      = Work.BourgainPlan.IonescuWainger.ftLp (⇑F') F'.2 from
    Work.BourgainPlan.IonescuWainger.ftLp_congr hweq hw F'.2]
  filter_upwards [MeasureTheory.Lp.ext_iff.mp hft,
    MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (hsym.toLp σ) (Work.BourgainPlan.IonescuWainger.ftLp f hf),
    MeasureTheory.MemLp.coeFn_toLp hsym] with ξ hftξ hsmul hσeq hξ
  change (Work.Analysis.IonescuWainger.fourierZ F' :
      Work.Analysis.IonescuWainger.Circle → ℂ) ξ = 0
  rw [hftξ, hsmul]
  change ⇑(hsym.toLp σ) ξ •
      (Work.BourgainPlan.IonescuWainger.ftLp f hf :
        Work.Analysis.IonescuWainger.Circle → ℂ) ξ = 0
  have hzero : σ ξ = 0 := by
    refine Work.KMTAreas.A7.iwSymbolSet_eq_zero_of_forall_not_mem_arcSet A φ δ hmsupp ξ ?_
    intro α hα hmem
    exact hξ (by simp only [Set.mem_iUnion]; exact ⟨α, hα, hmem⟩)
  rw [hσeq, hzero, zero_smul]

/-! ## The window `φ̃_{N,t,j}`: support, integrability and Fourier decay -/

open MeasureTheory in
/-- **The support bound of the modified `g`-side bump**: a nonzero value of
`φ̃_{N,t,j}(ξ) = (2^{-dk}N^dξ)^j φ̃_{N,t}(ξ)` forces `|ξ| ≤ 2^{d(k - Log N)}`.  The weight
`(2^{-dk}N^dξ)^j` is nowhere zero away from the origin, so the support is that of `φ̃_{N,t}`
(`Work.KMTAreas.A7.varphitildeNt_support_all`). -/
theorem varphitildeNtj_abs_le (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ) :
    ∀ ξ : ℝ, varphitildeNtj P N k j t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  intro ξ hξ
  have hNt : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ ≠ 0 :=
    Work.KMTPlan.A6.varphitildeNt_ne_zero_of_varphitildeNtj_ne_zero P N k j t hξ
  exact Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k t ξ hNt

open MeasureTheory in
/-- **Integrability of the modified `g`-side bump** in the non-singular cases `k ≠ 0` or `j ≥ 0`:
it is smooth with compact support. -/
theorem integrable_varphitildeNtj (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (hk : k ≠ 0 ∨ 0 ≤ j) : MeasureTheory.Integrable (varphitildeNtj P N k j t) :=
  (Work.KMTPlan.A6.contDiff_varphitildeNtj_all P N k j t hk).continuous
      |>.integrable_of_hasCompactSupport
        (Work.KMTPlan.A6.hasCompactSupport_varphitildeNtj_all P N k j t)

open MeasureTheory in
/-- **Summability of the Fourier coefficients of the modified `g`-side bump.**  The `C²` decay of
the Fourier transform of a compactly supported `C²` function gives
`Σ'_j ‖cw φ j‖ < ∞` (`Work.KMTAreas.A7.summable_cw_of_contDiff_hasCompactSupport`). -/
theorem summable_cw_varphitildeNtj (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (hk : k ≠ 0 ∨ 0 ≤ j) :
    Summable (fun i : ℤ => ‖Work.KMTAreas.A7.cw (varphitildeNtj P N k j t) i‖) :=
  Work.KMTAreas.A7.summable_cw_of_contDiff_hasCompactSupport
    ((Work.KMTPlan.A6.contDiff_varphitildeNtj_all P N k j t hk).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (Work.KMTPlan.A6.hasCompactSupport_varphitildeNtj_all P N k j t)

/-! ## The exact-height shell `mdlG` preserves `ℓ²` -/

open MeasureTheory in
/-- `mdlG ρ P U l g = piExact (kmtPj ρ) l (-(d·U)) g` is square summable whenever `g` is: the
`ℓ²`-boundedness of the Ionescu--Wainger projections
(`Work.A7HiRep.exists_hasFreqSupport_kmtProj`) applied to the two terms of the exact-height
difference. -/
theorem memℓp_mdlG (ρ : ℝ) (P : Polynomial ℤ) (U l : ℕ) {g : ℤ → ℂ} (hg : Memℓp g 2) :
    Memℓp (mdlG ρ P U l g) 2 := by
  set k : ℤ := -((P.natDegree : ℤ) * (U : ℤ)) with hk
  have hmem : ∀ (m : ℕ), Memℓp (Work.KMTContract.kmtProj ρ m k g) 2 :=
    fun m => (Work.A7HiRep.exists_hasFreqSupport_kmtProj ρ m k g hg).1
  have hpi : Memℓp (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k g) 2 := by
    rw [Work.Analysis.EndVar.piExact]
    split_ifs with h
    · exact hmem 0
    · exact (hmem l).sub (hmem (l - 1))
  simpa [mdlG, hk] using hpi

/-! ## The zero sequence is band-limited to every set -/

open MeasureTheory in
/-- The zero sequence is square summable and its Fourier transform vanishes, hence it is
band-limited to every set of frequencies. -/
theorem zero_hasFreqSupport (E : Set Work.BourgainPlan.IonescuWainger.Circle) :
    ∃ h : Memℓp (0 : ℤ → ℂ) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (0 : ℤ → ℂ) h E := by
  have h0 : Memℓp (0 : ℤ → ℂ) 2 := by rw [Memℓp]; simp
  refine ⟨h0, ?_⟩
  have hft : Work.BourgainPlan.IonescuWainger.ftLp (0 : ℤ → ℂ) h0 = 0 := by
    rw [Work.BourgainPlan.IonescuWainger.ftLp]
    have hz : (⟨(0 : ℤ → ℂ), h0⟩ : lp (fun _ : ℤ => ℂ) 2) = 0 := by ext m; rfl
    rw [hz, map_zero]
  rw [Work.BourgainPlan.IonescuWainger.HasFreqSupport]
  filter_upwards with θ _
  rw [hft]
  simp

/-! ## The band of the `g`-side packet family -/

theorem MdlSliceGband (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (n : ℕ)
    (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (hmain : (P.natDegree * k₂ : ℕ) + 2 * (P.natDegree * (Work.KMTAreas.A7.uScale ρ
        (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) : ℕ)
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)
    (hg : Memℓp g 2) :
    ∃ h : Memℓp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) h
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          Work.BourgainPlan.IonescuWainger.arcSet α
            ((2 : ℝ) ^ ((P.natDegree : ℝ)
              * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℝ))))) := by
  classical
  -- the excluded case `(k₂, j₂) = (0, -1)`: the weight `(N^dξ)^{-1}` is singular at the origin
  have hmod : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
    have hj : j₂ = -1 ∨ j₂ = 0 ∨ j₂ = 1 := by simpa using hj₂
    rcases hj with h | h | h
    · by_cases hk : k₂ = 0
      · exact absurd h (hk₂ hk)
      · exact Or.inl hk
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [mdlSliceG, if_pos hc]
    obtain ⟨hw, hsupp⟩ := Tle_hasFreqSupport_of_memℓp ρ l₂
      (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
      ((2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℝ))))
      (integrable_varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t hmod)
      (summable_cw_varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t hmod)
      (fun θ hθ => Work.KMTAreas.A7.fiberOpTex_periodize_ne_zero_mem_arcSet
        (varphitildeNtj_abs_le P (Nat.floor (a n)) k₂ j₂ t) hθ)
      (mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)
      (memℓp_mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ hg)
    exact ⟨hw, hsupp⟩
  · rw [mdlSliceG, if_neg hc]
    exact zero_hasFreqSupport _

end Work.KMTPlan.A6
