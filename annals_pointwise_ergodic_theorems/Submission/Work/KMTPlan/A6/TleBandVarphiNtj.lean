/-
# The band-limitation of the modified `f`-side model projection `T^{≤l}_{φ_{N,t,j}}`

This module supplies the band half of the model-input statement `MdlSliceFband` for the *modified*
bump `varphiNtj N k j t` (the bump of the Krause--Mirek--Tao integration-by-parts identity,
`(2^{-k}Nξ)^j φ_{N,t}(ξ)`) at the *non-singular* scales `j ∈ {-1,0,1}`, `k = 0 → j ≠ -1`:

  `Tle ρ l (varphiNtj N k j t) F = iwConv (iwArithFreqs ρ l) (periodize (varphiNtj N k j t)) F`

is square summable and its Fourier transform is supported in the union of the major arcs
`α + arcSet 0 (2^{k - Log N})`, `α ∈ (ℚ/ℤ)_{≤l}`.

## The two inputs

* `Work.KMTPlan.A6.varphiNtjPeriodize_aux` (`VarphiNtjPeriodizeAux.lean`) gives, simultaneously,
  the `L^∞` bound of the periodisation (hence `MemLp _ ⊤`) and the *arc*: the periodisation
  vanishes off the `δ`-arc around `0`, `δ = 2^{k - Log N}`.  Note that this is a statement about
  the *support* of `varphiNtj` alone -- the unimodular modulation `e(Nt·)` is irrelevant to it --
  and the crude bound `‖varphiNtj‖ ≤ 8` never has to be improved.
* `exists_hasFreqSupport_Tle_of_arc` below is the general band-limitation of `Tle` for any profile
  `φ` whose periodisation vanishes off a `δ`-arc: `Tle` is the `L²`-multiplier with symbol
  `iwSymbolSet A (periodize φ)`, so its Fourier transform is the product of that symbol with `𝓕F`
  (`fourierZ_multiplierOf`) and the symbol vanishes off the union of the `δ`-arcs because
  `periodize φ` does.  No boundedness of `F` and no real-valuedness of the profile is needed: the
  identification `iwConvEqIwOpSetMemlp` of the convolution form with the multiplier form holds on
  all of `ℓ²(ℤ)`.

This is the `Tle` analogue of `Work.KMTAreas.A7.hasFreqSupport_Tex_of_memℓp` (the exact-height
projection `Tex`), and it is the `MemLp`-carrying form of `Work.KMTPlan.A6.TleBand`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.VarphiNtjPeriodizeAux
import Submission.Work.A7HiRep.incFamBandLimitedL2
import Submission.Work.KMTPlan.A6.memLp_kmtProj
import Submission.Work.Analysis.RubioDeFrancia.tsum_inv_one_add_abs_sq_le
import Submission.Work.KMTAreas.A4.fourierZCoeFnEqTsum

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- If `ξ - α` lies in the arc `arcSet 0 δ` around `0`, then `ξ` lies in the translated arc
`arcSet α δ`. -/
private lemma mem_arcSet_of_sub_mem {α ξ : Circ} {δ : ℝ}
    (h : ξ - α ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ) :
    ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet α δ := by
  obtain ⟨θ, hθ, hξ⟩ := h
  refine ⟨θ, hθ, ?_⟩
  have h2 : ξ = α + (0 + (θ : Circ)) := sub_eq_iff_eq_add'.mp hξ
  simpa using h2

/-- **Band-limitation of the Ionescu--Wainger projection `Tle`.**  If the periodisation of `φ`
vanishes off the `δ`-arc around `0`, then for every `F ∈ ℓ²(ℤ)` the projection
`Tle ρ l φ F = iwConv (iwArithFreqs ρ l) (periodize φ) F` is square summable and band-limited to
the union of the `δ`-arcs around the arithmetic frequencies `(ℚ/ℤ)_{≤l}`.

The proof identifies `Tle` with the scalar `L²`-multiplier whose symbol is
`iwSymbolSet (iwArithFreqs ρ l) (periodize φ)` (`iwConvEqIwOpSetMemlp`, valid on all of `ℓ²(ℤ)`),
whose Fourier transform is the product of the symbol with `𝓕F` (`fourierZ_multiplierOf`); the
symbol vanishes off the union because `periodize φ` vanishes off the `δ`-arc around `0`. -/
private theorem exists_hasFreqSupport_Tle_of_arc (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (δ : ℝ)
    (hper : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (harc : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize φ θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (F : ℤ → ℂ) (hF : Memℓp F 2) :
    ∃ hw : Memℓp (Work.KMTAreas.A7.Tle ρ l φ F) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (Work.KMTAreas.A7.Tle ρ l φ F) hw
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          Work.BourgainPlan.IonescuWainger.arcSet α δ) := by
  classical
  set A : Finset Circ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  set σ : Circ → ℂ := Work.Analysis.IonescuWainger.iwSymbolSet A
    (Work.Analysis.IonescuWainger.periodize φ) with hσdef
  have hsym : MeasureTheory.MemLp σ ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet A hper
  set Fl : Work.Analysis.IonescuWainger.L2Z := ⟨F, hF⟩ with hFldef
  set Fl' : Work.Analysis.IonescuWainger.L2Z :=
    Work.Analysis.IonescuWainger.iwOpSet A (Work.Analysis.IonescuWainger.periodize φ) hsym Fl
    with hFl'def
  have hweq : Work.KMTAreas.A7.Tle ρ l φ F = ⇑Fl' := by
    rw [← Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hsym Fl]
    rfl
  have hw : Memℓp (Work.KMTAreas.A7.Tle ρ l φ F) 2 := hweq ▸ Fl'.2
  refine ⟨hw, ?_⟩
  -- the Fourier transform of the multiplier is the product with its symbol
  have hft : Work.Analysis.IonescuWainger.fourierZ Fl'
      = hsym.toLp σ • Work.BourgainPlan.IonescuWainger.ftLp F hF := by
    rw [hFl'def]
    exact Work.Analysis.IonescuWainger.fourierZ_multiplierOf σ hsym Fl
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport]
  rw [show Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7.Tle ρ l φ F) hw
      = Work.BourgainPlan.IonescuWainger.ftLp (⇑Fl') Fl'.2 from
    Work.BourgainPlan.IonescuWainger.ftLp_congr hweq hw Fl'.2]
  filter_upwards [MeasureTheory.Lp.ext_iff.mp hft,
    MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (hsym.toLp σ) (Work.BourgainPlan.IonescuWainger.ftLp F hF),
    MeasureTheory.MemLp.coeFn_toLp hsym] with ξ hftξ hsmul hσeq hξ
  change (Work.Analysis.IonescuWainger.fourierZ Fl' : Circ → ℂ) ξ = 0
  rw [hftξ, hsmul]
  change ⇑(hsym.toLp σ) ξ • (Work.BourgainPlan.IonescuWainger.ftLp F hF : Circ → ℂ) ξ = 0
  have hzero : σ ξ = 0 := by
    rw [hσdef, Work.Analysis.IonescuWainger.iwSymbolSet_apply]
    refine Finset.sum_eq_zero fun α hα => ?_
    by_contra hne
    have hsub : ξ - α ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ := harc _ hne
    exact hξ (by
      simp only [Set.mem_iUnion]
      exact ⟨α, hα, mem_arcSet_of_sub_mem hsub⟩)
  rw [hσeq, hzero, zero_smul]

/-- **The band half of `MdlSliceFband` for the modified `f`-side bump.**  For the modified bump
`varphiNtj N k j t` (`j ∈ {-1,0,1}`, the singular case `k = 0, j = -1` excluded) and any `ℓ²`
input `F`, the projection `Tle ρ l (varphiNtj N k j t) F` is square summable and band-limited to
the union of the major arcs of the arithmetic frequencies `(ℚ/ℤ)_{≤l}` at radius
`2^{k - Log N}`. -/
theorem TleBandVarphiNtj (ρ : ℝ) (l N k : ℕ) (j : ℤ) (t : ℝ) (F : ℤ → ℂ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k = 0 → j ≠ -1) (hN : 1 ≤ N)
    (hF : Memℓp F 2) :
    ∃ h : Memℓp (Work.KMTAreas.A7.Tle ρ l (Work.KMTPlan.A6.varphiNtj N k j t) F) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTAreas.A7.Tle ρ l (Work.KMTPlan.A6.varphiNtj N k j t) F) h
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          Work.BourgainPlan.IonescuWainger.arcSet α
            ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) := by
  obtain ⟨_M, _hM0, _hbnd, hper, harc⟩ :=
    Work.KMTPlan.A6.varphiNtjPeriodize_aux N k j t hj hk hN
  exact exists_hasFreqSupport_Tle_of_arc ρ l (Work.KMTPlan.A6.varphiNtj N k j t)
    ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) hper harc F hF

end Work.KMTPlan.A6
