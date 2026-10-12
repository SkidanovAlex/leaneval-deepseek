import ChallengeDeps
import Submission.Work.UBBInputs.Normalisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs.Sliding` — input (2): FS `eq:BSsliding2`

The delivered per-state sliding inequality (`Work.DLWire.DLSlide`, FS
`eq:BSsliding2`) is assembled here from the delivered pieces, in the
normalisation-correct form `DLSlideCov` (`Normalisation.lean` records why the
delivered form is not FS's statement):

    `SlidingSumData`  →  `SlidingRawNorm`  →  `DLSlideCov`  →  `AprioriNPlusCov`

* **`slidingRawNorm_of_data`** — the delivered
  `Work.SmallBoxTBWord.Sliding.sliding_sum_bound_of_tBLocalisation` applied to
  the residual bundle `SlidingSumData`.  Its fields:
  - the Bratteli–Solovej Thm 3.10 field
    `Work.SmallBoxTBWord.Sliding.tBLocalisation` (FS's own citation; the
    corpus's `SmallBoxTBWord/NOTES.md` §4 records, with machine-checked
    support, that this operator-level inequality cannot be obtained from the
    word-level identities — the `Q_B`-projection is free for the slot
    derivative and the plain box kinetic integrates *exactly* to `kinWord`,
    leaving no room for the gap `(b/2ℓ²)cnPlus`);
  - the per-box lower bound (`hbox`/`hsum`), whose intended input is the
    PROVED `Submission.BoseGases.smallbox_dl_energy_bound_at_count` summed over
    the sliding family — the bundle carries it in the integrated form because
    the sliding chapter's per-box density is the real `n(u)/|B(u)|` while the
    delivered DL bundle is indexed by the discrete count;
  - FS `lem:LocPotential` (`hpot`), the integrability bookkeeping, and the
    discarded-mass pair (`hlow`, `hmass`, discharged by the CLOSED
    `Work.SmallBoxSliding.compl_mass_le` + `chiSmallB_badband_integral_law`).
* **`dlSlideCov_of_slidingRawNorm`** — the `kinWord + qLHSword` form of
  `SlidingRawNorm` is `EnergyWord` at norm one, so it *is* `DLSlideNorm`; the
  scaling equivalence `dlSlideNorm_iff_dlSlideCov` then gives `DLSlideCov`.
* **`aprioriNPlusCov_of_dlSlideCov`** — the a-priori arithmetic: the covariant
  sliding inequality plus the low-state condition give the covariant `n₊`
  window `cnPlus/∫Φ² ≤ (2L²/b)·4πρ²(a v)L³(J+K_B³)·√(ρ(a v)³)` (the covariant
  mirror of `Work.UBB.Apriori.cnPlus_le_window_of_low`, whose arithmetic core
  is the CLOSED `Work.SmallBoxSliding.cnPlus_and_R_le`).
* **`spectralInput_of_cov`** — the repaired decomposition
  `AprioriNPlusCov + BogoliubovLowCov ⟹ SpectralInput`, i.e. the one-line
  composition of FS's a-priori chapter with FS §9–11.  (Contrast the delivered
  `Work.UBB.Assembly.spectralInput_of_pieces`, which composes the two
  normalisation-broken statements.)
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **`SlidingRawNorm` from the residual bundle** — the delivered sliding
assembly at the corpus per-box word (FS `eq:BSsliding2`/`eq:appsliding`). -/
theorem slidingRawNorm_of_data {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ}
    {d M : ℕ} (hdata : SlidingSumData v h b K_B R' J ε₀ d M) :
    SlidingRawNorm v h b K_B R' J ε₀ := by
  intro L hL N hN Φ hnorm hlow
  obtain ⟨ε, c, C, B, eBf, hC, hloc, hbox, hpot, hintt, hintq, _hintf, hintmass,
    hlowu, hmass, hsum⟩ := hdata L hL N hN Φ hnorm hlow
  have hmain := Work.SmallBoxTBWord.sliding_sum_bound_of_tBLocalisation (h := h) (M := M)
    (Φ := (Φ : X N → ℝ)) eBf (∫ u : ℝ³, eBf u) ε c hC _hintf hintmass rfl hbox hloc hpot
    hintt hintq hlowu hmass
  linarith [hmain, hsum]

/-- **The residual bundle from its two pieces**: the Bratteli–Solovej
citation `SlidingLocalisation` (the *other paper*'s input) plus the
corpus-side bundle `BoxSumBound`. -/
theorem slidingSumData_of {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ}
    {d M : ℕ} (hloc : SlidingLocalisation d b)
    (hrest : BoxSumBound v h b K_B R' J ε₀ d M) :
    SlidingSumData v h b K_B R' J ε₀ d M := by
  intro L hL N hN Φ hnorm hlow
  obtain ⟨ε, c, C, B, eBf, hC, hbox, hpot, hintt, hintq, hintf, hintmass,
    hlowu, hmass, hsum⟩ := hrest L hL N hN Φ hnorm hlow
  exact ⟨ε, c, C, B, eBf, hC, hloc N L ε c (Φ : X N → ℝ), hbox, hpot, hintt,
    hintq, hintf, hintmass, hlowu, hmass, hsum⟩

/-- `SlidingRawNorm` in the quotient form `DLSlideNorm` (norm-one states). -/
theorem dlSlideNorm_of_slidingRawNorm {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} (hd : SlidingRawNorm v h b K_B R' J ε₀) :
    DLSlideNorm v h b K_B R' J ε₀ := by
  intro L hL N hN Φ hnorm hlow
  have hres := hd L hL N hN Φ hnorm hlow
  rw [energyWord_eq Φ, hnorm, div_one]
  exact hres

/-- **`DLSlideCov` from the residual bundle** (composing the two steps). -/
theorem dlSlideCov_of_data {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ}
    {d M : ℕ} (hdata : SlidingSumData v h b K_B R' J ε₀ d M) :
    DLSlideCov v h b K_B R' J ε₀ :=
  dlSlideCov_of_dlSlideNorm (dlSlideNorm_of_slidingRawNorm (slidingRawNorm_of_data hdata))

/-- **FS `eq:apriorinn+` (second conjunct) in the covariant normalisation**:
the sliding inequality plus the low-state condition bound the excited count *per
unit `abox`-norm* by the FS window
`(2L²/b)·4πρ²(a v)L³(J+K_B³)·√(ρ(a v)³)`. -/
theorem aprioriNPlusCov_of_dlSlideCov {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B ε₀ R' J : ℝ} (hb : 0 < b) (ha : 0 ≤ a v) (hR' : 0 ≤ R')
    (hslide : DLSlideCov v h b K_B R' J ε₀) :
    AprioriNPlusCov v h J
      (fun N L => (2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
        * (J + K_B ^ 3) * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))) ε₀ := by
  intro L hL N hN Φ hΦ
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hIpos : 0 < sqNormN N L (Φ : X N → ℝ) := Φ.sq_pos
  have hE := energyWord_le_of_wordDens_le (v := v) (h := h) (J := J) (hL := hLpos)
    (μ := dens N L) hΦ
  have hsl := hslide L hL N hN Φ hΦ
  -- the product form: `(b/2L²)·(cnPlus/∫Φ²) ≤ 4πρ²aL³(J+K_B³)√(ρa³)`
  have h1 : (b / (2 * L ^ 2)) * (cnPlus L (Φ : X N → ℝ) / sqNormN N L (Φ : X N → ℝ))
      ≤ 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
          * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    have hexp : - (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (1 - J * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          + 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
        = 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
            * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) := by ring
    linarith [hsl, hE, hexp, hR']
  -- multiply by `∫Φ² > 0` and divide by `b/(2L²) > 0`
  have hb2 : 0 < b / (2 * L ^ 2) := by positivity
  have h2 : (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
      ≤ (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
            * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) * sqNormN N L (Φ : X N → ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right h1 (le_of_lt hIpos)
    have hid : (b / (2 * L ^ 2)) * (cnPlus L (Φ : X N → ℝ) / sqNormN N L (Φ : X N → ℝ))
          * sqNormN N L (Φ : X N → ℝ)
        = (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ) := by
      field_simp
    rwa [hid] at hmul
  have h3 : cnPlus L (Φ : X N → ℝ)
      ≤ (2 * L ^ 2 / b) * ((4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
            * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) * sqNormN N L (Φ : X N → ℝ)) := by
    have h2' : cnPlus L (Φ : X N → ℝ) * (b / (2 * L ^ 2))
        ≤ (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
            * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) * sqNormN N L (Φ : X N → ℝ) := by
      rw [mul_comm]
      exact h2
    have := (le_div_iff₀ hb2).mpr h2'
    have hQid : (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
            * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) * sqNormN N L (Φ : X N → ℝ)
          / (b / (2 * L ^ 2))
        = (2 * L ^ 2 / b) * ((4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
            * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) * sqNormN N L (Φ : X N → ℝ)) := by
      rw [div_div_eq_mul_div]
      ring
    rwa [hQid] at this
  have h4 : (2 * L ^ 2 / b) * ((4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
        * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) * sqNormN N L (Φ : X N → ℝ))
      = ((2 * L ^ 2 / b) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * (J + K_B ^ 3)
        * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))) * sqNormN N L (Φ : X N → ℝ) := by ring
  rwa [h4] at h3

/-- **The repaired decomposition of the deep input**: the covariant a-priori
window and the covariant Bogoliubov window bound give the per-state spectral
input FS `eq:ToProve` (`Work.UBB.SpectralInput`), which is already
normalisation-correct. -/
theorem spectralInput_of_cov {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ}
    (ha1 : AprioriNPlusCov v h J W ε₀) (ha2 : BogoliubovLowCov v h J W ε₀ η₀) :
    SpectralInput v h J ε₀ η₀ := by
  rcases ha2 with ⟨C, hC, hlow⟩
  exact ⟨C, hC, fun L hL N hN Φ hΦ => hlow L hL N hN Φ (ha1 L hL N hN Φ hΦ) hΦ⟩

/-- **`DLSlideCov` from the two named pieces** (composition of
`slidingSumData_of` with `dlSlideCov_of_data`). -/
theorem dlSlideCov_of_localisation_and_boxSum {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} (hloc : SlidingLocalisation d b)
    (hrest : BoxSumBound v h b K_B R' J ε₀ d M) :
    DLSlideCov v h b K_B R' J ε₀ :=
  dlSlideCov_of_dlSlideNorm
    (dlSlideNorm_of_slidingRawNorm (slidingRawNorm_of_data (slidingSumData_of hloc hrest)))

end Work.UBBInputs
