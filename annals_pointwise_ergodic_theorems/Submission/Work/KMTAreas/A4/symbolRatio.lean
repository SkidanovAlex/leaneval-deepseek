import Mathlib
import Submission.Work.KMTAreas.A4.symRealMono
import Submission.Work.KMTAreas.A4.symbolOfReal
import Submission.Work.KMTAreas.A4.measurableSymReal

namespace Work.KMTAreas.A4

open MeasureTheory
open Work.Analysis.IonescuWainger

/-- **Nesting of the Ionescu–Wainger symbols.**  For `l' ≤ l` and `k' ≤ k` the symbol
`σ_{l',k'} = ∑_{α ∈ (ℚ/ℤ)_{≤l'}} η_{≤k'}(· - α)` is a bounded multiple of the symbol
`σ_{l,k} = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(· - α)`: there is `m` with `MemLp m ⊤`, `‖m‖ ≤ 1` and
`σ_{l',k'} = m · σ_{l,k}` pointwise.  (The point behind it: `(ℚ/ℤ)_{≤l'}` is contained in
`(ℚ/ℤ)_{≤l}`, and `η_{≤k'} ≤ η_{≤k}` pointwise for `k' ≤ k`, since `η` is nonnegative and equal
to `1` on `[-1/2,1/2]`; so `0 ≤ σ_{l',k'} ≤ σ_{l,k}` and one can take `m = σ_{l',k'}/σ_{l,k}`.) -/
theorem symbolRatio (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l l' : ℕ} (hl : l' ≤ l) {k k' : ℤ} (hk : k' ≤ k) :
    ∃ m : Work.Analysis.IonescuWainger.Circle → ℂ,
      MeasureTheory.MemLp m ⊤ Work.Analysis.IonescuWainger.circleMeasure ∧
      (∀ ξ : Work.Analysis.IonescuWainger.Circle, ‖m ξ‖ ≤ 1) ∧
      (∀ ξ : Work.Analysis.IonescuWainger.Circle,
        Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l')
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k')) ξ
          = m ξ * Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) ξ) := by
  -- Write `R = 2^k`; then `2^k' ≤ R` and both symbols are expanded over `suppIdx R`.
  set R : ℝ := (2 : ℝ) ^ k with hRdef
  have hk'R : (2 : ℝ) ^ k' ≤ R := by
    rw [hRdef]
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hk
  -- Both complex symbols are the complexifications of the real symbols.
  have hσl : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut KMTContract.kmtEta k)) ξ
        = ((symReal ρ l k R ξ : ℝ) : ℂ) := fun ξ => symbolOfReal ρ l k le_rfl ξ
  have hσl' : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut KMTContract.kmtEta k')) ξ
        = ((symReal ρ l' k' R ξ : ℝ) : ℂ) := fun ξ => symbolOfReal ρ l' k' hk'R ξ
  -- The real symbol is nonnegative and monotone in `(l,k)`.
  have hmono : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      symReal ρ l' k' R ξ ≤ symReal ρ l k R ξ :=
    fun ξ => symRealMono hρ hρ1 hl hk R ξ
  have hnn : ∀ ξ : Work.Analysis.IonescuWainger.Circle, 0 ≤ symReal ρ l' k' R ξ :=
    fun ξ => symReal_nonneg ρ l' k' R ξ
  -- Measurability of the two complex symbols.
  have hmeasl : Measurable (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut KMTContract.kmtEta k)) ξ) := by
    rw [funext hσl]
    exact Complex.measurable_ofReal.comp (measurableSymReal ρ l k R)
  have hmeasl' : Measurable (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut KMTContract.kmtEta k')) ξ) := by
    rw [funext hσl']
    exact Complex.measurable_ofReal.comp (measurableSymReal ρ l' k' R)
  refine ⟨fun ξ : Work.Analysis.IonescuWainger.Circle =>
      iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut KMTContract.kmtEta k')) ξ
        / iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut KMTContract.kmtEta k)) ξ, ?_, ?_, ?_⟩
  · -- essential boundedness of the quotient
    refine MemLp.mono' (memLp_top_const (1 : ℝ)) ((hmeasl'.div hmeasl).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [hσl' ξ, hσl ξ]
    exact norm_ofReal_div_le_one (hnn ξ) (hmono ξ)
  · -- the pointwise bound `‖m ξ‖ ≤ 1`
    intro ξ
    dsimp only
    rw [hσl' ξ, hσl ξ]
    exact norm_ofReal_div_le_one (hnn ξ) (hmono ξ)
  · -- the pointwise identity `σ_{l',k'} = m · σ_{l,k}`
    intro ξ
    dsimp only
    rw [hσl' ξ, hσl ξ]
    by_cases hr : symReal ρ l k R ξ = 0
    · have hr' : symReal ρ l' k' R ξ = 0 := by
        have h := hmono ξ
        rw [hr] at h
        exact le_antisymm h (hnn ξ)
      rw [hr, hr']
      simp
    · exact (div_mul_cancel₀ _ (by rw [Complex.ofReal_ne_zero]; exact hr)).symm

end Work.KMTAreas.A4
