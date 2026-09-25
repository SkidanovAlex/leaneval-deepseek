import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.Value.moserClassicalChainX
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.Fleet.selfImprove

/-! # The windowed Moser sup bound

The target `Work.Value.moserWindowedSupBound`: from the *windowed* real-exponent Caccioppoli
hypothesis (levels `γ ≥ 1` with `∃k ≥ 1, |γ-k| < δk`) one gets the Moser sup bound.  The proof
takes the integer levels `γ = k` of the hypothesis, feeds them into the classical-Moser-boost
chain (`Value.classicalChainFamilyX`, proved in terms of `Value.classicalMoserBoost`), and
concludes with `Work.NN.Core.Fleet.selfImprove`.
-/
namespace Work.Value

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

/-- The windowed hypothesis, at the integer level `k`, gives the classical level-`k` weighted
Caccioppoli inequality with the same constant. -/
lemma intLevelHypX {n : ℕ} {ρ : Fin n → ℝ} {C₀ δ : ℝ} (hδ : 0 < δ)
    {u : Work.NN.Core.Cn n → ℂ}
    (hHyp : ∀ (γ : ℝ), 1 ≤ γ →
      (∃ k : ℕ, 1 ≤ k ∧ |γ - (k : ℝ)| < δ * (k : ℝ)) →
      ∀ (ψ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ ψ z) →
        ∫ z in Work.CR.Flat.polydisc 0 ρ, (ψ z)^2 * ‖u z‖ ^ (2*γ-2) *
            (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
          ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ ψ z‖^2 * ‖u z‖ ^ (2*γ)) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
      ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖ ^ (2*k-2) *
          (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
        ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k) := by
  intro k hk φ hφcd hφcs hφts hφnn
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hwin : ∃ k' : ℕ, 1 ≤ k' ∧ |(k:ℝ) - (k' : ℝ)| < δ * (k' : ℝ) := by
    refine ⟨k, hk, ?_⟩
    rw [sub_self, abs_zero]
    exact mul_pos hδ (by exact_mod_cast (by omega : 0 < k))
  have h := hHyp (k:ℝ) hk1 hwin φ hφcd hφcs hφts hφnn
  have hms : MeasurableSet (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) ρ) :=
    (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  have hL : (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖ ^ (2*(k:ℝ)-2) *
        (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)))
      = ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖ ^ (2*k-2) *
        (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)) := by
    refine setIntegral_congr_fun hms fun z _ => ?_
    have h2 : (2*(k:ℝ) - 2 : ℝ) = ((2*k-2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2*k)]; push_cast; ring
    rw [h2, Real.rpow_natCast]
  have hR : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*(k:ℝ)))
      = ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k) := by
    refine setIntegral_congr_fun hms fun z _ => ?_
    have h2 : (2*(k:ℝ) : ℝ) = ((2*k : ℕ) : ℝ) := by push_cast; ring
    rw [h2, Real.rpow_natCast]
  rw [hL, hR] at h
  exact h

/-- Restriction of an integer-level weighted Caccioppoli hypothesis to a smaller polydisc. -/
lemma intLevelHypXRestrictX {n : ℕ} {ρ ρ' : Fin n → ℝ} (hρ'ρ : ∀ j, ρ' j ≤ ρ j)
    {C₀ : ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hH : ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
      ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖ ^ (2*k-2) *
          (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
        ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k)) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ' → (∀ z, 0 ≤ φ z) →
      ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * ‖u z‖ ^ (2*k-2) *
          (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
        ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k) := by
  intro k hk φ hφcd hφcs hφts hφnn
  have hsub : Work.CR.Flat.polydisc 0 ρ' ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono hρ'ρ
  have h := hH k hk φ hφcd hφcs (hφts.trans hsub) hφnn
  have hmeasρ : MeasurableSet (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) ρ) :=
    (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  have hF : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ \ Work.CR.Flat.polydisc 0 ρ',
      (φ z)^2 * ‖u z‖ ^ (2*k-2) *
          (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)) = 0 := by
    intro z hz
    have hz0 : φ z = 0 := by
      by_contra hne
      exact hz.2 (hφts (subset_closure (Function.mem_support.mpr hne)))
    rw [hz0]; ring
  have hG : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ \ Work.CR.Flat.polydisc 0 ρ',
      ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k) = 0 := by
    intro z hz
    have hzts : z ∉ tsupport φ := fun h => hz.2 (hφts h)
    have hdf : fderiv ℝ φ z = 0 := by
      have hmem : (tsupport φ)ᶜ ∈ 𝓝 z := (isClosed_tsupport φ).isOpen_compl.mem_nhds hzts
      have h0 : φ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
        filter_upwards [hmem] with y hy
        exact Function.notMem_support.mp (fun h => hy (subset_closure h))
      rw [h0.fderiv_eq]; simp
    rw [hdf]; simp
  have e1 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖ ^ (2*k-2) *
        (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)))
      = ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * ‖u z‖ ^ (2*k-2) *
        (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasρ hsub hF
  have e2 : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k))
      = ∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasρ hsub hG
  rw [e1, e2] at h
  exact h

theorem moserWindowedSupBoundX {n : ℕ} (hn : 0 < n) {σ ρ : Fin n → ℝ} (hσ0 : ∀ j, 0 < σ j)
    (hρ0 : ∀ j, 0 < ρ j) (hσρ : ∀ j, σ j < ρ j) {C₀ δ : ℝ} (hC₀ : 0 < C₀) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Work.NN.Core.Cn n → ℂ},
      ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
      (∀ (γ : ℝ), 1 ≤ γ →
        (∃ k : ℕ, 1 ≤ k ∧ |γ - (k : ℝ)| < δ * (k : ℝ)) →
        ∀ (ψ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ ψ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ, (ψ z)^2 * ‖u z‖ ^ (2*γ-2) *
              (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
            ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ ψ z‖^2 * ‖u z‖ ^ (2*γ)) →
      ∀ z ∈ Work.CR.Flat.polydisc 0 σ,
        ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm u 2
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))

    := by
  have hn0 : 0 < n := by omega
  set ρstar : Fin n → ℝ := fun j => (σ j + ρ j) / 2 with hρstardef
  have hσρstar : ∀ j, σ j < ρstar j := by
    intro j; rw [hρstardef]; linarith [hσρ j]
  have hρstarρ : ∀ j, ρstar j < ρ j := by
    intro j; rw [hρstardef]; linarith [hσρ j]
  obtain ⟨A, B, hA, hB, hfam⟩ := classicalChainFamilyX hn0 hσ0 hσρstar hC₀
  obtain ⟨C, hC, hCb⟩ := Work.NN.Core.Fleet.selfImprove hn0 hσ0 hσρstar hρstarρ hA hB
  refine ⟨C, hC, ?_⟩
  intro u hu hHyp
  have hsub : Work.CR.Flat.polydisc 0 ρstar ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono (fun j => (hρstarρ j).le)
  have hH := intLevelHypXRestrictX (n := n) (ρ := ρ) (ρ' := ρstar)
    (fun j => (hρstarρ j).le) (C₀ := C₀) (u := u) (intLevelHypX hδ hHyp)
  exact hCb u hu (hfam u (hu.mono hsub) hH)


end

end Work.Value
