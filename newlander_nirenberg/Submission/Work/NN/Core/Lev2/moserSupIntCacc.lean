import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Lev.moserTheta
import Submission.Work.NN.Core.Lev2.srcMoserBoost
import Submission.Work.NN.Core.Lev2.srcChainMeanValueFamily
import Submission.Work.NN.Core.Lev2.selfImproveLipCopy

namespace Work.NN.Core.Lev2

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

/-! ## Small bookkeeping lemmas (complexification, restriction of the hypothesis) -/

/-- Complexification preserves `eLpNorm`. -/
lemma eLpNorm_ofReal_complexify {n : ℕ} {W : Work.NN.Core.Cn n → ℝ} {p : ENNReal}
    {μ : Measure (Work.NN.Core.Cn n)} (hW : AEStronglyMeasurable W μ) :
    MeasureTheory.eLpNorm (fun z => (W z : ℂ)) p μ = MeasureTheory.eLpNorm W p μ := by
  refine MeasureTheory.eLpNorm_congr_norm_ae
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hW) hW ?_
  filter_upwards with z
  exact Complex.norm_real (W z)

/-- Complexification preserves `eLpNorm`, Lipschitz version. -/
lemma eLpNorm_ofReal_eq_of_lipschitz {n : ℕ} {K : NNReal} {W : Work.NN.Core.Cn n → ℝ}
    {ρ r : Fin n → ℝ} (hLip : LipschitzOnWith K W (Work.CR.Flat.polydisc 0 ρ))
    (hr : ∀ j, r j ≤ ρ j) {p : ENNReal} :
    MeasureTheory.eLpNorm (fun z => (W z : ℂ)) p
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = MeasureTheory.eLpNorm W p (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) :=
  eLpNorm_ofReal_complexify ((hLip.mono (Work.CR.Flat.polydisc_mono hr)).continuousOn
    |>.aestronglyMeasurable (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet)

/-- Complexification preserves `LipschitzOnWith`. -/
lemma lipschitzOnWith_ofReal_complexify {n : ℕ} {K : NNReal} {W : Work.NN.Core.Cn n → ℝ}
    {s : Set (Work.NN.Core.Cn n)} (h : LipschitzOnWith K W s) :
    LipschitzOnWith K (fun z => (W z : ℂ)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have h1 := h.dist_le_mul x hx y hy
  have h2 : dist ((W x : ℂ)) ((W y : ℂ)) = dist (W x) (W y) := by
    rw [dist_eq_norm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h2]
  exact h1

/-- **Restriction of the sourced power Caccioppoli family to a smaller polydisc.** -/
lemma srcHypRestrict {n : ℕ} {ρ ρ' : Fin n → ℝ} (hρ'ρ : ∀ j, ρ' j ≤ ρ j) {A Λ : ℝ}
    {W : Work.NN.Core.Cn n → ℝ}
    (hH : ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
        ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
          ≤ A * ((k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (W z)^(2*k-2))
                + (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (W z)^(2*k)))) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ' → (∀ z, 0 ≤ φ z) →
        ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
          ≤ A * ((k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (W z)^(2*k-2))
                + (∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * (W z)^(2*k))) := by
  intro k hk φ hφcd hφcs hφts hφnn
  have hsub : Work.CR.Flat.polydisc 0 ρ' ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono hρ'ρ
  have hmeasρ : MeasurableSet (Work.CR.Flat.polydisc 0 ρ) :=
    (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  have h := hH k hk φ hφcd hφcs (hφts.trans hsub) hφnn
  have hφzero : ∀ z, z ∉ Work.CR.Flat.polydisc 0 ρ' → φ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (hφts (subset_closure (Function.mem_support.mpr hne)))
  have hdfzero : ∀ z, z ∉ Work.CR.Flat.polydisc 0 ρ' → fderiv ℝ φ z = 0 := by
    intro z hz
    have hU : (tsupport φ)ᶜ ∈ 𝓝 z := (isClosed_tsupport φ).isOpen_compl.mem_nhds
      (fun h => hz (hφts h))
    have h0 : φ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      filter_upwards [hU] with y hy
      exact Function.notMem_support.mp (fun h => hy (subset_closure h))
    rw [h0.fderiv_eq]; simp
  have e1 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2)
      = ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2 := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasρ hsub ?_
    intro z hz
    rw [hφzero z hz.2]; simp
  have e2 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (W z)^(2*k-2))
      = ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (W z)^(2*k-2) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasρ hsub ?_
    intro z hz
    rw [hφzero z hz.2]; simp
  have e3 : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (W z)^(2*k))
      = ∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * (W z)^(2*k) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasρ hsub ?_
    intro z hz
    rw [hdfzero z hz.2]; simp
  rw [e1, e2, e3] at h
  exact h

/-! ## The target lemma -/

theorem moserSupIntCacc {n : ℕ} (hn : 0 < n) {σ ρ : Fin n → ℝ}
    (hσ0 : ∀ j, 0 < σ j) (hρ0 : ∀ j, 0 < ρ j) (hσρ : ∀ j, σ j < ρ j)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {K : NNReal} {W : Work.NN.Core.Cn n → ℝ},
        LipschitzOnWith K W (Work.CR.Flat.polydisc 0 ρ) → (∀ z, Λ ≤ W z) →
        (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
            ≤ A * ((k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (W z)^(2*k-2))
                  + (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (W z)^(2*k)))) →
        ∀ z ∈ Work.CR.Flat.polydisc 0 σ,
          ENNReal.ofReal (W z) ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm W 2
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ)) := by
  set ρstar : Fin n → ℝ := fun i => (σ i + ρ i) / 2 with hρstardef
  have hσρstar : ∀ i, σ i < ρstar i := fun i => by rw [hρstardef]; linarith [hσρ i]
  have hρstarρ : ∀ i, ρstar i < ρ i := fun i => by rw [hρstardef]; linarith [hσρ i]
  have hρstar0 : ∀ i, 0 < ρstar i := fun i => lt_trans (hσ0 i) (hσρstar i)
  obtain ⟨C₁, hC₁pos, hBoost⟩ := srcMoserBoost (n := n) hn (A := A) hA
  obtain ⟨A', B, hA'pos, hB1, hFam⟩ :=
    srcChainMeanValueFamily (n := n) (σ := σ) (ρstar := ρstar) hn hσ0 hσρstar hC₁pos
  obtain ⟨C, hCpos, hSelf⟩ :=
    selfImproveLipCopy (n := n) (σ := σ) (ρ := ρ) (ρstar := ρstar) hn hσ0 hσρstar hρstarρ
      hA'pos hB1
  refine ⟨C, hCpos, ?_⟩
  intro Λ hΛ K W hLip hge hH z hz
  have hsub : Work.CR.Flat.polydisc 0 ρstar ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono (fun i => (hρstarρ i).le)
  have hLip' : LipschitzOnWith K W (Work.CR.Flat.polydisc 0 ρstar) := hLip.mono hsub
  have hH' := srcHypRestrict (ρ := ρ) (ρ' := ρstar) (fun i => (hρstarρ i).le) (A := A) (Λ := Λ) hH
  have hboostC : ∀ {r s : Fin n → ℝ}, (∀ j, r j < s j) → (∀ j, s j < ρstar j) →
      ∀ {χ : Work.NN.Core.Cn n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        tsupport χ ⊆ Work.CR.Flat.polydisc 0 s → (∀ z, 0 ≤ χ z) → (∀ z, χ z ≤ 1) →
        (∀ z, (∀ j, ‖z j‖ ≤ r j) → χ z = 1) →
      ∀ {L : ℝ}, 0 ≤ L → (∀ z, ‖fderiv ℝ χ z‖ ≤ L) →
      ∀ (k : ℕ), 1 ≤ k →
        MeasureTheory.eLpNorm (fun z => (W z : ℂ))
            (ENNReal.ofReal (2 * ((k : ℝ) * Work.NN.Core.Lev.moserTheta n)))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
          ≤ (ENNReal.ofReal (C₁ * (1 + L) * (1 + (k : ℝ)))) ^ (1 / (2 * (k : ℝ))) *
            MeasureTheory.eLpNorm (fun z => (W z : ℂ)) (ENNReal.ofReal (2 * (k : ℝ)))
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    intro r s hrs hsρ χ hχcd hχcs hχsupp hχnn hχle1 hχone L hL0 hLgrad k hk
    have hrρ : ∀ j, r j ≤ ρ j :=
      fun j => le_trans (le_of_lt (hrs j)) (le_trans (le_of_lt (hsρ j)) ((hρstarρ j).le))
    have hsρρ : ∀ j, s j ≤ ρ j := fun j => le_trans (le_of_lt (hsρ j)) ((hρstarρ j).le)
    rw [eLpNorm_ofReal_eq_of_lipschitz (ρ := ρ) (r := r) hLip hrρ,
        eLpNorm_ofReal_eq_of_lipschitz (ρ := ρ) (r := s) hLip hsρρ]
    exact hBoost hρstar0 hΛ hLip' hge hH' hrs hsρ hχcd hχcs hχsupp hχnn hχle1 hχone
      hL0 hLgrad k hk
  have hLipC : LipschitzOnWith K (fun z => (W z : ℂ)) (Work.CR.Flat.polydisc 0 ρ) :=
    lipschitzOnWith_ofReal_complexify hLip
  have hfam := hFam (fun z => (W z : ℂ)) (lipschitzOnWith_ofReal_complexify hLip') hboostC
  have hres := hSelf (fun z => (W z : ℂ)) hLipC hfam z hz
  have hzeq : ‖((fun z => (W z : ℂ)) z)‖ = W z := by
    show ‖(W z : ℂ)‖ = W z
    rw [Complex.norm_real, Real.norm_of_nonneg (le_trans hΛ (hge z))]
  rw [hzeq, eLpNorm_ofReal_eq_of_lipschitz (ρ := ρ) (r := ρ) hLip (fun j => le_rfl)] at hres
  exact hres


end Work.NN.Core.Lev2
