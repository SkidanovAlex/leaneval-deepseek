import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.GalTame.mulJet_pointwise_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `mulJet_le_sharp_univ`: the sharp Leibniz `L²` estimate on `ℝⁿ`

For a smooth cut-off `φ : (Fin n → ℝ) → ℝ` whose iterated partial derivatives of order `≤ m`
are bounded by `Kφ`, a smooth `W : (Fin n → ℝ) → ℂ` with compact support, and a multi-index
`β : Fin m → Fin n`, one has

`∫ ‖∂^β (φ · W)‖² ≤ C Kφ² Σ_{j ≤ m} Σ_{γ : Fin j → Fin n} ∫ ‖∂^γ W‖²`,

the integral being taken over all of `ℝⁿ` (as opposed to a fundamental domain, as in
`Work.Diff.STE.B3.mulJet_le_clean`).

The proof is split in two:

* `Work.Diff.STE.Lead.GalTame.mulJet_pointwise_le` (a separate, self-contained file) is the
  *pointwise* sharp Leibniz bound
  `‖∂^β(φ·W) z‖² ≤ C Kφ² Σ_{j ≤ m} Σ_γ ‖∂^γ W z‖²`,
  obtained from the iterated Leibniz rule `Work.Diff.STE.pdList_mul_sub` plus Cauchy–Schwarz;
* the integration step `integral_leibniz_bound` below, which uses that all the functions involved
  are continuous with compact support (the iterated derivatives of `W` vanish identically off
  `tsupport W`, which is compact), so that `MeasureTheory.integral_mono`,
  `MeasureTheory.integral_const_mul` and `MeasureTheory.integral_finset_sum` apply.
-/

noncomputable section

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory Filter

/-! ## Elementary smoothness/continuity helpers -/

/-- Lowering a smoothness level from `∞` to a finite one. -/
private lemma contDiff_level_le (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-- `pdVec` of a globally smooth function is continuous, at any order. -/
private lemma continuous_pdVec_of_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) (l : Fin m → Fin n) :
    Continuous (Work.Diff.STE.pdVec m l f) :=
  Work.Diff.STE.continuous_pdVec m l f (hf.of_le (contDiff_level_le m))

/-- The squared norm of a continuous function is continuous. -/
private lemma continuous_normSq_pd {n : ℕ} {F : (Fin n → ℝ) → ℂ} (h : Continuous F) :
    Continuous (fun z : Fin n → ℝ => ‖F z‖ ^ 2) := by
  have h2 := h.norm.mul h.norm
  convert h2 using 1
  ext z
  simp only [Pi.mul_apply, pow_two]

/-- The squared norm of an iterated partial derivative of a smooth function is continuous. -/
private lemma continuous_normSq_pdVec_of_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) (l : Fin m → Fin n) :
    Continuous (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec m l f z‖ ^ 2) :=
  continuous_normSq_pd (continuous_pdVec_of_smooth hf m l)

/-! ## Jets of a function vanishing on an open set -/

/-- All iterated partial derivatives of a function that vanishes on an open set vanish on it. -/
private lemma pdList_eq_zero_of_isOpen {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {F : (Fin n → ℝ) → ℂ} (hF : ∀ y ∈ U, F y = 0) (l : List (Fin n)) :
    ∀ y ∈ U, Work.Diff.STE.pdList l F y = 0 := by
  induction l with
  | nil => intro y hy; simpa [Work.Diff.STE.pdList] using hF y hy
  | cons i l ih =>
      intro y hy
      have hz : Work.Diff.STE.pdList l F =ᶠ[nhds y] 0 :=
        Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => ih z hz)
      have hfd : fderiv ℝ (Work.Diff.STE.pdList l F) y = 0 := by
        rw [hz.fderiv_eq]; simp
      show Work.Diff.STE.pd i (Work.Diff.STE.pdList l F) y = 0
      simp only [Work.Diff.STE.pd]
      rw [hfd]
      simp

/-- The same for `pdVec`. -/
private lemma pdVec_eq_zero_of_isOpen {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {F : (Fin n → ℝ) → ℂ} (hF : ∀ y ∈ U, F y = 0) (j : ℕ) (γ : Fin j → Fin n) :
    ∀ y ∈ U, Work.Diff.STE.pdVec j γ F y = 0 :=
  fun y hy => pdList_eq_zero_of_isOpen hU hF (List.ofFn γ) y hy

/-- A function vanishing off the (compact) support of `W` has compact support. -/
private lemma hasCompactSupport_of_vanishes_off {n : ℕ} {β : Type*} [TopologicalSpace β] [Zero β]
    {W : (Fin n → ℝ) → ℂ} {F : (Fin n → ℝ) → β} (hW : HasCompactSupport W)
    (h : ∀ z, z ∉ tsupport W → F z = 0) : HasCompactSupport F := by
  have hsub : Function.support F ⊆ tsupport W := fun z hz => by
    by_contra hz'
    exact hz (h z hz')
  exact IsCompact.of_isClosed_subset hW (isClosed_tsupport F)
    (closure_minimal hsub (isClosed_tsupport W))

/-- Off `tsupport W`, every iterated partial derivative of `W` vanishes. -/
private lemma pdVec_eq_zero_compl_tsupport {n : ℕ} {W : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hz : z ∉ tsupport W) (j : ℕ) (γ : Fin j → Fin n) :
    Work.Diff.STE.pdVec j γ W z = 0 :=
  pdVec_eq_zero_of_isOpen (isClosed_tsupport W).isOpen_compl
    (fun y hy => by
      by_contra h
      exact hy (subset_tsupport W h)) j γ z hz

/-! ## The integration step -/

/-- Pointwise sharp Leibniz bound `⟹` integrated sharp Leibniz bound on `ℝⁿ`.

All the integrands are continuous and compactly supported (the iterated derivatives of `W` are
supported in the compact set `tsupport W`), so the usual rules for the Bochner integral apply. -/
private lemma integral_leibniz_bound (n m : ℕ) {C : ℝ}
    (φ : (Fin n → ℝ) → ℝ) (W : (Fin n → ℝ) → ℂ) (Kφ : ℝ) (β : Fin m → Fin n)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWc : HasCompactSupport W)
    (hpt : ∀ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β
        (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
      ≤ C * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2) :
    ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β
        (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
      ≤ C * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
  set B : (Fin n → ℝ) → ℝ := fun z => ∑ j ∈ Finset.range (m + 1),
      ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 with hB
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * W z) :=
    (Complex.ofRealCLM.contDiff.comp hφ).mul hW
  have hcontL : Continuous (fun z : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2) :=
    continuous_normSq_pdVec_of_smooth hsm m β
  have hcontB : Continuous B := by
    rw [hB]
    refine continuous_finsetSum (Finset.range (m + 1)) (fun j hj => ?_)
    exact continuous_finsetSum Finset.univ
      (fun γ hγ => continuous_normSq_pdVec_of_smooth hW j γ)
  have hcL : HasCompactSupport (fun z : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2) := by
    refine hasCompactSupport_of_vanishes_off hWc (fun z hz => ?_)
    have hU : IsOpen (tsupport W)ᶜ := (isClosed_tsupport W).isOpen_compl
    have hF : ∀ y ∈ (tsupport W)ᶜ, ((φ y : ℝ) : ℂ) * W y = 0 := by
      intro y hy
      have : W y = 0 := by
        by_contra h
        exact hy (subset_tsupport W h)
      simp [this]
    have h0 := pdVec_eq_zero_of_isOpen hU hF m β z hz
    rw [h0]
    simp
  have hcB : HasCompactSupport B := by
    refine hasCompactSupport_of_vanishes_off hWc (fun z hz => ?_)
    rw [hB]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    refine Finset.sum_eq_zero (fun γ hγ => ?_)
    rw [pdVec_eq_zero_compl_tsupport hz j γ]
    simp
  have hintL : Integrable (fun z : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2) :=
    hcontL.integrable_of_hasCompactSupport hcL
  have hintB : Integrable B := hcontB.integrable_of_hasCompactSupport hcB
  have h1 : ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β
        (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
      ≤ ∫ z : Fin n → ℝ, C * Kφ ^ 2 * B z :=
    integral_mono hintL (hintB.const_mul (C * Kφ ^ 2)) (fun z => hpt z)
  have h2 : ∫ z : Fin n → ℝ, C * Kφ ^ 2 * B z = C * Kφ ^ 2 * ∫ z : Fin n → ℝ, B z :=
    integral_const_mul (C * Kφ ^ 2) B
  have h3 : ∫ z : Fin n → ℝ, B z = ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
      ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
    rw [hB, integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [integral_finsetSum]
      intro γ hγ
      exact (continuous_normSq_pdVec_of_smooth hW j γ).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanishes_off hWc (fun z hz => by
          rw [pdVec_eq_zero_compl_tsupport hz j γ]; simp))
    · intro j hj
      exact integrable_finsetSum _ (fun γ hγ =>
        (continuous_normSq_pdVec_of_smooth hW j γ).integrable_of_hasCompactSupport
          (hasCompactSupport_of_vanishes_off hWc (fun z hz => by
            rw [pdVec_eq_zero_compl_tsupport hz j γ]; simp)))
  rw [h2, h3] at h1
  exact h1

/-! ## The target -/

theorem mulJet_le_sharp_univ (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : (Fin n → ℝ) → ℝ) (W : (Fin n → ℝ) → ℂ) (Kφ : ℝ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ →
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) W →
      HasCompactSupport W →
      (∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
        |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ) →
      ∀ (β : Fin m → Fin n),
        ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β
            (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
          ≤ C * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := mulJet_pointwise_le n m
  refine ⟨C, hC0, ?_⟩
  intro φ W Kφ hφ hW hWc hφb β
  exact integral_leibniz_bound n m φ W Kφ β hφ hW hWc (hC φ W Kφ hφ hW hφb β)

end Work.Diff.STE.Lead.GalTame
