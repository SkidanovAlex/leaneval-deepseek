import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword_radial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.DvapInputs` — the a priori inputs of FS `eq:dvapriori`

`Work.BoseFixB2.DvApriori.q4word_le_of_low` is FS `eq:Q4apriori` in the form the `d₁,d₂` node
consumes: for a *low* box state `Φ` (`eq:aprioriPsi` at the threshold `J`, with the particle
window `n ≤ 2μℓ³`) the renormalised four-Q word is bounded by `10·potappC·a·μ²ℓ³·‖Φ‖²`.

The proof is the FS chain: `wordB = kinFormB + potPart` (`Sector`), `kinFormB ≥ 0`
(`Word.kinFormB_nonneg`), `IsLowB` gives `wordB ≤ ℓ³Θ(a,J,μ)‖Φ‖² ≤ 0` (needs `J√(μa³) ≤ 1`),
the potential part is the corpus's `qLHSword` (`potWordU_form_eq_qLHSword`), FS's `lm:potapp`
lower bound `potapp_q4` gives `qLHSword ≥ -potappC(n²ℓ⁻³+μ²ℓ³)a‖Φ‖² + ½Q₄`, and `n ≤ 2μℓ³`
turns `n²ℓ⁻³ ≤ 4μ²ℓ³`.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-- The a priori `Q₄` bound (FS `eq:Q4apriori`) from the low-state hypothesis. -/
theorem q4word_le_of_low {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {R J : ℝ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦs : Submission.BoseGases.PermInvariant n Φ) (hΦn : Φ ≠ 0)
    (hℓ : 0 < fsSide v μ) (hμ : 0 < μ) (ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1)
    (hav : 0 < _root_.BoseGases.a v)
    (hR : 0 < R) (hRℓ : R ≤ fsSide v μ * Submission.BoseGases.chiR0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hJ : J ≤ (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3)
    (hn : (n : ℝ) ≤ 2 * μ * (fsSide v μ) ^ 3)
    (hlow : IsLowB v h J μ n Φ) :
    Submission.BoseGases.q4word (N := n) (fsSide v μ) (Submission.BoseGases.wPairC (fsSide v μ) v)
        (Submission.BoseGases.omC (Classical.choose h)) Φ
      ≤ (10 * Submission.BoseGases.potappC * (_root_.BoseGases.a v)) * μ ^ 2 * (fsSide v μ) ^ 3
          * normB v μ n Φ := by
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hsq : (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)
      = Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) := (Real.sqrt_eq_rpow _).symm
  have hKB3 : J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) ≤ 1 := by
    have h2 := Work.BoseFixB1.KB3_half_eq (A := _root_.BoseGases.a v) (μ := μ) hav hμ
    have h3 : fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) ≤ 1 :=
      Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)
    have h4 : J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1 := by
      calc J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)
          ≤ (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg ht0.le _)
        _ = fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) := h2
        _ ≤ 1 := h3
    rw [← hsq]
    exact h4
  have hΘ : Theta (_root_.BoseGases.a v) J μ ≤ 0 := by
    rw [Work.UBB.Theta]
    have h1 : 0 ≤ 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hpar := params_facts hμ hav ht1
  have hν : 0 ≤ normB v μ n Φ := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hkin : 0 ≤ kinPart v h μ n Φ :=
    Work.BoseKinLoc.Word.kinFormB_nonneg hℓ hpar.1 hpar.2.1 hpar.2.2.1 hpar.2.2.2.1 hpar.2.2.2.2
      ⟨Φ, hΦ, hΦs, hΦn⟩
  have hword0 : Work.BoseBoxFix.wordB v h μ n Φ ≤ 0 := by
    have h' : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 * Theta (_root_.BoseGases.a v) J μ
        * normB v μ n Φ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hΘ) hν
    have h2 := hlow
    unfold Work.BoseBoxFix.IsLowB at h2
    linarith
  have hpot0 : potPart v h μ n Φ ≤ 0 := by
    have h1 := wordB_eq_kinPart_add_potPart (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ)
    linarith
  have hbridge := potWordU_form_eq_qLHSword_of_radial (v := v) (h := h) (μ := μ) (n := n)
    (ℓ := fsSide v μ) hvrad hℓ (Φ := Φ) hΦ
  have hpot : potPart v h μ n Φ = Submission.BoseGases.qLHSword (N := n) (fsSide v μ) μ
      (Submission.BoseGases.wPairC (fsSide v μ) v)
      (Submission.BoseGases.wPairC (fsSide v μ) (Submission.BoseGases.g0 v h)) Φ := hbridge
  have hq4 := Submission.BoseGases.potapp_q4 (N := n) (ℓ := fsSide v μ) hℓ μ hμ.le hv hvrad hv1
    hR hv_supp h hRℓ hΦ.continuous
  have hQ4 : Submission.BoseGases.q4word (N := n) (fsSide v μ)
      (Submission.BoseGases.wPairC (fsSide v μ) v)
      (Submission.BoseGases.omC (Classical.choose h)) Φ
      ≤ 2 * (Submission.BoseGases.potappC
          * ((n : ℝ) ^ 2 / (fsSide v μ) ^ 3 + μ ^ 2 * (fsSide v μ) ^ 3)
          * (_root_.BoseGases.a v) * normB v μ n Φ) := by
    rw [hpot] at hpot0
    have hnorm : (∫ x in Submission.BoseGases.abox n (fsSide v μ), (Φ x) ^ 2)
        = Work.BoseBoxFix.normB v μ n Φ := rfl
    rw [hnorm] at hq4
    linarith
  have hn2 : (n : ℝ) ^ 2 / (fsSide v μ) ^ 3 ≤ 4 * μ ^ 2 * (fsSide v μ) ^ 3 := by
    have hℓ3 : 0 < (fsSide v μ) ^ 3 := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ 2 * μ * (fsSide v μ) ^ 3 := by positivity
    rw [div_le_iff₀ hℓ3]
    nlinarith [hn, hn0, h2, sq_nonneg ((n : ℝ) - 2 * μ * (fsSide v μ) ^ 3)]
  have hC0 : 0 ≤ Submission.BoseGases.potappC := by
    rw [Submission.BoseGases.potappC]; positivity
  have hX0 : 0 ≤ μ ^ 2 * (fsSide v μ) ^ 3 := by positivity
  have hX5 : (n : ℝ) ^ 2 / (fsSide v μ) ^ 3 + μ ^ 2 * (fsSide v μ) ^ 3
      ≤ 5 * (μ ^ 2 * (fsSide v μ) ^ 3) := by linarith
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hX5 hC0) hav.le) hν
  nlinarith [hQ4, hmain]


end

end Work.BoseFixB2.DvApriori
