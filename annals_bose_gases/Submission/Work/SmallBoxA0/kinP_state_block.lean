import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.KinPDefs
import Submission.Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC
import Submission.Work.SmallBoxA0.qLHSword_zero_case
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- At one particle the four-body pairing word `q4PairWord` has no pair to sum over. -/
lemma q4PairWord_one_eq_zero {s : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (Φ : X 1 → ℝ) :
    q4PairWord (ℓ := s) (v := v) h (Φ := Φ) = 0 := by
  unfold q4PairWord
  rw [show pairSet 1 = ∅ from by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp (Subsingleton.elim p.1 p.2)]
  simp

/-- The D1 constant `d1C Ct` is nonnegative. -/
lemma d1C_nonneg (Ct : ℝ) : 0 ≤ d1C Ct := by
  unfold d1C Submission.BoseGases.d1TargetC
  exact le_trans (by positivity : (0 : ℝ) ≤ 6 * (2 * Real.pi) ^ 3) (le_max_left _ _)

/-- **The `cS1 > 0` chain.**  From the potential summary `pot_sharp_summary`, the
`∬w₂`-slack `cs2_mass_slack`, the linear `Corr` bound, and a Bogoliubov-type lower bound on
`kinPWord + q4PairWord` of the shape

    `−½(1+η)·D·m²/s³ − B − E·n₊ ≤ kinPWord + q4PairWord`

(with `m² ≤ (N̂+1)²`), the per-state `kinPWord`-block shape follows.  The mass term of the
hypothesis `hQ` is `m²` rather than the sharp `(N̂+1)²`; the remaining deficit
`½D((N̂+1)² − m²)/s³` is nonnegative and is simply discarded. -/
private lemma cS1_pos_chain {n : ℕ} {s μ R0 K_B Ct c0 cgap ηq m Bq Eq : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hμ : 0 < μ) (hR0 : 0 < R0) (hKB : 0 < K_B)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (hRs : R0 ≤ s * chiR0) (hμs : 1 ≤ μ * s ^ 3) (hc0 : 0 < c0)
    {Φ : X (n + 1) → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox (n + 1) s, (Φ x) ^ 2) = 1)
    (hwin : (((n + 1 : ℕ) : ℝ)) / s ^ 3 ≤ 9 * μ)
    (hSc1 : 0 < cS1 s Φ)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * (a v))
    (hbox : totNCoeff s μ v + kinPBogErr Ct n s v ≤ cgap)
    (hCorr : 2 * (s ^ 3)⁻¹ * CorrWord s h Φ ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
    (hbr : Bq ≤ (88 * π + 39) * (a v) * μ)
    (heta : -((1 / 2) * ηq * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹)
        ≥ -(μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v)))
    (hQ : -((1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹)
        - Bq - Eq * cnPlus s Φ
        ≤ kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ))
    (hEq : Eq ≤ kinPBogErr Ct n s v)
    (hm : m ^ 2 ≤ ((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) :
    ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v
      - (272 * π + 40) * μ * (a v)
    ≤ kinPEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c0 cgap Φ := by
  classical
  set G : ℝ := kinPGamma R0 s K_B μ v with hGdef
  rw [hGdef] at heta
  have hav : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  have hDnn : 0 ≤ g0w0Mass (v := v) h :=
    g0w0Mass_nonneg (v := v) (R := R0) hR0 hv_nonneg hvrad hv_supp h
  have hnn : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have hμnn : 0 ≤ μ := le_of_lt hμ
  have hs3i : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
  have hGnn : 0 ≤ G := by
    rw [hGdef]; unfold kinPGamma
    refine add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3) ?_)
    exact Real.rpow_nonneg (by positivity) (1 / 2)
  -- the potential side
  have hpot : (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        + (1 / 2) * (s ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 s Φ
        + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
        - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
        - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
      ≤ qLHSword (N := n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    simpa [CorrWord] using pot_sharp_summary (N := n + 1) (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad
      hv_memL1 hR0 hv_supp h hRs hΦc.continuous hnorm hwin hSc1
  -- the `∬w₂`-slack
  have hslack := cs2_mass_slack (N := n + 1) (s := s) (μ := μ)
    (D := g0w0Mass (v := v) h) (v := v) hs hμ hDnn hD hav hμs hwin hΦc.continuous hnorm
  -- the linear `Corr` bound
  have hcorr : -((1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
      ≤ -(2 * (s ^ 3)⁻¹ * CorrWord s h Φ) := by linarith [hCorr]
  -- the mass bookkeeping: the deficit `m² → (N̂+1)²` is a nonnegative surplus
  have hsurplus : 0 ≤ (1 / 2) * (g0w0Mass (v := v) h)
      * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2 - m ^ 2) * (s ^ 3)⁻¹ := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDnn) ?_) hs3i
    linarith [hm]
  have hsplit : (1 / 2) * (g0w0Mass (v := v) h) * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
      - (1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹
      = (1 / 2) * (g0w0Mass (v := v) h) * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2 - m ^ 2) * (s ^ 3)⁻¹
        - (1 / 2) * ηq * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹ := by ring
  have hmass : (1 / 2) * (g0w0Mass (v := v) h) * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
        - (1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹
      ≥ -(μ ^ 2 * (a v) * s ^ 3 * G + μ * (a v)) := by
    rw [hsplit]; linarith [hsurplus, heta]
  -- the `n₊`-coefficient bookkeeping
  have hnf : 0 ≤ (cgap - kinPBogErr Ct n s v) * cnPlus s Φ - (1 / (72 * s ^ 2)) * cnPlus s Φ
      - potNCoeff μ (a v) * cnPlus s Φ - 72 * π * (a v) * μ * cnPlus s Φ := by
    have h0 : potNCoeff μ (a v) + 72 * π * (a v) * μ + 1 / (72 * s ^ 2) + kinPBogErr Ct n s v ≤ cgap := by
      rw [totNCoeff] at hbox
      linarith [hbox]
    nlinarith [h0, hnn]
  have hEeq : 0 ≤ (kinPBogErr Ct n s v - Eq) * cnPlus s Φ := by
    refine mul_nonneg ?_ hnn; linarith [hEq]
  -- arithmetic facts
  have hCpos : (0 : ℝ) ≤ 272 * π + 40 := by positivity
  have hC1 : (1 : ℝ) ≤ 272 * π + 40 := by nlinarith [Real.pi_pos]
  have hX : 0 ≤ μ ^ 2 * (a v) * s ^ 3 * G := by
    have h1 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
    have h2 : (0 : ℝ) ≤ s ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hGnn
  have hY : 0 ≤ μ * (a v) := mul_nonneg hμnn hav
  -- the assembly
  rw [kinPEnergy]
  have key : (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        - (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * G - (272 * π + 40) * μ * (a v)
      ≤ cgap * cnPlus s Φ + kinPWord s c0 Φ
        + qLHSword (N := n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    nlinarith [hpot, hslack, hcorr, hQ, hbr, hmass, hnf, hEeq, hX, hY, hC1, hDnn, hnn]
  have heq : ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
        * (8 * π * (a v) * s ^ 3)
      = (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) := by ring
  rw [heq]
  exact key

theorem kinP_state_block {n : ℕ} {s μ R0 K_B Ct c0 cgap : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hμ : 0 < μ) (hR0 : 0 < R0) (hKB : 0 < K_B)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (hRs : R0 ≤ s * chiR0) (hμs : 1 ≤ μ * s ^ 3) (hCt : 0 ≤ Ct) (hc0 : 0 < c0)
    (hav : 0 < a v) (hdil : 2 * c0 * (a v) ≤ 1)
    (hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    (hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
            (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * Ct * (R0 / s) ^ 2) * g0w0Mass (v := v) h)
    {Φ : X (n + 1) → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox (n + 1) s, (Φ x) ^ 2) = 1)
    (hwin : (((n + 1 : ℕ) : ℝ)) / s ^ 3 ≤ 9 * μ)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * (a v))
    (hbox : totNCoeff s μ v + kinPBogErr Ct n s v ≤ cgap)
    (hη : (1 / 2) * |kinPeta Ct R0 s c0 v| * (8 * π * (a v))
        * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
      ≤ μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v))
    (hbracket : kinPBracket Ct n s c0 v ≤ (88 * π + 39) * (a v) * μ)
    (hcorrreg : 4 * ((32 * π * chiSup ^ 2 * ((((n + 1 : ℕ) : ℝ)) + 1)) * (a v)) ^ 2
        * (((n + 1 : ℕ) : ℝ)) ≤ π * (a v) * μ * s ^ 4)
    (hcgap : 1 / (36 * s ^ 2) ≤ cgap)
    (hchi : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1) :
    ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v
      - (272 * π + 40) * μ * (a v)
    ≤ kinPEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c0 cgap Φ := by
  classical
  have hav' : 0 ≤ a v := le_of_lt hav
  have hμnn : 0 ≤ μ := le_of_lt hμ
  -- the linear `Corr` bound
  have hcorr : 2 * (s ^ 3)⁻¹ * CorrWord s h Φ ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ := by
    have hbound := corr_sqrt_bound_all (N := n + 1) (s := s) (R := R0) (v := v)
      hs hR0 hv_nonneg hvrad hv_supp h hRs hΦc.continuous hnorm
    exact corr_linear_of_sqrt (N := n + 1) (s := s) (μ := μ)
      (CorrC := 32 * π * chiSup ^ 2 * ((((n + 1 : ℕ) : ℝ)) + 1)) (v := v)
      h hs hav' (by positivity) hΦc.continuous hnorm hcorrreg hbound
  by_cases hSc1 : 0 < cS1 s Φ
  · by_cases hn : 1 ≤ n
    · obtain ⟨C1, hC1eq, _, hD1⟩ := lm_appbogolubov_pWord_explicitC (N := n) (s := s)
        (c0 := c0) (Ct := Ct) hs hc0 hv_nonneg hvrad hv_memL1 hR0 hv_supp h hRs hn hav hdil
        hWfin hCt hNewton
      subst hC1eq
      have hD1' := hD1 Φ hΦc hnorm
      have hQ : -((1 / 2) * (1 + kinPeta Ct R0 s c0 v) * (g0w0Mass (v := v) h)
            * (((n : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹)
          - kinPBracket Ct n s c0 v - kinPBogErr Ct n s v * cnPlus s Φ
          ≤ kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
        have h := hD1 Φ hΦc hnorm
        unfold kinPeta kinPBracket kinPBogErr d1C
        ring_nf at h ⊢
        linarith [h]
      have hm : ((n : ℝ) + 1) ^ 2 ≤ ((((n + 1 : ℕ) : ℝ)) + 1) ^ 2 := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        rw [Nat.cast_succ]; nlinarith [hn]
      have heta : -((1 / 2) * kinPeta Ct R0 s c0 v * (g0w0Mass (v := v) h)
            * ((n : ℝ) + 1) ^ 2 * (s ^ 3)⁻¹)
          ≥ -(μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v)) := by
        have hηsq : (1 / 2) * |kinPeta Ct R0 s c0 v| * (8 * π * (a v))
              * ((n : ℝ) + 1) ^ 2 * (s ^ 3)⁻¹
            ≤ μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v) := by
          have hf : 0 ≤ (1 / 2) * |kinPeta Ct R0 s c0 v| * (8 * π * (a v)) := by positivity
          have h2 := mul_le_mul_of_nonneg_left hm hf
          have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (s ^ 3)⁻¹)
          linarith [h3, hη]
        exact eta_mass_le (N := n) (s := s) (μ := μ) (η := kinPeta Ct R0 s c0 v)
          (D := g0w0Mass (v := v) h) (G := kinPGamma R0 s K_B μ v) (a := a v) hs
          (g0w0Mass_nonneg (v := v) (R := R0) hR0 hv_nonneg hvrad hv_supp h) hD hηsq
      exact cS1_pos_chain (ηq := kinPeta Ct R0 s c0 v) (m := (n : ℝ) + 1)
        (Bq := kinPBracket Ct n s c0 v) (Eq := kinPBogErr Ct n s v)
        h hs hμ hR0 hKB hv_nonneg hvrad hv_memL1 hv_supp hRs hμs hc0 hΦc hnorm hwin hSc1
        hD hbox hcorr hbracket heta hQ le_rfl hm
    · have hn0 : n = 0 := by omega
      subst hn0
      have hq4 : q4PairWord (ℓ := s) (v := v) h (Φ := Φ) = 0 := q4PairWord_one_eq_zero h Φ
      have hkP : 0 ≤ kinPWord s c0 Φ := kinPWord_nonneg hs Φ
      have hQ : -((1 / 2) * (1 + (0 : ℝ)) * (g0w0Mass (v := v) h) * (0 : ℝ) ^ 2 * (s ^ 3)⁻¹)
            - 0 - (0 : ℝ) * cnPlus s Φ
          ≤ kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
        rw [hq4]; linarith [hkP]
      have hm : (0 : ℝ) ^ 2 ≤ ((((0 + 1 : ℕ) : ℝ)) + 1) ^ 2 := by norm_num
      have heta : -((1 / 2) * (0 : ℝ) * (g0w0Mass (v := v) h) * (0 : ℝ) ^ 2 * (s ^ 3)⁻¹)
          ≥ -(μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v)) := by
        have hG : 0 ≤ kinPGamma R0 s K_B μ v := by
          unfold kinPGamma
          refine add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3) ?_)
          exact Real.rpow_nonneg (by positivity) (1 / 2)
        have hnn' : 0 ≤ μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v) := by
          have h1 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
          have h2 : (0 : ℝ) ≤ s ^ 3 := by positivity
          exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 hav') h2) hG)
            (mul_nonneg hμnn hav')
        linarith [hnn']
      have hbr : (0 : ℝ) ≤ (88 * π + 39) * (a v) * μ := by
        have h := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 88 * π + 39) hav') hμnn
        linarith [h]
      have hEq : (0 : ℝ) ≤ kinPBogErr Ct 0 s v := by
        unfold kinPBogErr
        have hc := d1C_nonneg Ct
        positivity
      exact cS1_pos_chain (ηq := 0) (m := 0) (Bq := 0) (Eq := 0)
        h hs hμ hR0 hKB hv_nonneg hvrad hv_memL1 hv_supp hRs hμs hc0 hΦc hnorm hwin hSc1
        hD hbox hcorr hbr heta hQ hEq hm
  · have hz : cS1 s Φ = 0 := le_antisymm (le_of_not_gt hSc1) cS1_nonneg
    have h1 := cnPlus_add_cS1 (N := n + 1) hs hΦc.continuous
    rw [hnorm, mul_one] at h1
    have hcP : cnPlus s Φ = (((n + 1 : ℕ) : ℝ)) := by linarith [h1, hz]
    have hqar := qZeroArith (N := n + 1) (s := s) (μ := μ) (a := a v) (q := chiSup ^ 2)
      hs hμ hav' (sq_nonneg chiSup) hwin hchi
    have hqL := qLHSword_chosen_lower (N := n + 1) (s := s) (R := R0) (μ := μ) (v := v)
      hR0 hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμnn hΦc
    rw [hnorm, mul_one] at hqL
    have hsbox : sboxC (n + 1) μ v = μ * (((n + 1 : ℕ) : ℝ)) * (16 * π * chiSup ^ 2 * (a v)) := by
      rw [sboxC]; ring
    rw [hsbox] at hqL
    have hkP : 0 ≤ kinPWord s c0 Φ := kinPWord_nonneg hs Φ
    have hG : 0 ≤ kinPGamma R0 s K_B μ v := by
      unfold kinPGamma
      refine add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3) ?_)
      exact Real.rpow_nonneg (by positivity) (1 / 2)
    have hNnn : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
    have hX : 0 ≤ μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v := by
      have h1 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
      have h2 : (0 : ℝ) ≤ s ^ 3 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 hav') h2) hG
    have hY : 0 ≤ μ * (a v) := mul_nonneg hμnn hav'
    have hcN : (((n + 1 : ℕ) : ℝ)) / (36 * s ^ 2) ≤ cgap * (((n + 1 : ℕ) : ℝ)) := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [one_div] using hcgap) hNnn
    have hCpos : (0 : ℝ) ≤ 272 * π + 40 := by positivity
    rw [kinPEnergy, hcP]
    have hsub : (1 / 4 * (((n + 1 : ℕ) : ℝ) / s ^ 3 - μ) ^ 2 - 1 / 2 * μ ^ 2) * (8 * π * (a v) * s ^ 3)
        ≤ cgap * (((n + 1 : ℕ) : ℝ)) + kinPWord s c0 Φ
          + qLHSword (N := n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
      nlinarith [hqar, hqL, hkP, hcN]
    have hT : (0 : ℝ) ≤ (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v
        + (272 * π + 40) * μ * (a v) := by
      nlinarith [hCpos, hX, hY]
    linarith [hsub, hT]


end Work.SmallBoxA0
