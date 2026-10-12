import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.AprioriCount.wordB_eq_kin_sub_potMass_add_pair
import Submission.Work.BoseBoxFock.bf3a
import Submission.Work.BoseFixB1B.slidingWindowComparisonWeighted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kinFormB_le_of_isLowB` — the a-priori kinetic bound of a low box state

The target (FS `eq:aprioriPsi` ⟹ FS's a-priori kinetic bound): a low box state at FS's parameters
has `⟨kin⟩ ≲ (a v) μ² ℓ³ ‖Φ‖²`.

## The route (all inputs are PROVED corpus lemmas)

`IsLowB v h J μ n Φ` says

    wordB ≤ ℓ³·Theta (a v) J μ·normB ,      ℓ = sideAt μ (a v),  Theta A J ρ = −4πρ²A(1 − J√(ρA³)) .

1. **The low threshold is negative**: for `J ≤ K_B³` and `μ(a v)³ ≤ 1/2` we have
   `K_B³ = (μa³)^{−18/323}` (FS `eq:Xchoice`) so `J√(μa³) ≤ (μa³)^{287/646} < 1`, whence
   `Theta (a v) J μ < 0` (`theta_neg_of_KB_aux` below).
2. **The box-word splitting** (`Work.AprioriCount.wordB_eq_kin_sub_potMass_add_pair`):
   `wordB = kinFormB − μ·potMass + pairPartB`, so with `pairPartB ≥ 0`
   (`Work.BoseFixB1B.pairPartB_nonneg`) and `wordB ≤ ℓ³Θ·normB ≤ 0`,
   `kinFormB ≤ μ·potMass`.
3. **The one-body mass bound** (`Work.BoseFixB1B.chemMassLe`, the `hMupper` row):
   `μ·potMass ≤ 16π·chiSup²·(a v)·μ·n·normB`, and `n ≤ 2μℓ³` closes it:
   `kinFormB ≤ 32π·chiSup²·(a v)·μ²·ℓ³·normB`.

So `ε₀` is `min ε_R (min ε_M (1/2))` (the range threshold of `exists_adm_chiR0_ge`, the mass
threshold of `chemMassLe`, and the diluteness cap `1/2` that makes the exponent arithmetic strict),
and `C = 32π·chiSup²`.

Note the target's `hv`, `hv1`, `hvrad` are used only through the `chemMassLe` supply; the identity
(2) needs no sign hypothesis on `v`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- The exponent arithmetic of this file: the exact closed form of FS's `K_B³`. -/
lemma theta_neg_of_KB_aux_KB_cube_eq {μ a : ℝ} (ht : 0 ≤ μ * a ^ 3) :
    (Work.BoseBox.paramsAt μ a).KB ^ 3 = (μ * a ^ 3) ^ (-(18 / 323) : ℝ) := by
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  rw [Work.BoseBox.fsXp_pow ht (-(6 : ℝ)) 3, Work.BoseBox.fsXp]
  norm_num

/-- **`J√(μa³) < 1` for `J ≤ K_B³` in the dilute regime `μa³ ≤ 1/2`** (FS `eq:Xchoice`:
`K_B = X^{−6}`, `X = (μa³)^{1/323}`). -/
lemma theta_neg_of_KB_aux_J_mul_sqrt_lt_one {a μ J : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    (ht : μ * a ^ 3 ≤ 1 / 2) (hJ : J ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3) :
    J * Real.sqrt (μ * a ^ 3) < 1 := by
  have htpos : 0 < μ * a ^ 3 := by positivity
  have htlt : μ * a ^ 3 < 1 := by linarith
  rw [theta_neg_of_KB_aux_KB_cube_eq htpos.le] at hJ
  rw [Real.sqrt_eq_rpow]
  have h1 : J * (μ * a ^ 3) ^ (1 / 2 : ℝ)
      ≤ (μ * a ^ 3) ^ (-(18 / 323) : ℝ) * (μ * a ^ 3) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg htpos.le _)
  have h2 : (μ * a ^ 3) ^ (-(18 / 323) : ℝ) * (μ * a ^ 3) ^ (1 / 2 : ℝ)
      = (μ * a ^ 3) ^ (287 / 646 : ℝ) := by
    rw [← Real.rpow_add htpos]
    norm_num
  rw [h2] at h1
  exact lt_of_le_of_lt h1 (Real.rpow_lt_one htpos.le htlt (by norm_num))

/-- **The low-state threshold is strictly negative**: `Theta a J μ < 0` for `0 < a`, `0 < μ`,
`μa³ ≤ 1/2` and `J ≤ K_B³`. -/
lemma theta_neg_of_KB_aux {a μ J : ℝ} (ha : 0 < a) (hμ : 0 < μ) (ht : μ * a ^ 3 ≤ 1 / 2)
    (hJ : J ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3) : Work.UBB.Theta a J μ < 0 := by
  have hJsqrt := theta_neg_of_KB_aux_J_mul_sqrt_lt_one ha hμ ht hJ
  rw [Work.UBB.Theta]
  have hcoef : 0 < 4 * Real.pi * μ ^ 2 * a := by positivity
  have hbr : 0 < 1 - J * Real.sqrt (μ * a ^ 3) := by linarith
  nlinarith [mul_pos hcoef hbr]

theorem kinFormB_le_of_isLowB (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ (J : ℝ) (μ : ℝ), Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ C * (BoseGases.a v) * μ ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
                * Work.BoseBoxFix.normB v μ n Φ := by
  obtain ⟨εR, hεRpos, hεR⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  obtain ⟨εM, hεMpos, hεM⟩ := Work.BoseFixB1B.chemMassLe (v := v) h hv hvrad hR hv_supp hav
  refine ⟨min εR (min εM (1 / 2)), 32 * Real.pi * Submission.BoseGases.chiSup ^ 2, ?_, ?_, ?_⟩
  · exact lt_min hεRpos (lt_min hεMpos (by norm_num))
  · have hsq : (0 : ℝ) ≤ Submission.BoseGases.chiSup ^ 2 := sq_nonneg _
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [hsq, hpi]
  · intro J μ hAdm hJ n Φ hnc hnorm hL
    have hμ : 0 < μ := hAdm.1
    have ha0 : 0 < _root_.BoseGases.a v := hav
    have ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 / 2 :=
      le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hAdmR : Work.BoseBoxFix.Adm v εR μ :=
      ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
    have hAdmM : Work.BoseBoxFix.Adm v εM μ :=
      ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _)), hAdm.2.2⟩
    have hRℓ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
      hεR μ hAdmR
    have hΘ : Work.UBB.Theta (_root_.BoseGases.a v) J μ < 0 :=
      theta_neg_of_KB_aux hav hμ ht hJ
    -- the box-word splitting at the target's vocabulary
    have hsplit := Work.AprioriCount.wordB_eq_kin_sub_potMass_add_pair (v := v) h hv1 hR hv_supp
        (μ := μ) hRℓ Φ
    have hpair : 0 ≤ Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ) := Work.BoseFixB1B.pairPartB_nonneg hv _ _
    -- `potMass` in the currency of the mass bound
    have hpot : Work.AprioriCount.potMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v h
        (Φ : Submission.BoseGases.X n → ℝ)
        = ∫ (x : Submission.BoseGases.X n) in Submission.BoseGases.abox n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
              ∑ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin 3)),
                Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.g0 v h) 0 (x i) y := by
      simp only [Work.AprioriCount.potMass, Work.BoseBox.potBr]
    have hmass : μ * Work.AprioriCount.potMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v h
        (Φ : Submission.BoseGases.X n → ℝ)
        ≤ 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ * (n : ℝ)
          * Work.BoseBoxFix.normB v μ n Φ := by
      rw [hpot]
      exact hεM μ hAdmM n Φ
    -- `n ≤ 2 μ ℓ³` in the constant
    have hcoef : 0 ≤ 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16)
        Real.pi_pos.le) (sq_nonneg Submission.BoseGases.chiSup)) ha0.le) hμ.le
    have hstep : 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ * (n : ℝ)
          * Work.BoseBoxFix.normB v μ n Φ
        ≤ 32 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ ^ 2
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 * Work.BoseBoxFix.normB v μ n Φ := by
      have h1 : 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ * (n : ℝ)
          ≤ 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ
            * (2 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) :=
        mul_le_mul_of_nonneg_left hnc hcoef
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hnorm)
      calc 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ * (n : ℝ)
            * Work.BoseBoxFix.normB v μ n Φ
          = (16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ * (n : ℝ))
            * Work.BoseBoxFix.normB v μ n Φ := rfl
        _ ≤ (16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ
              * (2 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3))
            * Work.BoseBoxFix.normB v μ n Φ := h2
        _ = 32 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ ^ 2
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 * Work.BoseBoxFix.normB v μ n Φ := by
            ring
    -- the low condition is a negative bound
    have hℓ3 : 0 ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 :=
      pow_nonneg (le_of_lt (Work.BoseFixB1.adm_ell_pos hAdm)) 3
    have hword : Work.BoseBoxFix.wordB v h μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      have hh := hL
      unfold Work.BoseBoxFix.IsLowB at hh
      exact hh
    have hneg : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hℓ3 hΘ.le) (le_of_lt hnorm)
    linarith [hsplit, hpair, hmass, hstep, hword, hneg]

end Work.BoseBoxFock
