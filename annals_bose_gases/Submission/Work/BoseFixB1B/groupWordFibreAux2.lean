import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.twoArmFAltDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.groupWordFibreAux2` — the degenerate-side lemmas

The lemmas handling the case in which the sliding box side `L = PBℓ v μ` is nonpositive (which
happens exactly when `μ · a v ≤ 0`, the diluteness `μ(a v)³` being nonpositive: `sideAt` is
`K_ℓ(μa)^{-1/2}` and `(μa)^{-1/2}` is `cos(−π/2) = 0` for a negative base and `0` for the base
`0`).  In that regime the corpus boxes `abox K L` (`K ≥ 1`) and `dlBox L d u` are null, so both
sides of the fibre factorisation vanish identically.

* `abox_measure_zero_of_nonpos` — `abox K L` is null for `L ≤ 0`, `K ≥ 1`;
* `cnPlusBoxInd_eq_zero_of_card_zero_or_nonpos`,
  `tBdiagFormInd_eq_zero_of_card_zero_or_nonpos`,
  `qLHSword_eq_zero_of_card_zero_or_nonpos` — the three pieces of the sliding word vanish for
  `K = 0` (empty sums / vanishing density) and for `L ≤ 0`, `1 ≤ K` (null box);
* `abox_psi_sq_qLHSdenS_eq_zero_of_nonpos` — the potential integrand of the group word vanishes
  in the same regime;
* `rpow_neg_half_eq_zero_of_nonpos`, `PBd_pos_of_PBℓ_pos` — `0 < PBℓ v μ` forces the diluteness
  `μ (a v)³` to be positive, hence `0 < PBd v μ` (so that the generic, positive-side lemmas apply
  whenever the box side is positive).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.UBBInputs8

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The degenerate box is null -/

/-- For a nonpositive box side `L ≤ 0` and `K ≥ 1` the corpus box `abox K L` is a null set
(`acube L` is empty for `L < 0` and `{0}` for `L = 0`). -/
lemma abox_measure_zero_of_nonpos {K : ℕ} (hK : 1 ≤ K) {L : ℝ} (hL : L ≤ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X K))
      (Submission.BoseGases.abox K L) = 0 := by
  rcases lt_or_eq_of_le hL with h | h
  · have hempty : Submission.BoseGases.abox K L = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hmem : x ⟨0, hK⟩ ∈ Submission.BoseGases.acube L := hx _
      have hcoord := (Submission.BoseGases.mem_acube_iff L (x ⟨0, hK⟩)).mp hmem 0
      simp only [Set.mem_Icc] at hcoord
      linarith [hcoord.1, hcoord.2]
    rw [hempty, measure_empty]
  · subst h
    rw [Submission.BoseGases.abox_volume K 0 le_rfl]
    have hz : (((0 : ℝ) ^ 3) ^ K) = 0 := by
      rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow (by omega : K ≠ 0)]
    rw [hz, ENNReal.ofReal_zero]

/-! ## 2. The three pieces of the sliding word vanish in the degenerate regime -/

/-- The box excited count vanishes when the particle number is `0` (empty slot sum) or when
`L ≤ 0` and the particle number is at least one (null box). -/
lemma cnPlusBoxInd_eq_zero_of_card_zero_or_nonpos {K : ℕ} {L : ℝ}
    (h : K = 0 ∨ (1 ≤ K ∧ L ≤ 0)) (A : Set E3) (volA : ℝ)
    (Ψ : Submission.BoseGases.X K → ℝ) :
    Work.UBBInputs8.cnPlusBoxInd L A volA Ψ = 0 := by
  rcases h with rfl | ⟨hK, hL⟩
  · rw [Work.UBBInputs8.cnPlusBoxInd]
    simp
  · rw [Work.UBBInputs8.cnPlusBoxInd]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact MeasureTheory.setIntegral_measure_zero _
      (abox_measure_zero_of_nonpos hK hL)

/-- The `p`-diagonal kinetic form vanishes in the same regime: for `K ≥ 1` the inner box integral
is over a null set (so the `p`-integrand is `0`), and for `K = 0` the slot sum is empty. -/
lemma tBdiagFormInd_eq_zero_of_card_zero_or_nonpos {K : ℕ} {L : ℝ}
    (h : K = 0 ∨ (1 ≤ K ∧ L ≤ 0)) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ) (F : ℝ → ℝ)
    (Ψ : Submission.BoseGases.X K → ℝ) :
    Work.UBBInputs8.tBdiagFormInd L A volA χ F Ψ = 0 := by
  rcases h with rfl | ⟨hK, hL⟩
  · rw [Work.UBBInputs8.tBdiagFormInd]
    simp
  · rw [Work.UBBInputs8.tBdiagFormInd]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hzero : ∀ p : E3, (∫ x in Submission.BoseGases.abox K L,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) = 0 :=
      fun p => MeasureTheory.setIntegral_measure_zero _
        (abox_measure_zero_of_nonpos hK hL)
    have hfun : (fun p : E3 => F ‖p‖ * ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox K L,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2))
        = fun _ : E3 => 0 := by
      funext p
      rw [hzero p]
      ring
    rw [hfun, MeasureTheory.integral_zero, mul_zero]

/-- The potential word vanishes in the same regime: for `K ≥ 1` the integral runs over a null box,
and for `K = 0` the diagonal density `qLHSden` vanishes identically (both sums are empty). -/
lemma qLHSword_eq_zero_of_card_zero_or_nonpos {K : ℕ} {L : ℝ}
    (h : K = 0 ∨ (1 ≤ K ∧ L ≤ 0)) (μ : ℝ) (w w1 : E3 → E3 → ℝ)
    (Ψ : Submission.BoseGases.X K → ℝ) :
    Submission.BoseGases.qLHSword (N := K) L μ w w1 Ψ = 0 := by
  rcases h with rfl | ⟨hK, hL⟩
  · rw [Submission.BoseGases.qLHSword_eq_integral_qLHSden]
    have hfun : (fun x : Submission.BoseGases.X 0 => (Ψ x) ^ 2 *
        Submission.BoseGases.qLHSden 0 L μ w w1 x) = fun _ => 0 := by
      funext x
      have hq : Submission.BoseGases.qLHSden 0 L μ w w1 x = 0 := by
        rw [Submission.BoseGases.qLHSden,
          Finset.sum_eq_zero (fun i _ => Fin.elim0 i),
          Finset.sum_eq_zero (fun p _ => Fin.elim0 p.1)]
        ring
      rw [hq, mul_zero]
    rw [hfun, MeasureTheory.integral_zero]
  · rw [Submission.BoseGases.qLHSword_eq_integral_qLHSden]
    exact MeasureTheory.setIntegral_measure_zero _
      (abox_measure_zero_of_nonpos hK hL)

/-- The potential integrand of the group word vanishes for `L ≤ 0`: for `N ≥ 1` the integral runs
over the null box `abox N L`, and for `N = 0` the slot set `S : Finset (Fin 0)` is empty, so the
restricted density `qLHSdenS` vanishes identically. -/
lemma abox_psi_sq_qLHSdenS_eq_zero_of_nonpos {N : ℕ} {L : ℝ} (hL : L ≤ 0) (μ : ℝ)
    (w w1 : E3 → E3 → ℝ) (S : Finset (Fin N)) (Ψ : Submission.BoseGases.X N → ℝ) :
    (∫ x in Submission.BoseGases.abox N L,
        (Ψ x) ^ 2 * qLHSdenS L μ w w1 S x) = 0 := by
  by_cases hN : N = 0
  · subst hN
    have hfun : (fun x : Submission.BoseGases.X 0 => (Ψ x) ^ 2 *
        qLHSdenS L μ w w1 S x) = fun _ => 0 := by
      funext x
      have hq : qLHSdenS L μ w w1 S x = 0 := by
        rw [qLHSdenS,
          Finset.sum_eq_zero (fun i _ => Fin.elim0 i),
          Finset.sum_eq_zero (fun p _ => Fin.elim0 p.1)]
        ring
      rw [hq, mul_zero]
    rw [hfun, MeasureTheory.integral_zero]
  · have hK : 1 ≤ N := by omega
    exact MeasureTheory.setIntegral_measure_zero _
      (abox_measure_zero_of_nonpos hK hL)

/-- **The sliding word vanishes for `K = 0` or `L ≤ 0`**, at arbitrary state `Φ`.  The three
pieces are the three lemmas above. -/
lemma fibreWord_eq_zero_of_card_zero_or_nonpos {K : ℕ} {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (μ L d ε c : ℝ) (M : ℕ) (u : E3) (hK : K = 0 ∨ (1 ≤ K ∧ L ≤ 0))
    (Φ : Submission.BoseGases.X K → ℝ) :
    Work.SlotWord.fibreWord h M K L d ε c μ u Φ = 0 := by
  rw [Work.SlotWord.fibreWord, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
    Work.UBBInputs8.tBwordKinInd, Work.SmallBoxSliding.qLHSwordB]
  rw [cnPlusBoxInd_eq_zero_of_card_zero_or_nonpos hK _ _ _,
    tBdiagFormInd_eq_zero_of_card_zero_or_nonpos hK _ _ _ _ _,
    qLHSword_eq_zero_of_card_zero_or_nonpos hK _ _ _ _]
  ring

/-- **The (unfolded) group word vanishes for `L ≤ 0`**: each of its three pieces is either an
integral over the null box `abox N L` (the two slot sums, whose index `i : Fin N` forces `N ≥ 1`)
or the potential integral of `abox_psi_sq_qLHSdenS_eq_zero_of_nonpos`. -/
lemma groupWord_unfolded_eq_zero_of_nonpos {N : ℕ} {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (μ : ℝ) (u : E3) (S : Finset (Fin N)) {Ψ : Submission.BoseGases.X N → ℝ}
    (L d ε c : ℝ) (hL : L ≤ 0) (M : ℕ) :
    (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε *
        (∑ i ∈ S, ∫ x in Submission.BoseGases.abox N L,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i Ψ x) ^ 2)
      + (∑ i ∈ S, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N L,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i Ψ) i x‖ ^ 2))
      + ∫ x in Submission.BoseGases.abox N L, (Ψ x) ^ 2 *
          qLHSdenS L μ (Submission.BoseGases.wSmallPair M L d u v)
            (Submission.BoseGases.wSmall1Pair h M L d u) S x) = 0 := by
  have h1 : (∑ i ∈ S, ∫ x in Submission.BoseGases.abox N L,
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i Ψ x) ^ 2) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact MeasureTheory.setIntegral_measure_zero _
      (abox_measure_zero_of_nonpos (by have := i.isLt; omega) hL)
  have h2 : (∑ i ∈ S, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
      Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N L,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i Ψ) i x‖ ^ 2)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hK : 1 ≤ N := by have := i.isLt; omega
    have hzero : ∀ p : E3, (∫ x in Submission.BoseGases.abox N L,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i Ψ) i x‖ ^ 2) = 0 :=
      fun p => MeasureTheory.setIntegral_measure_zero _
        (abox_measure_zero_of_nonpos hK hL)
    have hfun : (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N L,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i Ψ) i x‖ ^ 2)) = fun _ : E3 => 0 := by
      funext p
      rw [hzero p]
      ring
    rw [hfun]
    simp
  have h3 : (∫ x in Submission.BoseGases.abox N L, (Ψ x) ^ 2 *
      qLHSdenS L μ (Submission.BoseGases.wSmallPair M L d u v)
        (Submission.BoseGases.wSmall1Pair h M L d u) S x) = 0 :=
    abox_psi_sq_qLHSdenS_eq_zero_of_nonpos hL μ _ _ S Ψ
  rw [h1, h2, h3]
  ring

/-! ## 3. The positivity of `PBℓ` forces the diluteness to be positive -/

/-- `x ^ (−1/2) = 0` for `x ≤ 0` (for `x < 0` by the Libm-free definition of `Real.rpow` at a
negative base, `cos(−π/2) = 0`; for `x = 0` by `Real.zero_rpow`). -/
lemma rpow_neg_half_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    x ^ (-(1 / 2) : ℝ) = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.rpow_def_of_neg h]
    have harg : (-(1 / 2) : ℝ) * Real.pi = -(Real.pi / 2) := by ring
    rw [harg, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · subst h
    rw [Real.zero_rpow (by norm_num : (-(1 / 2) : ℝ) ≠ 0)]

/-- **The positivity of the box side forces the diluteness to be positive.**  If
`0 < PBℓ v μ = K_ℓ (μ · a v)^{−1/2}`, then `μ · a v > 0` (the half-integer power vanishes on the
nonpositive half-line), hence the diluteness `μ (a v)³ = (μ · a v)(a v)²` is positive and so is
`PBd v μ = (μ (a v)³)^{6/323}`. -/
lemma PBd_pos_of_PBℓ_pos {v : E3 → ℝ} {μ : ℝ} (h : 0 < PBℓ v μ) : 0 < PBd v μ := by
  have hside : PBℓ v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl *
      (μ * _root_.BoseGases.a v) ^ (-(1 / 2) : ℝ) :=
    Work.BoseFixB1.sideAt_eq μ (_root_.BoseGases.a v)
  have hy : 0 < μ * _root_.BoseGases.a v := by
    by_contra hc
    push_neg at hc
    rw [hside, rpow_neg_half_eq_zero_of_nonpos hc, mul_zero] at h
    exact lt_irrefl 0 h
  have hane : _root_.BoseGases.a v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hy
    exact lt_irrefl 0 hy
  have hd_eq : PBd v μ = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6 := by
    show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = _
    rw [Work.BoseFixB1.paramsAt_eq_fsParams]
    rfl
  rw [hd_eq]
  refine Work.BoseBox.fsXp_pos ?_
  have hrewrite : μ * (_root_.BoseGases.a v) ^ 3
      = (μ * _root_.BoseGases.a v) * (_root_.BoseGases.a v) ^ 2 := by ring
  rw [hrewrite]
  exact mul_pos hy (sq_pos_of_ne_zero hane)

end Work.BoseFixB1B
