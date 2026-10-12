import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.flatArm37Defs
import Submission.Work.BoseB1Cube.flatArm37LowerAux
import Submission.Work.BoseB1Cube.rowOneArith
import Submission.Work.BoseFixB1B.bandPairLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.flatArm37RowOneGoodLower`

Row 1 of the flat arm of the small-window rows (**`Work.BoseB1Cube.FlatArm37`**) on the *good*
region `12 ≤ μ|B(u)|`.  This is the **holder-free** statement of
`Work.BoseB1Cube.flatArm37RowOneGood` (`Submission/Work/BoseB1Cube/flatArm37RowOneGood.lean`):
same hypotheses, same conclusion, but its import cone avoids `cubeFlatArm_holds` (and hence
avoids `nominalPerBoxRow → nomRowSqWindowRow → cubeSmallNArb12ExHolds`, the holder that must be
able to import *this* module).  The one declaration of `cubeFlatArm_holds` used by the original
proof, the 25-line `Work.BoseB1Cube.pairCountPayment`, is re-supplied as
`Work.BoseB1Cube.pairCountPaymentLower` in `flatArm37LowerAux`, so the original proof transcribes
verbatim.

The helper lemmas below are marked `private` so that this module and
`flatArm37RowOneGood.lean` may be imported together.

Contents (all of them the original proof, unchanged):

* `sqrt_mul_le_add_div` — Young for `√(Qθ)`;
* `boxM1_eq_w1MassB`, `boxM2_g2_le_v_box`, `w1MassB_le_boxM2_v` — the chain `W = M₁ ≤ M₂`;
* `rowOneLedger`, `rowOneFinal`, `rowOneMain` — the pure-real ledger, the `W/U²` bookkeeping and
  the count split/arithmetic;
* `flatArm37RowOneGoodLower` — the assembly, discharging the ledger's hypotheses from the corpus.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. Young's inequality for the `√(Qθ)` cross term -/

/-- **Young for `√(Qθ)`**: `√(Qθ) ≤ ηQ + θ/(4η)` for `η > 0` and `Q, θ ≥ 0` (the sharp
two-variable AM–GM, with the free parameter `η` that makes both coefficients arbitrarily small at
the cost of the other). -/
private lemma sqrt_mul_le_add_div {Q θ η : ℝ} (hQ : 0 ≤ Q) (hθ : 0 ≤ θ) (hη : 0 < η) :
    Real.sqrt (Q * θ) ≤ η * Q + θ / (4 * η) := by
  rw [Real.sqrt_mul hQ]
  have h1 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ
  have h2 : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ
  have h4 : 0 < 4 * η := by linarith
  have key : (Real.sqrt Q * Real.sqrt θ) * (4 * η) ≤ (η * Q + θ / (4 * η)) * (4 * η) := by
    have hh : (η * Q + θ / (4 * η)) * (4 * η) = 4 * η ^ 2 * Q + θ := by field_simp
    rw [hh]
    nlinarith [sq_nonneg (2 * η * Real.sqrt Q - Real.sqrt θ)]
  exact le_of_mul_le_mul_right key h4

/-! ## 2. The box mass `M₁` of the one-body kernel is `W = PBW` -/

/-- **`boxM1` over the sliding box is `w1MassB`.**  Both sides are the double integral of the
localised one-body kernel `wSmall1Pair`; the sliding box `dlBox ℓ d u` supports the cutoff in both
slots (`wSmall1Pair_eq_zero_of_notMem_left/right`), so the full-space double integral
`w1MassB = ∫_x ∫_y wSmall1Pair x y` collapses onto `boxM1 = ∫_{B} ∫_{acube ℓ} wSmall1Pair`. -/
private theorem boxM1_eq_w1MassB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      = Work.BoseFixB1.w1MassB h M ℓ d u := by
  have h1 : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
    intro x
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    exact Work.BoseFixB1S.wSmall1Pair_eq_zero_of_notMem_right hM hℓ hd u x
      (fun hyB => hy (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hyB))
  simp only [Work.BoseFixB1S.boxM1, Submission.BoseGases.w1Fibre]
  simp only [h1]
  exact Work.BoseFixB1S.fibreMass_eq_w1MassB hM hℓ hd u

/-! ## 3. The `g₂ → v` monotonicity of the pair mass -/

/-- **`boxM2` of the `g₂`-kernel is at most `boxM2` of the `v`-kernel** (pointwise
`wSmallPair g₂ ≤ wSmallPair v` on the nonnegative cutoffs, integrated over the box × box). -/
private theorem boxM2_g2_le_v_box {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v) := by
  rw [Work.BoseFixB1S.boxM2, Work.BoseFixB1S.boxM2]
  have hA : Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u
      ⊆ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ :=
    Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u) :=
    (Work.BoseFixB1.integrableOn_wSmallPair_cube
      (Submission.BoseGases.g2_integrable hR hv hvrad hv_supp h)
      (fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR16 hRχ u
      ).mono_set hA
  have hIntv : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u) :=
    (Work.BoseFixB1.integrableOn_wSmallPair_cube
      (MeasureTheory.memLp_one_iff_integrable.mp hv1)
      (fun z hz => by
        by_contra hne
        have hz1 : z ∈ tsupport v := subset_tsupport v (Function.mem_support.mpr hne)
        have hz2 : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := hv_supp hz1
        rw [Metric.mem_ball, dist_zero_right] at hz2
        exact absurd hz2 (not_lt.mpr hz)) hM hℓ hd hR16 hRχ u).mono_set hA
  exact MeasureTheory.setIntegral_mono_ae hInt2 hIntv
    (Filter.Eventually.of_forall
      (fun p => Work.BoseFixB1B.wSmallPair_g2_le_v h hv M ℓ d u p.1 p.2))

/-! ## 4. `PBW ≤ M₂`: the one-body mass is dominated by the pair mass -/

/-- **`w1MassB ≤ boxM2 (wSmallPair v)`.**  The chain is `W = boxM1 ≤ boxM2 g₂ ≤ boxM2 v`:
`boxM1_eq_w1MassB`, the PROVED `Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1` (the `g₂` pair
mass dominates the `g₀` fibre mass) and `boxM2_g2_le_v_box`.  This is the constant-`1` version of
`Work.BoseFixB1S.w1MassB_le_const_mul_boxM2` (whose proof delivers the constant `1` but whose
*statement* only exposes an existential constant, so it cannot be consumed downstream). -/
private theorem w1MassB_le_boxM2_v {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.w1MassB h M ℓ d u
      ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v) := by
  have h1 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Submission.BoseGases.wSmall1Pair h M ℓ d u) = Work.BoseFixB1.w1MassB h M ℓ d u :=
    boxM1_eq_w1MassB hM hℓ hd u
  have h2 := Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1 (v := v) (R := R) hv_supp hR hv
    hvrad hv1 h hav hM hℓ hd hR16 hRχ u
  have h3 := boxM2_g2_le_v_box (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hM hℓ hd
    hR16 hRχ u
  rw [← h1]
  linarith

/-! ## 5. The pure-real ledger -/

/-- **The flat-arm row-1 ledger (pure real).**  From the pair-row domination `B₀ ≤ P`, the manifest
fibre bound `F ≤ θ + C·a·(√(Qθ) + Q)` (`θ = (M₁/U)S`), the Young bound on `μCa√(Qθ)`, the gap
payment `(2500 C²a + C)·μa·Q ≤ bG·Q` and the count pairing `bG·Q + P − μF ≤ sbW`, the word
dominates `(M₂/U²)·S·br` with `br = (10/37)(S/J − 1) − (1 + 1/10000)μU`. -/
private lemma rowOneLedger {S Q J U M1 M2 P F bG sbW Cm a μ : ℝ}
    (hU : 0 < U) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hμ : 0 ≤ μ) (hCm : 0 ≤ Cm)
    (hθ : (M1 / U) * S ≤ (M2 / U) * S)
    (hG : (2500 * Cm ^ 2 * a + Cm) * μ * a * Q ≤ bG * Q)
    (hP0 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) ≤ P)
    (hF0 : F ≤ (M1 / U) * S + Cm * a * (Real.sqrt (Q * ((M1 / U) * S)) + Q))
    (hY : μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      ≤ μ * (1 / 10000) * ((M1 / U) * S) + μ * (2500 * Cm ^ 2 * a ^ 2) * Q)
    (hbed : bG * Q + P - μ * F ≤ sbW) :
    (M2 / U ^ 2) * (S * ((10 / 37) * (S / J - 1) - (1 + 1 / 10000) * (μ * U))) ≤ sbW := by
  have hF1 : μ * F ≤ μ * ((M1 / U) * S) + μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      + μ * Cm * a * Q := by
    have h1 : μ * F ≤ μ * ((M1 / U) * S + Cm * a * (Real.sqrt (Q * ((M1 / U) * S)) + Q)) :=
      mul_le_mul_of_nonneg_left hF0 hμ
    nlinarith [h1]
  have hQpay : μ * ((M1 / U) * S) + μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      + μ * Cm * a * Q ≤ μ * (1 + 1 / 10000) * ((M1 / U) * S) + bG * Q := by
    nlinarith [hY, hG, hQ, hμ, ha, hCm]
  have hθ' : μ * (1 + 1 / 10000) * ((M1 / U) * S)
      ≤ μ * (1 + 1 / 10000) * ((M2 / U) * S) :=
    mul_le_mul_of_nonneg_left hθ (by positivity)
  have key : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) - μ * (1 + 1 / 10000) * ((M2 / U) * S)
      ≤ sbW := by
    have h1 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) - μ * (1 + 1 / 10000) * ((M2 / U) * S)
        ≤ (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1))
          - μ * (1 + 1 / 10000) * ((M1 / U) * S) := by linarith [hθ']
    have h2 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1))
        - μ * (1 + 1 / 10000) * ((M1 / U) * S) ≤ sbW := by
      nlinarith [hbed, hP0, hF1, hQpay]
    linarith [h1, h2]
  have hE : (M2 / U ^ 2) * (S * ((10 / 37) * (S / J - 1) - (1 + 1 / 10000) * (μ * U)))
      = (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1))
        - μ * (1 + 1 / 10000) * ((M2 / U) * S) := by
    rw [mul_assoc]
    field_simp
    try ring
  linarith [key, hE.le, hE.ge]

/-- **The final bookkeeping (pure real).**  `(1/18)μ(n'/U)WJ = (W/U²)·(J·(μU n'/18))` and both
factors of the right-hand side are monotone in the right direction (`W ≤ M₂`, `S·br ≥ 0`). -/
private lemma rowOneFinal {S J U W M2 br μ n' : ℝ}
    (hU : 0 < U) (hJ : 0 ≤ J) (hS : 0 ≤ S) (hW : 0 ≤ W) (hWM2 : W ≤ M2)
    (hbr : 0 ≤ br) (hSbr : J * (μ * U * n' / 18) ≤ S * br) :
    (1 / 18) * μ * (n' / U) * W * J ≤ (M2 / U ^ 2) * (S * br) := by
  have hWU : 0 ≤ W / U ^ 2 := div_nonneg hW (by positivity)
  have hSb : 0 ≤ S * br := mul_nonneg hS hbr
  have h1 : (1 / 18) * μ * (n' / U) * W * J = (W / U ^ 2) * (J * (μ * U * n' / 18)) := by
    field_simp
    try ring
  have h2 : (W / U ^ 2) * (J * (μ * U * n' / 18)) ≤ (W / U ^ 2) * (S * br) :=
    mul_le_mul_of_nonneg_left hSbr hWU
  have h3 : (W / U ^ 2) * (S * br) ≤ (M2 / U ^ 2) * (S * br) := by
    have hdiv := div_le_div_of_nonneg_right hWM2 (by positivity : (0 : ℝ) ≤ U ^ 2)
    exact mul_le_mul_of_nonneg_right hdiv hSb
  linarith [h1.le, h1.ge, h2, h3]

/-! ## 6. The count split and the arithmetic -/

/-- **The row-1 core.**  The count split `S + Q = n'J` with `Q < c₀J` gives `S/J ≥ n' − c₀`, so
`Work.BoseB1Cube.rowOneArith` controls the bracket; the ledger and the bookkeeping then close. -/
private theorem rowOneMain {S Q J U W M1 M2 P F bG sbW br : ℝ} {Cm a μ n' c₀ : ℝ}
    (hU : 0 < U) (hJ : 0 < J) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hμ : 0 ≤ μ)
    (hCm : 0 ≤ Cm) (hW : 0 ≤ W) (hM1W : M1 = W) (hWM2 : W ≤ M2)
    (hG : (2500 * Cm ^ 2 * a + Cm) * μ * a * Q ≤ bG * Q)
    (hP0 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) ≤ P)
    (hF0 : F ≤ (M1 / U) * S + Cm * a * (Real.sqrt (Q * ((M1 / U) * S)) + Q))
    (hY : μ * Cm * a * Real.sqrt (Q * ((M1 / U) * S))
      ≤ μ * (1 / 10000) * ((M1 / U) * S) + μ * (2500 * Cm ^ 2 * a ^ 2) * Q)
    (hbed : bG * Q + P - μ * F ≤ sbW)
    (hcount : S + Q = n' * J) (hQc : Q < c₀ * J) (hc₀0 : 0 < c₀) (hc₀ : c₀ ≤ 1 / 10 ^ 6)
    (hX12 : 12 ≤ μ * U) (h4 : 4 * (μ * U) ≤ n')
    (hbrdef : br = (10 / 37) * (S / J - 1) - (1 + 1 / 10000) * (μ * U)) :
    (1 / 18) * μ * (n' / U) * W * J ≤ sbW := by
  have hsJ : n' - c₀ ≤ S / J := by
    rw [le_div_iff₀ hJ]
    nlinarith [hcount, hQc]
  obtain ⟨hbrnn, harith⟩ :=
    Work.BoseB1Cube.rowOneArith (X := μ * U) (n := n') (s := S / J) (c₀ := c₀)
      (ρ := 1 + 1 / 10000) hX12 h4 hsJ hc₀0 hc₀ (by norm_num) (by norm_num)
  have hSbr : J * (μ * U * n' / 18) ≤ S * br := by
    have h1 := mul_le_mul_of_nonneg_left harith hJ.le
    have h2 : J * ((S / J) * ((10 / 37) * (S / J - 1) - (μ * U) * (1 + 1 / 10000)))
        = S * br := by
      rw [hbrdef]
      field_simp
      try ring
    linarith [h1, h2.le, h2.ge]
  have hbr0 : 0 ≤ br := by rw [hbrdef]; linarith [hbrnn]
  have hθ : (M1 / U) * S ≤ (M2 / U) * S := by
    rw [hM1W]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hWM2 hU.le) hS
  have hledger : (M2 / U ^ 2) * (S * br) ≤ sbW := by
    have h := rowOneLedger (S := S) (Q := Q) (J := J) (U := U) (M1 := M1) (M2 := M2) (P := P)
      (F := F) (bG := bG) (sbW := sbW) (Cm := Cm) (a := a) (μ := μ)
      hU hS hQ ha hμ hCm hθ hG hP0 hF0 hY hbed
    rw [hbrdef]
    exact h
  have hfin := rowOneFinal (S := S) (J := J) (U := U) (W := W) (M2 := M2) (br := br) (μ := μ)
    (n' := n') hU hJ.le hS hW hWM2 hbr0 hSbr
  linarith [hledger, hfin]

theorem flatArm37RowOneGoodLower {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ u : EuclideanSpace ℝ (Fin 3),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
          μ * Work.BoseFixB1B.PBW h μ u ≤ _root_.BoseGases.a v →
          12 ≤ μ * Work.BoseFixB1B.PBBV v μ u →
          (∀ {n' : ℕ}, 4 * μ * Work.BoseFixB1B.PBBV v μ u ≤ (n' : ℝ) →
              (n' : ℝ) < 5 * μ * Work.BoseFixB1B.PBBV v μ u →
              ∀ (Φ : Submission.BoseGases.X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
                Work.BoseFixB1B.InBox v μ u Φ →
                Work.BoseB1Cube.FlatArm37 v h μ n' Φ u →
                Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Φ
                  < c₀ * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) →
                (1 / 18) * μ * ((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u)
                    * Work.BoseFixB1B.PBW h μ u
                    * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2)
                  ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ) := by
  classical
  -- ### the manifest constant and the two diluteness thresholds
  obtain ⟨Cm, hCm0, hman⟩ := Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad hR
    hv_supp hav (M := Work.BoseBox.mValue) (by rw [Work.BoseBox.mValue]; norm_num)
  obtain ⟨εR, hεR, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εK, hεK, hgate⟩ := Work.BoseB1Cube.bGapCoeff_gate (v := v) hav
    (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1) (by positivity)
  refine ⟨min (min εK εR) 1, 1 / 10 ^ 6, lt_min (lt_min hεK hεR) one_pos, by norm_num, ?_⟩
  intro μ hAdm u hu hWmu hX12 n' h4 h5 Φ hΦc hInBox hFlat hQc
  have hAdmR : Work.BoseBoxFix.Adm v εR μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmK : Work.BoseBoxFix.Adm v εK μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdmR.1 hAdmR.2.1
  have hμ0 : 0 < μ := hAdm.1
  have ha0 : 0 ≤ _root_.BoseGases.a v := hav.le
  have hℓ : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hΦcont : Continuous Φ := hΦc.continuous
  have hMle : 1 ≤ Work.BoseFixB1B.PBM v μ := by
    show (1 : ℕ) ≤ Work.BoseBox.mValue
    rw [Work.BoseBox.mValue]
    norm_num
  -- ### the local objects
  set U : ℝ := Work.BoseFixB1B.PBBV v μ u with hUdef
  set W : ℝ := Work.BoseFixB1B.PBW h μ u with hWdef
  set J : ℝ := ∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2 with hJdef
  set S : ℝ := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u)
    (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ with hSdef
  set Q : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
    (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Φ with hQdef
  set M1 : ℝ := Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
    (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u) with hM1def
  set M2 : ℝ := Work.BoseFixB1S.boxM2 (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBB v μ u)
    (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u v) with hM2def
  set P : ℝ := Work.BoseFixB1.pairSum v (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
    (Work.BoseFixB1B.PBd v μ) u Φ with hPdef
  set F : ℝ := Work.BoseFixB1.fibSum h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
    (Work.BoseFixB1B.PBd v μ) u Φ with hFdef
  set Pc : ℝ := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1B.PBBV v μ u)
    (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ with hPcdef
  set br : ℝ := (10 / 37) * (S / J - 1) - (1 + 1 / 10000) * (μ * U) with hbrdef
  -- ### basic signs
  have hUpos : 0 < U := by
    rw [hUdef]
    exact Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ0 hu
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hJ0 : 0 ≤ J := by
    rw [hJdef]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact Work.BoseFixB1S.cnPlusBoxInd_nonneg _ _ _ _
  have hS0 : 0 ≤ S := by
    rw [hSdef, Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hJpos : 0 < J := by
    rcases eq_or_lt_of_le hJ0 with hz | hp
    · exfalso
      have h0 : (1 / 10 ^ 6) * J = 0 := by rw [hz.symm, mul_zero]
      rw [h0] at hQc
      exact absurd hQc (not_lt_of_ge hQ0)
    · exact hp
  have hJne : J ≠ 0 := ne_of_gt hJpos
  have hX12' : 12 ≤ μ * U := hX12
  have h4' : 4 * (μ * U) ≤ (n' : ℝ) := by linarith [h4]
  -- ### the gate `(2500·Cc²a + Cc)·μa·Q ≤ bGapCoeff·Q`
  have hG : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1)) * μ
        * (_root_.BoseGases.a v) * Q ≤ Work.BoseFixB1.bGapCoeff v μ * Q := by
    have h3 : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1))
          * (μ * (_root_.BoseGases.a v))
        ≤ (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1)
          * (μ * (_root_.BoseGases.a v)) := by
      have hle : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1))
          ≤ (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1) := by linarith
      exact mul_le_mul_of_nonneg_right hle (mul_nonneg hμ0.le ha0)
    have h4 : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1) + 1)
          * (μ * (_root_.BoseGases.a v)) ≤ Work.BoseFixB1.bGapCoeff v μ := hgate μ hAdmK
    have h5 : (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) + (Cm + 1))
          * (μ * (_root_.BoseGases.a v)) * Q ≤ Work.BoseFixB1.bGapCoeff v μ * Q :=
      mul_le_mul_of_nonneg_right (le_trans h3 h4) hQ0
    linarith [h5]
  -- ### the word decomposition
  have hkin : Work.BoseFixB1.bGapCoeff v μ * Q ≤ Work.BoseFixB1B.sbKinCube v μ u Φ := by
    have hnn : 0 ≤ Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u)
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ :=
      Work.BoseFixB1.tBwordKinInd_nonneg Φ
    rw [hQdef, Work.BoseFixB1B.sbKinCube, Work.BoseFixB1B.cubeSpectral]
    linarith
  have hpot : Work.BoseFixB1.sbPot h μ u Φ = P - μ * F := by
    have hs := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
      hAdm hΦcont u hR16 hRχ
    rw [hPdef, hFdef]
    linarith [hs]
  have hbed : Work.BoseFixB1.bGapCoeff v μ * Q + P - μ * F
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
    have hword : Work.BoseFixB1B.sbWordCube v h μ u Φ
        = Work.BoseFixB1B.sbKinCube v μ u Φ + Work.BoseFixB1.sbPot h μ u Φ := rfl
    rw [hword, hpot]
    linarith [hkin]
  -- ### the pair row
  have hFlat' : Pc ≤ (37 / 10) * (U ^ 2 / M2) * P := by
    have hh := hFlat
    rw [Work.BoseB1Cube.FlatArm37] at hh
    rw [hPcdef, hUdef, hM2def, hPdef]
    exact hh
  have hvolA : Work.BoseFixB1B.PBBV v μ u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u)).toReal := by
    rw [Work.BoseFixB1B.PBBV, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.Measure.real_def]
  have hpairPay : S ^ 2 / J - S ≤ Pc := by
    rw [hSdef, hPcdef, hJdef]
    exact Work.BoseB1Cube.pairCountPaymentLower (N := n') hℓ hUpos
      (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u) hvolA
      (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u) hΦcont hJpos
  have hM1W : M1 = W := by
    rw [hM1def, hWdef]
    exact boxM1_eq_w1MassB (h := h) (M := Work.BoseFixB1B.PBM v μ) hMle hℓ hd u
  have hWM2 : W ≤ M2 := by
    rw [hWdef, hM2def]
    exact w1MassB_le_boxM2_v (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseFixB1B.PBM v μ) hMle hℓ hd hR16 hRχ u
  have hM2nn : 0 ≤ M2 := le_trans hW0 hWM2
  have hnn37 : 0 ≤ (10 / 37) * (M2 / U ^ 2) :=
    mul_nonneg (by norm_num) (div_nonneg hM2nn (by positivity))
  have hPcP : (10 / 37) * (M2 / U ^ 2) * Pc ≤ P := by
    have h1 := mul_le_mul_of_nonneg_left hFlat' hnn37
    rcases eq_or_lt_of_le hM2nn with h2 | h2
    · have hL : (10 / 37) * (M2 / U ^ 2) * Pc = 0 := by rw [h2.symm]; simp
      rw [hL]
      exact Work.BoseFixB1.pairSum_nonneg hv (M := Work.BoseFixB1B.PBM v μ)
        (ℓ := Work.BoseFixB1B.PBℓ v μ) (d := Work.BoseFixB1B.PBd v μ) u Φ
    · have h2ne : M2 ≠ 0 := ne_of_gt h2
      have heq : (10 / 37) * (M2 / U ^ 2) * ((37 / 10) * (U ^ 2 / M2) * P) = P := by
        field_simp
      linarith [h1, heq.le, heq.ge]
  have hP0 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1)) ≤ P := by
    have h2 : (10 / 37) * (M2 / U ^ 2) * (S ^ 2 / J - S)
        ≤ (10 / 37) * (M2 / U ^ 2) * Pc := mul_le_mul_of_nonneg_left hpairPay hnn37
    have h3 : (M2 / U ^ 2) * S * ((10 / 37) * (S / J - 1))
        = (10 / 37) * (M2 / U ^ 2) * (S ^ 2 / J - S) := by
      field_simp
      try ring
      try ring_nf
    linarith [h2, h3, hPcP]
  -- ### the manifest fibre row
  have hFraw : F ≤ (M1 / U) * S + Cm * (_root_.BoseGases.a v)
      * (Real.sqrt (Q * ((M1 / U) * S)) + Q) := by
    rw [hFdef, hM1def, hSdef, hUdef, hQdef]
    exact hman (μ := μ) hℓ hd hR16 hRχ u hUpos hΦcont
  have hF0 : F ≤ (M1 / U) * S + (Cm + 1) * (_root_.BoseGases.a v)
      * (Real.sqrt (Q * ((M1 / U) * S)) + Q) := by
    have h2 : Cm * (_root_.BoseGases.a v) * (Real.sqrt (Q * ((M1 / U) * S)) + Q)
        ≤ (Cm + 1) * (_root_.BoseGases.a v) * (Real.sqrt (Q * ((M1 / U) * S)) + Q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) ha0
    linarith [hFraw, h2]
  -- ### Young
  have hθnn : 0 ≤ (M1 / U) * S := by
    rw [hM1W]
    exact mul_nonneg (div_nonneg hW0 (by positivity)) hS0
  have hY : μ * (Cm + 1) * (_root_.BoseGases.a v) * Real.sqrt (Q * ((M1 / U) * S))
      ≤ μ * (1 / 10000) * ((M1 / U) * S)
        + μ * (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) ^ 2) * Q := by
    rcases eq_or_lt_of_le (mul_nonneg (by positivity : (0 : ℝ) ≤ Cm + 1) ha0) with hz | hpos
    · have h0 : μ * (Cm + 1) * (_root_.BoseGases.a v) = 0 := by
        rw [mul_assoc, hz.symm, mul_zero]
      rw [h0, zero_mul]
      have ha1 : 0 ≤ μ * (1 / 10000) * ((M1 / U) * S) :=
        mul_nonneg (mul_nonneg hμ0.le (by norm_num)) hθnn
      have hb1 : 0 ≤ μ * (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) ^ 2) * Q :=
        mul_nonneg (mul_nonneg hμ0.le (by positivity)) hQ0
      linarith
    · have hη : 0 < 2500 * (Cm + 1) * (_root_.BoseGases.a v) := by positivity
      have hy := sqrt_mul_le_add_div (Q := Q) (θ := (M1 / U) * S)
        (η := 2500 * (Cm + 1) * (_root_.BoseGases.a v)) hQ0 hθnn hη
      have hm : μ * (Cm + 1) * (_root_.BoseGases.a v) * Real.sqrt (Q * ((M1 / U) * S))
          ≤ μ * (Cm + 1) * (_root_.BoseGases.a v)
            * (2500 * (Cm + 1) * (_root_.BoseGases.a v) * Q
              + ((M1 / U) * S) / (4 * (2500 * (Cm + 1) * (_root_.BoseGases.a v)))) :=
        mul_le_mul_of_nonneg_left hy
          (mul_nonneg (mul_nonneg hμ0.le (by positivity : (0 : ℝ) ≤ Cm + 1)) ha0)
      have heq : μ * (Cm + 1) * (_root_.BoseGases.a v)
            * (2500 * (Cm + 1) * (_root_.BoseGases.a v) * Q
              + ((M1 / U) * S) / (4 * (2500 * (Cm + 1) * (_root_.BoseGases.a v))))
          = μ * (1 / 10000) * ((M1 / U) * S)
            + μ * (2500 * (Cm + 1) ^ 2 * (_root_.BoseGases.a v) ^ 2) * Q := by
        field_simp
        try ring
        try ring_nf
      linarith [hm, heq.le, heq.ge]
  -- ### assemble
  exact rowOneMain (S := S) (Q := Q) (J := J) (U := U) (W := W) (M1 := M1) (M2 := M2) (P := P)
    (F := F) (bG := Work.BoseFixB1.bGapCoeff v μ)
    (sbW := Work.BoseFixB1B.sbWordCube v h μ u Φ) (br := br) (Cm := Cm + 1)
    (a := _root_.BoseGases.a v) (μ := μ) (n' := (n' : ℝ)) (c₀ := 1 / 10 ^ 6)
    hUpos hJpos hS0 hQ0 ha0 hμ0.le (by positivity) hW0 hM1W hWM2 hG hP0 hF0 hY hbed
    (by
      rw [hSdef, hQdef, hJdef]
      exact Work.BoseFixB1S.b1sCountSplit (N := n') hℓ hUpos
        (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u) hvolA
        (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u) hΦcont hInBox)
    hQc (by norm_num) (by norm_num) hX12' h4' hbrdef

end Work.BoseB1Cube
