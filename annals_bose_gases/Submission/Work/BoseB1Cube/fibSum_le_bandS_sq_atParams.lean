import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1S.bandFlatArmGateB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.fibSum_le_bandS_sq_atParams`

The **band fibre bound at FS's parameters**: on the bad band
`u ∈ bandSet (sideAt μ a) d μ` the cutoff `χ_{B(u)}` is pointwise dominated by the band scale
`bandS M ℓ d μ` (`Work.BoseFixB1.chiSmallB_le_bandS`).  Consequently each of the `n` particles
contributes at most one factor `bandS` to the linear (`fibre`) part of the localised potential
word, on top of the factor `bandK · bandS` carried by the one-body fibre kernel:

    fibSum ≤ bandK · bandS² · n · ‖Φ‖² .

## The route

1. `Work.BoseFixB1S.fibSum_le_bandS_mul_occChi` (**PROVED**, `bandFlatArmGateB1`): on the band
   the fibre integral is bounded by `bandK · bandS` times the `χ`-weighted occupancy
   `occChi = ∫ Φ²·Σᵢχ_{B(u)}(xᵢ)`.
2. `occChi ≤ bandS · (n·‖Φ‖²)`: purely pointwise, since `Σᵢχ_{B(u)}(xᵢ) ≤ n·bandS` by the band
   domination and `‖Φ‖² = ∫_{abox n ℓ} Φ²` (`Work.BoseBoxFix.normB` = `Work.BoseKinLoc.sqNormB`).

Both steps are nonnegative-monotonicity statements for the integral over the compact box
`abox n ℓ`; the integrands are continuous, hence integrable there.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The band fibre bound at free box parameters.**  For a continuous state `Φ` on the `n`-particle
box of side `ℓ`, on the band `bandSet ℓ d μ`,

    fibSum h M ℓ d u Φ ≤ bandK v h M · bandS M ℓ d μ² · n · ∫_{abox n ℓ} Φ² .

This is the parameter-free form of the target (`ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`M = (paramsAt μ (a v)).M`). -/
theorem fibSum_le_bandS_sq_general {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (hR16 : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) {u : E3}
    (hu : u ∈ Work.SmallBoxSliding.bandSet ℓ d μ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.fibSum h M ℓ d u Φ
      ≤ Work.BoseFixB1.bandK v h M * Work.BoseFixB1.bandS M ℓ d μ ^ 2 * (n : ℝ)
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  -- Step 1: the fibre bound against the `χ`-weighted occupancy.
  have hmain := Work.BoseFixB1S.fibSum_le_bandS_mul_occChi (h := h) hv hvrad hR hv_supp hM hℓ hd
    hμ hR16 hRχ hu Φ hΦc
  -- the band domination of the cutoff
  have hband : ∀ z : E3, Submission.BoseGases.chiSmallB M ℓ d u z
      ≤ Work.BoseFixB1.bandS M ℓ d μ :=
    fun z => Work.BoseFixB1.chiSmallB_le_bandS hM hℓ hd hμ hu z
  -- Step 2: `occChi ≤ bandS·(n·∫Φ²)`, purely pointwise.
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)
        ≤ (Φ x) ^ 2 * ((n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ) := by
    intro x
    have hs : (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ ∑ _i : Fin n, Work.BoseFixB1.bandS M ℓ d μ :=
      Finset.sum_le_sum fun i _ => hband (x i)
    have hs' : (∑ _i : Fin n, Work.BoseFixB1.bandS M ℓ d μ)
        = (n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hs.trans (le_of_eq hs')) (sq_nonneg _)
  -- integrability of the two integrands on the compact `n`-particle box
  have hsum_cont : Continuous (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) :=
    continuous_finsetSum _ fun i _ =>
      (Work.SmallBoxSliding.chiSmallB_continuous_joint M ℓ d i).comp
        (continuous_const.prodMk continuous_id)
  have hfi : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      (Submission.BoseGases.abox n ℓ) :=
    ((hΦc.pow 2).mul hsum_cont).continuousOn.integrableOn_compact
      (Submission.BoseGases.abox_compact n hℓ)
  have hgi : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ((n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ))
      (Submission.BoseGases.abox n ℓ) :=
    (((hΦc.pow 2).mul continuous_const)).continuousOn.integrableOn_compact
      (Submission.BoseGases.abox_compact n hℓ)
  have hmono : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ((n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ) :=
    MeasureTheory.setIntegral_mono_on hfi hgi (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => hpt x)
  have hgval : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ((n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ))
      = (n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
    rw [MeasureTheory.integral_mul_const]
    ring
  have hocc : Work.BoseFixR.occChi M ℓ d u Φ
      ≤ Work.BoseFixB1.bandS M ℓ d μ
          * ((n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
    rw [Work.BoseFixR.occChi]
    calc (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * ((n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ) := hmono
      _ = (n : ℝ) * Work.BoseFixB1.bandS M ℓ d μ
            * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := hgval
      _ = Work.BoseFixB1.bandS M ℓ d μ
            * ((n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by ring
  -- Assembly.
  have hK : 0 ≤ Work.BoseFixB1.bandK v h M * Work.BoseFixB1.bandS M ℓ d μ :=
    mul_nonneg (Work.BoseFixB1.bandK_nonneg M) (Work.BoseFixB1.bandS_nonneg M ℓ d μ)
  calc Work.BoseFixB1.fibSum h M ℓ d u Φ
      ≤ Work.BoseFixB1.bandK v h M * Work.BoseFixB1.bandS M ℓ d μ
          * Work.BoseFixR.occChi M ℓ d u Φ := hmain
    _ ≤ Work.BoseFixB1.bandK v h M * Work.BoseFixB1.bandS M ℓ d μ
          * (Work.BoseFixB1.bandS M ℓ d μ
              * ((n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hocc hK
    _ = Work.BoseFixB1.bandK v h M * Work.BoseFixB1.bandS M ℓ d μ ^ 2 * (n : ℝ)
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by ring

theorem fibSum_le_bandS_sq_atParams {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        * Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ^ 2
        * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    using fibSum_le_bandS_sq_general (v := v) h hv hvrad hR hv_supp hM hℓ hd hμ hR16 hRχ hu
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous

end Work.BoseB1Cube
