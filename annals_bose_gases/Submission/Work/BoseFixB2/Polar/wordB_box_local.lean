import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB2.Defs
import Submission.Work.BoseKinLoc.Sector.fsT_box_invariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Polar.wordB_box_local`

The frozen box word `Work.BoseBoxFix.wordB v h μ n` (FS `eq:Def_HB2`, i.e. the
box-restricted form `Work.BoseKinLoc.boxFormB`) is a **box functional**: it is defined
from the box integrals of `boxFormB` over the centred configuration box
`abox n ℓ`, `ℓ = fsSide v μ = sideAt μ (a v)`.

* The potential piece `∫_{abox} Φ²·potWordU … 0` is a plain box integral, so it is
  unchanged as soon as the two states agree on the box.
* The kinetic piece is `ℓ⁻³ Σᵢ ∫_{x∈abox} indU ℓ 0 (xᵢ)·fsT ℓ d s εT b 0 (fibre n i Φ x)`.
  For `x` in the box the slot-`i` fibre `z ↦ Φ(x_{i←z})` is only probed on the anchored
  box `lamBox ℓ 0 = acube ℓ`, and replacing the `i`-th slot of a box configuration by a
  point of `acube ℓ` keeps the configuration inside `abox n ℓ`.  Hence two states that
  agree on `abox n ℓ` have fibres that agree on `lamBox ℓ 0`, and the box-locality of
  `fsT` (`Sector.fsT_box_invariant`) makes the integrands equal pointwise on the box.

The degenerate side length `ℓ ≤ 0` — which occurs exactly when the parameters collapse
the box (`μ ≤ 0` gives `(μ a)^{-1/2} = 0` in `boxSide`) — is handled separately: then the
box is a null set (`abox_volume_eq_zero_of_one_le_of_nonpos`), so both words vanish.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The fibres of two states agreeing on the box agree on the anchored box -/

/-- If `X = Y` on the configuration box `abox n ℓ`, then for every point `x` of that box the
slot-`i` fibres `z ↦ X(x_{i←z})` and `z ↦ Y(x_{i←z})` agree on the anchored box
`lamBox ℓ 0 = acube ℓ`. -/
theorem fibre_eqOn_lamBox_of_eqOn_abox {ℓ : ℝ} {n : ℕ}
    {X Y : Submission.BoseGases.X n → ℝ}
    (hXY : ∀ x ∈ Submission.BoseGases.abox n ℓ, X x = Y x) (i : Fin n) :
    ∀ x ∈ Submission.BoseGases.abox n ℓ, ∀ z ∈ Work.BoseKinLoc.lamBox ℓ 0,
      Work.BoseKinLoc.fibre n i X x z = Work.BoseKinLoc.fibre n i Y x z := by
  intro x hx z hz
  have hz' : z ∈ Submission.BoseGases.acube ℓ := by
    simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hz
  show X (Function.update x i z) = Y (Function.update x i z)
  refine hXY _ fun j => ?_
  by_cases hji : j = i
  · subst hji; rw [Function.update_self]; exact hz'
  · rw [Function.update_of_ne hji]; exact hx j

/-! ## 2. The box word is local: the positive side case -/

/-- The box-restricted form `boxFormB` only sees the restriction of the state to the box
`abox n ℓ`, for a positive side length `ℓ` (which is what the box-locality
`fsT_box_invariant` of the kinetic word requires). -/
theorem boxFormB_congr_of_pos {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ d s εT b : ℝ}
    (hℓ : 0 < ℓ) {n : ℕ} {X Y : Submission.BoseGases.X n → ℝ}
    (hXY : ∀ x ∈ Submission.BoseGases.abox n ℓ, X x = Y x) :
    Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b X
      = Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b Y := by
  have hkin : Work.BoseKinLoc.kinFormB n ℓ d s εT b X
      = Work.BoseKinLoc.kinFormB n ℓ d s εT b Y := by
    simp only [Work.BoseKinLoc.kinFormB]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    refine MeasureTheory.setIntegral_congr_fun
      (Submission.BoseGases.abox_measurable n ℓ) fun x hx => ?_
    rw [Work.BoseKinLoc.Sector.fsT_box_invariant (u := 0) hℓ
      (fibre_eqOn_lamBox_of_eqOn_abox hXY i x hx)]
  have hpot : (∫ x in Submission.BoseGases.abox n ℓ,
        (X x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
        (Y x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      fun x hx => by rw [hXY x hx]
  rw [Work.BoseKinLoc.boxFormB, Work.BoseKinLoc.boxFormB, hkin, hpot]

/-! ## 3. The degenerate side: the centred cube and the box are null sets -/

/-- For `ℓ ≤ 0` the centred cube `acube ℓ` is a null set (for `ℓ < 0` it is empty, for
`ℓ = 0` it is the single point `0`). -/
theorem acube_volume_eq_zero_of_nonpos (ℓ : ℝ) (hℓ : ℓ ≤ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.acube ℓ) = 0 := by
  rcases lt_or_eq_of_le hℓ with hlt | heq
  · have hemp : Submission.BoseGases.acube ℓ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have h0 := (Submission.BoseGases.mem_acube_iff ℓ y).mp hy 0
      simp only [Set.mem_Icc] at h0
      linarith [h0.1, h0.2]
    rw [hemp, measure_empty]
  · subst heq
    rw [Submission.BoseGases.acube_volume 0 le_rfl]
    norm_num

/-- For `ℓ ≤ 0` and `n ≥ 1` the configuration box `abox n ℓ` is a null set (one slot of the
product already collapses). -/
theorem abox_volume_eq_zero_of_one_le_of_nonpos (n : ℕ) (hn : 1 ≤ n) (ℓ : ℝ) (hℓ : ℓ ≤ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) = 0 := by
  rw [show (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      = MeasureTheory.Measure.pi (fun _ : Fin n =>
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      from rfl]
  rw [Submission.BoseGases.abox_eq_pi_acube, MeasureTheory.Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    (acube_volume_eq_zero_of_nonpos ℓ hℓ)

/-! ## 4. The box word vanishes on a degenerate box -/

/-- On a box of nonpositive side length `ℓ ≤ 0` the box-restricted form vanishes: the box
is a null set, so all its integrals do. -/
theorem boxFormB_eq_zero_of_nonpos {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {ℓ μ d s εT b : ℝ} (hℓ : ℓ ≤ 0) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b Φ = 0 := by
  cases n with
  | zero =>
      simp only [Work.BoseKinLoc.boxFormB, Work.BoseKinLoc.kinFormB,
        Work.BoseKinLoc.potWordU]
      simp
  | succ m =>
      have hvol : (MeasureTheory.volume :
            MeasureTheory.Measure (Submission.BoseGases.X (m + 1)))
          (Submission.BoseGases.abox (m + 1) ℓ) = 0 :=
        abox_volume_eq_zero_of_one_le_of_nonpos (m + 1) (Nat.le_add_left 1 m) ℓ hℓ
      rw [Work.BoseKinLoc.boxFormB, Work.BoseKinLoc.kinFormB]
      have hsum : (∑ i : Fin (m + 1),
            ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x i) *
                Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x))
          = 0 :=
        Finset.sum_eq_zero fun i _ =>
          MeasureTheory.setIntegral_measure_zero _ hvol
      have hpot : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU (m + 1) v g ℓ μ 0 x) = 0 :=
        MeasureTheory.setIntegral_measure_zero _ hvol
      rw [hsum, hpot]
      simp

/-! ## 5. The target: `wordB` is a box functional -/

theorem wordB_box_local {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {X Y : Submission.BoseGases.X n → ℝ}
    (hXY : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ), X x = Y x) :
    Work.BoseBoxFix.wordB v h μ n X = Work.BoseBoxFix.wordB v h μ n Y := by
  rw [Work.BoseBoxFix.wordB]
  by_cases hpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  · exact boxFormB_congr_of_pos hpos hXY
  · exact (boxFormB_eq_zero_of_nonpos (le_of_not_gt hpos) X).trans
      (boxFormB_eq_zero_of_nonpos (le_of_not_gt hpos) Y).symm

end Work.BoseFixB2.Polar
