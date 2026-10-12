import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- **The degenerate box state.**  A `BoxState` may have `normB v μ n Φ = ∫_{abox}Φ² = 0` (the
class carries only `ContDiff` + `PermInvariant` + `≠ 0`, so a state vanishing a.e. on the
configuration box is allowed).  In that case the localised pair/one-body word vanishes
(`qLHSwordB` is the integral of `Φ² · density`, and `Φ² = 0` a.e.), while the kinetic word
`sbKin = tBwordBInd` is `≥ 0`; so the whole sliding word is `≥ 0`.  This is the case the
`0 < normB` gates of `Work.BoseFixB1B.PerBoxFLow` / `OffGoodCrudeLow` do not cover and which the
target `Work.BoseFixB1S.perBoxCrudeLowerB1` (whose statement has no such gate) still needs, its
right-hand side being `0` there. -/
theorem sbWord_nonneg_of_normB_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ε₀ μ : ℝ} (hadm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    (u : EuclideanSpace ℝ (Fin 3))
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (h0 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0) :
    0 ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseFixB1.adm_ell_pos hadm
  -- The kinetic half is nonnegative at an admissible point.
  have hkin : 0 ≤ Work.BoseFixB1.sbKin (v := v) μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
      (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [show Work.BoseFixB1.sbKin (v := v) μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
        (Φ : Submission.BoseGases.X n → ℝ)
        = Work.UBBInputs8.tBwordBInd n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
            (Φ : Submission.BoseGases.X n → ℝ) from rfl]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ (Work.BoseFixB1.adm_eT_bounds hadm).1 u _
  -- The potential half vanishes: its integrand carries the factor `Φ² = 0` a.e. on the box.
  have hpot : Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
    rw [show Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
        = Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
            (Φ : Submission.BoseGases.X n → ℝ) from rfl]
    rw [Work.SmallBoxSliding.qLHSwordB_eq_integral]
    have h0' : Work.BoseKinLoc.sqNormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ) = 0 := h0
    -- `Φ²` is integrable on the (compact) box, so a vanishing integral forces it to vanish a.e.
    have hInt : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (MeasureTheory.volume) :=
      ContinuousOn.integrableOn_compact
        (Submission.BoseGases.abox_compact n hℓ)
        (((Φ.contDiff.continuous).continuousOn).pow 2)
    have hae : (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))] 0 :=
      (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hInt).mp h0'
    have hae2 : (fun x : Submission.BoseGases.X n =>
          Work.SmallBoxSliding.qLHSBIntegrand h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
            (Φ : Submission.BoseGases.X n → ℝ) u x)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))] 0 := by
      filter_upwards [hae] with x hx
      have hx' : (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 = 0 := by simpa using hx
      simp only [Work.SmallBoxSliding.qLHSBIntegrand]
      rw [hx']; simp
    rw [MeasureTheory.integral_congr_ae hae2]
    simp
  rw [show Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ) from rfl,
      hpot, add_zero]
  exact hkin

end Work.BoseFixB1S
