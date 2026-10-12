import ChallengeDeps
import Submission.Work.BoseBogFS.W1_mass_bounds
import Submission.Work.BoseBogFS.honest_E_W1_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Real

namespace Work.BoseBogFS

/-! `sideAt μ a = K_ℓ(μa)^{-1/2}` is positive as soon as `μ, a > 0`: the box side is
positive and the exponent `-(1/2)` of a positive base is positive. -/
lemma sideAt_pos_honest {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 < Work.BoseBox.sideAt μ a :=
  Work.BoseBox.boxSide_pos hμ ha (Work.BoseBox.fsXp_pos (by positivity))

theorem honest_W1_mass_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R r₁ C : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (μ : ℝ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hreg : R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ r₁)
    (hcond : C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 2) :
    0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0 ∧
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
        ≤ 8 * π * _root_.BoseGases.a v
          * (1 + 2 * C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := sideAt_pos_honest hμ hav
  -- the mass row of `W₁` at the box side `ℓ = sideAt μ (a v)`
  have hb := W1_mass_bounds (v := v) (h := h) (R := R)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (r₁ := r₁) (C := C)
    hR hv hvrad hv_supp hC hr₁ hℓ hT hreg hcond
  -- the environment's `W1` at the zero mode *is* that mass
  rw [honest_E_W1_zero fc fu HM μ]
  exact ⟨lt_of_lt_of_le (by positivity) hb.1, hb.2⟩

end Work.BoseBogFS
