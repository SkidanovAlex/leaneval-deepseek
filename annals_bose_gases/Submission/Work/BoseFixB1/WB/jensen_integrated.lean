import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.integrableOn_wbMass_interior
import Submission.Work.BoseFixB1.WB.jensen_dens
import Submission.Work.BoseFixB1.WB.ji_boxinner_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

theorem jensen_integrated {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        * (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            Work.BoseFixB1.wbMass v h μ u
              * Work.SmallBoxSliding.psiWeight 1 μ
                  (Work.BoseFixB1.wbDens v h μ n (Φ : Submission.BoseGases.X n → ℝ) u))
      ≤ Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) := by
  -- the `x`-inner integral is uniformly bounded
  obtain ⟨M, hM0, hMb⟩ :=
    boxInner_le_const_self (v := v) (h := h) (μ := μ) (n := n) hμ hM hℓ hd Φ
  -- the localised mass is integrable on `I₋`
  have hInt : IntegrableOn (fun u : ℝ³ => wbMass v h μ u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    integrableOn_wbMass_interior (v := v) (h := h) (R0 := R0) hv hvrad hv_supp hR0 hμ hav hM hℓ hd
  have hwb : ∀ u : ℝ³, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg (v := v) (h := h) (R0 := R0) hv hvrad hv_supp hR0 hM hℓ hd u
  -- hence the product with `boxInner` is integrable
  have hglue : IntegrableOn (fun u : ℝ³ => wbMass v h μ u * boxInner v h μ n (Φ : X n → ℝ) u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    integrableOn_wbMass_mul_boxInner_of (v := v) (h := h) (μ := μ) (n := n)
      hμ hM hℓ hd Φ hwb hInt hM0 hMb
  -- the pointwise (Jensen) inequality, multiplied by the nonnegative mass
  have hpt : ∀ u : ℝ³, normB v μ n (Φ : X n → ℝ)
      * (wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u))
      ≤ wbMass v h μ u * boxInner v h μ n (Φ : X n → ℝ) u := by
    intro u
    have hJ := jensen_dens (v := v) (h := h) (μ := μ) (n := n) hμ Φ u
    have h1 : normB v μ n (Φ : X n → ℝ)
          * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)
        ≤ boxInner v h μ n (Φ : X n → ℝ) u := hJ
    calc normB v μ n (Φ : X n → ℝ)
          * (wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u))
        = (normB v μ n (Φ : X n → ℝ)
            * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)) * wbMass v h μ u := by ring
      _ ≤ boxInner v h μ n (Φ : X n → ℝ) u * wbMass v h μ u :=
          mul_le_mul_of_nonneg_right h1 (hwb u)
      _ = wbMass v h μ u * boxInner v h μ n (Φ : X n → ℝ) u := by ring
  -- integrate the pointwise inequality
  show normB v μ n (Φ : X n → ℝ)
      * (∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
          wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u))
      ≤ ∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
          wbMass v h μ u * boxInner v h μ n (Φ : X n → ℝ) u
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hglue ?_
  · filter_upwards with u
    exact mul_nonneg (normB_nonneg _)
      (mul_nonneg (hwb u)
        (Work.BoseFixB1.WB.psiWeight_one_nonneg_local hμ (wbDens_nonneg (Φ : X n → ℝ) u)))
  · filter_upwards with u
    exact hpt u

end Work.BoseFixB1.WB
