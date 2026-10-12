import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory Metric Filter
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS's weight `F(t) = c(t−μ)²/(1+tμ⁻¹)` is nonnegative on the *physical*
range `t ≥ 0` (the denominator `1 + tμ⁻¹` there exceeds `1`, whereas it can be
negative for `t < −μ`, which is why the sign hypothesis `0 ≤ t` matters). -/
lemma psiWeight_nonneg {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight c μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hd : 0 < 1 + t * μ⁻¹ := by positivity
  exact div_nonneg (mul_nonneg hc (sq_nonneg _)) hd.le

/-- The per-configuration small-box particle count `Σᵢχ_{B(u)}(xᵢ)²` is
nonnegative: it is a sum of squares. -/
lemma nCountB_nonneg (M : ℕ) (ℓ d : ℝ) (u : ℝ³) {n : ℕ} (x : X n) :
    0 ≤ nCountB M ℓ d u x := by
  rw [nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The small-box volume `|B(u)| = (ℓd)³` is positive. -/
lemma boxVol_pos {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    0 < Work.SmallBoxSliding.boxVol ℓ d := by
  rw [Work.SmallBoxSliding.boxVol]
  exact pow_pos (mul_pos hℓ hd) 3

theorem rPsiB_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {μ : ℝ} (hμ : 0 < μ) {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 ≤ c) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1.RPsiB h M c μ ℓ d Φ := by
  -- the small-box mass `|B(u)| = chiMass M ℓ d u` is nonnegative
  have hvol : ∀ u : ℝ³, 0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u := fun u =>
    Work.SmallBoxSliding.chiMass_nonneg M ℓ d u
  -- the per-box weight `∬ w_{1,B(u)}` is nonnegative (sign structure of the kernels)
  have hker : ∀ u : ℝ³, 0 ≤ w1MassB h M ℓ d u := fun u =>
    wSmall1Pair_mass_nonneg hv hvrad hv_supp hR h hM hℓ hd u
  -- the inner configuration integral: `Φ² ≥ 0` against `F(n/|B|) ≥ 0`
  have hinn : ∀ u : ℝ³, 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ,
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight c μ
        (nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) := by
    intro u
    apply integral_nonneg
    intro x
    refine mul_nonneg (sq_nonneg _) (psiWeight_nonneg hc hμ (div_nonneg ?_ (hvol u)))
    exact nCountB_nonneg M ℓ d u x
  rw [RPsiB]
  exact integral_nonneg fun u => mul_nonneg (hker u) (hinn u)

end Work.BoseFixB1
