import ChallengeDeps
import Submission.Work.BoseFixB1B.perBoxCrudeLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.PerBoxFibreB1` — the linear fibre bound of the sliding one-body kernel

The target is the *linear* fibre bound of the localised one-body kernel `wSmall1Pair` at FS's
small-box parameters:

    |∫_{acube ℓ} wSmall1Pair h M ℓ d u x y dy|  ≤  K · (a v) · χ_{B(u)}(x) ,  ℓ = sideAt μ (a v),

with `K` uniform in the admissible `μ` and in `(u, x)`.  This is the loss-kernel bound of the
per-box analysis; the χ²-version `|F| ≤ K a χ_B²` is **false**
(`Work.BoseFixB1.w1Fibre_chiB_sq_bounds_core`), so the linear shape matters.

The mathematics — `g₀ = v(1−w₀) ≥ 0` with `∫g₀ = 8π(a v)`, the numerators' support in
`ball 0 R` with `R ≤ ℓd/16` and `R ≤ ℓ·χR0` (the regime produced by the free `ε₀` through
`Work.BoseFixB1.regime_sideAt_ge`), and the lower bounds on the two renormalisation
denominators (`convScale_ge_half_ball`, `smallConvLower`) — is carried out in the corpus
`Work.BoseFixB1B.fibre_chiB_le` (parameter-free form: `fibre_chiB_le_general`).  FS's
parameters `(paramsAt μ (a v)).M`, `sideAt μ (a v)`, `(paramsAt μ (a v)).d` are exactly its
variables, so the target is an instantiation of that lemma.
-/

noncomputable section

namespace Work.BoseFixB1S

theorem PerBoxFibreB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (u x : EuclideanSpace ℝ (Fin 3)),
        |∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Submission.BoseGases.wSmall1Pair h
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y|
          ≤ K * (_root_.BoseGases.a v) * Submission.BoseGases.chiSmallB
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x :=
  Work.BoseFixB1B.fibre_chiB_le h hv hv1 hvrad hR hv_supp hav

end Work.BoseFixB1S
