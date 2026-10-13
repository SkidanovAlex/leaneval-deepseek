/-
Interior regularity of `bslOp α` (weight `(5-α)/α`): the localized weak identity on the strip.

If `(V, G)` satisfies the strip weak formulation `Q0.StripWeakC` (tested against smooth compactly
supported functions with topological support in the strip `stripE`), then for every cut-off `χ`
with `tsupport χ ⊆ stripE` the pair `(χ · V, χ · G)` satisfies the weak identity against every
smooth compactly supported `ψ` whose support lies in `{χ = 1}`.

The mechanism (as in the sibling `VT.weakLoc`) is that `Kop` is a differential operator with
smooth coefficients: `Kop ψ` is supported in `tsupport ψ ⊆ {χ = 1}`, so the factor `χ` is
redundant on the `Kop ψ`-side; on the `ψ`-side it is redundant because `ψ` itself is supported in
`{χ = 1}`.  The redundant cut-off is then removed by testing the weak identity with `χ · ψ`,
which equals `ψ` (because `χ = 1` on `support ψ`, hence on `tsupport ψ`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.VT.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory Set Filter

theorem weakLocQ0 {V G : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    (hSW : Work.EllipticEst.InteriorRegularity.Q0.StripWeakC V G)
    {χ : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (hχsub : tsupport χ ⊆ Work.EllipticEst.InteriorRegularity.stripE) :
    ∀ ψ : Work.EllipticEst.InteriorRegularity.E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) →
      HasCompactSupport ψ → Function.support ψ ⊆ {x | χ x = 1} →
      ∫ x, (χ x * V x) * Work.EllipticEst.InteriorRegularity.Kop ψ x
        = ∫ x, (χ x * G x) * ψ x := by
  intro ψ hψs hψc hψsub
  -- `χ = 1` on the support of `ψ`, so `χ · ψ = ψ`
  have hχψ : (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y) = ψ := by
    funext x
    by_cases hx : ψ x = 0
    · simp [hx]
    · have h1 : χ x = 1 := hψsub (Function.mem_support.mpr hx)
      simp [h1]
  have hKopEq : Work.EllipticEst.InteriorRegularity.Kop
      (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y)
      = Work.EllipticEst.InteriorRegularity.Kop ψ := by rw [hχψ]
  -- the set `{χ = 1}` is closed and contained in `tsupport χ`
  have hclosed : IsClosed {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} :=
    isClosed_eq (hχs 0).continuous continuous_const
  have hts : tsupport ψ ⊆ {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} := by
    rw [tsupport]
    exact (closure_mono hψsub).trans (le_of_eq hclosed.closure_eq)
  have hχ1ts : {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} ⊆ tsupport χ :=
    fun x hx => subset_closure (by
      rw [Function.mem_support]
      rw [hx]
      exact one_ne_zero)
  have htsuppψ : tsupport ψ ⊆ Work.EllipticEst.InteriorRegularity.stripE :=
    hts.trans (hχ1ts.trans hχsub)
  -- `Kop ψ` is supported in `tsupport ψ`, hence in `{χ = 1}`
  have hKop : Function.support (Work.EllipticEst.InteriorRegularity.Kop ψ)
      ⊆ {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxn
    exact hx (Work.EllipticEst.InteriorRegularity.VT.Kop_eq_zero_of_notMem_tsupport hψs
      (fun h => hxn (hts h)))
  calc ∫ x, (χ x * V x) * Work.EllipticEst.InteriorRegularity.Kop ψ x
      = ∫ x, (χ x * Work.EllipticEst.InteriorRegularity.Kop ψ x) * V x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x, Work.EllipticEst.InteriorRegularity.Kop ψ x * V x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : Work.EllipticEst.InteriorRegularity.Kop ψ x = 0
        · simp [hx]
        · have h1 : χ x = 1 := hKop (Function.mem_support.mpr hx)
          simp only [h1, one_mul]
    _ = ∫ x, V x * Work.EllipticEst.InteriorRegularity.Kop ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x, V x * Work.EllipticEst.InteriorRegularity.Kop
          (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y) x := by
        rw [hKopEq]
    _ = ∫ x, G x * (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y) x :=
        hSW (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y)
          (fun n => by rw [hχψ]; exact hψs n) (by rw [hχψ]; exact hψc)
          (by rw [hχψ]; exact htsuppψ)
    _ = ∫ x, (χ x * G x) * ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

end Work.EllipticEst.InteriorRegularity.Q0
