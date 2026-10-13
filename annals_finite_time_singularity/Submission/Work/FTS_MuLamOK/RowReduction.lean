/-
# `Submission/Work/FTS_MuLamOK/RowReduction.lean` — `MuLamOK` from the three row envelopes

The end-point of the chapter's *arithmetic* layer: given the three zero-mode row envelopes

  `|L₁₂(N₀ α (F_*+f) f)(0)| ≤ K₀·(α² + √α X + α^{-3/2} X²)`,
  `|L₁₂(N α (F_*+f) (Φs+Ef))(0)| ≤ K₁·(α² + √α X + α^{-3/2} X²)`,
  `|L₁₂(3D_θf/(1+z))(0)| ≤ K₂·X`,                                            `X = Xn α f`,

for every `f` in the source class `Work.FTS.ClassC.ClassC α f` (the class in which the μ/λ
clause is evaluated) the μ/λ clause holds:

  `Work.FTS.StrongEps.MuLamOK α C₀ Φs E`    as soon as   `9·K·α ≤ 2`,

with `K = max (K₀(1 + C₀ + C₀²)) (max (K₁(1 + C₀ + C₀²)) (K₂C₀))` the constant obtained by
scaling the envelopes to `K α²` on profiles of `ℋ⁴`-size `≤ C₀α²` (`Conversion.lean`), and
where `MuLamOK_of_zeroModes` (`Defs.lean`) turns the three scaled zero modes into the clause.

The rows are quantified over `ClassC` because the `N`-row is only available as a statement about
class-`C` profiles (its hypothesis `EllPkgGo α Ce f (E f)` is supplied by the elliptic layer on
that class); `Rows/Rl0Open` and `Rows/Rl2Open` are *stated* for the weaker honest pair
`(SmoothOpen f, HkMem α 4 f)`, so they are restricted to `ClassC` in `Main.lean` through the
`ClassC`-quantified variants of the conversion lemmas.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLamOK.Conversion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK

open Work.FTS.Galerkin (Fn Fam slice muDyn lamDyn)

set_option autoImplicit false

/-- The combined constant of the three scaled zero-mode bounds. -/
def KRow (C₀ K₀ K₁ K₂ : ℝ) : ℝ :=
  max (K₀ * (1 + C₀ + C₀ ^ 2)) (max (K₁ * (1 + C₀ + C₀ ^ 2)) (K₂ * C₀))

theorem KRow_nonneg {C₀ K₀ K₁ K₂ : ℝ} (h0 : 0 ≤ K₀) (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂) :
    0 ≤ KRow C₀ K₀ K₁ K₂ := by
  refine le_trans ?_ (le_max_left _ _)
  exact mul_nonneg h0 (by nlinarith [sq_nonneg C₀])

/-- **`MuLamOK` from the three row envelopes (at class-`C` profiles).** -/
theorem MuLamOK_of_rowEnvelopes {α C₀ K₀ K₁ K₂ : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hrow0 : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
        ≤ K₀ * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2))
    (hrow1 : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + E f z θ)) 0|
        ≤ K₁ * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2))
    (hrow2 : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
        ≤ K₂ * Work.FTS.Nonlin.Xn α f)
    (hsmall : 9 * KRow C₀ K₀ K₁ K₂ * α ≤ 2) :
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E := by
  have h0 : ZeroMode0 α C₀ (KRow C₀ K₀ K₁ K₂) :=
    (ZeroMode0_of_row_classC hα hα1 hK₀ hrow0).mono (le_max_left _ _)
  have h1 : ZeroMode1 α C₀ (KRow C₀ K₀ K₁ K₂) Φs E :=
    (ZeroMode1_of_row_classC hα hα1 hK₁ hrow1).mono
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have h2 : ZeroMode2 α C₀ (KRow C₀ K₀ K₁ K₂) :=
    (ZeroMode2_of_row_classC hK₂ hrow2).mono
      (le_trans (le_max_right _ _) (le_max_right _ _))
  exact MuLamOK_of_zeroModes hα h0 h1 h2 hsmall

/-- **The sharp-order form of the μ-bound from the three row envelopes**: with no smallness
hypothesis on `α`, the modulation is of order `α`,

  `|μ| ≤ (3/2)·KRow·α`   at the constant family of every class-`C` profile of `ℋ⁴`-size `≤ C₀α²`.

This is the form consumed by the `τ`-regularity (Lipschitz / Hölder) estimates of `muDyn` — the
clause `MuLamOK` itself only records `|μ| ≤ 1/2`. -/
theorem abs_muDyn_le_of_rowEnvelopes {α C₀ K₀ K₁ K₂ : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hrow0 : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
        ≤ K₀ * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2))
    (hrow1 : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + E f z θ)) 0|
        ≤ K₁ * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2))
    (hrow2 : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
        ≤ K₂ * Work.FTS.Nonlin.Xn α f) :
    ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
        (fun z θ _ => f z θ) 0| ≤ 3 * KRow C₀ K₀ K₁ K₂ * α / 2 := by
  have h0 : ZeroMode0 α C₀ (KRow C₀ K₀ K₁ K₂) :=
    (ZeroMode0_of_row_classC hα hα1 hK₀ hrow0).mono (le_max_left _ _)
  have h1 : ZeroMode1 α C₀ (KRow C₀ K₀ K₁ K₂) Φs E :=
    (ZeroMode1_of_row_classC hα hα1 hK₁ hrow1).mono
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have h2 : ZeroMode2 α C₀ (KRow C₀ K₀ K₁ K₂) :=
    (ZeroMode2_of_row_classC hK₂ hrow2).mono
      (le_trans (le_max_right _ _) (le_max_right _ _))
  exact abs_muDyn_le_three_halves hα h0 h1 h2

end Work.FTS_MuLamOK
