import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.BoseBoxFock.SqrtKinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKinGradBound` — Lipschitz and sup bounds for smooth compactly supported `g`

For `g : ℝ³ → ℂ` that is `C^∞` and compactly supported:

* `g` is globally Lipschitz: `∃ C ≥ 0, ∀ x y, ‖g x − g y‖ ≤ C‖x − y‖`;
* `g` is bounded: `∃ C ≥ 0, ∀ x, ‖g x‖ ≤ C`.

Both are needed for the integrability of the Riesz integrand
`‖x − y‖^{−4}‖g x − g y‖²` (Lipschitz near the diagonal, bounded away from it).

The proof of the Lipschitz bound uses that `fderiv ℝ g` is supported in `tsupport g` (a compact
set, since on the open complement of `tsupport g` the function vanishes identically), hence is
bounded by compactness, and then the mean value inequality.  (Note that `ContDiff ℝ ⊤` is a
*global* smoothness hypothesis; a function such as `φ(x)·sin(1/x²)` with `φ ≡ 1` near `0` is not
even continuous at `0`, so it is not a counterexample.)
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology BigOperators ContDiff

namespace Work.BoseBoxFock

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The Fréchet derivative of a compactly supported `g` is supported in `tsupport g`. -/
lemma fderiv_support_subset_tsupport {g : ℝ³ → ℂ} (hgc : HasCompactSupport g) :
    Function.support (fderiv ℝ g) ⊆ tsupport g := by
  intro x hx
  by_contra hx'
  exact hx (by
    have hev : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    rw [hev.fderiv_eq]
    simp)

/-- A smooth compactly supported function is globally Lipschitz. -/
theorem lipschitz_bound_g {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ³, ‖g x - g y‖ ≤ C * ‖x - y‖ := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x y => ?_⟩
  have hle : ∀ z : ℝ³, ‖fderiv ℝ g z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ tsupport g
    · exact (hC z hz).trans (le_max_left _ _)
    · have h0 : fderiv ℝ g z = 0 :=
        (Function.notMem_support (f := fderiv ℝ g)).mp
          (fun h => hz (fderiv_support_subset_tsupport (g := g) hgc h))
      rw [h0, norm_zero]
      exact le_max_right _ _
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (s := Set.univ) (C := max C 0)
    (fun z _ => hdiff.differentiableAt) (fun z _ => hle z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
/-- A smooth compactly supported function is bounded. -/
theorem bounded_g {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ³, ‖g x‖ ≤ C := by
  have hcont : Continuous g := hg.continuous
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact (hC x hx).trans (le_max_left _ _)
  · have h0 : g x = 0 :=
      (Function.notMem_support (f := g)).mp (fun h => hx (subset_tsupport g h))
    rw [h0, norm_zero]
    exact le_max_right _ _

/-- The Gaussian-integrability form needed for the `(t,p)`-Tonelli step. -/
lemma integrable_g_of {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) : Integrable g :=
  (hgc.toSchwartzMap hg).integrable

end Work.BoseBoxFock
