/-
# Auxiliary analytic lemmas for the jet bound of the chart matrix `Gf`

The module `Submission.Work.Diff.STE.B3.Gtot_aux` carries (among much else) three elementary
analytic lemmas used by `Work.Diff.STE.B3.Gf_pair_jet_bound`:

* `contDiffOn_of_isOpen_contDiffAt` — pointwise `ContDiffAt` on an open set gives `ContDiffOn`;
* `iteratedFDeriv_congr_of_eventuallyEq` — locality of the iterated derivative;
* `norm_iteratedFDeriv_ofReal` — the norm of the iterated derivative of the complexification of a
  real function is at most that of the real function.

This file reproduces exactly those three (under the `Lead.Gal` namespace) so that the jet-bound
argument can be replayed without depending on the (currently non-compiling) `Gtot_aux`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.CoeffDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead.Gal

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- Pointwise `ContDiffAt` on an open set gives `ContDiffOn`. -/
lemma contDiffOn_of_isOpen_contDiffAt {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {s : Set E'} (hs : IsOpen s) {f : E' → F'}
    (h : ∀ x ∈ s, ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ContDiffOn ℝ (⊤ : ℕ∞) f s :=
  fun x hx => (contDiffWithinAt_iff_contDiffAt (hs.mem_nhds hx)).mpr (h x hx)

/-- **Locality of the iterated derivative**: functions which agree near a point have the same
iterated derivatives there. -/
lemma iteratedFDeriv_congr_of_eventuallyEq {n : ℕ} {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {f g : (Fin n → ℝ) → F'}
    {y : Fin n → ℝ} (h : f =ᶠ[𝓝 y] g) (m : ℕ) :
    iteratedFDeriv ℝ m f y = iteratedFDeriv ℝ m g y := by
  obtain ⟨v, hv, hvsub⟩ := h.exists_mem
  have hvsub' : ∀ y ∈ v, f y = g y := hvsub
  obtain ⟨t, htv, hto, hyt⟩ := _root_.mem_nhds_iff.mp hv
  have h1 : iteratedFDeriv ℝ m f y = iteratedFDerivWithin ℝ m f t y :=
    ((iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hto) hyt).symm
  have h2 : iteratedFDerivWithin ℝ m f t y = iteratedFDerivWithin ℝ m g t y :=
    iteratedFDerivWithin_congr (fun x hx => hvsub' x (htv hx)) hyt m
  have h3 : iteratedFDerivWithin ℝ m g t y = iteratedFDeriv ℝ m g y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hto) hyt
  rw [h1, h2, h3]

/-- **The complexification does not increase the jets**: for a real-valued smooth function `f`,
the norm of the `m`-th iterated derivative of `fun z => ((f z : ℝ) : ℂ)` is at most that of `f`. -/
lemma norm_iteratedFDeriv_ofReal {n : ℕ} (f : (Fin n → ℝ) → ℝ) (m : ℕ)
    {y : Fin n → ℝ} (hf : ContDiffAt ℝ (⊤ : ℕ∞) f y) :
    ‖iteratedFDeriv ℝ m (fun z => ((f z : ℝ) : ℂ)) y‖ ≤ ‖iteratedFDeriv ℝ m f y‖ := by
  have hcomp : (fun z => ((f z : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [hcomp]
  refine (Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hf (by simp)).trans ?_
  have hnorm : ‖Complex.ofRealCLM‖ ≤ 1 := by
    refine Complex.ofRealCLM.opNorm_le_bound (by norm_num) fun x => ?_
    simp
  calc ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ m f y‖
      ≤ 1 * ‖iteratedFDeriv ℝ m f y‖ := by gcongr
    _ = ‖iteratedFDeriv ℝ m f y‖ := one_mul _

end Work.Diff.STE.Lead.Gal
