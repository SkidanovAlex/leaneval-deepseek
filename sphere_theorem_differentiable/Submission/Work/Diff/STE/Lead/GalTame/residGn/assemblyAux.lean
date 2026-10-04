import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Plumbing for the sharp residual assembly

Two elementary facts about the iterated partial derivatives `Work.Diff.STE.pdVec`:

* `pdVec_congr_open`: two functions that agree on an open set have the same iterated partial
  derivatives at every point of that set (this is what lets us replace the explicit residual
  `residualLow` by the smooth box function on the closed `σ_j`-ball);
* `pdVec_comp_add_right`: the iterated partial derivatives commute with a translation of the
  argument (this is what turns the `2^n` shifted outer functions of `residCubeSplit` into the
  shifted outer functions fed to the engine `ResidGn.compositeGnR`).
-/

noncomputable section

open scoped BigOperators ContDiff

namespace Work.Diff.STE.Lead.GalTame.ResidGn

/-- **Local congruence of iterated partial derivatives.**  If two functions agree on an open set
`U`, they have the same iterated partial derivatives at every point of `U`. -/
lemma pdList_congr_open {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (l : List ι) (f g : (ι → ℝ) → ℂ) (U : Set (ι → ℝ)), IsOpen U →
      (∀ z ∈ U, f z = g z) → ∀ x ∈ U,
      Work.Diff.STE.pdList l f x = Work.Diff.STE.pdList l g x := by
  intro l
  induction l with
  | nil => intro f g U _ h x hx; exact h x hx
  | cons i l ih =>
      intro f g U hU h x hx
      show Work.Diff.STE.pd i (Work.Diff.STE.pdList l f) x
        = Work.Diff.STE.pd i (Work.Diff.STE.pdList l g) x
      have hev : Work.Diff.STE.pdList l f =ᶠ[nhds x] Work.Diff.STE.pdList l g := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih f g U hU h y hy
      simp only [Work.Diff.STE.pd]
      rw [Filter.EventuallyEq.fderiv_eq hev]

/-- **Local congruence of `pdVec`.** -/
lemma pdVec_congr_open {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (l : Fin m → ι)
    {f g : (ι → ℝ) → ℂ} {U : Set (ι → ℝ)} (hU : IsOpen U) (h : ∀ z ∈ U, f z = g z)
    {x : ι → ℝ} (hx : x ∈ U) :
    Work.Diff.STE.pdVec m l f x = Work.Diff.STE.pdVec m l g x :=
  pdList_congr_open (List.ofFn l) f g U hU h x hx

/-- **Translation invariance of `pdVec`.**  For a globally smooth `g`, the iterated partial
derivatives of `z ↦ g (z + v)` are the translates of the iterated partial derivatives of `g`. -/
lemma pdVec_comp_add_right {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (l : Fin m → ι)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) (v : ι → ℝ) :
    Work.Diff.STE.pdVec m l (fun z => g (z + v))
      = fun z => Work.Diff.STE.pdVec m l g (z + v) := by
  funext z
  have hgv : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z : ι → ℝ => g (z + v)) :=
    hg.comp (contDiff_id.add contDiff_const)
  rw [Work.Diff.STE.B3.pdVec_eq_iteratedFDeriv_at (f := fun z => g (z + v))
        hgv.contDiffAt m l,
      Work.Diff.STE.B3.pdVec_eq_iteratedFDeriv_at (f := g) hg.contDiffAt m l,
      iteratedFDeriv_comp_add_right]

end Work.Diff.STE.Lead.GalTame.ResidGn
