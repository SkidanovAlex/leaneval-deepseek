import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS muDyn lamDyn)
open Work.FTS.Nonlin (PsiCan)

set_option autoImplicit false

/-! ## Congruence lemmas for the gluing

The equation of the dynamic modulated problem depends on a family only through its slice; the
pointwise-in-time companion of `Work.FTS.Galerkin.dynRHS_congr` (which is stated for two families
whose *all* slices agree) is what the junction argument needs.  The two relative-neighbourhood
lemmas then let a within-derivative on `Icc a τ₀` be read as one on `Icc a b` (and symmetrically),
whenever `τ` is strictly inside the appropriate half. -/

/-- `dynRHS` (with the canonical stream function of `Φs`, `EllSol`) depends on a family only
through its slice at the same fake time. -/
theorem dynRHS_congr_at {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {g g' : Fam} {τ : ℝ}
    (h : slice g τ = slice g' τ) :
    dynRHS α (PsiCan Φs EllSol g) g τ = dynRHS α (PsiCan Φs EllSol g') g' τ := by
  funext z θ
  have h1 : muDyn α (PsiCan Φs EllSol g) g τ = muDyn α (PsiCan Φs EllSol g') g' τ :=
    muDyn_congr h
  have h2 : lamDyn α (PsiCan Φs EllSol g) g τ = lamDyn α (PsiCan Φs EllSol g') g' τ := by
    simp only [lamDyn, h1]
  have h3 : Work.Construction.Ftau α g τ = Work.Construction.Ftau α g' τ := Ftau_congr h
  have h4 : slice (PsiCan Φs EllSol g) τ = slice (PsiCan Φs EllSol g') τ :=
    slice_PsiCan_congr h
  simp only [dynRHS, h1, h2, h3, h4, h]

/-- The left half `[a,τ₀]` is a neighbourhood of `τ` relative to `[a,b]` as soon as `τ < τ₀`. -/
theorem Icc_left_mem_nhdsWithin_Icc {a b τ τ₀ : ℝ} (h : τ < τ₀) :
    Set.Icc a τ₀ ∈ 𝓝[Set.Icc a b] τ := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨Set.Iio τ₀, Iio_mem_nhds h, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩

/-- The right half `[τ₀,b]` is a neighbourhood of `τ` relative to `[a,b]` as soon as `τ₀ < τ`. -/
theorem Icc_right_mem_nhdsWithin_Icc {a b τ τ₀ : ℝ} (h : τ₀ < τ) :
    Set.Icc τ₀ b ∈ 𝓝[Set.Icc a b] τ := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨Set.Ioi τ₀, Ioi_mem_nhds h, fun y hy => ⟨le_of_lt hy.1, hy.2.2⟩⟩

/-- **The junction glue for the dynamic modulated problem.**  If `G` solves the dynamic modulated
problem (equation plus the elliptic law `IsBslSolPos` for the canonical stream function
`PsiCan Φs EllSol`) on the closed fake-time interval `[a,τ₀]` and `H` solves it on `[τ₀,b]`, with
`a ≤ τ₀ ≤ b`, and if the two families agree at the junction `τ₀` (as functions of `(z,θ)`), then
their concatenation `τ ↦ if τ ≤ τ₀ then G(τ) else H(τ)` solves the problem on `[a,b]`.

Proof plan.
* Law part (`∀ τ ∈ Icc a b`, `IsBslSolPos`): the two arguments `Ftau α (concat G H τ₀) τ` and
  `slice (PsiCan Φs EllSol (concat G H τ₀)) τ` depend on the concatenation only through
  `slice (concat G H τ₀) τ` (this is `Work.FTS.StrongGlobal.Ftau_congr` and
  `Work.FTS.StrongGlobal.slice_PsiCan_congr`), which is `slice G τ` for `τ ≤ τ₀` and `slice H τ`
  for `τ₀ < τ` (`Work.FTS.StrongGlobal.slice_concat_of_le`/`slice_concat_of_gt`, which are `simp`
  lemmas); at `τ = τ₀` both descriptions agree by `hag`.  Transport the law of the relevant piece
  with `Work.FTS.StrongGlobal.IsBslSolPos.congr`.
* Equation part: the within-`Icc a b`-derivative of `τ ↦ concat G H τ₀ z θ τ` has value
  `dynLin α (concat G H τ₀) τ z θ + dynRHS α (PsiCan Φs EllSol (concat G H τ₀))
  (concat G H τ₀) τ z θ`, which by the same slice congruences (`Work.FTS.StrongGlobal.dynLin_congr`,
  `Work.FTS.StrongGlobal.muDyn_congr`, `Work.FTS.StrongGlobal.Ftau_congr`,
  `Work.FTS.StrongGlobal.slice_PsiCan_congr`, all in `Defs`) equals the right-hand side of the piece
  that is active at `τ`.
  - `τ < τ₀`: `slice (concat G H τ₀) τ = slice G τ`; use `hG` and enlarge the interval from `Icc a τ₀`
    to `Icc a b` with `HasFDerivWithinAt.hasFDerivWithinAt_inter` (`Icc a τ₀ ∈ 𝓝[Icc a b] τ` since
    `τ < τ₀`), plus `HasFDerivWithinAt.congr` for the two functions agreeing on `Icc a τ₀`.
  - `τ > τ₀`: symmetric, with `hH` on `Icc τ₀ b`.
  - `τ = τ₀`: the two values coincide, because `slice G τ₀ = slice H τ₀` (as functions of `(z,θ)`)
    by `hag` and `dynLin`/`dynRHS` depend on the slice only; combine the two one-sided
    within-derivatives with `HasFDerivWithinAt.union`, using `Icc a τ₀ ∪ Icc τ₀ b = Icc a b`. -/
theorem isDynGSolOnIcc_concat {α a τ₀ b : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G H : Work.FTS.Galerkin.Fam}
    (haτ : a ≤ τ₀) (hτb : τ₀ ≤ b)
    (hG : Work.FTS.StrongGlobal.IsDynGSolOnIcc α a τ₀ Φs EllSol G)
    (hH : Work.FTS.StrongGlobal.IsDynGSolOnIcc α τ₀ b Φs EllSol H)
    (hag : ∀ z θ, G z θ τ₀ = H z θ τ₀) :
    Work.FTS.StrongGlobal.IsDynGSolOnIcc α a b Φs EllSol
      (Work.FTS.StrongGlobal.concat G H τ₀) := by
  constructor
  · -- the elliptic law at every time of `[a,b]`
    intro τ hτ
    rcases le_or_gt τ τ₀ with hle | hlt
    · have hs : slice (concat G H τ₀) τ = slice G τ := slice_concat_of_le hle
      exact (hG.1 τ ⟨hτ.1, hle⟩).congr (Ftau_congr hs.symm) (slice_PsiCan_congr hs.symm)
    · have hs : slice (concat G H τ₀) τ = slice H τ := slice_concat_of_gt hlt
      exact (hH.1 τ ⟨hlt.le, hτ.2⟩).congr (Ftau_congr hs.symm) (slice_PsiCan_congr hs.symm)
  · -- the equation on `[a,b]`
    intro z θ τ hτ hz
    rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
    · -- `τ < τ₀`: the left piece is active
      have hs : slice (concat G H τ₀) τ = slice G τ := slice_concat_of_le hlt.le
      have hv : dynLin α (concat G H τ₀) τ z θ
            + dynRHS α (PsiCan Φs EllSol (concat G H τ₀)) (concat G H τ₀) τ z θ
          = dynLin α G τ z θ + dynRHS α (PsiCan Φs EllSol G) G τ z θ := by
        rw [dynLin_congr hs, dynRHS_congr_at hs]
      rw [hv]
      exact ((hG.2 z θ τ ⟨hτ.1, hlt.le⟩ hz).congr
        (fun y hy => concat_apply_of_le hy.2) (concat_apply_of_le hlt.le)).mono_of_mem_nhdsWithin
        (Icc_left_mem_nhdsWithin_Icc hlt)
    · -- `τ = τ₀`: the two one-sided derivatives agree and cover `[a,b]`
      have hs : slice (concat G H τ₀) τ = slice G τ := slice_concat_of_le heq.le
      have hv : dynLin α (concat G H τ₀) τ z θ
            + dynRHS α (PsiCan Φs EllSol (concat G H τ₀)) (concat G H τ₀) τ z θ
          = dynLin α G τ z θ + dynRHS α (PsiCan Φs EllSol G) G τ z θ := by
        rw [dynLin_congr hs, dynRHS_congr_at hs]
      rw [hv]
      have hGH : slice G τ = slice H τ := by
        rw [heq]
        exact funext fun z => funext fun θ => hag z θ
      have hvGH : dynLin α H τ z θ + dynRHS α (PsiCan Φs EllSol H) H τ z θ
          = dynLin α G τ z θ + dynRHS α (PsiCan Φs EllSol G) G τ z θ := by
        rw [dynLin_congr hGH, dynRHS_congr_at hGH]
      have hH_on : ∀ y ∈ Set.Icc τ₀ b, concat G H τ₀ z θ y = H z θ y := by
        intro y hy
        rcases lt_or_eq_of_le hy.1 with hylt | hyeq
        · exact concat_apply_of_gt hylt
        · rw [← hyeq, concat_apply_of_le le_rfl]; exact hag z θ
      have hL : HasDerivWithinAt (fun s => concat G H τ₀ z θ s)
          (dynLin α G τ z θ + dynRHS α (PsiCan Φs EllSol G) G τ z θ) (Set.Icc a τ₀) τ :=
        (hG.2 z θ τ ⟨hτ.1, heq.le⟩ hz).congr (fun y hy => concat_apply_of_le hy.2)
          (concat_apply_of_le heq.le)
      have hR : HasDerivWithinAt (fun s => concat G H τ₀ z θ s)
          (dynLin α G τ z θ + dynRHS α (PsiCan Φs EllSol G) G τ z θ) (Set.Icc τ₀ b) τ := by
        rw [← hvGH]
        exact (hH.2 z θ τ ⟨heq.ge, hτ.2⟩ hz).congr hH_on (hH_on τ ⟨heq.ge, hτ.2⟩)
      have hunion := hL.union hR
      rwa [Set.Icc_union_Icc_eq_Icc haτ hτb] at hunion
    · -- `τ₀ < τ`: the right piece is active
      have hs : slice (concat G H τ₀) τ = slice H τ := slice_concat_of_gt hgt
      have hv : dynLin α (concat G H τ₀) τ z θ
            + dynRHS α (PsiCan Φs EllSol (concat G H τ₀)) (concat G H τ₀) τ z θ
          = dynLin α H τ z θ + dynRHS α (PsiCan Φs EllSol H) H τ z θ := by
        rw [dynLin_congr hs, dynRHS_congr_at hs]
      rw [hv]
      have hH_on : ∀ y ∈ Set.Icc τ₀ b, concat G H τ₀ z θ y = H z θ y := by
        intro y hy
        rcases lt_or_eq_of_le hy.1 with hylt | hyeq
        · exact concat_apply_of_gt hylt
        · rw [← hyeq, concat_apply_of_le le_rfl]; exact hag z θ
      exact ((hH.2 z θ τ ⟨hgt.le, hτ.2⟩ hz).congr hH_on
        (hH_on τ ⟨hgt.le, hτ.2⟩)).mono_of_mem_nhdsWithin (Icc_right_mem_nhdsWithin_Icc hgt)

end Work.FTS.StrongGlobal
