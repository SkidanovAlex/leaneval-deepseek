/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StrongEpsP/RegGlueP.lean` — the regularity glue of the
`P₀`-scheme (`EpsRegP`)

This module is the `P₀`-analogue of `Work.FTS.StrongEps.GlueParts.RegGlue`: it is the `hReg` slot
of `Work.FTS.StrongEps.StrongEpsP.EpsGlue_of_glueP`.

From a regular `P₀`-solution `G` on `[0,t]` (`EpsRegP α ρ ε t G`) and a restarted one `H` on
`[0,δ]` whose zero slice agrees with the time-`t` slice of `G` and whose fake-time derivatives
agree at the junction (both equal to `R`), the concatenation
`concat G (shiftFam H t) t` is a regular `P₀`-solution on `[0, t+δ]`.

`EpsRegP α ρ ε T g` is

* joint `C¹`-regularity of `(z,θ,τ) ↦ g z θ τ` on `(0,∞) × (0,π/2) × [0,T]`, and
* `EpsDatumP α ρ ε (slice g τ)` for every `τ ∈ [0,T]`.

The two clauses are dealt with separately, exactly as in the un-projected sibling:

* the **first clause** is the junction `C¹`-glue `contDiffOn_concat_shiftFam` below.  The junction
  `τ = t` is simultaneously the right endpoint of the first piece's slab and the left endpoint of
  the second's, so the library's interior-junction lemma
  (`Work.FTS.StrongGlobal.contDiffOn_concat_1`) does not apply; the one-sided variant is
  `Work.FTS.StrongEps.GlueParts.contDiffWithinAt_concat_halfslab`, and the `C¹`-transfer along the
  fake-time shift is `Work.FTS.StrongEps.GlueParts.contDiffOn_shiftFam`.  Off the junction the
  concatenation agrees with one of the two pieces on a neighbourhood, so
  `ContDiffWithinAt.mono_of_mem_nhdsWithin` + `ContDiffWithinAt.congr_of_eventuallyEq` reduce the
  statement to the pieces.  (This clause is *independent of the scheme*: it is the same statement
  as the private helper of `GlueParts/RegGlue.lean`, restated here in public form.)
* the **second clause** is bookkeeping: for `τ ≤ t` the concatenated slice is literally
  `slice G τ` (`Work.FTS.StrongGlobal.slice_concat_of_le`), and for `t < τ` it is
  `slice H (τ - t)` (`Work.FTS.StrongGlobal.slice_concat_of_gt` + `slice_shiftFam`); both hypotheses
  `hG.2`, `hH.2` are of exactly the required shape, so no congruence of `EpsDatumP` is needed.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.StrongEpsP.Defs
import Submission.Work.FTS.StrongEps.GlueParts.contDiffWithinAt_concat_halfslab
import Submission.Work.FTS.StrongEps.GlueParts.contDiffOn_shiftFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 uncurry3 concat concat_apply_of_le concat_apply_of_gt)

/-! ## The slabs of the fake-time quadrant -/

/-- The closed slab `(0,∞) × (0,π/2) × [a,b]` of the fake-time quadrant (the domain of the joint
`C¹`-clause of `EpsRegP`). -/
def Qslab (a b : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc a b

theorem mem_Qslab {a b : ℝ} {q : P3} :
    q ∈ Qslab a b ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2 ∧ a ≤ q.2.2 ∧ q.2.2 ≤ b := by
  simp only [Qslab, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

/-! ## The shift of a one-sided derivative -/

/-- The fake-time shift of a one-sided derivative: if `f` has within-derivative `f'` on `[0,c]` at
`x - a`, then `y ↦ f (y - a)` has the same within-derivative on `[a, a+c]` at `x`. -/
theorem hasDerivWithinAt_comp_sub_Icc {f : ℝ → ℝ} {f' x a c : ℝ}
    (h : HasDerivWithinAt f f' (Set.Icc 0 c) (x - a)) :
    HasDerivWithinAt (fun y : ℝ => f (y - a)) f' (Set.Icc a (a + c)) x := by
  have hg : HasDerivWithinAt (fun y : ℝ => y - a) 1 (Set.Icc a (a + c)) x :=
    ((hasDerivAt_id (x := x)).sub_const a).hasDerivWithinAt
  have hst : MapsTo (fun y : ℝ => y - a) (Set.Icc a (a + c)) (Set.Icc 0 c) :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcomp := h.comp x hg hst
  rw [show (f ∘ fun y : ℝ => y - a) = (fun y : ℝ => f (y - a)) from rfl, mul_one] at hcomp
  exact hcomp

/-! ## The joint `C¹`-regularity of the concatenation -/

/-- The joint `C¹`-regularity clause of `EpsRegP` for the concatenated family: the pieces are `C¹`
on the closed slabs `[0,t]` and `[0,δ]`, agree at the junction as functions of `(z,θ)` and have
the same one-sided fake-time derivative `R` there, hence `uncurry3 (concat G (shiftFam H t) t)` is
`C¹` on `(0,∞) × (0,π/2) × [0,t+δ]`.  The junction `t` is a *common boundary* of the two slabs, so
this is `GlueParts.contDiffWithinAt_concat_halfslab` (at the junction) combined with the two
off-junction reductions to `hG` resp. `contDiffOn_shiftFam hH`. -/
theorem contDiffOn_concat_shiftFam {G H : Fam} {t δ : ℝ} {R : Fn} (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (uncurry3 G) (Qslab 0 t))
    (hH : ContDiffOn ℝ 1 (uncurry3 H) (Qslab 0 δ))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) :
    ContDiffOn ℝ 1 (uncurry3 (concat G (shiftFam H t) t)) (Qslab 0 (t + δ)) := by
  have hHt : ContDiffOn ℝ 1 (uncurry3 (shiftFam H t)) (Qslab t (t + δ)) :=
    Work.FTS.StrongEps.GlueParts.contDiffOn_shiftFam (H := H) (t := t) (δ := δ) hH
  intro q hq
  obtain ⟨hz, hθ0, hθ1, hτ0, hτ1⟩ := mem_Qslab.mp hq
  rcases lt_trichotomy q.2.2 t with hlt | heq | hgt
  · -- strictly before the junction: the concatenation agrees with `G`
    have hqUG : q ∈ Qslab 0 t := mem_Qslab.mpr ⟨hz, hθ0, hθ1, hτ0, le_of_lt hlt⟩
    have hUG : Qslab 0 t ∈ 𝓝[Qslab 0 (t + δ)] q := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨{y : P3 | y.2.2 < t}, ?_, ?_⟩
      · exact (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt
      · rintro y ⟨hylt, hyU⟩
        obtain ⟨h1, h2, h3, h4, -⟩ := mem_Qslab.mp hyU
        exact mem_Qslab.mpr ⟨h1, h2, h3, h4, le_of_lt hylt⟩
    refine ContDiffWithinAt.congr_of_eventuallyEq
      (f₁ := uncurry3 (concat G (shiftFam H t) t))
      ((hG.contDiffWithinAt hqUG).mono_of_mem_nhdsWithin hUG) ?_ ?_
    · show uncurry3 (concat G (shiftFam H t) t) =ᶠ[𝓝[Qslab 0 (t + δ)] q] uncurry3 G
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ y in 𝓝 (q : P3), y.2.2 < t from
          (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt)]
        with y hy
      exact concat_apply_of_le (le_of_lt hy)
    · exact concat_apply_of_le (le_of_lt hlt)
  · -- at the junction: the one-sided junction glue
    exact Work.FTS.StrongEps.GlueParts.contDiffWithinAt_concat_halfslab (G := G)
      (H := shiftFam H t) (R := R) (q := q)
      hδ hG hHt (fun z θ hz' hθ0' hθ1' => by
        rw [Work.FTS.StrongEps.shiftFam_apply, sub_self]
        exact hval z θ hz' hθ0' hθ1') hderG
      (fun z θ hz' hθ0' hθ1' => hasDerivWithinAt_comp_sub_Icc (f := fun s => H z θ s)
        (a := t) (c := δ) (x := t) (by simpa using hderH z θ hz' hθ0' hθ1')) hq heq
  · -- strictly after the junction: the concatenation agrees with the shifted `H`
    have hqUH : q ∈ Qslab t (t + δ) := mem_Qslab.mpr ⟨hz, hθ0, hθ1, le_of_lt hgt, hτ1⟩
    have hmemUH : Qslab t (t + δ) ∈ 𝓝[Qslab 0 (t + δ)] q := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨{y : P3 | t < y.2.2}, ?_, ?_⟩
      · exact (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt
      · rintro y ⟨hygt, hyU⟩
        obtain ⟨h1, h2, h3, -, h5⟩ := mem_Qslab.mp hyU
        exact mem_Qslab.mpr ⟨h1, h2, h3, le_of_lt hygt, h5⟩
    refine ContDiffWithinAt.congr_of_eventuallyEq
      (f₁ := uncurry3 (concat G (shiftFam H t) t))
      ((hHt.contDiffWithinAt hqUH).mono_of_mem_nhdsWithin hmemUH) ?_ ?_
    · show uncurry3 (concat G (shiftFam H t) t) =ᶠ[𝓝[Qslab 0 (t + δ)] q]
        uncurry3 (shiftFam H t)
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ y in 𝓝 (q : P3), t < y.2.2 from
          (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt)]
        with y hy
      exact concat_apply_of_gt hy
    · exact concat_apply_of_gt hgt

/-! ## The regularity glue of the `P₀`-scheme -/

theorem RegGlueP {α ε t δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G H : Work.FTS.Galerkin.Fam}
    {R : Work.FTS.Galerkin.Fn} (ht : 0 ≤ t) (hδ : 0 < δ)
    (hG : Work.FTS.StrongEps.EpsRegP α ρ ε t G) (hH : Work.FTS.StrongEps.EpsRegP α ρ ε δ H)
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) :
    Work.FTS.StrongEps.EpsRegP α ρ ε (t + δ)
      (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t) := by
  refine ⟨?_, ?_⟩
  · -- the joint `C¹`-regularity of the concatenation
    exact contDiffOn_concat_shiftFam (G := G) (H := H) (t := t) (δ := δ) (R := R) hδ
      hG.1 hH.1 hval hderG hderH
  · -- the datum bookkeeping: the slices are those of the two pieces
    intro τ hτ
    rcases le_or_gt τ t with hle | hlt
    · rw [Work.FTS.StrongGlobal.slice_concat_of_le (G := G) (H := shiftFam H t) (τ₀ := t)
        (τ := τ) hle]
      exact hG.2 τ ⟨hτ.1, hle⟩
    · rw [Work.FTS.StrongGlobal.slice_concat_of_gt (G := G) (H := shiftFam H t) (τ₀ := t)
        (τ := τ) hlt, Work.FTS.StrongEps.slice_shiftFam]
      exact hH.2 (τ - t) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩

end Work.FTS.StrongEps.StrongEpsP
