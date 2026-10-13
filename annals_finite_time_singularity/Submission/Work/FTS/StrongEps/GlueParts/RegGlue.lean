/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/GlueParts/RegGlue.lean` — the `EpsReg` glue of the `ε`-scheme

The continuation of the `ε`-scheme (`Work.FTS.StrongEps.EpsGlue`, and its restart-and-concatenate
core `Work.FTS.StrongEps.GlueParts.Induction.EpsGlue_of_glue`) restarts the local existence at a
junction time `t` and concatenates the pieces.  This module is the **regularity** glue: from a
regular `ε`-solution `G` on `[0,t]` and a restarted one `H` on `[0,δ]` whose zero slice is
`slice G t` (and whose fake-time derivatives match at the junction, both equal to `R`), the
concatenation `concat G (shiftFam H t) t` is a regular `ε`-solution on `[0, t+δ]`.

`EpsReg α ρ ε T g` is the conjunction of

* the joint `C¹`-regularity of `(z,θ,τ) ↦ g z θ τ` on `(0,∞) × (0,π/2) × [0,T]`, and
* `EpsDatum α ρ ε (slice g τ)` for every `τ ∈ [0,T]`.

The second clause is bookkeeping: for `τ ≤ t` the concatenated slice is literally `slice G τ`
(`StrongGlobal.slice_concat_of_le`) and for `t < τ` it is `slice H (τ-t)`
(`StrongGlobal.slice_concat_of_gt` + `slice_shiftFam`).  The first clause is the real content and
is concentrated at the **junction** `τ = t`, which is the *right* endpoint of the first piece's
slab and the *left* endpoint of the second's, so the interior-junction lemma of the library
(`StrongGlobal.contDiffOn_concat_1`) does not apply; the one-sided variant is
`GlueParts.contDiffWithinAt_concat_halfslab` (delegated), and the C¹-transfer of the shifted piece
is `GlueParts.contDiffOn_shiftFam` (delegated).  Off the junction the concatenation agrees with one
of the two pieces on a neighbourhood, so `ContDiffWithinAt.mono_of_mem_nhdsWithin` +
`ContDiffWithinAt.congr_of_eventuallyEq` reduce the statement to the pieces.

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
import Submission.Work.FTS.StrongEps.GlueParts.Basic
import Submission.Work.FTS.StrongEps.GlueParts.contDiffWithinAt_concat_halfslab
import Submission.Work.FTS.StrongEps.GlueParts.contDiffOn_shiftFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 uncurry3 concat concat_apply_of_le concat_apply_of_gt)

/-! ## The slabs of the fake-time quadrant -/

/-- The closed slab `(0,∞) × (0,π/2) × [a,b]` of the fake-time quadrant. -/
private def Qslab (a b : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc a b

private theorem mem_Qslab {a b : ℝ} {q : P3} :
    q ∈ Qslab a b ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2 ∧ a ≤ q.2.2 ∧ q.2.2 ≤ b := by
  simp only [Qslab, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

/-! ## The shift of a one-sided derivative -/

private theorem hasDerivWithinAt_comp_sub_Icc {f : ℝ → ℝ} {f' x a c : ℝ}
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

/-- The joint `C¹`-regularity clause of `EpsReg` for the concatenated family: the pieces are `C¹`
on the closed slabs `[0,t]` and `[0,δ]`, agree at the junction as functions of `(z,θ)` and have
the same one-sided fake-time derivative `R` there. -/
private theorem contDiffOn_concat_shiftFam {G H : Fam} {t δ : ℝ} {R : Fn} (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (uncurry3 G) (Qslab 0 t))
    (hH : ContDiffOn ℝ 1 (uncurry3 H) (Qslab 0 δ))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) :
    ContDiffOn ℝ 1 (uncurry3 (concat G (shiftFam H t) t)) (Qslab 0 (t + δ)) := by
  have hHt : ContDiffOn ℝ 1 (uncurry3 (shiftFam H t)) (Qslab t (t + δ)) :=
    contDiffOn_shiftFam (H := H) (t := t) (δ := δ) hH
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
    exact contDiffWithinAt_concat_halfslab (G := G) (H := shiftFam H t) (R := R) (q := q)
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

theorem RegGlue {α ε t δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G H : Work.FTS.Galerkin.Fam} {R : Work.FTS.Galerkin.Fn}
    (ht : 0 ≤ t) (hδ : 0 < δ)
    (hG : Work.FTS.StrongEps.EpsReg α ρ ε t G) (hH : Work.FTS.StrongEps.EpsReg α ρ ε δ H)
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ 0)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc 0 δ) 0) :
    Work.FTS.StrongEps.EpsReg α ρ ε (t + δ) (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t) := by
  refine ⟨?_, ?_⟩
  · exact contDiffOn_concat_shiftFam (G := G) (H := H) (t := t) (δ := δ) (R := R) hδ
      hG.1 hH.1 hval hderG hderH
  · intro τ hτ
    rcases le_or_gt τ t with hle | hlt
    · rw [Work.FTS.StrongGlobal.slice_concat_of_le (G := G) (H := shiftFam H t) (τ₀ := t)
        (τ := τ) hle]
      exact hG.2 τ ⟨hτ.1, hle⟩
    · rw [Work.FTS.StrongGlobal.slice_concat_of_gt (G := G) (H := shiftFam H t) (τ₀ := t)
        (τ := τ) hlt, Work.FTS.StrongEps.slice_shiftFam]
      exact hH.2 (τ - t) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩

end Work.FTS.StrongEps.GlueParts
