import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.GlueParts.Basic
import Submission.Work.FTS.StrongEps.GlueParts.junction_eq_fderivWithin
import Submission.Work.FTS.StrongEps.GlueParts.continuousOn_junctionStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam)
open Work.FTS.StrongGlobal (P3 concat uncurry3 concat_apply_of_le concat_apply_of_gt)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The main case `0 < t`

The proof is factored so that the two genuinely independent inputs are explicit hypotheses of the
private lemma `key`:

* `hjunc0` — the agreement of the two one-sided derivative fields at every junction point of the
  closed slab (the *boundary junction comparison*, proved in
  `GlueParts/junction_eq_fderivWithin.lean`);
* `hcontFact` — the continuity on the closed slab of the piecewise derivative field, as a function
  of that agreement (proved in `GlueParts/continuousOn_junctionStep.lean`).

This lets the body of `key` (the derivative field, the union over the two closed halves, and the
`C¹`-characterisation) be developed and checked independently of those two inputs. -/

/-- The main case (`0 < t`) of the boundary junction glue. -/
private theorem key {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    {R : Work.FTS.Galerkin.Fn} {q : Work.FTS.StrongGlobal.P3}
    (htpos : 0 < t) (hδ : 0 < δ)
    (hjunc0 : ∀ (p : Work.FTS.StrongGlobal.P3) (cG cH : Work.FTS.StrongGlobal.P3 →L[ℝ] ℝ),
        p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ) →
        p.2.2 = t →
        HasFDerivWithinAt
          (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cG
          ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
            {r : Work.FTS.StrongGlobal.P3 | r.2.2 ≤ t}) p →
        HasFDerivWithinAt
          (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cH
          ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
            {r : Work.FTS.StrongGlobal.P3 | t ≤ r.2.2}) p →
        cG = cH)
    (hcontFact : (∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ), p.2.2 = t →
        fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p =
        fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p) →
      ContinuousOn (fun p : Work.FTS.StrongGlobal.P3 =>
          if p.2.2 ≤ t then
            fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p
          else
            fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)))
    (hG : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 G)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t))
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ t)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc t (t + δ)) t)
    (hq : q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
    (hqt : q.2.2 = t) :
    ContDiffWithinAt ℝ 1
      (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) q := by
  -- the two half-slabs
  let UG : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t
  let UH : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)
  let U : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)
  let Ψ : P3 → ℝ := uncurry3 (concat G H t)
  let f' : P3 → P3 →L[ℝ] ℝ := fun p : P3 =>
    if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
    else fderivWithin ℝ (uncurry3 H) UH p
  -- differentiability of each piece on its own half-slab
  have hdG : ∀ p ∈ UG,
      HasFDerivWithinAt (uncurry3 G) (fderivWithin ℝ (uncurry3 G) UG p) UG p :=
    fun p hp => (hG.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
  have hdH : ∀ p ∈ UH,
      HasFDerivWithinAt (uncurry3 H) (fderivWithin ℝ (uncurry3 H) UH p) UH p :=
    fun p hp => (hH.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
  -- the agreement of the two one-sided derivative fields at the junction points of the slab
  have hjunc : ∀ p ∈ U, p.2.2 = t →
      fderivWithin ℝ (uncurry3 G) UG p = fderivWithin ℝ (uncurry3 H) UH p := by
    intro p hpU hp4
    have hpUG : p ∈ UG := ⟨hpU.1, hpU.2.1, ⟨hpU.2.2.1, le_of_eq hp4⟩⟩
    have hpUH : p ∈ UH := ⟨hpU.1, hpU.2.1, ⟨le_of_eq hp4.symm, hpU.2.2.2⟩⟩
    have hA : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
        (U ∩ {r : P3 | r.2.2 ≤ t}) p :=
      ((hdG p hpUG).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.1.2.2.1, hr.2⟩⟩)).congr
        (fun r hr => by
          show concat G H t r.1 r.2.1 r.2.2 = G r.1 r.2.1 r.2.2
          rw [concat_apply_of_le hr.2])
        (by
          show concat G H t p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
          rw [concat_apply_of_le (le_of_eq hp4)])
    have hB : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p)
        (U ∩ {r : P3 | t ≤ r.2.2}) p :=
      ((hdH p hpUH).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.2, hr.1.2.2.2⟩⟩)).congr
        (fun r hr => by
          show concat G H t r.1 r.2.1 r.2.2 = H r.1 r.2.1 r.2.2
          have hr2 : t ≤ r.2.2 := by simpa using hr.2
          rcases lt_or_eq_of_le hr2 with hlt | hEq
          · rw [concat_apply_of_gt hlt]
          · rw [concat_apply_of_le (le_of_eq hEq.symm), hEq.symm]
            exact hval r.1 r.2.1 hr.1.1 hr.1.2.1.1 hr.1.2.1.2)
        (by
          show concat G H t p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
          rw [concat_apply_of_le (le_of_eq hp4), hp4]
          exact hval p.1 p.2.1 hpU.1 hpU.2.1.1 hpU.2.1.2)
    exact hjunc0 p (fderivWithin ℝ (uncurry3 G) UG p) (fderivWithin ℝ (uncurry3 H) UH p)
      hpU hp4 hA hB
  -- continuity of the piecewise derivative field
  have hcont : ContinuousOn f' U := hcontFact hjunc
  -- the derivative of the concatenation at every point of the slab
  have hderiv : ∀ p ∈ U, HasFDerivWithinAt Ψ (f' p) U p := by
    intro p hpU
    rcases lt_trichotomy p.2.2 t with hlt | heq | hgt
    · -- strictly before the junction
      have hpUG : p ∈ UG := ⟨hpU.1, hpU.2.1, ⟨hpU.2.2.1, le_of_lt hlt⟩⟩
      have h1 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          (U ∩ {r : P3 | r.2.2 < t}) p :=
        ((hdG p hpUG).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.1.2.2.1, le_of_lt hr.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = G r.1 r.2.1 r.2.2
            rw [concat_apply_of_le (le_of_lt hr.2)])
          (by
            show concat G H t p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
            rw [concat_apply_of_le (le_of_lt hlt)])
      have h2 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p) U p :=
        h1.mono_of_mem_nhdsWithin (by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{r : P3 | r.2.2 < t},
            (isOpen_lt (by fun_prop) continuous_const).mem_nhds hlt,
            fun r hr => ⟨hr.2, hr.1⟩⟩)
      have hfp : f' p = fderivWithin ℝ (uncurry3 G) UG p := by
        show (if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
            else fderivWithin ℝ (uncurry3 H) UH p) = fderivWithin ℝ (uncurry3 G) UG p
        rw [if_pos (le_of_lt hlt)]
      rw [hfp]
      exact h2
    · -- on the junction hyperplane: glue the two one-sided derivatives
      have hpUG : p ∈ UG := ⟨hpU.1, hpU.2.1, ⟨hpU.2.2.1, le_of_eq heq⟩⟩
      have hpUH : p ∈ UH := ⟨hpU.1, hpU.2.1, ⟨le_of_eq heq.symm, hpU.2.2.2⟩⟩
      have h1 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          (U ∩ {r : P3 | r.2.2 ≤ t}) p :=
        ((hdG p hpUG).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.1.2.2.1, hr.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = G r.1 r.2.1 r.2.2
            rw [concat_apply_of_le hr.2])
          (by
            show concat G H t p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
            rw [concat_apply_of_le (le_of_eq heq)])
      have h2 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p)
          (U ∩ {r : P3 | t ≤ r.2.2}) p :=
        ((hdH p hpUH).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.2, hr.1.2.2.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = H r.1 r.2.1 r.2.2
            have hr2 : t ≤ r.2.2 := by simpa using hr.2
            rcases lt_or_eq_of_le hr2 with hlt | hEq
            · rw [concat_apply_of_gt hlt]
            · rw [concat_apply_of_le (le_of_eq hEq.symm), hEq.symm]
              exact hval r.1 r.2.1 hr.1.1 hr.1.2.1.1 hr.1.2.1.2)
          (by
            show concat G H t p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
            rw [concat_apply_of_le (le_of_eq heq), heq]
            exact hval p.1 p.2.1 hpU.1 hpU.2.1.1 hpU.2.1.2)
      have h2' : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          (U ∩ {r : P3 | t ≤ r.2.2}) p := by
        rw [hjunc p hpU heq]
        exact h2
      have hunion : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          ((U ∩ {r : P3 | r.2.2 ≤ t}) ∪ (U ∩ {r : P3 | t ≤ r.2.2})) p :=
        h1.union h2'
      have hcov : (U ∩ {r : P3 | r.2.2 ≤ t}) ∪ (U ∩ {r : P3 | t ≤ r.2.2}) = U := by
        ext r
        constructor
        · rintro (hr | hr) <;> exact hr.1
        · intro hr
          rcases le_total r.2.2 t with h | h
          · exact Or.inl ⟨hr, h⟩
          · exact Or.inr ⟨hr, h⟩
      rw [hcov] at hunion
      have hfp : f' p = fderivWithin ℝ (uncurry3 G) UG p := by
        show (if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
            else fderivWithin ℝ (uncurry3 H) UH p) = fderivWithin ℝ (uncurry3 G) UG p
        rw [if_pos (le_of_eq heq)]
      rw [hfp]
      exact hunion
    · -- strictly after the junction
      have hpUH : p ∈ UH := ⟨hpU.1, hpU.2.1, ⟨le_of_lt hgt, hpU.2.2.2⟩⟩
      have h1 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p)
          (U ∩ {r : P3 | t < r.2.2}) p :=
        ((hdH p hpUH).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨le_of_lt hr.2, hr.1.2.2.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = H r.1 r.2.1 r.2.2
            rw [concat_apply_of_gt hr.2])
          (by
            show concat G H t p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
            rw [concat_apply_of_gt hgt])
      have h2 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p) U p :=
        h1.mono_of_mem_nhdsWithin (by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{r : P3 | t < r.2.2},
            (isOpen_lt continuous_const (by fun_prop)).mem_nhds hgt,
            fun r hr => ⟨hr.2, hr.1⟩⟩)
      have hfp : f' p = fderivWithin ℝ (uncurry3 H) UH p := by
        show (if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
            else fderivWithin ℝ (uncurry3 H) UH p) = fderivWithin ℝ (uncurry3 H) UH p
        rw [if_neg (not_le.mpr hgt)]
      rw [hfp]
      exact h2
  -- the `C¹`-characterisation on the closed slab
  have hmain : ContDiffWithinAt ℝ ((0 : WithTop ℕ∞) + 1) (uncurry3 (concat G H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) q := by
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (𝕜 := ℝ) (n := (0 : WithTop ℕ∞))
      (f := uncurry3 (concat G H t))
      (s := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
      (x := q) (by norm_num)]
    refine ⟨U, ?_, ?_, f', hderiv, ?_⟩
    · rw [Set.insert_eq_of_mem hq]
      exact self_mem_nhdsWithin
    · intro h
      exact absurd h (by simp)
    · refine (contDiffWithinAt_zero hq).mpr ⟨U, self_mem_nhdsWithin, ?_⟩
      rwa [Set.inter_self]
  exact hmain

/-- **The junction glue for the joint `C¹`-regularity at a *boundary* junction.**

Two families `G`, `H` are jointly `C¹` on the two closed half-slabs `τ ≤ t` resp. `τ ≥ t` of fake
time (open quadrant in `(z,θ)`); they agree on the hyperplane `τ = t` over the open quadrant
(`hval`) and their fake-time one-sided derivatives there agree, both being `R` (`hderG`, `hderH`).
Then the concatenation `concat G H t` (`G` for `τ ≤ t`, `H` for `τ > t`) is jointly `C¹` *within*
the closed slab `τ ∈ [0, t+δ]` at every point `q` of that slab on the junction hyperplane `τ = t`.
This is the boundary-junction version of `Work.FTS.StrongGlobal.contDiffOn_concat_1` (which needs
the junction to be *interior* to both slabs, achieved there by one unit of slack).

Route.  Write `UG = Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 t`, `UH = Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc t (t+δ)`,
`U = Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 (t+δ)`, `f = uncurry3 (concat G H t)`, and fix a junction point
`q = (x,y,t) ∈ U` (so `0 ≤ t`; the case `t = 0` is degenerate: then `f = H` on `U` by `hval`).
Use `contDiffWithinAt_succ_iff_hasFDerivWithinAt` with `n = 0` on the slab `U` itself (which is a
neighbourhood of `q` within `insert q U`).  On `U` take
`f' p = if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p else fderivWithin ℝ (uncurry3 H) UH p`.
(i) `HasFDerivWithinAt f (f' p) U p` for `p ∈ U`: off the junction this is the within-derivative of
the relevant piece on `U ∩ {τ < t}` (resp. `U ∩ {t < τ}`), upgraded to `U` by
`HasFDerivWithinAt.mono_of_mem_nhdsWithin`; at a junction point `p` glue the two one-sided
derivatives with `HasFDerivWithinAt.union` over `U ∩ {τ ≤ t}` and `U ∩ {τ ≥ t}`
(`Work.FTS.StrongEps.GlueParts.junction_eq_fderivWithin` supplies the agreement of the two
branches there).
(ii) `ContDiffWithinAt ℝ 0 f' U q` (`ContinuousOn f' U`), i.e. `f'` continuous on the slab: on
`U ∩ {τ ≤ t}` it is `fderivWithin ℝ (uncurry3 G) UG`, continuous on `UG` by
`ContDiffOn.continuousOn_fderivWithin` (`UniqueDiffOn` from `uniqueDiffOn_Ioi`, `uniqueDiffOn_Ioo`,
`uniqueDiffOn_Icc`, `UniqueDiffOn.prod`); likewise on the right half `U ∩ {τ ≥ t}`, which splits as
`{τ = t} ∪ {t < τ}`: on the first part `f'` is again the `G`-branch (its value at `p` included) and
on the second the `H`-branch, whose value at a junction point is identified with that of `f'` by
(i); combine with `ContinuousWithinAt.union`.  This is
`Work.FTS.StrongEps.GlueParts.continuousOn_junctionStep`. -/
theorem contDiffWithinAt_concat_halfslab {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    {R : Work.FTS.Galerkin.Fn} {q : Work.FTS.StrongGlobal.P3} (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 G)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t))
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ t)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc t (t + δ)) t)
    (hq : q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
    (hqt : q.2.2 = t) :
    ContDiffWithinAt ℝ 1 (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) q := by
  by_cases h0 : t = 0
  · -- degenerate case: on the slab the concatenation *is* `H` (by `hval` on the hyperplane `τ = 0`)
    subst h0
    have hEqOn : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (0 + δ),
        uncurry3 (concat G H 0) p = uncurry3 H p := by
      intro p hp
      show concat G H 0 p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
      rcases lt_or_ge (0 : ℝ) p.2.2 with h | h
      · rw [concat_apply_of_gt h]
      · have hp0 : p.2.2 = 0 := le_antisymm h hp.2.2.1
        rw [concat_apply_of_le h, hp0]
        exact hval p.1 p.2.1 hp.1 hp.2.1.1 hp.2.1.2
    exact (hH.contDiffWithinAt hq).congr hEqOn (hEqOn q hq)
  · -- main case
    have ht0 : 0 ≤ t := hqt ▸ hq.2.2.1
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
    refine key (G := G) (H := H) (t := t) (δ := δ) (R := R) (q := q) htpos hδ ?_ ?_
      hG hH hval hderG hderH hq hqt
    · -- the junction comparison of the two one-sided derivative fields
      intro p cG cH hpU hp4 hA hB
      exact junction_eq_fderivWithin (G := G) (H := H) (t := t) (δ := δ) (R := R) (p := p)
        (cG := cG) (cH := cH) htpos hδ hpU hp4 hA hB hval hderG hderH
    · -- continuity of the piecewise derivative field
      exact continuousOn_junctionStep (G := G) (H := H) (t := t) (δ := δ) htpos hδ hG hH

end Work.FTS.StrongEps.GlueParts
