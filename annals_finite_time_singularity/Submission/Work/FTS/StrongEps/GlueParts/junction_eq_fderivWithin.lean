import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.GlueParts.Basic
import Submission.Work.FTS.StrongEps.GlueParts.Box

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.StrongGlobal (P3 concat uncurry3)

/-- At a *boundary* junction point `p = (z,θ,t)` (with `0 < t`) of the concatenation
`concat G H t` (`G` for `τ ≤ t`, `H` for `τ > t`) the two one-sided derivatives of the
concatenation agree.

`hA` (resp. `hB`) is a within-derivative of the concatenation on the left (resp. right) half of the
closed slab `U = (0,∞) × (0,π/2) × [0, t+δ]`, i.e. on `U ∩ {τ ≤ t}` (resp. `U ∩ {t ≤ τ}`); the
point `p` lies on the junction hyperplane `τ = t` and in `U`.  `hval` says the two pieces agree on
the hyperplane over the open quadrant of `(z,θ)`, and `hderG`/`hderH` give the one-sided fake-time
derivatives of the two pieces at `t`, both equal to `R`.

Proof (coordinate directions).  The `z`- and `θ`-directions of `cG` and `cH` are the corresponding
partial derivatives of the *same* function `uncurry3 (concat G H t)` at `p`
(`GlueParts.Basic`'s `hasFDerivWithinAt_apply_fst`/`_snd`), hence equal.  The `τ`-direction is
`R p.1 p.2.1` for both: on the left this is `hderG` restricted to `Icc (t-r) t`, on the right
`hderH` restricted to `Icc t (t+r)` together with `hval` at the single point `s = t`
(the concatenation equals `H` on `Icc t (t+r)`), and the derivatives within the closed intervals
are unique (`UniqueDiffWithinAt` for `Icc`). -/
theorem junction_eq_fderivWithin {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    {R : Work.FTS.Galerkin.Fn} {p : Work.FTS.StrongGlobal.P3} {cG cH : Work.FTS.StrongGlobal.P3 →L[ℝ] ℝ}
    (ht : 0 < t) (hδ : 0 < δ)
    (hpU : p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
    (hp4 : p.2.2 = t)
    (hA : HasFDerivWithinAt (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cG
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | q.2.2 ≤ t}) p)
    (hB : HasFDerivWithinAt (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cH
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | t ≤ q.2.2}) p)
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ t)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc t (t + δ)) t) :
    cG = cH := by
  have hz : 0 < p.1 := hpU.1
  have hθ0 : 0 < p.2.1 := hpU.2.1.1
  have hθ1 : p.2.1 < Real.pi / 2 := hpU.2.1.2
  have hτ0 : 0 ≤ p.2.2 := hpU.2.2.1
  have hτδ : p.2.2 ≤ t + δ := hpU.2.2.2
  have htδ : t ≤ t + δ := by linarith
  have hp4' : p.2.2 ≤ t := le_of_eq hp4
  -- membership in the two half slabs
  have memL : ∀ s θ τ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0 : ℝ) t →
      (s, θ, τ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | q.2.2 ≤ t} := by
    intro s θ τ hs hθ0' hθ1' hτ
    rw [Set.mem_Icc] at hτ
    exact ⟨⟨hs, ⟨hθ0', hθ1'⟩, ⟨hτ.1, le_trans hτ.2 htδ⟩⟩, hτ.2⟩
  have memR : ∀ s θ τ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc t (t + δ) →
      (s, θ, τ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | t ≤ q.2.2} := by
    intro s θ τ hs hθ0' hθ1' hτ
    rw [Set.mem_Icc] at hτ
    exact ⟨⟨hs, ⟨hθ0', hθ1'⟩, ⟨le_trans ht.le hτ.1, hτ.2⟩⟩, hτ.1⟩
  -- the `z`-direction: both sides read the common hyperplane profile `G ·· t`
  have he1 : cG ((1 : ℝ), 0, 0) = cH ((1 : ℝ), 0, 0) := by
    have hfun : (fun s : ℝ => uncurry3 (concat G H t) (s, p.2.1, p.2.2)) =
        (fun s : ℝ => G s p.2.1 t) := by
      funext s
      rw [Work.FTS.StrongGlobal.uncurry3_apply,
        Work.FTS.StrongGlobal.concat_apply_of_le hp4', hp4]
    have hGd : cG ((1 : ℝ), 0, 0) = deriv (fun s : ℝ => G s p.2.1 t) p.1 := by
      have h := hasFDerivWithinAt_apply_fst (c := cG) (x := p) (r := p.1 / 2) (by linarith) hA
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memL s p.2.1 p.2.2 (by linarith) hθ0 hθ1 ⟨hτ0, hp4'⟩)
      rw [h, hfun]
    have hHd : cH ((1 : ℝ), 0, 0) = deriv (fun s : ℝ => G s p.2.1 t) p.1 := by
      have h := hasFDerivWithinAt_apply_fst (c := cH) (x := p) (r := p.1 / 2) (by linarith) hB
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memR s p.2.1 p.2.2 (by linarith) hθ0 hθ1 ⟨le_of_eq hp4.symm, hτδ⟩)
      rw [h, hfun]
    exact hGd.trans hHd.symm
  -- the `θ`-direction: again the common hyperplane profile
  have he2 : cG ((0 : ℝ), 1, 0) = cH ((0 : ℝ), 1, 0) := by
    have hfun : (fun s : ℝ => uncurry3 (concat G H t) (p.1, s, p.2.2)) =
        (fun s : ℝ => G p.1 s t) := by
      funext s
      rw [Work.FTS.StrongGlobal.uncurry3_apply,
        Work.FTS.StrongGlobal.concat_apply_of_le hp4', hp4]
    set rθ : ℝ := min p.2.1 (Real.pi / 2 - p.2.1) / 2 with hrθdef
    have hrθ : 0 < rθ := by
      rw [hrθdef]
      have h : 0 < min p.2.1 (Real.pi / 2 - p.2.1) := lt_min hθ0 (by linarith)
      linarith
    have hrθ1 : rθ ≤ p.2.1 / 2 := by
      rw [hrθdef]; linarith [min_le_left p.2.1 (Real.pi / 2 - p.2.1)]
    have hrθ2 : rθ ≤ (Real.pi / 2 - p.2.1) / 2 := by
      rw [hrθdef]; linarith [min_le_right p.2.1 (Real.pi / 2 - p.2.1)]
    have hGd : cG ((0 : ℝ), 1, 0) = deriv (fun s : ℝ => G p.1 s t) p.2.1 := by
      have h := hasFDerivWithinAt_apply_snd (c := cG) (x := p) (r := rθ) hrθ hA
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memL p.1 s p.2.2 hz
            (by linarith) (by linarith) ⟨hτ0, hp4'⟩)
      rw [h, hfun]
    have hHd : cH ((0 : ℝ), 1, 0) = deriv (fun s : ℝ => G p.1 s t) p.2.1 := by
      have h := hasFDerivWithinAt_apply_snd (c := cH) (x := p) (r := rθ) hrθ hB
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memR p.1 s p.2.2 hz
            (by linarith) (by linarith) ⟨le_of_eq hp4.symm, hτδ⟩)
      rw [h, hfun]
    exact hGd.trans hHd.symm
  -- the `τ`-direction: both sides are `R p.1 p.2.1`
  have he3 : cG ((0 : ℝ), 0, 1) = cH ((0 : ℝ), 0, 1) := by
    have huL : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) t) t :=
      uniqueDiffWithinAt_Icc ht ⟨ht.le, le_rfl⟩
    have huR : UniqueDiffWithinAt ℝ (Set.Icc t (t + δ)) t :=
      uniqueDiffWithinAt_Icc (by linarith) ⟨le_rfl, by linarith⟩
    have hGτ : cG ((0 : ℝ), 0, 1) = R p.1 p.2.1 := by
      have h := hasFDerivWithinAt_apply_thd (a := (0 : ℝ)) (b := t) (c := cG) (x := p) hA
        (fun τ hτ => memL p.1 p.2.1 τ hz hθ0 hθ1 hτ)
      rw [hp4] at h
      have hcongr : Set.EqOn (fun s : ℝ => G p.1 p.2.1 s)
          (fun s : ℝ => uncurry3 (concat G H t) (p.1, p.2.1, s)) (Set.Icc (0 : ℝ) t) := by
        intro s hs
        rw [Set.mem_Icc] at hs
        change G p.1 p.2.1 s = uncurry3 (concat G H t) (p.1, p.2.1, s)
        rw [Work.FTS.StrongGlobal.uncurry3_apply,
          Work.FTS.StrongGlobal.concat_apply_of_le hs.2]
      have h1 : derivWithin (fun s : ℝ => G p.1 p.2.1 s) (Set.Icc (0 : ℝ) t) t =
          cG ((0 : ℝ), 0, 1) := by
        rw [derivWithin_congr hcongr
          (hcongr (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht.le, le_rfl⟩)), h.derivWithin huL]
      have h2 := (hderG p.1 p.2.1 hz hθ0 hθ1).derivWithin huL
      rw [← h2, ← h1]
    have hHτ : cH ((0 : ℝ), 0, 1) = R p.1 p.2.1 := by
      have h := hasFDerivWithinAt_apply_thd (a := t) (b := t + δ) (c := cH) (x := p) hB
        (fun τ hτ => memR p.1 p.2.1 τ hz hθ0 hθ1 hτ)
      rw [hp4] at h
      have hcongr : Set.EqOn (fun s : ℝ => H p.1 p.2.1 s)
          (fun s : ℝ => uncurry3 (concat G H t) (p.1, p.2.1, s)) (Set.Icc t (t + δ)) := by
        intro s hs
        rw [Set.mem_Icc] at hs
        change H p.1 p.2.1 s = uncurry3 (concat G H t) (p.1, p.2.1, s)
        rcases lt_or_eq_of_le hs.1 with hlt | heq
        · rw [Work.FTS.StrongGlobal.uncurry3_apply,
            Work.FTS.StrongGlobal.concat_apply_of_gt hlt]
        · rw [← heq, Work.FTS.StrongGlobal.uncurry3_apply,
            Work.FTS.StrongGlobal.concat_apply_of_le (le_refl t), hval p.1 p.2.1 hz hθ0 hθ1]
      have h1 : derivWithin (fun s : ℝ => H p.1 p.2.1 s) (Set.Icc t (t + δ)) t =
          cH ((0 : ℝ), 0, 1) := by
        rw [derivWithin_congr hcongr
          (hcongr (show t ∈ Set.Icc t (t + δ) from ⟨le_rfl, by linarith⟩)), h.derivWithin huR]
      have h2 := (hderH p.1 p.2.1 hz hθ0 hθ1).derivWithin huR
      rw [← h2, ← h1]
    exact hGτ.trans hHτ.symm
  -- assemble: `cG = cH` from equality on the three basis vectors
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1 • (((1 : ℝ), 0, 0) : P3) + v.2.1 • (((0 : ℝ), 1, 0) : P3)
      + v.2.2 • (((0 : ℝ), 0, 1) : P3) := by
    ext <;> simp
  rw [hv]
  simp only [map_add, map_smul, smul_eq_mul, he1, he2, he3]

end Work.FTS.StrongEps.GlueParts
