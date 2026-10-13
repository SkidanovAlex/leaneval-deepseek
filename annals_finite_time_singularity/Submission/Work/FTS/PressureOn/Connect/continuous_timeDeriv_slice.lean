import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_slice_of_hasFDerivAt_uncurry

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.FTS.PressureOn.Connect

/-- **Continuity in space of the time derivative of a joint `C^{1,α}` strip field.**

If `v.uncurry` is of class `C^{1,α}` on the closed strip `ℝ³ × [0,S]`, then at every *interior*
time `t ∈ (0,S)` the time derivative `x ↦ ∂ₜ v(x,t)` is a continuous function of `x`.

The point of the lemma is that the strip hypothesis controls the *joint* derivative of
`v.uncurry`: on the open sub-strip `ℝ³ × (t-ε, t+ε)` (which is a neighbourhood of every point
`(x,t)`, because `t` is interior to `[0,S]`) the map `(x,τ) ↦ fderiv ℝ v.uncurry (x,τ)` is
continuous (`ContDiffOn.continuousOn_fderiv_of_isOpen`), and evaluating it at the time direction
`(0,1)` gives exactly `∂ₜ v(x,τ)` for points of that open strip
(`hasDerivAt_slice_of_hasFDerivAt_uncurry`). -/
theorem continuous_timeDeriv_slice {α : NNReal} {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {S t : ℝ} (ht : t ∈ Set.Ioo 0 S)
    (hstrip : IsContDiffHolderOn ℝ α v.uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    Continuous (fun x : Work.FTS.PressureOn.R3 => FiniteTimeSingularity.timeDeriv v x t) := by
  obtain ⟨hcd, -, -⟩ := hstrip
  have ht0 : (0 : ℝ) < t := ht.1
  have htS : t < S := ht.2
  -- An open time-interval `J` around `t`, entirely inside `[0,S]`.
  set J : Set ℝ := Set.Ioo (t - min t (S - t) / 2) (t + min t (S - t) / 2) with hJ
  have hmin_pos : 0 < min t (S - t) := lt_min ht0 (sub_pos.mpr htS)
  have hJsub : J ⊆ Set.Icc (0 : ℝ) S := by
    intro s hs
    have h1 : min t (S - t) ≤ t := min_le_left _ _
    have h2 : min t (S - t) ≤ S - t := min_le_right _ _
    exact ⟨by linarith [hs.1, h1], by linarith [hs.2, h2]⟩
  have hJmem : J ∈ 𝓝 t := Ioo_mem_nhds (by linarith [hmin_pos]) (by linarith [hmin_pos])
  -- The open sub-strip and its derivative field.
  set str : Set (Work.FTS.PressureOn.R3 × ℝ) := Set.univ ×ˢ J with hstr
  have hstr_open : IsOpen str := isOpen_univ.prod isOpen_Ioo
  have hcd' : ContDiffOn ℝ 1 v.uncurry str :=
    hcd.mono (Set.prod_mono (subset_refl _) hJsub)
  have hcont : ContinuousOn (fderiv ℝ v.uncurry) str :=
    hcd'.continuousOn_fderiv_of_isOpen hstr_open le_rfl
  have hcont2 : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      fderiv ℝ v.uncurry p ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))) str :=
    hcont.clm_apply continuousOn_const
  have hstr_mem : ∀ x : Work.FTS.PressureOn.R3, str ∈ 𝓝 (x, t) := by
    intro x
    rw [hstr, nhds_prod_eq]
    exact prod_mem_prod univ_mem hJmem
  -- Continuity of `x ↦ fderiv ℝ v.uncurry (x,t) (0,1)`: restrict the continuous derivative
  -- field to the slice `τ = t`.
  have hmain : Continuous (fun x : Work.FTS.PressureOn.R3 =>
      fderiv ℝ v.uncurry (x, t) ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))) := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hg : ContinuousAt
        (fun p : Work.FTS.PressureOn.R3 × ℝ =>
          fderiv ℝ v.uncurry p ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))) (x0, t) :=
      hcont2.continuousAt (hstr_mem x0)
    have hpair : ContinuousAt (fun x : Work.FTS.PressureOn.R3 => (x, t)) x0 := by fun_prop
    exact ContinuousAt.comp (f := fun x : Work.FTS.PressureOn.R3 => (x, t)) hg hpair
  -- On the strip, the time derivative is exactly the evaluation of the joint derivative.
  refine hmain.congr fun x => ?_
  have hstripmem : Set.univ ×ˢ Set.Icc (0 : ℝ) S ∈ 𝓝 (x, t) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod univ_mem (Icc_mem_nhds ht0 htS)
  have hcdat : ContDiffAt ℝ 1 v.uncurry (x, t) := hcd.contDiffAt hstripmem
  have hdiff : DifferentiableAt ℝ v.uncurry (x, t) := hcdat.differentiableAt (by norm_num)
  have hfda : HasFDerivAt v.uncurry (fderiv ℝ v.uncurry (x, t)) (x, t) := hdiff.hasFDerivAt
  have hd := hasDerivAt_slice_of_hasFDerivAt_uncurry (v := v) hfda
  simp only [FiniteTimeSingularity.timeDeriv]
  exact hd.deriv.symm

end Work.FTS.PressureOn.Connect
