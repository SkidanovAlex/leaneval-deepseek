import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EpsRLX.WpUniformBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect.BoundaryTime

/-- **The right-hand time derivative of a slice, from the derivative within a product strip.**
If `u.uncurry` is differentiable within `univ ×ˢ I` at `(x, s₀)` with derivative `f'`, and the
time set `I` is a neighbourhood of `s₀` within `Ici s₀`, then the one sided derivative of the
slice `s ↦ u x s` at `s₀` (within `Ici s₀`) is `f' (0,1)`.

The proof is the chain rule `HasFDerivWithinAt.comp_of_tendsto` for the curve
`γ s = (x,s)`: `γ` maps `𝓝[Ici s₀] s₀` into `𝓝[univ ×ˢ I] (x, s₀)` because `γ` is continuous
and, eventually within `Ici s₀`, `γ s ∈ univ ×ˢ I` (this is where `hs` is used — for the strip
`I = Icc 0 S` and `s₀ = 0` the set `Icc 0 S` is indeed such a neighbourhood). -/
theorem hasDerivWithinAt_timeSlice_of_hasFDerivWithinAt
    {u : R3 → ℝ → R3} {I : Set ℝ} {x : R3} {s₀ : ℝ} {f' : (R3 × ℝ) →L[ℝ] R3}
    (hs : I ∈ 𝓝[Set.Ici s₀] s₀)
    (h : HasFDerivWithinAt (Function.uncurry u) f' (Set.univ ×ˢ I) (x, s₀)) :
    HasDerivWithinAt (fun t => u x t) (f' ((0 : R3), 1)) (Set.Ici s₀) s₀ := by
  have hmk0 : Tendsto (fun t : ℝ => ((x, t) : R3 × ℝ)) (𝓝[Set.Ici s₀] s₀)
      (𝓝 ((x, s₀) : R3 × ℝ)) :=
    (continuousAt_const.prodMk continuousAt_id).continuousWithinAt.tendsto
  have hmk : Tendsto (fun t : ℝ => ((x, t) : R3 × ℝ)) (𝓝[Set.Ici s₀] s₀)
      (𝓝[Set.univ ×ˢ I] ((x, s₀) : R3 × ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun t : ℝ => ((x, t) : R3 × ℝ)) hmk0 (by
        filter_upwards [hs] with t ht
        exact ⟨trivial, ht⟩)
  have hγ : HasFDerivWithinAt (fun t : ℝ => ((x, t) : R3 × ℝ)) (ContinuousLinearMap.inr ℝ R3 ℝ)
      (Set.Ici s₀) s₀ := (hasFDerivAt_prodMk_right x s₀).hasFDerivWithinAt
  have hcomp := h.comp_of_tendsto (x := s₀) hγ hmk
  have := hcomp.hasDerivWithinAt
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    Function.uncurry_apply_pair] using this

theorem velocity_strip_blocks {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) x = ω x t) :
    ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
        fderivWithin ℝ (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) p (0, 1))
      (Set.univ ×ˢ Set.Icc 0 S) ∧
    (∀ (x : Work.FTS.PressureOn.R3) (t : ℝ), t ∈ Set.Ioo 0 S →
      fderivWithin ℝ (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, t) (0, 1)
        = FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t) ∧
    (∀ x : Work.FTS.PressureOn.R3, HasDerivWithinAt
      (fun s => Work.FTS.Physical.physVel ω x s)
      (fderivWithin ℝ (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, 0) (0, 1))
      (Set.Ici 0) 0) := by
  have hS0 : 0 < S := hS.1
  -- the strip regularity at level `S`
  obtain ⟨hcd, -, -⟩ := hstrips S hS
  have hU : UniqueDiffOn ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) :=
    UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS0)
  have hcont : ContinuousOn
      (fderivWithin ℝ (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
      (Set.univ ×ˢ Set.Icc 0 S) := hcd.continuousOn_fderivWithin hU le_rfl
  -- (1) continuity of the time block on the closed strip
  have h1 : ContinuousOn (fun p : R3 × ℝ =>
      fderivWithin ℝ (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) p ((0 : R3), 1))
      (Set.univ ×ˢ Set.Icc 0 S) := hcont.clm_apply continuousOn_const
  -- (2) at interior times the within derivative is the two sided `timeDeriv`
  have h2 : ∀ (x : R3) (t : ℝ), t ∈ Set.Ioo 0 S →
      fderivWithin ℝ (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, t) ((0 : R3), 1)
        = timeDeriv (physVel ω) x t := by
    intro x t ht
    have hnhds : (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) ∈ 𝓝 (x, t) := by
      rw [nhds_prod_eq]
      exact prod_mem_prod univ_mem (Icc_mem_nhds ht.1 ht.2)
    rw [fderivWithin_of_mem_nhds hnhds]
    have hdiff : DifferentiableAt ℝ (physVel ω).uncurry (x, t) :=
      (hcd.contDiffAt hnhds).differentiableAt (by norm_num)
    rw [timeDeriv,
      (Work.FTS.PressureOn.Connect.hasDerivAt_slice_of_hasFDerivAt_uncurry
        (v := physVel ω) (x := x) (t := t) hdiff.hasFDerivAt).deriv]
  -- (3) at the boundary time the within derivative is the right derivative
  have hmem : Set.Icc (0 : ℝ) S ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [Iio_mem_nhds hS0] with t ht h0
    exact ⟨h0, ht.le⟩
  have h3 : ∀ x : R3, HasDerivWithinAt (fun s => physVel ω x s)
      (fderivWithin ℝ (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, 0) ((0 : R3), 1))
      (Set.Ici 0) 0 := by
    intro x
    have hx : (x, 0) ∈ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) :=
      ⟨trivial, le_refl 0, hS0.le⟩
    have hL : HasFDerivWithinAt (physVel ω).uncurry
        (fderivWithin ℝ (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, 0))
        (Set.univ ×ˢ Set.Icc 0 S) (x, 0) :=
      ((hcd.contDiffWithinAt hx).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    exact hasDerivWithinAt_timeSlice_of_hasFDerivWithinAt (I := Set.Icc 0 S) (s₀ := 0) hmem hL
  exact ⟨h1, h2, h3⟩

end Work.FTS.PressureOn.Connect.BoundaryTime
