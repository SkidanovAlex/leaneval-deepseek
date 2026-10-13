import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_of_hasDerivWithinAt_Ici

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

-- required full name (path convention): Work.FTS.PressureOn.Connect.hasDerivAt_omega_slice_at
theorem hasDerivAt_omega_slice_at {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T t : ℝ}
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s)
    (hcontDt : ContinuousOn (fun q : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s)
    (ht : t ∈ Set.Ioo 0 T) (y : Work.FTS.PressureOn.R3) :
    HasDerivAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t := by
  obtain ⟨ht0, htT⟩ := ht
  -- Choose an intermediate time `S` with `t < S < T`: the hypotheses are local near `t`, and
  -- every strip hypothesis is available strictly below `T`.
  set S : ℝ := (t + T) / 2 with hSdef
  have hS0 : 0 < S := by rw [hSdef]; linarith
  have hST : S < T := by rw [hSdef]; linarith
  have htS : t < S := by rw [hSdef]; linarith
  have hS : S ∈ Set.Ioo 0 T := ⟨hS0, hST⟩
  -- `s ↦ ω y s` is continuous on `[0,S]`, being the curl of the spatial derivative of the
  -- jointly `C^{1,α}` field `physVel ω`.
  have hg : ContinuousOn (fun s => ω y s) (Set.Icc 0 S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl y
  -- `s ↦ ∂ₜω y s` is continuous on `[0,S)`.
  have hpair : ContinuousOn (fun s : ℝ => ((y, s) : Work.FTS.PressureOn.R3 × ℝ))
      (Set.Ico 0 S) := (continuous_const.prodMk continuous_id).continuousOn
  have hc : ContinuousOn (fun s : ℝ => FiniteTimeSingularity.timeDeriv ω y s) (Set.Ico 0 S) :=
    hcontDt.comp hpair
      (fun s hs => ⟨Set.mem_univ _, ⟨hs.1, lt_of_lt_of_le hs.2 (le_of_lt hST)⟩⟩)
  -- and the one-sided (right) derivative identity holds on `[0,S)`.
  have hd : ∀ s ∈ Set.Ico 0 S,
      HasDerivWithinAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y s) (Set.Ici s) s :=
    fun s hs => hderiv y s ⟨hs.1, lt_of_lt_of_le hs.2 (le_of_lt hST)⟩
  exact hasDerivAt_of_hasDerivWithinAt_Ici ⟨ht0, htS⟩ hg hc hd

end Work.FTS.PressureOn.Connect
