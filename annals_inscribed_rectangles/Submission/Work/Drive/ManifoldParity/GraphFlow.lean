import Mathlib
import Submission.Work.Drive.ManifoldParity.GraphMap
import Submission.Work.Drive.exists_local_normalForm

/-!
# The flow line of a field tangent to a graph stays on the graph

`eq_graphMap_of_tangent_flow_right`: if `V` is a Lipschitz field tangent to the graph
`g = graphMap i η` at the graph point with the same `i`-th coordinate as a flow line `γ`, and `γ`
starts on the graph, then `γ` stays on the graph for positive times.

The defect `s ↦ γ s - g ((γ s) i)` has derivative
`V (γ s) - Dg ((γ s) i) ((V (γ s)) i)`, which by the tangency hypothesis equals
`(V (γ s) - V (g ((γ s) i))) - Dg ((γ s) i) ((V (γ s) - V (g ((γ s) i))) i)`, so its norm is bounded
by `(L + C L) ‖γ s - g ((γ s) i)‖`; Grönwall
(`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`) then gives that the defect vanishes.
-/

namespace Work.Drive.ManifoldParity

open Set Filter
open scoped Topology

noncomputable section

variable {m : ℕ}

/-- **A flow line of a field tangent to a graph stays on the graph (forward in time).** -/
theorem eq_graphMap_of_tangent_flow_right {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m}
    {V : Work.Drive.Amb m → Work.Drive.Amb m} {L : NNReal} (hL : LipschitzWith L V)
    {γ : ℝ → Work.Drive.Amb m} (hγ : ∀ s, HasDerivAt γ (V (γ s)) s)
    (hη : Differentiable ℝ η)
    {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) ε, ‖fderiv ℝ (graphMap i η) ((γ s) i)‖ ≤ C)
    (htan : ∀ s ∈ Set.Icc (0 : ℝ) ε, V (graphMap i η ((γ s) i)) =
      fderiv ℝ (graphMap i η) ((γ s) i) ((V (graphMap i η ((γ s) i))) i))
    (hinit : γ 0 = graphMap i η ((γ 0) i)) :
    ∀ s ∈ Set.Icc (0 : ℝ) ε, γ s = graphMap i η ((γ s) i) := by
  -- the `i`-th coordinate of the flow line
  have hud : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (γ t) i) ((V (γ s)) i) s := by
    intro s
    have h := (Work.Drive.coordL_hasFDerivAt (m := m) i (γ s)).comp s (hγ s).hasFDerivAt
    have h2 := h.hasDerivAt
    simpa [ContinuousLinearMap.comp_apply, Work.Drive.coordL_apply, Function.comp_def] using h2
  -- the graph curve
  have hgun : ∀ s : ℝ, HasDerivAt (fun t : ℝ => graphMap i η ((γ t) i))
      (fderiv ℝ (graphMap i η) ((γ s) i) ((V (γ s)) i)) s := by
    intro s
    have hg : HasFDerivAt (graphMap i η) (fderiv ℝ (graphMap i η) ((γ s) i)) ((γ s) i) :=
      (differentiableAt_graphMap (hη.differentiableAt (x := (γ s) i))).hasFDerivAt
    exact hg.comp_hasDerivAt s (hud s)
  -- the defect
  set n : ℝ → Work.Drive.Amb m := fun s => γ s - graphMap i η ((γ s) i) with hn
  have hnd : ∀ s : ℝ, HasDerivAt n (V (γ s) - fderiv ℝ (graphMap i η) ((γ s) i) ((V (γ s)) i)) s :=
    fun s => (hγ s).sub (hgun s)
  have hn0 : n 0 = 0 := by
    show γ 0 - graphMap i η ((γ 0) i) = 0
    exact sub_eq_zero.mpr hinit
  have hncont : ContinuousOn n (Set.Icc (0 : ℝ) ε) :=
    DifferentiableOn.continuousOn
      (fun s _ => (hnd s).differentiableAt.differentiableWithinAt)
  -- the Grönwall bound
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) ε,
      ‖V (γ s) - fderiv ℝ (graphMap i η) ((γ s) i) ((V (γ s)) i)‖ ≤
        ((L : ℝ) + C * (L : ℝ)) * ‖n s‖ := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) ε := ⟨hs.1, le_of_lt hs.2⟩
    have h2 : fderiv ℝ (graphMap i η) ((γ s) i)
        ((V (graphMap i η ((γ s) i))) i - (V (γ s)) i) =
        V (graphMap i η ((γ s) i)) - fderiv ℝ (graphMap i η) ((γ s) i) ((V (γ s)) i) := by
      rw [map_sub, (htan s hs').symm]
    have hkey : V (γ s) - fderiv ℝ (graphMap i η) ((γ s) i) ((V (γ s)) i) =
        (V (γ s) - V (graphMap i η ((γ s) i))) +
          fderiv ℝ (graphMap i η) ((γ s) i)
            ((V (graphMap i η ((γ s) i))) i - (V (γ s)) i) := by
      rw [h2]
      abel
    have hlip : ‖V (γ s) - V (graphMap i η ((γ s) i))‖ ≤ (L : ℝ) * ‖n s‖ := by
      have h := hL.dist_le_mul (γ s) (graphMap i η ((γ s) i))
      rw [dist_eq_norm] at h
      rw [dist_eq_norm] at h
      simpa only [hn] using h
    have hcoord : |(V (graphMap i η ((γ s) i))) i - (V (γ s)) i| ≤ (L : ℝ) * ‖n s‖ := by
      have h1 : |(V (graphMap i η ((γ s) i))) i - (V (γ s)) i| =
          ‖(V (graphMap i η ((γ s) i)) - V (γ s)) i‖ := by
        simp [Real.norm_eq_abs]
      rw [h1]
      refine (PiLp.norm_apply_le (V (graphMap i η ((γ s) i)) - V (γ s)) i).trans ?_
      have h := hL.dist_le_mul (graphMap i η ((γ s) i)) (γ s)
      rw [dist_eq_norm] at h
      rw [dist_eq_norm] at h
      rw [norm_sub_rev (graphMap i η ((γ s) i)) (γ s)] at h
      simpa only [hn] using h
    have hop : ‖fderiv ℝ (graphMap i η) ((γ s) i)
        ((V (graphMap i η ((γ s) i))) i - (V (γ s)) i)‖ ≤
        C * ((L : ℝ) * ‖n s‖) := by
      have h1 := (fderiv ℝ (graphMap i η) ((γ s) i)).le_opNorm
        ((V (graphMap i η ((γ s) i))) i - (V (γ s)) i)
      rw [Real.norm_eq_abs] at h1
      refine h1.trans ?_
      exact mul_le_mul (hC s hs') hcoord (abs_nonneg _) (le_trans (norm_nonneg _) (hC s hs'))
    calc ‖V (γ s) - fderiv ℝ (graphMap i η) ((γ s) i) ((V (γ s)) i)‖
        = ‖(V (γ s) - V (graphMap i η ((γ s) i))) +
            fderiv ℝ (graphMap i η) ((γ s) i)
              ((V (graphMap i η ((γ s) i))) i - (V (γ s)) i)‖ := by rw [hkey]
      _ ≤ ‖V (γ s) - V (graphMap i η ((γ s) i))‖ +
            ‖fderiv ℝ (graphMap i η) ((γ s) i)
              ((V (graphMap i η ((γ s) i))) i - (V (γ s)) i)‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖n s‖ + C * ((L : ℝ) * ‖n s‖) := add_le_add hlip hop
      _ = ((L : ℝ) + C * (L : ℝ)) * ‖n s‖ := by ring
  intro s hs
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := n) (f' := fun s => V (γ s) - fderiv ℝ (graphMap i η) ((γ s) i) ((V (γ s)) i))
    (K := (L : ℝ) + C * (L : ℝ)) (a := 0) (b := ε) hncont
    (fun x hx => (hnd x).hasDerivWithinAt) hn0 hbound s hs
  simp only [hn, sub_eq_zero] at hz
  exact hz

end

end Work.Drive.ManifoldParity
