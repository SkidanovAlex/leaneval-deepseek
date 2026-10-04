import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.ricNormSq_eq_ricSq_rmFrame
import Submission.Work.Diff.GE.rot_invariance
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.derivWithin_Ico_zero
import Submission.Work.Diff.GE.uhlenbeck_frame_kit
import Submission.Work.Diff.GE.scal_lapl_basic
import Submission.Work.Diff.GE.scal_lapl
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar curvature evolution `∂ₜ scal = Δ scal + 2|Ric|²` (kit)

This is the *scalar* counterpart of `Work.Diff.GE.evol_rm_normsq` (Hamilton's identity for `|Rm|²`).
Route (the lead's plan):

* the shared contract `CurvEvolution` gives, in an Uhlenbeck frame `e(s)` through `x`,
  `∂ₛ rmFrame = lapRmFrame + Q(rmFrame)`;
* `scalAlg` is linear, so `∂ₛ scalAlg(rmFrame) = scalAlg(lapRmFrame) + scalAlg(Q rmFrame)`;
* `scalAlg (Q R) = 2|Ric|²` for an algebraic curvature array (`Work.Diff.Alg.Pinch.scalAlg_Q`, H2);
* `scalAlg (lapRmFrame) = Δ(scalAlg ∘ rmFrame) = Δ scal` by `LapRmFrameParallel` applied to
  `ℓ = scalAlg`, plus frame independence (`scalAt_eq_scalAlg_rmFrame_of_isONFrame`);
* `scalAt (G s) x = scalAlg (rmFrame (G s) x (e s))` transfers the derivative to the frozen
  `scalAt`.

`CurvEvolution`, `LapRmFrameParallel`, the Uhlenbeck-frame existence and the continuity of the flow
quantities at `0` are taken as *hypotheses* here; the contract modules discharge them at the
assembly of `evol_scal.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## 5. The reaction term `scalAlg (Q R) = 2|Ric|²` for the curvature of `g` -/

/-- **Hamilton's reaction term on `scal`**: `scalAlg (Q R) = 2 |Ric|²` for the curvature array of the
Levi-Civita connection of `g` (H2, `Work.Diff.Alg.Pinch.scalAlg_Q`, plus `isAlgCurv_rmFrame_kit`). -/
theorem scalAlg_Q_rmFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    scalAlg (Q (rmFrame g x e)) = 2 * ricSq (rmFrame g x e) := by
  rw [Work.Diff.Alg.Pinch.scalAlg_Q _ (isAlgCurv_rmFrame_kit hLC g x e), ricSq]
  simp only [Work.Diff.Alg.Pinch.ric, pow_two]

/-! ## 6. The interior derivation of `EvolScal`, given an Uhlenbeck frame -/

/-- **Hamilton's scalar curvature identity in the interior of the flow interval**, given a family of
frames at `x`, orthonormal for `G s`, differentiable at `t` with the Uhlenbeck derivative
`⟨∂ₛeᵢ, eⱼ⟩ = Ric(eᵢ,eⱼ)`.

`scalAt (G s) x = scalAlg (rmFrame (G s) x (e s))` by frame independence, so the derivative is
`scalAlg ∘ (ΔR + Q(R))` by `CurvEvolution`; `scalAlg (Q R) = 2|Ric|²` is `scalAlg_Q_rmFrame`, and
`scalAlg (ΔR) = Δ scal` is `Work.Diff.GE.laplAt_scalAt_eq_scalAlg_lapRmFrame` (the scalar case of
`LapRmFrameParallel`, proved without any parallel frame). -/
theorem hasDerivAt_scalAt_of_CE_of_frame (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : ℝ → Fin (Module.finrank ℝ E) → E)
    (hON : ∀ s ∈ Set.Ico 0 T, IsONFrame (G s) x (e s))
    (hder : ∀ i, HasDerivWithinAt (fun s : ℝ ↦ e s i)
        ((∑ j, ricAt (lcOf (G t)) x (e t i) (e t j) • e t j
          : TangentSpace I x) : E) (Set.Ico 0 T) t) :
    HasDerivAt (fun s ↦ scalAt (G s) x)
      (laplAt (G t) (scalAt (G t)) x + 2 * ricNormSq (G t) x) t := by
  have htIco : t ∈ Set.Ico 0 T := ⟨ht.1.le, ht.2⟩
  have hne : Set.Ico 0 T ∈ 𝓝 t :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) fun y hy => ⟨hy.1.le, hy.2⟩
  -- (1) the Uhlenbeck derivative as an ordinary derivative at `t`
  have hderAt : ∀ i, HasDerivAt (fun s : ℝ ↦ ((e s i : TangentSpace I x) : E))
      (((∑ j, ricAt (lcOf (G t)) x (e t i) (e t j) • e t j
        : TangentSpace I x)) : E) t := by
    intro i
    exact (hder i).hasDerivAt hne
  -- (2) the componentwise evolution, from the shared contract
  have hframe : HasDerivAt (fun s ↦ rmFrame (G s) x (e s))
      (lapRmFrame (G t) x (e t) + Q (rmFrame (G t) x (e t))) t :=
    hCE G T hflow t ht x e (fun s hs => hON s ⟨hs.1.le, hs.2⟩) hderAt
  -- (3) `scalAlg` is linear
  have hscal := hasDerivAt_scalAlg_comp (n := Module.finrank ℝ E) _ _ t hframe
  -- (4) the two pieces of the value
  haveI hcov : ContMDiffCovariantDerivative (lcOf (G t)) ∞ := Classical.choice (hLC (G t)).1
  -- the scalar Laplacian identity (no parallel frame needed)
  have hLPval : scalAlg (lapRmFrame (G t) x (e t)) = laplAt (G t) (scalAt (G t)) x :=
    (laplAt_scalAt_eq_scalAlg_lapRmFrame (I := I) (M := M) hLC (G t) x (e t)
      (hON t htIco)).symm
  have hQ := scalAlg_Q_rmFrame hLC (G t) x (e t)
  have hric : ricSq (rmFrame (G t) x (e t)) = ricNormSq (G t) x :=
    (ricNormSq_eq_ricSq_rmFrame (G t) hcov x hn (e t) (hON t htIco)).symm
  have hval : scalAlg (lapRmFrame (G t) x (e t) + Q (rmFrame (G t) x (e t)))
      = laplAt (G t) (scalAt (G t)) x + 2 * ricNormSq (G t) x := by
    rw [← scalAlgL_apply (Module.finrank ℝ E)
        (lapRmFrame (G t) x (e t) + Q (rmFrame (G t) x (e t))),
      map_add, scalAlgL_apply, scalAlgL_apply, hLPval, hQ, hric]
  rw [hval] at hscal
  -- (5) transfer from `scalAlg (rmFrame ...)` to the frozen `scalAt`
  refine hscal.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact scalAt_eq_scalAlg_rmFrame_of_isONFrame (G s) hLC x (e s) (hON s ⟨hs.1.le, hs.2⟩)

/-- The interior derivation with the frame produced by the Uhlenbeck existence lemma. -/
theorem hasDerivAt_scalAt_of_CE (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (x : M) (hn : 0 < Module.finrank ℝ E) :
    HasDerivAt (fun s ↦ scalAt (G s) x)
      (laplAt (G t) (scalAt (G t)) x + 2 * ricNormSq (G t) x) t := by
  obtain ⟨e, hON, hder⟩ := uhlenbeck_frame_kit hLC G T hflow t ⟨ht.1.le, ht.2⟩ x
  exact hasDerivAt_scalAt_of_CE_of_frame hLC hCE G T hflow t ht x hn e hON hder

/-! ## 7. The endpoint `t = 0` -/

/-- **The endpoint `t = 0`**: the identity holds on `(0,T)`; at `0` it follows by the mean value
theorem (`derivWithin_Ico_zero`) once the two sides are known to be continuous at `0` from the
right.  This is the scalar analogue of `Work.Diff.GE.FlowContAtZero`. -/
def FlowContAtZeroScal : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ x : M,
    ContinuousWithinAt (fun s ↦ scalAt (G s) x) (Set.Ico 0 T) 0 ∧
    ContinuousWithinAt (fun s ↦ laplAt (G s) (scalAt (G s)) x + 2 * ricNormSq (G s) x)
      (Set.Ico 0 T) 0

theorem hasDerivWithinAt_scalAt_zero (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (hcont : FlowContAtZeroScal (I := I) (M := M))
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) (hT : 0 < T) (x : M)
    (hn : 0 < Module.finrank ℝ E) :
    HasDerivWithinAt (fun s ↦ scalAt (G s) x)
      (laplAt (G 0) (scalAt (G 0)) x + 2 * ricNormSq (G 0) x) (Set.Ico 0 T) 0 := by
  obtain ⟨hc1, hc2⟩ := hcont G T hflow x
  exact derivWithin_Ico_zero _ _ T hT
    (fun s hs => hasDerivAt_scalAt_of_CE hLC hCE G T hflow s hs x hn) hc1 hc2

/-- **EV3 modulo the shared contract**: `EvolScal` from `CurvEvolution` and the continuity of the
flow quantities at `0⁺`.  (`LapRmFrameParallel` is not needed: its scalar case is
`Work.Diff.GE.laplAt_scalAt_eq_scalAlg_lapRmFrame`.) -/
theorem evol_scal_of_CE_of_FlowCont (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (hcont : FlowContAtZeroScal (I := I) (M := M)) :
    EvolScal I M := by
  intro G T hflow t ht x
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    by_cases hn : 0 < Module.finrank ℝ E
    · exact hasDerivWithinAt_scalAt_zero hLC hCE hcont G T hflow ht.2 x hn
    · -- degenerate case `finrank ℝ E = 0`: all index sets are empty
      have hzero : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
      have hz : ∀ s : ℝ, scalAt (G s) x = 0 := by
        intro s
        simp only [scalAt, rmC, rmFrame, scalAlg]
        refine Finset.sum_eq_zero fun i _ => ?_
        refine Finset.sum_eq_zero fun j _ => ?_
        exact Fin.elim0 (hzero ▸ i)
      have hL0 : laplAt (G 0) (scalAt (G 0)) x + 2 * ricNormSq (G 0) x = 0 := by
        have h1 : laplAt (G 0) (scalAt (G 0)) x = 0 := by
          simp only [laplAt]
          refine Finset.sum_eq_zero fun i _ => ?_
          exact Fin.elim0 (hzero ▸ i)
        have h2 : ricNormSq (G 0) x = 0 := by
          simp only [ricNormSq, ricSq]
          refine Finset.sum_eq_zero fun i _ => ?_
          refine Finset.sum_eq_zero fun j _ => ?_
          exact Fin.elim0 (hzero ▸ i)
        rw [h1, h2]; ring
      have hfun : (fun s ↦ scalAt (G s) x) = fun _ : ℝ => 0 := by
        funext s; exact hz s
      rw [hfun, hL0]
      exact hasDerivWithinAt_const (c := (0 : ℝ)) (x := (0 : ℝ)) (s := Set.Ico 0 T)
  · by_cases hn : 0 < Module.finrank ℝ E
    · exact (hasDerivAt_scalAt_of_CE hLC hCE G T hflow t ⟨hpos, ht.2⟩ x hn).hasDerivWithinAt
    · -- degenerate case: the derivative of the identically zero function
      have hzero : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
      have hz : ∀ s : ℝ, scalAt (G s) x = 0 := by
        intro s
        simp only [scalAt, rmC, rmFrame, scalAlg]
        refine Finset.sum_eq_zero fun i _ => ?_
        refine Finset.sum_eq_zero fun j _ => ?_
        exact Fin.elim0 (hzero ▸ i)
      have hL0 : laplAt (G t) (scalAt (G t)) x + 2 * ricNormSq (G t) x = 0 := by
        have h1 : laplAt (G t) (scalAt (G t)) x = 0 := by
          simp only [laplAt]
          refine Finset.sum_eq_zero fun i _ => ?_
          exact Fin.elim0 (hzero ▸ i)
        have h2 : ricNormSq (G t) x = 0 := by
          simp only [ricNormSq, ricSq]
          refine Finset.sum_eq_zero fun i _ => ?_
          refine Finset.sum_eq_zero fun j _ => ?_
          exact Fin.elim0 (hzero ▸ i)
        rw [h1, h2]; ring
      have hfun : (fun s ↦ scalAt (G s) x) = fun _ : ℝ => 0 := by
        funext s; exact hz s
      rw [hfun, hL0]
      exact hasDerivWithinAt_const (c := (0 : ℝ)) (x := t) (s := Set.Ico 0 T)

end Work.Diff.GE
