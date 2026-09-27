import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.pairMeetDefs
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.ppParity.exists_ppReg_shift_strip_of_pieces_fixed
import Submission.Work.Drive.ppParity.piece_data_pp_strip
import Submission.Work.Drive.exists_eps_ppShift_avoidances

/-!
# `Work.Drive.ppParity.htube_of_strip`

The Sard-plus-avoidance package `htube` in the *strip* (repaired collar) convention, for an arbitrary
smooth `4`-manifold `M`: for every `ε' > 0` there is a perturbation parameter `t : ℝ⁸` of norm `< ε'`
at which

* every perturbed pair meet lying in the given set `K` is `PPRegAt` (in fact, by
  `Work.Drive.ppParity.exists_ppReg_shift_strip_of_pieces_fixed`, *every* perturbed pair meet in the
  box is regular), and
* every perturbed pair meet still avoids the four level faces `ftY2 ∈ {0,1}`, `ftZ2 ∈ {0,1}`
  (`Work.Drive.exists_eps_ppShift_avoidances`).

The statement is weaker than the `CappingSpace` package `Work.Drive.exists_ppTubeData`
(`ppDesignInputs.lean`) in that no compactness of `K` and no slab-covering hypothesis is asked for;
this is possible because the regularity input of the Sard
(`exists_ppReg_shift_strip_of_pieces_fixed`) is available on a *fixed* compact set containing the
nine-box in its interior, and regularity there is a statement about *all* box meets.  The set `K` of
the conclusion is therefore irrelevant and is simply ignored.
-/

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The nine-box lies in the closed ball of radius `4` about the origin.  (Every coordinate is in
`[0,1]`, so the Euclidean norm is at most `3`.) -/
private lemma norm_le_three_of_unitBox {x : EuclideanSpace ℝ (Fin 9)}
    (hx : x ∈ Submission.Drive.unitBox 8) : ‖x‖ ≤ 3 := by
  have h1 : ∀ i : Fin 9, ‖x i‖ ≤ 1 := by
    intro i
    have hi := hx i
    rw [Real.norm_eq_abs, abs_of_nonneg hi.1]
    exact hi.2
  have h2 : ‖x‖ ^ 2 ≤ 9 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i, ‖x.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 9, (1 : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have := h1 i
          nlinarith [norm_nonneg (x.ofLp i)]
      _ = 9 := by simp
  nlinarith [norm_nonneg x]

/-- Every point of the nine-box is an interior point of the closed ball of radius `4`. -/
private lemma unitBox_subset_interior_closedBall {x : EuclideanSpace ℝ (Fin 9)}
    (hx : x ∈ Submission.Drive.unitBox 8) :
    x ∈ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 9)) 4) := by
  refine interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball ?_
  rw [Metric.mem_ball, dist_zero_right]
  have h := norm_le_three_of_unitBox hx
  linarith

theorem htube_of_strip
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hΞsurj : ∀ (t : EuclideanSpace ℝ (Fin 4)) (p : M),
      Function.Surjective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' p) t))
    (w : ℝ → ℝ) (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hwstrip : ∀ s : ℝ, δ < s → s < 1 - δ → w s ≠ 0)
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Work.Drive.ppMeet E E' V W,
      (Work.Drive.ftS x ≤ δ ∨ 1 - δ ≤ Work.Drive.ftS x) → Work.Drive.PPRegAt E E' V W x)
    (hY : ∀ x ∈ Work.Drive.ppMeet E E' V W, Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1)
    (hZ : ∀ x ∈ Work.Drive.ppMeet E E' V W, Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1)
    (K : Set (EuclideanSpace ℝ (Fin 9))) :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε' ∧
      (∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W, x ∈ K →
        Work.Drive.PPRegAt (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W x) ∧
      (∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
        Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1 ∧
          Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1) := by
  intro ε' hε'
  -- ## continuity of the four blocks of the configuration
  have hΞc : Continuous (Function.uncurry Ξ) := hΞsm.continuous
  have hEc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E (ftS x) (ftU x) :=
    (contMDiff_composed_of hE).continuous
  have hE'c : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E' (ftS x) (ftU x) :=
    (contMDiff_composed_of hE').continuous
  have hVc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => V (ftY x) :=
    (contMDiff_comp_ftY hV).continuous
  have hWc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => W (ftZ x) :=
    (contMDiff_comp_ftZ hW).continuous
  -- ## the perturbation-stable level-face avoidances
  obtain ⟨εa, hεa, havoid⟩ :=
    exists_eps_ppShift_avoidances Ξ hΞ0 hΞc E E' V W w hw.continuous hEc hE'c hVc hWc hY hZ
  -- ## the repaired Sard on a fixed compact set containing the box in its interior
  obtain ⟨t, ht, hreg⟩ :=
    ppParity.exists_ppReg_shift_strip_of_pieces_fixed Ξ hΞ0 hΞsm hΞsurj w hw hδ hE hE' hV hW
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 9)) 4) (isCompact_closedBall _ _)
      (fun x _ h1 h2 => hwstrip (ftS x) h1 h2)
      (fun x hx _ _ => unitBox_subset_interior_closedBall hx)
      hwleft hwright
      (fun x _ hc hm => hregBase x hm hc)
      (fun p p' => ppParity.piece_data_pp_strip Ξ hΞsm hΞ0 w hw hδ hE hE' hV hW hwleft hwright
        (fun x _ hc hm => hregBase x hm hc) p p')
      (min ε' εa) (lt_min hε' hεa)
  refine ⟨t, lt_of_lt_of_le ht (min_le_left _ _), ?_, fun x hx =>
    havoid t (lt_of_lt_of_le ht (min_le_right _ _)) x hx⟩
  intro x hx _
  exact hreg x (mem_ppMeet.mp hx).1 hx

end

end Work.Drive.ppParity
