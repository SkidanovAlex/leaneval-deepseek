/-
  Work.WilE2 — the local connectivity of `cubeC k ∩ Zset c f`.

  `X = cubeC k ∩ Zset c f` is the zero set of a finite family of EA polynomials on the chain `c`,
  cut by the closed cube.  The proof has three parts.

  * **Finitely many components in every local box.**  `VarietyBound (k + r)` — the Khovanskii /
    Gabrielov–Vorobjov component bound for EA varieties in the cube, `varietyBound_all` below —
    gives, uniformly in the format `k + r`, a finite hitting set for the components of
    `cubeC k ∩ Zset c' g'`.  Via the diagonal affine reparametrisation of `BoxLocDefs` this
    applies to *every* axis-parallel box `axBox a b = ∏ᵢ [aᵢ, bᵢ]`:
    `boxMap a b '' (cubeC k ∩ Zset (boxChain c a b) (g.image (boxSub a b))) = axBox a b ∩ Zset c g`
    (`Work.WilE2.BoxLoc.boxMap_image_Zset`), and a homeomorphism carries components to components
    (`Work.WilE2.WilE2Aux.finite_range_componentIn_image_of_hits`), so
    `axBox a b ∩ Zset c g` has only finitely many components
    (`finite_components_axBox_inter_Zset`).
  * **Finitely many components in every local ball of `X`.**  For `x ∈ cubeC k` and `δ > 0` the
    trace of the ball is a box `cubeC k ∩ closedBall x δ = axBox (max (xᵢ-δ) (-1)) (min (xᵢ+δ) 1)`
    (`cubeC_inter_closedBall`), hence `X ∩ closedBall x δ` has finitely many components
    (`finite_components_cubeC_Zset_closedBall`).
  * **A closed set with finitely many components in every ball is locally connected**
    (`Work.WilE2.WilE2Aux.locallyConnectedSpace_of_component_finite`): the component of `x` in
    `X ∩ closedBall x δ` then is a neighbourhood of `x` in `X` — the other components, being
    finitely many closed sets avoiding `x`, stay a positive distance away.
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE2.VcbTopology
import Submission.Work.WilE2.BoxLocDefs
import Submission.Work.WilE2.variety_components_bound
import Submission.Work.WilE2.E2_khovanskii_proved
import Submission.Work.WilE2.BoxLoc.boxMap_image_Zset
import Submission.Work.WilE2.WilE2Aux.finite_range_componentIn_image_of_hits
import Submission.Work.WilE2.WilE2Aux.locallyConnectedSpace_of_component_finite

set_option autoImplicit false
noncomputable section

namespace Work.WilE2

open Classical Set
open WilkiesDesign WilkiesDesign.E

/-- **The variety bound, unconditionally.**  The Gabrielov–Vorobjov Corollary 3.3 component bound
for EA varieties on the cube, assembled from the two inputs of `variety_components_bound`:
Khovanskii's bound for non-degenerate zeros (`E2_khovanskii_proved`) and the density of regular
values of a rectangular `C²` map (`regular_values_dense`). -/
theorem varietyBound_all (F : ℕ) : VarietyBound F :=
  variety_components_bound (fun F => E2_khovanskii_proved F)
    (fun _ G hG y₀ ε hε => regular_values_dense G hG y₀ ε hε) F

/-- The lower side of the box `cubeC k ∩ closedBall x δ` at `x ∈ cubeC k`, `δ > 0`. -/
def lcLo {k : ℕ} (x : Fin k → ℝ) (δ : ℝ) : Fin k → ℝ := fun i => max (x i - δ) (-1)

/-- The upper side of the box `cubeC k ∩ closedBall x δ`. -/
def lcHi {k : ℕ} (x : Fin k → ℝ) (δ : ℝ) : Fin k → ℝ := fun i => min (x i + δ) 1

/-- The sides of the local box are non-degenerate at a point of the cube. -/
theorem lcLo_lt_lcHi {k : ℕ} {x : Fin k → ℝ} (hx : x ∈ cubeC k) {δ : ℝ} (hδ : 0 < δ) :
    ∀ i, lcLo x δ i < lcHi x δ i := by
  intro i
  have h := hx i
  rw [abs_le] at h
  rcases le_total (x i - δ) (-1) with h1 | h1 <;> rcases le_total (x i + δ) 1 with h2 | h2 <;>
    simp only [lcLo, lcHi, max_eq_left h1, max_eq_right h1, min_eq_left h2, min_eq_right h2] <;>
    linarith

/-- The trace of a ball centred at a point of the cube is the axis-parallel box with the
truncated sides. -/
theorem mem_cubeC_inter_closedBall {k : ℕ} {x z : Fin k → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    z ∈ cubeC k ∩ Metric.closedBall x δ ↔ z ∈ axBox (lcLo x δ) (lcHi x δ) := by
  simp only [Set.mem_inter_iff, Metric.mem_closedBall, dist_pi_le_iff (le_of_lt hδ),
    Real.dist_eq, cubeC, Set.mem_ofPred_eq, axBox, lcLo, lcHi]
  constructor
  · rintro ⟨h1, h2⟩ i
    have h1i := abs_le.mp (h1 i)
    have h2i := abs_le.mp (h2 i)
    exact ⟨max_le (by linarith [h2i.1]) h1i.1, le_min (by linarith [h2i.2]) h1i.2⟩
  · intro h
    constructor
    · intro i
      have hi := h i
      exact abs_le.mpr ⟨le_trans (le_max_right _ _) hi.1, le_trans hi.2 (min_le_right _ _)⟩
    · intro i
      have hi := h i
      exact abs_le.mpr ⟨by linarith [hi.1, le_max_left (x i - δ) (-1)],
        by linarith [hi.2, min_le_left (x i + δ) 1]⟩

/-- The trace of a ball centred at a point of the cube is the corresponding axis-parallel box. -/
theorem cubeC_inter_closedBall {k : ℕ} {x : Fin k → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    cubeC k ∩ Metric.closedBall x δ = axBox (lcLo x δ) (lcHi x δ) :=
  Set.ext fun _ => mem_cubeC_inter_closedBall hδ

/-- **Finitely many components in every axis-parallel box.**  The component bound for the cube,
transported along the homeomorphism `boxMap a b : cubeC k ≃ axBox a b` of `BoxLocDefs`. -/
theorem finite_components_axBox_inter_Zset {k r : ℕ} (c : EAChain k r) {a b : Fin k → ℝ}
    (hab : ∀ i, a i < b i) (g : Finset (EAPoly k r)) :
    (Set.range (connectedComponentIn (axBox a b ∩ Zset c g))).Finite := by
  obtain ⟨p, hp⟩ := varietyBound_all (k + r)
  obtain ⟨s, -, -, hs⟩ := hp k r (boxChain c a b) (g.image (boxSub a b)) le_rfl
  have h1 : (Set.range (connectedComponentIn
      (boxMap a b '' (cubeC k ∩ Zset (boxChain c a b) (g.image (boxSub a b)))))).Finite :=
    Work.WilE2.WilE2Aux.finite_range_componentIn_image_of_hits (boxHomeo a b hab)
      (fun y hy => hs y hy)
  rw [Work.WilE2.BoxLoc.boxMap_image_Zset c hab g] at h1
  exact h1

/-- **Finitely many components of the trace of `X = cubeC ∩ Zset` on a local ball.** -/
theorem finite_components_cubeC_Zset_closedBall {k r : ℕ} (c : EAChain k r)
    (g : Finset (EAPoly k r)) {x : Fin k → ℝ} (hx : x ∈ cubeC k) {δ : ℝ} (hδ : 0 < δ) :
    (Set.range (connectedComponentIn ((cubeC k ∩ Zset c g) ∩ Metric.closedBall x δ))).Finite := by
  have hset : (cubeC k ∩ Zset c g) ∩ Metric.closedBall x δ
      = axBox (lcLo x δ) (lcHi x δ) ∩ Zset c g := by
    rw [Set.inter_assoc, Set.inter_comm (Zset c g) (Metric.closedBall x δ), ← Set.inter_assoc,
      cubeC_inter_closedBall hδ]
  rw [hset]
  exact finite_components_axBox_inter_Zset c (lcLo_lt_lcHi hx hδ) g

/-- `cubeC k ∩ Zset c f` is locally connected: its traces on the balls around a point of it have
only finitely many components, by the Khovanskii–Gabrielov–Vorobjov component bound. -/
theorem locallyConnected_cubeC_Zset (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
    (f : Finset (WilkiesDesign.E.EAPoly k r)) :
    LocallyConnectedSpace ↥(WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c f) := by
  refine Work.WilE2.WilE2Aux.locallyConnectedSpace_of_component_finite
    ((isClosed_cubeC k).inter (isClosed_Zset c f)) ?_
  intro x hx δ hδ
  exact finite_components_cubeC_Zset_closedBall c f hx.1 hδ

end Work.WilE2
