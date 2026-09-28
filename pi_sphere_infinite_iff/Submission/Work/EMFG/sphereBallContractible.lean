import Mathlib
import Submission.Work.EMFG.sphereBallDefs
import Submission.Work.EMFG.contractible_convexCone_sphere
import Submission.Work.EMFG.dist_lt_iff_inner_gt
import Submission.Work.EMFG.ballCone_convex_smul_ne_zero

/-!
# Nonempty intersections of small balls on a sphere are contractible

Let `a : α → Metric.sphere (0 : E) 1` be finitely many points of the unit sphere of a real inner
product space and `0 < ε < 1`.  Any nonempty intersection `⋂ i ∈ S, Metric.ball (a i) ε` of the
corresponding (chordal) balls on the sphere is contractible.

The point is that on the unit sphere the ball of radius `ε` around a unit vector `a` is cut out by
the *linear* inequality `1 - ε²/2 < ⟪x, a⟫` (`dist_lt_iff_inner_gt`).  Consequently the
intersection is the trace on the sphere of the open convex cone
`ballCone S a ε = {x | ∀ i ∈ S, (1 - ε²/2) * ‖x‖ < ⟪x, a i⟫}`.  A convex cone not containing the
origin meets the sphere in a contractible space (`contractible_convexCone_sphere`), which gives the
claim.
-/

set_option linter.style.haveILetI false

namespace Work.EMFG

open Set Metric

/-- On the unit sphere, membership in `ballCone` is the same as lying in each of the balls. -/
lemma mem_ballCone_iff_dist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α : Type*} (S : Finset α) (a : α → Metric.sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε)
    {x : E} (hx : ‖x‖ = 1) :
    x ∈ ballCone S a ε ↔ ∀ i ∈ S, dist x (a i : E) < ε := by
  constructor
  · intro h i hi
    rw [dist_lt_iff_inner_gt hx (norm_eq_one_of_mem_sphere (a i).2) hε]
    simpa [hx] using h i hi
  · intro h i hi
    have hi' := h i hi
    rw [dist_lt_iff_inner_gt hx (norm_eq_one_of_mem_sphere (a i).2) hε] at hi'
    simpa [hx] using hi'

/-- The set `⋂ i ∈ S, Metric.ball (a i) ε` inside the unit sphere is the trace of the cone
`ballCone S a ε`. -/
lemma inter_ball_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α : Type*} (S : Finset α) (a : α → Metric.sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε) :
    (⋂ i ∈ S, (Metric.ball (a i) ε : Set (Metric.sphere (0 : E) 1)))
      = {x : Metric.sphere (0 : E) 1 | (x : E) ∈ ballCone S a ε} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [mem_ballCone_iff_dist S a hε (norm_eq_one_of_mem_sphere x.2)]
  simp only [Set.mem_iInter, Metric.mem_ball, Subtype.dist_eq]

/-- The subtype `{x : ↥A | (x : Z) ∈ B}` of `A` is homeomorphic to `↥(B ∩ A)`. -/
def homeoOfSubtypeInter {Z : Type*} [TopologicalSpace Z] (A B : Set Z) :
    ↥{x : ↥A | (x : Z) ∈ B} ≃ₜ ↥(B ∩ A) where
  toFun x := ⟨(x : Z), x.2, x.1.2⟩
  invFun y := ⟨⟨(y : Z), y.2.2⟩, y.2.1⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun x => ⟨x.2, x.1.2⟩)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun y => y.2.2)) (fun y => y.2.1)

theorem sphereBallContractible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α : Type*} (S : Finset α) (hS : S.Nonempty) (a : α → Metric.sphere (0 : E) 1) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hne : (⋂ i ∈ S, (Metric.ball (a i) ε : Set (Metric.sphere (0 : E) 1))).Nonempty) :
    ContractibleSpace ↥(⋂ i ∈ S, (Metric.ball (a i) ε : Set (Metric.sphere (0 : E) 1))) := by
  obtain ⟨hconv, hcone, h0⟩ := ballCone_convex_smul_ne_zero S hS a hε hε1
  have hneC : (ballCone S a ε).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    simp only [Set.mem_iInter] at hx
    refine ⟨(x : E), ?_⟩
    rw [mem_ballCone_iff_dist S a hε (norm_eq_one_of_mem_sphere x.2)]
    intro i hi
    have := hx i hi
    rwa [Metric.mem_ball, Subtype.dist_eq] at this
  have hAB : ContractibleSpace ↥(ballCone S a ε ∩ Metric.sphere (0 : E) 1) :=
    contractible_convexCone_sphere hconv hcone h0 hneC
  rw [inter_ball_eq S a hε]
  haveI : ContractibleSpace ↥(ballCone S a ε ∩ Metric.sphere (0 : E) 1) := hAB
  exact (homeoOfSubtypeInter (Metric.sphere (0 : E) 1) (ballCone S a ε)).contractibleSpace

end Work.EMFG
