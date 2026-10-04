import Mathlib
import Submission.Work.Diff.Dim2.Caps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The polar cap charts of `S²` are smooth and immersive on the open unit disc

The maps `northCap w = (w₀, w₁, √(1 - ‖w‖²))` and `southCap w = (w₀, w₁, -√(1 - ‖w‖²))` are the
two polar-cap charts of the round sphere.  This file proves the two facts about them that the
`d = 2` sphere theorem needs:

* they are `C^∞` on the open unit disc `‖w‖ < 1` (the only non-polynomial ingredient is `√·`,
  which is smooth at every point where its argument is nonzero);
* their derivatives are injective there — indeed both are left-inverse to the same
  projection `(x₀, x₁, x₂) ↦ (x₀, x₁)`, so `fderiv northCap w` has a left inverse.

The two facts are independent of one another except that injectivity of the derivative uses
differentiability (hence smoothness) at the point in question.
-/

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

noncomputable section

/-! ## The projection onto the first two coordinates

This continuous linear map is a left inverse of both cap charts. -/

/-- The projection `(x₀, x₁, x₂) ↦ (x₀, x₁)`, as a continuous linear map. -/
def capProj : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 3 => ℝ) (Fin.castSucc i)))

lemma capProj_apply (x : EuclideanSpace ℝ (Fin 3)) :
    capProj x = fun i : Fin 2 => x.ofLp (Fin.castSucc i) := rfl

lemma capProj_northCap (w : EuclideanSpace ℝ (Fin 2)) : capProj (northCap w) = w := by
  refine PiLp.ext (fun i => ?_)
  rw [show (capProj (northCap w)).ofLp i = (northCap w).ofLp i.castSucc from rfl]
  fin_cases i <;> simp [ofLp_northCap]

lemma capProj_southCap (w : EuclideanSpace ℝ (Fin 2)) : capProj (southCap w) = w := by
  refine PiLp.ext (fun i => ?_)
  rw [show (capProj (southCap w)).ofLp i = (southCap w).ofLp i.castSucc from rfl]
  fin_cases i <;> simp [ofLp_southCap]

/-! ## Smoothness on the open unit disc -/

/-- The height function `w ↦ √(1 - ‖w‖²)` of the cap charts is smooth on the open unit disc. -/
lemma contDiffOn_sqrt_one_sub_normSq :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => Real.sqrt (1 - ‖w‖ ^ 2))
      {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
  refine ContDiffOn.sqrt ?_ ?_
  · have h : (fun w : EuclideanSpace ℝ (Fin 2) => 1 - ‖w‖ ^ 2)
        = fun w : EuclideanSpace ℝ (Fin 2) => 1 - ((w.ofLp 0) ^ 2 + (w.ofLp 1) ^ 2) := by
      funext w
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [h]
    fun_prop
  · intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    intro hc
    nlinarith [norm_nonneg w]

lemma contDiffOn_northCap :
    ContDiffOn ℝ (⊤ : ℕ∞) northCap {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
  have c0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => northCapComp 0 w)
      {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
    simp only [northCapComp_zero]
    fun_prop
  have c1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => northCapComp 1 w)
      {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
    simp only [northCapComp_one]
    fun_prop
  have c2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => northCapComp 2 w)
      {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
    simp only [northCapComp_two]
    exact contDiffOn_sqrt_one_sub_normSq
  rw [show northCap = ⇑(EuclideanSpace.equiv (Fin 3) ℝ).symm ∘
      (fun w : EuclideanSpace ℝ (Fin 2) => fun i : Fin 3 => northCapComp i w) from rfl]
  rw [(EuclideanSpace.equiv (Fin 3) ℝ).symm.comp_contDiffOn_iff]
  refine contDiffOn_pi.mpr (fun i => ?_)
  fin_cases i
  · exact c0
  · exact c1
  · exact c2

lemma contDiffOn_southCap :
    ContDiffOn ℝ (⊤ : ℕ∞) southCap {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
  have c0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => southCapComp 0 w)
      {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
    simp only [southCapComp_zero]
    fun_prop
  have c1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => southCapComp 1 w)
      {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
    simp only [southCapComp_one]
    fun_prop
  have c2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => southCapComp 2 w)
      {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} := by
    simp only [southCapComp_two]
    exact contDiffOn_sqrt_one_sub_normSq.neg
  rw [show southCap = ⇑(EuclideanSpace.equiv (Fin 3) ℝ).symm ∘
      (fun w : EuclideanSpace ℝ (Fin 2) => fun i : Fin 3 => southCapComp i w) from rfl]
  rw [(EuclideanSpace.equiv (Fin 3) ℝ).symm.comp_contDiffOn_iff]
  refine contDiffOn_pi.mpr (fun i => ?_)
  fin_cases i
  · exact c0
  · exact c1
  · exact c2

/-! ## Injectivity of the derivative

Since `capProj` is a continuous linear left inverse of the chart, its composition with the
derivative is the identity, which forces the derivative to be injective. -/

lemma ball_eq_unitBall :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ) =
      {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ < 1} := by
  ext y; simp [Metric.mem_ball, dist_zero_right]

lemma unitBall_mem_nhds (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ < 1) :
    ({w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} : Set _) ∈ 𝓝 w := by
  have h : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ) ∈ 𝓝 w :=
    Metric.isOpen_ball.mem_nhds
      (show w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ) from by
        rw [Metric.mem_ball, dist_zero_right]; exact hw)
  rw [ball_eq_unitBall] at h
  exact h

lemma injective_fderiv_northCap
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) northCap {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1})
    (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ < 1) :
    Function.Injective (fderiv ℝ northCap w) := by
  have hs := unitBall_mem_nhds w hw
  have hdiff : DifferentiableAt ℝ northCap w :=
    (hsm.contDiffAt hs).differentiableAt (by simp)
  have hleft : capProj.comp (fderiv ℝ northCap w)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
    have h2 : fderiv ℝ (fun u => capProj (northCap u)) w
        = capProj.comp (fderiv ℝ northCap w) := by
      rw [show (fun u => capProj (northCap u)) = ⇑capProj ∘ northCap from rfl]
      rw [fderiv_comp w capProj.differentiableAt hdiff, capProj.fderiv]
    have h3 : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 2) => capProj (northCap u)) w
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [show (fun u => capProj (northCap u)) = (fun u : EuclideanSpace ℝ (Fin 2) => u) from
        funext capProj_northCap]
      simp
    exact h2 ▸ h3
  have key : ∀ v, capProj (fderiv ℝ northCap w v) = v := by
    intro v
    have := congrArg
      (fun (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) => L v) hleft
    simpa using this
  exact fun a b hab => by rw [← key a, ← key b, hab]

lemma injective_fderiv_southCap
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) southCap {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1})
    (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ < 1) :
    Function.Injective (fderiv ℝ southCap w) := by
  have hs := unitBall_mem_nhds w hw
  have hdiff : DifferentiableAt ℝ southCap w :=
    (hsm.contDiffAt hs).differentiableAt (by simp)
  have hleft : capProj.comp (fderiv ℝ southCap w)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
    have h2 : fderiv ℝ (fun u => capProj (southCap u)) w
        = capProj.comp (fderiv ℝ southCap w) := by
      rw [show (fun u => capProj (southCap u)) = ⇑capProj ∘ southCap from rfl]
      rw [fderiv_comp w capProj.differentiableAt hdiff, capProj.fderiv]
    have h3 : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 2) => capProj (southCap u)) w
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [show (fun u => capProj (southCap u)) = (fun u : EuclideanSpace ℝ (Fin 2) => u) from
        funext capProj_southCap]
      simp
    exact h2 ▸ h3
  have key : ∀ v, capProj (fderiv ℝ southCap w v) = v := by
    intro v
    have := congrArg
      (fun (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) => L v) hleft
    simpa using this
  exact fun a b hab => by rw [← key a, ← key b, hab]

theorem northCapFacts :
    ContDiffOn ℝ (⊤ : ℕ∞) Work.Diff.Dim2.northCap {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} ∧
    (∀ w : EuclideanSpace ℝ (Fin 2), ‖w‖ < 1 →
      Function.Injective (fderiv ℝ Work.Diff.Dim2.northCap w)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) Work.Diff.Dim2.southCap {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} ∧
    (∀ w : EuclideanSpace ℝ (Fin 2), ‖w‖ < 1 →
      Function.Injective (fderiv ℝ Work.Diff.Dim2.southCap w)) :=
  ⟨contDiffOn_northCap, fun w hw => injective_fderiv_northCap contDiffOn_northCap w hw,
    contDiffOn_southCap, fun w hw => injective_fderiv_southCap contDiffOn_southCap w hw⟩

end

end Work.Diff.Dim2
