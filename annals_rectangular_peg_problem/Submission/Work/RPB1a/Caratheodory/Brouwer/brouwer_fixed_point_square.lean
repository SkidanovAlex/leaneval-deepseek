import Mathlib
import Submission.Work.RPB.Port.Drive.WindingNumber
import Submission.Work.RPCore.Port.Whitney.noRetractionBallSphere
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_retraction_of_fixedPointFree
import Submission.Work.RPB1a.Caratheodory.Brouwer.brouwer_ball_of_unit_ball

/-!
# Brouwer's fixed point theorem for the closed square

`Work.RPB1a.Caratheodory.Brouwer.brouwer_fixed_point_square`: every continuous map of the closed
square `[-1,1] × [-1,1]` into itself has a fixed point.

## Strategy

1. `exists_retraction_of_fixedPointFree`: a continuous self-map of the closed unit ball of
   `EuclideanSpace ℝ (Fin N)` without fixed point yields a continuous retraction of the ball onto
   its boundary sphere (the classical radial construction).
2. `brouwer_unitBall`: this contradicts the no-retraction theorem
   `Work.RPCore.Port.Whitney.noRetractionBallSphere`, giving the fixed point property of the closed
   unit ball of `EuclideanSpace ℝ (Fin N)`.
3. `brouwer_ball`: rescaling gives the same for the closed ball of any radius `R > 0`
   (`brouwer_ball_of_unit_ball`).
4. Transport to the square: the coordinatewise clamp `clampPair` retracts `ℝ × ℝ` onto the square
   `[-1,1] × [-1,1]`, and the linear equivalence `pairEquiv : ℝ^2 ≃ ℝ × ℝ` (with `x ↦ (x 0, x 1)`)
   identifies `ℝ × ℝ` with `EuclideanSpace ℝ (Fin 2)`. From a fixed-point-free continuous
   `f` of the square into itself we build `y ↦ pairEquiv.symm (clampPair (f (pairEquiv y)))`, whose
   values all lie in the square, hence in the closed ball of radius `√2` of `EuclideanSpace ℝ
   (Fin 2)`; step 3 supplies a fixed point `y` of it, and since `clampPair` is the identity on the
   square the point `pairEquiv y` is a fixed point of `f` in the square.
-/

namespace Work.RPB1a.Caratheodory.Brouwer

open Set Metric
open scoped Topology

/-- **Brouwer's fixed point theorem for the closed unit ball of `ℝ^N`.**  A continuous self-map of
the closed unit ball of `EuclideanSpace ℝ (Fin N)` has a fixed point there.  Combining the radial
retraction `exists_retraction_of_fixedPointFree` with the no-retraction theorem
`Work.RPCore.Port.Whitney.noRetractionBallSphere`. -/
private theorem brouwer_unitBall {N : ℕ} (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : Continuous g) (hmaps : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ g x = x := by
  by_contra hcon
  have hfix : ∀ x, ‖x‖ ≤ 1 → g x ≠ x := fun x hx hgx => hcon ⟨x, hx, hgx⟩
  obtain ⟨F, hFc, hFsphere, hFball⟩ := exists_retraction_of_fixedPointFree g hg hmaps hfix
  refine Work.RPCore.Port.Whitney.noRetractionBallSphere (N := N) 0 (r := 1) one_pos
    ⟨F, hFc, ?_, ?_⟩
  · intro z hz
    exact hFsphere z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)
  · intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact hFball z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

/-- **Brouwer's fixed point theorem for a closed ball of `ℝ^N`.** -/
private theorem brouwer_ball {N : ℕ} {R : ℝ} (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (hg : Continuous g)
    (hmaps : ∀ x, ‖x‖ ≤ R → ‖g x‖ ≤ R) : ∃ x, ‖x‖ ≤ R ∧ g x = x :=
  brouwer_ball_of_unit_ball hR (fun g hg hmaps => brouwer_unitBall g hg hmaps) g hg hmaps

/-! ### Clamping to the square -/

/-- The coordinatewise clamp of `ℝ` onto `[-1,1]`. -/
private noncomputable def clampR (t : ℝ) : ℝ := min 1 (max (-1) t)

private lemma continuous_clampR : Continuous clampR :=
  continuous_const.min (continuous_const.max continuous_id)

private lemma clampR_mem (t : ℝ) : clampR t ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

private lemma clampR_eq_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : clampR t = t := by
  rw [clampR, min_eq_right (max_le (by norm_num) ht.2), max_eq_right ht.1]

private lemma sq_clampR_le_one (t : ℝ) : clampR t ^ 2 ≤ 1 := by
  have h := abs_le.mp (abs_le.mpr (clampR_mem t) : |clampR t| ≤ 1)
  nlinarith [h.1, h.2]

/-- The coordinatewise clamp of `ℝ × ℝ` onto the square `[-1,1] × [-1,1]`. -/
private noncomputable def clampPair (p : ℝ × ℝ) : ℝ × ℝ := (clampR p.1, clampR p.2)

private lemma continuous_clampPair : Continuous clampPair :=
  Continuous.prodMap continuous_clampR continuous_clampR

private lemma clampPair_eq_of_mem {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) : clampPair p = p := by
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
  simp [clampPair, clampR_eq_of_mem h1, clampR_eq_of_mem h2]

/-- The coordinate identification `ℝ^2 ≃ ℝ × ℝ`. -/
private noncomputable def pairEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

private lemma pairEquiv_apply (x : EuclideanSpace ℝ (Fin 2)) : pairEquiv x = (x 0, x 1) := by
  simp [pairEquiv]

private lemma norm_sq_eq_pair (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 = (pairEquiv x).1 ^ 2 + (pairEquiv x).2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [pairEquiv]

/-- Every continuous map of the closed square `[-1,1] x [-1,1]` into itself has a fixed point. -/
theorem brouwer_fixed_point_square (f : ℝ × ℝ → ℝ × ℝ) (hf : Continuous f)
    (hmaps : ∀ x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1,
      f x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1, f x = x := by
  -- The clamped map, defined on `ℝ^2 = EuclideanSpace ℝ (Fin 2)`.
  set G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y => pairEquiv.symm (clampPair (f (pairEquiv y))) with hG
  have hGc : Continuous G :=
    pairEquiv.symm.continuous.comp (continuous_clampPair.comp (hf.comp pairEquiv.continuous))
  have hpairG : ∀ y, pairEquiv (G y) = clampPair (f (pairEquiv y)) := fun y => by simp [hG]
  -- Every value of `G` lies in the square, hence in the closed ball of radius `√2`.
  have hGnorm : ∀ y, ‖G y‖ ≤ Real.sqrt 2 := by
    intro y
    have hsq : ‖G y‖ ^ 2 ≤ 2 := by
      rw [norm_sq_eq_pair (G y), hpairG y]
      have h1 : clampR (f (pairEquiv y)).1 ^ 2 ≤ 1 := sq_clampR_le_one _
      have h2 : clampR (f (pairEquiv y)).2 ^ 2 ≤ 1 := sq_clampR_le_one _
      simp only [clampPair] at h1 h2 ⊢
      linarith
    have h3 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at h3
  obtain ⟨x, hx, hfix⟩ := brouwer_ball (N := 2) (R := Real.sqrt 2)
    (Real.sqrt_pos.mpr (by norm_num)) G hGc (fun y _ => hGnorm y)
  -- `pairEquiv x` is a fixed point of the clamped map.
  have hEx : pairEquiv x = clampPair (f (pairEquiv x)) := by
    have h := congrArg pairEquiv hfix.symm
    rwa [hpairG x] at h
  have hx1 : (pairEquiv x).1 = clampR ((f (pairEquiv x)).1) := by
    have h := congrArg Prod.fst hEx; simpa [clampPair] using h
  have hx2 : (pairEquiv x).2 = clampR ((f (pairEquiv x)).2) := by
    have h := congrArg Prod.snd hEx; simpa [clampPair] using h
  -- Hence `pairEquiv x` lies in the square, and so does its image.
  have hmem : pairEquiv x ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_prod]
    exact ⟨by rw [hx1]; exact clampR_mem _, by rw [hx2]; exact clampR_mem _⟩
  have hfmem : f (pairEquiv x) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 :=
    hmaps (pairEquiv x) hmem
  obtain ⟨hf1, hf2⟩ := Set.mem_prod.mp hfmem
  refine ⟨pairEquiv x, hmem, ?_⟩
  have e1 : (pairEquiv x).1 = (f (pairEquiv x)).1 := by rw [hx1, clampR_eq_of_mem hf1]
  have e2 : (pairEquiv x).2 = (f (pairEquiv x)).2 := by rw [hx2, clampR_eq_of_mem hf2]
  exact (Prod.ext e1 e2).symm

end Work.RPB1a.Caratheodory.Brouwer
