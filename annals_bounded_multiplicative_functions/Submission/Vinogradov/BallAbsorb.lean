/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.FromDecLin
import Submission.Vinogradov.DecouplingClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Enlarging a plate by a Euclidean ball

GLYZ Corollary 3.7 is proved by multiplying the pieces by a Schwartz bump `ψ_B` whose Fourier
transform is supported in a ball of radius `≍ |B|^{-1/l}`, the ball `B` having radius `δ^{-l}`
while the pieces have scale `δ`.  For the multiplied pieces to remain in a class `𝒞(U)` over a
*plate*, one needs to know that adding that small ball to a plate stays inside a fixed
multiple of the plate:

  `plate l d c + Metric.ball 0 ρ ⊆ plate l (2d) c`  whenever `2^{2l} ρ ≤ d^l` and `0 < d ≤ 1`.

This is the content of `plate_add_ball_subset` below.  (The bound `ρ ≤ d^l/2^{2l}` is far from
optimal --- geometrically the plate absorbs a ball of radius a fixed multiple of `d` --- but it
is what the coordinate estimate `abs_affVecDual_one_neg_le` gives, and it is enough for the
application, where `ρ = δ^l` and `d = λ δ/2` with `λ` a fixed constant, so that the condition
reads `2^{2l} ≤ (λ/2)^l`, i.e. `λ ≥ 8`.)

The proof is elementary:  `plate l d c = γ(c) + A_{1,c}(box(d))` where `box(d)` is the
coordinate box of half-sides `(j+1)! d^{j+1}` (this is `affVecDual_zero_apply`), and
`A_{1,c}^{-1} = A_{1,-c}` maps the Euclidean ball `B(0,ρ)` into the sup-box of half-side
`2^{2l}ρ ≤ d^l`, which fits into the `2d`-box because `d^l ≤ (j+1)!(2^{j+1}-1)d^{j+1}`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- A vector whose coordinates are bounded by `(j+1)!·δ^{j+1}` is the image under the diagonal
map `A_{δ,0}` of a point of the plate box. -/
lemma exists_affVecDual_zero_eq {l : ℕ} {δ : ℝ} (hδ : 0 < δ) {ζ : E l}
    (hζ : ∀ j : Fin l, |ζ j| ≤ ((j.val + 1).factorial : ℝ) * δ ^ (j.val + 1)) :
    ∃ u : E l, u ∈ plateBox l ∧ affVecDual l δ 0 u = ζ := by
  refine ⟨WithLp.toLp 2 (fun j => ζ j / δ ^ (j.val + 1)), ?_, ?_⟩
  · intro j
    rw [abs_div, abs_of_pos (pow_pos hδ _)]
    rw [div_le_iff₀ (pow_pos hδ _)]
    exact hζ j
  · ext j
    rw [affVecDual_zero_apply, WithLp.ofLp_toLp]
    field_simp

/-- **The ball absorption, per-coordinate form.**  If the radius `ρ` is small enough that
`2^{2l} ρ` fits into the margin of every coordinate of the plate box
(`(j+1)!(2^{j+1}-1)d^{j+1}`), then adding the ball `B(0,ρ)` to the plate of scale `d` stays
inside the plate of doubled scale `2d`. -/
lemma plate_add_ball_subset_of {l : ℕ} {d ρ : ℝ} (hd : 0 < d) {c : ℝ} (hc : |c| ≤ 1)
    (hρ0 : 0 ≤ ρ)
    (hρ : ∀ j : Fin l, (2 : ℝ) ^ (2 * l) * ρ
      ≤ ((j.val + 1).factorial : ℝ) * ((2 : ℝ) ^ (j.val + 1) - 1) * d ^ (j.val + 1))
    {z w : E l} (hz : z ∈ plate l d c) (hw : ‖w‖ ≤ ρ) :
    z + w ∈ plate l (2 * d) c := by
  obtain ⟨y, hy, hyz⟩ := hz
  have hcomp₁ : affVecDual l d c y = affVecDual l 1 c (affVecDual l d 0 y) := by
    have h := affVecDual_comp l 1 c d 0 y
    simpa using h.symm
  have hη : affVecDual l 1 c (affVecDual l 1 (-c) w) = w := by
    have h := affVecDual_inv_comp l (by norm_num : (1 : ℝ) ≠ 0) c w
    simpa using h
  set ζ : E l := affVecDual l d 0 y + affVecDual l 1 (-c) w with hζdef
  have hcoord : ∀ j : Fin l, |ζ j| ≤ ((j.val + 1).factorial : ℝ) * (2 * d) ^ (j.val + 1) := by
    intro j
    have hyj : |y j| ≤ ((j.val + 1).factorial : ℝ) := hy j
    have h1 : |affVecDual l 1 (-c) w j| ≤ (2 : ℝ) ^ (2 * l) * ‖w‖ :=
      abs_affVecDual_one_neg_le l hc w j
    have h2 : (2 : ℝ) ^ (2 * l) * ‖w‖ ≤ (2 : ℝ) ^ (2 * l) * ρ :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h3 : |affVecDual l d 0 y j| ≤ ((j.val + 1).factorial : ℝ) * d ^ (j.val + 1) := by
      rw [affVecDual_zero_apply, abs_mul, abs_of_pos (pow_pos hd _)]
      exact mul_le_mul_of_nonneg_right hyj (pow_nonneg hd.le _)
    have h4 : |ζ j| ≤ ((j.val + 1).factorial : ℝ) * d ^ (j.val + 1) + (2 : ℝ) ^ (2 * l) * ρ := by
      rw [hζdef, PiLp.add_apply]
      refine (abs_add_le _ _).trans ?_
      linarith [h1, h2, h3]
    have h5 := hρ j
    have h6 : ((j.val + 1).factorial : ℝ) * d ^ (j.val + 1) + (2 : ℝ) ^ (2 * l) * ρ
        ≤ ((j.val + 1).factorial : ℝ) * (2 : ℝ) ^ (j.val + 1) * d ^ (j.val + 1) := by
      nlinarith [h5]
    have h7 : ((j.val + 1).factorial : ℝ) * (2 : ℝ) ^ (j.val + 1) * d ^ (j.val + 1)
        = ((j.val + 1).factorial : ℝ) * (2 * d) ^ (j.val + 1) := by
      rw [mul_pow]
      ring
    exact h4.trans (h6.trans h7.le)
  obtain ⟨u, hu, huu⟩ := exists_affVecDual_zero_eq (l := l) (δ := 2 * d)
    (by positivity) (ζ := ζ) hcoord
  refine ⟨u, hu, ?_⟩
  rw [← hyz]
  have hcomp₂ : affVecDual l (2 * d) c u = affVecDual l 1 c (affVecDual l (2 * d) 0 u) := by
    have h := affVecDual_comp l 1 c (2 * d) 0 u
    have h2 : (1 : ℝ) * 0 + c = c := by ring
    rw [h2, one_mul] at h
    exact h.symm
  have hdiag : affVecDual l d 0 y + affVecDual l 1 (-c) w
      = affVecDual l (2 * d) 0 u := huu.symm
  calc affMap l (2 * d) c u
      = gammaVec l c + affVecDual l (2 * d) c u := affMap_apply l (2 * d) c u
    _ = gammaVec l c + affVecDual l 1 c (affVecDual l (2 * d) 0 u) := by rw [hcomp₂]
    _ = gammaVec l c + affVecDual l 1 c (affVecDual l d 0 y + affVecDual l 1 (-c) w) := by
          rw [← hdiag]
    _ = gammaVec l c + (affVecDual l 1 c (affVecDual l d 0 y)
          + affVecDual l 1 c (affVecDual l 1 (-c) w)) := by rw [affVecDual_add]
    _ = gammaVec l c + (affVecDual l d c y + w) := by rw [← hcomp₁, hη]
    _ = affMap l d c y + w := by rw [affMap_apply]; abel

/-- **The ball absorption for small plates.**  For `0 < d ≤ 1` the plate absorbs a ball of
radius `ρ` as soon as `2^{2l} ρ ≤ d^l`. -/
lemma plate_add_ball_subset {l : ℕ} (hl : 1 ≤ l) {d ρ : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    {c : ℝ} (hc : |c| ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : (2 : ℝ) ^ (2 * l) * ρ ≤ d ^ l)
    {z w : E l} (hz : z ∈ plate l d c) (hw : ‖w‖ ≤ ρ) :
    z + w ∈ plate l (2 * d) c := by
  refine plate_add_ball_subset_of hd hc hρ0 (fun j => ?_) hz hw
  have hfac : (1 : ℝ) ≤ ((j.val + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j.val + 1)
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (j.val + 1) - 1 := by
    have h2p : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (j.val + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hprod : (1 : ℝ) ≤ ((j.val + 1).factorial : ℝ) * ((2 : ℝ) ^ (j.val + 1) - 1) := by
    have := mul_le_mul hfac htwo (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa using this
  have hdl : d ^ l ≤ d ^ (j.val + 1) := pow_le_pow_of_le_one hd.le hd1 (by omega)
  calc (2 : ℝ) ^ (2 * l) * ρ ≤ d ^ l := hρ
    _ ≤ (((j.val + 1).factorial : ℝ) * ((2 : ℝ) ^ (j.val + 1) - 1)) * d ^ (j.val + 1) := by
        refine hdl.trans ?_
        nth_rewrite 1 [show d ^ (j.val + 1) = 1 * d ^ (j.val + 1) from (one_mul _).symm]
        exact mul_le_mul_of_nonneg_right hprod (pow_nonneg hd.le _)

/-- **The ball absorption for large plates.**  For `d ≥ 1` the plate absorbs a ball of
radius `ρ` as soon as `2^{2l} ρ ≤ d`. -/
lemma plate_add_ball_subset_of_one_le {l : ℕ} {d ρ : ℝ} (hd : 0 < d) (hd1 : 1 ≤ d)
    {c : ℝ} (hc : |c| ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : (2 : ℝ) ^ (2 * l) * ρ ≤ d)
    {z w : E l} (hz : z ∈ plate l d c) (hw : ‖w‖ ≤ ρ) :
    z + w ∈ plate l (2 * d) c := by
  refine plate_add_ball_subset_of hd hc hρ0 (fun j => ?_) hz hw
  have hfac : (1 : ℝ) ≤ ((j.val + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j.val + 1)
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (j.val + 1) - 1 := by
    have h2p : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (j.val + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hprod : (1 : ℝ) ≤ ((j.val + 1).factorial : ℝ) * ((2 : ℝ) ^ (j.val + 1) - 1) := by
    have := mul_le_mul hfac htwo (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa using this
  have hdj : d ≤ d ^ (j.val + 1) := by
    have h1 : d ^ 1 ≤ d ^ (j.val + 1) := pow_le_pow_right₀ hd1 (by omega)
    simpa using h1
  calc (2 : ℝ) ^ (2 * l) * ρ ≤ d := hρ
    _ ≤ d ^ (j.val + 1) := hdj
    _ ≤ (((j.val + 1).factorial : ℝ) * ((2 : ℝ) ^ (j.val + 1) - 1)) * d ^ (j.val + 1) := by
        nth_rewrite 1 [show d ^ (j.val + 1) = 1 * d ^ (j.val + 1) from (one_mul _).symm]
        exact mul_le_mul_of_nonneg_right hprod (pow_nonneg hd.le _)

/-- The set form of the ball absorption, in the shape needed to enlarge the frequency support
of a product `f * ψ` where `ψ` has Fourier support in a ball of radius `ρ`. -/
lemma setPlus_plate_closedBall_subset {l : ℕ} (hl : 1 ≤ l) {d ρ : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    {c : ℝ} (hc : |c| ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : (2 : ℝ) ^ (2 * l) * ρ ≤ d ^ l) :
    setPlus (plate l d c) (Metric.closedBall 0 ρ) ⊆ plate l (2 * d) c := by
  rintro z ⟨u, hu, v, hv, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv
  exact plate_add_ball_subset hl hd hd1 hc hρ0 hρ hu hv

end Submission.Vinogradov
