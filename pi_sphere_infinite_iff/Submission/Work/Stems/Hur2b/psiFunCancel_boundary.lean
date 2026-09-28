import Mathlib
import Submission.Work.Stems.Hur2b.PsiCancel

/-!
# The boundary values of the cancellation family `psiFunCancel`

`psiFunCancel x₀ c s` is `Ψ(c)` with the radial `K₁`-coordinates of the four sectors interpolated at
parameter `s` (`Submission/Work/Stems/Hur2b/PsiCancel.lean`).  The four sectors are indexed by the
four edges of the square; a point of the *outer boundary* of the square that lies on the edge
carried by a sector has the corresponding `K₁`-value with radial coordinate exactly `s`, the
tangential coordinate `clamp (2u - 1/2)`.  This file records these four boundary values: they are
exactly what makes the family glue along the seams of `∂I³` (each shared cube edge is seen with the
same value from both incident faces).

Concretely, with `t = (a,b)`, the sectors are (`Submission/Work/Stems/Hur2/Psi.lean`)
* left  (`a ≤ 1/4`):  `K₁ (c∘faceCM 0 0) (pair2 (clamp (4a)) (clamp (2b - 1/2)))`,
* right (`a ≥ 3/4`):  `K₁ (c∘faceCM 0 1) (pair2 (clamp (4-4a)) (clamp (2b - 1/2)))`,
* bottom(`b ≤ 1/4`):  `K₁ (c∘faceCM 1 0) (pair2 (clamp (4b)) (clamp (2a - 1/2)))`,
* top   (`b ≥ 3/4`):  `K₁ (c∘faceCM 1 1) (pair2 (clamp (4-4b)) (clamp (2a - 1/2)))`,
with the radial coordinate interpolated to `interp s ·`.  On `a = 0` (left), `b = 0` (bottom),
`a = 1` (right) and `b = 1` (top) the clamped radial expression is `0`, and `interp s 0 = s`; so the
radial coordinate is `s` in all four cases, as claimed.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## The radial interpolation at `0` -/

theorem interp_of_eq_zero {τ a : unitInterval} (ha : a = 0) : interp τ a = τ := by
  subst ha
  apply Subtype.ext
  have h : (1 - (τ : ℝ)) * (((0 : unitInterval)) : ℝ) + (τ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [coe_zero_I]; constructor <;> linarith [τ.2.1, τ.2.2]
  rw [interp_coe h, coe_zero_I]; ring

@[simp] theorem interp_zero_right (τ : unitInterval) : interp τ 0 = τ :=
  interp_of_eq_zero rfl

/-! ## The four boundary values -/

/-- The value on the left edge `{a = 0}`: the `(0,0)`-edge with radial coordinate `s`. -/
theorem psiFunCancel_pair2_0_left (x₀ : X) (c : C(IC 2, X)) (s u : unitInterval) :
    psiFunCancel x₀ c s (pair2 0 u) =
      K₁ x₀ (c.comp (faceCM (0 : Fin 2) (0 : unitInterval)))
        (pair2 s (clamp (2 * (u : ℝ) - 1/2))) := by
  have ht : pair2 0 u ∈ leftSet := by
    show ((pair2 0 u) 0 : ℝ) ≤ 1/4 ∧ ((pair2 0 u) 0 : ℝ) ≤ ((pair2 0 u) 1 : ℝ) ∧
      ((pair2 0 u) 1 : ℝ) ≤ 1 - ((pair2 0 u) 0 : ℝ)
    rw [pair2_zero, pair2_one, coe_zero_I]
    exact ⟨by norm_num, u.2.1, by linarith [u.2.2]⟩
  rw [psiFunCancel_eq_leftValC' ht, leftValC]
  simp only [pair2_zero, pair2_one, coe_zero_I, mul_zero, clamp_zero, interp_zero_right]

/-- The value on the right edge `{a = 1}`: the `(0,1)`-edge with radial coordinate `s`. -/
theorem psiFunCancel_pair2_1_right (x₀ : X) (c : C(IC 2, X)) (s u : unitInterval) :
    psiFunCancel x₀ c s (pair2 1 u) =
      K₁ x₀ (c.comp (faceCM (0 : Fin 2) (1 : unitInterval)))
        (pair2 s (clamp (2 * (u : ℝ) - 1/2))) := by
  have ht : pair2 1 u ∈ rightSet := by
    show (3/4 : ℝ) ≤ ((pair2 1 u) 0 : ℝ) ∧
      1 - ((pair2 1 u) 0 : ℝ) ≤ ((pair2 1 u) 1 : ℝ) ∧
      ((pair2 1 u) 1 : ℝ) ≤ ((pair2 1 u) 0 : ℝ)
    rw [pair2_zero, pair2_one, coe_one_I]
    exact ⟨by norm_num, by linarith [u.2.1], u.2.2⟩
  rw [psiFunCancel_eq_rightValC' ht, rightValC]
  simp only [pair2_zero, pair2_one, coe_one_I, mul_one, sub_self, clamp_zero,
    interp_zero_right]

/-- The value on the bottom edge `{b = 0}`: the `(1,0)`-edge with radial coordinate `s`. -/
theorem psiFunCancel_pair2_0_bot (x₀ : X) (c : C(IC 2, X)) (s u : unitInterval) :
    psiFunCancel x₀ c s (pair2 u 0) =
      K₁ x₀ (c.comp (faceCM (1 : Fin 2) (0 : unitInterval)))
        (pair2 s (clamp (2 * (u : ℝ) - 1/2))) := by
  have ht : pair2 u 0 ∈ botSet := by
    show ((pair2 u 0) 1 : ℝ) ≤ 1/4 ∧ ((pair2 u 0) 1 : ℝ) ≤ ((pair2 u 0) 0 : ℝ) ∧
      ((pair2 u 0) 0 : ℝ) ≤ 1 - ((pair2 u 0) 1 : ℝ)
    rw [pair2_zero, pair2_one, coe_zero_I]
    exact ⟨by norm_num, by linarith [u.2.1], by linarith [u.2.2]⟩
  rw [psiFunCancel_eq_botValC' ht, botValC]
  simp only [pair2_zero, pair2_one, coe_zero_I, mul_zero, clamp_zero, interp_zero_right]

/-- The value on the top edge `{b = 1}`: the `(1,1)`-edge with radial coordinate `s`. -/
theorem psiFunCancel_pair2_1_top (x₀ : X) (c : C(IC 2, X)) (s u : unitInterval) :
    psiFunCancel x₀ c s (pair2 u 1) =
      K₁ x₀ (c.comp (faceCM (1 : Fin 2) (1 : unitInterval)))
        (pair2 s (clamp (2 * (u : ℝ) - 1/2))) := by
  have ht : pair2 u 1 ∈ topSet := by
    show (3/4 : ℝ) ≤ ((pair2 u 1) 1 : ℝ) ∧
      1 - ((pair2 u 1) 1 : ℝ) ≤ ((pair2 u 1) 0 : ℝ) ∧
      ((pair2 u 1) 0 : ℝ) ≤ ((pair2 u 1) 1 : ℝ)
    rw [pair2_zero, pair2_one, coe_one_I]
    exact ⟨by norm_num, by linarith [u.2.1], u.2.2⟩
  rw [psiFunCancel_eq_topValC ht, topValC]
  simp only [pair2_zero, pair2_one, coe_one_I, mul_one, sub_self, clamp_zero,
    interp_zero_right]

/-! ## The requested boundary statement -/

theorem psiFunCancel_boundary {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x₀ : X)
    (c : ContinuousMap (Work.Stems.Cubical.IC 2) X) (s : unitInterval) (u : unitInterval) :
    (Work.Stems.Hur2b.psiFunCancel x₀ c s (Work.Stems.Hur2.pair2 0 u)
        = Work.Stems.Hur2.K₁ x₀ (c.comp (Work.Stems.Cubical.faceCM (0 : Fin 2) (0 : unitInterval)))
            (Work.Stems.Hur2.pair2 s (Work.Stems.Hur2.clamp (2 * (u : ℝ) - 1/2))))
    ∧ (Work.Stems.Hur2b.psiFunCancel x₀ c s (Work.Stems.Hur2.pair2 1 u)
        = Work.Stems.Hur2.K₁ x₀ (c.comp (Work.Stems.Cubical.faceCM (0 : Fin 2) (1 : unitInterval)))
            (Work.Stems.Hur2.pair2 s (Work.Stems.Hur2.clamp (2 * (u : ℝ) - 1/2))))
    ∧ (Work.Stems.Hur2b.psiFunCancel x₀ c s (Work.Stems.Hur2.pair2 u 0)
        = Work.Stems.Hur2.K₁ x₀ (c.comp (Work.Stems.Cubical.faceCM (1 : Fin 2) (0 : unitInterval)))
            (Work.Stems.Hur2.pair2 s (Work.Stems.Hur2.clamp (2 * (u : ℝ) - 1/2))))
    ∧ (Work.Stems.Hur2b.psiFunCancel x₀ c s (Work.Stems.Hur2.pair2 u 1)
        = Work.Stems.Hur2.K₁ x₀ (c.comp (Work.Stems.Cubical.faceCM (1 : Fin 2) (1 : unitInterval)))
            (Work.Stems.Hur2.pair2 s (Work.Stems.Hur2.clamp (2 * (u : ℝ) - 1/2)))) :=
  ⟨psiFunCancel_pair2_0_left x₀ c s u, psiFunCancel_pair2_1_right x₀ c s u,
    psiFunCancel_pair2_0_bot x₀ c s u, psiFunCancel_pair2_1_top x₀ c s u⟩

end

end Work.Stems.Hur2b
