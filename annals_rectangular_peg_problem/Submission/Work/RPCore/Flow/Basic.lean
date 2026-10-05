import Submission.Work.RPCore.Defs

/-!
# Global flows of bounded Lipschitz vector fields

The ported fleet code (`Submission/Work/RPCore/Port/ODE/`) provides, for a Lipschitz vector field
`V` on a finite-dimensional normed space with a global bound on `‖V‖`, the existence of a global
integral curve through every point (`exists_isIntegralCurve_of_lipschitzWith`) and uniqueness of
integral curves (`eq_of_isIntegralCurve`).

Here we package these into an actual **flow** `Φ : ℝ → E → E` with

* `Φ 0 = id`,
* `t ↦ Φ t z` is an integral curve through `z`,
* the semigroup law `Φ (s+t) = Φ s ∘ Φ t`,
* the contraction/expansion bound `dist (Φ t z) (Φ t z') ≤ exp (L * |t|) * dist z z'`
  (Grönwall, with `L` the Lipschitz constant).

This is the tool used by the CORE block both for the Hamiltonian flow of a `CptPerHam` (C0) and for
the cut-off negative-gradient descent used in the saddle-point theorem (C5).
-/

open Set Function
open scoped Topology NNReal

set_option autoImplicit false

noncomputable section

namespace Work.RPCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The integral curve through `z` of a bounded Lipschitz field, chosen once and for all. -/
noncomputable def flowCurveOf (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) (z : E) : ℝ → E :=
  Classical.choose (Port.ODE.exists_isIntegralCurve_of_lipschitzWith V hL hM z)

theorem flowCurveOf_zero (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) (z : E) : flowCurveOf V hL hM z 0 = z :=
  (Classical.choose_spec (Port.ODE.exists_isIntegralCurve_of_lipschitzWith V hL hM z)).1

theorem flowCurveOf_isIntegralCurve (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) (z : E) :
    IsIntegralCurve (flowCurveOf V hL hM z) (fun _ y => V y) :=
  (Classical.choose_spec (Port.ODE.exists_isIntegralCurve_of_lipschitzWith V hL hM z)).2

/-- The flow of a bounded Lipschitz field. -/
noncomputable def flowOf (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) (t : ℝ) (z : E) : E := flowCurveOf V hL hM z t

theorem flowOf_zero (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) (z : E) : flowOf V hL hM 0 z = z :=
  flowCurveOf_zero V hL hM z

theorem flowOf_isIntegralCurve (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) (z : E) :
    IsIntegralCurve (fun t => flowOf V hL hM t z) (fun _ y => V y) :=
  flowCurveOf_isIntegralCurve V hL hM z

theorem flowOf_add (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) (s t : ℝ) (z : E) :
    flowOf V hL hM (s + t) z = flowOf V hL hM s (flowOf V hL hM t z) := by
  have hv : (fun (_ : ℝ) (y : E) => V y) ∘ (· + t) = (fun (_ : ℝ) (y : E) => V y) := by
    funext r y; rfl
  have h1 : IsIntegralCurve (fun u => flowOf V hL hM (u + t) z) (fun _ y => V y) := by
    have h := (flowOf_isIntegralCurve V hL hM z).comp_add t
    rwa [hv] at h
  have h2 : IsIntegralCurve (fun u => flowOf V hL hM u (flowOf V hL hM t z)) (fun _ y => V y) :=
    flowOf_isIntegralCurve V hL hM _
  have h3 : (fun u => flowOf V hL hM (u + t) z) 0
      = (fun u => flowOf V hL hM u (flowOf V hL hM t z)) 0 := by
    show flowOf V hL hM (0 + t) z = flowOf V hL hM 0 (flowOf V hL hM t z)
    rw [zero_add, flowOf_zero]
  have h := Port.ODE.eq_of_isIntegralCurve hL h1 h2 h3
  exact congrFun h s

/-- Grönwall estimate along two integral curves of the same Lipschitz field, for positive times. -/
theorem flowOf_dist_le_pos (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) (z z' : E) :
    dist (flowOf V hL hM t z) (flowOf V hL hM t z') ≤ Real.exp ((L : ℝ) * t) * dist z z' := by
  have hγ₁c : Continuous (fun u : ℝ => flowOf V hL hM u z) :=
    (flowOf_isIntegralCurve V hL hM z).continuous
  have hγ₂c : Continuous (fun u : ℝ => flowOf V hL hM u z') :=
    (flowOf_isIntegralCurve V hL hM z').continuous
  have hmain : ∀ x ∈ Icc (0:ℝ) t,
      ‖flowOf V hL hM x z - flowOf V hL hM x z'‖
        ≤ gronwallBound ‖z - z'‖ (L : ℝ) 0 (x - 0) := by
    refine norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun x : ℝ => flowOf V hL hM x z - flowOf V hL hM x z')
      (f' := fun x : ℝ => V (flowOf V hL hM x z) - V (flowOf V hL hM x z')) ?_ ?_ ?_ ?_
    · exact (hγ₁c.sub hγ₂c).continuousOn
    · intro x _
      exact ((flowOf_isIntegralCurve V hL hM z x).sub
        (flowOf_isIntegralCurve V hL hM z' x)).hasDerivWithinAt
    · rw [flowOf_zero, flowOf_zero]
    · intro x _
      have h : dist (V (flowOf V hL hM x z)) (V (flowOf V hL hM x z'))
          ≤ (L : ℝ) * dist (flowOf V hL hM x z) (flowOf V hL hM x z') := hL.dist_le_mul _ _
      simp only [dist_eq_norm] at h
      calc ‖V (flowOf V hL hM x z) - V (flowOf V hL hM x z')‖
          ≤ (L : ℝ) * ‖flowOf V hL hM x z - flowOf V hL hM x z'‖ := h
        _ = (L : ℝ) * ‖flowOf V hL hM x z - flowOf V hL hM x z'‖ + 0 := by ring
  have ht' := hmain t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at ht'
  rw [dist_eq_norm]
  calc ‖flowOf V hL hM t z - flowOf V hL hM t z'‖
      ≤ ‖z - z'‖ * Real.exp ((L : ℝ) * t) := ht'
    _ = Real.exp ((L : ℝ) * t) * dist z z' := by rw [dist_eq_norm]; ring

/-- The packaged statement: existence of a global Lipschitz flow. -/
theorem exists_globalFlow_lipschitz (V : E → E) {L : NNReal} (hL : LipschitzWith L V) {M : ℝ}
    (hM : ∀ z, ‖V z‖ ≤ M) :
    ∃ Φ : ℝ → E → E, (∀ z, Φ 0 z = z) ∧
      (∀ z, IsIntegralCurve (fun t => Φ t z) (fun _ y => V y)) ∧
      (∀ s t z, Φ (s + t) z = Φ s (Φ t z)) ∧
      (∀ t z z', dist (Φ t z) (Φ t z') ≤ Real.exp ((L : ℝ) * |t|) * dist z z') := by
  refine ⟨flowOf V hL hM, fun z => flowOf_zero V hL hM z,
    fun z => flowOf_isIntegralCurve V hL hM z, fun s t z => flowOf_add V hL hM s t z, ?_⟩
  intro t z z'
  rcases le_or_gt 0 t with ht | ht
  · have h := flowOf_dist_le_pos V hL hM ht z z'
    rw [abs_of_nonneg ht]
    exact h
  · -- negative time: reverse the field
    have hneg : LipschitzWith L (fun y : E => -V y) := hL.neg
    have hM' : ∀ y : E, ‖-V y‖ ≤ M := fun y => by rw [norm_neg]; exact hM y
    have hshift : ∀ (u : ℝ) (w : E),
        flowOf (fun y : E => -V y) hneg hM' u w = flowOf V hL hM (-u) w := by
      intro u w
      have h2 : IsIntegralCurve (fun s => flowOf V hL hM (-s) w) (fun _ y => -V y) := by
        have h := (flowOf_isIntegralCurve V hL hM w).comp_mul (-1)
        convert h using 1 <;> ext s <;> simp
      have h1 : IsIntegralCurve (fun s => flowOf (fun y : E => -V y) hneg hM' s w)
          (fun _ y => -V y) := flowOf_isIntegralCurve _ hneg hM' w
      have h3 : flowOf (fun y : E => -V y) hneg hM' 0 w = flowOf V hL hM (-0) w := by
        rw [flowOf_zero, neg_zero, flowOf_zero]
      exact congrFun (Port.ODE.eq_of_isIntegralCurve hneg h1 h2 h3) u
    have h := flowOf_dist_le_pos (fun y : E => -V y) hneg hM' (by linarith : (0:ℝ) ≤ -t) z z'
    rw [hshift, hshift] at h
    rw [abs_of_neg ht]
    simpa using h

end Work.RPCore
