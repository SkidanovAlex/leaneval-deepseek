/-
# The Caffarelli iteration for the improvement of flatness

This file contains the iteration that turns Savin's Proposition 4.1
(`Submission.Savin.Prop41Flat.improvement_of_flatness`) into an interior Hessian bound
(Savin's Theorem 1.3 in the concrete `Fop` formulation).

Design (see `Submission/Roadmap.md`, SESSION 38):

* `step_quad`: one improvement step together with the *universal* bounds on the coefficients of the
  approximating quadratic that the iteration needs in order to keep the ellipticity class fixed.
* `quadform_cofOp_le`: the drift bound `|⟪cofOp P₂ v, v⟫| ≤ 5 K ‖v‖²` from `|⟪P₂ v, v⟫| ≤ K ‖v‖²`.

The iteration itself (the state transition and the limiting argument) is developed below.
-/
import Submission.Savin.Prop41Flat
import Submission.Commons.Analysis.Quadratic.bounds_of_value_bound
import Submission.Commons.Analysis.Calculus.FDeriv.hessOp_quadratic

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- If the quadratic form of `P₂` is bounded by `K ‖v‖²` then the quadratic form of `cofOp P₂`
is bounded by `5 K ‖v‖²` (the trace of `P₂` is at most `4 K`). -/
theorem quadform_cofOp_le {P₂ : ℝ⁴ →L[ℝ] ℝ⁴} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : ℝ⁴, |⟪P₂ v, v⟫| ≤ K * ‖v‖ ^ 2) :
    ∀ v : ℝ⁴, |⟪cofOp P₂ v, v⟫| ≤ 5 * K * ‖v‖ ^ 2 := by
  intro v
  have h1 : ⟪cofOp P₂ v, v⟫ = trOp P₂ * ‖v‖ ^ 2 - ⟪P₂ v, v⟫ := by
    unfold cofOp
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  rw [h1]
  have h2 : |trOp P₂| ≤ 4 * K := by
    rw [trOp_eq_sum]
    calc |∑ i : Fin 4, ⟪P₂ (stdB4 i), stdB4 i⟫|
        ≤ ∑ i : Fin 4, |⟪P₂ (stdB4 i), stdB4 i⟫| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 4, K := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hv := h (stdB4 i)
          rwa [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at hv
      _ = 4 * K := by simp
  have h4 : |trOp P₂| * ‖v‖ ^ 2 ≤ 4 * K * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have h5 : |trOp P₂ * ‖v‖ ^ 2| ≤ 4 * K * ‖v‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)]
    exact h4
  have h6 : |trOp P₂ * ‖v‖ ^ 2 - ⟪P₂ v, v⟫| ≤ |trOp P₂| * ‖v‖ ^ 2 + |⟪P₂ v, v⟫| := by
    rw [sub_eq_add_neg]
    calc |trOp P₂ * ‖v‖ ^ 2 + -⟪P₂ v, v⟫| ≤ |trOp P₂ * ‖v‖ ^ 2| + |-⟪P₂ v, v⟫| := abs_add_le _ _
      _ = |trOp P₂| * ‖v‖ ^ 2 + |⟪P₂ v, v⟫| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖), abs_neg]
  have h7 := h v
  have h9 : |trOp P₂| * ‖v‖ ^ 2 ≤ 4 * K * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have h8 : (4 * K) * ‖v‖ ^ 2 + K * ‖v‖ ^ 2 = 5 * K * ‖v‖ ^ 2 := by ring
  linarith [h6, h9, h7, h8]

/-- **One improvement step, with coefficient bounds.**  If `W` is a `C²` function on `ball 0 2`
with `|W| ≤ 1` that solves the linearised equation at a base `A` of the ellipticity class
`[c/2, 2c']` with parameter `ρ ≤ ε`, then there is a quadratic approximation whose Hessian `P₂`
solves the same equation and whose coefficients obey the universal bounds
`|⟪P₂ v, v⟫| ≤ (8/θ²)‖v‖²` and `|⟪cofOp P₂ v, v⟫| ≤ (40/θ²)‖v‖²`. -/
theorem step_quad {c c' θ ε : ℝ} (hc : 0 < c) (hθpos : 0 < θ) (hθ16 : θ ≤ 1 / 16)
    (hFlat : FlatGood (c / 2) (2 * c') θ ε)
    {A : ℝ⁴ →L[ℝ] ℝ⁴} (hAsym : A.IsSymmetric) (hA1 : s2 A = 1) (hAtr : 0 < trOp A)
    (hAcq : ∀ v : ℝ⁴, (c / 2) * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hAcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ (2 * c') * ‖v‖ ^ 2)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ ≤ ε)
    {W : ℝ⁴ → ℝ} (hWcd : ContDiffOn ℝ 2 W (ball 0 2))
    (hWeq : ∀ x ∈ ball 0 2, Fop (cofOp A) ρ (hessOp W x) = 0)
    (hWpos : ∀ x ∈ ball 0 2, 0 < trOp (A + ρ • hessOp W x))
    (hW1 : ∀ x ∈ ball 0 2, |W x| ≤ 1) :
    ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ), P₂.IsSymmetric ∧
      Fop (cofOp A) ρ P₂ = 0 ∧
      (∀ x ∈ closedBall 0 θ, |W x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ θ ^ ((5 : ℝ) / 2)) ∧
      (∀ v : ℝ⁴, |⟪P₂ v, v⟫| ≤ (8 / θ ^ 2) * ‖v‖ ^ 2) ∧
      (∀ v : ℝ⁴, |⟪cofOp P₂ v, v⟫| ≤ 5 * (8 / θ ^ 2) * ‖v‖ ^ 2) := by
  obtain ⟨P₂, P₁, P₀, hsym, heq, hbd⟩ :=
    hFlat A hAsym hA1 hAtr hAcq hAcq' ρ W hρ0 hρε hWcd hWeq hWpos hW1
  -- the value bound for the quadratic
  have hPval : ∀ x : ℝ⁴, ‖x‖ ≤ θ → |⟪P₂ x, x⟫ / 2 + P₁ x + P₀| ≤ 2 := by
    intro x hx
    have hxθ : x ∈ closedBall 0 θ := by rwa [mem_closedBall, dist_zero_right]
    have h1 := hbd x hxθ
    have hx2 : x ∈ ball (0 : ℝ⁴) 2 := by
      rw [mem_ball, dist_zero_right]; linarith
    have h2 := hW1 x hx2
    have h3 : θ ^ ((5 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hθpos.le (by linarith) (by norm_num)
    have h6 : |⟪P₂ x, x⟫ / 2 + P₁ x + P₀| ≤ |W x| + |W x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| := by
      have he : (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)
          = W x + -(W x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)) := by ring
      conv_lhs => rw [he]
      calc |W x + -(W x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀))|
          ≤ |W x| + |-(W x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀))| := abs_add_le _ _
        _ = |W x| + |W x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| := by rw [abs_neg]
    linarith
  have hb := Commons.Analysis.Quadratic.bounds_of_value_bound P₂ P₁ P₀ θ 2 hθpos hPval
  have hK2 : ∀ v : ℝ⁴, |⟪P₂ v, v⟫| ≤ (8 / θ ^ 2) * ‖v‖ ^ 2 := by
    intro v
    have h := hb.1 v
    have he : 4 * 2 * ‖v‖ ^ 2 / θ ^ 2 = (8 / θ ^ 2) * ‖v‖ ^ 2 := by ring
    rwa [he] at h
  exact ⟨P₂, P₁, P₀, hsym, heq, hbd, hK2, quadform_cofOp_le (by positivity) hK2⟩


section IterationSetup

/-- The flatness decay factor `q = 4√θ` of one iteration step. -/
noncomputable def qDecay (θ : ℝ) : ℝ := 4 * Real.sqrt θ

/-- Universal bound for `|⟪P₂ v, v⟫|` at one step. -/
noncomputable def Kquad (θ : ℝ) : ℝ := 8 / θ ^ 2

/-- Universal bound for `|⟪cofOp P₂ v, v⟫|` at one step. -/
noncomputable def Kcof (θ : ℝ) : ℝ := 5 * (8 / θ ^ 2)

theorem qDecay_pos {θ : ℝ} (h : 0 < θ) : 0 < qDecay θ := by
  rw [qDecay]; positivity

theorem qDecay_le_quarter {θ : ℝ} (h : θ ≤ 1 / 256) : qDecay θ ≤ 1 / 4 := by
  have h1 : Real.sqrt θ ≤ 1 / 16 := by
    have h2 : Real.sqrt θ ≤ Real.sqrt (1 / 256) := Real.sqrt_le_sqrt h
    have h3 : Real.sqrt ((1 : ℝ) / 256) = 1 / 16 := by
      rw [show (1 : ℝ) / 256 = (1 / 16) ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
    rwa [h3] at h2
  rw [qDecay]
  linarith

theorem Kquad_pos {θ : ℝ} (h : 0 < θ) : 0 < Kquad θ := by
  rw [Kquad]; positivity

theorem Kcof_pos {θ : ℝ} (h : 0 < θ) : 0 < Kcof θ := by
  rw [Kcof]; positivity

theorem Kcof_eq {θ : ℝ} : Kcof θ = 5 * Kquad θ := by rw [Kcof, Kquad]

/-- `cofOp` is affine. -/
theorem cofOp_add (S T : ℝ⁴ →L[ℝ] ℝ⁴) : cofOp (S + T) = cofOp S + cofOp T := by
  ext v
  simp only [cofOp, sub_apply, add_apply, smul_apply, trOp_add, one_apply_eq_self]
  rw [add_smul]
  abel

theorem trOp_cofOp (S : ℝ⁴ →L[ℝ] ℝ⁴) : trOp (cofOp S) = 3 * trOp S := by
  unfold cofOp
  rw [trOp_sub, trOp_smul, trOp_one]
  ring

/-- The Hessian of the model quadratic `y ↦ ⟪M y, y⟫/2 + L y + c` is `M`. -/
theorem hessOp_modelQuad {M : ℝ⁴ →L[ℝ] ℝ⁴} (hM : M.IsSymmetric) (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ)
    (x : ℝ⁴) :
    hessOp (fun y => ⟪M y, y⟫ / 2 + L y + c) x = M := by
  unfold hessOp
  exact Commons.Analysis.Calculus.FDeriv.hessOp_quadratic M (fun u v => hM u v) L c x

/-- The Hessian under `y ↦ φ (r • y)` (the `x₀ = 0` case of `hessOp_comp_affine`). -/
theorem hessOp_comp_smul {φ : ℝ⁴ → ℝ} {x : ℝ⁴} {r : ℝ}
    (hφ : ContDiffAt ℝ 2 φ (r • x)) :
    hessOp (fun y : ℝ⁴ => φ (r • y)) x = (r * r) • hessOp φ (r • x) := by
  have h := hessOp_comp_affine (x₀ := 0) (r := r) (x := x) (by simpa using hφ)
  simpa using h

/-- The Hessian of `x ↦ w (R • x) / (ρ * R ^ 2)` is `(1/ρ) • D²w(Rx)`: the Hessian is invariant
under the value/argument rescaling used at each iteration step. -/
theorem hessOp_scaled_comp {w : ℝ⁴ → ℝ} {R ρ : ℝ} {x : ℝ⁴}
    (hR : R ≠ 0) (hρ : ρ ≠ 0) (hw : ContDiffAt ℝ 2 w (R • x)) :
    hessOp (fun y => w (R • y) / (ρ * R ^ 2)) x = (1 / ρ) • hessOp w (R • x) := by
  have h1 : (fun y : ℝ⁴ => w (R • y) / (ρ * R ^ 2)) = fun y => (1 / (ρ * R ^ 2)) * w (R • y) := by
    funext y; rw [div_eq_inv_mul, one_div]
  rw [h1]
  have hcd : ContDiffAt ℝ 2 (fun y : ℝ⁴ => w (R • y)) x :=
    hw.comp x (contDiffAt_id.const_smul R)
  rw [hessOp_const_mul _ hcd, hessOp_comp_smul hw, smul_smul]
  congr 1
  field_simp


end IterationSetup




/-- The data of one level of the Caffarelli iteration: the accumulated quadratic
`Q(y) = ⟪M y, y⟫/2 + L y + c`, the ball radius `R` of the current flatness estimate, the
flatness ratio `ρ` (so that `|u - Q| ≤ ρR²` on `ball 0 (2R)`), and `drift`, the accumulated
bound on `cofOp (A₀ + M) - cofOp A₀`. -/
structure IterState where
  M : ℝ⁴ →L[ℝ] ℝ⁴
  L : ℝ⁴ →L[ℝ] ℝ
  c : ℝ
  R : ℝ
  ρ : ℝ
  drift : ℝ

/-- The invariant of the Caffarelli iteration (see `Submission/Roadmap.md`, SESSION 38). -/
def IterInv (c c' θ Λ R₀ : ℝ) (A₀ : ℝ⁴ →L[ℝ] ℝ⁴) (u : ℝ⁴ → ℝ) (k : ℕ)
    (s : IterState) : Prop :=
  s.M.IsSymmetric ∧
  0 < s.R ∧ s.R = R₀ * (θ / 2) ^ k ∧ 0 < s.ρ ∧ s.ρ = Λ * qDecay θ ^ k ∧
  0 ≤ s.drift ∧ s.drift ≤ Λ * Kcof θ * (1 - qDecay θ ^ k) / (1 - qDecay θ) ∧
  (∀ v : ℝ⁴, |⟪s.M v, v⟫| ≤ Kquad θ * Λ * (1 - qDecay θ ^ k) / (1 - qDecay θ) * ‖v‖ ^ 2) ∧
  s2 (A₀ + s.M) = 1 ∧ 0 < trOp (A₀ + s.M) ∧
  (∀ v : ℝ⁴, (c - s.drift) * ‖v‖ ^ 2 ≤ ⟪cofOp (A₀ + s.M) v, v⟫) ∧
  (∀ v : ℝ⁴, ⟪cofOp (A₀ + s.M) v, v⟫ ≤ (c' + s.drift) * ‖v‖ ^ 2) ∧
  (∀ x ∈ ball 0 (2 * s.R), |u x - (⟪s.M x, x⟫ / 2 + s.L x + s.c)| ≤ s.ρ * s.R ^ 2)

/-- The initial state of the iteration: the perturbing quadratic is zero and the flatness ratio
is the given value `Λ`. -/
noncomputable def IterState.init (Λ R₀ : ℝ) : IterState :=
  ⟨0, 0, 0, R₀, Λ, 0⟩

/-- The initial state satisfies the invariant at level `0`. -/
theorem IterInv_zero {c c' θ Λ R₀ : ℝ} {A₀ : ℝ⁴ →L[ℝ] ℝ⁴} {u : ℝ⁴ → ℝ}
    (hΛ : 0 < Λ) (hR₀ : 0 < R₀) (hA₀sym : A₀.IsSymmetric) (hA₀1 : s2 A₀ = 1)
    (hA₀tr : 0 < trOp A₀)
    (hA₀cq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A₀ v, v⟫)
    (hA₀cq' : ∀ v : ℝ⁴, ⟪cofOp A₀ v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (hflat : ∀ x ∈ ball 0 (2 * R₀), |u x| ≤ Λ * R₀ ^ 2) :
    IterInv c c' θ Λ R₀ A₀ u 0 (IterState.init Λ R₀) := by
  refine ⟨?_, hR₀, by simp [IterState.init], hΛ, by simp [IterState.init, qDecay],
    le_rfl, ?_, ?_, ?_, (by simpa [IterState.init] using hA₀tr), ?_, ?_, ?_⟩
  · intro v w
    simp [IterState.init]
  · simp [IterState.init]
  · intro v
    simp [IterState.init]
  · simpa [IterState.init] using hA₀1
  · intro v
    simpa [IterState.init] using hA₀cq v
  · intro v
    simpa [IterState.init] using hA₀cq' v
  · intro x hx
    simpa [IterState.init] using hflat x hx

theorem contDiff_modelQuad (M : ℝ⁴ →L[ℝ] ℝ⁴) (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ) :
    ContDiff ℝ 2 (fun y : ℝ⁴ => ⟪M y, y⟫ / 2 + L y + c) := by
  have h1 : ContDiff ℝ 2 (fun y : ℝ⁴ => ⟪M y, y⟫) :=
    ContDiff.inner ℝ M.contDiff contDiff_id
  exact ((h1.div_const 2).add L.contDiff).add contDiff_const

theorem hessOp_modelQuad_sub {u : ℝ⁴ → ℝ} {M : ℝ⁴ →L[ℝ] ℝ⁴} (hM : M.IsSymmetric)
    (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ) {x : ℝ⁴} (hu : ContDiffAt ℝ 2 u x) :
    hessOp (fun y => u y - (⟪M y, y⟫ / 2 + L y + c)) x = hessOp u x - M := by
  have hq : ContDiffAt ℝ 2 (fun y : ℝ⁴ => ⟪M y, y⟫ / 2 + L y + c) x :=
    (contDiff_modelQuad M L c).contDiffAt
  have h := hessOp_sub_of_contDiffAt (φ := u)
    (ψ := fun y : ℝ⁴ => ⟪M y, y⟫ / 2 + L y + c) hu hq
  rw [show (u - fun y : ℝ⁴ => ⟪M y, y⟫ / 2 + L y + c)
      = (fun y => u y - (⟪M y, y⟫ / 2 + L y + c)) from rfl] at h
  rw [h, hessOp_modelQuad hM L c x]

theorem hessOp_scaled_sub_quad {u : ℝ⁴ → ℝ} {M : ℝ⁴ →L[ℝ] ℝ⁴} (hM : M.IsSymmetric)
    (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ) {R ρ : ℝ} (hR : R ≠ 0) (hρ : ρ ≠ 0) {x : ℝ⁴}
    (hu : ContDiffAt ℝ 2 u (R • x)) :
    hessOp (fun y => (u (R • y) - (⟪M (R • y), R • y⟫ / 2 + L (R • y) + c)) / (ρ * R ^ 2))
        x = (1 / ρ) • (hessOp u (R • x) - M) := by
  have hw : ContDiffAt ℝ 2 (fun y : ℝ⁴ => u y - (⟪M y, y⟫ / 2 + L y + c)) (R • x) :=
    hu.sub (contDiff_modelQuad M L c).contDiffAt
  have hsc := hessOp_scaled_comp (w := fun y : ℝ⁴ => u y - (⟪M y, y⟫ / 2 + L y + c))
    hR hρ hw (x := x)
  rw [hessOp_modelQuad_sub hM L c hu] at hsc
  rw [show (fun y : ℝ⁴ => (fun y : ℝ⁴ => u y - (⟪M y, y⟫ / 2 + L y + c)) (R • y) / (ρ * R ^ 2))
      = (fun y => (u (R • y) - (⟪M (R • y), R • y⟫ / 2 + L (R • y) + c)) / (ρ * R ^ 2))
      from rfl] at hsc
  exact hsc

/-- The one-step algebraic identity for the model quadratics. -/
theorem modelQuad_add_step (M P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (L P₁ : ℝ⁴ →L[ℝ] ℝ) (c P₀ ρ R : ℝ)
    (hR : R ≠ 0) (x : ℝ⁴) :
    (⟪(M + ρ • P₂) x, x⟫ / 2 + (L + (ρ * R) • P₁) x + (c + ρ * R ^ 2 * P₀))
      = (⟪M x, x⟫ / 2 + L x + c)
        + ρ * R ^ 2 * (⟪P₂ (R⁻¹ • x), R⁻¹ • x⟫ / 2 + P₁ (R⁻¹ • x) + P₀) := by
  have hA : ⟪(M + ρ • P₂) x, x⟫ = ⟪M x, x⟫ + ρ * ⟪P₂ x, x⟫ := by
    simp [inner_add_left, real_inner_smul_left]
  have hB : (L + (ρ * R) • P₁) x = L x + (ρ * R) * P₁ x := by
    simp
  have hC : ⟪P₂ (R⁻¹ • x), R⁻¹ • x⟫ = R⁻¹ * (R⁻¹ * ⟪P₂ x, x⟫) := by
    simp [real_inner_smul_left, real_inner_smul_right]
  have hD : P₁ (R⁻¹ • x) = R⁻¹ * P₁ x := by simp
  have h1 : ρ * R ^ 2 * (R⁻¹ * (R⁻¹ * ⟪P₂ x, x⟫) / 2) = ρ * ⟪P₂ x, x⟫ / 2 := by
    field_simp
  have h2 : ρ * R ^ 2 * (R⁻¹ * P₁ x) = ρ * R * P₁ x := by
    field_simp
  rw [hA, hB, hC, hD, mul_add, mul_add, h1, h2]
  ring


theorem sqrt_mul_sq_eq_rpow {t : ℝ} (ht : 0 < t) : Real.sqrt t * t ^ 2 = t ^ ((5:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_add ht]
  norm_num

theorem cofOp_smul (a : ℝ) (S : ℝ⁴ →L[ℝ] ℝ⁴) : cofOp (a • S) = a • cofOp S := by
  unfold cofOp
  rw [trOp_smul, smul_sub]
  congr 1
  rw [smul_smul]


theorem geom_step (q Λ K : ℝ) (hq : 1 - q ≠ 0) (k : ℕ) :
    Λ * K * (1 - q ^ k) / (1 - q) + Λ * q ^ k * K = Λ * K * (1 - q ^ (k + 1)) / (1 - q) := by
  rw [pow_succ]
  field_simp
  ring

theorem geom_step_mul (q Λ K x : ℝ) (hq : 1 - q ≠ 0) (k : ℕ) :
    Λ * K * (1 - q ^ k) / (1 - q) * x + Λ * q ^ k * K * x
      = Λ * K * (1 - q ^ (k + 1)) / (1 - q) * x := by
  rw [pow_succ]
  field_simp
  ring

theorem IterInv_step {c c' θ Λ R₀ : ℝ} {A₀ : ℝ⁴ →L[ℝ] ℝ⁴} {u : ℝ⁴ → ℝ} {k : ℕ} {s : IterState}
    (hc : 0 < c) (hc' : 0 < c')
    (hθpos : 0 < θ) (hθ256 : θ ≤ 1 / 256)
    {ε : ℝ} (hFlat : FlatGood (c / 2) (2 * c') θ ε)
    (hΛpos : 0 < Λ) (hΛε : Λ ≤ ε) (hR₀pos : 0 < R₀) (hR₀1 : R₀ ≤ 1)
    (hA₀sym : A₀.IsSymmetric)
    (hdriftc : Λ * Kcof θ / (1 - qDecay θ) ≤ c / 2)
    (hdriftc' : Λ * Kcof θ / (1 - qDecay θ) ≤ c')
    (hu : ContDiffOn ℝ 2 u (ball 0 2))
    (hueq : ∀ x ∈ ball 0 2, s2 (A₀ + hessOp u x) = 1)
    (hupos : ∀ x ∈ ball 0 2, 0 < trOp (A₀ + hessOp u x))
    (hinv : IterInv c c' θ Λ R₀ A₀ u k s) :
    ∃ s', IterInv c c' θ Λ R₀ A₀ u (k + 1) s' := by
  unfold IterInv at hinv
  obtain ⟨hMsym, hRpos, hRk, hρpos, hρk, hdrift0, hdriftle, hMbd, hA1, hAtr, hAcq, hAcq', hflat⟩ := hinv
  have hq0 : 0 < qDecay θ := qDecay_pos hθpos
  have hq1 : qDecay θ ≤ 1 / 4 := qDecay_le_quarter hθ256
  have hqlt : qDecay θ < 1 := by linarith
  have h1mq : 0 < 1 - qDecay θ := by linarith
  have hKcof0 : 0 < Kcof θ := Kcof_pos hθpos
  have hθ16 : θ ≤ 1 / 16 := by linarith
  have hRne : s.R ≠ 0 := ne_of_gt hRpos
  have hρne : s.ρ ≠ 0 := ne_of_gt hρpos
  have hRle : s.R ≤ R₀ := by
    rw [hRk]
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_one₀ (by linarith) (by linarith)) hR₀pos.le)
      (le_of_eq (mul_one _))
  have hR1 : s.R ≤ 1 := le_trans hRle hR₀1
  have hρle : s.ρ ≤ Λ := by
    rw [hρk]
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_one₀ hq0.le (by linarith : qDecay θ ≤ 1)) hΛpos.le)
      (le_of_eq (mul_one _))
  have hρε : s.ρ ≤ ε := le_trans hρle hΛε
  -- the normalised function
  set W : ℝ⁴ → ℝ := fun x =>
    (u (s.R • x) - (⟪s.M (s.R • x), s.R • x⟫ / 2 + s.L (s.R • x) + s.c)) / (s.ρ * s.R ^ 2)
    with hWdef
  have hsmul_mem : ∀ {x : ℝ⁴}, x ∈ ball 0 2 → s.R • x ∈ ball 0 2 := by
    intro x hx
    rw [mem_ball, dist_zero_right] at hx ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    nlinarith
  have hWhess : ∀ x ∈ ball 0 2, hessOp W x = (1 / s.ρ) • (hessOp u (s.R • x) - s.M) := by
    intro x hx
    have hcd : ContDiffAt ℝ 2 u (s.R • x) := hu.contDiffAt (isOpen_ball.mem_nhds (hsmul_mem hx))
    have h := hessOp_scaled_sub_quad hMsym s.L s.c hRne hρne hcd
    rw [hWdef]
    exact h
  have hAeq : ∀ x ∈ ball 0 2,
      (A₀ + s.M) + s.ρ • hessOp W x = A₀ + hessOp u (s.R • x) := by
    intro x hx
    rw [hWhess x hx, smul_smul, one_div, mul_inv_cancel₀ hρne, one_smul]
    abel
  have hWeq : ∀ x ∈ ball 0 2, Fop (cofOp (A₀ + s.M)) s.ρ (hessOp W x) = 0 := by
    intro x hx
    have hsym : (hessOp W x).IsSymmetric := by
      rw [hWhess x hx]
      exact ((hessOp_symm_of_contDiffAt
        (hu.contDiffAt (isOpen_ball.mem_nhds (hsmul_mem hx)))).sub hMsym).smul (by simp)
    rw [fop_eq_zero_iff_s2 (hA₀sym.add hMsym) hsym hρne hA1, hAeq x hx]
    exact hueq _ (hsmul_mem hx)
  have hWpos : ∀ x ∈ ball 0 2, 0 < trOp ((A₀ + s.M) + s.ρ • hessOp W x) := by
    intro x hx
    rw [hAeq x hx]
    exact hupos _ (hsmul_mem hx)
  have hW1 : ∀ x ∈ ball 0 2, |W x| ≤ 1 := by
    intro x hx
    have hx2 : ‖x‖ < 2 := by
      rw [mem_ball, dist_zero_right] at hx; exact hx
    have hRu : s.R • x ∈ ball 0 (2 * s.R) := by
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
      nlinarith
    have hfl := hflat _ hRu
    have hden : 0 < s.ρ * s.R ^ 2 := by positivity
    rw [hWdef]
    simp only
    rw [abs_div, abs_of_pos hden, div_le_one hden]
    simpa using hfl
  have hWcd : ContDiffOn ℝ 2 W (ball 0 2) := by
    have hWu : ContDiffOn ℝ 2 (fun y : ℝ⁴ => u (s.R • y)) (ball 0 2) :=
      hu.comp ((contDiff_id.const_smul s.R).contDiffOn) (fun y hy => hsmul_mem hy)
    have hq : ContDiffOn ℝ 2 (fun y : ℝ⁴ =>
        ⟪s.M (s.R • y), s.R • y⟫ / 2 + s.L (s.R • y) + s.c) (ball 0 2) :=
      (((contDiff_modelQuad s.M s.L s.c).comp (contDiff_id.const_smul s.R)).contDiffOn).mono
        (Set.subset_univ _)
    have h := (hWu.sub hq).div_const (s.ρ * s.R ^ 2)
    refine h.congr fun y hy => ?_
    rw [hWdef]
  -- the class conditions of `A = A₀ + s.M`
  have hdriftaux : Λ * Kcof θ * (1 - qDecay θ ^ k) / (1 - qDecay θ) ≤ Λ * Kcof θ / (1 - qDecay θ) := by
    have h8 : qDecay θ ^ k ≤ 1 := pow_le_one₀ hq0.le (by linarith : qDecay θ ≤ 1)
    have h9 : 0 ≤ Λ * Kcof θ := mul_nonneg hΛpos.le hKcof0.le
    rw [div_le_div_iff_of_pos_right h1mq]
    nlinarith
  have hdriftc2 : s.drift ≤ c / 2 := le_trans (le_trans hdriftle hdriftaux) hdriftc
  have hdriftc'2 : s.drift ≤ c' := le_trans (le_trans hdriftle hdriftaux) hdriftc'
  obtain ⟨P₂, P₁, P₀, hP₂sym, hP₂eq, hPbd, hP₂bd, hP₂cof⟩ :=
    step_quad hc hθpos hθ16 hFlat (hA₀sym.add hMsym) hA1 hAtr
      (fun v => by
        have h1 := hAcq v
        have h2 : (c / 2) * ‖v‖ ^ 2 ≤ (c - s.drift) * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
        linarith)
      (fun v => by
        have h1 := hAcq' v
        have h2 : (c' + s.drift) * ‖v‖ ^ 2 ≤ (2 * c') * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
        linarith)
      hρpos hρε hWcd hWeq hWpos hW1
  -- the cofOp identity at the new base

  have hcof_new : ∀ v : ℝ⁴,
      ⟪cofOp (A₀ + (s.M + s.ρ • P₂)) v, v⟫
        = ⟪cofOp (A₀ + s.M) v, v⟫ + s.ρ * ⟪cofOp P₂ v, v⟫ := by
    intro v
    rw [show A₀ + (s.M + s.ρ • P₂) = (A₀ + s.M) + s.ρ • P₂ from by abel, cofOp_add,
      cofOp_smul]
    simp [inner_add_left, real_inner_smul_left]
  have hdriftstep : s.drift + s.ρ * Kcof θ
      ≤ Λ * Kcof θ * (1 - qDecay θ ^ (k + 1)) / (1 - qDecay θ) := by
    rw [hρk]
    have h := geom_step (qDecay θ) Λ (Kcof θ) (ne_of_gt h1mq) k
    linarith
  have hdriftnew : s.drift + s.ρ * Kcof θ ≤ Λ * Kcof θ / (1 - qDecay θ) := by
    refine le_trans hdriftstep ?_
    have h8 : qDecay θ ^ (k + 1) ≤ 1 := pow_le_one₀ hq0.le (by linarith : qDecay θ ≤ 1)
    rw [div_le_div_iff_of_pos_right h1mq]
    have h9 : 0 ≤ Λ * Kcof θ * qDecay θ ^ (k + 1) :=
      mul_nonneg (mul_nonneg hΛpos.le hKcof0.le) (pow_nonneg hq0.le _)
    nlinarith [h9]
  have hlow : ∀ v : ℝ⁴, (c - (s.drift + s.ρ * Kcof θ)) * ‖v‖ ^ 2
      ≤ ⟪cofOp (A₀ + (s.M + s.ρ • P₂)) v, v⟫ := by
    intro v
    rw [hcof_new v]
    have h1 := hAcq v
    have h2 := hP₂cof v
    have h2' : ⟪cofOp P₂ v, v⟫ ≥ -(Kcof θ * ‖v‖ ^ 2) := by
      have h3 : |⟪cofOp P₂ v, v⟫| ≤ Kcof θ * ‖v‖ ^ 2 := by
        have h : (5 : ℝ) * (8 / θ ^ 2) = Kcof θ := rfl
        rwa [h] at h2
      exact (abs_le.mp h3).1
    have h4 : s.ρ * ⟪cofOp P₂ v, v⟫ ≥ -(s.ρ * Kcof θ * ‖v‖ ^ 2) := by
      have h5 : s.ρ * (-(Kcof θ * ‖v‖ ^ 2)) ≤ s.ρ * ⟪cofOp P₂ v, v⟫ :=
        mul_le_mul_of_nonneg_left h2' hρpos.le
      have h6 : s.ρ * (-(Kcof θ * ‖v‖ ^ 2)) = -(s.ρ * Kcof θ * ‖v‖ ^ 2) := by ring
      linarith [h5, h6]
    have hexp : (c - (s.drift + s.ρ * Kcof θ)) * ‖v‖ ^ 2
        = (c - s.drift) * ‖v‖ ^ 2 - s.ρ * Kcof θ * ‖v‖ ^ 2 := by ring
    rw [hexp]
    linarith [h1, h4]
  have hlow2 : ∀ v : ℝ⁴, (c / 2) * ‖v‖ ^ 2
      ≤ ⟪cofOp (A₀ + (s.M + s.ρ • P₂)) v, v⟫ := by
    intro v
    have h3 : c / 2 ≤ c - (s.drift + s.ρ * Kcof θ) := by linarith [le_trans hdriftnew hdriftc]
    exact le_trans (mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖v‖)) (hlow v)
  have hup : ∀ v : ℝ⁴, ⟪cofOp (A₀ + (s.M + s.ρ • P₂)) v, v⟫
      ≤ (c' + (s.drift + s.ρ * Kcof θ)) * ‖v‖ ^ 2 := by
    intro v
    rw [hcof_new v]
    have h1 := hAcq' v
    have h2 := hP₂cof v
    have h2' : ⟪cofOp P₂ v, v⟫ ≤ Kcof θ * ‖v‖ ^ 2 := by
      have h3 : |⟪cofOp P₂ v, v⟫| ≤ Kcof θ * ‖v‖ ^ 2 := by
        have h : (5 : ℝ) * (8 / θ ^ 2) = Kcof θ := rfl
        rwa [h] at h2
      exact (abs_le.mp h3).2
    have h4 : s.ρ * ⟪cofOp P₂ v, v⟫ ≤ s.ρ * Kcof θ * ‖v‖ ^ 2 := by
      have h5 := mul_le_mul_of_nonneg_left h2' hρpos.le
      nlinarith [h5, sq_nonneg ‖v‖]
    have hexp : (c' + (s.drift + s.ρ * Kcof θ)) * ‖v‖ ^ 2
        = (c' + s.drift) * ‖v‖ ^ 2 + s.ρ * Kcof θ * ‖v‖ ^ 2 := by ring
    rw [hexp]
    linarith [h1, h4]
  have hAtr' : 0 < trOp (A₀ + (s.M + s.ρ • P₂)) := by
    have h1 : 3 * trOp (A₀ + (s.M + s.ρ • P₂))
        = ∑ i : Fin 4, ⟪cofOp (A₀ + (s.M + s.ρ • P₂)) (stdB4 i), stdB4 i⟫ := by
      rw [← trOp_cofOp, trOp_eq_sum]
    have h2 : (∑ _i : Fin 4, c / 2 : ℝ) ≤
        ∑ i : Fin 4, ⟪cofOp (A₀ + (s.M + s.ρ • P₂)) (stdB4 i), stdB4 i⟫ := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h := hlow2 (stdB4 i)
      rwa [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at h
    have h3 : (∑ _i : Fin 4, c / 2 : ℝ) = 2 * c := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    linarith
  refine ⟨⟨s.M + s.ρ • P₂, s.L + (s.ρ * s.R) • P₁, s.c + s.ρ * s.R ^ 2 * P₀,
      θ * s.R / 2, qDecay θ * s.ρ, s.drift + s.ρ * Kcof θ⟩, ?_⟩
  unfold IterInv
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hMsym.add (hP₂sym.smul (by simp))
  · positivity
  · rw [hRk, pow_succ]; ring
  · positivity
  · rw [hρk, pow_succ]; ring
  · exact add_nonneg hdrift0 (mul_nonneg hρpos.le hKcof0.le)
  · exact hdriftstep
  · intro v
    have h3 : ⟪(s.M + s.ρ • P₂) v, v⟫ = ⟪s.M v, v⟫ + s.ρ * ⟪P₂ v, v⟫ := by
      simp [inner_add_left, real_inner_smul_left]
    rw [h3]
    have h2 := hP₂bd v
    have h2' : |⟪P₂ v, v⟫| ≤ Kquad θ * ‖v‖ ^ 2 := by
      have h : (8 : ℝ) / θ ^ 2 = Kquad θ := rfl
      rwa [h] at h2
    have h1 := hMbd v
    have hb1 : |s.ρ * ⟪P₂ v, v⟫| ≤ Λ * qDecay θ ^ k * Kquad θ * ‖v‖ ^ 2 := by
      rw [abs_mul, abs_of_pos hρpos]
      calc s.ρ * |⟪P₂ v, v⟫| ≤ s.ρ * (Kquad θ * ‖v‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h2' hρpos.le
        _ = Λ * qDecay θ ^ k * Kquad θ * ‖v‖ ^ 2 := by rw [hρk]; ring
    have h1' : |⟪s.M v, v⟫| ≤ Λ * Kquad θ * (1 - qDecay θ ^ k) / (1 - qDecay θ) * ‖v‖ ^ 2 := by
      rw [← mul_comm (Kquad θ) Λ]; exact h1
    have hb3 : Λ * Kquad θ * (1 - qDecay θ ^ k) / (1 - qDecay θ) * ‖v‖ ^ 2
        + Λ * qDecay θ ^ k * Kquad θ * ‖v‖ ^ 2
        = Λ * Kquad θ * (1 - qDecay θ ^ (k + 1)) / (1 - qDecay θ) * ‖v‖ ^ 2 :=
      geom_step_mul (qDecay θ) Λ (Kquad θ) (‖v‖ ^ 2) (ne_of_gt h1mq) k
    calc |⟪s.M v, v⟫ + s.ρ * ⟪P₂ v, v⟫|
        ≤ |⟪s.M v, v⟫| + |s.ρ * ⟪P₂ v, v⟫| := abs_add_le _ _
      _ ≤ Λ * Kquad θ * (1 - qDecay θ ^ k) / (1 - qDecay θ) * ‖v‖ ^ 2
            + Λ * qDecay θ ^ k * Kquad θ * ‖v‖ ^ 2 := by linarith
      _ = Λ * Kquad θ * (1 - qDecay θ ^ (k + 1)) / (1 - qDecay θ) * ‖v‖ ^ 2 := hb3
      _ = Kquad θ * Λ * (1 - qDecay θ ^ (k + 1)) / (1 - qDecay θ) * ‖v‖ ^ 2 := by ring
  · have h := (fop_eq_zero_iff_s2 (hA₀sym.add hMsym) hP₂sym hρne hA1).mp hP₂eq
    rwa [show A₀ + (s.M + s.ρ • P₂) = (A₀ + s.M) + s.ρ • P₂ from by abel]
  · exact hAtr'
  · exact hlow
  · exact hup
  · intro x hx
    rw [mem_ball, dist_zero_right] at hx
    have hx' : ‖x‖ < θ * s.R := by linarith
    set z : ℝ⁴ := s.R⁻¹ • x with hzdef
    have hRz : s.R • z = x := by
      rw [hzdef, smul_smul, mul_inv_cancel₀ hRne, one_smul]
    have hzn : ‖z‖ ≤ θ := by
      rw [hzdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
      have h : s.R⁻¹ * ‖x‖ < θ := by
        calc s.R⁻¹ * ‖x‖ < s.R⁻¹ * (θ * s.R) := mul_lt_mul_of_pos_left hx' (inv_pos.mpr hRpos)
          _ = θ := by field_simp
      exact h.le
    have hWz := hPbd z (by rwa [mem_closedBall, dist_zero_right])
    have hWval : s.ρ * s.R ^ 2 * W z
        = u (s.R • z) - (⟪s.M (s.R • z), s.R • z⟫ / 2 + s.L (s.R • z) + s.c) := by
      rw [hWdef]; field_simp
    have hWval' : s.ρ * s.R ^ 2 * W z = u x - (⟪s.M x, x⟫ / 2 + s.L x + s.c) := by
      rw [← hRz]; exact hWval
    have hQ' : (⟪(s.M + s.ρ • P₂) x, x⟫ / 2 + (s.L + (s.ρ * s.R) • P₁) x
          + (s.c + s.ρ * s.R ^ 2 * P₀))
        = (⟪s.M x, x⟫ / 2 + s.L x + s.c)
          + s.ρ * s.R ^ 2 * (⟪P₂ z, z⟫ / 2 + P₁ z + P₀) := by
      have hmq := modelQuad_add_step s.M P₂ s.L P₁ s.c P₀ s.ρ s.R hRne x
      rwa [show s.R⁻¹ • x = z from hzdef.symm] at hmq
    have hKey : u x - (⟪(s.M + s.ρ • P₂) x, x⟫ / 2 + (s.L + (s.ρ * s.R) • P₁) x
          + (s.c + s.ρ * s.R ^ 2 * P₀))
        = s.ρ * s.R ^ 2 * (W z - (⟪P₂ z, z⟫ / 2 + P₁ z + P₀)) := by
      rw [hQ']
      have hv : u x - (⟪s.M x, x⟫ / 2 + s.L x + s.c) = s.ρ * s.R ^ 2 * W z := hWval'.symm
      rw [show u x - ((⟪s.M x, x⟫ / 2 + s.L x + s.c)
            + s.ρ * s.R ^ 2 * (⟪P₂ z, z⟫ / 2 + P₁ z + P₀))
          = (u x - (⟪s.M x, x⟫ / 2 + s.L x + s.c))
            - s.ρ * s.R ^ 2 * (⟪P₂ z, z⟫ / 2 + P₁ z + P₀) from by ring, hv]
      ring
    have hden : 0 < s.ρ * s.R ^ 2 := by positivity
    have hfinal : |u x - (⟪(s.M + s.ρ • P₂) x, x⟫ / 2 + (s.L + (s.ρ * s.R) • P₁) x
        + (s.c + s.ρ * s.R ^ 2 * P₀))| ≤ s.ρ * s.R ^ 2 * θ ^ ((5 : ℝ) / 2) := by
      rw [hKey, abs_mul, abs_of_pos hden]
      exact mul_le_mul_of_nonneg_left hWz hden.le
    have hRHS : (qDecay θ * s.ρ) * (θ * s.R / 2) ^ 2 = s.ρ * s.R ^ 2 * θ ^ ((5 : ℝ) / 2) := by
      have hsq : (θ * s.R / 2) ^ 2 = θ ^ 2 * s.R ^ 2 / 4 := by ring
      have key : 4 * Real.sqrt θ * θ ^ 2 = 4 * θ ^ ((5 : ℝ) / 2) := by
        have h := sqrt_mul_sq_eq_rpow hθpos
        linarith
      rw [qDecay, hsq,
        show 4 * Real.sqrt θ * s.ρ * (θ ^ 2 * s.R ^ 2 / 4)
            = (4 * Real.sqrt θ * θ ^ 2) * (s.ρ * s.R ^ 2 / 4) from by ring, key]
      ring
    rwa [hRHS]

end

end Submission
