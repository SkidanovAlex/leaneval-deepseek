import Mathlib
import Submission.Work.Diff.C.rhess_comp
import Submission.Work.Diff.C.hess_upper
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.mvfderiv_second_along_fields_contMDiffAt
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## Bilinearity of `rhess` and the symmetry of the Hessian at a point -/

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}

lemma rhess_add_left_pt {F : M → ℝ}
    (x : M) (V V' W : TangentSpace I x) :
    rhess cov F x (V + V') W = rhess cov F x V W + rhess cov F x V' W := by
  simp only [rhess, map_add, inner_add_left]

lemma rhess_smul_left_pt {F : M → ℝ}
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    rhess cov F x (c • V) W = c * rhess cov F x V W := by
  simp only [rhess, map_smul, real_inner_smul_left]

lemma rhess_add_right_pt {F : M → ℝ}
    (x : M) (V W W' : TangentSpace I x) :
    rhess cov F x V (W + W') = rhess cov F x V W + rhess cov F x V W' := by
  simp only [rhess, inner_add_right]

lemma rhess_smul_right_pt {F : M → ℝ}
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    rhess cov F x V (c • W) = c * rhess cov F x V W := by
  simp only [rhess, real_inner_smul_right]

/-- **Metric compatibility at a point, from the challenge's form of it.**

The hypothesis `IsMetricCompatible cov` states the identity `v·⟨σ, τ⟩ = ⟨∇_v σ, τ⟩ + ⟨σ, ∇_v τ⟩`
only for *globally* `C^∞` sections `σ`, `τ` (and an arbitrary direction vector `v`).  Mathlib's
`CovariantDerivative.IsMetricCompatible` (the `derivMetricTensor` form) is equivalent to the same
identity for sections that are only differentiable *at the point* `x`, and this is what the
computation of the Hessian needs (its first slot is the gradient `y ↦ ∇f(y)` of a function that is
only smooth at `x`).  The bridge is the usual tensoriality of `derivMetricTensor`: its value at `x`
only depends on the *values* `σ x`, `τ x`, `v` of its arguments, so one may replace `σ`, `τ` by
globally `C^∞` sections with the same values at `x`
(`Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq`). -/
theorem mvfderiv_inner_eq_of_isMetricCompatible_pt
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {σ τ : Π y : M, TangentSpace I y} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => inner ℝ (σ y) (τ y)) x v =
      inner ℝ (cov σ x v) (τ x) + inner ℝ (σ x) (cov τ x v) := by
  obtain ⟨Y, hYsm, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) (σ x)
  obtain ⟨Z, hZsm, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) (τ x)
  have hYmd : MDiffAt (T% Y) x := hYsm.mdifferentiableAt (by simp)
  have hZmd : MDiffAt (T% Z) x := hZsm.mdifferentiableAt (by simp)
  have keyY := CovariantDerivative.derivMetricTensor_apply (cov := cov) (x := x) (σ := Y)
    (τ := Z) (X := fun _ : M => v) hYmd hZmd
  beta_reduce at keyY
  have hhm := hmet Y Z hYsm hZsm x v
  have key : cov.derivMetricTensor x (σ x) (τ x) v = 0 := by
    rw [← hYx, ← hZx, keyY, hhm]
    ring
  have h2 := CovariantDerivative.derivMetricTensor_apply (cov := cov) (x := x) (σ := σ)
    (τ := τ) (X := fun _ : M => v) hσ hτ
  beta_reduce at h2
  rw [key] at h2
  linarith

-- NOTE for the area owner: the theorem below is a sorry-free replacement of
-- `Work.Diff.C.rhess_symm` (`Submission/Work/Diff/C/rhess_symm.lean`), whose proof was missing
-- exactly the Lie-bracket identity used here, available sorry-free as
-- `Work.Diff.C.mvfderiv_second_along_fields_contMDiffAt`
-- (`Submission/Work/Diff/C/mvfderiv_second_along_fields_contMDiffAt.lean`).
-- `Submission/Work/Diff/C/fcos_inputs.lean` becomes compilable once its use of `rhess_symm`
-- (in `rhess_expansion`) is replaced by `rhess_symm_pt` imported from this module.

/-- **Symmetry of the Hessian at a point, for a function that is only smooth *at* that point.**

`Work.Diff.C.rhess` is symmetric in its two vector slots whenever `f` is `C^∞` at `x`, metric
compatibility and torsion-freeness being the only inputs.  The hypothesis `CMDiffAt ∞ f x` is
Mathlib's weak pointwise notion, which does *not* give a neighbourhood on which `f` is `C^∞`; the
Lie-bracket identity at a point for such an `f` is
`Work.Diff.C.mvfderiv_second_along_fields_contMDiffAt`. -/
theorem rhess_symm_pt
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {f : M → ℝ} {x : M} (hf : CMDiffAt ∞ f x) (V W : TangentSpace I x) :
    rhess cov f x V W = rhess cov f x W V := by
  -- The gradient field, differentiable at `x`
  have hσmd : MDiffAt (T% (fun y : M => rgrad (I := I) f y)) x :=
    (grad_smoothAt (I := I) (F := f) (x := x) hf).mdifferentiableAt (by simp)
  -- Globally smooth extensions of `V` and `W`
  obtain ⟨X, hXsm, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) V
  obtain ⟨Y, hYsm, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) W
  have hXmd : MDiffAt (T% X) x := hXsm.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% Y) x := hYsm.mdifferentiableAt (by simp)
  -- `⟪∇f, ·⟫ = d% f(·)`, pointwise
  have hfun1 : (fun y : M => inner ℝ (rgrad (I := I) f y) (Y y))
      = (fun y : M => mvfderiv I f y (Y y)) := by
    funext y; exact inner_rgrad_mvfderiv f y (Y y)
  have hfun2 : (fun y : M => inner ℝ (rgrad (I := I) f y) (X y))
      = (fun y : M => mvfderiv I f y (X y)) := by
    funext y; exact inner_rgrad_mvfderiv f y (X y)
  -- metric compatibility, in the two pairings we need
  have hA := mvfderiv_inner_eq_of_isMetricCompatible_pt cov hmet hσmd hYmd V
  rw [hfun1, ← hXx] at hA
  have hC := mvfderiv_inner_eq_of_isMetricCompatible_pt cov hmet hσmd hXmd W
  rw [hfun2, ← hYx] at hC
  -- second derivatives of `f` commute up to the Lie bracket
  have hcl : mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x)
      = mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)
        + mvfderiv I f x (mlieBracket I X Y x) :=
    mvfderiv_second_along_fields_contMDiffAt (I := I) (M := M) (f := f) (X := X) (Y := Y)
      hf hXsm hYsm
  rw [← inner_rgrad_mvfderiv f x (mlieBracket I X Y x)] at hcl
  -- torsion-freeness: `∇_X Y - ∇_Y X = [X,Y]`
  have htorx : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    (CovariantDerivative.torsion_eq_zero_iff (𝕜 := ℝ) (E := E) (I := I) (M := M) cov).mp
      htor hXmd hYmd
  -- the vector of the inner product with `∇f` vanishes, by torsion-freeness
  have hpe : inner ℝ (rgrad (I := I) f x)
      (cov X x (Y x) + mlieBracket I X Y x - cov Y x (X x)) = 0 := by
    have h0 : cov X x (Y x) + mlieBracket I X Y x - cov Y x (X x) = 0 := by
      rw [← htorx]; abel
    rw [h0, inner_zero_right]
  rw [inner_sub_right, inner_add_right] at hpe
  -- conclude
  show inner ℝ (cov (fun y : M => rgrad (I := I) f y) x V) W
    = inner ℝ (cov (fun y : M => rgrad (I := I) f y) x W) V
  rw [← hXx, ← hYx]
  linarith

/-- The expansion of the quadratic form of `rhess` (uses the symmetry of the Hessian). -/
lemma rhess_expansion_pt (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x) (V W : TangentSpace I x) (t : ℝ) :
    rhess cov F x (V + t • W) (V + t • W)
      = rhess cov F x V V + 2 * t * rhess cov F x V W + t ^ 2 * rhess cov F x W W := by
  have hsym : rhess cov F x W V = rhess cov F x V W := rhess_symm_pt hmet htor hF W V
  rw [rhess_add_left_pt]
  rw [rhess_add_right_pt, rhess_add_right_pt]
  rw [rhess_smul_right_pt]
  rw [rhess_smul_left_pt, rhess_smul_left_pt, rhess_smul_right_pt]
  rw [hsym]
  ring

end Helpers

/-- A symmetric-bilinear-form bound: if `0 ≤ E x x ≤ ε‖x‖²` and the quadratic function
`t ↦ E (a + t b) (a + t b)` expands as `E a a + 2t·E a b + t²·E b b`, then `|E a b| ≤ ε‖a‖‖b‖`. -/
lemma abs_le_of_quad_expansion_pt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {E : V → V → ℝ} {ε : ℝ} (hε : 0 ≤ ε) {a b : V}
    (hpos : ∀ x, 0 ≤ E x x) (hle : ∀ x, E x x ≤ ε * ‖x‖ ^ 2)
    (hexp : ∀ t : ℝ, E (a + t • b) (a + t • b) = E a a + 2 * t * E a b + t ^ 2 * E b b) :
    |E a b| ≤ ε * ‖a‖ * ‖b‖ := by
  have hεnn : 0 ≤ ε * ‖a‖ * ‖b‖ := by positivity
  have hquad : ∀ t : ℝ, 0 ≤ E a a + 2 * t * E a b + t ^ 2 * E b b := fun t => by
    rw [← hexp t]; exact hpos _
  have hC : 0 ≤ E b b := hpos b
  rcases lt_or_eq_of_le hC with hCpos | hCzero
  · have h1 : (E a b) ^ 2 ≤ E a a * E b b := by
      have h2 : 0 ≤ E a a + 2 * (-(E a b) / E b b) * E a b + (-(E a b) / E b b) ^ 2 * E b b :=
        hquad _
      have h4 : 2 * (-(E a b) / E b b) * E a b + (-(E a b) / E b b) ^ 2 * E b b
          = -((E a b) ^ 2 / E b b) := by
        field_simp
        ring
      have h3 : (E a b) ^ 2 / E b b ≤ E a a := by linarith [h2, h4]
      have hmul : (E a b) ^ 2 / E b b * E b b ≤ E a a * E b b :=
        mul_le_mul_of_nonneg_right h3 hC
      rwa [div_mul_cancel₀ _ (ne_of_gt hCpos)] at hmul
    have h7 : (E a b) ^ 2 ≤ (ε * ‖a‖ ^ 2) * (ε * ‖b‖ ^ 2) :=
      le_trans h1 (mul_le_mul (hle a) (hle b) hC (by positivity))
    have h9 : (E a b) ^ 2 ≤ (ε * ‖a‖ * ‖b‖) ^ 2 := by
      have : (ε * ‖a‖ ^ 2) * (ε * ‖b‖ ^ 2) = (ε * ‖a‖ * ‖b‖) ^ 2 := by ring
      rw [← this]; exact h7
    exact abs_le_of_sq_le_sq h9 hεnn
  · have hzero : E a b = 0 := by
      by_contra hne
      have h1 : 0 ≤ E a a + 2 * (-(E a a + 1) / (2 * E a b)) * E a b
          + (-(E a a + 1) / (2 * E a b)) ^ 2 * E b b := hquad _
      have hCz : E b b = 0 := hCzero.symm
      rw [hCz, mul_zero, add_zero] at h1
      have h2 : 2 * (-(E a a + 1) / (2 * E a b)) * E a b = -(E a a + 1) := by
        field_simp
      rw [h2] at h1
      linarith
    rw [hzero, abs_zero]
    exact hεnn

/-- **The pointwise Hessian bound for `fcos q = cos ∘ d(q,·)` away from the centre.**
(`∞` is smoothness, i.e. `((⊤ : ℕ∞) : WithTop ℕ∞)`.)

This is the pointwise version of `Submission.Work.Diff.C.hessBound_region` in
`Submission/Work/Diff/C/fcos_inputs.lean`, which contains a complete proof of the *region* version.
Two remarks:
* that file currently fails to compile only because it uses `rhess_symm` without importing it;
  `Work.Diff.C.rhess_symm` is stated in `Submission/Work/Diff/C/rhess_symm.lean`, whose single
  `sorry` is the identity `mvfderiv_second_along_fields` of
  `Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields` (PROVED), so
  `rhess_symm` is obtained by importing that module;
* the bilinearity/expansion lemmas `rhess_add_left'`, `rhess_add_right'`, `rhess_smul_left'`,
  `rhess_smul_right'`, `rhess_expansion` and `abs_le_of_quad_expansion` are all PROVED inside
  `fcos_inputs.lean` (import it, or copy them).
The proof: `rhess (cos ∘ d)(x)(V,W) = -cos d·⟪∇d,V⟫⟪∇d,W⟫ - sin d·rhess d(x)(V,W)` for
`d = rdist q x` (`Work.Diff.C.rhess_comp`, PROVED, with `mvfderiv I d x V = ⟪∇d,V⟫`); `hUpper`
and `hLower` bound `rhess d` on `V⊥`, and `hkey` gives
`cos d - sin d·√(1+η)·cot(√(1+η)d) ≤ ε₁`; hence for the bilinear form
`E(V,W) = rhess (cos ∘ d)(x)(V,W) + cos d·⟪V,W⟫` one gets `0 ≤ E(u,u) ≤ ε₁‖u‖²` for all `u`, and
the quadratic expansion together with the symmetry of `rhess` (`Work.Diff.C.rhess_symm`) upgrades
this to `|E(V,W)| ≤ ε₁‖V‖‖W‖` via `abs_le_of_quad_expansion`. -/
theorem fcos_hess_pt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ℕ∞) : WithTop ℕ∞)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q x : M} {c ε₁ η : ℝ} (hη : -1 < η) (hc : 0 < c) (hε₁ : 0 ≤ ε₁)
    (hx0 : 0 < Work.Diff.C.rdist (I := I) (M := M) q x)
    (hxd : Work.Diff.C.rdist (I := I) (M := M) q x < Real.arccos (-1 + c))
    (hlt : Real.sqrt (1 + η) * Work.Diff.C.rdist (I := I) (M := M) q x < Real.pi)
    (hsm : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) x)
    (hunit : Inner.inner ℝ
      (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.rdist (I := I) (M := M) q) x)
      (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.rdist (I := I) (M := M) q) x) = 1)
    (hUpper : Work.Diff.C.HessUpperInput (I := I) (M := M) cov)
    (hLower : Work.Diff.C.HessLowerInput (I := I) (M := M) cov η)
    (hkey : max (Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
        - Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) * Real.sqrt (1 + η)
          * Real.cot (Real.sqrt (1 + η) * Work.Diff.C.rdist (I := I) (M := M) q x)) 0 ≤ ε₁) :
    ∀ V W : TangentSpace I x,
      |Work.Diff.C.rhess cov (Work.Diff.C.fcos (I := I) (M := M) q) x V W
          + Work.Diff.C.fcos (I := I) (M := M) q x * Inner.inner ℝ V W| ≤ ε₁ * ‖V‖ * ‖W‖ := by
  intro V W
  -- ## Preliminaries: `0 < d < π` and `sin d ≠ 0`
  have hpi : Work.Diff.C.rdist (I := I) (M := M) q x < Real.pi :=
    lt_of_lt_of_le hxd (Real.arccos_le_pi (-1 + c))
  have hsind : 0 < Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hpi
  have hcot : Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
        * Real.cot (Work.Diff.C.rdist (I := I) (M := M) q x)
      = Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x) := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  -- ## The gradient of the distance, named `G`
  generalize hg : Work.Diff.C.rgrad (I := I) (M := M)
      (Work.Diff.C.rdist (I := I) (M := M) q) x = G at *
  have hunitG : Inner.inner ℝ G G = 1 := hunit
  have hunit_e : Inner.inner ℝ
      (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.rdist (I := I) (M := M) q) x)
      (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.rdist (I := I) (M := M) q) x) = 1 := by
    rw [hg]; exact hunitG
  -- ## The two Hessian comparison inequalities, restricted to `G^⊥`
  have hU : ∀ u : TangentSpace I x,
      rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u u
        ≤ Real.cot (Work.Diff.C.rdist (I := I) (M := M) q x)
          * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u) := by
    intro u
    have h := hUpper q x hsm hunit_e u
    rw [hg] at h
    simpa [sq] using h
  have hL : ∀ u : TangentSpace I x,
      Real.sqrt (1 + η) * Real.cot (Real.sqrt (1 + η)
          * Work.Diff.C.rdist (I := I) (M := M) q x)
          * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u)
        ≤ rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u u := by
    intro u
    have h := hLower q x hsm hunit_e hlt u
    rw [hg] at h
    simpa [sq] using h
  have hcs : ∀ u : TangentSpace I x,
      Inner.inner ℝ G u * Inner.inner ℝ G u ≤ Inner.inner ℝ u u := by
    intro u
    have h := real_inner_mul_inner_self_le G u
    rw [hunitG, one_mul, real_inner_self_eq_norm_sq u] at h
    rwa [real_inner_self_eq_norm_sq]
  -- ## The quadratic form `E` is nonnegative ...
  have hQpos : ∀ u : TangentSpace I x,
      0 ≤ -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
            * rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u u
        + Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
          * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u) := by
    intro u
    have h1 := hU u
    have h3 := mul_le_mul_of_nonpos_left h1
      (show -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) ≤ 0 by linarith)
    rw [← mul_assoc] at h3
    have h4 : -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
          * Real.cot (Work.Diff.C.rdist (I := I) (M := M) q x)
        = -(Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)) := by
      have h5 : -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
            * Real.cot (Work.Diff.C.rdist (I := I) (M := M) q x)
          = -(Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
              * Real.cot (Work.Diff.C.rdist (I := I) (M := M) q x)) := by ring
      rw [h5, hcot]
    rw [h4, neg_mul] at h3
    linarith [h3]
  -- ... and bounded above by `ε₁‖u‖²`
  have hkey'' : Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
        - Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) * Real.sqrt (1 + η)
          * Real.cot (Real.sqrt (1 + η) * Work.Diff.C.rdist (I := I) (M := M) q x) ≤ ε₁ :=
    le_trans (le_max_left _ _) hkey
  have hQle : ∀ u : TangentSpace I x,
      -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
          * rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u u
        + Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
          * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u)
      ≤ ε₁ * Inner.inner ℝ u u := by
    intro u
    have h1 := hL u
    have hS : 0 ≤ Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u := by
      linarith [hcs u]
    have h3 : -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
          * rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u u
        ≤ -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) * (Real.sqrt (1 + η)
            * Real.cot (Real.sqrt (1 + η) * Work.Diff.C.rdist (I := I) (M := M) q x)
            * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u)) :=
      mul_le_mul_of_nonpos_left h1 (show -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) ≤ 0 by
        linarith)
    calc -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
            * rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u u
          + Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
            * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u)
        ≤ -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) * (Real.sqrt (1 + η)
            * Real.cot (Real.sqrt (1 + η) * Work.Diff.C.rdist (I := I) (M := M) q x)
            * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u))
          + Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
            * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u) :=
        add_le_add_left h3 _
      _ = (Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
            - Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x) * Real.sqrt (1 + η)
            * Real.cot (Real.sqrt (1 + η) * Work.Diff.C.rdist (I := I) (M := M) q x))
          * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u) := by ring
      _ ≤ ε₁ * (Inner.inner ℝ u u - Inner.inner ℝ G u * Inner.inner ℝ G u) :=
          mul_le_mul_of_nonneg_right hkey'' hS
      _ ≤ ε₁ * Inner.inner ℝ u u :=
          mul_le_mul_of_nonneg_left
            (sub_le_iff_le_add.mpr (le_add_of_nonneg_right (mul_self_nonneg _))) hε₁
  -- ## The chain rule, in the form of the bilinear form `E`
  have hchain := rhess_comp (cov := cov) (c := Real.cos)
    (F := fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x V W
    Real.contDiff_cos.contDiffAt hsm
  have hd2 : iteratedDeriv 2 Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
      = -Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x) := by
    have h1 : deriv Real.cos = fun y : ℝ => -Real.sin y := funext fun y => Real.deriv_cos
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
    exact ((Real.hasDerivAt_sin (Work.Diff.C.rdist (I := I) (M := M) q x)).neg).deriv
  have hmv : ∀ u : TangentSpace I x,
      mvfderiv I (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u
        = Inner.inner ℝ G u := by
    intro u
    rw [← hg]
    exact (inner_rgrad_mvfderiv (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x u).symm
  have hE : rhess cov (fcos (I := I) (M := M) q) x V W
        + fcos (I := I) (M := M) q x * Inner.inner ℝ V W
      = -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
          * rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x V W
        + Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
          * (Inner.inner ℝ V W - Inner.inner ℝ G V * Inner.inner ℝ G W) := by
    rw [show fcos (I := I) (M := M) q
        = fun y : M => Real.cos (Work.Diff.C.rdist (I := I) (M := M) q y) from rfl,
      hchain, hd2, Real.deriv_cos, hmv V, hmv W]
    ring
  rw [hE]
  -- ## Upgrade the quadratic bound to a bilinear bound
  refine abs_le_of_quad_expansion_pt (ε := ε₁)
    (E := fun A B => -Real.sin (Work.Diff.C.rdist (I := I) (M := M) q x)
          * rhess cov (fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y) x A B
        + Real.cos (Work.Diff.C.rdist (I := I) (M := M) q x)
          * (Inner.inner ℝ A B - Inner.inner ℝ G A * Inner.inner ℝ G B))
    hε₁ hQpos ?_ ?_
  · intro u
    simpa [real_inner_self_eq_norm_sq u] using hQle u
  · intro t
    rw [rhess_expansion_pt hmet htor hsm V W t]
    have hi : Inner.inner ℝ (V + t • W) (V + t • W)
        = Inner.inner ℝ V V + 2 * t * Inner.inner ℝ V W + t ^ 2 * Inner.inner ℝ W W := by
      rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm (x := W) (y := V)]
      ring
    have hi2 : Inner.inner ℝ G (V + t • W)
        = Inner.inner ℝ G V + t * Inner.inner ℝ G W := by
      rw [inner_add_right, real_inner_smul_right]
    rw [hi, hi2]
    ring_nf

end Work.Diff.C
