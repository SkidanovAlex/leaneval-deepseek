import Mathlib
import Submission.Work.Drive.encodedShear

/-!
# The differential of the clamped cross-shear of the parameter square

`Work.Drive.shear q` (`Submission/Work/Drive/encodedShear.lean`) is the cross-shear of the parameter
square `[0,1]²` with clamped parameter `q ∈ 𝔼⁴`,

`shear₁ q y = (y₀ + C(y₁) hb y₀, y₁)`, `shear₂ q u = (u₀, u₁ + D(u₀) hb u₁)`,
`shear q = shear₂ q ∘ shear₁ q`, with `C (y₁) = a₀ (1 - 2 y₁) + a₂ hb y₁`,
`D (u₀) = a₁ (1 - 2 u₀) + a₃ hb u₀`, `a = ballClamp q`, `‖a‖ < 1/2` and `hb x = x (1 - x)`.

This file computes `fderiv ℝ (shear q) y` at every point `y` of the unit box `[0,1]²`:

* it is a linear isomorphism (so the shear is a local diffeomorphism everywhere on the box, the
  property the parametric Sard lemma `Work.Drive.localSard_family_in_open` needs), and
* on the four faces `y₀ ∈ {0,1}`, `y₁ ∈ {0,1}` it is *coordinatewise* triangular: the `i`-th
  component of the differential vanishes exactly on the hyperplane `vᵢ = 0`.  In particular the
  differential of the shear preserves the corner structure of the box, which is what makes the
  shear commute with the seam involution.

The Jacobian of the composite is the product of the two triangular Jacobians
`[[1 + C(y₁)(1-2y₀), C'(y₁) hb y₀], [0, 1]]` and `[[1, 0], [D'(u₀) hb u₁, 1 + D(u₀)(1-2y₁)]]`
with `u = shear₁ q y`, so the two claims reduce to the two scalar bounds
`|C(t)| ≤ 5/8` (giving the first diagonal entry `≥ 3/8`) and `|D(u₀)| < 1` (giving the second
diagonal entry `> 0`), the latter via the range bound `u₀ ∈ [-5/32, 37/32]` — the only place where
the clamping `‖ballClamp q‖ < 1/2` is used.
-/

namespace Work.Drive

noncomputable section

open scoped Manifold Topology

/-! ## 1. Coordinates and the linear maps `mat2` -/

/-- The `i`-th coordinate functional of `EuclideanSpace ℝ (Fin 2)`. -/
def coordCLM (i : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ) i

lemma coordCLM_apply (i : Fin 2) (v : EuclideanSpace ℝ (Fin 2)) : coordCLM i v = v i := by
  simp [coordCLM]

lemma pt2_smul_basis (a b : ℝ) : pt2 a b = a • pt2 1 0 + b • pt2 0 1 := by
  ext i
  fin_cases i <;> simp

/-- The canonical continuous linear map `ℝ × ℝ → 𝔼²`, `(a,b) ↦ pt2 a b`. -/
def pt2CLM : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (pt2 1 0) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (pt2 0 1)

lemma pt2CLM_apply (p : ℝ × ℝ) : pt2CLM p = pt2 p.1 p.2 := by
  rw [pt2_smul_basis]
  simp [pt2CLM]

/-- The linear map with matrix `[[α, β], [γ, δ]]`. -/
def mat2 (α β γ δ : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  pt2CLM.comp ((α • coordCLM 0 + β • coordCLM 1).prod (γ • coordCLM 0 + δ • coordCLM 1))

lemma mat2_apply_pt2 (α β γ δ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    mat2 α β γ δ v = pt2 (α * v 0 + β * v 1) (γ * v 0 + δ * v 1) := by
  simp [mat2, pt2CLM_apply, coordCLM_apply]

lemma mat2_apply_zero (α β γ δ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (mat2 α β γ δ v) 0 = α * v 0 + β * v 1 := by
  rw [mat2_apply_pt2]; simp

lemma mat2_apply_one (α β γ δ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (mat2 α β γ δ v) 1 = γ * v 0 + δ * v 1 := by
  rw [mat2_apply_pt2]; simp

/-- The first coordinate of the composite `mat2 1 0 γ δ ∘ mat2 α β 0 1`: the second factor is
upper triangular with diagonal `1`, so only `α, β` survive. -/
lemma mat2_comp_apply_zero (α β γ δ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ((mat2 1 0 γ δ).comp (mat2 α β 0 1)) v 0 = α * v 0 + β * v 1 := by
  simp only [ContinuousLinearMap.comp_apply, mat2_apply_zero, mat2_apply_one]
  ring

/-- The second coordinate of the composite `mat2 1 0 γ δ ∘ mat2 α β 0 1`. -/
lemma mat2_comp_apply_one (α β γ δ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ((mat2 1 0 γ δ).comp (mat2 α β 0 1)) v 1 = γ * (α * v 0 + β * v 1) + δ * v 1 := by
  simp only [ContinuousLinearMap.comp_apply, mat2_apply_zero, mat2_apply_one]
  ring

/-- `mat2 α β 0 1` is a bijection when `α ≠ 0` (explicit lower triangular inverse). -/
lemma mat2_bijective_of_ne_zero_left {α β : ℝ} (hα : α ≠ 0) :
    Function.Bijective (⇑(mat2 α β 0 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2))) := by
  set g : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mat2 α⁻¹ (-(β * α⁻¹)) 0 1 with hg
  have h0 : ∀ v : EuclideanSpace ℝ (Fin 2), (g (mat2 α β 0 1 v)) 0 = v 0 := by
    intro v
    rw [hg]
    rw [mat2_apply_zero, mat2_apply_zero, mat2_apply_one]
    field_simp
    ring
  have h1 : ∀ v : EuclideanSpace ℝ (Fin 2), (g (mat2 α β 0 1 v)) 1 = v 1 := by
    intro v
    rw [hg]
    rw [mat2_apply_one, mat2_apply_one]
    ring
  have h0' : ∀ v : EuclideanSpace ℝ (Fin 2), ((mat2 α β 0 1) (g v)) 0 = v 0 := by
    intro v
    rw [hg]
    rw [mat2_apply_zero, mat2_apply_zero, mat2_apply_one]
    field_simp
    ring
  have h1' : ∀ v : EuclideanSpace ℝ (Fin 2), ((mat2 α β 0 1) (g v)) 1 = v 1 := by
    intro v
    rw [hg]
    rw [mat2_apply_one, mat2_apply_one]
    ring
  have hleft : Function.LeftInverse (⇑g) (⇑(mat2 α β 0 1)) := by
    intro v
    ext i
    fin_cases i
    · exact h0 v
    · exact h1 v
  have hright : Function.RightInverse (⇑g) (⇑(mat2 α β 0 1)) := by
    intro v
    ext i
    fin_cases i
    · exact h0' v
    · exact h1' v
  exact ⟨hleft.injective, hright.surjective⟩

/-- `mat2 1 0 γ δ` is a bijection when `δ ≠ 0` (explicit upper triangular inverse). -/
lemma mat2_bijective_of_ne_zero_right {γ δ : ℝ} (hδ : δ ≠ 0) :
    Function.Bijective (⇑(mat2 1 0 γ δ : EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2))) := by
  set g : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mat2 1 0 (-(γ * δ⁻¹)) δ⁻¹ with hg
  have h0 : ∀ v : EuclideanSpace ℝ (Fin 2), (g (mat2 1 0 γ δ v)) 0 = v 0 := by
    intro v
    rw [hg]
    rw [mat2_apply_zero, mat2_apply_zero, mat2_apply_one]
    ring
  have h1 : ∀ v : EuclideanSpace ℝ (Fin 2), (g (mat2 1 0 γ δ v)) 1 = v 1 := by
    intro v
    rw [hg]
    rw [mat2_apply_one, mat2_apply_zero, mat2_apply_one]
    field_simp
    ring
  have h0' : ∀ v : EuclideanSpace ℝ (Fin 2), ((mat2 1 0 γ δ) (g v)) 0 = v 0 := by
    intro v
    rw [hg]
    rw [mat2_apply_zero, mat2_apply_zero]
    ring
  have h1' : ∀ v : EuclideanSpace ℝ (Fin 2), ((mat2 1 0 γ δ) (g v)) 1 = v 1 := by
    intro v
    rw [hg]
    rw [mat2_apply_one, mat2_apply_zero, mat2_apply_one]
    field_simp
    ring
  have hleft : Function.LeftInverse (⇑g) (⇑(mat2 1 0 γ δ)) := by
    intro v
    ext i
    fin_cases i
    · exact h0 v
    · exact h1 v
  have hright : Function.RightInverse (⇑g) (⇑(mat2 1 0 γ δ)) := by
    intro v
    ext i
    fin_cases i
    · exact h0' v
    · exact h1' v
  exact ⟨hleft.injective, hright.surjective⟩

/-! ## 2. The scalar coefficient functions `Ccoef`, `Dcoef` and their derivatives -/

lemma hasDerivAt_hb (x : ℝ) : HasDerivAt hb (1 - 2 * x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t * (1 - t)) ((1 : ℝ) * (1 - x) + x * (0 - 1)) x :=
    (hasDerivAt_id x).mul ((hasDerivAt_const (x := x) (1 : ℝ)).sub (hasDerivAt_id x))
  exact h1.congr_deriv (by ring)

/-- `C (y₁) = a₀ (1 - 2 y₁) + a₂ hb y₁`, the coefficient of the first shear factor. -/
def Ccoef (q : EuclideanSpace ℝ (Fin 4)) (t : ℝ) : ℝ :=
  ballClamp q 0 * (1 - 2 * t) + ballClamp q 2 * hb t

/-- The derivative of `Ccoef q`. -/
def CcoefDeriv (q : EuclideanSpace ℝ (Fin 4)) (t : ℝ) : ℝ :=
  -2 * ballClamp q 0 + ballClamp q 2 * (1 - 2 * t)

/-- `D (y₀) = a₁ (1 - 2 y₀) + a₃ hb y₀`, the coefficient of the second shear factor. -/
def Dcoef (q : EuclideanSpace ℝ (Fin 4)) (t : ℝ) : ℝ :=
  ballClamp q 1 * (1 - 2 * t) + ballClamp q 3 * hb t

/-- The derivative of `Dcoef q`. -/
def DcoefDeriv (q : EuclideanSpace ℝ (Fin 4)) (t : ℝ) : ℝ :=
  -2 * ballClamp q 1 + ballClamp q 3 * (1 - 2 * t)

lemma hasDerivAt_cc (q : EuclideanSpace ℝ (Fin 4)) (x : ℝ) :
    HasDerivAt (Ccoef q) (CcoefDeriv q x) x := by
  have hbase : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) x := by
    have h := (hasDerivAt_const (x := x) (1 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)
    exact h.congr_deriv (by ring)
  have h1 : HasDerivAt (fun t : ℝ => ballClamp q 0 * (1 - 2 * t)) (ballClamp q 0 * (-2)) x :=
    hbase.const_mul (ballClamp q 0)
  have h2 : HasDerivAt (fun t : ℝ => ballClamp q 2 * hb t) (ballClamp q 2 * (1 - 2 * x)) x :=
    (hasDerivAt_hb x).const_mul (ballClamp q 2)
  have h3 : HasDerivAt (fun t : ℝ => ballClamp q 0 * (1 - 2 * t) + ballClamp q 2 * hb t)
      (ballClamp q 0 * (-2) + ballClamp q 2 * (1 - 2 * x)) x := h1.add h2
  refine h3.congr_deriv ?_
  simp only [CcoefDeriv]
  ring

lemma hasDerivAt_dd (q : EuclideanSpace ℝ (Fin 4)) (x : ℝ) :
    HasDerivAt (Dcoef q) (DcoefDeriv q x) x := by
  have hbase : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) x := by
    have h := (hasDerivAt_const (x := x) (1 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)
    exact h.congr_deriv (by ring)
  have h1 : HasDerivAt (fun t : ℝ => ballClamp q 1 * (1 - 2 * t)) (ballClamp q 1 * (-2)) x :=
    hbase.const_mul (ballClamp q 1)
  have h2 : HasDerivAt (fun t : ℝ => ballClamp q 3 * hb t) (ballClamp q 3 * (1 - 2 * x)) x :=
    (hasDerivAt_hb x).const_mul (ballClamp q 3)
  have h3 : HasDerivAt (fun t : ℝ => ballClamp q 1 * (1 - 2 * t) + ballClamp q 3 * hb t)
      (ballClamp q 1 * (-2) + ballClamp q 3 * (1 - 2 * x)) x := h1.add h2
  refine h3.congr_deriv ?_
  simp only [DcoefDeriv]
  ring

/-! ## 3. `HasFDerivAt` of the two shear factors -/

/-- Composition lemma: the map `y ↦ pt2 (φ y) (ψ y)` has differential `pt2CLM ∘ (φ', ψ')`. -/
lemma hasFDerivAt_pt2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ ψ : E → ℝ} {φ' ψ' : E →L[ℝ] ℝ} {y : E}
    (hφ : HasFDerivAt φ φ' y) (hψ : HasFDerivAt ψ ψ' y) :
    HasFDerivAt (fun z => pt2 (φ z) (ψ z)) (pt2CLM.comp (φ'.prod ψ')) y := by
  have hlin : ∀ p : ℝ × ℝ, HasFDerivAt (fun p : ℝ × ℝ => pt2 p.1 p.2) pt2CLM p := by
    intro p
    rw [show (fun p : ℝ × ℝ => pt2 p.1 p.2) = ⇑pt2CLM from funext fun q => (pt2CLM_apply q).symm]
    exact pt2CLM.hasFDerivAt
  exact (hlin (φ y, ψ y)).comp y (hφ.prodMk hψ)

lemma hasFDerivAt_hb_coord (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => hb (z 0)) ((1 - 2 * y 0) • coordCLM 0) y := by
  have hy0 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0) (coordCLM 0) y :=
    (coordCLM 0).hasFDerivAt
  refine ((hasDerivAt_hb (y 0)).hasFDerivAt.comp y hy0).congr_fderiv ?_
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, coordCLM_apply, smul_eq_mul, mul_comm]

lemma hasFDerivAt_cc_coord (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => Ccoef q (z 1)) (CcoefDeriv q (y 1) • coordCLM 1) y := by
  have hy1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1) (coordCLM 1) y :=
    (coordCLM 1).hasFDerivAt
  refine ((hasDerivAt_cc q (y 1)).hasFDerivAt.comp y hy1).congr_fderiv ?_
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, coordCLM_apply, smul_eq_mul, mul_comm]

lemma hasFDerivAt_dd_coord (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => Dcoef q (z 0)) (DcoefDeriv q (y 0) • coordCLM 0) y := by
  have hy0 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0) (coordCLM 0) y :=
    (coordCLM 0).hasFDerivAt
  refine ((hasDerivAt_dd q (y 0)).hasFDerivAt.comp y hy0).congr_fderiv ?_
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, coordCLM_apply, smul_eq_mul, mul_comm]

lemma hasFDerivAt_hb_coord_one (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => hb (z 1)) ((1 - 2 * y 1) • coordCLM 1) y := by
  have hy1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1) (coordCLM 1) y :=
    (coordCLM 1).hasFDerivAt
  refine ((hasDerivAt_hb (y 1)).hasFDerivAt.comp y hy1).congr_fderiv ?_
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, coordCLM_apply, smul_eq_mul, mul_comm]

/-- The differential of the first shear factor at every point: the matrix
`[[1 + C(y₁)(1-2y₀), C'(y₁) hb y₀], [0, 1]]`. -/
lemma hasFDerivAt_shear₁ (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (shear₁ q)
      (mat2 (1 + Ccoef q (y 1) * (1 - 2 * y 0)) (CcoefDeriv q (y 1) * hb (y 0)) 0 1) y := by
  have hy0 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0) (coordCLM 0) y :=
    (coordCLM 0).hasFDerivAt
  have hy1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1) (coordCLM 1) y :=
    (coordCLM 1).hasFDerivAt
  have hC := hasFDerivAt_cc_coord q y
  have hhb := hasFDerivAt_hb_coord y
  have hprod : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => Ccoef q (z 1) * hb (z 0))
      (Ccoef q (y 1) • ((1 - 2 * y 0) • coordCLM 0) + hb (y 0) • (CcoefDeriv q (y 1) • coordCLM 1)) y :=
    hC.mul hhb
  have hsum : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0 + Ccoef q (z 1) * hb (z 0))
      (coordCLM 0 + (Ccoef q (y 1) • ((1 - 2 * y 0) • coordCLM 0) +
        hb (y 0) • (CcoefDeriv q (y 1) • coordCLM 1))) y :=
    hy0.add hprod
  refine (hasFDerivAt_pt2 hsum hy1).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, pt2CLM_apply, coordCLM_apply,
      mat2_apply_pt2]
  ext i
  fin_cases i <;> simp only [pt2_zero, pt2_one] <;>
    simp only [add_apply, smul_apply, coordCLM_apply, smul_eq_mul] <;> ring

/-- The differential of the second shear factor at every point: the matrix
`[[1, 0], [D'(u₀) hb u₁, 1 + D(u₀)(1-2u₁)]]`. -/
lemma hasFDerivAt_shear₂ (q : EuclideanSpace ℝ (Fin 4)) (u : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (shear₂ q)
      (mat2 1 0 (DcoefDeriv q (u 0) * hb (u 1)) (1 + Dcoef q (u 0) * (1 - 2 * u 1))) u := by
  have hy0 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0) (coordCLM 0) u :=
    (coordCLM 0).hasFDerivAt
  have hy1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1) (coordCLM 1) u :=
    (coordCLM 1).hasFDerivAt
  have hD := hasFDerivAt_dd_coord q u
  have hhb := hasFDerivAt_hb_coord_one u
  have hprod : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => Dcoef q (z 0) * hb (z 1))
      (Dcoef q (u 0) • ((1 - 2 * u 1) • coordCLM 1) + hb (u 1) • (DcoefDeriv q (u 0) • coordCLM 0)) u :=
    hD.mul hhb
  have hsum : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1 + Dcoef q (z 0) * hb (z 1))
      (coordCLM 1 + (Dcoef q (u 0) • ((1 - 2 * u 1) • coordCLM 1) +
        hb (u 1) • (DcoefDeriv q (u 0) • coordCLM 0))) u :=
    hy1.add hprod
  refine (hasFDerivAt_pt2 hy0 hsum).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, pt2CLM_apply, coordCLM_apply,
      mat2_apply_pt2]
  ext i
  fin_cases i <;> simp only [pt2_zero, pt2_one] <;>
    simp only [add_apply, smul_apply, coordCLM_apply, smul_eq_mul] <;> ring

/-! ## 4. The scalar bounds -/

lemma abs_coord_ballClamp_lt {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |(ballClamp q) i| < 1 / 2 := by
  have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin n => ℝ) (ballClamp q) i
  rw [Real.norm_eq_abs] at h
  exact lt_of_le_of_lt h (norm_ballClamp_lt q)

lemma abs_hb_le_quarter_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-5 / 32) (37 / 32)) : |hb t| ≤ 1 / 4 := by
  rw [abs_le]
  refine ⟨?_, hb_le t⟩
  have hprod : (t + 5 / 32) * (t - 37 / 32) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1]) (by linarith [ht.2])
  unfold hb
  nlinarith [hprod]

/-- `|C(t)| ≤ 5/8` for `t ∈ [0,1]`. -/
lemma abs_cc_le (q : EuclideanSpace ℝ (Fin 4)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |Ccoef q t| ≤ 5 / 8 := by
  have h1 : |1 - 2 * t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h2 : |hb t| ≤ 1 / 4 := by
    rw [abs_le]
    exact ⟨by unfold hb; nlinarith [ht.1, ht.2], hb_le t⟩
  have h3 : |ballClamp q 0| < 1 / 2 := abs_coord_ballClamp_lt q 0
  have h4 : |ballClamp q 2| < 1 / 2 := abs_coord_ballClamp_lt q 2
  have h5 : |ballClamp q 0| * |1 - 2 * t| ≤ (1 / 2) * 1 :=
    mul_le_mul (le_of_lt h3) h1 (abs_nonneg _) (by norm_num)
  have h6 : |ballClamp q 2| * |hb t| ≤ (1 / 2) * (1 / 4) :=
    mul_le_mul (le_of_lt h4) h2 (abs_nonneg _) (by norm_num)
  rw [Ccoef]
  calc |ballClamp q 0 * (1 - 2 * t) + ballClamp q 2 * hb t|
      ≤ |ballClamp q 0 * (1 - 2 * t)| + |ballClamp q 2 * hb t| := abs_add_le _ _
    _ = |ballClamp q 0| * |1 - 2 * t| + |ballClamp q 2| * |hb t| := by rw [abs_mul, abs_mul]
    _ ≤ 5 / 8 := by linarith

/-- `|D(t)| < 1` for `t ∈ [-5/32, 37/32]`. -/
lemma abs_dd_lt_one (q : EuclideanSpace ℝ (Fin 4)) {t : ℝ}
    (ht : t ∈ Set.Icc (-5 / 32) (37 / 32)) : |Dcoef q t| < 1 := by
  have h1 : |1 - 2 * t| ≤ 21 / 16 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h2 : |hb t| ≤ 1 / 4 := abs_hb_le_quarter_of_mem ht
  have h3 : |ballClamp q 1| < 1 / 2 := abs_coord_ballClamp_lt q 1
  have h4 : |ballClamp q 3| < 1 / 2 := abs_coord_ballClamp_lt q 3
  have h5 : |ballClamp q 1| * |1 - 2 * t| ≤ (1 / 2) * (21 / 16) :=
    mul_le_mul (le_of_lt h3) h1 (abs_nonneg _) (by norm_num)
  have h6 : |ballClamp q 3| * |hb t| ≤ (1 / 2) * (1 / 4) :=
    mul_le_mul (le_of_lt h4) h2 (abs_nonneg _) (by norm_num)
  rw [Dcoef]
  calc |ballClamp q 1 * (1 - 2 * t) + ballClamp q 3 * hb t|
      ≤ |ballClamp q 1 * (1 - 2 * t)| + |ballClamp q 3 * hb t| := abs_add_le _ _
    _ = |ballClamp q 1| * |1 - 2 * t| + |ballClamp q 3| * |hb t| := by rw [abs_mul, abs_mul]
    _ ≤ 25 / 32 := by linarith
    _ < 1 := by norm_num

/-- The first coordinate of `shear₁ q y` stays in `[-5/32, 37/32]` for `y` in the box: the shear
moves the first coordinate by at most `(5/8) · (1/4)`. -/
lemma shear₁_zero_mem (q : EuclideanSpace ℝ (Fin 4)) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) :
    (shear₁ q y) 0 ∈ Set.Icc (-5 / 32) (37 / 32) := by
  have hy0 : y 0 ∈ Set.Icc (0 : ℝ) 1 := hy 0
  have hy1 : y 1 ∈ Set.Icc (0 : ℝ) 1 := hy 1
  have hcc : |Ccoef q (y 1)| ≤ 5 / 8 := abs_cc_le q hy1
  have hhb : |hb (y 0)| ≤ 1 / 4 := by
    rw [abs_le]
    exact ⟨by unfold hb; nlinarith [hy0.1, hy0.2], hb_le _⟩
  have hsh : (shear₁ q y) 0 = y 0 + Ccoef q (y 1) * hb (y 0) := shear₁_apply_zero q y
  have hdiff : |(shear₁ q y) 0 - y 0| ≤ 5 / 32 := by
    rw [hsh]
    rw [show y 0 + Ccoef q (y 1) * hb (y 0) - y 0 = Ccoef q (y 1) * hb (y 0) by ring, abs_mul]
    calc |Ccoef q (y 1)| * |hb (y 0)| ≤ (5 / 8) * (1 / 4) :=
          mul_le_mul hcc hhb (abs_nonneg _) (by norm_num)
      _ = 5 / 32 := by norm_num
  constructor
  · linarith [(abs_le.mp hdiff).1, hy0.1]
  · linarith [(abs_le.mp hdiff).2, hy0.2]

/-! ## 5. The main theorem -/

theorem shear_fderiv (q : EuclideanSpace ℝ (Fin 4)) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) :
    Function.Bijective (fderiv ℝ (Work.Drive.shear q) y) ∧
    (∀ i : Fin 2, (y i = 0 ∨ y i = 1) → ∀ v : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (Work.Drive.shear q) y v) i = 0 ↔ v i = 0) := by
  have hy0 : y 0 ∈ Set.Icc (0 : ℝ) 1 := hy 0
  have hy1 : y 1 ∈ Set.Icc (0 : ℝ) 1 := hy 1
  set α : ℝ := 1 + Ccoef q (y 1) * (1 - 2 * y 0) with hαdef
  set β : ℝ := CcoefDeriv q (y 1) * hb (y 0) with hβdef
  set γ : ℝ := DcoefDeriv q ((shear₁ q y) 0) * hb ((shear₁ q y) 1) with hγdef
  set δ : ℝ := 1 + Dcoef q ((shear₁ q y) 0) * (1 - 2 * (shear₁ q y) 1) with hδdef
  have hs1 := hasFDerivAt_shear₁ q y
  have hs2 := hasFDerivAt_shear₂ q (shear₁ q y)
  have hf' : fderiv ℝ (shear q) y = (mat2 1 0 γ δ).comp (mat2 α β 0 1) := by
    have hcomp := fderiv_comp (𝕜 := ℝ) y hs2.differentiableAt hs1.differentiableAt
    rw [hs2.fderiv, hs1.fderiv] at hcomp
    exact hcomp
  -- the two diagonal entries of the Jacobian are non-zero
  have hα : α ≠ 0 := by
    have hcc : |Ccoef q (y 1)| ≤ 5 / 8 := abs_cc_le q hy1
    have h1 : |1 - 2 * y 0| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hy0.1, hy0.2]
    have h2 : |α - 1| ≤ 5 / 8 := by
      rw [hαdef]
      rw [show 1 + Ccoef q (y 1) * (1 - 2 * y 0) - 1 = Ccoef q (y 1) * (1 - 2 * y 0) by ring, abs_mul]
      calc |Ccoef q (y 1)| * |1 - 2 * y 0| ≤ (5 / 8) * 1 :=
            mul_le_mul hcc h1 (abs_nonneg _) (by norm_num)
        _ = 5 / 8 := by norm_num
    intro h
    rw [h] at h2
    norm_num at h2
  have hδ : δ ≠ 0 := by
    have hu : (shear₁ q y) 0 ∈ Set.Icc (-5 / 32) (37 / 32) := shear₁_zero_mem q hy
    have hdd : |Dcoef q ((shear₁ q y) 0)| < 1 := abs_dd_lt_one q hu
    have hu1 : (shear₁ q y) 1 = y 1 := shear₁_apply_one q y
    have h1 : |1 - 2 * (shear₁ q y) 1| ≤ 1 := by
      rw [hu1]
      rw [abs_le]
      constructor <;> linarith [hy1.1, hy1.2]
    have h2 : |δ - 1| < 1 := by
      rw [hδdef]
      rw [show 1 + Dcoef q ((shear₁ q y) 0) * (1 - 2 * (shear₁ q y) 1) - 1
          = Dcoef q ((shear₁ q y) 0) * (1 - 2 * (shear₁ q y) 1) by ring, abs_mul]
      calc |Dcoef q ((shear₁ q y) 0)| * |1 - 2 * (shear₁ q y) 1|
          ≤ |Dcoef q ((shear₁ q y) 0)| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ < 1 * 1 := mul_lt_mul_of_pos_right hdd one_pos
        _ = 1 := by norm_num
    intro h
    rw [h] at h2
    norm_num at h2
  refine ⟨?_, ?_⟩
  · rw [hf']
    have hbij : Function.Bijective (⇑(mat2 1 0 γ δ) ∘ ⇑(mat2 α β 0 1)) :=
      (mat2_bijective_of_ne_zero_right hδ).comp (mat2_bijective_of_ne_zero_left hα)
    rw [show ⇑((mat2 1 0 γ δ).comp (mat2 α β 0 1))
        = ⇑(mat2 1 0 γ δ) ∘ ⇑(mat2 α β 0 1) from
      funext fun v => ContinuousLinearMap.comp_apply _ _ v]
    exact hbij
  · rw [Fin.forall_fin_two]
    constructor
    · intro hi v
      have hb0 : hb (y 0) = 0 := by
        rcases hi with h | h
        · rw [h]; simp [hb]
        · rw [h]; simp [hb]
      have hβ0 : β = 0 := by rw [hβdef, hb0, mul_zero]
      rw [hf', mat2_comp_apply_zero, hβ0, zero_mul, add_zero]
      constructor
      · intro h
        exact (mul_eq_zero.mp h).resolve_left hα
      · intro h
        rw [h, mul_zero]
    · intro hi v
      have hu1 : (shear₁ q y) 1 = y 1 := shear₁_apply_one q y
      have hb1 : hb (y 1) = 0 := by
        rcases hi with h | h
        · rw [h]; simp [hb]
        · rw [h]; simp [hb]
      have hγ0 : γ = 0 := by rw [hγdef, hu1, hb1, mul_zero]
      rw [hf', mat2_comp_apply_one, hγ0, zero_mul, zero_add]
      constructor
      · intro h
        exact (mul_eq_zero.mp h).resolve_left hδ
      · intro h
        rw [h, mul_zero]

end

end Work.Drive
