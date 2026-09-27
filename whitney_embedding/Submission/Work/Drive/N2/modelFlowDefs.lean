import Mathlib
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.FieldData
import Submission.Work.Drive.N2.exists_flow_jointSmooth_levelField
import Submission.Work.Projection.compact_embedding
import Submission.Work.Drive.N2.exists_smooth_retraction_manifold
import Submission.Work.Drive.N2.exists_contDiff_bump_isCompact
import Submission.Work.Drive.N2.isIntegralCurve_mem_tsupport_or_eq
import Submission.Work.Drive.N2.retraction_fixed_of_isIntegralCurve
import Submission.Work.Drive.N2.auxField_retraction_ne_zero

/-!
# Ambient data and the raw model-adapted field: definitions

The target `Work.Drive.N2.exists_modelAdapted_levelFlow` produces a smooth flow on a compact
surface which (a) raises `f` at unit speed off the model balls of the Morse charts and (b) makes
the chart-radius a strictly increasing function of `|chartQ|` on the regions `C i`.  The flow is
built in this development as the flow of a smooth compactly supported vector field on `ℝ^5`,
transported back to the surface by a nearest-point retraction `π` of a tubular neighbourhood of a
Whitney embedding `e : M → ℝ^5`.

This file contains the *definitions* of that ambient field:

* `AmbSetup` bundles the embedding `e`, the open set `U`, the retraction `π` and the properties we
  use (`π (e x) = x`, the orthogonality of `z - e (π z)` to the tangent space);
* `chartVel` is the chart-coordinate velocity of the *model* field: with a multiplier `b`, the
  chart image of the orbit satisfies `u' = b (‖u‖ ^ 2) • (s₁ u 0, s₂ u 1)`, i.e.
  `u' = b (‖u‖ ^ 2) • (1/2) ∇Q`, which is a positive multiple of the model field `∇Q`;
* `uCoord`, `uGrad`, `gramDet` are the ambient scalar functions `z ↦ φ (π z) j`, their Euclidean
  gradients, and the Gram determinant of the two gradients;
* `modelRaw` is the least-squares solution of `⟨∇u_j, Y⟩ = w_j` (`j = 0, 1`), where `w` is
  `chartVel`; `modelField` is its projection by `dE`, hence lands in the range of `dE z`, i.e. it is
  tangent to the image of `e`.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

/-- Embedding and nearest-point retraction data for the surface `M`: a smooth embedding into `ℝ^5`,
a neighbourhood `U` of its image, and a smooth retraction `π` of `U` onto `M` whose fibres are
orthogonal to the image. -/
structure AmbSetup (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] where
  /-- the Whitney embedding of the surface -/
  e : M → EuclideanSpace ℝ (Fin 5)
  he : ContMDiff (𝓡 2) (𝓡 5) ((⊤ : ℕ∞) : WithTop ℕ∞) e
  hinj : Function.Injective e
  himm : ∀ x, Function.Injective (mfderiv (𝓡 2) (𝓡 5) e x)
  /-- the neighbourhood of the image which the retraction is defined on -/
  U : Set (EuclideanSpace ℝ (Fin 5))
  π : EuclideanSpace ℝ (Fin 5) → M
  hU : IsOpen U
  hUe : Set.range e ⊆ U
  hπ : ContMDiffOn (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) π U
  hπe : ∀ x, π (e x) = x
  hπorth : ∀ z ∈ U, z - e (π z) ∈ (fderiv ℝ (fun z => e (π z)) z).rangeᗮ

namespace AmbSetup

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- The ambient retraction map `E = e ∘ π`. -/
noncomputable def E (A : AmbSetup M) :
    EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5) := fun z => A.e (A.π z)

end AmbSetup

/-- The vector `(a, b)` of the chart model space `ℝ²`. -/
noncomputable def vec2 (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun j : Fin 2 => if j = 0 then a else b)

lemma vec2_apply (a b : ℝ) (j : Fin 2) : vec2 a b j = if j = 0 then a else b := by
  simp [vec2]

@[simp] lemma vec2_apply_zero (a b : ℝ) : vec2 a b 0 = a := by simp [vec2]

@[simp] lemma vec2_apply_one (a b : ℝ) : vec2 a b 1 = b := by simp [vec2]

/-- The `j`-th coordinate functional on the chart model space, as a continuous linear map. -/
noncomputable def coordProj (j : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap

@[simp] lemma coordProj_apply (j : Fin 2) (v : EuclideanSpace ℝ (Fin 2)) :
    coordProj j v = v j := by
  simp [coordProj, EuclideanSpace.equiv]


variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- The chart-coordinate velocity of the model field at the chart point `u`: it is
`β (‖u‖ ^ 2) • (s₁ u 0, s₂ u 1)`, so that the pairing with `∇Q = (2 s₁ u 0, 2 s₂ u 1)` is
`2 * ‖u‖ ^ 2 * β (‖u‖ ^ 2)`. -/
noncomputable def chartVel (β : ℝ → ℝ) (s₁ s₂ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (β (‖u‖ ^ 2)) • WithLp.toLp 2 (fun j : Fin 2 => if j = 0 then s₁ * u 0 else s₂ * u 1)

lemma contDiff_chartVel {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (s₁ s₂ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartVel β s₁ s₂) := by
  have hβ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => β (‖u‖ ^ 2)) :=
    hβ.comp (contDiff_norm_sq ℝ)
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin 2) =>
      WithLp.toLp 2 (fun j : Fin 2 => if j = 0 then s₁ * u 0 else s₂ * u 1)) := by
    rw [contDiff_piLp]
    intro j
    have h : (fun u : EuclideanSpace ℝ (Fin 2) =>
        (WithLp.toLp 2 (fun j : Fin 2 => if j = 0 then s₁ * u 0 else s₂ * u 1)).ofLp j)
        = fun u : EuclideanSpace ℝ (Fin 2) => if j = 0 then s₁ * u 0 else s₂ * u 1 := by
      funext u
      rw [PiLp.toLp_apply]
    rw [h]
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte]
      have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : EuclideanSpace ℝ (Fin 2) => s₁ * coordProj (0 : Fin 2) u) :=
        contDiff_const.mul (coordProj (0 : Fin 2)).contDiff
      simpa [coordProj_apply] using h0
    · simp only [if_neg hj]
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : EuclideanSpace ℝ (Fin 2) => s₂ * coordProj (1 : Fin 2) u) :=
        contDiff_const.mul (coordProj (1 : Fin 2)).contDiff
      simpa [coordProj_apply] using h1
  exact hβ'.smul hlin

/-- The `j`-th chart coordinate of a point, as a scalar function on the ambient space. -/
noncomputable def uCoord (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (j : Fin 2) :
    EuclideanSpace ℝ (Fin 5) → ℝ := fun z => φ (A.π z) j

/-- The Euclidean gradient of the `j`-th chart coordinate. -/
noncomputable def uGrad (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (j : Fin 2) :
    EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5) :=
  fun z => grad (uCoord A φ j) z

/-- The Gram determinant of the two gradients `∇ (φ ∘ π) 0`, `∇ (φ ∘ π) 1`. -/
noncomputable def gramDet (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 5) → ℝ := fun z =>
  ‖uGrad A φ 0 z‖ ^ 2 * ‖uGrad A φ 1 z‖ ^ 2 - (inner ℝ (uGrad A φ 0 z) (uGrad A φ 1 z)) ^ 2

/-- The least-squares solution of `⟨∇ (φ ∘ π) j, Y⟩ = chartVel b s₁ s₂ (φ (π z)) j` (`j = 0, 1`),
written out with the adjugate matrix. -/
noncomputable def modelRaw (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (b : ℝ → ℝ) (s₁ s₂ : ℝ)
    (z : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 5) :=
  (gramDet A φ z)⁻¹ •
    (((‖uGrad A φ 1 z‖ ^ 2 * chartVel b s₁ s₂ (φ (A.π z)) 0
        - inner ℝ (uGrad A φ 0 z) (uGrad A φ 1 z) * chartVel b s₁ s₂ (φ (A.π z)) 1) • uGrad A φ 0 z)
      + ((‖uGrad A φ 0 z‖ ^ 2 * chartVel b s₁ s₂ (φ (A.π z)) 1
        - inner ℝ (uGrad A φ 0 z) (uGrad A φ 1 z) * chartVel b s₁ s₂ (φ (A.π z)) 0) • uGrad A φ 1 z))

/-- The raw model field: the least-squares solution of the two chart-coordinate equations. -/
noncomputable def modelRawField (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (b : ℝ → ℝ) (s₁ s₂ : ℝ) :
    EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5) := fun z => modelRaw A φ b s₁ s₂ z

/-- The model field, projected by `dE` so that it is tangent to the image of `e`. -/
noncomputable def modelField (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (b : ℝ → ℝ) (s₁ s₂ : ℝ) :
    EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5) :=
  fun z => (fderiv ℝ A.E z) (modelRaw A φ b s₁ s₂ z)

/-- A smooth multiplier which is `0` below `r ^ 2 / 2` and `1 / (2 σ)` above `r ^ 2`.  It is the
function of `‖u‖ ^ 2` multiplying `(s₁ u 0, s₂ u 1)` in the chart-velocity `chartVel`: with it the
model field raises `chartQ` at speed `2 σ b σ`, which is `0` near the critical point and `1` on the
shell `‖u‖ ^ 2 ≥ r ^ 2`. -/
noncomputable def chartMult (r : ℝ) : ℝ → ℝ :=
  fun σ => Real.smoothTransition (2 * σ / r ^ 2 - 1) * (2 * σ)⁻¹

lemma chartMult_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartMult r) := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  rw [contDiff_iff_contDiffAt]
  intro σ
  rcases lt_or_ge σ (r ^ 2 / 2) with h | h
  · have hev : chartMult r =ᶠ[𝓝 σ] fun _ => (0 : ℝ) := by
      refine Filter.eventually_of_mem (isOpen_Iio.mem_nhds h) ?_
      intro s hs
      have hs' : 2 * s / r ^ 2 - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hr2]
        linarith [le_of_lt (show s < r ^ 2 / 2 from hs)]
      simp [chartMult, Real.smoothTransition.zero_of_nonpos hs']
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hpos : (0 : ℝ) < σ := lt_of_lt_of_le (by positivity) h
    have haff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => 2 * s / r ^ 2 - 1) := by
      have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (2 : ℝ) * s) :=
        contDiff_const.mul contDiff_id
      exact (hlin.div_const (r ^ 2)).sub contDiff_const
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => Real.smoothTransition (2 * s / r ^ 2 - 1)) σ :=
      (Real.smoothTransition.contDiff.comp haff).contDiffAt
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (2 * s)⁻¹) σ := by
      have hlin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (2 : ℝ) * s) σ :=
        contDiffAt_const.mul contDiffAt_id
      exact hlin.inv (mul_ne_zero two_ne_zero (ne_of_gt hpos))
    exact h1.mul h2

lemma chartMult_nonneg (r σ : ℝ) : 0 ≤ chartMult r σ := by
  rcases lt_or_ge σ 0 with h | h
  · have h1 : 2 * σ / r ^ 2 - 1 ≤ 0 := by
      have h2 : 2 * σ / r ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg r)
      linarith
    simp [chartMult, Real.smoothTransition.zero_of_nonpos h1]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (inv_nonneg.mpr (by positivity))

lemma chartMult_eq_zero {r σ : ℝ} (hr : 0 < r) (hσ : σ ≤ r ^ 2 / 2) : chartMult r σ = 0 := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hs' : 2 * σ / r ^ 2 - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hr2]
    linarith
  simp [chartMult, Real.smoothTransition.zero_of_nonpos hs']

lemma chartMult_mul {r σ : ℝ} (hr : 0 < r) (hσ : r ^ 2 ≤ σ) : 2 * σ * chartMult r σ = 1 := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have h2 : (2 : ℝ) ≤ 2 * σ / r ^ 2 := by
    rw [le_div_iff₀ hr2]
    linarith
  have hs : 1 ≤ 2 * σ / r ^ 2 - 1 := by linarith
  have hσ0 : (2 : ℝ) * σ ≠ 0 := by
    have : (0 : ℝ) < σ := hr2.trans_le hσ
    positivity
  rw [chartMult, Real.smoothTransition.one_of_one_le hs, one_mul, mul_inv_cancel₀ hσ0]

lemma chartMult_pos {r σ : ℝ} (hr : 0 < r) (hσ : r ^ 2 / 2 < σ) : 0 < chartMult r σ := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have h1 : 0 < 2 * σ / r ^ 2 - 1 := by
    have : (1 : ℝ) < 2 * σ / r ^ 2 := by
      rw [lt_div_iff₀ hr2]
      linarith
    linarith
  have hσ0 : (0 : ℝ) < σ := lt_of_le_of_lt (by positivity) hσ
  exact mul_pos (Real.smoothTransition.pos_of_pos h1) (inv_pos.mpr (by positivity))

/-- The coordinates of `chartVel`. -/
lemma chartVel_apply (b : ℝ → ℝ) (s₁ s₂ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    chartVel b s₁ s₂ u 0 = b (‖u‖ ^ 2) * (s₁ * u 0) ∧
      chartVel b s₁ s₂ u 1 = b (‖u‖ ^ 2) * (s₂ * u 1) := by
  constructor <;> simp [chartVel]

/-- The two chart coordinates of a vector: `(u 0) ^ 2 + (u 1) ^ 2 = ‖u‖ ^ 2`. -/
lemma norm_uVec (u : EuclideanSpace ℝ (Fin 2)) :
    (u 0) ^ 2 + (u 1) ^ 2 = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

/-- The model quadratic form pairing: `∇Q · chartVel = 2 * ‖u‖ ^ 2 * b (‖u‖ ^ 2)`. -/
lemma quadForm_chartVel (b : ℝ → ℝ) {s₁ s₂ : ℝ} (h₁ : s₁ = 1 ∨ s₁ = -1)
    (h₂ : s₂ = 1 ∨ s₂ = -1) (u : EuclideanSpace ℝ (Fin 2)) :
    (2 * s₁ * u 0) * (chartVel b s₁ s₂ u 0) + (2 * s₂ * u 1) * (chartVel b s₁ s₂ u 1)
      = 2 * ‖u‖ ^ 2 * b (‖u‖ ^ 2) := by
  obtain ⟨h0, h1⟩ := chartVel_apply b s₁ s₂ u
  rw [h0, h1]
  have hs₁ : s₁ ^ 2 = 1 := by rcases h₁ with h | h <;> rw [h] <;> norm_num
  have hs₂ : s₂ ^ 2 = 1 := by rcases h₂ with h | h <;> rw [h] <;> norm_num
  have hthis : (2 * s₁ * u 0) * (b (‖u‖ ^ 2) * (s₁ * u 0))
      + (2 * s₂ * u 1) * (b (‖u‖ ^ 2) * (s₂ * u 1))
      = (2 * s₁ ^ 2 * u 0 ^ 2 + 2 * s₂ ^ 2 * u 1 ^ 2) * b (‖u‖ ^ 2) := by ring
  rw [hthis, hs₁, hs₂, ← norm_uVec u]
  ring

/-- The two chart coordinates of a vector: `(u 0) ^ 2 + (u 1) ^ 2 = ‖u‖ ^ 2`. -/
theorem inner_gram_leastSquares {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) (w₀ w₁ : ℝ)
    (hdet : ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2 ≠ 0) :
    inner ℝ x ((‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2)⁻¹ •
        ((‖y‖ ^ 2 * w₀ - inner ℝ x y * w₁) • x + (‖x‖ ^ 2 * w₁ - inner ℝ x y * w₀) • y)) = w₀
      ∧ inner ℝ y ((‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2)⁻¹ •
        ((‖y‖ ^ 2 * w₀ - inner ℝ x y * w₁) • x + (‖x‖ ^ 2 * w₁ - inner ℝ x y * w₀) • y)) = w₁ := by
  have hx : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have hy : inner ℝ y y = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  constructor
  · rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right, hx]
    rw [show (‖y‖ ^ 2 * w₀ - inner ℝ x y * w₁) * ‖x‖ ^ 2
          + (‖x‖ ^ 2 * w₁ - inner ℝ x y * w₀) * inner ℝ x y
          = w₀ * (‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2) from by ring]
    rw [mul_comm w₀, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
  · have hdet'' : ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ y x) ^ 2 ≠ 0 := by
      simpa [real_inner_comm y x] using hdet
    rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right, hy,
      real_inner_comm y x]
    rw [show (‖y‖ ^ 2 * w₀ - inner ℝ y x * w₁) * inner ℝ y x
          + (‖x‖ ^ 2 * w₁ - inner ℝ y x * w₀) * ‖y‖ ^ 2
          = w₁ * (‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ y x) ^ 2) from by ring]
    rw [mul_comm w₁, ← mul_assoc, inv_mul_cancel₀ hdet'', one_mul]

end Work.Drive.N2
