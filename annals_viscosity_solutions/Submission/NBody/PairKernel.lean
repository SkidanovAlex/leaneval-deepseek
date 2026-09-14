import ChallengeDeps
import Mathlib

/-!
# The pairwise interaction `x ↦ mᵢ mⱼ ‖xᵢ - xⱼ‖⁻¹`

First stone of the analytic layer of the `N`-body formalisation: the two-body interaction
kernel is *smooth away from the diagonal* and has the *Newtonian gradient*.

Let `E` be a real inner-product space, `N : ℕ` and `Eᴺ := EuclideanSpace E (Fin N)` the
configuration space.  For two distinct bodies `i j : Fin N` consider the pairwise map

    `p_ij (x) := ‖xᵢ - xⱼ‖⁻¹`

(times the constant `mᵢ mⱼ`, which plays no role in the calculus).  On the open set
`{x | xᵢ ≠ xⱼ}` (the complement of the diagonal) this map is `Cⁿ` for every `n`, and its
Fréchet derivative at `x` is the linear map

    `w ↦ -⟨xᵢ - xⱼ, wᵢ - wⱼ⟩ / ‖xᵢ - xⱼ‖³`,

i.e. `-‖xᵢ - xⱼ‖⁻³ • (innerSL (xᵢ - xⱼ) ∘ (x ↦ xᵢ - xⱼ))`.  Equivalently the gradient
points *towards the other body*: the contribution of the pair `(i,j)` to the force on body
`i` is `mᵢ mⱼ (xⱼ - xᵢ)/‖xᵢ - xⱼ‖³` — the Newtonian sign convention, so that summing over
pairs in `U m` reproduces Newton's equations `mᵢ xᵢ'' = -Σⱼ≠ᵢ mᵢ mⱼ (xᵢ - xⱼ)/rᵢⱼ³`.

Every declaration below is fully proved (no `sorry`, no axioms).
-/

open scoped BigOperators
open ContinuousLinearMap

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Submission.NBody

/-! ## The radial kernel `z ↦ ‖z‖⁻¹` on a Euclidean space `E` -/

/-- The derivative of the norm at a non-zero point: `∇‖z‖ = z / ‖z‖`. -/
lemma hasFDerivAt_norm₀ (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun w : E => ‖w‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hqx : (‖x‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (by simpa using (norm_ne_zero_iff.mpr hx))
  have hq : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hs : HasDerivAt (fun t : ℝ => √t) (1 / (2 * √(‖x‖ ^ 2))) (‖x‖ ^ 2) :=
    Real.hasDerivAt_sqrt hqx
  have hcomp : HasFDerivAt (fun w : E => √(‖w‖ ^ 2))
      ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x := by
    exact HasDerivAt.comp_hasFDerivAt x hs hq
  have hfuneq : (fun w : E => √(‖w‖ ^ 2)) = (fun w : E => ‖w‖) := by
    funext w
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (norm_nonneg w)
  have hcoe : (((‖x‖⁻¹ * 2⁻¹) • (2 • innerSL ℝ x)) : E →L[ℝ] ℝ) =
      ‖x‖⁻¹ • innerSL ℝ x := by
    ext w
    simp only [smul_apply, smul_eq_mul]
    ring_nf
  simpa [hfuneq, hcoe] using hcomp

/-- The gradient of the Newtonian kernel `z ↦ ‖z‖⁻¹` at a non-zero point is `-z / ‖z‖³`.
This is the radial part of the pairwise interaction, written in the sign convention that
makes the force point *towards* the other body. -/
lemma hasFDerivAt_inv_norm (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun w : E => ‖w‖⁻¹) (-((‖x‖ ^ 3)⁻¹) • innerSL ℝ x) x := by
  have hnx : ‖x‖ ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hx)
  have hinv := hasDerivAt_inv hnx
  have hcomp := HasDerivAt.comp_hasFDerivAt x hinv (hasFDerivAt_norm₀ x hx)
  have hcoe : ((-(‖x‖ ^ 2)⁻¹) • (‖x‖⁻¹ • innerSL ℝ x) : E →L[ℝ] ℝ) =
      -((‖x‖ ^ 3)⁻¹) • innerSL ℝ x := by
    ext w
    simp only [smul_apply, smul_eq_mul, neg_mul]
    field_simp [hnx]
  have hfun : ((fun y : ℝ => y⁻¹) ∘ norm) = (fun w : E => ‖w‖⁻¹) := by
    rfl
  simpa [hfun, hcoe] using hcomp

/-- The Newtonian kernel is `Cⁿ` away from the origin, for every order `n`. -/
lemma contDiffOn_inv_norm {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun w : E => ‖w‖⁻¹) {x | x ≠ 0} := by
  have hf : ContDiffOn ℝ n (fun w : E => ‖w‖) {x | x ≠ 0} := by
    refine ContDiffOn.norm ℝ ?hf ?h0
    · exact contDiffOn_id
    · intro x hx
      simpa using hx
  exact ContDiffOn.inv hf (by intro x hx; exact norm_ne_zero_iff.mpr hx)

/-! ## The pairwise kernel on the configuration space `Eᴺ := EuclideanSpace E (Fin N)` -/

variable {N : ℕ}

abbrev EN (E : Type*) (N : ℕ) := EuclideanSpace E (Fin N)

/-- Difference of the projections onto the coordinates `i` and `j`:
`(pairMap i j) x = xᵢ - xⱼ`. -/
def pairMap (i j : Fin N) : EN E N →L[ℝ] E :=
  PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) i -
    PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) j

lemma pairMap_apply (y : EN E N) (i j : Fin N) : pairMap i j y = y i - y j := by
  simp [pairMap]

/-- Fréchet derivative of the pairwise kernel `y ↦ ‖yᵢ - yⱼ‖⁻¹` away from the diagonal.
The sign is Newton's: the kernel decreases in the direction in which the two bodies move
apart, so the corresponding force on body `i` points towards body `j`. -/
lemma hasFDerivAt_pair_inv_norm (i j : Fin N) (x : EN E N) (h : x i ≠ x j) :
    HasFDerivAt (fun y : EN E N => ‖y i - y j‖⁻¹)
      (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j))) x := by
  let L : EN E N →L[ℝ] E := pairMap i j
  have hLx : L x = x i - x j := by simp [L, pairMap]
  have hLz : L x ≠ 0 := by
    rw [hLx]
    exact sub_ne_zero.mpr h
  have hk : HasFDerivAt (fun w : E => ‖w‖⁻¹)
      (-((‖x i - x j‖ ^ 3)⁻¹) • innerSL ℝ (x i - x j)) (L x) := by
    have hk0 := hasFDerivAt_inv_norm (L x) hLz
    simpa [hLx] using hk0
  have hL : HasFDerivAt (fun y : EN E N => L y) L x := L.hasFDerivAt
  have hc := hk.comp x hL
  have hfun : ((fun w : E => ‖w‖⁻¹) ∘ fun y : EN E N => L y) = fun y : EN E N => ‖y i - y j‖⁻¹ := by
    funext y
    change ‖pairMap i j y‖⁻¹ = ‖y i - y j‖⁻¹
    rw [pairMap_apply y i j]
  simpa [L, hfun, hLx] using hc

/-- The pairwise kernel is `Cⁿ` on the complement of the diagonal, for every order `n`. -/
lemma contDiffOn_pair_inv_norm {n : WithTop ℕ∞} (i j : Fin N) :
    ContDiffOn ℝ n (fun y : EN E N => ‖y i - y j‖⁻¹) {x | x i ≠ x j} := by
  let L : EN E N →L[ℝ] E := pairMap i j
  have hLc : ContDiffOn ℝ n (fun y : EN E N => L y) {x | x i ≠ x j} :=
    (ContinuousLinearMap.contDiff L).contDiffOn
  have hnorm : ContDiffOn ℝ n (fun y : EN E N => ‖L y‖) {x | x i ≠ x j} := by
    refine ContDiffOn.norm ℝ hLc ?h0
    intro x hx
    have hLx : L x = x i - x j := by simp [L, pairMap]
    rw [hLx]
    exact sub_ne_zero.mpr hx
  have hinv : ContDiffOn ℝ n (fun y : EN E N => ‖L y‖⁻¹) {x | x i ≠ x j} := by
    exact ContDiffOn.inv hnorm (by
      intro x hx
      have hLx : L x = x i - x j := by simp [L, pairMap]
      rw [hLx]
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
  have hfeq : (fun y : EN E N => ‖L y‖⁻¹) = (fun y : EN E N => ‖y i - y j‖⁻¹) := by
    funext y
    simp [L, pairMap]
  rw [← hfeq]
  exact hinv

/-- Directional form of the derivative, spelling out the Newtonian sign: an infinitesimal
motion of the configuration `x` with velocity field `d` changes the pair kernel at rate
`-⟨xᵢ - xⱼ, dᵢ - dⱼ⟩ / ‖xᵢ - xⱼ‖³`.  In particular, moving only body `i` towards `j`
increases the kernel (force on `i` points towards `j`). -/
lemma fderiv_pair_inv_norm_apply (i j : Fin N) (x d : EN E N) (h : x i ≠ x j) :
    (fderiv ℝ (fun y : EN E N => ‖y i - y j‖⁻¹) x) d =
      -((‖x i - x j‖ ^ 3)⁻¹) • inner ℝ (x i - x j) (d i - d j) := by
  have hf := hasFDerivAt_pair_inv_norm i j x h
  rw [hf.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [pairMap_apply d i j]
  rfl
