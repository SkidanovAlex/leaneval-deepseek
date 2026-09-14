import ChallengeDeps
import Submission.NBody.Potential
import Submission.Commons.Data.Fin.sum_Iio_add_Ioi_eq_erase
import Submission.Commons.Data.Fin.pairSum_k_partition
import Mathlib

/-!
# Newton's force identity, per body

Third stone of the analytic layer.  We take the pair-sum derivative of `U m`
(`hasFDerivAt_U_pair`) and read off its action on a direction that moves only body `k`,
which must equal the scalar product of `(∇(U m) x)ₖ` with the test velocity.  The result
is the per-body Newton force identity

    `⟨(∇(U m) x)ₖ, v⟩ = ∑_{j ≠ k} mₖ mⱼ · ⟨xⱼ - xₖ, v⟩ / ‖xⱼ - xₖ‖³`

and hence (dividing by `mₖ`) the mass-weighted gradient field used in the equations of motion.

All declarations here are fully proved (no `sorry`, no axioms).
-/

open ViscositySolutions
open InnerProductSpace
open scoped BigOperators

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The direction in configuration space that moves only body `k`, by the vector `v`. -/
def singleBodyVec (k : Fin N) (v : E) : EN E N :=
  WithLp.toLp 2 (fun i : Fin N => if i = k then v else 0)

lemma singleBodyVec_self (k : Fin N) (v : E) : singleBodyVec k v k = v := by
  simp [singleBodyVec]

lemma singleBodyVec_of_ne {k i : Fin N} (h : i ≠ k) (v : E) : singleBodyVec k v i = 0 := by
  simp [singleBodyVec, h]

/-- Evaluating the pair-sum derivative of `U m` at an arbitrary direction `d` gives the sum
over the pairs `i < j` of `mᵢ mⱼ · (-⟨xᵢ - xⱼ, dᵢ - dⱼ⟩ / ‖xᵢ - xⱼ‖³)`. -/
lemma fderiv_U_pair_apply (m : Fin N → ℝ) (x d : EN E N) (hx : WithoutCollisions x) :
    (fderiv ℝ (U m) x) d =
      ∑ p ∈ pairFinset N, m p.1 * m p.2 *
        (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2) (d p.1 - d p.2)) := by
  have hf := hasFDerivAt_U_pair m x hx
  rw [hf.fderiv]
  let ev : (EN E N →L[ℝ] ℝ) →+ ℝ :=
    { toFun := fun (φ : EN E N →L[ℝ] ℝ) => φ d
      map_zero' := by simp
      map_add' := by intro f g; rfl }
  change ev (∑ p ∈ pairFinset N, ((m p.1 * m p.2) •
      (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) • ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2))))) =
      ∑ p ∈ pairFinset N, m p.1 * m p.2 *
        (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2) (d p.1 - d p.2))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp [ev]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [pairMap_apply d p.1 p.2]
  rfl


/-- Per-body directional derivative: moving only body `k` by `v` changes `U m` at the
Newtonian rate `∑_{j ≠ k} mₖ mⱼ ⟨xⱼ - xₖ, v⟩ / ‖xⱼ - xₖ‖³`.  This is the scalar form of
Newton's force law `(∇(U m) x)ₖ = ∑_{j ≠ k} mₖ mⱼ (xⱼ - xₖ)/rⱼₖ³`. -/
lemma fderiv_U_singleBody (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x)
    (k : Fin N) (v : E) :
    (fderiv ℝ (U m) x) (singleBodyVec k v) =
      ∑ j ∈ Finset.univ.erase k, m k * m j * (‖x j - x k‖ ^ 3)⁻¹ * inner ℝ (x j - x k) v := by
  let f : Fin N → Fin N → ℝ := fun i j =>
    m i * m j * (-((‖x i - x j‖ ^ 3)⁻¹) *
      inner ℝ (x i - x j) ((singleBodyVec k v) i - (singleBodyVec k v) j))
  rw [fderiv_U_pair_apply m x (singleBodyVec k v) hx]
  change (∑ p ∈ pairFinset N, f p.1 p.2) =
      ∑ j ∈ Finset.univ.erase k, m k * m j * (‖x j - x k‖ ^ 3)⁻¹ * inner ℝ (x j - x k) v
  -- use the partition of the pair sum at body k
  unfold pairFinset
  rw [Commons.Data.Fin.pairSum_k_partition (k := k) (f := f)]
  have hrest : (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).filter
      (fun p => p.1 ≠ k ∧ p.2 ≠ k), f p.1 p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨h1, h2⟩
    simp [f, singleBodyVec, h1, h2]
  have hlt : (∑ i ∈ Finset.Iio k, f i k) =
      ∑ i ∈ Finset.Iio k, m k * m i * (‖x i - x k‖ ^ 3)⁻¹ * inner ℝ (x i - x k) v := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≠ k := ne_of_lt (Finset.mem_Iio.mp hi)
    simp [f, singleBodyVec, hik]
    ring_nf
  have hgt : (∑ j ∈ Finset.Ioi k, f k j) =
      ∑ j ∈ Finset.Ioi k, m k * m j * (‖x j - x k‖ ^ 3)⁻¹ * inner ℝ (x j - x k) v := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≠ k := ne_of_gt (Finset.mem_Ioi.mp hj)
    have hnorm : (‖x k - x j‖ ^ 3)⁻¹ = (‖x j - x k‖ ^ 3)⁻¹ := by
      have hsub : ‖x k - x j‖ = ‖x j - x k‖ := by
        simpa [neg_sub] using norm_neg (x j - x k)
      rw [hsub]
    simp [f, singleBodyVec, hjk, hnorm]
    have hsub' : x k - x j = -(x j - x k) := by abel
    have hin : inner ℝ (x k - x j) v = -inner ℝ (x j - x k) v := by
      rw [hsub', inner_neg_left]
    rw [hin]
    ring_nf
  rw [hrest, hlt, hgt, add_zero]
  rw [← Commons.Data.Fin.sum_Iio_add_Ioi_eq_erase (k := k)
    (f := fun j : Fin N => m k * m j * (‖x j - x k‖ ^ 3)⁻¹ * inner ℝ (x j - x k) v)]


/-! ## Gradient form of the force identity -/

/-- The gradient tested against a direction equals the Fréchet derivative along it. -/
lemma inner_gradient_eq_fderiv {f : EN E N → ℝ} (x d : EN E N) :
    inner ℝ (gradient f x) d = (fderiv ℝ f x) d := by
  have h := toDual_gradient (f := f) (x := x)
  simpa using congrFun h d

/-- Inner product with the direction that moves only body `k` reads off the coordinate `k`. -/
lemma inner_singleBody (a : EN E N) (k : Fin N) (v : E) :
    inner ℝ a (singleBodyVec k v) = inner ℝ (a k) v := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single k]
  · simp [singleBodyVec]
  · intro i hi hik
    have hne : i ≠ k := hik
    simp [singleBodyVec, hne]
  · intro hk
    simp at hk

/-- Newton's law, scalar form: the force on body `k` tested against the velocity `v` is
`∑_{j ≠ k} mₖ mⱼ ⟨xⱼ - xₖ, v⟩ / ‖xⱼ - xₖ‖³`. -/
lemma gradient_U_singleBody_apply (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x)
    (k : Fin N) (v : E) :
    inner ℝ (gradient (U m) x) (singleBodyVec k v) =
      ∑ j ∈ Finset.univ.erase k, m k * m j * (‖x j - x k‖ ^ 3)⁻¹ * inner ℝ (x j - x k) v := by
  rw [inner_gradient_eq_fderiv]
  exact fderiv_U_singleBody m x hx k v


/-- **Newton's force identity, per coordinate.**  The `k`-th coordinate of `∇(U m)` is the
sum of the Newtonian pulls of all the other bodies:
`(∇(U m) x)ₖ = ∑_{j ≠ k} mₖ mⱼ (xⱼ - xₖ)/‖xⱼ - xₖ‖³`. -/
lemma gradient_U_coord (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x) (k : Fin N) :
    (gradient (U m) x) k =
      ∑ j ∈ Finset.univ.erase k, (m k * m j * (‖x j - x k‖ ^ 3)⁻¹) • (x j - x k) := by
  apply (toDual ℝ E).injective
  ext v
  change inner ℝ ((gradient (U m) x) k) v =
    inner ℝ (∑ j ∈ Finset.univ.erase k, (m k * m j * (‖x j - x k‖ ^ 3)⁻¹) • (x j - x k)) v
  rw [← inner_singleBody (gradient (U m) x) k v]
  rw [gradient_U_singleBody_apply m x hx k v]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_left]
  simp

/-- **Mass-weighted Newton force identity.**  For the mass-weighted gradient (the field in
Newton's equations `x'' = ∇ₘ U(x)`) the `k`-th coordinate is
`∑_{j ≠ k} mⱼ (xⱼ - xₖ)/‖xⱼ - xₖ‖³`, i.e. exactly `mₖ xₖ''`. -/
lemma weightedGrad_U_coord (m : Fin N → ℝ) (hm : ∀ i, m i ≠ 0) (x : EN E N)
    (hx : WithoutCollisions x) (k : Fin N) :
    (weightedGrad m (U m) x) k =
      ∑ j ∈ Finset.univ.erase k, (m j * (‖x j - x k‖ ^ 3)⁻¹) • (x j - x k) := by
  have hcoord : (weightedGrad m (U m) x) k = (m k)⁻¹ • (gradient (U m) x) k := by
    simp [weightedGrad]
  rw [hcoord, gradient_U_coord m x hx k, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul]
  congr 1
  have hk : m k ≠ 0 := hm k
  field_simp

end Submission.NBody
