import ChallengeDeps
import Submission.NBody.PairKernel
import Submission.Commons.Data.Fin.pairSum_Iio_filter
import Submission.Commons.Data.Fin.pairFilter_snd
import Submission.Commons.Data.Fin.pairFilter_fst
import Mathlib

/-!
# The gradient of the Newtonian potential `U m` (finite sum over pairs)

Second stone of the analytic layer.  `U m` is a finite sum over the pairs `i < j` of the
pairwise terms `y ↦ mᵢ mⱼ (r y i j)⁻¹` (with `r y i j = ‖yᵢ - yⱼ‖`).  Using the pairwise
derivative from `PairKernel.lean` and the fact that `HasFDerivAt` commutes with finite sums
(`HasFDerivAt.sum`), we obtain the derivative of the whole potential at every collision-free
configuration `x`:

    `fderiv (U m) x = ∑_{i < j} mᵢ mⱼ · (-(‖xᵢ - xⱼ‖³)⁻¹ · innerSL (xᵢ - xⱼ) ∘ pairMap i j)`.

Combined with the mass-weighted gradient (`weightedGrad m (U m) x` has coordinate `i`
equal to `(mᵢ)⁻¹ (∇(U m) x)ᵢ`) this is the analytic content behind Newton's equations.

The pair-enumeration scaffolding (double sums `∑ j, ∑ i < j` vs. single sums over the finset
of pairs) is provided by the shared Commons (`Commons.Data.Fin.pairSum_Iio_filter` etc.);
the statements below are written in the shape of `U` itself (the `∑ i < j` double sum), which
is definitionally the same as `∑ i ∈ Finset.Iio j`.

Every declaration here is fully proved (no `sorry`, no axioms).
-/

open ViscositySolutions
open scoped BigOperators

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The finset of unordered pairs `{(i, j) | i < j}`. -/
def pairFinset (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)

/-! ## `r` is the norm of the coordinate difference, and collision-freeness -/

/-- `r y i j = ‖yᵢ - yⱼ‖` (definitional unfolding of `dist` on a normed group). -/
lemma r_eq_norm_sub (y : EN E N) (i j : Fin N) : r y i j = ‖y i - y j‖ := by
  simp [r, dist_eq_norm_sub]

/-- Non-collision of the pair `(i,j)` is exactly `yᵢ ≠ yⱼ`. -/
lemma r_ne_zero_iff (y : EN E N) (i j : Fin N) : r y i j ≠ 0 ↔ y i ≠ y j := by
  rw [r_eq_norm_sub]
  rw [norm_ne_zero_iff]
  exact sub_ne_zero

/-! ## Derivative of a single pair term of `U m` -/

/-- Fréchet derivative of one summand `y ↦ mᵢ mⱼ (r y i j)⁻¹` of the potential at a
configuration where the two bodies are separated. -/
lemma hasFDerivAt_U_pair_term (m : Fin N → ℝ) (i j : Fin N) (x : EN E N) (hx : r x i j ≠ 0) :
    HasFDerivAt (fun y : EN E N => m i * m j * (r y i j)⁻¹)
      ((m i * m j) • (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j)))) x := by
  have hne : x i ≠ x j := (r_ne_zero_iff x i j).mp hx
  have hk := hasFDerivAt_pair_inv_norm i j x hne
  have hker : HasFDerivAt (fun y : EN E N => (r y i j)⁻¹)
      (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j))) x := by
    have hfeq : (fun y : EN E N => ‖y i - y j‖⁻¹) = (fun y : EN E N => (r y i j)⁻¹) := by
      funext y
      rw [← r_eq_norm_sub y i j]
    simpa [hfeq] using hk
  exact hker.const_mul (m i * m j)

/-! ## Derivative of the full potential -/

/-- The Newtonian potential `U m` is differentiable at every collision-free configuration,
and its derivative is the sum over the pairs `i < j` of the pairwise derivatives
(scaled by `mᵢ mⱼ`). -/
lemma hasFDerivAt_U (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x) :
    HasFDerivAt (U m)
      (∑ j : Fin N, (∑ i ∈ Finset.Iio j,
          (m i * m j) • (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j))))) x := by
  -- outer sum over j, inner over i ∈ Iio j; bind the derivative expression
  let D : EN E N →L[ℝ] ℝ := ∑ j : Fin N, (∑ i ∈ Finset.Iio j,
          (m i * m j) • (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j))))
  change HasFDerivAt (U m) D x
  change HasFDerivAt (fun y : EN E N => ∑ j : Fin N, (∑ i ∈ Finset.Iio j,
      m i * m j * (r y i j)⁻¹)) D x
  -- inner sums: for each j, differentiate ∑ over i < j term by term
  have hFj : ∀ j : Fin N,
      HasFDerivAt (∑ i ∈ Finset.Iio j, (fun y : EN E N => m i * m j * (r y i j)⁻¹))
        (∑ i ∈ Finset.Iio j,
          (m i * m j) • (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j)))) x := by
    intro j
    exact HasFDerivAt.sum (u := Finset.Iio j)
      (A := fun i : Fin N => (fun y : EN E N => m i * m j * (r y i j)⁻¹))
      (A' := fun i : Fin N => (m i * m j) •
        (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j))))
      (by
        intro i hi
        have hij : i < j := (Finset.mem_Iio.mp hi)
        have hne : r x i j ≠ 0 := hx i j (ne_of_lt hij)
        exact hasFDerivAt_U_pair_term m i j x hne)
  -- outer sum over j of the inner derivatives
  have hF : HasFDerivAt (∑ j : Fin N, (∑ i ∈ Finset.Iio j,
        (fun y : EN E N => m i * m j * (r y i j)⁻¹)))
      D x := by
    simpa [D] using (HasFDerivAt.sum (u := Finset.univ)
      (A := fun j : Fin N => ∑ i ∈ Finset.Iio j, (fun y : EN E N => m i * m j * (r y i j)⁻¹))
      (A' := fun j : Fin N => ∑ i ∈ Finset.Iio j,
        (m i * m j) • (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j))))
      (by intro j hj; exact hFj j))
  -- a sum of functions equals the pointwise sum of the values
  have hfeq : (fun y : EN E N => ∑ j : Fin N, (∑ i ∈ Finset.Iio j,
      m i * m j * (r y i j)⁻¹)) =
      (∑ j : Fin N, (∑ i ∈ Finset.Iio j, (fun y : EN E N => m i * m j * (r y i j)⁻¹))) := by
    ext y
    simp only [Finset.sum_apply]
  rw [hfeq]
  exact hF


/-! ## The potential as a single sum over the pair finset -/

/-- `U m y` equals the single sum over the finset of pairs `{(i, j) | i < j}`. -/
lemma U_eq_pairFinset (m : Fin N → ℝ) (y : EN E N) :
    U m y = ∑ p ∈ pairFinset N, m p.1 * m p.2 * (r y p.1 p.2)⁻¹ := by
  simpa [U, pairFinset] using
    (Commons.Data.Fin.pairSum_Iio_filter (f := fun i j : Fin N => m i * m j * (r y i j)⁻¹))

/-- The derivative of `U m` expressed as a single sum over the pair finset (the form used
in the Newton-force identity and the energy estimate). -/
lemma hasFDerivAt_U_pair (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x) :
    HasFDerivAt (U m)
      (∑ p ∈ pairFinset N,
        (m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
          ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2)))) x := by
  unfold pairFinset
  rw [← Commons.Data.Fin.pairSum_Iio_filter
    (f := fun i j : Fin N => (m i * m j) •
      (-((‖x i - x j‖ ^ 3)⁻¹) • ((innerSL ℝ (x i - x j)).comp (pairMap i j))))]
  simpa using hasFDerivAt_U m x hx

end Submission.NBody
