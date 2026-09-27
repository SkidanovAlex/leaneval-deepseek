import Mathlib
import Submission.Work.KT.Idx.PenDefs

/-!
# `Work.Idx.matPenProj_eval` — slicing of the pencil projection

The pencil projection `matPenProj` of `Work.KT.Idx.PenDefs` is the Riesz projection
`(2πi)⁻¹ ∮_{|z|=1} (z•A + B)⁻¹ A dz` of a matrix pencil over `C(X, ℂ)`, computed in the
`L∞`-operator-norm Banach algebra of matrices.  Here we show that it is compatible with
evaluation of the base parameter at a point `t : I`: the algebraic operations occurring in the
definition (scalar multiplication, inversion of a matrix which is a unit, matrix multiplication,
and the circle integral, which is a limit of finite sums) are all preserved by the continuous
`ℂ`-algebra homomorphism `Matrix.map (evalPull X t)`.

The file proves the ingredients separately, in a form independent of the particular matrix
algebra, and then assembles them:

* `ringHom_map_ringInverse` — a ring homomorphism commutes with `Ring.inverse` of a unit;
* `circleIntegral_map_clm` — a continuous linear map commutes with circle integrals;
* `continuousOn_res` — continuity of the resolvent on the unit circle (from `Ring.inverse`
  being continuous at units);
* `penProj_map` — the abstract statement: for a continuous `ℂ`-algebra homomorphism `T`
  (contraction, commutes with `algebraMap`) and a pencil invertible on the unit circle,
  `T (penProj A B) = penProj (T A) (T B)`;
* `mapMatrix_evalPull_algebraMap` — the entrywise evaluation map is `ℂ`-linear;
* and the final `matPenProj_eval`, where the norm contraction of the evaluation map is
  established directly (`‖M.map (evalPull X t)‖ ≤ ‖M‖` for the `L∞` operator norms).
-/

set_option linter.style.haveILetI false

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- A ring homomorphism commutes with the totalized inverse of a unit. -/
theorem ringHom_map_ringInverse {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) {x : R}
    (hx : IsUnit x) : φ (Ring.inverse x) = Ring.inverse (φ x) := by
  have h1 : φ x * φ (Ring.inverse x) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel x hx, map_one]
  have hu : IsUnit (φ x) := hx.map φ
  calc φ (Ring.inverse x) = 1 * φ (Ring.inverse x) := (one_mul _).symm
    _ = (Ring.inverse (φ x) * φ x) * φ (Ring.inverse x) := by rw [Ring.inverse_mul_cancel _ hu]
    _ = Ring.inverse (φ x) * (φ x * φ (Ring.inverse x)) := by rw [mul_assoc]
    _ = Ring.inverse (φ x) * 1 := by rw [h1]
    _ = Ring.inverse (φ x) := mul_one _

open Work.KT.Idx in
/-- A continuous linear map commutes with circle integrals. -/
theorem circleIntegral_map_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : ℂ → E) (c : ℂ) (R : ℝ) (hf : CircleIntegrable f c R) :
    L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  have hd : ContinuousOn (fun θ : ℝ => deriv (circleMap c R) θ) (Set.uIcc 0 (2 * Real.pi)) := by
    rw [show (fun θ : ℝ => deriv (circleMap c R) θ)
        = fun θ : ℝ => circleMap 0 R θ * Complex.I from funext fun θ => deriv_circleMap c R θ]
    exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
  have hfi : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * Real.pi) :=
    IntervalIntegrable.continuousOn_smul
      (show IntervalIntegrable (fun θ : ℝ => f (circleMap c R θ)) volume 0 (2 * Real.pi)
        from hf) hd
  have h := L.intervalIntegral_comp_comm (μ := volume) (a := 0) (b := 2 * Real.pi)
    (f := fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) hfi
  rw [circleIntegral, circleIntegral]
  rw [← h]
  exact intervalIntegral.integral_congr fun θ _ => L.map_smul _ _

/-- The resolvent of a pencil is continuous on the unit circle, whenever the pencil is
invertible there. -/
theorem continuousOn_res {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    ContinuousOn (fun z : ℂ => Ring.inverse (z • A + B) * A) (Metric.sphere (0:ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hzu : IsUnit (z • A + B) := hunit z hz1
  have h1 : ContinuousWithinAt (fun z : ℂ => z • A + B) (Metric.sphere (0:ℂ) 1) z := by
    fun_prop
  have h2 : ContinuousAt Ring.inverse (z • A + B) := by
    have h := NormedRing.inverse_continuousAt hzu.unit
    rwa [hzu.unit_spec] at h
  have h3 : ContinuousWithinAt (fun z : ℂ => Ring.inverse (z • A + B))
      (Metric.sphere (0:ℂ) 1) z :=
    h2.comp_continuousWithinAt (f := fun z : ℂ => z • A + B) h1
  exact h3.mul_const A

open Work.KT.Idx in
/-- **Abstract slicing.** If `T : R →+* S` is a contraction between complex Banach algebras
which is `ℂ`-linear (i.e. commutes with `algebraMap`) and `A B : R` have the pencil `z • A + B`
invertible on the unit circle, then `T` commutes with the pencil projection. -/
theorem penProj_map {R S : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    [NormedRing S] [NormedAlgebra ℂ S] [CompleteSpace S]
    (T : R →+* S) (hTalg : ∀ c : ℂ, T (algebraMap ℂ R c) = algebraMap ℂ S c)
    (hTnorm : ∀ x : R, ‖T x‖ ≤ ‖x‖)
    (A B : R) (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B))
    (hcont : ContinuousOn (fun z : ℂ => Ring.inverse (z • A + B) * A) (Metric.sphere (0:ℂ) 1)) :
    T (penProj A B) = penProj (T A) (T B) := by
  have hTlin : ∀ (c : ℂ) (x : R), T (c • x) = c • T x := fun c x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hTalg]
  let L : R →L[ℂ] S := LinearMap.mkContinuous
    { toFun := ⇑T, map_add' := T.map_add, map_smul' := hTlin } 1
    (fun x => by rw [one_mul]; exact hTnorm x)
  have hL : ∀ x : R, L x = T x := fun x => rfl
  have hTAB : ∀ z : ℂ, T (z • A + B) = z • T A + T B := fun z => by rw [map_add, hTlin]
  have hpoint : ∀ z : ℂ, ‖z‖ = 1 → T (pResA A B z) = pResA (T A) (T B) z := by
    intro z hz
    have hzu := hunit z hz
    show T (Ring.inverse (z • A + B) * A) = Ring.inverse (z • T A + T B) * T A
    rw [map_mul, ringHom_map_ringInverse T hzu, hTAB z]
  have hcirc : L (∮ z in C(0,1), pResA A B z) = ∮ z in C(0,1), pResA (T A) (T B) z := by
    have hc := circleIntegral_map_clm (L := L) (f := fun z : ℂ => pResA A B z) (c := 0) (R := 1)
      (hcont.circleIntegrable (by norm_num))
    rw [hc]
    refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
    rw [hL, hpoint z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)]
  show T ((2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0,1), pResA A B z)) =
    (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0,1), pResA (T A) (T B) z)
  rw [hTlin, ← hL, hcirc]

/-- The entrywise evaluation map `Matrix.map (evalPull X t)` sends the scalar matrix
`algebraMap ℂ _ c` to the scalar matrix `algebraMap ℂ _ c`. -/
theorem mapMatrix_evalPull_algebraMap (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (t : unitInterval) {N : ℕ} (c : ℂ) :
    RingHom.mapMatrix (Work.KT.Idx.evalPull X t)
        (algebraMap ℂ (Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ)) c) =
      algebraMap ℂ (Matrix (Fin N) (Fin N) C(X, ℂ)) c := by
  rw [RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_map (map_zero _)]
  congr 1

/-- **Slicing of the pencil projection.** The pencil projection over the base `X × unitInterval`
commutes with the evaluation-at-`t` ring homomorphism `Work.KT.Idx.evalPull X t` (the pull-back
along `x ↦ (x,t)`).  This is what turns a homotopy of pencils over `X × I` into a continuous path
of idempotents over `C(X, ℂ)`, hence (by `Work.KT.homotopy_inv`) into an equality of `cls`.

Route: `matPenProj` is `(2πi)⁻¹ • ∮_{C(0,1)} Ring.inverse (z • A + B) * A dz`.  The entrywise map
`Matrix.map (evalPull X t)` is a ℂ-algebra homomorphism `T` and a contraction for the `L∞` operator
norms, hence a continuous ℂ-linear map of the Banach spaces, so it commutes with the vector-valued
circle integral.  For the integrand one needs
`T (Ring.inverse (z • A + B)) = Ring.inverse (T (z • A + B))`, which holds because
`hunit` says `z • A + B` is a unit (and then `Ring.inverse` is the honest inverse, commuting with
the ring hom). -/
theorem matPenProj_eval (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {N : ℕ} (A B : Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ)) (t : unitInterval)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    (Work.KT.Idx.matPenProj (X × unitInterval) A B).map (Work.KT.Idx.evalPull X t) =
      Work.KT.Idx.matPenProj X (A.map (Work.KT.Idx.evalPull X t))
        (B.map (Work.KT.Idx.evalPull X t)) := by
  letI : NormedRing (Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ)) :=
    Matrix.linftyOpNormedAlgebra
  have hcomp₁ : CompleteSpace (Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ)) :=
    Matrix.instCompleteSpace _ _ _
  letI : NormedRing (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  have hcomp₂ : CompleteSpace (Matrix (Fin N) (Fin N) C(X, ℂ)) :=
    Matrix.instCompleteSpace _ _ _
  have hTnorm : ∀ M : Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ),
      ‖RingHom.mapMatrix (Work.KT.Idx.evalPull X t) M‖ ≤ ‖M‖ := by
    intro M
    have hpt : ∀ f : C(X × unitInterval, ℂ), ‖Work.KT.Idx.evalPull X t f‖ ≤ ‖f‖ := by
      intro f
      rw [ContinuousMap.norm_le (Work.KT.Idx.evalPull X t f) (norm_nonneg f)]
      intro x
      exact ContinuousMap.norm_coe_le_norm f (x, t)
    have hle : (Finset.univ.sup fun i : Fin N =>
          ∑ j : Fin N, ‖(RingHom.mapMatrix (Work.KT.Idx.evalPull X t) M) i j‖₊)
        ≤ (Finset.univ.sup fun i : Fin N => ∑ j : Fin N, ‖M i j‖₊) := by
      refine Finset.sup_le fun i _ => ?_
      calc ∑ j : Fin N, ‖(RingHom.mapMatrix (Work.KT.Idx.evalPull X t) M) i j‖₊
          ≤ ∑ j : Fin N, ‖M i j‖₊ := Finset.sum_le_sum fun j _ =>
              NNReal.coe_le_coe.mp (by simpa using hpt (M i j))
        _ ≤ Finset.univ.sup (fun i : Fin N => ∑ j : Fin N, ‖M i j‖₊) :=
            Finset.le_sup (f := fun i : Fin N => ∑ j : Fin N, ‖M i j‖₊) (Finset.mem_univ i)
    simp only [Matrix.linfty_opNorm_def]
    exact NNReal.coe_le_coe.mpr hle
  have hcont : ContinuousOn (fun z : ℂ => Ring.inverse (z • A + B) * A) (Metric.sphere 0 1) :=
    @continuousOn_res _ _ _ hcomp₁ A B hunit
  have key : RingHom.mapMatrix (Work.KT.Idx.evalPull X t)
        (Work.KT.Idx.matPenProj (X × unitInterval) A B) =
      Work.KT.Idx.matPenProj X (RingHom.mapMatrix (Work.KT.Idx.evalPull X t) A)
        (RingHom.mapMatrix (Work.KT.Idx.evalPull X t) B) := by
    unfold Work.KT.Idx.matPenProj
    refine @penProj_map (Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ))
        (Matrix (Fin N) (Fin N) C(X, ℂ)) Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
        hcomp₁ Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra hcomp₂
        (RingHom.mapMatrix (Work.KT.Idx.evalPull X t))
        (fun c => mapMatrix_evalPull_algebraMap X t c) hTnorm A B hunit hcont
  simpa only [RingHom.mapMatrix_apply] using key

end

end Work.Idx
