import Mathlib
import Submission.Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional
import Submission.Commons.Algebra.MvPolynomial.zonal_harmonic_pair_linDep
import Submission.Commons.Algebra.MvPolynomial.axisInv_harmonic_pair_linDep
import Submission.Commons.Algebra.MvPolynomial.exists_harmonic_homogeneous_value_one
import Submission.Commons.Algebra.MvPolynomial.axisInv_homogeneous_structure
import Submission.Commons.Analysis.MeasureTheory.continuous_integrable_sphere
import Submission.Commons.Analysis.MeasureTheory.sphere_integral_sq_pos_of_homogeneous_nz
import Submission.Commons.Analysis.MeasureTheory.sphere_linearIsometry_measurePreserving

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Commons.Analysis.MeasureTheory

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev S (n : ℕ) := Metric.sphere (0 : E n) 1

-- ============================================================
-- The harmonic homogeneous space and its L²-style bilinear form
-- ============================================================

/-- harmonic homogeneous polynomials of degree k -/
private def Hk (n k : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) where
  carrier := {P | P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0}
  zero_mem' := by
    constructor
    · exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k).zero_mem
    · simp
  add_mem' := by
    intro a b ha hb
    constructor
    · exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k).add_mem ha.1 hb.1
    · calc
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (a + b)))
            = ∑ i : Fin n, (MvPolynomial.pderiv i (MvPolynomial.pderiv i a) + MvPolynomial.pderiv i (MvPolynomial.pderiv i b)) := by simp
        _ = (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i a)) + (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i b)) := by rw [Finset.sum_add_distrib]
        _ = 0 := by rw [ha.2, hb.2]; simp
  smul_mem' := by
    intro a P hP
    constructor
    · exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k).smul_mem a hP.1
    · calc
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (a • P)))
            = ∑ i : Fin n, a • (MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) := by simp
        _ = a • (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) := by rw [Finset.smul_sum]
        _ = 0 := by rw [hP.2]; simp

private lemma Hk_le (n k : ℕ) : Hk n k ≤ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
  intro P hP
  exact hP.1

private lemma Hk_finite (n k : ℕ) : Module.Finite ℝ (Hk n k) := by
  let hom : Submodule ℝ (MvPolynomial (Fin n) ℝ) := MvPolynomial.homogeneousSubmodule (Fin n) ℝ k
  have hfin : Module.Finite ℝ hom := Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional (n := n) (k := k)
  let f : Hk n k →ₗ[ℝ] hom :=
    { toFun := fun x => ⟨x.1, Hk_le n k x.2⟩
      map_add' := by intro x y; ext; rfl
      map_smul' := by intro a x; ext; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f] using congrArg (fun z : hom => (z : MvPolynomial (Fin n) ℝ)) hxy
  exact FiniteDimensional.of_injective f hf


/-- the continuous function on the unit sphere induced by a polynomial -/
private def evalS {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : S n → ℝ :=
  fun θ => MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P

private lemma evalS_continuous {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : Continuous (evalS P) := by
  -- eval is continuous in the coordinate function; composing with θ ↦ coordinates
  have h1 : Continuous (fun f : Fin n → ℝ => MvPolynomial.eval f P) := MvPolynomial.continuous_eval P
  have h2 : Continuous (fun θ : S n => (fun i : Fin n => (θ : E n) i)) := by fun_prop
  exact h1.comp h2

private lemma evalS_add {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ) : evalS (P + Q) = evalS P + evalS Q := by
  funext θ
  simp [evalS]

private lemma evalS_mul {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ) : evalS (P * Q) = evalS P * evalS Q := by
  funext θ
  simp [evalS]

private lemma evalS_smul {n : ℕ} (a : ℝ) (P : MvPolynomial (Fin n) ℝ) : evalS (a • P) = fun θ => a * evalS P θ := by
  funext θ
  simp [evalS]

/-- surface-integral linearity for continuous functions on the sphere -/
private lemma sphere_integral_lin {n : ℕ} [Nonempty (Fin n)] (a b : ℝ) (f g : S n → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ θ : S n, (a * f θ + b * g θ) ∂MeasureTheory.volume.toSphere) =
      a * (∫ θ : S n, f θ ∂MeasureTheory.volume.toSphere) +
      b * (∫ θ : S n, g θ ∂MeasureTheory.volume.toSphere) := by
  have hfI : MeasureTheory.Integrable f MeasureTheory.volume.toSphere :=
    continuous_integrable_sphere (n := n) f hf
  have hgI : MeasureTheory.Integrable g MeasureTheory.volume.toSphere :=
    continuous_integrable_sphere (n := n) g hg
  calc
    (∫ θ : S n, (a * f θ + b * g θ) ∂MeasureTheory.volume.toSphere)
        = ∫ θ : S n, (a * f θ + b * g θ) ∂MeasureTheory.volume.toSphere := rfl
    _ = (∫ θ : S n, a * f θ ∂MeasureTheory.volume.toSphere) +
        (∫ θ : S n, b * g θ ∂MeasureTheory.volume.toSphere) := by
          rw [MeasureTheory.integral_add]
          · exact hfI.const_mul a
          · exact hgI.const_mul b
    _ = a * (∫ θ : S n, f θ ∂MeasureTheory.volume.toSphere) +
        b * (∫ θ : S n, g θ ∂MeasureTheory.volume.toSphere) := by
          rw [MeasureTheory.integral_const_mul]
          rw [MeasureTheory.integral_const_mul]

/-- the surface integral of the product of the restrictions of two harmonic
homogeneous polynomials -/
private def bilin (n k : ℕ) : Hk n k → Hk n k → ℝ := fun P Q =>
  ∫ θ : S n, evalS P.1 θ * evalS Q.1 θ ∂MeasureTheory.volume.toSphere

private lemma bilin_symm (n k : ℕ) (P Q : Hk n k) : bilin n k P Q = bilin n k Q P := by
  unfold bilin
  apply MeasureTheory.integral_congr_ae
  filter_upwards with θ
  ring

private lemma bilin_right_add (n k : ℕ) [Nonempty (Fin n)] (P Q R : Hk n k) :
    bilin n k P (Q + R) = bilin n k P Q + bilin n k P R := by
  unfold bilin
  calc
    (∫ θ : S n, evalS P.1 θ * evalS (Q + R).1 θ ∂MeasureTheory.volume.toSphere)
        = ∫ θ : S n, (evalS P.1 θ * evalS Q.1 θ + evalS P.1 θ * evalS R.1 θ)
            ∂MeasureTheory.volume.toSphere := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with θ
          simp [evalS]
          ring
    _ = (∫ θ : S n, evalS P.1 θ * evalS Q.1 θ ∂MeasureTheory.volume.toSphere) +
        (∫ θ : S n, evalS P.1 θ * evalS R.1 θ ∂MeasureTheory.volume.toSphere) := by
          -- linearity: f + g with coefficient 1
          have hf : Continuous (fun θ : S n => evalS P.1 θ * evalS Q.1 θ) :=
            (evalS_continuous P.1).mul (evalS_continuous Q.1)
          have hg : Continuous (fun θ : S n => evalS P.1 θ * evalS R.1 θ) :=
            (evalS_continuous P.1).mul (evalS_continuous R.1)
          simpa using (sphere_integral_lin (n := n) (a := 1) (b := 1)
            (f := fun θ : S n => evalS P.1 θ * evalS Q.1 θ)
            (g := fun θ : S n => evalS P.1 θ * evalS R.1 θ) hf hg)

private lemma bilin_right_smul (n k : ℕ) [Nonempty (Fin n)] (a : ℝ) (P Q : Hk n k) :
    bilin n k P (a • Q) = a * bilin n k P Q := by
  unfold bilin
  calc
    (∫ θ : S n, evalS P.1 θ * evalS (a • Q).1 θ ∂MeasureTheory.volume.toSphere)
        = ∫ θ : S n, (a * (evalS P.1 θ * evalS Q.1 θ)) ∂MeasureTheory.volume.toSphere := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with θ
          simp [evalS]
          ring
    _ = a * (∫ θ : S n, evalS P.1 θ * evalS Q.1 θ ∂MeasureTheory.volume.toSphere) := by
          have h : Continuous (fun θ : S n => evalS P.1 θ * evalS Q.1 θ) :=
            (evalS_continuous P.1).mul (evalS_continuous Q.1)
          have hI : MeasureTheory.Integrable (fun θ : S n => evalS P.1 θ * evalS Q.1 θ)
              MeasureTheory.volume.toSphere := continuous_integrable_sphere (n := n) _ h
          simpa [MeasureTheory.integral_const_mul]

private lemma bilin_left_add (n k : ℕ) [Nonempty (Fin n)] (P Q R : Hk n k) :
    bilin n k (P + Q) R = bilin n k P R + bilin n k Q R := by
  calc
    bilin n k (P + Q) R = bilin n k R (P + Q) := bilin_symm n k (P+Q) R
    _ = bilin n k R P + bilin n k R Q := bilin_right_add n k R P Q
    _ = bilin n k P R + bilin n k Q R := by rw [bilin_symm n k R P, bilin_symm n k R Q]

private lemma bilin_left_smul (n k : ℕ) [Nonempty (Fin n)] (a : ℝ) (P Q : Hk n k) :
    bilin n k (a • P) Q = a * bilin n k P Q := by
  calc
    bilin n k (a • P) Q = bilin n k Q (a • P) := bilin_symm n k (a•P) Q
    _ = a * bilin n k Q P := bilin_right_smul n k a Q P
    _ = a * bilin n k P Q := by rw [bilin_symm n k Q P]

private lemma bilin_pos {n k : ℕ} [Nonempty (Fin n)] (P : Hk n k) (hP : P ≠ 0) :
    0 < bilin n k P P := by
  have hh : P.1 ≠ 0 := by
    intro hz
    apply hP
    apply Subtype.ext
    exact hz
  have hhom : P.1 ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := P.2.1
  have hpos := sphere_integral_sq_pos_of_homogeneous_nz (n := n) (k := k) P.1 hhom hh
  unfold bilin
  convert hpos using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with θ
  simp [evalS]
  ring

/-- subtraction in the left slot -/
private lemma bilin_sub_left (n k : ℕ) [Nonempty (Fin n)] (P Q R : Hk n k) :
    bilin n k (P - Q) R = bilin n k P R - bilin n k Q R := by
  calc
    bilin n k (P - Q) R = bilin n k (P + (-Q)) R := by
          congr 1
          apply Subtype.ext
          simp [sub_eq_add_neg]
    _ = bilin n k P R + bilin n k (-Q) R := bilin_left_add n k P (-Q) R
    _ = bilin n k P R - bilin n k Q R := by
          have hneg : bilin n k (-Q) R = - bilin n k Q R := by
            rw [← neg_one_smul ℝ Q, bilin_left_smul n k (-1) Q R]
            ring
          rw [hneg]
          ring

/-- subtraction in the right slot -/
private lemma bilin_sub_right (n k : ℕ) [Nonempty (Fin n)] (P Q R : Hk n k) :
    bilin n k P (Q - R) = bilin n k P Q - bilin n k P R := by
  calc
    bilin n k P (Q - R) = bilin n k (Q - R) P := bilin_symm n k P (Q - R)
    _ = bilin n k Q P - bilin n k R P := bilin_sub_left n k Q R P
    _ = bilin n k P Q - bilin n k P R := by rw [bilin_symm n k Q P, bilin_symm n k R P]

/-- the bilinear form as a linear map into the dual -/
private noncomputable def Bflat (n k : ℕ) [Nonempty (Fin n)] : Hk n k →ₗ[ℝ] Module.Dual ℝ (Hk n k) where
  toFun := fun P =>
    { toFun := fun Q => bilin n k P Q
      map_add' := fun Q R => bilin_right_add n k P Q R
      map_smul' := fun a Q => by
        rw [bilin_right_smul n k a P Q]
        simp [smul_eq_mul] }
  map_add' := by
    intro P₁ P₂
    ext Q
    exact bilin_left_add n k P₁ P₂ Q
  map_smul' := by
    intro a P
    ext Q
    change bilin n k (a • P) Q = a • bilin n k P Q
    rw [bilin_left_smul n k a P Q]
    simp [smul_eq_mul]

private lemma Bflat_apply (n k : ℕ) [Nonempty (Fin n)] (P Q : Hk n k) :
    (Bflat n k P) Q = bilin n k P Q := rfl

private lemma Bflat_injective (n k : ℕ) [Nonempty (Fin n)] : Function.Injective (Bflat n k) := by
  intro P₁ P₂ hP
  by_contra hz
  have hPne : P₁ - P₂ ≠ 0 := by
    intro h
    apply hz
    have hv : P₁.1 - P₂.1 = 0 := by simpa using congrArg Subtype.val h
    exact Subtype.ext (sub_eq_zero.mp hv)
  have hpos : 0 < bilin n k (P₁ - P₂) (P₁ - P₂) := bilin_pos (n := n) (k := k) (P := P₁ - P₂) hPne
  have hval : bilin n k (P₁ - P₂) (P₁ - P₂) = 0 := by
    have hdiff : bilin n k P₁ (P₁ - P₂) - bilin n k P₂ (P₁ - P₂) = 0 := by
      have heq : bilin n k P₁ (P₁ - P₂) = bilin n k P₂ (P₁ - P₂) := by
        change (Bflat n k P₁) (P₁ - P₂) = (Bflat n k P₂) (P₁ - P₂)
        rw [hP]
      linarith
    calc
      bilin n k (P₁ - P₂) (P₁ - P₂) = bilin n k P₁ (P₁ - P₂) - bilin n k P₂ (P₁ - P₂) :=
        bilin_sub_left n k P₁ P₂ (P₁ - P₂)
      _ = 0 := hdiff
  linarith

/-- Riesz-style: every linear functional on `Hk` is given by the bilinear form -/
private lemma exists_rep (n k : ℕ) [Nonempty (Fin n)] (ℓ : Module.Dual ℝ (Hk n k)) :
    ∃ v : Hk n k, ∀ w : Hk n k, bilin n k v w = ℓ w := by
  haveI : Module.Finite ℝ (Hk n k) := Hk_finite n k
  let f := Bflat n k
  have hf : Function.Injective f := Bflat_injective n k
  have hfinrank : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ (Module.Dual ℝ (Hk n k)) := by
    calc
      Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ (Hk n k) := LinearMap.finrank_range_of_inj hf
      _ = Module.finrank ℝ (Module.Dual ℝ (Hk n k)) := by
            rw [Module.finrank_linearMap_self (R := ℝ) (S := ℝ) (M := Hk n k)]
  have hrange : LinearMap.range f = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa using hfinrank
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
  obtain ⟨v, hv⟩ := hsurj ℓ
  refine ⟨v, ?_⟩
  intro w
  change (Bflat n k v) w = ℓ w
  rw [hv]

/-- uniqueness of the representing vector -/
private lemma rep_unique (n k : ℕ) [Nonempty (Fin n)] {u v : Hk n k}
    (h : ∀ w : Hk n k, bilin n k u w = bilin n k v w) : u = v := by
  by_contra hz
  have hPne : u - v ≠ 0 := by
    intro hh
    apply hz
    have hv : u.1 - v.1 = 0 := by simpa using congrArg Subtype.val hh
    exact Subtype.ext (sub_eq_zero.mp hv)
  have hpos : 0 < bilin n k (u - v) (u - v) := bilin_pos (n := n) (k := k) (P := u - v) hPne
  have hval : bilin n k (u - v) (u - v) = 0 := by
    calc
      bilin n k (u - v) (u - v) = bilin n k u (u - v) - bilin n k v (u - v) :=
        bilin_sub_left n k u v (u - v)
      _ = bilin n k v (u - v) - bilin n k v (u - v) := by rw [h (u - v)]
      _ = 0 := by ring
  linarith

/-! Substitution of an orthogonal linear coordinate change into a polynomial
(pull-back along linear isometries of `EuclideanSpace ℝ (Fin n)`). -/
namespace CsSub

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def matA (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (j i : Fin n) : ℝ := (A (EuclideanSpace.single i 1)) j

lemma basis_expansion (n : ℕ) (x : E n) :
    x = ∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ) := by
  ext i
  simp [EuclideanSpace.single, Pi.single_apply]

lemma linear_map_apply_coord (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (x : E n) (j : Fin n) :
    (A x) j = ∑ i : Fin n, matA n A j i * x i := by
  have hxsum : A x = A (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) := by
    congr 1
    exact basis_expansion n x
  have hsum : A (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) =
      ∑ i : Fin n, A (x i • EuclideanSpace.single i (1 : ℝ)) := by
    rw [map_sum]
  have hcoord : (∑ i : Fin n, A (x i • EuclideanSpace.single i (1 : ℝ))) j =
      ∑ i : Fin n, (A (x i • EuclideanSpace.single i (1 : ℝ))) j := by simp
  calc
    (A x) j = (∑ i : Fin n, A (x i • EuclideanSpace.single i (1 : ℝ))) j := by rw [hxsum, hsum]
    _ = ∑ i : Fin n, matA n A j i * x i := by
          rw [hcoord]
          apply Finset.sum_congr rfl
          intro i hi
          simp [matA]
          ring

lemma inner_eq_sum (n : ℕ) (x y : E n) : inner ℝ x y = ∑ i : Fin n, x i * y i := by
  rw [PiLp.inner_apply]
  simp
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma coord_eq_inner_left (n : ℕ) (v : E n) (i : Fin n) : v i = inner ℝ (EuclideanSpace.single i (1 : ℝ)) v := by
  rw [inner_eq_sum]
  simp [EuclideanSpace.single, Pi.single_apply]

lemma coord_eq_inner_right (n : ℕ) (v : E n) (i : Fin n) : v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
  rw [inner_eq_sum]
  simp [EuclideanSpace.single, Pi.single_apply]

lemma basis_inner (n : ℕ) (j j' : Fin n) :
    inner ℝ (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single j' (1 : ℝ)) =
      if j = j' then 1 else 0 := by
  let b : OrthonormalBasis (Fin n) ℝ (E n) := EuclideanSpace.basisFun (Fin n) ℝ
  have h := orthonormal_iff_ite.mp b.orthonormal j j'
  simpa [b, EuclideanSpace.basisFun_apply] using h

/-- rows of the matrix of an isometry are orthonormal -/
lemma matA_orth (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (j j' : Fin n) :
    (∑ s : Fin n, matA n A j s * matA n A j' s) = if j = j' then 1 else 0 := by
  let b : OrthonormalBasis (Fin n) ℝ (E n) := (EuclideanSpace.basisFun (Fin n) ℝ).map A
  have hb : ∀ s : Fin n, b s = A (EuclideanSpace.single s (1 : ℝ)) := by
    intro s
    simp [b, OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply]
  have hprod : ∀ s : Fin n,
      matA n A j s * matA n A j' s =
        inner ℝ (EuclideanSpace.single j' (1 : ℝ)) (b s) *
          inner ℝ (b s) (EuclideanSpace.single j (1 : ℝ)) := by
    intro s
    rw [hb]
    have h1 : matA n A j s = inner ℝ (A (EuclideanSpace.single s (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ)) := by
      rw [matA]
      exact coord_eq_inner_right n (A (EuclideanSpace.single s (1 : ℝ))) j
    have h2 : matA n A j' s = inner ℝ (EuclideanSpace.single j' (1 : ℝ)) (A (EuclideanSpace.single s (1 : ℝ))) := by
      rw [matA]
      exact coord_eq_inner_left n (A (EuclideanSpace.single s (1 : ℝ))) j'
    rw [h1, h2]
    ring
  calc
    (∑ s : Fin n, matA n A j s * matA n A j' s)
        = ∑ s : Fin n,
            inner ℝ (EuclideanSpace.single j' (1 : ℝ)) (b s) *
              inner ℝ (b s) (EuclideanSpace.single j (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact hprod s
    _ = inner ℝ (EuclideanSpace.single j' (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
          exact OrthonormalBasis.sum_inner_mul_inner b
            (x := EuclideanSpace.single j' (1 : ℝ)) (y := EuclideanSpace.single j (1 : ℝ))
    _ = if j = j' then 1 else 0 := by
          have hbi := basis_inner n j j'
          rw [real_inner_comm] at hbi
          exact hbi

/-- substitution of a linear coordinate change -/
def substA (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.bind₁ (fun j : Fin n => ∑ i : Fin n, C (matA n A j i) * X i) P

lemma substA_add (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P Q : MvPolynomial (Fin n) ℝ) :
    substA n A (P + Q) = substA n A P + substA n A Q := by
  simp [substA]

lemma substA_smul (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (a : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    substA n A (a • P) = a • substA n A P := by
  simp [substA]

lemma substA_mul (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P Q : MvPolynomial (Fin n) ℝ) :
    substA n A (P * Q) = substA n A P * substA n A Q := by
  simp [substA]

lemma substA_one (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) : substA n A (1 : MvPolynomial (Fin n) ℝ) = 1 := by
  simp [substA]

lemma substA_X (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (i : Fin n) :
    substA n A (X i : MvPolynomial (Fin n) ℝ) = ∑ k : Fin n, C (matA n A i k) * X k := by
  rw [substA]
  exact MvPolynomial.bind₁_X_right (fun j : Fin n => ∑ k : Fin n, C (matA n A j k) * X k) i

lemma pderiv_substA_X (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (i s : Fin n) :
    MvPolynomial.pderiv s (substA n A (X i : MvPolynomial (Fin n) ℝ)) = C (matA n A i s) := by
  rw [substA_X]
  simp
  rw [Finset.sum_eq_single s]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hs
    simp at hs

/-- chain rule: pderiv of a linear substitution -/
lemma pderiv_substA (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P : MvPolynomial (Fin n) ℝ) (s : Fin n) :
    MvPolynomial.pderiv s (substA n A P) =
      ∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r =>
      simp [substA]
  | add P Q hP hQ =>
      rw [substA_add, map_add, hP, hQ]
      rw [show (∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j P)) +
              (∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j Q)) =
              ∑ j : Fin n, (C (matA n A j s) * substA n A (MvPolynomial.pderiv j P) +
                C (matA n A j s) * substA n A (MvPolynomial.pderiv j Q)) by
                rw [← Finset.sum_add_distrib]]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_add, substA_add]
      ring
  | mul_X P i hP =>
      let AP : MvPolynomial (Fin n) ℝ := substA n A P
      let S : MvPolynomial (Fin n) ℝ := substA n A (X i : MvPolynomial (Fin n) ℝ)
      have hSS : MvPolynomial.pderiv s S = C (matA n A i s) := pderiv_substA_X n A i s
      have hPQ : substA n A (P * X i) = AP * S := by
        dsimp [AP, S]
        rw [substA_mul]
      have hPP : MvPolynomial.pderiv s AP =
          ∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j P) := hP
      have hx : ∀ j : Fin n,
          MvPolynomial.pderiv j (X i : MvPolynomial (Fin n) ℝ) = if j = i then 1 else 0 := by
        intro j
        by_cases hji : j = i
        · subst i
          simp
        · simp [hji]
      have hder : ∀ j : Fin n,
          MvPolynomial.pderiv j (P * X i) =
            MvPolynomial.pderiv j P * X i + (if j = i then P else 0) := by
        intro j
        rw [MvPolynomial.pderiv_mul, hx j]
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      have hterm : ∀ j : Fin n,
          C (matA n A j s) * (substA n A (MvPolynomial.pderiv j P) * S) +
            (if j = i then C (matA n A i s) * AP else 0)
          = C (matA n A j s) * substA n A (MvPolynomial.pderiv j (P * X i)) := by
        intro j
        by_cases hji : j = i
        · subst j
          rw [hder i]
          rw [substA_add, substA_mul]
          simp [substA_one]
          ring
        · rw [hder j]
          simp only [hji, if_false]
          rw [substA_add]
          rw [show substA n A (0 : MvPolynomial (Fin n) ℝ) = 0 by simp [substA]]
          rw [substA_mul]
          dsimp [S]
          ring
      have hmerge : (∑ j : Fin n, C (matA n A j s) * (substA n A (MvPolynomial.pderiv j P) * S)) +
            C (matA n A i s) * AP
          = ∑ j : Fin n,
              (C (matA n A j s) * (substA n A (MvPolynomial.pderiv j P) * S) +
                (if j = i then C (matA n A i s) * AP else 0)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [hj]
        · intro hi
          simp at hi
      have hmain :
          (∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j P)) * S
              + AP * C (matA n A i s)
          = ∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j (P * X i)) := by
        calc
          (∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j P)) * S
              + AP * C (matA n A i s)
              = (∑ j : Fin n, (C (matA n A j s) * substA n A (MvPolynomial.pderiv j P)) * S)
                  + AP * C (matA n A i s) := by rw [Finset.sum_mul]
          _ = (∑ j : Fin n, C (matA n A j s) * (substA n A (MvPolynomial.pderiv j P) * S))
                  + AP * C (matA n A i s) := by
                congr 1
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = (∑ j : Fin n, C (matA n A j s) * (substA n A (MvPolynomial.pderiv j P) * S))
                  + C (matA n A i s) * AP := by
                rw [mul_comm AP (C (matA n A i s))]
          _ = ∑ j : Fin n,
                  (C (matA n A j s) * (substA n A (MvPolynomial.pderiv j P) * S) +
                    (if j = i then C (matA n A i s) * AP else 0)) := hmerge
          _ = ∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j (P * X i)) := by
                apply Finset.sum_congr rfl
                intro j hj
                exact hterm j
      calc
        MvPolynomial.pderiv s (substA n A (P * X i))
            = MvPolynomial.pderiv s (AP * S) := by rw [hPQ]
        _ = MvPolynomial.pderiv s AP * S + AP * MvPolynomial.pderiv s S := by
              rw [MvPolynomial.pderiv_mul]
        _ = (∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j P)) * S
              + AP * C (matA n A i s) := by rw [hPP, hSS]
        _ = ∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j (P * X i)) := hmain


/-- substitution preserves homogeneity -/
lemma substA_mem_homogeneous (n : ℕ) {k : ℕ} (A : E n ≃ₗᵢ[ℝ] E n)
    {P : MvPolynomial (Fin n) ℝ} (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :
    substA n A P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
  classical
  let f : Fin n → MvPolynomial (Fin n) ℝ := fun j => ∑ i : Fin n, C (matA n A j i) * X i
  have hsubst : substA n A P = MvPolynomial.eval₂Hom (C : ℝ →+* MvPolynomial (Fin n) ℝ) f P := by
    simp [substA, f, MvPolynomial.eval₂Hom_C_eq_bind₁]
  rw [hsubst]
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP ⊢
  have h := MvPolynomial.IsHomogeneous.eval₂ hP
    (f := (C : ℝ →+* MvPolynomial (Fin n) ℝ)) (g := f)
    (hf := by intro r; exact MvPolynomial.isHomogeneous_C (R := ℝ) (σ := Fin n) r)
    (hg := by
      intro i
      apply MvPolynomial.IsHomogeneous.sum
      intro j hj
      simpa [f] using (MvPolynomial.IsHomogeneous.C_mul (MvPolynomial.isHomogeneous_X (R := ℝ) (σ := Fin n) j) (matA n A i j)))
  change (MvPolynomial.eval₂ (C : ℝ →+* MvPolynomial (Fin n) ℝ) f P).IsHomogeneous k
  simpa using h

lemma pderiv_smul (n : ℕ) (s : Fin n) (a : ℝ) (Q : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv s (C a * Q) = C a * MvPolynomial.pderiv s Q := by
  rw [pderiv_C_mul]

lemma pderiv_sum_univ (n : ℕ) (s : Fin n) (Q : Fin n → MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv s (∑ j : Fin n, Q j) = ∑ j : Fin n, MvPolynomial.pderiv s (Q j) := by
  rw [map_sum]

lemma substA_sum (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℝ) :
    substA n A (∑ i ∈ s, f i) = ∑ i ∈ s, substA n A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [substA]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, substA_add, ih]

/-- the Laplacian commutes with orthogonal substitution -/
lemma substA_lap (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P : MvPolynomial (Fin n) ℝ) :
    (∑ s : Fin n, MvPolynomial.pderiv s (MvPolynomial.pderiv s (substA n A P))) =
      substA n A (∑ s : Fin n, MvPolynomial.pderiv s (MvPolynomial.pderiv s P)) := by
  classical
  calc
    (∑ s : Fin n, MvPolynomial.pderiv s (MvPolynomial.pderiv s (substA n A P)))
        = ∑ s : Fin n,
            MvPolynomial.pderiv s (∑ j : Fin n, C (matA n A j s) * substA n A (MvPolynomial.pderiv j P)) := by
          apply Finset.sum_congr rfl
          intro s hs
          congr 1
          exact pderiv_substA n A P s
    _ = ∑ s : Fin n,
          ∑ j : Fin n,
            C (matA n A j s) * MvPolynomial.pderiv s (substA n A (MvPolynomial.pderiv j P)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [pderiv_sum_univ]
          apply Finset.sum_congr rfl
          intro j hj
          exact pderiv_smul n s (matA n A j s) (substA n A (MvPolynomial.pderiv j P))
    _ = ∑ s : Fin n,
          ∑ j : Fin n,
            C (matA n A j s) * (∑ j' : Fin n, C (matA n A j' s) * substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P))) := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          exact pderiv_substA n A (MvPolynomial.pderiv j P) s
    _ = ∑ s : Fin n,
          ∑ j : Fin n,
            ∑ j' : Fin n,
              (C (matA n A j s) * C (matA n A j' s)) * substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)) := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j' hj'
          ring
    _ = ∑ j : Fin n, ∑ j' : Fin n,
          C (∑ s : Fin n, matA n A j s * matA n A j' s) *
            substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)) := by
          have hCsum : ∀ (x : Fin n → ℝ),
              (∑ s : Fin n, (C (x s) : MvPolynomial (Fin n) ℝ)) =
                (C (∑ s : Fin n, x s) : MvPolynomial (Fin n) ℝ) := by
            intro x
            let c : ℝ →+* MvPolynomial (Fin n) ℝ := MvPolynomial.C (R := ℝ) (σ := Fin n)
            exact (map_sum (c : ℝ →+ MvPolynomial (Fin n) ℝ) x (Finset.univ)).symm
          calc
            (∑ s : Fin n, ∑ j : Fin n, ∑ j' : Fin n,
                (C (matA n A j s) * C (matA n A j' s)) *
                  substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)))
                = ∑ j : Fin n, ∑ s : Fin n, ∑ j' : Fin n,
                    (C (matA n A j s) * C (matA n A j' s)) *
                      substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)) := by
                  rw [Finset.sum_comm]
            _ = ∑ j : Fin n, ∑ j' : Fin n, ∑ s : Fin n,
                    (C (matA n A j s) * C (matA n A j' s)) *
                      substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [Finset.sum_comm]
            _ = ∑ j : Fin n, ∑ j' : Fin n,
                  C (∑ s : Fin n, matA n A j s * matA n A j' s) *
                    substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  apply Finset.sum_congr rfl
                  intro j' hj'
                  rw [← hCsum (fun s : Fin n => matA n A j s * matA n A j' s)]
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [← map_mul]
    _ = ∑ j : Fin n, substA n A (MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) := by
          have horth : ∀ j j' : Fin n,
              C (∑ s : Fin n, matA n A j s * matA n A j' s) =
                (if j = j' then (1 : MvPolynomial (Fin n) ℝ) else 0) := by
            intro j j'
            rw [matA_orth n A j j']
            by_cases hjj : j = j'
            · simp [hjj]
            · simp [hjj]
          have hdiag_inner : ∀ j : Fin n,
              (∑ j' : Fin n,
                C (∑ s : Fin n, matA n A j s * matA n A j' s) *
                  substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)))
              = substA n A (MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) := by
            intro j
            rw [Finset.sum_eq_single j]
            · rw [horth j j]
              simp
            · intro j' _ hjj'
              rw [horth j j']
              rw [if_neg]
              · simp
              · intro h
                exact hjj' h.symm
            · intro hmem
              simp at hmem
          have hdiag : (∑ j : Fin n, ∑ j' : Fin n,
              C (∑ s : Fin n, matA n A j s * matA n A j' s) *
                substA n A (MvPolynomial.pderiv j' (MvPolynomial.pderiv j P)))
              = ∑ j : Fin n, substA n A (MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hdiag_inner j
          exact hdiag
    _ = substA n A (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) := by
          -- substA is additive over finite sums
          let F : Fin n → MvPolynomial (Fin n) ℝ := fun j => MvPolynomial.pderiv j (MvPolynomial.pderiv j P)
          have hlin : ∑ j : Fin n, substA n A (F j) = substA n A (∑ j : Fin n, F j) := by
            simpa using (substA_sum n A (Finset.univ) F).symm
          exact hlin

/-- evaluation of the substitution at a vector -/
lemma substA_eval' (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P : MvPolynomial (Fin n) ℝ) (x : E n) :
    MvPolynomial.eval (fun i : Fin n => x i) (substA n A P) =
      MvPolynomial.eval (fun i : Fin n => (A x) i) P := by
  rw [substA]
  have h := MvPolynomial.aeval_bind₁ (R := ℝ) (S := ℝ)
    (f := fun i : Fin n => x i)
    (g := fun j : Fin n => ∑ i : Fin n, C (matA n A j i) * X i) P
  rw [aeval_eq_eval] at h
  apply h.trans ?_
  apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
  funext j
  simp
  exact (linear_map_apply_coord n A x j).symm

end CsSub


/-! ## Rotation actions on the sphere and on the harmonic space -/

/-- the point map on the unit sphere induced by a linear isometry -/
private def sphMap {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) : S n → S n := fun θ =>
  ⟨L θ.1, by simpa [mem_sphere_zero_iff_norm] using (mem_sphere_zero_iff_norm.mp θ.2)⟩

private lemma sphMap_apply_val {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) (θ : S n) :
    ((sphMap L θ : S n) : E n) = L (θ : E n) := rfl

private lemma sphMap_invol_comp {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) (θ : S n) :
    sphMap L.symm (sphMap L θ) = θ := by
  apply Subtype.ext
  change (L.symm (L (θ : E n)) : E n) = (θ : E n)
  simp

private def sphEquiv {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) : S n ≃ᵐ S n where
  toFun := sphMap L
  invFun := sphMap L.symm
  left_inv θ := sphMap_invol_comp L θ
  right_inv θ := sphMap_invol_comp L.symm θ
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact L.continuous.measurable.comp measurable_subtype_coe
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact L.symm.continuous.measurable.comp measurable_subtype_coe

private lemma euclideanNontrivial (n : ℕ) [Nonempty (Fin n)] : Nontrivial (E n) := by
  classical
  let i := Classical.choice ‹Nonempty (Fin n)›
  refine ⟨⟨0, EuclideanSpace.single i (1 : ℝ), ?_⟩⟩
  intro h
  have := congrArg (fun v : E n => v i) h
  simp at this

private lemma sphEquiv_measurePreserving {n : ℕ} [Nontrivial (E n)]
    (L : E n ≃ₗᵢ[ℝ] E n) :
    MeasureTheory.MeasurePreserving (⇑(sphEquiv L))
      MeasureTheory.volume.toSphere MeasureTheory.volume.toSphere := by
  have h := sphere_linearIsometry_measurePreserving (V := E n) (f := L)
  have hfun' : (⇑(sphEquiv L)) =
      (fun θ : Metric.sphere (0 : E n) 1 =>
        (⟨L θ.1, by simpa [mem_sphere_zero_iff_norm] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : E n) 1)) := by
    funext θ
    apply Subtype.ext
    rfl
  rw [hfun']
  exact h

/-- integrals on the sphere are invariant under the map induced by a linear isometry -/
private lemma sphere_integral_comp_isometry {n : ℕ} [Nontrivial (E n)]
    (L : E n ≃ₗᵢ[ℝ] E n) (g : S n → ℝ) :
    (∫ θ : S n, g (sphMap L θ) ∂MeasureTheory.volume.toSphere) =
      ∫ θ : S n, g θ ∂MeasureTheory.volume.toSphere := by
  have h := MeasureTheory.MeasurePreserving.integral_comp' (f := sphEquiv L)
    (sphEquiv_measurePreserving L) g
  have hfun : (fun θ : S n => g (sphMap L θ)) = (fun x : S n => g ((sphEquiv L) x)) := by
    funext x
    rfl
  calc
    (∫ θ : S n, g (sphMap L θ) ∂MeasureTheory.volume.toSphere)
        = (∫ x : S n, g ((sphEquiv L) x) ∂MeasureTheory.volume.toSphere) := by
          rw [hfun]
    _ = (∫ y : S n, g y ∂MeasureTheory.volume.toSphere) := h

private def pull {n k : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) (P : Hk n k) : Hk n k :=
  ⟨CsSub.substA n L P.1, by
    constructor
    · exact CsSub.substA_mem_homogeneous n L P.2.1
    · have hlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P.1)) = 0 := P.2.2
      rw [CsSub.substA_lap]
      rw [hlap]
      simp [CsSub.substA]⟩

private lemma pull_apply_eval {n k : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) (P : Hk n k) (x : E n) :
    MvPolynomial.eval (fun i : Fin n => x i) (pull L P).1 =
      MvPolynomial.eval (fun i : Fin n => (L x) i) P.1 := by
  exact CsSub.substA_eval' n L P.1 x

private lemma bilin_pull {n k : ℕ} [Nonempty (Fin n)] (L : E n ≃ₗᵢ[ℝ] E n) (P Q : Hk n k) :
    bilin n k (pull L P) Q = bilin n k P (pull L.symm Q) := by
  letI : Nontrivial (E n) := euclideanNontrivial n
  -- pointwise: the pull-back of P evaluated at θ equals P evaluated at Lθ
  have hpoint : ∀ θ : S n, evalS (pull L P).1 θ = evalS P.1 (sphMap L θ) := by
    intro θ
    change MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (pull L P).1 =
      MvPolynomial.eval (fun i : Fin n => (L (θ : E n)) i) P.1
    rw [pull_apply_eval]
  -- pointwise: Q evaluated at (L⁻¹θ) equals the pull-back of Q evaluated at θ
  have hpointQ : ∀ θ : S n, evalS Q.1 (sphMap L.symm θ) = evalS (pull L.symm Q).1 θ := by
    intro θ
    change MvPolynomial.eval (fun i : Fin n => (L.symm (θ : E n)) i) Q.1 =
      MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (pull L.symm Q).1
    rw [pull_apply_eval]
  unfold bilin
  let g : S n → ℝ := fun η => evalS P.1 η * evalS Q.1 (sphMap L.symm η)
  have hcomp : (∫ θ : S n, g (sphMap L θ) ∂MeasureTheory.volume.toSphere) =
      (∫ η : S n, g η ∂MeasureTheory.volume.toSphere) := by
    have hc := MeasureTheory.MeasurePreserving.integral_comp' (f := sphEquiv L)
      (sphEquiv_measurePreserving L) g
    have hfun : (fun θ : S n => g (sphMap L θ)) = (fun x : S n => g ((sphEquiv L) x)) := by
      funext x
      rfl
    calc
      (∫ θ : S n, g (sphMap L θ) ∂MeasureTheory.volume.toSphere)
          = (∫ x : S n, g ((sphEquiv L) x) ∂MeasureTheory.volume.toSphere) := by
            rw [hfun]
      _ = (∫ η : S n, g η ∂MeasureTheory.volume.toSphere) := hc
  calc
    (∫ θ : S n, evalS (pull L P).1 θ * evalS Q.1 θ ∂MeasureTheory.volume.toSphere)
        = (∫ θ : S n, evalS P.1 (sphMap L θ) * evalS Q.1 θ
            ∂MeasureTheory.volume.toSphere) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with θ
          rw [hpoint θ]
    _ = (∫ θ : S n, g (sphMap L θ) ∂MeasureTheory.volume.toSphere) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with θ
          dsimp [g]
          congr 1
          rw [sphMap_invol_comp L θ]
    _ = (∫ η : S n, g η ∂MeasureTheory.volume.toSphere) := hcomp
    _ = (∫ θ : S n, evalS P.1 θ * evalS (pull L.symm Q).1 θ
          ∂MeasureTheory.volume.toSphere) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with θ
          dsimp [g]
          congr 1
          rw [hpointQ θ]

/-! ## The two linear functionals on `Hk` -/

/-- the first basis vector -/
private noncomputable def e0vec (n : ℕ) [NeZero n] : E n := EuclideanSpace.single (0 : Fin n) (1 : ℝ)

private lemma abs_inner_e0_cont {n : ℕ} [NeZero n] :
    Continuous (fun θ : S n => |inner ℝ (e0vec n) ((θ : E n))|) := by
  fun_prop

/-- evaluation at the first basis vector -/
private noncomputable def Eval (n k : ℕ) [NeZero n] : Hk n k →ₗ[ℝ] ℝ where
  toFun P := MvPolynomial.eval (fun i : Fin n => (e0vec n) i) P.1
  map_add' := by intro P Q; simp
  map_smul' := by intro a P; simp

/-- the cosine integral functional: `P ↦ ∫ |⟨e₀, θ⟩| · P(θ) dσ` -/
private noncomputable def Lambda (n k : ℕ) [NeZero n] : Hk n k →ₗ[ℝ] ℝ where
  toFun P := ∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ
    ∂MeasureTheory.volume.toSphere
  map_add' := by
    intro P Q
    calc
      (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS (P + Q).1 θ
          ∂MeasureTheory.volume.toSphere)
          = ∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * (evalS P.1 θ + evalS Q.1 θ)
              ∂MeasureTheory.volume.toSphere := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with θ
                rw [show evalS (P + Q).1 θ = evalS P.1 θ + evalS Q.1 θ by simp [evalS]]
      _ = ∫ θ : S n, (1 * (|inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ) +
          1 * (|inner ℝ (e0vec n) ((θ : E n))| * evalS Q.1 θ))
          ∂MeasureTheory.volume.toSphere := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with θ
                ring
      _ = (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ
            ∂MeasureTheory.volume.toSphere) +
          (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS Q.1 θ
            ∂MeasureTheory.volume.toSphere) := by
                have hPc : Continuous (fun θ : S n => |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ) :=
                  (abs_inner_e0_cont.mul (evalS_continuous P.1))
                have hQc : Continuous (fun θ : S n => |inner ℝ (e0vec n) ((θ : E n))| * evalS Q.1 θ) :=
                  (abs_inner_e0_cont.mul (evalS_continuous Q.1))
                simpa using (sphere_integral_lin (n := n) (a := 1) (b := 1)
                  (f := fun θ : S n => |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ)
                  (g := fun θ : S n => |inner ℝ (e0vec n) ((θ : E n))| * evalS Q.1 θ) hPc hQc)
  map_smul' := by
    intro a P
    calc
      (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS (a • P).1 θ
          ∂MeasureTheory.volume.toSphere)
          = ∫ θ : S n, a * (|inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ)
              ∂MeasureTheory.volume.toSphere := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with θ
                simp [evalS]
                ring
      _ = a * (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ
            ∂MeasureTheory.volume.toSphere) := by
                have hPc : Continuous (fun θ : S n => |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ) :=
                  (abs_inner_e0_cont.mul (evalS_continuous P.1))
                have hI : MeasureTheory.Integrable
                    (fun θ : S n => |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ)
                    MeasureTheory.volume.toSphere := continuous_integrable_sphere (n := n) _ hPc
                rw [MeasureTheory.integral_const_mul]


/-- an isometry fixing the axis does not change the inner product with the axis vector -/
private lemma axis_inner_inv {n : ℕ} [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hL : L (e0vec n) = e0vec n) (v : E n) :
    inner ℝ (e0vec n) (L.symm v) = inner ℝ (e0vec n) v := by
  have hmm := LinearIsometryEquiv.inner_map_map L (e0vec n) (L.symm v)
  calc
    inner ℝ (e0vec n) (L.symm v) = inner ℝ (L (e0vec n)) v := by
          simpa using hmm.symm
    _ = inner ℝ (e0vec n) v := by rw [hL]

/-- evaluation at the axis point is invariant under pull-backs by axis-fixing isometries -/
private lemma Eval_pull {n k : ℕ} [Nonempty (Fin n)] [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hL : L (e0vec n) = e0vec n) (P : Hk n k) : (Eval n k) (pull L P) = (Eval n k) P := by
  unfold Eval
  have h1 : MvPolynomial.eval (fun i : Fin n => (e0vec n) i) (pull L P).1 =
      MvPolynomial.eval (fun i : Fin n => (L (e0vec n)) i) P.1 := by
    exact pull_apply_eval L P (e0vec n)
  change MvPolynomial.eval (fun i : Fin n => (e0vec n) i) (pull L P).1 =
    MvPolynomial.eval (fun i : Fin n => (e0vec n) i) P.1
  rw [h1, hL]

/-- the cosine integral is invariant under pull-backs by axis-fixing isometries -/
private lemma Lambda_pull {n k : ℕ} [Nonempty (Fin n)] [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hL : L (e0vec n) = e0vec n) (P : Hk n k) : (Lambda n k) (pull L P) = (Lambda n k) P := by
  letI : Nontrivial (E n) := euclideanNontrivial n
  unfold Lambda
  let f : S n → ℝ := fun η => |inner ℝ (e0vec n) ((sphMap L.symm η : S n) : E n)| * evalS P.1 η
  have h1 : (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS (pull L P).1 θ
        ∂MeasureTheory.volume.toSphere)
      = ∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 (sphMap L θ)
          ∂MeasureTheory.volume.toSphere := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        congr 1
        change MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (pull L P).1 =
          MvPolynomial.eval (fun i : Fin n => ((sphMap L θ : S n) : E n) i) P.1
        rw [pull_apply_eval L P (θ : E n)]
        apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g P.1)
        funext i
        rfl
  have h2 : (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 (sphMap L θ)
        ∂MeasureTheory.volume.toSphere)
      = ∫ η : S n, f η ∂MeasureTheory.volume.toSphere := by
        have hc := sphere_integral_comp_isometry L f
        -- hc : (∫ θ, f (sphMap L θ)) = (∫ η, f η)
        calc
          (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 (sphMap L θ)
              ∂MeasureTheory.volume.toSphere)
              = (∫ θ : S n, f (sphMap L θ) ∂MeasureTheory.volume.toSphere) := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with θ
                dsimp [f]
                congr 1
                rw [sphMap_invol_comp L θ]
          _ = ∫ η : S n, f η ∂MeasureTheory.volume.toSphere := hc
  have h3 : (∫ η : S n, f η ∂MeasureTheory.volume.toSphere)
      = ∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ
          ∂MeasureTheory.volume.toSphere := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        dsimp [f]
        have hin : |inner ℝ (e0vec n) (L.symm (θ : E n))| = |inner ℝ (e0vec n) (θ : E n)| := by
          rw [axis_inner_inv L hL (θ : E n)]
        change |inner ℝ (e0vec n) (L.symm (θ : E n))| * evalS P.1 θ =
          |inner ℝ (e0vec n) (θ : E n)| * evalS P.1 θ
        rw [hin]
  calc
    (∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS (pull L P).1 θ
          ∂MeasureTheory.volume.toSphere)
        = ∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 (sphMap L θ)
            ∂MeasureTheory.volume.toSphere := h1
    _ = ∫ η : S n, f η ∂MeasureTheory.volume.toSphere := h2
    _ = ∫ θ : S n, |inner ℝ (e0vec n) ((θ : E n))| * evalS P.1 θ
          ∂MeasureTheory.volume.toSphere := h3

/-- the representing vector of evaluation -/
private noncomputable def vEval (n k : ℕ) [Nonempty (Fin n)] [NeZero n] : Hk n k :=
  Classical.choose (exists_rep n k (Eval n k))

private lemma vEval_rep {n k : ℕ} [Nonempty (Fin n)] [NeZero n] (w : Hk n k) :
    bilin n k (vEval n k) w = (Eval n k) w :=
  Classical.choose_spec (exists_rep n k (Eval n k)) w

/-- the representing vector of the cosine integral -/
private noncomputable def vLambda (n k : ℕ) [Nonempty (Fin n)] [NeZero n] : Hk n k :=
  Classical.choose (exists_rep n k (Lambda n k))

private lemma vLambda_rep {n k : ℕ} [Nonempty (Fin n)] [NeZero n] (w : Hk n k) :
    bilin n k (vLambda n k) w = (Lambda n k) w :=
  Classical.choose_spec (exists_rep n k (Lambda n k)) w

/-- the representative of evaluation is fixed by all axis-fixing isometries -/
private lemma vEval_axisInv {n k : ℕ} [Nonempty (Fin n)] [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hL : L (e0vec n) = e0vec n) : pull L (vEval n k) = vEval n k := by
  apply rep_unique (n := n) (k := k)
  intro w
  calc
    bilin n k (pull L (vEval n k)) w = bilin n k (vEval n k) (pull L.symm w) :=
      bilin_pull (n := n) (k := k) L (vEval n k) w
    _ = (Eval n k) (pull L.symm w) := vEval_rep (pull L.symm w)
    _ = (Eval n k) w := Eval_pull L.symm (by
          -- L.symm fixes the axis too
          calc
            L.symm (e0vec n) = L.symm (L (e0vec n)) := by rw [hL]
            _ = e0vec n := by simp) w
    _ = bilin n k (vEval n k) w := (vEval_rep w).symm

/-- the representative of the cosine integral is fixed by all axis-fixing isometries -/
private lemma vLambda_axisInv {n k : ℕ} [Nonempty (Fin n)] [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hL : L (e0vec n) = e0vec n) : pull L (vLambda n k) = vLambda n k := by
  apply rep_unique (n := n) (k := k)
  intro w
  calc
    bilin n k (pull L (vLambda n k)) w = bilin n k (vLambda n k) (pull L.symm w) :=
      bilin_pull (n := n) (k := k) L (vLambda n k) w
    _ = (Lambda n k) (pull L.symm w) := vLambda_rep (pull L.symm w)
    _ = (Lambda n k) w := Lambda_pull L.symm (by
          calc
            L.symm (e0vec n) = L.symm (L (e0vec n)) := by rw [hL]
            _ = e0vec n := by simp) w
    _ = bilin n k (vLambda n k) w := (vLambda_rep w).symm

private lemma vEval_axisInv_eval {n k : ℕ} [Nonempty (Fin n)] [NeZero n]
    (L : E n ≃ₗᵢ[ℝ] E n) (hL : L (e0vec n) = e0vec n) (x : E n) :
    MvPolynomial.eval (fun i : Fin n => (L x) i) (vEval n k).1 =
      MvPolynomial.eval (fun i : Fin n => x i) (vEval n k).1 := by
  have hfix : pull L (vEval n k) = vEval n k := vEval_axisInv (n := n) (k := k) L hL
  have hpfx : (pull L (vEval n k)).1 = (vEval n k).1 := congrArg Subtype.val hfix
  have hval := pull_apply_eval L (vEval n k) x
  calc
    MvPolynomial.eval (fun i : Fin n => (L x) i) (vEval n k).1
        = MvPolynomial.eval (fun i : Fin n => x i) (pull L (vEval n k)).1 := hval.symm
    _ = MvPolynomial.eval (fun i : Fin n => x i) (vEval n k).1 := by rw [hpfx]

private lemma vLambda_axisInv_eval {n k : ℕ} [Nonempty (Fin n)] [NeZero n]
    (L : E n ≃ₗᵢ[ℝ] E n) (hL : L (e0vec n) = e0vec n) (x : E n) :
    MvPolynomial.eval (fun i : Fin n => (L x) i) (vLambda n k).1 =
      MvPolynomial.eval (fun i : Fin n => x i) (vLambda n k).1 := by
  have hfix : pull L (vLambda n k) = vLambda n k := vLambda_axisInv (n := n) (k := k) L hL
  have hpfx : (pull L (vLambda n k)).1 = (vLambda n k).1 := congrArg Subtype.val hfix
  have hval := pull_apply_eval L (vLambda n k) x
  calc
    MvPolynomial.eval (fun i : Fin n => (L x) i) (vLambda n k).1
        = MvPolynomial.eval (fun i : Fin n => x i) (pull L (vLambda n k)).1 := hval.symm
    _ = MvPolynomial.eval (fun i : Fin n => x i) (vLambda n k).1 := by rw [hpfx]

/-- the representative of evaluation is non-zero (evaluation does not vanish on `Hk`) -/
private lemma vEval_ne_zero {n k : ℕ} [Nonempty (Fin n)] [NeZero n] (hn2 : 2 ≤ n) :
    vEval n k ≠ 0 := by
  intro hz
  obtain ⟨P0, hP0h, hP0lap, hP0val⟩ :=
    Commons.Algebra.MvPolynomial.exists_harmonic_homogeneous_value_one (n := n) (k := k) hn2
  let elem0 : Hk n k := ⟨P0, hP0h, hP0lap⟩
  have hE0 : (Eval n k) elem0 = 0 := by
    calc
      (Eval n k) elem0 = bilin n k (vEval n k) elem0 := (vEval_rep elem0).symm
      _ = bilin n k 0 elem0 := by rw [hz]
      _ = 0 := by simp [bilin, evalS]
  have hE1 : (Eval n k) elem0 = 1 := by
    change MvPolynomial.eval (fun i : Fin n => (e0vec n) i) P0 = 1
    simpa [e0vec] using hP0val
  linarith

theorem harmonic_cosine_integral_axis_scalar
    {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    ∃ c : ℝ, ∀ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 →
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) (θ : EuclideanSpace ℝ (Fin n))| *
            MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
        ∂MeasureTheory.volume.toSphere) =
      c * MvPolynomial.eval (fun i : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) i) P := by
  classical
  letI : Nonempty (Fin n) := ⟨(0 : Fin n)⟩
  have hvE_ne : vEval n k ≠ 0 := vEval_ne_zero (n := n) (k := k) hn2
  -- the two representatives are axis-invariant harmonic homogeneous polynomials of degree k
  obtain ⟨a, b, hab, hlin⟩ := Commons.Algebra.MvPolynomial.axisInv_harmonic_pair_linDep (n := n) (k := k) hn2
    (vLambda n k).1 (vEval n k).1 (vLambda n k).2.1 (vEval n k).2.1 (vLambda n k).2.2 (vEval n k).2.2
    (vLambda_axisInv_eval (n := n) (k := k)) (vEval_axisInv_eval (n := n) (k := k))
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hb_ne : b ≠ 0 := hab.resolve_left (by intro h; exact h ha0)
    have hlin0 : b • (vEval n k).1 = 0 := by
      have htmp := hlin
      rw [ha0] at htmp
      simpa using htmp
    have hb_or : b = 0 ∨ (vEval n k).1 = 0 := smul_eq_zero.mp hlin0
    rcases hb_or with hb0 | hv0
    · exact False.elim (hb_ne hb0)
    · have : vEval n k = 0 := by
        apply Subtype.ext
        exact hv0
      exact False.elim (hvE_ne this)
  let c : ℝ := a⁻¹ * (-b)
  have hv : (vLambda n k).1 = c • (vEval n k).1 := by
    have h1 : a • (vLambda n k).1 = - (b • (vEval n k).1) := eq_neg_of_add_eq_zero_left hlin
    have hback : (a⁻¹ • (a • (vLambda n k).1)) = (vLambda n k).1 := by
      rw [smul_smul]
      rw [inv_mul_cancel₀ ha_ne]
      simp
    calc
      (vLambda n k).1 = a⁻¹ • (a • (vLambda n k).1) := hback.symm
      _ = a⁻¹ • (-(b • (vEval n k).1)) := by rw [h1]
      _ = (a⁻¹ * (-b)) • (vEval n k).1 := by
            rw [show -(b • (vEval n k).1) = (-b) • (vEval n k).1 by simp [neg_smul]]
            rw [smul_smul]
      _ = c • (vEval n k).1 := by rfl
  have hvH : vLambda n k = c • vEval n k := by
    apply Subtype.ext
    simpa using hv
  have hfunc : ∀ w : Hk n k, (Lambda n k) w = c * (Eval n k) w := by
    intro w
    calc
      (Lambda n k) w = bilin n k (vLambda n k) w := (vLambda_rep w).symm
      _ = bilin n k (c • vEval n k) w := by rw [hvH]
      _ = c * bilin n k (vEval n k) w := bilin_left_smul n k c (vEval n k) w
      _ = c * (Eval n k) w := by rw [vEval_rep w]
  refine ⟨c, ?_⟩
  intro P hP hlap
  let elem : Hk n k := ⟨P, hP, hlap⟩
  have hmain := hfunc elem
  calc
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) (θ : EuclideanSpace ℝ (Fin n))| *
          MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
      ∂MeasureTheory.volume.toSphere)
        = (Lambda n k) elem := by
          dsimp [elem]
          rfl
    _ = c * (Eval n k) elem := hmain
    _ = c * MvPolynomial.eval (fun i : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) i) P := by
          dsimp [elem]
          rfl

end Commons.Analysis.MeasureTheory
