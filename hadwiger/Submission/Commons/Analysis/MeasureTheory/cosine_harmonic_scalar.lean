import Mathlib
import Submission.Commons.Analysis.MvPolynomial.coeff_odd_of_flip_invariant
import Submission.Commons.Analysis.MvPolynomial.eval_two_var_even
import Submission.Commons.Analysis.MvPolynomial.eval_sum_sq_erase
import Submission.Commons.Analysis.InnerProductSpace.axis_isometry_coord0
import Submission.Commons.Analysis.InnerProductSpace.axis_isometry_preserves_compl_norm
import Submission.Commons.Analysis.InnerProductSpace.compl_norm_sq_eq
import Submission.Commons.Analysis.InnerProductSpace.erase_sum_sq_eq_if
import Submission.Commons.Analysis.MeasureTheory.cosine_rotate
import Submission.Commons.Analysis.MeasureTheory.cosine_harmonic_scalar_fin_one
import Submission.Commons.Analysis.MeasureTheory.harmonic_cosine_integral_axis_scalar
import Submission.Commons.Analysis.MeasureTheory.continuous_integrable_sphere
import Submission.Commons.Analysis.MeasureTheory.sphere_linearIsometry_measurePreserving

noncomputable section
open scoped BigOperators Classical
open MvPolynomial MeasureTheory


noncomputable section
open scoped BigOperators

namespace Fh1

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma inner_ww_ne_zero (n : ℕ) (w : E n) (hw : w ≠ 0) : inner ℝ w w ≠ 0 := by
  have h : 0 < inner ℝ w w := (real_inner_self_pos).mpr hw
  exact ne_of_gt h

lemma star_apply (a : ℝ) : (starRingEnd ℝ) a = a := rfl

/-- reflection in the hyperplane orthogonal to w (w ≠ 0), as a linear map -/
def reflMap (n : ℕ) (w : E n) (hw : w ≠ 0) : E n →ₗ[ℝ] E n where
  toFun x := x - ((2 * inner ℝ x w) / inner ℝ w w) • w
  map_add' x y := by
    let d : ℝ := inner ℝ w w
    have hd : d ≠ 0 := inner_ww_ne_zero n w hw
    change (x + y) - ((2 * inner ℝ (x + y) w) / d) • w =
        (x - ((2 * inner ℝ x w) / d) • w) + (y - ((2 * inner ℝ y w) / d) • w)
    rw [inner_add_left]
    have hscalar : 2 * (inner ℝ x w + inner ℝ y w) / d =
        2 * inner ℝ x w / d + 2 * inner ℝ y w / d := by ring
    rw [hscalar, add_smul]
    abel
  map_smul' a x := by
    let d : ℝ := inner ℝ w w
    have hd : d ≠ 0 := inner_ww_ne_zero n w hw
    change (a • x) - ((2 * inner ℝ (a • x) w) / d) • w = a • (x - ((2 * inner ℝ x w) / d) • w)
    rw [inner_smul_left]
    simp only [star_apply]
    have hscalar : 2 * (a * inner ℝ x w) / d = a * (2 * inner ℝ x w / d) := by ring
    rw [hscalar]
    conv_rhs => rw [smul_sub]
    rw [← smul_smul]

lemma reflMap_apply (n : ℕ) (w : E n) (hw : w ≠ 0) (x : E n) :
    reflMap n w hw x = x - ((2 * inner ℝ x w) / inner ℝ w w) • w := rfl

lemma reflMap_inner (n : ℕ) (w : E n) (hw : w ≠ 0) (x : E n) :
    inner ℝ (reflMap n w hw x) w = - inner ℝ x w := by
  rw [reflMap_apply]
  let d : ℝ := inner ℝ w w
  have hd : d ≠ 0 := inner_ww_ne_zero n w hw
  calc
    inner ℝ (x - ((2 * inner ℝ x w) / d) • w) w
        = inner ℝ x w - inner ℝ (((2 * inner ℝ x w) / d) • w) w := by
          rw [inner_sub_left]
    _ = inner ℝ x w - ((2 * inner ℝ x w) / d) * inner ℝ w w := by
          rw [inner_smul_left]
          simp only [star_apply]
    _ = - inner ℝ x w := by
          simp [d]
          field_simp [hd]
          ring

lemma reflMap_involutive (n : ℕ) (w : E n) (hw : w ≠ 0) (x : E n) :
    reflMap n w hw (reflMap n w hw x) = x := by
  rw [reflMap_apply]
  rw [reflMap_apply]
  let d : ℝ := inner ℝ w w
  have hd : d ≠ 0 := inner_ww_ne_zero n w hw
  have hinner : inner ℝ (x - ((2 * inner ℝ x w) / d) • w) w = - inner ℝ x w := by
    calc
      inner ℝ (x - ((2 * inner ℝ x w) / d) • w) w
          = inner ℝ x w - inner ℝ (((2 * inner ℝ x w) / d) • w) w := by rw [inner_sub_left]
      _ = inner ℝ x w - ((2 * inner ℝ x w) / d) * inner ℝ w w := by
            rw [inner_smul_left]
            simp only [star_apply]
      _ = - inner ℝ x w := by
            simp [d]
            field_simp [hd]
            ring
  have hs : (2 * -inner ℝ x w / d) = -(2 * inner ℝ x w / d) := by ring
  have hneg : (2 * -inner ℝ x w / d) • w = -(((2 * inner ℝ x w) / d) • w) := by
    rw [hs]
    rw [neg_smul]
  calc
    x - ((2 * inner ℝ x w) / d) • w - ((2 * inner ℝ (x - ((2 * inner ℝ x w) / d) • w) w) / d) • w
        = x - ((2 * inner ℝ x w) / d) • w - ((2 * (-(inner ℝ x w))) / d) • w := by
          congr 1
          rw [hinner]
    _ = x - ((2 * inner ℝ x w) / d) • w + (((2 * inner ℝ x w) / d) • w) := by
          rw [hneg]
          abel
    _ = x := by
          simp

lemma inner_reflMap_reflMap (n : ℕ) (w : E n) (hw : w ≠ 0) (x y : E n) :
    inner ℝ (reflMap n w hw x) (reflMap n w hw y) = inner ℝ x y := by
  rw [reflMap_apply, reflMap_apply]
  let a := (2 * inner ℝ x w) / inner ℝ w w
  let b := (2 * inner ℝ y w) / inner ℝ w w
  have hsq : inner ℝ w w ≠ 0 := inner_ww_ne_zero n w hw
  have h1 : inner ℝ x (y - b • w) = inner ℝ x y - b * inner ℝ x w := by
    rw [inner_sub_right, inner_smul_right]

  have h2a : inner ℝ (a • w) (b • w) = a * b * inner ℝ w w := by
    rw [inner_smul_right, inner_smul_left]
    simp only [star_apply]
    ring
  have h2 : inner ℝ (a • w) (y - b • w) = a * inner ℝ w y - a * b * inner ℝ w w := by
    rw [inner_sub_right, inner_smul_left]
    simp only [star_apply]
    rw [h2a]
  calc
    inner ℝ (x - a • w) (y - b • w)
        = inner ℝ x (y - b • w) - inner ℝ (a • w) (y - b • w) := by
          rw [inner_sub_left]
    _ = (inner ℝ x y - b * inner ℝ x w) - (a * inner ℝ w y - a * b * inner ℝ w w) := by
          rw [h1, h2]
    _ = inner ℝ x y := by
          have huvc : inner ℝ w y = inner ℝ y w := real_inner_comm (x := y) (y := w)
          dsimp [a, b]
          rw [huvc]
          field_simp [hsq]
          ring

/-- reflection is a linear isometry equivalence (self-inverse). -/
def reflIsom (n : ℕ) (w : E n) (hw : w ≠ 0) : E n ≃ₗᵢ[ℝ] E n := by
  refine LinearIsometryEquiv.ofLinearIsometry ?f ?g ?h1 ?h2
  · refine LinearIsometry.mk (reflMap n w hw) ?_
    intro x
    have hsq : ‖reflMap n w hw x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (x := reflMap n w hw x)]
      rw [inner_reflMap_reflMap n w hw x x]
      exact (real_inner_self_eq_norm_sq (x := x))
    have hx : 0 ≤ ‖reflMap n w hw x‖ := norm_nonneg _
    have hy : 0 ≤ ‖x‖ := norm_nonneg _
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).elim (fun h => h) (fun h => by nlinarith)
  · exact (reflMap n w hw)
  · apply LinearMap.ext
    intro x
    simpa using reflMap_involutive n w hw x
  · apply LinearMap.ext
    intro x
    simpa using reflMap_involutive n w hw x

/-- The bisector reflection maps unit vector `u` to unit vector `v`. -/
lemma reflIsom_map (n : ℕ) (u v : E n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) :
    (reflIsom n (u - v) (sub_ne_zero.mpr huv)) u = v := by
  change reflMap n (u - v) (sub_ne_zero.mpr huv) u = v
  rw [reflMap_apply]
  have hsq : inner ℝ (u - v) (u - v) ≠ 0 := inner_ww_ne_zero n (u - v) (sub_ne_zero.mpr huv)
  have h1 : inner ℝ u (u - v) = inner ℝ u u - inner ℝ u v := by rw [inner_sub_right]
  have h2 : inner ℝ v (u - v) = inner ℝ v u - inner ℝ v v := by rw [inner_sub_right]
  have hin : inner ℝ (u - v) (u - v) = 2 * inner ℝ u (u - v) := by
    calc
      inner ℝ (u - v) (u - v) = inner ℝ u (u - v) - inner ℝ v (u - v) := by
            rw [inner_sub_left]
      _ = (inner ℝ u u - inner ℝ u v) - (inner ℝ v u - inner ℝ v v) := by rw [h1, h2]
      _ = 2 * (inner ℝ u u - inner ℝ u v) := by
            have huvc : inner ℝ v u = inner ℝ u v := real_inner_comm (x := u) (y := v)
            have huu : inner ℝ u u = 1 := by
              rw [real_inner_self_eq_norm_sq, hu]
              norm_num
            have hvv : inner ℝ v v = 1 := by
              rw [real_inner_self_eq_norm_sq, hv]
              norm_num
            rw [huvc, huu, hvv]
            ring
      _ = 2 * inner ℝ u (u - v) := by
            rw [h1]
  have hcoef : (2 * inner ℝ u (u - v)) / inner ℝ (u - v) (u - v) = 1 := by
    field_simp [hsq]
    rw [hin]
  rw [hcoef]
  simp

/-- For any two unit vectors there is a linear isometry mapping `u` to `v`. -/
lemma exists_isometry_unit {n : ℕ} (u v : E n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ L : E n ≃ₗᵢ[ℝ] E n, L u = v := by
  by_cases huv : u = v
  · refine ⟨LinearIsometryEquiv.refl ℝ (E n), ?_⟩
    simpa [huv]
  · refine ⟨reflIsom n (u - v) (sub_ne_zero.mpr huv), reflIsom_map n u v hu hv huv⟩

end Fh1


noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Fh2

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

end Fh2


noncomputable section
open scoped BigOperators
open MvPolynomial

namespace FhCHS

open Fh1 Fh2

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def axisVec (n : ℕ) [NeZero n] : E n := EuclideanSpace.single (0 : Fin n) (1 : ℝ)

/-- slice-coordinate index (1 : Fin n) -/
def cIdx (n : ℕ) (hn2 : 2 ≤ n) : Fin n := ⟨1, by omega⟩

def cvec (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) : E n := EuclideanSpace.single (cIdx n hn2) (1 : ℝ)

lemma cvec_eq (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) :
    cvec n hn2 = EuclideanSpace.single (cIdx n hn2) (1 : ℝ) := rfl

/-- the slice coordinate has index 1, distinct from 0 when n ≥ 2 -/
lemma cIdx_ne_zero (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) : cIdx n hn2 ≠ (0 : Fin n) := by
  intro h
  have : (1 : ℕ) = 0 := congrArg (fun i : Fin n => (i : ℕ)) h
  norm_num at this

def AxisInv (n : ℕ) [NeZero n] (P : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ L : E n ≃ₗᵢ[ℝ] E n, L (axisVec n) = axisVec n → Fh2.substA n L P = P

def R2m (n : ℕ) [NeZero n] : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.univ.erase (0 : Fin n), (X i : MvPolynomial (Fin n) ℝ) ^ 2

lemma single_ne_zero (n : ℕ) [NeZero n] (i : Fin n) : EuclideanSpace.single i (1 : ℝ) ≠ 0 := by
  intro hz
  have h := congrArg (fun v : E n => v i) hz
  simp [EuclideanSpace.single, Pi.single_apply] at h

/-- sign flip of the coordinate i (reflection through the hyperplane ⟂ e_i) -/
def flipIsom (n : ℕ) [NeZero n] (i : Fin n) : E n ≃ₗᵢ[ℝ] E n :=
  Fh1.reflIsom n (EuclideanSpace.single i (1 : ℝ)) (single_ne_zero n i)

lemma refl_fix_axis (n : ℕ) [NeZero n] (w : E n) (hw : w ≠ 0) (hw0 : w (0 : Fin n) = 0) :
    Fh1.reflIsom n w hw (axisVec n) = axisVec n := by
  change Fh1.reflMap n w hw (axisVec n) = axisVec n
  rw [Fh1.reflMap_apply]
  have hin : inner ℝ (axisVec n) w = 0 := by
    rw [Fh2.inner_eq_sum n (axisVec n) w]
    simp [axisVec, EuclideanSpace.single, Pi.single_apply, hw0]
  simp [hin]

lemma flipIsom_fix_axis (n : ℕ) [NeZero n] {i : Fin n} (hi : i ≠ (0 : Fin n)) :
    flipIsom n i (axisVec n) = axisVec n := by
  change Fh1.reflMap n (EuclideanSpace.single i (1 : ℝ)) (single_ne_zero n i) (axisVec n) = axisVec n
  rw [Fh1.reflMap_apply]
  have hin : inner ℝ (axisVec n) (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    rw [Fh2.inner_eq_sum n (axisVec n) (EuclideanSpace.single i (1 : ℝ))]
    simp [axisVec, EuclideanSpace.single, Pi.single_apply, hi]
  simp [hin]

lemma flipIsom_coord (n : ℕ) [NeZero n] (i : Fin n) :
    flipIsom n i (EuclideanSpace.single i (1 : ℝ)) = - (EuclideanSpace.single i (1 : ℝ)) := by
  change Fh1.reflMap n (EuclideanSpace.single i (1 : ℝ)) (single_ne_zero n i)
      (EuclideanSpace.single i (1 : ℝ)) = - (EuclideanSpace.single i (1 : ℝ))
  rw [Fh1.reflMap_apply]
  have hw : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) = 1 := by
    rw [Fh2.inner_eq_sum n (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))]
    simp [EuclideanSpace.single, Pi.single_apply]
  have hw2 : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) ≠ 0 := by
    rw [hw]
    norm_num
  rw [hw]
  norm_num
  simp [two_smul]

/-- flip leaves every other coordinate fixed -/
lemma flipIsom_other_coord (n : ℕ) [NeZero n] {i j : Fin n} (hij : j ≠ i) :
    (flipIsom n i (EuclideanSpace.single j (1 : ℝ))) = EuclideanSpace.single j (1 : ℝ) := by
  change Fh1.reflMap n (EuclideanSpace.single i (1 : ℝ)) (single_ne_zero n i)
      (EuclideanSpace.single j (1 : ℝ)) = EuclideanSpace.single j (1 : ℝ)
  ext k
  rw [Fh1.reflMap_apply]
  have hin : inner ℝ (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    have hn : ¬ i = j := fun h => hij h.symm
    rw [Fh2.inner_eq_sum n (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))]
    simp [EuclideanSpace.single, Pi.single_apply, hn]
  simp [hin]



/-- an isometry fixing the axis sends unit vector w (axis-orthogonal) to e_c -/
lemma exists_axisFixing_isometry_to_slice {n : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (w : E n) (hw : ‖w‖ = 1) (hw0 : w (0 : Fin n) = 0) :
    ∃ L : E n ≃ₗᵢ[ℝ] E n, L (axisVec n) = axisVec n ∧ L w = cvec n hn2 := by
  have hc : ‖cvec n hn2‖ = 1 := by simp [cvec, EuclideanSpace.single]
  by_cases h : w = cvec n hn2
  · refine ⟨LinearIsometryEquiv.refl ℝ (E n), ?_, ?_⟩
    · rfl
    · simpa [h]
  · refine ⟨Fh1.reflIsom n (w - cvec n hn2) (sub_ne_zero.mpr h), ?_, ?_⟩
    · exact refl_fix_axis n (w - cvec n hn2) (sub_ne_zero.mpr h) (by
        simp [cvec_eq, cIdx_ne_zero n hn2, hw0, EuclideanSpace.single, Pi.single_apply])
    · simpa using (Fh1.reflIsom_map (n := n) w (cvec n hn2) hw hc h)

/-- any nonzero axis-orthogonal vector is axis-fixed-isometric to a multiple of e_c -/
lemma complement_trans {n : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (x : E n) (hx0 : x (0 : Fin n) = 0) (hxn : x ≠ 0) :
    ∃ L : E n ≃ₗᵢ[ℝ] E n,
      L (axisVec n) = axisVec n ∧
      L x = (‖x‖ : ℝ) • cvec n hn2 := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxn
  let u : E n := (‖x‖)⁻¹ • x
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul]
    have hxnn : 0 ≤ ‖x‖ := norm_nonneg x
    have hx0n : ‖x‖ ≠ 0 := ne_of_gt hxnorm
    have hmul : |(‖x‖ : ℝ)⁻¹| * ‖x‖ = 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr hxnn)]
      exact inv_mul_cancel₀ hx0n
    exact hmul
  have hu0 : u (0 : Fin n) = 0 := by
    simp [u, hx0]
  rcases exists_axisFixing_isometry_to_slice hn2 u hu hu0 with ⟨L, hLfix, hLu⟩
  refine ⟨L, hLfix, ?_⟩
  calc
    L x = L ((‖x‖ : ℝ) • u) := by
            congr 1
            ext i
            simp [u, smul_smul]
            field_simp [hxnorm.ne']
    _ = (‖x‖ : ℝ) • L u := by
          rw [← LinearIsometryEquiv.map_smul]
    _ = (‖x‖ : ℝ) • cvec n hn2 := by rw [hLu]

/-- eval of the substitution -/
lemma substA_eval' (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P : MvPolynomial (Fin n) ℝ) (x : E n) :
    MvPolynomial.eval (fun i : Fin n => x i) (Fh2.substA n A P) =
      MvPolynomial.eval (fun i : Fin n => (A x) i) P := by
  rw [Fh2.substA]
  have h := MvPolynomial.aeval_bind₁ (R := ℝ) (S := ℝ)
    (f := fun i : Fin n => x i)
    (g := fun j : Fin n => ∑ i : Fin n, C (Fh2.matA n A j i) * X i) P
  rw [aeval_eq_eval] at h
  apply h.trans ?_
  apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
  funext j
  simp
  exact (Fh2.linear_map_apply_coord n A x j).symm

/-- Invariance at the level of values: AxisInv P with L fixing the axis gives P (L x) = P x. -/
lemma AxisInv_apply (n : ℕ) [NeZero n] (P : MvPolynomial (Fin n) ℝ) (hI : AxisInv n P)
    (L : E n ≃ₗᵢ[ℝ] E n) (hLfix : L (axisVec n) = axisVec n) (x : E n) :
    MvPolynomial.eval (fun i : Fin n => (L x) i) P =
      MvPolynomial.eval (fun i : Fin n => x i) P := by
  have hsub := hI L hLfix
  -- substA L P = P :  eval x (substA L P) = eval (L x) P
  have hval := substA_eval' n L P x
  -- hval : eval x (substA L P) = eval (fun i => (L x) i) P
  rw [hsub] at hval
  exact hval.symm



 
/-- substitution that kills all coordinates except the axis 0 and the slice coordinate c;
    image lives in the two variables X 0, X (cIdx n hn2). -/
def sliceSubst (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) :
    MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ := fun P =>
  MvPolynomial.bind₁ (fun i : Fin n =>
    if i = (0 : Fin n) then (X (0 : Fin n) : MvPolynomial (Fin n) ℝ)
    else if i = cIdx n hn2 then (X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
    else 0) P

lemma sliceSubst_add (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    (P Q : MvPolynomial (Fin n) ℝ) :
    sliceSubst n hn2 (P + Q) = sliceSubst n hn2 P + sliceSubst n hn2 Q := by
  simp [sliceSubst]

lemma sliceSubst_mul (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    (P Q : MvPolynomial (Fin n) ℝ) :
    sliceSubst n hn2 (P * Q) = sliceSubst n hn2 P * sliceSubst n hn2 Q := by
  simp [sliceSubst]

lemma sliceSubst_X_zero (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) :
    sliceSubst n hn2 (X (0 : Fin n) : MvPolynomial (Fin n) ℝ) = X (0 : Fin n) := by
  simp [sliceSubst, cIdx]

lemma sliceSubst_X_c (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) :
    sliceSubst n hn2 (X (cIdx n hn2) : MvPolynomial (Fin n) ℝ) = X (cIdx n hn2) := by
  simp [sliceSubst, cIdx_ne_zero n hn2]

lemma sliceSubst_X_other (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {i : Fin n}
    (hi0 : i ≠ (0 : Fin n)) (hic : i ≠ cIdx n hn2) :
    sliceSubst n hn2 (X i : MvPolynomial (Fin n) ℝ) = 0 := by
  unfold sliceSubst
  rw [MvPolynomial.bind₁_X_right]
  simp [hi0, hic]

/-- slicing a product with a scalar C a keeps the scalar -/
lemma sliceSubst_C (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (a : ℝ) :
    sliceSubst n hn2 (C a : MvPolynomial (Fin n) ℝ) = C a := by
  simp [sliceSubst]





/-- evaluation at the slice point as a polynomial function of the coordinates -/
lemma axisVec_coord (n : ℕ) [NeZero n] (i : Fin n) :
    (axisVec n) i = if i = (0 : Fin n) then 1 else 0 := by
  simp [axisVec, EuclideanSpace.single, Pi.single_apply]

lemma cvec_coord (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (i : Fin n) :
    (cvec n hn2) i = if i = cIdx n hn2 then 1 else 0 := by
  rw [cvec_eq]
  simp [EuclideanSpace.single, Pi.single_apply]

lemma slicePoint_coord (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) (i : Fin n) :
    ((s • axisVec n + t • cvec n hn2) : E n) i =
      (if i = (0 : Fin n) then s else if i = cIdx n hn2 then t else 0) := by
  by_cases h0 : i = (0 : Fin n)
  · subst i
    simp [axisVec, cvec_eq, EuclideanSpace.single, Pi.single_apply, cIdx_ne_zero n hn2]
  · by_cases hc : i = cIdx n hn2
    · subst i
      simp [axisVec, cvec_eq, EuclideanSpace.single, Pi.single_apply, h0]
    · simp [axisVec, cvec_eq, EuclideanSpace.single, Pi.single_apply, h0, hc]

lemma eval_slice_point (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (P : MvPolynomial (Fin n) ℝ)
    (s t : ℝ) :
    MvPolynomial.eval (fun i : Fin n => ((s • axisVec n + t • cvec n hn2) : E n) i) P =
      MvPolynomial.eval (fun i : Fin n =>
        (if i = (0 : Fin n) then s else if i = cIdx n hn2 then t else 0)) P := by
  apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
  funext i
  exact slicePoint_coord n hn2 s t i

/-- Axis-invariance gives evenness of P on the slice plane: P(s e0 + t ec) = P(s e0 − t ec). -/
lemma AxisInv_slice_value_even (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {P : MvPolynomial (Fin n) ℝ}
    (hI : AxisInv n P) (s t : ℝ) :
    MvPolynomial.eval (fun i : Fin n => ((s • axisVec n + t • cvec n hn2) : E n) i) P =
      MvPolynomial.eval (fun i : Fin n => ((s • axisVec n - t • cvec n hn2) : E n) i) P := by
  have hfix : flipIsom n (cIdx n hn2) (axisVec n) = axisVec n :=
    flipIsom_fix_axis n (cIdx_ne_zero n hn2)
  have hLc : flipIsom n (cIdx n hn2) (cvec n hn2) = - (cvec n hn2) := by
    change flipIsom n (cIdx n hn2) (EuclideanSpace.single (cIdx n hn2) (1 : ℝ)) =
        - (EuclideanSpace.single (cIdx n hn2) (1 : ℝ))
    exact flipIsom_coord n (cIdx n hn2)
  have hL : flipIsom n (cIdx n hn2) (s • axisVec n + t • cvec n hn2) =
      s • axisVec n - t • cvec n hn2 := by
    rw [map_add]
    rw [map_smul, map_smul]
    rw [hfix]
    rw [hLc]
    rw [smul_neg]
    rw [sub_eq_add_neg]
  have hv := AxisInv_apply n P hI (flipIsom n (cIdx n hn2)) hfix (s • axisVec n + t • cvec n hn2)
  rw [hL] at hv
  exact hv.symm



/-- coordinates of the slice point s e0 + t e_c -/
def sliceCoord (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) : Fin n → ℝ := fun i =>
  if i = (0 : Fin n) then s else if i = cIdx n hn2 then t else 0

lemma sliceCoord_zero (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) :
    sliceCoord n hn2 s t (0 : Fin n) = s := by
  simp [sliceCoord]

lemma sliceCoord_c (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) :
    sliceCoord n hn2 s t (cIdx n hn2) = t := by
  simp [sliceCoord, cIdx_ne_zero n hn2]

lemma sliceCoord_other (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) {i : Fin n}
    (hi0 : i ≠ (0 : Fin n)) (hic : i ≠ cIdx n hn2) :
    sliceCoord n hn2 s t i = 0 := by
  simp [sliceCoord, hi0, hic]

/-- R2m evaluated on the slice gives t². -/
lemma R2m_eval_slice (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) :
    MvPolynomial.eval (sliceCoord n hn2 s t) (R2m n) = t ^ 2 := by
  classical
  dsimp [R2m]
  rw [map_sum]
  have hrewrite :
      (∑ i ∈ Finset.univ.erase (0 : Fin n),
        MvPolynomial.eval (sliceCoord n hn2 s t) ((X i : MvPolynomial (Fin n) ℝ) ^ 2))
      = ∑ i ∈ Finset.univ.erase (0 : Fin n), (if i = cIdx n hn2 then t ^ 2 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : i ≠ (0 : Fin n) := (Finset.mem_erase.mp hi).1
    by_cases hic : i = cIdx n hn2
    · subst i
      simp [sliceCoord, cIdx_ne_zero n hn2]
    · simp [sliceCoord, hi0, hic]
  rw [hrewrite]
  have hcIn : cIdx n hn2 ∈ Finset.univ.erase (0 : Fin n) := by
    rw [Finset.mem_erase]
    exact ⟨cIdx_ne_zero n hn2, Finset.mem_univ _⟩
  rw [Finset.sum_eq_single (cIdx n hn2)]
  · simp
  · intro i _ hic
    rw [if_neg hic]
  · intro hnmem
    exfalso
    exact hnmem hcIn

lemma X0_pow_eval_slice (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) (e : ℕ) :
    MvPolynomial.eval (sliceCoord n hn2 s t)
      ((X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ e) = s ^ e := by
  rw [map_pow]
  simp [sliceCoord]



/-- coefficients of the slice expansion of an axis-invariant homogeneous polynomial -/
def sliceCoeff (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (P : MvPolynomial (Fin n) ℝ) (k j : ℕ) : ℝ :=
  P.coeff (Finsupp.single (0 : Fin n) (k - 2 * j) + Finsupp.single (cIdx n hn2) (2 * j))

/-- candidate Q reconstructing an axis-invariant homogeneous P from its slice coefficients -/
def axisQ (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (P : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Finset.range (k / 2 + 1),
    C (sliceCoeff n hn2 P k j) * ((R2m n) ^ j * (X (0 : Fin n)) ^ (k - 2 * j))

lemma eval_R2m_pow_slice (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) (j : ℕ) :
    MvPolynomial.eval (sliceCoord n hn2 s t) ((R2m n) ^ j) = (t ^ 2) ^ j := by
  rw [map_pow, R2m_eval_slice n hn2 s t]

/-- Q evaluates on the slice plane to the same series as its coefficients. -/
lemma axisQ_eval_slice (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (P : MvPolynomial (Fin n) ℝ)
    (k : ℕ) (s t : ℝ) :
    MvPolynomial.eval (sliceCoord n hn2 s t) (axisQ n hn2 P k)
      = ∑ j ∈ Finset.range (k / 2 + 1),
          sliceCoeff n hn2 P k j * s ^ (k - 2 * j) * t ^ (2 * j) := by
  rw [axisQ, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  -- eval (C c * (R2m^j * X0^e)) = c * (t^2)^j * s^e
  rw [eval_mul]
  rw [eval_C]
  rw [eval_mul]
  rw [eval_R2m_pow_slice n hn2 s t j]
  -- eval of X0^e:
  have hx : MvPolynomial.eval (sliceCoord n hn2 s t) ((X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2 * j))
      = s ^ (k - 2 * j) := by
    simp [sliceCoord]
  rw [hx]
  -- (t^2)^j = t^(2*j)
  have hpow : (t ^ 2) ^ j = t ^ (2 * j) := by
    rw [pow_mul]
  rw [hpow]
  ring



/-- the flip isometry at the slice coordinate negates exactly that coordinate -/
lemma flipIsom_coord_apply (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (x : E n) (j : Fin n) :
    (flipIsom n (cIdx n hn2) x) j = if j = cIdx n hn2 then - x j else x j := by
  change (Fh1.reflMap n (EuclideanSpace.single (cIdx n hn2) (1 : ℝ)) (single_ne_zero n (cIdx n hn2)) x) j =
      if j = cIdx n hn2 then - x j else x j
  rw [Fh1.reflMap_apply]
  have hinner : inner ℝ x (EuclideanSpace.single (cIdx n hn2) (1 : ℝ)) = x (cIdx n hn2) := by
    exact (Fh2.coord_eq_inner_right n x (cIdx n hn2)).symm
  have hself : inner ℝ (EuclideanSpace.single (cIdx n hn2) (1 : ℝ))
      (EuclideanSpace.single (cIdx n hn2) (1 : ℝ)) = 1 := by
    rw [Fh2.inner_eq_sum n (EuclideanSpace.single (cIdx n hn2) (1 : ℝ))
      (EuclideanSpace.single (cIdx n hn2) (1 : ℝ))]
    simp [EuclideanSpace.single, Pi.single_apply]
  by_cases hj : j = cIdx n hn2
  · subst j
    simp [hinner, hself]
    ring
  · have hsingle : (EuclideanSpace.single (cIdx n hn2) (1 : ℝ)) j = 0 := by
      simp [EuclideanSpace.single, Pi.single_apply, hj]
    simp [hinner, hself, hj, hsingle]

/-- Axis-invariance at the slice-coordinate flip is the flip-substitution invariance
    expected by `Commons.Analysis.MvPolynomial.coeff_odd_of_flip_invariant`. -/
lemma AxisInv_flip_bind_eq (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {P : MvPolynomial (Fin n) ℝ}
    (hI : AxisInv n P) :
    MvPolynomial.bind₁ (fun j : Fin n =>
        if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
        else MvPolynomial.X j) P = P := by
  apply MvPolynomial.funext
  intro f
  let v : E n := (EuclideanSpace.equiv (Fin n) ℝ).symm f
  have hv : ∀ j : Fin n, v j = f j := by
    intro j
    simp [v]
  have hfix : flipIsom n (cIdx n hn2) (axisVec n) = axisVec n :=
    flipIsom_fix_axis n (cIdx_ne_zero n hn2)
  have hval := AxisInv_apply n P hI (flipIsom n (cIdx n hn2)) hfix v
  -- eval (fun i => v i) (bind₁ g P) = eval f P
  let g : Fin n → MvPolynomial (Fin n) ℝ := fun j =>
    if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
    else MvPolynomial.X j
  have hevalg : ∀ j : Fin n,
      MvPolynomial.eval (fun i : Fin n => v i) (g j) =
        if j = cIdx n hn2 then - v j else v j := by
    intro j
    by_cases hj : j = cIdx n hn2
    · subst j
      simp [g]
    · simp [g, hj]
  have hbind : MvPolynomial.eval (fun i : Fin n => v i)
      (MvPolynomial.bind₁ (fun j : Fin n =>
        if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
        else MvPolynomial.X j) P)
      = MvPolynomial.eval (fun j : Fin n => if j = cIdx n hn2 then - v j else v j) P := by
    have h := MvPolynomial.aeval_bind₁ (R := ℝ) (S := ℝ)
      (f := fun i : Fin n => v i) (g := g) P
    rw [aeval_eq_eval] at h
    calc
      MvPolynomial.eval (fun i : Fin n => v i)
          (MvPolynomial.bind₁ (fun j : Fin n =>
            if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
            else MvPolynomial.X j) P)
          = MvPolynomial.eval (fun i : Fin n => v i) (MvPolynomial.bind₁ g P) := rfl
      _ = MvPolynomial.eval (fun j : Fin n => MvPolynomial.eval (fun i : Fin n => v i) (g j)) P := by
            simpa using h
      _ = MvPolynomial.eval (fun j : Fin n => if j = cIdx n hn2 then - v j else v j) P := by
            apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
            funext j
            exact hevalg j
  -- eval v P at the flipped coordinates equals eval v P  (by hval)
  have hflip : MvPolynomial.eval (fun j : Fin n => if j = cIdx n hn2 then - v j else v j) P
      = MvPolynomial.eval (fun j : Fin n => v j) P := by
    have hcoord : (fun j : Fin n => if j = cIdx n hn2 then - v j else v j) =
        (fun j : Fin n => (flipIsom n (cIdx n hn2) v) j) := by
      funext j
      rw [flipIsom_coord_apply n hn2 v j]
    rw [hcoord]
    exact hval
  calc
    MvPolynomial.eval (fun i : Fin n => f i) (MvPolynomial.bind₁ (fun j : Fin n =>
        if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
        else MvPolynomial.X j) P)
        = MvPolynomial.eval (fun i : Fin n => v i) (MvPolynomial.bind₁ (fun j : Fin n =>
            if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
            else MvPolynomial.X j) P) := by
          apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g
            (MvPolynomial.bind₁ (fun j : Fin n =>
              if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
              else MvPolynomial.X j) P))
          funext i
          rw [hv i]
    _ = MvPolynomial.eval (fun j : Fin n => if j = cIdx n hn2 then - v j else v j) P := hbind
    _ = MvPolynomial.eval (fun j : Fin n => v j) P := hflip
    _ = MvPolynomial.eval (fun i : Fin n => f i) P := by
          apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g P)
          funext i
          exact (hv i).symm



/-- variant of the flip-substitution invariance whose true branch reads `-(X j)` -/
lemma AxisInv_flip_bind_eq' (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {P : MvPolynomial (Fin n) ℝ}
    (hI : AxisInv n P) :
    MvPolynomial.bind₁ (fun j : Fin n =>
        if j = cIdx n hn2 then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ)
        else MvPolynomial.X j) P = P := by
  have hmain := AxisInv_flip_bind_eq n hn2 hI
  have hf : (fun j : Fin n =>
        if j = cIdx n hn2 then -(MvPolynomial.X (cIdx n hn2) : MvPolynomial (Fin n) ℝ)
        else MvPolynomial.X j)
      = (fun j : Fin n =>
        if j = cIdx n hn2 then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ)
        else MvPolynomial.X j) := by
    funext j
    by_cases hj : j = cIdx n hn2
    · subst j
      rfl
    · simp [hj]
  rw [hf] at hmain
  exact hmain

/-- Axis-invariance forces the slice-coordinate-odd coefficients of P to vanish. -/
lemma AxisInv_coeff_odd_c (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {P : MvPolynomial (Fin n) ℝ}
    (hI : AxisInv n P) (d : Fin n →₀ ℕ) (hodd : Odd (d (cIdx n hn2))) :
    P.coeff d = 0 := by
  exact Commons.Analysis.MvPolynomial.coeff_odd_of_flip_invariant (i := cIdx n hn2) (P := P) (d := d)
    (hodd := hodd) (hflip := AxisInv_flip_bind_eq' n hn2 hI)



/-- slice values of an axis-invariant homogeneous polynomial equal its coefficient series -/
lemma AxisInv_slice_value_expand (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {P : MvPolynomial (Fin n) ℝ}
    {k : ℕ} (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (hI : AxisInv n P)
    (s t : ℝ) :
    MvPolynomial.eval (sliceCoord n hn2 s t) P
      = ∑ j ∈ Finset.range (k / 2 + 1),
          sliceCoeff n hn2 P k j * s ^ (k - 2 * j) * t ^ (2 * j) := by
  have hodd : ∀ d : Fin n →₀ ℕ, Odd (d (cIdx n hn2)) → P.coeff d = 0 :=
    fun d hd => AxisInv_coeff_odd_c n hn2 hI d hd
  have ht := Commons.Analysis.MvPolynomial.eval_two_var_even (a := (0 : Fin n)) (b := cIdx n hn2)
    (hab := fun h : (0 : Fin n) = cIdx n hn2 => cIdx_ne_zero n hn2 h.symm)
    (P := P) (k := k) (hP := hP) (hodd := hodd) (s := s) (t := t)
  -- rewrite the LHS from sliceCoord to the raw coordinate function
  rw [show MvPolynomial.eval (sliceCoord n hn2 s t) P =
      MvPolynomial.eval (fun i : Fin n =>
        if i = (0 : Fin n) then s else if i = cIdx n hn2 then t else 0) P by
        apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
        funext i
        rfl]
  exact ht



/-- the 0-row of the matrix of an axis-fixing isometry is (1, 0, ..., 0) -/
lemma matA_zero_row (n : ℕ) [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hfix : L (axisVec n) = axisVec n) (k : Fin n) :
    Fh2.matA n L (0 : Fin n) k = if k = (0 : Fin n) then 1 else 0 := by
  have hL0 : L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
      EuclideanSpace.single (0 : Fin n) (1 : ℝ) := by
    simpa [axisVec] using hfix
  have hsym : L.symm (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
      EuclideanSpace.single (0 : Fin n) (1 : ℝ) := by
    calc
      L.symm (EuclideanSpace.single (0 : Fin n) (1 : ℝ))
          = L.symm (L (EuclideanSpace.single (0 : Fin n) (1 : ℝ))) := by
            conv_lhs => rw [← hL0]
      _ = EuclideanSpace.single (0 : Fin n) (1 : ℝ) := by simp
  have hinner : inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ))
      (L (EuclideanSpace.single k (1 : ℝ))) = if k = (0 : Fin n) then 1 else 0 := by
    calc
      inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) (L (EuclideanSpace.single k (1 : ℝ)))
          = inner ℝ (L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)))
              (L (EuclideanSpace.single k (1 : ℝ))) := by
            congr 1
            exact hL0.symm
      _ = inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ)) := by
            rw [LinearIsometryEquiv.inner_map_map L]
      _ = if k = (0 : Fin n) then 1 else 0 := by
            have hb := Fh2.basis_inner n (0 : Fin n) k
            rw [hb]
            by_cases hk : k = (0 : Fin n)
            · simp [hk]
            · have h0k : (0 : Fin n) ≠ k := fun h => hk h.symm
              simp [hk, h0k]
  calc
    Fh2.matA n L (0 : Fin n) k = (L (EuclideanSpace.single k (1 : ℝ))) (0 : Fin n) := by
          rfl
    _ = inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) (L (EuclideanSpace.single k (1 : ℝ))) := by
          rw [Fh2.coord_eq_inner_left n (L (EuclideanSpace.single k (1 : ℝ))) (0 : Fin n)]
    _ = if k = (0 : Fin n) then 1 else 0 := hinner

/-- X_0 is invariant under every axis-fixing isometry. -/
lemma substA_X0_axisFix (n : ℕ) [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hfix : L (axisVec n) = axisVec n) :
    Fh2.substA n L (X (0 : Fin n) : MvPolynomial (Fin n) ℝ) = X (0 : Fin n) := by
  rw [Fh2.substA_X n L (0 : Fin n)]
  rw [show (∑ k : Fin n, C (Fh2.matA n L (0 : Fin n) k) * X k) =
      (∑ k : Fin n, C (if k = (0 : Fin n) then 1 else 0) * X k) by
        apply Finset.sum_congr rfl
        intro k hk
        rw [matA_zero_row n L hfix k]]
  rw [Finset.sum_eq_single (0 : Fin n)]
  · simp
  · intro k _ hk
    rw [if_neg hk]
    simp
  · intro h0
    simp at h0



/-- R2m evaluated at an arbitrary point is the sum of squares of the non-axis coordinates -/
lemma R2m_eval_eq (n : ℕ) [NeZero n] (y : E n) :
    MvPolynomial.eval (fun i : Fin n => y i) (R2m n)
      = ∑ i ∈ Finset.univ.erase (0 : Fin n), (y i) ^ 2 := by
  dsimp [R2m]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- substitution commutes with powers -/
lemma substA_pow (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P : MvPolynomial (Fin n) ℝ) (e : ℕ) :
    Fh2.substA n A (P ^ e) = (Fh2.substA n A P) ^ e := by
  rw [Fh2.substA]
  exact map_pow (MvPolynomial.bind₁ (fun j : Fin n =>
      ∑ i : Fin n, C (Fh2.matA n A j i) * X i) : MvPolynomial (Fin n) ℝ →+* MvPolynomial (Fin n) ℝ)
    P e

/-- powers of X_0 are invariant under axis-fixing isometries -/
lemma substA_X0_pow_axisFix (n : ℕ) [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hfix : L (axisVec n) = axisVec n) (e : ℕ) :
    Fh2.substA n L ((X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ e) =
      (X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ e := by
  rw [substA_pow]
  rw [substA_X0_axisFix n L hfix]



/-- norm-squared equals the sum of squared coordinates -/
lemma norm_sq_eq_sum_sq (n : ℕ) (v : E n) : ‖v‖ ^ 2 = ∑ i : Fin n, (v i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (x := v)]
  rw [Fh2.inner_eq_sum n v v]
  apply Finset.sum_congr rfl
  intro i hi
  ring



/-- R2m is invariant under every axis-fixing isometry -/
lemma substA_R2m_axisFix (n : ℕ) [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hfixL : L (axisVec n) = axisVec n) :
    Fh2.substA n L (R2m n) = R2m n := by
  have hfix : L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
      EuclideanSpace.single (0 : Fin n) (1 : ℝ) := by
    simpa [axisVec] using hfixL
  apply MvPolynomial.funext
  intro f
  let v : E n := (EuclideanSpace.equiv (Fin n) ℝ).symm f
  have hv : ∀ j : Fin n, v j = f j := by intro j; simp [v]
  have hcoord0 := Commons.Analysis.InnerProductSpace.axis_isometry_coord0 L hfix v
  calc
    MvPolynomial.eval (fun i : Fin n => f i) (Fh2.substA n L (R2m n))
        = MvPolynomial.eval (fun i : Fin n => v i) (Fh2.substA n L (R2m n)) := by
          apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g (Fh2.substA n L (R2m n)))
          funext i
          exact (hv i).symm
    _ = MvPolynomial.eval (fun i : Fin n => (L v) i) (R2m n) := by
          exact substA_eval' n L (R2m n) v
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n), ((L v) i) ^ 2 := by
          change MvPolynomial.eval (fun i : Fin n => (L v) i)
            (∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n),
              (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ 2) = _
          exact Commons.Analysis.MvPolynomial.eval_sum_sq_erase (y := L v)
    _ = ∑ i : Fin n, (if i = (0 : Fin n) then 0 else ((L v) i) ^ 2) := by
          exact Commons.Analysis.InnerProductSpace.erase_sum_sq_eq_if (y := L v)
    _ = ‖L v - (v (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)‖ ^ 2 := by
          have hc := Commons.Analysis.InnerProductSpace.compl_norm_sq_eq (y := L v)
          -- hc : ‖Lv - (Lv 0)e0‖² = if-sum (Lv)
          rw [← hc]
          congr 1
          rw [hcoord0]
    _ = ‖v - (v (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)‖ ^ 2 := by
          exact congrArg (fun a : ℝ => a ^ 2)
            (Commons.Analysis.InnerProductSpace.axis_isometry_preserves_compl_norm L hfix v)
    _ = ∑ i : Fin n, (if i = (0 : Fin n) then 0 else (v i) ^ 2) := by
          exact (Commons.Analysis.InnerProductSpace.compl_norm_sq_eq (y := v))
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n), (v i) ^ 2 := by
          exact (Commons.Analysis.InnerProductSpace.erase_sum_sq_eq_if (y := v)).symm
    _ = MvPolynomial.eval (fun i : Fin n => v i) (R2m n) := by
          change _ = MvPolynomial.eval (fun i : Fin n => v i)
            (∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n),
              (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ 2)
          exact (Commons.Analysis.MvPolynomial.eval_sum_sq_erase (y := v)).symm
    _ = MvPolynomial.eval (fun i : Fin n => f i) (R2m n) := by
          apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g (R2m n))
          funext i
          exact hv i



/-- powers of R2m are axis-invariant -/
lemma substA_R2m_pow_axisFix (n : ℕ) [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hfix : L (axisVec n) = axisVec n) (j : ℕ) :
    Fh2.substA n L ((R2m n) ^ j) = (R2m n) ^ j := by
  rw [substA_pow]
  rw [substA_R2m_axisFix n L hfix]

/-- monomials R2m^j * X_0^e are axis-invariant -/
lemma substA_R2m_X0_mono_axisFix (n : ℕ) [NeZero n] (L : E n ≃ₗᵢ[ℝ] E n)
    (hfix : L (axisVec n) = axisVec n) (j e : ℕ) :
    Fh2.substA n L ((R2m n) ^ j * (X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ e) =
      (R2m n) ^ j * (X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ e := by
  rw [Fh2.substA_mul]
  rw [substA_R2m_pow_axisFix n L hfix j]
  rw [substA_X0_pow_axisFix n L hfix e]

/-- substitution preserves constant polynomials -/
lemma substA_C (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (a : ℝ) :
    Fh2.substA n A (C a : MvPolynomial (Fin n) ℝ) = C a := by
  simp [Fh2.substA]

/-- substitution commutes with subtraction -/
lemma substA_sub (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P Q : MvPolynomial (Fin n) ℝ) :
    Fh2.substA n A (P - Q) = Fh2.substA n A P - Fh2.substA n A Q := by
  simp [Fh2.substA]

/-- the candidate axisQ is axis-invariant -/
lemma substA_axisQ_axisFix (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    (P : MvPolynomial (Fin n) ℝ) (k : ℕ) (L : E n ≃ₗᵢ[ℝ] E n)
    (hfix : L (axisVec n) = axisVec n) :
    Fh2.substA n L (axisQ n hn2 P k) = axisQ n hn2 P k := by
  unfold axisQ
  rw [Fh2.substA_sum n L (Finset.range (k / 2 + 1))
    (fun j => C (sliceCoeff n hn2 P k j) * ((R2m n) ^ j * (X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2 * j)))]
  apply Finset.sum_congr rfl
  intro j hj
  -- substA (C c * monomial) = C c * substA monomial
  rw [Fh2.substA_mul, substA_C]
  rw [substA_R2m_X0_mono_axisFix n L hfix j (k - 2 * j)]

/-- difference of two axis-invariant polynomials is axis-invariant -/
lemma AxisInv_sub (n : ℕ) [NeZero n] {P Q : MvPolynomial (Fin n) ℝ}
    (hP : AxisInv n P) (hQ : AxisInv n Q) : AxisInv n (P - Q) := by
  intro L hfix
  rw [substA_sub]
  rw [hP L hfix, hQ L hfix]

/-- the difference W := P - axisQ is axis-invariant -/
lemma AxisInv_W (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {P : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (hIP : AxisInv n P) : AxisInv n (P - axisQ n hn2 P k) := by
  refine AxisInv_sub (n := n) (P := P) (Q := axisQ n hn2 P k) hIP ?_
  intro L hfix
  exact substA_axisQ_axisFix n hn2 P k L hfix

/-- W vanishes on the slice plane -/
lemma W_slice_zero (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) {P : MvPolynomial (Fin n) ℝ}
    {k : ℕ} (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (hIP : AxisInv n P)
    (s t : ℝ) :
    MvPolynomial.eval (fun i : Fin n => ((s • axisVec n + t • cvec n hn2) : E n) i)
      (P - axisQ n hn2 P k) = 0 := by
  have hsliceP := AxisInv_slice_value_expand n hn2 hP hIP s t
  have hsliceQ := axisQ_eval_slice n hn2 P k s t
  -- eval at the slice point equals eval at sliceCoord
  have hp : MvPolynomial.eval (sliceCoord n hn2 s t) P =
      MvPolynomial.eval (fun i : Fin n => ((s • axisVec n + t • cvec n hn2) : E n) i) P := by
    exact (eval_slice_point n hn2 P s t).symm
  have hq : MvPolynomial.eval (sliceCoord n hn2 s t) (axisQ n hn2 P k) =
      MvPolynomial.eval (fun i : Fin n => ((s • axisVec n + t • cvec n hn2) : E n) i)
        (axisQ n hn2 P k) := by
    exact (eval_slice_point n hn2 (axisQ n hn2 P k) s t).symm
  -- both eval-sliceCoord equal the same series
  have hsame : MvPolynomial.eval (sliceCoord n hn2 s t) P =
      MvPolynomial.eval (sliceCoord n hn2 s t) (axisQ n hn2 P k) := by
    rw [hsliceP, hsliceQ]
  rw [map_sub]
  rw [← hp]
  rw [← hq]
  exact sub_eq_zero.mpr hsame

end FhCHS



noncomputable section
open scoped BigOperators
open MvPolynomial

namespace FhCHS4

open Fh1 Fh2 FhCHS

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- If an axis-invariant polynomial vanishes at every vector then it is zero. -/
lemma axisInv_eq_zero_of_eval_zero (n : ℕ) [NeZero n] {W : MvPolynomial (Fin n) ℝ}
    (hW : AxisInv n W)
    (heval : ∀ x : E n, MvPolynomial.eval (fun i : Fin n => x i) W = 0) : W = 0 := by
  apply MvPolynomial.funext
  intro f
  let x : E n := (EuclideanSpace.equiv (Fin n) ℝ).symm f
  have hx : ∀ i : Fin n, x i = f i := by
    intro i
    simp [x]
  calc
    MvPolynomial.eval (fun i : Fin n => f i) W
        = MvPolynomial.eval (fun i : Fin n => x i) W := by
          apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g W)
          funext i
          exact (hx i).symm
    _ = 0 := heval x

/-- The slice-point with parameters (s,t) equals s e0 + t e_c as a vector. -/
lemma slicePoint_eq (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (s t : ℝ) :
    ((s • axisVec n + t • cvec n hn2) : E n) = s • axisVec n + t • cvec n hn2 := rfl

/-- The first coordinate of the axis-orthogonal part of x is zero. -/
lemma sub_smul_single_coord0 (n : ℕ) [NeZero n] (x : E n) :
    (x - (x (0 : Fin n)) • (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : E n)) (0 : Fin n) = 0 := by
  simp [EuclideanSpace.single, Pi.single_apply]

/-- Transport: an axis-invariant polynomial vanishing on the slice plane vanishes everywhere. -/
lemma axisInv_zero_of_slice_zero (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    {W : MvPolynomial (Fin n) ℝ} (hW : AxisInv n W)
    (hslice : ∀ s t : ℝ,
      MvPolynomial.eval (fun i : Fin n => ((s • axisVec n + t • cvec n hn2) : E n) i) W = 0) :
    W = 0 := by
  apply axisInv_eq_zero_of_eval_zero (n := n) hW
  intro x
  let x0 : ℝ := x (0 : Fin n)
  let xp : E n := x - x0 • axisVec n
  have hdecomp : x = x0 • axisVec n + xp := by
    dsimp [xp]
    abel
  have hxp0 : xp (0 : Fin n) = 0 := by
    dsimp [xp, x0]
    simpa [axisVec] using sub_smul_single_coord0 (n := n) x
  by_cases hz : xp = 0
  · -- x lies on the axis, hence on the slice (t = 0)
    have hx : x = (x0 : ℝ) • axisVec n + (0 : ℝ) • cvec n hn2 := by
      rw [hdecomp, hz]
      simp
    calc
      MvPolynomial.eval (fun i : Fin n => x i) W
          = MvPolynomial.eval (fun i : Fin n =>
              (((x0 : ℝ) • axisVec n + (0 : ℝ) • cvec n hn2) : E n) i) W := by
            apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g W)
            funext i
            rw [hx]
      _ = 0 := hslice x0 0
  · -- general position: reflect the complement part onto the c-axis
    rcases complement_trans (n := n) hn2 xp hxp0 hz with ⟨L, hLfix, hLx⟩
    have hLx' : L x = (x0 : ℝ) • axisVec n + (‖xp‖ : ℝ) • cvec n hn2 := by
      calc
        L x = L (x0 • axisVec n + xp) := by rw [hdecomp]
        _ = L (x0 • axisVec n) + L xp := by rw [map_add]
        _ = x0 • L (axisVec n) + L xp := by rw [map_smul]
        _ = x0 • axisVec n + (‖xp‖ : ℝ) • cvec n hn2 := by rw [hLfix, hLx]
    have h0 : MvPolynomial.eval (fun i : Fin n => (L x) i) W = 0 := by
      calc
        MvPolynomial.eval (fun i : Fin n => (L x) i) W
            = MvPolynomial.eval (fun i : Fin n =>
                (((x0 : ℝ) • axisVec n + (‖xp‖ : ℝ) • cvec n hn2) : E n) i) W := by
              apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g W)
              funext i
              rw [hLx']
        _ = 0 := hslice x0 ‖xp‖
    have hEQ := AxisInv_apply n W hW L hLfix x
    -- hEQ : eval (coords (L x)) W = eval (coords x) W
    rw [← hEQ]
    exact h0

/-- Structure theorem: an axis-invariant homogeneous polynomial of degree k equals its axisQ. -/
lemma axisInv_homogeneous_eq_axisQ (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    {P : MvPolynomial (Fin n) ℝ} {k : ℕ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (hIP : AxisInv n P) :
    P = axisQ n hn2 P k := by
  let W : MvPolynomial (Fin n) ℝ := P - axisQ n hn2 P k
  have hW_ax : AxisInv n W := by
    dsimp [W]
    exact AxisInv_W n hn2 k hIP
  have hslice : ∀ s t : ℝ,
      MvPolynomial.eval (fun i : Fin n => ((s • axisVec n + t • cvec n hn2) : E n) i) W = 0 := by
    intro s t
    dsimp [W]
    exact W_slice_zero n hn2 hP hIP s t
  have hW0 : W = 0 := axisInv_zero_of_slice_zero n hn2 hW_ax hslice
  dsimp [W] at hW0
  exact sub_eq_zero.mp hW0

end FhCHS4


noncomputable section
open scoped BigOperators Classical
open MvPolynomial MeasureTheory

namespace FhCHS5

open Fh1 Fh2 FhCHS FhCHS4

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev S (n : ℕ) := Metric.sphere (0 : E n) 1

/-- axis vector e0 -/
def e0Vec (n : ℕ) [NeZero n] : E n := FhCHS.axisVec n

lemma e0Vec_unit (n : ℕ) [NeZero n] : ‖e0Vec n‖ = 1 := by
  simp [e0Vec, FhCHS.axisVec, EuclideanSpace.single]

/-- the sphere point on the axis -/
def e0Point (n : ℕ) [NeZero n] : S n := ⟨e0Vec n, by rw [mem_sphere_zero_iff_norm]; exact e0Vec_unit n⟩

lemma substA_eval_coord (n : ℕ) (A : E n ≃ₗᵢ[ℝ] E n) (P : MvPolynomial (Fin n) ℝ) (θ : S n) :
    MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (Fh2.substA n A P) =
      MvPolynomial.eval (fun i : Fin n => ((A : E n → E n) (θ : E n)) i) P := by
  simpa using substA_eval' n A P (θ : E n)

/-- rotation invariance of the cosine integral against e0:
    cos-integral of the rotated polynomial at e0 equals the cos-integral of the
    original polynomial at A e0. -/
lemma cosine_transform_rotate (n : ℕ) [NeZero n] (A : E n ≃ₗᵢ[ℝ] E n)
    (P : MvPolynomial (Fin n) ℝ) :
    (∫ θ : S n, |inner ℝ (e0Vec n) (θ : E n)| *
          MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (Fh2.substA n A P)
        ∂MeasureTheory.volume.toSphere) =
    (∫ θ : S n, |inner ℝ ((A : E n → E n) (e0Vec n)) (θ : E n)| *
          MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
        ∂MeasureTheory.volume.toSphere) := by
  classical
  haveI : Nontrivial (E n) := ⟨⟨e0Vec n, 0, by
    intro h
    have hc := congrArg (fun v : E n => ‖v‖) h
    rw [e0Vec_unit n, norm_zero] at hc
    norm_num at hc⟩⟩
  let m : S n → S n := fun θ => ⟨(A : E n → E n) θ.1, by
    simpa [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
      using (mem_sphere_zero_iff_norm.mp θ.2)⟩
  have hcore := Commons.Analysis.MeasureTheory.cosine_rotate (V := E n) A
    (g := fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P) (u := e0Vec n)
  -- hcore : (∫ θ, |⟨e0,θ⟩| * g (m θ)) = (∫ θ, |⟨A e0,θ⟩| * g θ)
  calc
    (∫ θ : S n, |inner ℝ (e0Vec n) (θ : E n)| *
          MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (Fh2.substA n A P)
        ∂MeasureTheory.volume.toSphere)
        = (∫ θ : S n, |inner ℝ (e0Vec n) (θ : E n)| *
            MvPolynomial.eval (fun i : Fin n => ((m θ : S n) : E n) i) P
          ∂MeasureTheory.volume.toSphere) := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro θ
          change |inner ℝ (e0Vec n) (θ : E n)| *
              MvPolynomial.eval (fun i : Fin n => (θ : E n) i) (Fh2.substA n A P) =
            |inner ℝ (e0Vec n) (θ : E n)| *
              MvPolynomial.eval (fun i : Fin n => ((m θ : S n) : E n) i) P
          rw [substA_eval_coord n A P θ]
    _ = (∫ θ : S n, |inner ℝ ((A : E n → E n) (e0Vec n)) (θ : E n)| *
          MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
        ∂MeasureTheory.volume.toSphere) := by
          simpa [m] using hcore

/-- core theorem for dimension at least 2, assuming the axis scalar lemma. -/
lemma cosineHarmonicScalar_core {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (g : S n → ℝ)
    (hg : ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
      ∀ θ : S n, g θ = MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P) :
    ∃ c : ℝ, ∀ u : S n,
      (∫ θ : S n, |inner ℝ (u : E n) (θ : E n)| * g θ ∂MeasureTheory.volume.toSphere) =
        c * g u := by
  classical
  rcases hg with ⟨P, hPh, hPlap, hgval⟩
  rcases Commons.Analysis.MeasureTheory.harmonic_cosine_integral_axis_scalar (n := n) (k := k) hn2 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro u
  obtain ⟨L, hLu⟩ := Fh1.exists_isometry_unit (n := n) (e0Vec n) (u : E n) (e0Vec_unit n)
    (mem_sphere_zero_iff_norm.mp u.2)
  let Q : MvPolynomial (Fin n) ℝ := Fh2.substA n L P
  have hQh : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
    dsimp [Q]
    exact Fh2.substA_mem_homogeneous n L hPh
  have hQlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) = 0 := by
    dsimp [Q]
    rw [Fh2.substA_lap n L P, hPlap]
    simp [Fh2.substA]
  have hrot := cosine_transform_rotate n L P
  -- hrot : ∫ |⟨e0,θ⟩| σ(Q) θ = ∫ |⟨L e0, θ⟩| σ(P) θ
  have hQeval : MvPolynomial.eval (fun i : Fin n => (e0Vec n) i) Q =
      MvPolynomial.eval (fun i : Fin n => (u : E n) i) P := by
    dsimp [Q]
    calc
      MvPolynomial.eval (fun i : Fin n => (e0Vec n) i) (Fh2.substA n L P)
          = MvPolynomial.eval (fun i : Fin n => ((L : E n → E n) (e0Vec n)) i) P :=
            substA_eval_coord n L P (e0Point n)
      _ = MvPolynomial.eval (fun i : Fin n => (u : E n) i) P := by
            congr 1
            rw [hLu]
  have hax := hc Q hQh hQlap
  -- hax : ∫ |⟨e0,θ⟩| σ(Q) θ = c * eval(coords (e0Vec n)) Q
  have hmain : (∫ θ : S n, |inner ℝ (u : E n) (θ : E n)| *
        MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P ∂MeasureTheory.volume.toSphere) =
      c * MvPolynomial.eval (fun i : Fin n => (u : E n) i) P := by
    calc
      (∫ θ : S n, |inner ℝ (u : E n) (θ : E n)| *
            MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
          ∂MeasureTheory.volume.toSphere)
          = (∫ θ : S n, |inner ℝ (e0Vec n) (θ : E n)| *
              MvPolynomial.eval (fun i : Fin n => (θ : E n) i) Q
            ∂MeasureTheory.volume.toSphere) := by
            rw [hLu] at hrot
            -- hrot : ∫ |⟨e0,θ⟩| σ(Q) θ = ∫ |⟨u,θ⟩| σ(P) θ (after rw hLu in the target of equality)
            exact hrot.symm
      _ = c * MvPolynomial.eval (fun i : Fin n => (e0Vec n) i) Q := by
            exact hax
      _ = c * MvPolynomial.eval (fun i : Fin n => (u : E n) i) P := by rw [hQeval]
  calc
    (∫ θ : S n, |inner ℝ (u : E n) (θ : E n)| * g θ ∂MeasureTheory.volume.toSphere)
        = (∫ θ : S n, |inner ℝ (u : E n) (θ : E n)| *
            MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
          ∂MeasureTheory.volume.toSphere) := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro θ
          change |inner ℝ (u : E n) (θ : E n)| * g θ =
            |inner ℝ (u : E n) (θ : E n)| *
              MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P
          rw [hgval θ]
    _ = c * MvPolynomial.eval (fun i : Fin n => (u : E n) i) P := hmain
    _ = c * g u := by rw [hgval u]

/-- final glue: either n = 1 (degenerate, handled directly) or n ≥ 2 (core). -/
lemma cosineHarmonicScalar_glue {n : ℕ} {k : ℕ} [Nonempty (Fin n)]
    (g : S n → ℝ)
    (hg : ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
      ∀ θ : S n, g θ = MvPolynomial.eval (fun i : Fin n => (θ : E n) i) P) :
    ∃ c : ℝ, ∀ u : S n,
      (∫ θ : S n, |inner ℝ (u : E n) (θ : E n)| * g θ ∂MeasureTheory.volume.toSphere) =
        c * g u := by
  classical
  by_cases hn1 : n = 1
  · subst n
    exact Commons.Analysis.MeasureTheory.cosine_harmonic_scalar_fin_one (k := k) g hg
  · haveI : NeZero n := ⟨by
        intro hz
        apply hn1
        have hnpos : 0 < n := by
          rcases ‹Nonempty (Fin n)› with ⟨i⟩
          have hi := i.isLt
          omega
        omega⟩
    have hn2 : 2 ≤ n := by
      have hnpos : 0 < n := by
        rcases ‹Nonempty (Fin n)› with ⟨i⟩
        have hi := i.isLt
        omega
      omega
    exact cosineHarmonicScalar_core (n := n) (k := k) hn2 g hg

end FhCHS5

namespace Commons.Analysis.MeasureTheory


/--
The Funk-Hecke scalar property of the cosine transform on harmonic polynomials:
for the restriction `g` of a harmonic homogeneous polynomial of degree `k` to the
unit sphere, the cosine transform `u ↦ ∫ |⟨u,θ⟩| g(θ) dθ` is proportional to `g`.
-/
theorem cosine_harmonic_scalar
    {n : ℕ} {k : ℕ} [Nonempty (Fin n)]
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hg : ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g θ = MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P) :
    ∃ c : ℝ, ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| * g θ
        ∂MeasureTheory.volume.toSphere) = c * g u := by
  simpa [FhCHS5.S, FhCHS5.E] using
    (FhCHS5.cosineHarmonicScalar_glue (n := n) (k := k) g hg)

end Commons.Analysis.MeasureTheory
