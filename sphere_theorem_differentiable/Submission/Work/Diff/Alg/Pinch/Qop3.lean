import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qop2
import Submission.Work.Diff.Alg.Pinch.secondVariation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Assembly lemmas for `Work.Diff.Alg.Pinch.inPIC2_Q_pointwise`

* `Rm R` and `Tmat R X` are Hermitian (pair symmetry of `R`);
* the Hermitian form of an algebraic curvature tensor is real-valued;
* the second-variation input gives nonnegativity of `Phi R (adF X v) (bar (adF X v))` for *every*
  `v` (reduction to the skew part via `skewPart`);
* `Tmat R X` is positive semidefinite and the trace hypothesis of `trace_mul_posSemidef` holds.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-! ## Elementary star facts -/

theorem star_ite_one_zero (c : Prop) [Decidable c] :
    star (if c then (1 : ℂ) else 0) = if c then (1 : ℂ) else 0 := by
  split <;> simp

theorem star_re' (z : ℂ) : (star z).re = z.re := by simp

theorem star_im' (z : ℂ) : (star z).im = -z.im := by simp

theorem star_reR (z : ℂ) : RCLike.re (star z) = RCLike.re z := by simp

theorem star_imR (z : ℂ) : RCLike.im (star z) = - RCLike.im z := by simp

theorem star_nonneg_iff' (z : ℂ) : 0 ≤ star z ↔ 0 ≤ z := by
  rw [RCLike.nonneg_iff (K := ℂ), RCLike.nonneg_iff (K := ℂ), star_reR, star_imR, neg_eq_zero]

/-! ## The conjugate transpose of `adMat` -/

theorem adMat_conjTranspose (X : Fin n × Fin n → ℂ) :
    (adMat X)ᴴ = adMat (bar (swapF X)) := by
  ext p q
  simp only [Matrix.conjTranspose_apply, adMat, bar, swapF]
  rw [star_sub, star_mul, star_mul, star_ite_one_zero, star_ite_one_zero]
  by_cases h1 : p.2 = q.2
  · by_cases h2 : p.1 = q.1
    · simp only [if_pos h1, if_pos h2, if_pos h1.symm, if_pos h2.symm, one_mul, mul_one]
      try ring
    · simp only [if_pos h1, if_pos h1.symm, if_neg h2, if_neg (fun hc : q.1 = p.1 => h2 hc.symm),
        one_mul, mul_zero, mul_one, zero_mul]
      try ring
  · by_cases h2 : p.1 = q.1
    · simp only [if_neg h1, if_neg (fun hc : q.2 = p.2 => h1 hc.symm), if_pos h2, if_pos h2.symm,
        one_mul, mul_zero, mul_one, zero_mul]
      try ring
    · simp only [if_neg h1, if_neg (fun hc : q.2 = p.2 => h1 hc.symm), if_neg h2,
        if_neg (fun hc : q.1 = p.1 => h2 hc.symm), one_mul, mul_zero, mul_one, zero_mul]
      try ring

theorem adMat_neg (X : Fin n × Fin n → ℂ) : adMat (-X) = - adMat X := by
  ext p q
  rw [Matrix.neg_apply]
  simp only [adMat, Pi.neg_apply]
  ring

theorem adMat_conjTranspose_of_skew {X : Fin n × Fin n → ℂ} (hX : swapF X = -X) :
    (adMat X)ᴴ = - adMat (bar X) := by
  rw [adMat_conjTranspose, hX, bar_neg, adMat_neg]

/-! ## Hermitian-ness -/

theorem Rm_isHermitian (R : Curv4 n) (hR : IsAlgCurv R) : (Rm R).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro p q
  simp only [Rm, star_ofReal']
  exact congrArg (fun r : ℝ => (r : ℂ)) (hR.2.1 q.1 q.2 p.1 p.2).symm

theorem Tmat_isHermitian (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ) :
    (Tmat R X).IsHermitian := by
  have h := Rm_isHermitian R hR
  show ((adMat X)ᴴ * Rm R * adMat X)ᴴ = (adMat X)ᴴ * Rm R * adMat X
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h]
  rw [Matrix.mul_assoc]

theorem dotProduct_conjTranspose_mulVec (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (v z : Fin n × Fin n → ℂ) :
    (star v) ⬝ᵥ (Mᴴ *ᵥ z) = (star (M *ᵥ v)) ⬝ᵥ z := by
  rw [Matrix.dotProduct_mulVec]
  simp only [dotProduct, vecMul, Matrix.mulVec, Matrix.conjTranspose_apply, star_sum, star_mul,
    Pi.star_apply, Finset.sum_mul]

/-! ## The Hermitian form of an algebraic curvature tensor -/

theorem Phi_bar_symm (R : Curv4 n) (hR : IsAlgCurv R) (X Y : Fin n × Fin n → ℂ) :
    Phi R Y (bar X) = star (Phi R X (bar Y)) := by
  have key : star (Phi R X (bar Y))
      = ∑ p, ∑ q, (R p.1 p.2 q.1 q.2 : ℂ) * star (X p) * Y q := by
    simp only [Phi, bar]
    rw [star_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [star_sum]
    apply Finset.sum_congr rfl; intro q _
    simp only [star_mul, star_ofReal', star_star]
    ring
  rw [key]
  simp only [Phi, bar]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  rw [hR.2.1 q.1 q.2 p.1 p.2]
  ring

theorem Phi_self_real (R : Curv4 n) (hR : IsAlgCurv R) (W : Fin n × Fin n → ℂ) :
    Phi R W (bar W) = star (Phi R W (bar W)) := by
  have h := Phi_bar_symm R hR W W
  simpa using h

theorem Phi_self_im (R : Curv4 n) (hR : IsAlgCurv R) (W : Fin n × Fin n → ℂ) :
    (Phi R W (bar W)).im = 0 := by
  have h := congrArg Complex.im (Phi_self_real R hR W)
  rw [star_im'] at h
  linarith

theorem Phi_self_nonneg_iff (R : Curv4 n) (hR : IsAlgCurv R) (W : Fin n × Fin n → ℂ) :
    0 ≤ Phi R W (bar W) ↔ 0 ≤ (Phi R W (bar W)).re := by
  rw [RCLike.nonneg_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, Phi_self_im R hR W⟩⟩

theorem Phi_add₁ (R : Curv4 n) (X X' Y : Fin n × Fin n → ℂ) :
    Phi R (X + X') Y = Phi R X Y + Phi R X' Y := by
  simp only [Phi, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem Phi_add₂ (R : Curv4 n) (X Y Y' : Fin n × Fin n → ℂ) :
    Phi R X (Y + Y') = Phi R X Y + Phi R X Y' := by
  simp only [Phi, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem Phi_self_star (R : Curv4 n) (hR : IsAlgCurv R) (W : Fin n × Fin n → ℂ) :
    (star W) ⬝ᵥ (Rop R W) = star (Phi R W (bar W)) := by
  simp only [Phi, bar, Rop, Rm, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [star_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [star_sum]
  apply Finset.sum_congr rfl; intro q _
  rw [Pi.star_apply]
  simp only [star_mul, star_ofReal', star_star]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-! ## Positivity on `im (adF X)` -/

theorem Phi_sym_left_zero (R : Curv4 n) (hR : IsAlgCurv R) {A : Fin n × Fin n → ℂ}
    (hA : swapF A = A) (Y : Fin n × Fin n → ℂ) : Phi R A Y = 0 := by
  have hA'' : ∀ p : Fin n × Fin n, A (p.2, p.1) = A p := by
    intro p; have := congrFun hA p; simpa [swapF] using this
  simp only [Phi]
  rw [show (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, (R p.1 p.2 q.1 q.2 : ℂ) * A p * Y q)
        = ∑ q : Fin n × Fin n, (∑ p : Fin n × Fin n, (R p.1 p.2 q.1 q.2 : ℂ) * A p) * Y q from by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro q _
      rw [Finset.sum_mul]]
  apply Finset.sum_eq_zero; intro q _
  have hzero : (∑ p : Fin n × Fin n, (R p.1 p.2 q.1 q.2 : ℂ) * A p) = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro a _
      show (R a.1 a.2 q.1 q.2 : ℂ) * A a + (R a.2 a.1 q.1 q.2 : ℂ) * A (a.2, a.1) = 0
      rw [hA'' a, hR.1 a.1 a.2 q.1 q.2]
      push_cast
      ring
    · intro a _ hf h
      apply hf
      have hdiag : a.1 = a.2 := by
        simpa using (congrArg Prod.snd h)
      have h2 : R a.2 a.1 q.1 q.2 = - R a.1 a.2 q.1 q.2 := hR.1 a.1 a.2 q.1 q.2
      rw [hdiag] at h2
      have hz : R a.2 a.2 q.1 q.2 = 0 := by linarith
      show (R a.1 a.2 q.1 q.2 : ℂ) * A a = 0
      rw [hdiag, hz]
      simp
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact Prod.swap_swap a
  rw [hzero, zero_mul]

theorem Phi_sym_right_zero (R : Curv4 n) (hR : IsAlgCurv R) {A : Fin n × Fin n → ℂ}
    (hA : swapF A = A) (Y : Fin n × Fin n → ℂ) : Phi R Y (bar A) = 0 := by
  have hA'' : ∀ p : Fin n × Fin n, A (p.2, p.1) = A p := by
    intro p; have := congrFun hA p; simpa [swapF] using this
  simp only [Phi, bar]
  rw [show (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
              (R p.1 p.2 q.1 q.2 : ℂ) * Y p * star (A q))
        = ∑ p : Fin n × Fin n, Y p
            * (∑ q : Fin n × Fin n, (R p.1 p.2 q.1 q.2 : ℂ) * star (A q)) from by
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      ring]
  apply Finset.sum_eq_zero; intro p _
  have hzero : (∑ q : Fin n × Fin n, (R p.1 p.2 q.1 q.2 : ℂ) * star (A q)) = 0 := by
    refine Finset.sum_involution (fun q _ => q.swap) ?_ ?_ ?_ ?_
    · intro a _
      show (R p.1 p.2 a.1 a.2 : ℂ) * star (A a)
        + (R p.1 p.2 a.2 a.1 : ℂ) * star (A (a.2, a.1)) = 0
      rw [hA'' a, Work.Diff.Alg.Q2P.IsAlgCurv_antisym₃₄ hR p.1 p.2 a.1 a.2]
      push_cast
      ring
    · intro a _ hf h
      apply hf
      have hdiag : a.1 = a.2 := by
        simpa using (congrArg Prod.snd h)
      have h2 : R p.1 p.2 a.2 a.1 = - R p.1 p.2 a.1 a.2 :=
        Work.Diff.Alg.Q2P.IsAlgCurv_antisym₃₄ hR p.1 p.2 a.1 a.2
      rw [hdiag] at h2
      have hz : R p.1 p.2 a.2 a.2 = 0 := by linarith
      show (R p.1 p.2 a.1 a.2 : ℂ) * star (A a) = 0
      rw [hdiag, hz]
      simp
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact Prod.swap_swap a
  rw [hzero, mul_zero]

/-- The second-variation input, in terms of `adF`. -/
theorem good_adF (R : Curv4 n) (hR : IsAlgCurv R) (hPIC : InPIC2 R) {ζ η : Fin n → ℂ}
    (h0 : Phi R (wedgeF ζ η) (bar (wedgeF ζ η)) = 0) {Y : Fin n × Fin n → ℂ}
    (hY : swapF Y = -Y) :
    0 ≤ (Phi R (adF Y (wedgeF ζ η)) (bar (adF Y (wedgeF ζ η)))).re := by
  have h := secondVariation n R hR hPIC ζ η (matVec Y ζ) (matVec Y η) h0
  rw [adF_shear hY ζ η]
  exact h

theorem Phi_neg_neg (R : Curv4 n) (Z : Fin n × Fin n → ℂ) :
    Phi R (-Z) (bar (-Z)) = Phi R Z (bar Z) := by
  simp only [Phi, bar, Pi.neg_apply, star_neg]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  ring

/-- For skew `Y`, the direction `adF X Y` is nonnegative for `Phi R`. -/
theorem good_adF_skew (R : Curv4 n) (hR : IsAlgCurv R) (hPIC : InPIC2 R) {ζ η : Fin n → ℂ}
    (h0 : Phi R (wedgeF ζ η) (bar (wedgeF ζ η)) = 0) {Y : Fin n × Fin n → ℂ}
    (hY : swapF Y = -Y) :
    0 ≤ (Phi R (adF (wedgeF ζ η) Y) (bar (adF (wedgeF ζ η) Y))).re := by
  have h := good_adF R hR hPIC h0 hY
  have hneg : adF (wedgeF ζ η) Y = - adF Y (wedgeF ζ η) := by
    funext p
    simp only [adF, Pi.neg_apply]
    ring
  rw [hneg, Phi_neg_neg]
  exact h

/-- The same for an arbitrary vector: the symmetric part is invisible to `Phi R`. -/
theorem good_any (R : Curv4 n) (hR : IsAlgCurv R) (hPIC : InPIC2 R) {ζ η : Fin n → ℂ}
    (h0 : Phi R (wedgeF ζ η) (bar (wedgeF ζ η)) = 0) (V : Fin n × Fin n → ℂ) :
    0 ≤ (Phi R (adF (wedgeF ζ η) V) (bar (adF (wedgeF ζ η) V))).re := by
  have hsym : swapF (adF (wedgeF ζ η) (symPart V)) = adF (wedgeF ζ η) (symPart V) := by
    conv_lhs => rw [← swapF_symPart V]
    rw [← adF_swap_of_skew (swapF_wedgeF ζ η) (symPart V), swapF_swapF]
  have hskew : swapF (adF (wedgeF ζ η) (skewPart V)) = - adF (wedgeF ζ η) (skewPart V) := by
    have h1 : skewPart V = - swapF (skewPart V) := by rw [swapF_skewPart]; abel
    conv_lhs => rw [h1]
    rw [adF_neg, swapF_neg, adF_swap_of_skew (swapF_wedgeF ζ η) (swapF (skewPart V)),
      swapF_swapF]
  have hdecomp : adF (wedgeF ζ η) V
      = adF (wedgeF ζ η) (symPart V) + adF (wedgeF ζ η) (skewPart V) := by
    rw [← adF_add]
    congr 1
    exact (symPart_add_skewPart V).symm
  have hmain : 0 ≤ (Phi R (adF (wedgeF ζ η) (skewPart V))
      (bar (adF (wedgeF ζ η) (skewPart V)))).re :=
    good_adF_skew R hR hPIC h0 (swapF_skewPart V)
  have hAA : Phi R (adF (wedgeF ζ η) (symPart V)) (bar (adF (wedgeF ζ η) (symPart V))) = 0 :=
    Phi_sym_left_zero R hR hsym (bar (adF (wedgeF ζ η) (symPart V)))
  have hAB : Phi R (adF (wedgeF ζ η) (symPart V)) (bar (adF (wedgeF ζ η) (skewPart V))) = 0 :=
    Phi_sym_left_zero R hR hsym (bar (adF (wedgeF ζ η) (skewPart V)))
  have hBA : Phi R (adF (wedgeF ζ η) (skewPart V)) (bar (adF (wedgeF ζ η) (symPart V))) = 0 :=
    Phi_sym_right_zero R hR hsym (adF (wedgeF ζ η) (skewPart V))
  have hsum : Phi R (adF (wedgeF ζ η) V) (bar (adF (wedgeF ζ η) V))
      = Phi R (adF (wedgeF ζ η) (skewPart V)) (bar (adF (wedgeF ζ η) (skewPart V))) := by
    rw [hdecomp, bar_add, Phi_add₁, Phi_add₂, Phi_add₂, hAA, hAB, hBA]
    ring

  rw [hsum]
  exact hmain

theorem Phi_comm (R : Curv4 n) (hR : IsAlgCurv R) (X Y : Fin n × Fin n → ℂ) :
    Phi R X Y = Phi R Y X := by
  simp only [Phi]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  rw [hR.2.1 q.1 q.2 p.1 p.2]
  ring

end Work.Diff.Alg.Pinch
