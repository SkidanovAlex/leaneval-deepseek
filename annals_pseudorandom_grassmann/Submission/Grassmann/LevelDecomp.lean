import Submission.Grassmann.BilinearDegree

/-!
# The level (pure-degree) decomposition on `L(V,W)`

`projPure d f` is the (unnormalised) pure-degree-`d` part of `f`.  This file collects the
orthogonality/Pythagoras properties of the level decomposition:

* `sum_projPure`: `f = 2^{-mn} ∑_d projPure d f` (the Fourier inversion, level by level);
* `projPure_orthogonal`: different levels are orthogonal for the bilinear pairing;
* `sum_normSq_projPure`: **level Pythagoras**,
  `∑_A ‖projPure d f A‖² = 2^{mn} · levelWeight d f`,
  so that `levelWeight` (the KMS/`L(V,W)` level weight) is exactly the squared norm of the
  pure-degree-`d` component;
* `degLe_iff_projPure_eq_zero`: the degree filtration in terms of the level projections.
-/

open Matrix Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-- Fourier inversion, summed level by level. -/
lemma sum_projPure {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    (∑ d ∈ Finset.range (min m n + 1), projPure d f) = (2 : ℂ) ^ (m * n) • f := by
  funext A
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, projPure]
  rw [← fhat_inversion f A, Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.sum_eq_single X.rank]
  · rw [if_pos rfl]
  · intro d _ hd
    rw [if_neg (Ne.symm hd)]
  · intro h
    exact absurd (Finset.mem_range.mpr (by
      have h := le_min (Matrix.rank_le_height X) (Matrix.rank_le_width X); omega)) h

/-- Different levels are orthogonal for the bilinear pairing `(f,g) ↦ ∑_A f A * g A`. -/
theorem projPure_orthogonal {m n d e : ℕ} (hde : d ≠ e)
    (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), projPure d f A * projPure e g A) = 0 := by
  have h0 : (∑ X : Matrix (Fin n) (Fin m) (ZMod 2),
      fhat (projPure d f) X * fhat (projPure e g) X) = 0 := by
    refine Finset.sum_eq_zero fun X _ => ?_
    rw [fhat_projPure d f X, fhat_projPure e g X]
    by_cases hd : X.rank = d
    · have he : ¬ X.rank = e := fun h => hde (hd.symm.trans h)
      rw [if_pos hd, if_neg he]; ring
    · simp [hd]
  have h := fhat_parseval (projPure d f) (projPure e g)
  rw [h0] at h
  have h' : (2 : ℂ) ^ (m * n) * (∑ A, projPure d f A * projPure e g A) = 0 := h.symm
  exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero _ (by norm_num))

/-- **Level Pythagoras**: the squared norm of the pure-degree-`d` component is `levelWeight`. -/
theorem sum_normSq_projPure {m n d : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), ‖projPure d f A‖ ^ 2) =
      (2 : ℝ) ^ (m * n) * levelWeight (m := m) (n := n) d f := by
  have hL : (∑ X : Matrix (Fin n) (Fin m) (ZMod 2), ‖fhat (projPure d f) X‖ ^ 2) =
      (2 : ℝ) ^ (m * n) * (2 : ℝ) ^ (m * n) * levelWeight (m := m) (n := n) d f := by
    rw [levelWeight, Finset.mul_sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [fhat_projPure d f X]
    by_cases hd : X.rank = d
    · simp only [if_pos hd]
      have hz : ‖((2 : ℂ) ^ (m * n))‖ = (2 : ℝ) ^ (m * n) := by
        rw [norm_pow, Complex.norm_ofNat]
      rw [norm_mul, hz]; ring
    · simp [if_neg hd]
  have h := fhat_parseval_normSq (projPure d f)
  rw [hL] at h
  have hkey : (2 : ℝ) ^ (m * n) * ((2 : ℝ) ^ (m * n) * levelWeight (m := m) (n := n) d f) =
      (2 : ℝ) ^ (m * n) * (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), ‖projPure d f A‖ ^ 2) := by
    rw [← mul_assoc]; exact h
  exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hkey).symm

/-- The degree filtration in terms of the level projections. -/
theorem degLe_iff_projPure_eq_zero {m n d : ℕ}
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} :
    DegLe d f ↔ ∀ e, d < e → projPure e f = 0 := by
  constructor
  · intro hf e he
    funext A
    rw [projPure]
    refine Finset.sum_eq_zero fun X _ => ?_
    by_cases hX : X.rank = e
    · rw [if_pos hX, hf X (by rw [hX]; exact he), zero_mul]
    · simp [hX]
  · intro h X hX
    have hzero : projPure X.rank f = 0 := h X.rank hX
    have hf : fhat (projPure X.rank f) X = 0 := by
      rw [hzero]
      simp [fhat]
    rw [fhat_projPure X.rank f X, if_pos rfl] at hf
    exact (mul_eq_zero.mp hf).resolve_left (pow_ne_zero (m * n) (by norm_num : (2 : ℂ) ≠ 0))

end

end Submission.Grassmann
