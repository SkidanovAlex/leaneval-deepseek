import Mathlib
import Submission.Work.Modular.Poisson.Periodize
import Submission.Work.Poisson.summable_intVec_zpow_neg
import Submission.Work.Poisson.summable_translates

/-!
# Summability of `𝓕 f (dᵀ k)` over `k ∈ ℤⁿ`

For a Schwartz function `f` on `EuclideanSpace ℝ (Fin n)` and a linear equivalence
`d` of `EuclideanSpace ℝ (Fin n)`, the series
`∑_{k : Fin n → ℤ} 𝓕 f (LinearMap.adjoint d k)`
converges.

The Fourier transform of a Schwartz function is again Schwartz, hence decays faster than any
polynomial. Since `d` is invertible, its adjoint is injective, and an injective linear map on a
finite-dimensional space is bounded below (`LinearMap.injective_iff_antilipschitz`); consequently
the sequence `k ↦ LinearMap.adjoint d (intVecE k)` grows at least linearly in `‖k‖`, which makes
the terms comparable to the convergent `p`-series `∑_k (1 + ‖intVec k‖) ^ (-N)`
(`Work.Poisson.summable_intVec_zpow_neg`, with `N = n + 1`).
-/

noncomputable section

open scoped FourierTransform SchwartzMap
open Filter

namespace Work.Poisson

/-- If `0 < a` and `a ≤ K * b` then `b⁻¹ ≤ K * a⁻¹` (multiply the hypothesis by `a⁻¹ b⁻¹`). -/
private lemma inv_le_mul_inv_of_le_mul {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ K * b) : b⁻¹ ≤ K * a⁻¹ := by
  have h2 : a * b⁻¹ ≤ K := by
    calc a * b⁻¹ ≤ (K * b) * b⁻¹ := mul_le_mul_of_nonneg_right h (by positivity)
      _ = K := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), mul_one]
  calc b⁻¹ = a⁻¹ * (a * b⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ha), one_mul]
    _ ≤ a⁻¹ * K := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = K * a⁻¹ := by ring

/-- The supremum norm of an integer vector is bounded by its Euclidean norm. -/
private lemma norm_intVec_le_norm_intVecE {n : ℕ} (m : Fin n → ℤ) :
    ‖Work.Modular.intVec m‖ ≤ ‖Work.Modular.intVecE m‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [Work.Modular.intVec_apply]
  simpa only [Work.Modular.intVecE_apply] using PiLp.norm_apply_le (Work.Modular.intVecE m) i

/-- A nonzero integer vector of `ℤⁿ` has sup norm at least `1`. -/
private lemma one_le_norm_intVec_of_ne_zero {n : ℕ} {m : Fin n → ℤ} (hm : m ≠ 0) :
    (1:ℝ) ≤ ‖Work.Modular.intVec m‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
  have h1 : (1:ℝ) ≤ ‖((m i : ℤ) : ℝ)‖ := by
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  refine h1.trans ?_
  simpa only [Work.Modular.intVec_apply] using norm_le_pi_norm (Work.Modular.intVec m) i

/-- **Summability of a Schwartz function along a linearily distorted integer lattice.**
If `T` is an injective linear map on finite-dimensional `EuclideanSpace ℝ (Fin n)` and `g` is a
Schwartz function, then `∑_{k : Fin n → ℤ} g (T (intVecE k))` converges. -/
theorem summable_schwartz_comp_linear {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : Function.Injective T)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Summable fun k : Fin n → ℤ => g (T (Work.Modular.intVecE k)) := by
  -- An injective linear map on a finite-dimensional space is bounded below.
  obtain ⟨K, hKpos, hK⟩ := (LinearMap.injective_iff_antilipschitz T).mp hT
  have hKb : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (K:ℝ) * ‖T x‖ := fun x => by
    simpa using hK.le_mul_dist x 0
  -- Decay of `g` at the order `N = n + 1`, which beats the rank `n` of the lattice.
  set N := n + 1 with hNdef
  obtain ⟨C, hCpos, hC'⟩ := g.decay N 0
  have hC : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖^N * ‖g x‖ ≤ C := fun x => by
    simpa using hC' x
  have hN : Fintype.card (Fin n) < N := by simp [hNdef]
  -- The `p`-series majorant over `ℤⁿ`.
  have hmaj : Summable fun m : Fin n → ℤ =>
      (C * (K:ℝ)^N * (2:ℝ)^N) * (1 + ‖Work.Modular.intVec m‖) ^ (-(N:ℤ)) :=
    (Work.Poisson.summable_intVec_zpow_neg N hN).mul_left _
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Filter.eventually_cofinite]
  -- Only `m = 0` is exceptional, and a singleton is finite.
  refine (Set.finite_singleton (0 : Fin n → ℤ)).subset ?_
  intro m hm
  by_contra hne
  have hm0 : m ≠ 0 := by simpa using hne
  have hle : ‖Work.Modular.intVec m‖ ≤ ‖Work.Modular.intVecE m‖ :=
    norm_intVec_le_norm_intVecE m
  have h1le : (1:ℝ) ≤ ‖Work.Modular.intVec m‖ := one_le_norm_intVec_of_ne_zero hm0
  -- Positivity of all the quantities involved.
  have hxpos : 0 < ‖Work.Modular.intVecE m‖ := lt_of_lt_of_le (by norm_num) (h1le.trans hle)
  have hxne : Work.Modular.intVecE m ≠ 0 := norm_pos_iff.mp hxpos
  have hTxne : T (Work.Modular.intVecE m) ≠ 0 := by
    intro h0
    exact hxne (hT (by simpa using h0))
  have hTxpos : 0 < ‖T (Work.Modular.intVecE m)‖ := norm_pos_iff.mpr hTxne
  -- `1 + ‖intVec m‖` is comparable to the Euclidean length.
  have hcomp : (1:ℝ) + ‖Work.Modular.intVec m‖ ≤ 2 * ‖Work.Modular.intVecE m‖ := by
    linarith
  -- Schwartz decay at `T (intVecE m)`.
  have hb1 : ‖g (T (Work.Modular.intVecE m))‖ ≤
      C * (‖T (Work.Modular.intVecE m)‖⁻¹)^N :=
    Work.Poisson.norm_le_mul_inv_pow g N hC (T (Work.Modular.intVecE m)) (ne_of_gt hTxpos)
  -- The two inverse comparisons coming from `‖intVecE m‖ ≤ K ‖T (intVecE m)‖` and from `hcomp`.
  have h2b : (‖T (Work.Modular.intVecE m)‖)⁻¹ ≤ (K:ℝ) * (‖Work.Modular.intVecE m‖)⁻¹ :=
    inv_le_mul_inv_of_le_mul hxpos hTxpos (hKb (Work.Modular.intVecE m))
  have h3b : (‖Work.Modular.intVecE m‖)⁻¹ ≤ (2:ℝ) * (1 + ‖Work.Modular.intVec m‖)⁻¹ :=
    inv_le_mul_inv_of_le_mul (by positivity) hxpos hcomp
  exact hm (by
    calc ‖g (T (Work.Modular.intVecE m))‖
        ≤ C * (‖T (Work.Modular.intVecE m)‖⁻¹)^N := hb1
      _ ≤ C * ((K:ℝ) * (‖Work.Modular.intVecE m‖⁻¹))^N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2b N) hCpos.le
      _ = C * (K:ℝ)^N * (‖Work.Modular.intVecE m‖⁻¹)^N := by rw [mul_pow]; ring
      _ ≤ C * (K:ℝ)^N * ((2:ℝ) * (1 + ‖Work.Modular.intVec m‖)⁻¹)^N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3b N) (by positivity)
      _ = (C * (K:ℝ)^N * (2:ℝ)^N) * (1 + ‖Work.Modular.intVec m‖) ^ (-(N:ℤ)) := by
          rw [mul_pow, zpow_neg, zpow_natCast, inv_pow]; ring)

/-- The adjoint of an invertible linear map is injective (its left inverse is the adjoint of the
inverse map). -/
private lemma injective_adjoint {n : ℕ}
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Function.Injective (LinearMap.adjoint d.toLinearMap) := by
  have hcomp : d.toLinearMap ∘ₗ d.symm.toLinearMap = 1 := by
    ext x
    simp
  have hST : LinearMap.adjoint d.symm.toLinearMap ∘ₗ LinearMap.adjoint d.toLinearMap = 1 := by
    have h := LinearMap.adjoint_comp d.toLinearMap d.symm.toLinearMap
    rw [hcomp, LinearMap.adjoint_one] at h
    exact h.symm
  intro x y hxy
  have hsub : (LinearMap.adjoint d.symm.toLinearMap)
      ((LinearMap.adjoint d.toLinearMap) (x - y)) = x - y := by
    rw [← LinearMap.comp_apply, hST]
    rfl
  rw [map_sub, hxy, sub_self, map_zero] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- **Summability of the Fourier transform on the dual lattice.**
For a linear equivalence `d` of `EuclideanSpace ℝ (Fin n)` and a Schwartz function `f`, the
Fourier transform of `f` is summable along the lattice `k ↦ LinearMap.adjoint d (intVecE k)`. -/
theorem summable_fourier_adjoint {n : ℕ}
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Summable fun k : Fin n → ℤ =>
      FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) f
        (LinearMap.adjoint d.toLinearMap (Work.Modular.intVecE k)) :=
  summable_schwartz_comp_linear (LinearMap.adjoint d.toLinearMap) (injective_adjoint d)
    (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) f)

end Work.Poisson
