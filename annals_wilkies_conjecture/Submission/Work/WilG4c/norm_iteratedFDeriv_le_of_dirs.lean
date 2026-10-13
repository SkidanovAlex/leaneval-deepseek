import Mathlib
import Submission.Work.WilG4c.Engine

open scoped BigOperators

namespace Work.WilG4c

set_option maxHeartbeats 1000000

/-- Coordinate expansion in the standard basis of `Fin N → ℝ`: `x j • e_j` is the `j`-th
coordinate vector `Pi.single j (x j)`. -/
private lemma smul_pi_single (N : ℕ) (x : Fin N → ℝ) (j : Fin N) :
    (x j) • Pi.single j (1 : ℝ) = Pi.single j (x j) := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_apply, h]

/-- Reassembly of a vector in `Fin N → ℝ` from its coordinate functions. -/
private lemma sum_pi_single_eq_self (N : ℕ) (x : Fin N → ℝ) :
    (∑ j : Fin N, Pi.single j (x j)) = x := by
  ext i
  rw [Finset.sum_apply]
  simpa using Finset.sum_pi_single i x Finset.univ

/-- The expansion of a vector in `Fin N → ℝ` in the standard basis. -/
private lemma sum_smul_single (N : ℕ) (x : Fin N → ℝ) :
    (∑ j : Fin N, (x j) • Pi.single j (1 : ℝ)) = x := by
  simpa only [smul_pi_single] using sum_pi_single_eq_self N x

/-- **Multilinear expansion bound.**  If the `m`-linear form `A = D^m G(z)` is bounded by `C` on
all tuples of coordinate directions, then it is bounded by `C * N^m` on all tuples of vectors,
after multiplying by `∏ i, ‖x i‖`.  The point is that expanding each argument in the coordinate
basis produces exactly `N^m` terms. -/
private lemma norm_expansion_bound {N m : ℕ} (G : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) (C : ℝ)
    (h : ∀ v : Fin m → Fin N, |iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1)| ≤ C)
    (x : Fin m → (Fin N → ℝ)) :
    ‖iteratedFDeriv ℝ m G z x‖ ≤ (C * (N : ℝ) ^ m) * ∏ i, ‖x i‖ := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin N → ℝ) ℝ := iteratedFDeriv ℝ m G z
  have hAeval : ∀ v : Fin m → Fin N, |A (fun k => Pi.single (v k) 1)| ≤ C := h
  have hA : A x = ∑ r : Fin m → Fin N,
      A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ)) := by
    have hmap := ContinuousMultilinearMap.map_sum A
      (fun (i : Fin m) (j : Fin N) => (x i j) • Pi.single j (1 : ℝ))
    rw [← hmap]
    exact congr_arg A (funext (fun i => (sum_smul_single N (x i)).symm))
  have hterm : ∀ r : Fin m → Fin N,
      ‖A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ))‖
        = (∏ i, |x i (r i)|) * |A (fun i => Pi.single (r i) (1 : ℝ))| := by
    intro r
    rw [ContinuousMultilinearMap.map_smul_univ, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, Finset.abs_prod]
  calc ‖A x‖
      = ‖∑ r : Fin m → Fin N, A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ))‖ := by
        rw [hA]
    _ ≤ ∑ r : Fin m → Fin N, ‖A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ))‖ :=
        norm_sum_le Finset.univ _
    _ = ∑ r : Fin m → Fin N,
          (∏ i, |x i (r i)|) * |A (fun i => Pi.single (r i) (1 : ℝ))| :=
        Finset.sum_congr rfl (fun r _ => hterm r)
    _ ≤ ∑ r : Fin m → Fin N, (∏ i, ‖x i‖) * C := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        have hprod : (∏ i, |x i (r i)|) ≤ ∏ i, ‖x i‖ :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x i) (r i))
        exact mul_le_mul hprod (hAeval r) (abs_nonneg _)
          (Finset.prod_nonneg (fun i _ => norm_nonneg _))
    _ = (Fintype.card (Fin m → Fin N) : ℝ) * ((∏ i, ‖x i‖) * C) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (C * (N : ℝ) ^ m) * ∏ i, ‖x i‖ := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
        ring

/-- The operator norm of the `m`-th iterated derivative of `G` at `z` is bounded by `N^m` times
any uniform bound on its values at the coordinate direction tuples `(Pi.single i 1)`: expanding
a tuple of unit vectors in the coordinate basis gives `N^m` terms. -/
theorem norm_iteratedFDeriv_le_of_dirs {N m : ℕ} (G : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) (C : ℝ)
    (h : ∀ v : Fin m → Fin N, |iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1)| ≤ C) :
    ‖iteratedFDeriv ℝ m G z‖ ≤ C * (N : ℝ) ^ m := by
  have hM : 0 ≤ C * (N : ℝ) ^ m := by
    by_cases hv : Nonempty (Fin m → Fin N)
    · obtain ⟨v0⟩ := hv
      exact mul_nonneg (le_trans (abs_nonneg _) (h v0)) (by positivity)
    · have hN0 : N = 0 := by
        by_contra hN
        exact hv ⟨fun _ : Fin m => (⟨0, Nat.pos_of_ne_zero hN⟩ : Fin N)⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hv ⟨fun i : Fin 0 => Fin.elim0 i⟩
      have hNpow : (N : ℝ) ^ m = 0 := by
        have h1 : (N : ℝ) = 0 := by exact_mod_cast hN0
        rw [h1, zero_pow hm0]
      simp [hNpow]
  exact ContinuousMultilinearMap.opNorm_le_bound (M := C * (N : ℝ) ^ m) hM
    (fun x => norm_expansion_bound G z C h x)

end Work.WilG4c
