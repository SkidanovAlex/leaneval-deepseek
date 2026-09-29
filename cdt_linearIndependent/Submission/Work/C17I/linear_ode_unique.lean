import Mathlib
import Submission.Work.C17I.defs

/-!
# Uniqueness of the solutions of a first order linear ODE system

`Work.C17I.linear_ode_unique` states that two solutions `Y`, `Z` of the (possibly
inhomogeneous) linear system

`Y' (z) = A z · Y z + b z`

on a convex set `S ⊆ ℂ`, with `A` continuous on `S`, which agree at a single point `z₀ ∈ S`,
agree on all of `S`.

The proof reduces to the homogeneous system satisfied by the difference `W = Y - Z` and then
applies Grönwall's inequality along the segment from `z₀` to a given point `z ∈ S`
(`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`), the coefficient of the relevant
linear estimate being the sup norm of the matrix `A` on that segment.

Note that no regularity of the inhomogeneity `b` is needed: it cancels in the difference.
-/

namespace Work.C17I

open scoped Topology
open Set

/-- Supremum norm bound for the linear map `y ↦ (∑ j, A i j * y j)` on `Fin k → ℂ`. -/
lemma norm_vecMap_le {k : ℕ} (hk : 0 < k) (A : Fin k → Fin k → ℂ) (y : Fin k → ℂ) :
    ‖(fun i => ∑ j, A i j * y j)‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖y‖ := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  have h1 : ‖∑ j, A i j * y j‖ ≤ (∑ j, ‖A i j‖) * ‖y‖ := by
    calc ‖∑ j, A i j * y j‖ ≤ ∑ j, ‖A i j * y j‖ := norm_sum_le _ _
      _ = ∑ j, ‖A i j‖ * ‖y j‖ := by simp
      _ ≤ ∑ j, ‖A i j‖ * ‖y‖ :=
            Finset.sum_le_sum
              (fun j _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm y j) (norm_nonneg _))
      _ = (∑ j, ‖A i j‖) * ‖y‖ := by rw [Finset.sum_mul]
  calc ‖∑ j, A i j * y j‖ ≤ (∑ j, ‖A i j‖) * ‖y‖ := h1
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
        exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
          (Finset.mem_univ i)

set_option linter.unusedVariables false in
/-- **Uniqueness of solutions of a linear ODE system.** Two solutions `Y`, `Z` of the linear
system `Y' = A z · Y + b z` on a convex set `S ⊆ ℂ`, with `A` continuous on `S`, which agree at
one point of `S` agree on all of `S`. -/
theorem linear_ode_unique {k : ℕ} {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S)
    (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (hA : ContinuousOn A S)
    (Y Z : ℂ → Fin k → ℂ)
    (hY : ∀ z ∈ S, HasDerivAt Y (fun i => ∑ j, A z i j * Y z j + b z i) z)
    (hZ : ∀ z ∈ S, HasDerivAt Z (fun i => ∑ j, A z i j * Z z j + b z i) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (h0 : Y z₀ = Z z₀) :
    ∀ z ∈ S, Y z = Z z := by
  rcases k with _ | k
  · -- the trivial case of the empty index type
    intro z _
    funext i
    exact i.elim0
  intro z hz
  -- the difference of the two solutions solves the homogeneous linear system
  let W : ℂ → Fin (k + 1) → ℂ := fun u i => Y u i - Z u i
  have hW : ∀ u ∈ S, HasDerivAt W (fun i => ∑ j, A u i j * W u j) u := by
    intro u hu
    have hY' := hasDerivAt_pi.mp (hY u hu)
    have hZ' := hasDerivAt_pi.mp (hZ u hu)
    have h := hasDerivAt_pi.mpr (fun i => (hY' i).sub (hZ' i))
    refine h.congr_deriv ?_
    funext i
    dsimp only [W]
    rw [Finset.sum_congr rfl (fun j _ => mul_sub (A u i j) (Y u j) (Z u j)),
      Finset.sum_sub_distrib]
    ring
  -- the segment from `z₀` to `z`, which lies in `S` by convexity
  let γ : ℝ → ℂ := fun t => z₀ + t • (z - z₀)
  have hγS : MapsTo γ (Icc (0 : ℝ) 1) S := fun t ht => hS.add_smul_sub_mem hz₀ hz ht
  have hγcont : Continuous γ := by fun_prop
  have hWcont : ContinuousOn W S := fun u hu => (hW u hu).continuousAt.continuousWithinAt
  have hfcont : ContinuousOn (W ∘ γ) (Icc (0 : ℝ) 1) := hWcont.comp hγcont.continuousOn hγS
  -- the derivative of `t ↦ W (γ t)`
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (W ∘ γ)
        ((z - z₀) • (fun i => ∑ j, A (γ t) i j * W (γ t) j)) (Ici t) t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    have hγ' : HasDerivAt γ (z - z₀) t := by
      dsimp only [γ]
      simpa using (((hasDerivAt_id t).smul_const (z - z₀)).const_add z₀)
    exact (HasDerivAt.scomp t (hW (γ t) (hγS htI)) hγ').hasDerivWithinAt
  -- a uniform bound for the coefficient along the segment
  have hgcont : ContinuousOn (fun t => ∑ i, ∑ j, ‖A (γ t) i j‖) (Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn (fun t => A (γ t)) (Icc (0 : ℝ) 1) :=
      hA.comp hγcont.continuousOn hγS
    have h2 : ∀ i j, ContinuousOn (fun t => A (γ t) i j) (Icc (0 : ℝ) 1) := fun i j =>
      (continuousOn_pi.mp (continuousOn_pi.mp h1 i)) j
    refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
    refine continuousOn_finsetSum Finset.univ (fun j _ => ?_)
    exact continuous_norm.comp_continuousOn (h2 i j)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgcont
  -- the linear Grönwall bound
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖(z - z₀) • (fun i => ∑ j, A (γ t) i j * W (γ t) j)‖
        ≤ (‖z - z₀‖ * C) * ‖W (γ t)‖ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    have hCt : (∑ i, ∑ j, ‖A (γ t) i j‖) ≤ C := by
      have h := hC t htI
      rwa [Real.norm_of_nonneg] at h
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
    have hb := norm_vecMap_le (Nat.succ_pos k) (A (γ t)) (W (γ t))
    calc ‖(z - z₀) • (fun i => ∑ j, A (γ t) i j * W (γ t) j)‖
        = ‖z - z₀‖ * ‖(fun i => ∑ j, A (γ t) i j * W (γ t) j)‖ := norm_smul _ _
      _ ≤ ‖z - z₀‖ * ((∑ i, ∑ j, ‖A (γ t) i j‖) * ‖W (γ t)‖) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ ‖z - z₀‖ * (C * ‖W (γ t)‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hCt (norm_nonneg _)) (norm_nonneg _)
      _ = (‖z - z₀‖ * C) * ‖W (γ t)‖ := by ring
  -- `W` vanishes at the initial point
  have hf0 : (W ∘ γ) 0 = 0 := by
    have hz0 : W z₀ = 0 := by
      funext i
      simp [W, h0]
    simpa only [Function.comp_apply, γ, zero_smul, add_zero] using hz0
  -- Grönwall along the segment
  have hgr := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := ‖z - z₀‖ * C)
    (a := 0) (b := 1) hfcont hderiv hf0 hbound
  have h1 : W z = 0 := by
    have hz1 : γ 1 = z := by simp [γ]
    have h := hgr 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    simp only [Function.comp_apply, hz1] at h
    exact h
  -- conclude
  funext i
  have := congrFun h1 i
  dsimp only [W] at this
  exact sub_eq_zero.mp this

end Work.C17I
