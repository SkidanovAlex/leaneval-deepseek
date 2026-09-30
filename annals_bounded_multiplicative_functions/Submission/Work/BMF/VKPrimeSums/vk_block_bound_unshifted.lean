import Mathlib
import Submission.Work.BMF.zeta_growth_defs
import Submission.Work.BMF.abel_ioc_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Filter
open scoped Topology

/-- For `σ ≥ 0` and `0 < x ≤ y`, the map `z ↦ z ^ (-σ)` is non-increasing. -/
private lemma rpow_neg_anti {σ : ℝ} (hσ : 0 ≤ σ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y ^ (-σ) ≤ x ^ (-σ) := by
  have hy : 0 ≤ y := le_trans hx.le hxy
  rw [Real.rpow_neg hy, Real.rpow_neg hx.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx σ) (Real.rpow_le_rpow hx.le hxy hσ)

/-- The unshifted (`u = 0`) form of the Vinogradov–Korobov exponential-sum bound, obtained from
`VKExpSum` by letting the shift `u ↓ 0`.  The summand depends continuously on `u` at `0`, since
the base `n + u` stays in the slit plane, so the uniform bound passes to the limit. -/
private lemma vk_unshifted_block_aux (C D : ℝ) (hVK : Work.BMF.VKExpSum C D)
    (N R : ℕ) (T : ℝ) (hN : 2 ≤ N) (hNT : (N : ℝ) ≤ T) (hR1 : N < R) (hR2 : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc N R, ((n : ℂ) ^ (-(Complex.I * (T : ℂ))))‖ ≤
      C * (N : ℝ) ^ (1 - 1 / (D * (Real.log T / Real.log N) ^ 2)) := by
  have hcont : ContinuousAt (fun u : ℝ => ∑ n ∈ Finset.Ioc N R,
      (((n : ℝ) + u : ℝ) : ℂ) ^ (-(Complex.I * (T : ℂ)))) 0 :=
    tendsto_finsetSum (Finset.Ioc N R) (fun n hn => by
      have hn0 : n ≠ 0 := by have h := (Finset.mem_Ioc.mp hn).1; omega
      exact ContinuousAt.cpow (f := (fun u : ℝ => (((n : ℝ) + u : ℝ) : ℂ)))
        (g := fun _ : ℝ => (-(Complex.I * (T : ℂ)))) (by fun_prop) continuousAt_const
        (by simpa using (Complex.natCast_mem_slitPlane.mpr hn0)))
  have hu_mem : ∀ k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ∈ Set.Ioc (0 : ℝ) 1 := by
    intro k
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  have hbound : ∀ k : ℕ, ‖∑ n ∈ Finset.Ioc N R,
      (((n : ℝ) + (1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ ≤
      C * (N : ℝ) ^ (1 - 1 / (D * (Real.log T / Real.log (N : ℝ)) ^ 2)) := by
    intro k
    have hk := hu_mem k
    have hvk := hVK (N : ℝ) T (by exact_mod_cast hN) hNT ((1 : ℝ) / ((k : ℝ) + 1))
      hk.1 hk.2 (R : ℝ) (by exact_mod_cast hR1) (by exact_mod_cast hR2)
    simpa only [Nat.floor_natCast] using hvk
  have htend : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomp := hcont.tendsto.comp htend
  have hnorm : Tendsto (fun k : ℕ => ‖∑ n ∈ Finset.Ioc N R,
      (((n : ℝ) + (1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖) atTop
      (𝓝 ‖∑ n ∈ Finset.Ioc N R, (((n : ℝ) + 0 : ℝ) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖) :=
    (continuous_norm.tendsto _).comp hcomp
  have hle := le_of_tendsto' hnorm hbound
  simpa using hle

/-- **Vinogradov–Korobov block bound.**  A block of the twisted sum `∑ n^{-σ-iT}`, of length at
most `N` and starting at `N`, is bounded by the VK exponential-sum bound with the weight `N^{-σ}`
pulled out (up to the harmless factor `1 + ·`). -/
theorem vk_block_bound_unshifted (C D : ℝ) (hC : 0 < C) (hD : 0 < D) (hVK : Work.BMF.VKExpSum C D)
    (N M : ℕ) (hN : 2 ≤ N) (T σ : ℝ) (hT : 2 ≤ T) (hNT : (N : ℝ) ≤ T)
    (hM2 : M ≤ 2 * N) (hσ : 0 ≤ σ) :
    ‖∑ n ∈ Finset.Ioc N M, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
      (1 + C * (N : ℝ) ^ (1 - 1 / (D * (Real.log T / Real.log N) ^ 2))) * (N : ℝ) ^ (-σ) := by
  let e : ℝ := 1 - 1 / (D * (Real.log T / Real.log (N : ℝ)) ^ 2)
  let B : ℝ := C * (N : ℝ) ^ e
  change ‖∑ n ∈ Finset.Ioc N M, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
    (1 + B) * (N : ℝ) ^ (-σ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB : 0 ≤ B := by
    change 0 ≤ C * (N : ℝ) ^ e
    exact mul_nonneg hC.le (Real.rpow_nonneg hNpos.le _)
  by_cases hNM : M ≤ N
  · have hempty : Finset.Ioc N M = ∅ := Finset.Ioc_eq_empty (not_lt.mpr hNM)
    rw [hempty, Finset.sum_empty, norm_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hNpos.le _)
  · rw [not_le] at hNM
    have hstep := abel_ioc_bound (a := fun n => (n : ℂ) ^ (-(Complex.I * (T : ℂ))))
        (w := fun n => (n : ℝ) ^ (-σ))
        (N := N) (M := M) (B := B) hNM hB
        (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))
        (fun n hn1 _ => rpow_neg_anti hσ (by exact_mod_cast (by omega : 0 < n))
          (by push_cast; linarith))
        (fun k hk1 hk2 => vk_unshifted_block_aux C D hVK N k T hN hNT hk1 (le_trans hk2 hM2))
    have hsum_eq : ∑ n ∈ Finset.Ioc N M, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (T : ℂ)))
        = ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hnne : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
      rw [Complex.ofReal_cpow hnp.le (-σ)]
      simp only [Complex.ofReal_natCast]
      rw [Complex.ofReal_neg]
      rw [← Complex.cpow_add _ _ hnne]
      congr 1
      ring
    rw [hsum_eq] at hstep
    refine le_trans hstep ?_
    have hwle : (((N + 1 : ℕ) : ℝ)) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
      rpow_neg_anti hσ hNpos (by push_cast; linarith)
    have hNpow : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hNpos.le _
    calc B * (((N + 1 : ℕ) : ℝ) ^ (-σ))
        = (C * (N : ℝ) ^ e) * (((N + 1 : ℕ) : ℝ) ^ (-σ)) := rfl
      _ ≤ (C * (N : ℝ) ^ e) * (N : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_left hwle (by
            change 0 ≤ C * (N : ℝ) ^ e
            exact mul_nonneg hC.le (Real.rpow_nonneg hNpos.le _))
      _ ≤ (1 + C * (N : ℝ) ^ e) * (N : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (by linarith) hNpow

end Work.BMF
