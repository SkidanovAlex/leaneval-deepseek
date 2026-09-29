import Mathlib
import Submission.Work.Holonomy3.psi_pow_norm_bound
import Submission.Work.Holonomy3.psi_pow_eval_hasSum
import Submission.Work.Holonomy3.coeff_subst_tsum

/-!
# Evaluating a substituted power series

If `ψ` has vanishing constant term, evaluates at `z` to `w`, and `h` evaluates at `w` to `S`
(with absolute convergence hypotheses), then the composite series `h ∘ ψ = PowerSeries.subst ψ h`
evaluates at `z` to `S`.

The proof is a classical rearrangement.  Writing `G (d, k) = coeff d h * (coeff k (ψ ^ d) * z ^ k)`
the double series `∑_{d,k} G d k` is absolutely summable, with:
* iterated sum over `d` first: `∑_d coeff d h * w ^ d = S` (hypothesis `hh`);
* iterated sum over `k` first: `∑_k coeff k (subst ψ h) * z ^ k` by `coeff_subst_tsum`.
-/

namespace Work.Holonomy3

theorem subst_hasSum_eval {h ψ : PowerSeries ℂ} {z w S : ℂ}
    (hψ0 : PowerSeries.coeff 0 ψ = 0)
    (hψ : HasSum (fun j : ℕ => PowerSeries.coeff j ψ * z ^ j) w)
    (hh : HasSum (fun p : ℕ => PowerSeries.coeff p h * w ^ p) S)
    (habsψ : Summable (fun j : ℕ => ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j))
    (habsh : Summable (fun p : ℕ => ‖PowerSeries.coeff p h‖ *
      (∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j) ^ p)) :
    HasSum (fun k : ℕ => PowerSeries.coeff k (PowerSeries.subst ψ h) * z ^ k) S := by
  let A : ℝ := ∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j
  have key : ∀ d : ℕ, Summable (fun k : ℕ => ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖) ∧
      (∑' k : ℕ, ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖) ≤ A ^ d := psi_pow_norm_bound habsψ
  have hpow : ∀ d : ℕ, HasSum (fun k : ℕ => PowerSeries.coeff k (ψ ^ d) * z ^ k) (w ^ d) :=
    psi_pow_eval_hasSum hψ (fun d => (key d).1)
  have habsh' : Summable (fun p : ℕ => ‖PowerSeries.coeff p h‖ * A ^ p) := habsh
  have hc0 : PowerSeries.constantCoeff ψ = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hψ0
  set G : ℕ × ℕ → ℂ :=
    fun p => PowerSeries.coeff p.1 h * (PowerSeries.coeff p.2 (ψ ^ p.1) * z ^ p.2) with hGdef
  have hGnorm_fiber : ∀ d : ℕ, Summable (fun k : ℕ => ‖G (d, k)‖) := by
    intro d
    have hcongr : (fun k : ℕ => ‖G (d, k)‖) =
        fun k => ‖PowerSeries.coeff d h‖ * ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖ := by
      funext k; rw [hGdef]; simp only [norm_mul]
    rw [hcongr]
    exact ((key d).1).mul_left _
  have hnorm_eq : ∀ d : ℕ, (∑' k : ℕ, ‖G (d, k)‖) =
      ‖PowerSeries.coeff d h‖ * (∑' k : ℕ, ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖) := by
    intro d
    have hc : (fun k : ℕ => ‖G (d, k)‖) =
        fun k => ‖PowerSeries.coeff d h‖ * ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖ := by
      funext k; rw [hGdef]; simp only [norm_mul]
    rw [hc, tsum_mul_left]
  have hGtsum_aux : Summable (fun d : ℕ => ∑' k : ℕ, ‖G (d, k)‖) :=
    Summable.of_nonneg_of_le (f := fun d : ℕ => ‖PowerSeries.coeff d h‖ * A ^ d)
      (g := fun d : ℕ => ∑' k : ℕ, ‖G (d, k)‖)
      (fun d => tsum_nonneg fun k => norm_nonneg _)
      (fun d => by
        rw [hnorm_eq d]
        exact mul_le_mul_of_nonneg_left (key d).2 (norm_nonneg _))
      habsh'
  have hGnorm : Summable (fun p : ℕ × ℕ => ‖G p‖) :=
    (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖G p‖) (fun p => norm_nonneg _)).2
      ⟨hGnorm_fiber, hGtsum_aux⟩
  have hGsum : Summable G := hGnorm.of_norm
  have hGk : ∀ d : ℕ, Summable (fun k : ℕ => G (d, k)) := fun d => (hGnorm_fiber d).of_norm
  have hGtsum : (∑' p : ℕ × ℕ, G p) = S := by
    have hinner : ∀ d : ℕ, (∑' k : ℕ, G (d, k)) = PowerSeries.coeff d h * w ^ d := by
      intro d
      have hc : (fun k : ℕ => G (d, k)) =
          fun k => PowerSeries.coeff d h * (PowerSeries.coeff k (ψ ^ d) * z ^ k) := by
        funext k; rw [hGdef]
      rw [hc, tsum_mul_left, (hpow d).tsum_eq]
    rw [hGsum.tsum_prod' hGk, tsum_congr hinner]
    exact hh.tsum_eq
  have hcoeff : ∀ k : ℕ, PowerSeries.coeff k (PowerSeries.subst ψ h) * z ^ k
      = ∑' p : ℕ, G (p, k) := by
    intro k
    have hG_eq : ∀ p : ℕ, G (p, k) =
        (PowerSeries.coeff p h * PowerSeries.coeff k (ψ ^ p)) * z ^ k := by
      intro p; rw [hGdef]; ring
    rw [tsum_congr hG_eq, tsum_mul_right, ← coeff_subst_tsum hψ0 k]
  have hGk' : ∀ k : ℕ, Summable (fun p : ℕ => G (p, k)) := by
    intro k
    refine summable_of_ne_finset_zero (s := Finset.range (k + 1)) (fun p hp => ?_)
    have hkp : k < p := by
      simp only [Finset.mem_range, not_lt] at hp; omega
    have hcoeff0 : PowerSeries.coeff k (ψ ^ p) = 0 :=
      PowerSeries.coeff_of_lt_order k (lt_of_lt_of_le (by exact_mod_cast hkp)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero p hc0))
    rw [hGdef]
    simp [hcoeff0]
  have hFiber : ∀ k : ℕ, HasSum (fun p : ℕ => G (p, k))
      (PowerSeries.coeff k (PowerSeries.subst ψ h) * z ^ k) := by
    intro k
    rw [hcoeff k]
    exact (hGk' k).hasSum
  have hswap_sum : Summable (fun q : ℕ × ℕ => G (q.2, q.1)) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr hGsum
  have hpack := HasSum.prod_fiberwise (f := fun q : ℕ × ℕ => G (q.2, q.1)) hswap_sum.hasSum
    (fun k => hFiber k)
  have hswap_tsum : (∑' q : ℕ × ℕ, G (q.2, q.1)) = ∑' p : ℕ × ℕ, G p := by
    simpa [Prod.swap] using Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) G
  rw [hswap_tsum, hGtsum] at hpack
  exact hpack

end Work.Holonomy3
