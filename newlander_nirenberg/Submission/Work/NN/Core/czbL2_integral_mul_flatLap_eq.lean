import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord_of_contDiff
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Work.NN.Core

/-! ## Self-adjointness of the flat Laplacian

The flat Laplacian `flatLap f = 4 Σ_k ∂_k ∂̄_k f` (see `Work.NN.Core.czB_L2_defs`) is formally
self-adjoint: `∫ u · Δv = ∫ Δu · v` whenever the boundary terms vanish.  Here the boundary terms
are removed by the compact support of `v`; no decay assumption on `u` is needed.

The proof goes through the two "half" identities

* `∫ u · Δv = -4 Σ_k ∫ ∂̄_k u · ∂_k v`
* `∫ Δu · v = -4 Σ_k ∫ ∂̄_k u · ∂_k v`,

each obtained from the first-order integration by parts lemmas for `∂ = dCoord` and
`∂̄ = dbarCoord` (`Work.CR.Flat.integral_mul_dbarCoord_eq_neg`,
`Work.NN.Core.integral_mul_dCoord_eq_neg`), together with the commutation
`∂̄_k ∂_k = ∂_k ∂̄_k` for `C²` functions (`Work.CR.Flat.Cauchy.dbarCoord_dCoord_comm`). -/

/-- **First half of the self-adjointness identity.**  For `u ∈ C¹` and `v ∈ C²` compactly
supported,
`∫ x, u x * flatLap v x = -4 Σ_k ∫ x, ∂̄_k u x * ∂_k v x`. -/
theorem integral_mul_flatLap_eq_neg_four_sum {n : ℕ} {u v : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∫ x, u x * flatLap v x
      = -4 * ∑ k : Fin n, ∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
  have hpt : ∀ x, u x * flatLap v x
      = 4 * ∑ k : Fin n, u x * Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k v w) x := by
    intro x
    rw [flatLap_eq_sum_dbarCoord (hv.contDiffAt), ← Finset.mul_sum]
    ring
  have hInt : ∀ k : Fin n,
      Integrable (fun x => u x * Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k v w) x) := by
    intro k
    refine (hu.continuous.mul
      (continuous_dbarCoord_of_contDiff (contDiff_one_dCoord hv k) k)).integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_dbarCoord_flat (hasCompactSupport_dCoord_flat hvc k) k).mul_left
  have hIBP : ∀ k : Fin n,
      ∫ x, u x * Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k v w) x
        = -∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
    intro k
    have hd : ContDiff ℝ 1 (fun w => Work.CR.Flat.dCoord k v w) := contDiff_one_dCoord hv k
    have hcs : HasCompactSupport (fun w => Work.CR.Flat.dCoord k v w) :=
      hasCompactSupport_dCoord_flat hvc k
    refine Work.CR.Flat.integral_mul_dbarCoord_eq_neg k hu hd ?_ ?_ ?_ ?_ ?_
    · exact (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        hd.continuous).integrable_of_hasCompactSupport hcs.mul_left
    · exact (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        hd.continuous).integrable_of_hasCompactSupport hcs.mul_left
    · refine (hu.continuous.mul (((hd.continuous_fderiv (by norm_num)).clm_apply
        continuous_const))).integrable_of_hasCompactSupport ?_
      exact ((hcs.fderiv ℝ).comp_left
        (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k 1)) (by simp)).mul_left
    · refine (hu.continuous.mul (((hd.continuous_fderiv (by norm_num)).clm_apply
        continuous_const))).integrable_of_hasCompactSupport ?_
      exact ((hcs.fderiv ℝ).comp_left
        (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k Complex.I)) (by simp)).mul_left
    · exact (hu.continuous.mul hd.continuous).integrable_of_hasCompactSupport hcs.mul_left
  calc ∫ x, u x * flatLap v x
      = ∫ x, 4 * ∑ k : Fin n, u x * Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k v w) x :=
          integral_congr_ae (Eventually.of_forall hpt)
    _ = 4 * ∫ x, ∑ k : Fin n, u x * Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k v w) x :=
          integral_const_mul 4 _
    _ = 4 * ∑ k : Fin n, ∫ x, u x * Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k v w) x := by
          rw [integral_finsetSum _ (fun k _ => hInt k)]
    _ = 4 * ∑ k : Fin n, -∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
          congr 1
          exact Finset.sum_congr rfl (fun k _ => hIBP k)
    _ = -4 * ∑ k : Fin n, ∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
          rw [Finset.sum_neg_distrib]
          ring

/-- **Second half of the self-adjointness identity.**  For `u ∈ C²` and `v ∈ C¹` compactly
supported,
`∫ x, flatLap u x * v x = -4 Σ_k ∫ x, ∂̄_k u x * ∂_k v x`,
the same right-hand side as `integral_mul_flatLap_eq_neg_four_sum`. -/
theorem integral_flatLap_mul_eq_neg_four_sum {n : ℕ} {u v : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    ∫ x, flatLap u x * v x
      = -4 * ∑ k : Fin n, ∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
  have hpt : ∀ x, flatLap u x * v x
      = 4 * ∑ k : Fin n, Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x * v x := by
    intro x
    rw [flatLap_eq_sum_dbarCoord (hu.contDiffAt), ← Finset.sum_mul]
    ring
  have hcomm : ∀ k : Fin n, ∀ x,
      Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x
        = Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k u w) x :=
    fun k x => Work.CR.Flat.Cauchy.dbarCoord_dCoord_comm k k u x (hu.contDiffAt)
  have hInt : ∀ k : Fin n,
      Integrable (fun x => Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x * v x) := by
    intro k
    refine ((continuous_dbarCoord_of_contDiff (contDiff_one_dCoord hu k) k).mul
      hv.continuous).integrable_of_hasCompactSupport ?_
    exact hvc.mul_left
  have hIBP : ∀ k : Fin n,
      ∫ x, Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x * v x
        = -∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
    intro k
    have hbu : ContDiff ℝ 1 (fun x => Work.CR.Flat.dbarCoord k u x) := contDiff_one_dbarCoord hu k
    have h1u : Integrable
        (fun x => fderiv ℝ (fun x => Work.CR.Flat.dbarCoord k u x) x (Pi.single k 1) * v x) := by
      refine (((hbu.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        hv.continuous).integrable_of_hasCompactSupport ?_
      exact hvc.mul_left
    have hIu : Integrable
        (fun x => fderiv ℝ (fun x => Work.CR.Flat.dbarCoord k u x) x (Pi.single k Complex.I) * v x) := by
      refine (((hbu.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        hv.continuous).integrable_of_hasCompactSupport ?_
      exact hvc.mul_left
    have h1v : Integrable
        (fun x => (fun x => Work.CR.Flat.dbarCoord k u x) x * fderiv ℝ v x (Pi.single k 1)) := by
      refine (hbu.continuous.mul (((hv.continuous_fderiv (by norm_num)).clm_apply
        continuous_const))).integrable_of_hasCompactSupport ?_
      exact ((hvc.fderiv ℝ).comp_left
        (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k 1)) (by simp)).mul_left
    have hIv : Integrable
        (fun x => (fun x => Work.CR.Flat.dbarCoord k u x) x * fderiv ℝ v x (Pi.single k Complex.I)) := by
      refine (hbu.continuous.mul (((hv.continuous_fderiv (by norm_num)).clm_apply
        continuous_const))).integrable_of_hasCompactSupport ?_
      exact ((hvc.fderiv ℝ).comp_left
        (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k Complex.I)) (by simp)).mul_left
    have huv : Integrable (fun x => (fun x => Work.CR.Flat.dbarCoord k u x) x * v x) :=
      (hbu.continuous.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
    have h := integral_mul_dCoord_eq_neg k hbu hv h1u hIu h1v hIv huv
    have hc : ∫ x, Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x * v x
        = ∫ x, Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k u w) x * v x := by
      refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
      simp only [hcomm k x]
    rw [hc, h]
    simp
  calc ∫ x, flatLap u x * v x
      = ∫ x, 4 * ∑ k : Fin n, Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x * v x :=
          integral_congr_ae (Eventually.of_forall hpt)
    _ = 4 * ∫ x, ∑ k : Fin n, Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x * v x :=
          integral_const_mul 4 _
    _ = 4 * ∑ k : Fin n, ∫ x, Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k u w) x * v x := by
          rw [integral_finsetSum _ (fun k _ => hInt k)]
    _ = 4 * ∑ k : Fin n, -∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
          congr 1
          exact Finset.sum_congr rfl (fun k _ => hIBP k)
    _ = -4 * ∑ k : Fin n, ∫ x, Work.CR.Flat.dbarCoord k u x * Work.CR.Flat.dCoord k v x := by
          rw [Finset.sum_neg_distrib]
          ring

theorem czbL2_integral_mul_flatLap_eq {n : ℕ} {u v : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∫ x, u x * Work.NN.Core.flatLap v x = ∫ x, Work.NN.Core.flatLap u x * v x := by
  rw [integral_mul_flatLap_eq_neg_four_sum (hu.of_le (by norm_num)) hv hvc,
      integral_flatLap_mul_eq_neg_four_sum hu (hv.of_le (by norm_num)) hvc]

end Work.NN.Core
