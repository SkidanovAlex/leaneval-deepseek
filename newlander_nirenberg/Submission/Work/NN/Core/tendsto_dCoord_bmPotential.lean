/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Pointwise convergence of `∂ (bmPotential F_m)` under convergence of `∂ F_m`

If `F m` (`m : ℕ`) and `f` are families of `C¹` functions on `ℂⁿ` vanishing outside the ball of
radius `ρ`, and `‖∂_k (F m)_j w - ∂_k f_j w‖ ≤ ε m` pointwise with `ε m → 0`, then for every `z`

  `∂_k (bmPotential (F m)) z → ∂_k (bmPotential f) z`.

The proof uses the integral representation
`∂_k (bmPotential g) z = Σ_j ∫ x, bmKernel j x * ∂_k g_j (z + x)`
(`Work.NN.Core.bmPotential_dCoord_eq`).  The difference of the two representations is, term by term,
the integral of `bmKernel j x * (∂_k (F m)_j (z+x) - ∂_k f_j (z+x))`; the integrand vanishes unless
`‖z + x‖ ≤ ρ`, so it is supported in a fixed ball and is dominated there by `ε m * ‖bmKernel j x‖`,
whose integral over that ball is finite (`locallyIntegrable_bmKernel`).
-/
import Mathlib
import Submission.Work.NN.Core.czbL2_smooth_aux
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.NN.Core.czB_L2_aux

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter
open Work.CR.Flat.Cauchy

namespace Work.NN.Core

theorem tendsto_dCoord_bmPotential {n : ℕ} (hn : 0 < n) (k : Fin n) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {F : ℕ → Fin n → (Fin n → ℂ) → ℂ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hFd : ∀ m j, ContDiff ℝ 1 (F m j)) (hfd : ∀ j, ContDiff ℝ 1 (f j))
    (hFk : ∀ m j, HasCompactSupport (F m j)) (hfk : ∀ j, HasCompactSupport (f j))
    (hFs : ∀ m j w, ρ ≤ ‖w‖ → F m j w = 0) (hfs : ∀ j w, ρ ≤ ‖w‖ → f j w = 0)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) (hεnn : ∀ m, 0 ≤ ε m)
    (hD : ∀ m j w, ‖Work.CR.Flat.dCoord k (F m j) w - Work.CR.Flat.dCoord k (f j) w‖ ≤ ε m) :
    ∀ z, Filter.Tendsto
      (fun m => Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential (F m)) z)
      Filter.atTop (nhds (Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential f) z)) := by
  intro z
  -- ## The integral representations of both sides
  have hrepF : ∀ m, Work.CR.Flat.dCoord k (bmPotential (F m)) z
      = ∑ l, ∫ x, bmKernel l x * Work.CR.Flat.dCoord k (F m l) (z + x) :=
    fun m => bmPotential_dCoord_eq hn (hFd m) (hFk m) k z
  have hrepf : Work.CR.Flat.dCoord k (bmPotential f) z
      = ∑ l, ∫ x, bmKernel l x * Work.CR.Flat.dCoord k (f l) (z + x) :=
    bmPotential_dCoord_eq hn hfd hfk k z
  -- ## The ball containing the support of every difference
  set B : Set (Fin n → ℂ) := Metric.closedBall (-z) ρ with hBdef
  have hBmeas : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hKint : ∀ l : Fin n, IntegrableOn (fun x => ‖bmKernel l x‖) B volume := by
    intro l
    exact ((Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn l).integrableOn_isCompact
      (isCompact_closedBall (-z) ρ)).norm
  set S : ℝ := ∑ l, ∫ x in B, ‖bmKernel l x‖ with hSdef
  -- ## Regularity and integrability of the data
  have hcontF : ∀ m l, Continuous (fun w => Work.CR.Flat.dCoord k (F m l) w) :=
    fun m l => continuous_dCoord_of_contDiff_one (hFd m l) k
  have hcsF : ∀ m l, HasCompactSupport (fun w => Work.CR.Flat.dCoord k (F m l) w) :=
    fun m l => hasCompactSupport_dCoord (hFk m l) k
  have hcontf : ∀ l, Continuous (fun w => Work.CR.Flat.dCoord k (f l) w) :=
    fun l => continuous_dCoord_of_contDiff_one (hfd l) k
  have hcsf : ∀ l, HasCompactSupport (fun w => Work.CR.Flat.dCoord k (f l) w) :=
    fun l => hasCompactSupport_dCoord (hfk l) k
  have hIntF : ∀ m l, Integrable (fun x => bmKernel l x *
      Work.CR.Flat.dCoord k (F m l) (z + x)) :=
    fun m l => integrable_bmKernel_mul_comp hn l (hcontF m l) (hcsF m l) z
  have hIntf : ∀ l, Integrable (fun x => bmKernel l x *
      Work.CR.Flat.dCoord k (f l) (z + x)) :=
    fun l => integrable_bmKernel_mul_comp hn l (hcontf l) (hcsf l) z
  -- ## The estimate in the `m`-th term and the `l`-th component
  have key : ∀ (m : ℕ) (l : Fin n),
      ‖∫ x, bmKernel l x *
          (Work.CR.Flat.dCoord k (F m l) (z + x) - Work.CR.Flat.dCoord k (f l) (z + x))‖
        ≤ ε m * ∫ x in B, ‖bmKernel l x‖ := by
    intro m l
    set D : (Fin n → ℂ) → ℂ := fun x =>
      Work.CR.Flat.dCoord k (F m l) (z + x) - Work.CR.Flat.dCoord k (f l) (z + x) with hDdef
    have hDzero : ∀ x, x ∉ B → D x = 0 := by
      intro x hx
      have hx1 : ρ < ‖x - (-z)‖ := by
        simpa only [hBdef, Metric.mem_closedBall, not_le, dist_eq_norm] using hx
      have hx2 : ρ < ‖z + x‖ := by
        rwa [sub_neg_eq_add, add_comm] at hx1
      have h := dCoord_sub_eq_zero_of_forall_norm_le k (hFs m l) (hfs l) (z + x) hx2
      simpa only [hDdef] using h
    have hDbd : ∀ x, ‖D x‖ ≤ ε m := fun x => by
      simpa only [hDdef] using hD m l (z + x)
    have hIntD : Integrable (fun x => ‖bmKernel l x‖ * ‖D x‖) := by
      have h2 : Integrable (fun x => bmKernel l x * Work.CR.Flat.dCoord k (F m l) (z + x)
          - bmKernel l x * Work.CR.Flat.dCoord k (f l) (z + x)) := (hIntF m l).sub (hIntf l)
      have h3 : Integrable (fun x => bmKernel l x * D x) :=
        h2.congr (Eventually.of_forall (fun x => by simp only [hDdef, mul_sub]))
      simpa only [norm_mul] using h3.norm
    calc ‖∫ x, bmKernel l x * D x‖
        ≤ ∫ x, ‖bmKernel l x * D x‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖bmKernel l x‖ * ‖D x‖ := by simp_rw [norm_mul]
      _ = ∫ x in B, ‖bmKernel l x‖ * ‖D x‖ :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero
              (fun x hx => by simp only [hDzero x hx, norm_zero, mul_zero])).symm
      _ ≤ ∫ x in B, ‖bmKernel l x‖ * ε m :=
            setIntegral_mono_on hIntD.integrableOn ((hKint l).mul_const (ε m)) hBmeas
              (fun x _ => mul_le_mul_of_nonneg_left (hDbd x) (norm_nonneg _))
      _ = (∫ x in B, ‖bmKernel l x‖) * ε m :=
            integral_mul_const (μ := volume.restrict B) (ε m) (fun x => ‖bmKernel l x‖)
      _ = ε m * ∫ x in B, ‖bmKernel l x‖ := by ring
  -- ## Assembling the sum
  have hmain : ∀ m, ‖Work.CR.Flat.dCoord k (bmPotential (F m)) z
      - Work.CR.Flat.dCoord k (bmPotential f) z‖ ≤ ε m * S := by
    intro m
    have hstep : ∀ l : Fin n,
        (∫ x, bmKernel l x * Work.CR.Flat.dCoord k (F m l) (z + x))
          - (∫ x, bmKernel l x * Work.CR.Flat.dCoord k (f l) (z + x))
        = ∫ x, bmKernel l x *
            (Work.CR.Flat.dCoord k (F m l) (z + x) - Work.CR.Flat.dCoord k (f l) (z + x)) := by
      intro l
      rw [← integral_sub (hIntF m l) (hIntf l)]
      exact integral_congr_ae (Eventually.of_forall (fun x => by ring))
    rw [hrepF m, hrepf, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun l _ => hstep l)]
    calc ‖∑ l, ∫ x, bmKernel l x *
            (Work.CR.Flat.dCoord k (F m l) (z + x) - Work.CR.Flat.dCoord k (f l) (z + x))‖
        ≤ ∑ l, ‖∫ x, bmKernel l x *
            (Work.CR.Flat.dCoord k (F m l) (z + x) - Work.CR.Flat.dCoord k (f l) (z + x))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ l, ε m * ∫ x in B, ‖bmKernel l x‖ := Finset.sum_le_sum (fun l _ => key m l)
      _ = ε m * S := by rw [hSdef]; exact (Finset.mul_sum _ _ _).symm
  -- ## Squeeze
  have hSlim : Filter.Tendsto (fun m => ε m * S) Filter.atTop (nhds 0) := by
    simpa using hε.mul_const S
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ))
      (h := fun m => ε m * S) tendsto_const_nhds hSlim (fun m => norm_nonneg _) hmain)

end Work.NN.Core
