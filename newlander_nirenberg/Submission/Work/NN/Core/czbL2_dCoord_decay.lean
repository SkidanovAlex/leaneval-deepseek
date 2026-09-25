import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.NN.Core.czB_L2_aux
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord_of_contDiff
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.hasFDerivAt_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.NN.Core.bmPotential_holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

open MeasureTheory Set Filter

/-! ## Support lemmas for `∂_k`

A function vanishing in a *neighbourhood* of a point has vanishing Fréchet derivative there, so
`∂_k` of a function supported in `eucClosedBall M` is again supported in `eucClosedBall M`, and
hence the integral of `∂_k` vanishes (integration by parts against the constant function `1`). -/

/-- The Euclidean closed ball is compact (it sits inside the closed ball of the same radius for the
ambient sup norm). -/
lemma czbL2_isCompact_eucClosedBall {n : ℕ} (R : ℝ) : IsCompact (eucClosedBall (n := n) R) := by
  refine (isCompact_closedBall (0 : Fin n → ℂ) R).of_isClosed_subset
    (isClosed_le continuous_eucNorm continuous_const) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact (pi_norm_le_eucNorm x).trans hx

lemma czbL2_isClosed_eucClosedBall {n : ℕ} (R : ℝ) : IsClosed (eucClosedBall (n := n) R) :=
  isClosed_le continuous_eucNorm continuous_const

/-- Outside the topological support a function vanishes in a neighbourhood of the point, so its
Fréchet derivative vanishes there. -/
lemma czbL2_fderiv_eq_zero_of_notMem_tsupport {n : ℕ} {g : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hx : x ∉ tsupport g) : fderiv ℝ g x = 0 := by
  have hopen : (tsupport g)ᶜ ∈ nhds x := (isClosed_tsupport g).isOpen_compl.mem_nhds hx
  have heq : g =ᶠ[nhds x] 0 := by
    filter_upwards [hopen] with y hy
    by_contra hne
    exact hy (subset_tsupport g (Function.mem_support.mpr hne))
  rw [heq.fderiv_eq]
  simp

/-- `x ↦ fderiv g x v` is compactly supported when `g` is supported in `eucClosedBall M`. -/
lemma czbL2_hasCompactSupport_fderiv_apply {n : ℕ} {g : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hsub : tsupport g ⊆ eucClosedBall (n := n) M) (v : Fin n → ℂ) :
    HasCompactSupport (fun x => fderiv ℝ g x v) := by
  rw [HasCompactSupport]
  refine (czbL2_isCompact_eucClosedBall (n := n) M).of_isClosed_subset (isClosed_tsupport _) ?_
  rw [tsupport]
  refine closure_minimal (fun x hx => ?_) (czbL2_isClosed_eucClosedBall M)
  by_contra hcon
  exact hx (by
    have h0 := czbL2_fderiv_eq_zero_of_notMem_tsupport (g := g) (x := x)
      (fun h => hcon (hsub h))
    simp [h0])

/-- `∂_k g` is compactly supported when `g` is supported in `eucClosedBall M`. -/
lemma czbL2_hasCompactSupport_dCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hsub : tsupport g ⊆ eucClosedBall (n := n) M) (k : Fin n) :
    HasCompactSupport (Work.CR.Flat.dCoord k g) := by
  rw [HasCompactSupport]
  refine (czbL2_isCompact_eucClosedBall (n := n) M).of_isClosed_subset (isClosed_tsupport _) ?_
  rw [tsupport]
  refine closure_minimal (fun x hx => ?_) (czbL2_isClosed_eucClosedBall M)
  by_contra hcon
  exact hx (by
    have h0 := czbL2_fderiv_eq_zero_of_notMem_tsupport (g := g) (x := x)
      (fun h => hcon (hsub h))
    simp [Work.CR.Flat.dCoord, h0])

/-- If `g` is supported in `eucClosedBall M` and `M < R`, then `∂_k g` vanishes at every point with
`eucNorm ≥ R`. -/
lemma czbL2_dCoord_eq_zero_of_ge_eucNorm {n : ℕ} {g : (Fin n → ℂ) → ℂ} {M R : ℝ}
    (hsub : tsupport g ⊆ eucClosedBall (n := n) M) (hMR : M < R) (k : Fin n) {x : Fin n → ℂ}
    (hx : R ≤ eucNorm x) : Work.CR.Flat.dCoord k g x = 0 := by
  have h0 := czbL2_fderiv_eq_zero_of_notMem_tsupport (g := g) (x := x) (fun h => by
    have h1 := hsub h
    rw [mem_eucClosedBall] at h1
    linarith)
  simp [Work.CR.Flat.dCoord, h0]

/-- `∂_k g` is continuous for `g` of class `C¹`. -/
lemma czbL2_continuous_dCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) (k : Fin n) :
    Continuous (Work.CR.Flat.dCoord k g) := by
  have hf : Continuous fun z : Fin n → ℂ => fderiv ℝ g z := hg.continuous_fderiv (by norm_num)
  have h1 : Continuous fun z : Fin n → ℂ => fderiv ℝ g z (Pi.single k (1 : ℂ)) :=
    hf.clm_apply continuous_const
  have h2 : Continuous fun z : Fin n → ℂ => fderiv ℝ g z (Pi.single k (Complex.I)) :=
    hf.clm_apply continuous_const
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

/-- **The total integral of `∂_k g` vanishes** for `g` of class `C¹` with compact support:
integrate by parts against the constant function `1`. -/
lemma czbL2_integral_dCoord_eq_zero {n : ℕ} {g : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hg : ContDiff ℝ 1 g) (hsub : tsupport g ⊆ eucClosedBall (n := n) M) (k : Fin n) :
    ∫ x, Work.CR.Flat.dCoord k g x = 0 := by
  have hcs : HasCompactSupport g :=
    (czbL2_isCompact_eucClosedBall (n := n) M).of_isClosed_subset (isClosed_tsupport g) hsub
  have hint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hcs
  have hfdcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hInt1 : Integrable (fun x => fderiv ℝ g x (Pi.single k (1 : ℂ))) :=
    (hfdcont.clm_apply continuous_const).integrable_of_hasCompactSupport
      (czbL2_hasCompactSupport_fderiv_apply hsub _)
  have hIntI : Integrable (fun x => fderiv ℝ g x (Pi.single k (Complex.I))) :=
    (hfdcont.clm_apply continuous_const).integrable_of_hasCompactSupport
      (czbL2_hasCompactSupport_fderiv_apply hsub _)
  have hzero : (fun x : Fin n → ℂ =>
      fderiv ℝ (fun _ : Fin n → ℂ => (1 : ℂ)) x (Pi.single k 1) * g x) = fun _ => 0 := by
    funext x; simp
  have hzeroI : (fun x : Fin n → ℂ =>
      fderiv ℝ (fun _ : Fin n → ℂ => (1 : ℂ)) x (Pi.single k Complex.I) * g x) = fun _ => 0 := by
    funext x; simp
  have h0 : Integrable (fun x : Fin n → ℂ =>
      fderiv ℝ (fun _ : Fin n → ℂ => (1 : ℂ)) x (Pi.single k 1) * g x) := by
    rw [hzero]; exact integrable_zero _ _ _
  have h0I : Integrable (fun x : Fin n → ℂ =>
      fderiv ℝ (fun _ : Fin n → ℂ => (1 : ℂ)) x (Pi.single k Complex.I) * g x) := by
    rw [hzeroI]; exact integrable_zero _ _ _
  have h := integral_mul_dCoord_eq_neg (n := n) k (u := fun _ : Fin n → ℂ => (1 : ℂ)) (v := g)
    contDiff_const hg h0 h0I (hInt1.const_mul (1 : ℂ)) (hIntI.const_mul (1 : ℂ))
    (hint.const_mul (1 : ℂ))
  have hL : (∫ x, (1 : ℂ) * Work.CR.Flat.dCoord k g x) = ∫ x, Work.CR.Flat.dCoord k g x := by
    simp
  have hR : (∫ x, Work.CR.Flat.dCoord k (fun _ : Fin n → ℂ => (1 : ℂ)) x * g x) = 0 := by
    have hfun : (fun x : Fin n → ℂ =>
        Work.CR.Flat.dCoord k (fun _ : Fin n → ℂ => (1 : ℂ)) x * g x) = fun _ => 0 := by
      funext x; simp [Work.CR.Flat.dCoord]
    rw [hfun]; simp
  rw [hL, hR] at h
  simpa using h

/-! ## The pointwise bound for `fderiv (bmKernel j)` -/

private lemma czbL2p_rpow_neg_three_quarter {z p : ℝ} (hz : 0 < z) :
    ((3:ℝ) / 4 * z) ^ (-p) = ((4:ℝ) / 3) ^ p * z ^ (-p) := by
  rw [Real.mul_rpow (by norm_num) hz.le, Real.rpow_neg (by norm_num),
    show ((3:ℝ) / 4) = ((4:ℝ) / 3)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
    Real.rpow_neg hz.le, inv_inv]

/-- **Pointwise bound for the derivative of the Bochner–Martinelli kernel.**  For `y ≠ 0`,
`‖fderiv ℝ (bmKernel j) y‖ ≤ C ‖y‖^{-2n}` (Euclidean norm), uniformly in `j`. -/
lemma czbL2p_norm_fderiv_bmKernel_le {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (y : Fin n → ℂ), y ≠ 0 →
      ‖fderiv ℝ (bmKernel j) y‖
        ≤ C * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
  refine ⟨2 * (n : ℝ) * (2 * (n : ℝ) + 1), by positivity, ?_⟩
  intro j y hy
  have hE : 0 < eucNorm y := eucNorm_pos hy
  have hpow : (eucNorm y) ^ (-(2 * (n : ℝ))) = ((eucNorm y) ^ (2 * n))⁻¹ := by
    rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hE.le,
      Real.rpow_natCast]
  have hterm : ∀ k : Fin n,
      ‖Work.CR.Flat.dCoord k (fun y => bmKernel j y) y‖
        + ‖Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) y‖
      ≤ (2 * (n : ℝ) + 1) * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
    intro k
    rw [bmCz.dCoord_bmKernel hy, bmCz.dbarCoord_bmKernel hy, hpow]
    have h1 := BmDzCzAux.norm_bmDzKernel_le k j hy
    have h2 := bmCz.norm_bmDbarKernel_le k j hy
    rw [div_eq_mul_inv] at h1 h2
    calc ‖bmDzKernel k j y‖ + ‖bmDbarKernel k j y‖
        ≤ (n : ℝ) * ((eucNorm y) ^ (2 * n))⁻¹
            + ((n : ℝ) + 1) * ((eucNorm y) ^ (2 * n))⁻¹ := add_le_add h1 h2
      _ = (2 * (n : ℝ) + 1) * ((eucNorm y) ^ (2 * n))⁻¹ := by ring
  calc ‖fderiv ℝ (fun y => bmKernel j y) y‖
      ≤ 2 * ∑ k : Fin n, (‖Work.CR.Flat.dCoord k (fun y => bmKernel j y) y‖
          + ‖Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) y‖) :=
        bmCz.norm_fderiv_le_sum_wirtinger _ _
    _ ≤ 2 * ∑ _k : Fin n, (2 * (n : ℝ) + 1) * (eucNorm y) ^ (-(2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hterm k) (by norm_num)
    _ = 2 * (n : ℝ) * (2 * (n : ℝ) + 1) * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Decay of the Bochner–Martinelli potential of mean-zero compactly supported data.** -/
lemma czbL2p_decay_zero_mean {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, Integrable (w j)) →
      (∀ j, Continuous (w j)) →
      (∀ j x, R ≤ eucNorm x → w j x = 0) →
      (∀ j, ∫ x, w j x = 0) →
      ∀ z : Fin n → ℂ, 4 * R ≤ ‖z‖ →
        ‖bmPotential w z‖ ≤ C * (∑ j, ∫ x, ‖w j x‖) * ‖z‖ ^ (-(2 * (n : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := czbL2p_norm_fderiv_bmKernel_le (n := n) hn
  refine ⟨C₀ * ((4:ℝ)/3) ^ (2 * (n : ℝ)) * R, by positivity, ?_⟩
  intro w hwint hwcont hwsup hwzero z hz
  have hzpos : 0 < ‖z‖ := by linarith
  have hcs : ∀ j, HasCompactSupport (w j) := fun j => hasCompactSupport_of_eucNorm (hwsup j)
  -- the shifted data
  have hshift : ∀ j : Fin n, ∫ x, w j (z + x) = 0 := by
    intro j
    rw [show (fun x : Fin n → ℂ => w j (z + x)) = fun x => w j (x + z) by
      funext x; rw [add_comm]]
    rw [MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y => w j y) z]
    exact hwzero j
  have hint : ∀ j : Fin n, Integrable (fun x => w j (z + x)) := fun j =>
    ((hwcont j).comp (continuous_const.add continuous_id)).integrable_of_hasCompactSupport
      ((hcs j).comp_homeomorph (Homeomorph.addLeft z))
  have hshiftnorm : ∀ j : Fin n, ∫ x, ‖w j (z + x)‖ = ∫ x, ‖w j x‖ := by
    intro j
    rw [show (fun x : Fin n → ℂ => ‖w j (z + x)‖) = fun x => (fun y => ‖w j y‖) (x + z) by
      funext x; rw [add_comm]]
    exact MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y => ‖w j y‖) z
  -- geometry on the ball around `-z`
  have hball : ∀ y : Fin n → ℂ, y ∈ Metric.closedBall (-z) R → (3:ℝ) / 4 * ‖z‖ ≤ ‖y‖ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have h1 : ‖(-z : Fin n → ℂ)‖ ≤ ‖-z - y‖ + ‖y‖ := by
      have h := norm_add_le (-z - y) y
      rwa [sub_add_cancel] at h
    rw [norm_neg] at h1
    have h2 : ‖-z - y‖ = ‖y - (-z)‖ := norm_sub_rev _ _
    rw [h2] at h1
    linarith
  -- the derivative bound on the ball
  have hM : ∀ j : Fin n, ∀ y ∈ Metric.closedBall (-z) R,
      ‖fderiv ℝ (bmKernel j) y‖
        ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) := by
    intro j y hy
    have hy1 := hball y hy
    have hypos : 0 < ‖y‖ := by linarith [hR]
    have hE : 0 < eucNorm y := lt_of_lt_of_le hypos (pi_norm_le_eucNorm y)
    have hyne : y ≠ 0 := fun h => by rw [h, eucNorm_zero] at hE; linarith
    have h1 : eucNorm y ^ (-(2 * (n : ℝ))) ≤ ((3:ℝ)/4 * ‖z‖) ^ (-(2 * (n : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (le_trans hy1 (pi_norm_le_eucNorm y)) (by linarith)
    have h2 : ((3:ℝ)/4 * ‖z‖) ^ (-(2 * (n : ℝ)))
        = ((4:ℝ)/3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) :=
      czbL2p_rpow_neg_three_quarter (p := 2 * (n : ℝ)) hzpos
    calc ‖fderiv ℝ (bmKernel j) y‖
        ≤ C₀ * eucNorm y ^ (-(2 * (n : ℝ))) := hC₀ j y hyne
      _ ≤ C₀ * ((3:ℝ)/4 * ‖z‖) ^ (-(2 * (n : ℝ))) := mul_le_mul_of_nonneg_left h1 hC₀pos.le
      _ = C₀ * ((4:ℝ)/3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) := by rw [h2]; ring
  -- the kernel-difference bound on the support of `w j (z + ·)`
  have hKdiff : ∀ j : Fin n, ∀ x : Fin n → ℂ, eucNorm (z + x) ≤ R →
      ‖bmKernel j x - bmKernel j (-z)‖
        ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) * R := by
    intro j x hxR
    have hxmem : x ∈ Metric.closedBall (-z) R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show x - -z = x + z from by abel]
      exact le_trans (pi_norm_le_eucNorm _) (by rw [add_comm]; exact hxR)
    have hzmem : (-z) ∈ Metric.closedBall (-z) R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show (-z : Fin n → ℂ) - -z = 0 from by abel, norm_zero]
      exact hR.le
    have hdiff : ∀ y ∈ Metric.closedBall (-z) R, DifferentiableAt ℝ (fun y => bmKernel j y) y := by
      intro y hy
      have hypos : 0 < ‖y‖ := by linarith [hball y hy, hR]
      have hE : 0 < eucNorm y := lt_of_lt_of_le hypos (pi_norm_le_eucNorm y)
      exact (bmCz.hasFDerivAt_bmKernel j
        (fun h => by rw [h, eucNorm_zero] at hE; linarith)).differentiableAt
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun y => bmKernel j y)
      (s := Metric.closedBall (-z) R)
      (C := C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))))
      hdiff (hM j) (convex_closedBall _ _) hzmem hxmem
    have hxd : ‖x - (-z)‖ ≤ R := by
      rw [show x - -z = x + z from by abel]
      exact le_trans (pi_norm_le_eucNorm _) (by rw [add_comm]; exact hxR)
    have hMnn : 0 ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) := by positivity
    calc ‖bmKernel j x - bmKernel j (-z)‖
        ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) * ‖x - -z‖ := hmv
      _ ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) * R :=
          mul_le_mul_of_nonneg_left hxd hMnn
  have hIntA : ∀ j : Fin n, Integrable (fun x => bmKernel j x * w j (z + x)) := fun j =>
    integrable_bmKernel_mul hn j ((hwcont j).comp (continuous_const.add continuous_id))
      ((hcs j).comp_homeomorph (Homeomorph.addLeft z))
  have hIntB : ∀ j : Fin n, Integrable (fun x => bmKernel j (-z) * w j (z + x)) := fun j =>
    (hint j).const_mul _
  -- subtract the value of the kernel at the centre
  have hmeanzero : ∀ j : Fin n, ∫ x, bmKernel j x * w j (z + x)
      = ∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x) := by
    intro j
    rw [show (fun x : Fin n → ℂ => (bmKernel j x - bmKernel j (-z)) * w j (z + x))
        = fun x => bmKernel j x * w j (z + x) - bmKernel j (-z) * w j (z + x) by
      funext x; ring]
    rw [MeasureTheory.integral_sub (hIntA j) (hIntB j), MeasureTheory.integral_const_mul,
      hshift j, mul_zero, sub_zero]
  -- the bound for a single summand
  have hbound : ∀ j : Fin n,
      ‖∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x)‖
        ≤ (C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) * R)
            * ∫ x, ‖w j x‖ := by
    intro j
    calc ‖∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x)‖
        ≤ ∫ x, ‖(bmKernel j x - bmKernel j (-z)) * w j (z + x)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖bmKernel j x - bmKernel j (-z)‖ * ‖w j (z + x)‖ := by simp_rw [norm_mul]
      _ ≤ ∫ x, (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ‖w j (z + x)‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
            ((hint j).norm.const_mul _) (Eventually.of_forall fun x => ?_)
          by_cases hx : w j (z + x) = 0
          · simp [hx]
          · have hxR : eucNorm (z + x) ≤ R :=
              le_of_lt (not_le.mp fun hcon => hx (hwsup j (z + x) hcon))
            exact mul_le_mul_of_nonneg_right (hKdiff j x hxR) (norm_nonneg _)
      _ = (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ∫ x, ‖w j (z + x)‖ :=
          MeasureTheory.integral_const_mul _ _
      _ = (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ∫ x, ‖w j x‖ := by
          rw [hshiftnorm j]
  rw [bmPotential_eq_bmPot, bmPot]
  calc ‖∑ j, ∫ x, bmKernel j x * w j (z + x)‖
      ≤ ∑ j, ‖∫ x, bmKernel j x * w j (z + x)‖ := norm_sum_le _ _
    _ = ∑ j, ‖∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x)‖ :=
        Finset.sum_congr rfl fun j _ => by rw [hmeanzero j]
    _ ≤ ∑ j, (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ∫ x, ‖w j x‖ :=
        Finset.sum_le_sum fun j _ => hbound j
    _ = ((C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * (∑ j, ∫ x, ‖w j x‖)) := by
        rw [Finset.mul_sum]
    _ = ((C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * R) * (∑ j, ∫ x, ‖w j x‖)) * ‖z‖ ^ (-(2 * (n : ℝ))) := by
        ring

/-- **The sharp decay of `∂_k (bmPotential h)`.**  For `h` of class `C²` with compact support,
every first derivative of the Bochner–Martinelli potential decays like `‖z‖^{-2n}`:
`∃ C R₀, 0 < C ∧ ∀ z, R₀ ≤ ‖z‖ → ∀ k, ‖∂_k (bmPotential h) z‖ ≤ C ‖z‖^{-2n}`.

Route.  By `Work.NN.Core.bmPotential_dCoord_eq`,
`∂_k (bmPotential h) z = Σ_l ∫ x, bmKernel l x · ∂_k h_l (z+x) dx`, i.e.
`∂_k (bmPotential h) = bmPot ((∂_k h_l)_l)`, and each `∂_k h_l` has
`∫ ∂_k h_l = 0` (integration by parts, compact support).  Hence the lemma
`Work.NN.Core.bmPotential_decay_zero_mean` (proved in `Submission/Work/NN/Core/czbL2_energy.lean`,
being finished in parallel — import it; if it is not yet available, prove the same statement
directly) applies to the data `(∂_k h_l)_l` and gives the bound `C ‖z‖^{-2n}` for `‖z‖ ≥ R₀`.
If `bmPotential_decay_zero_mean` is not importable yet, the direct proof is: for `‖z‖ ≥ 4R` with
`h` vanishing off the ball of radius `R`, each `∂_k h_l (z+·)` is supported in `B(-z,R)` where
`‖x‖ ≥ ‖z‖/2`, and `‖bmKernel l x‖ ≤ ‖x‖^{1-2n}` (`Work.CR.Flat.Cauchy.norm_bmKernel_le`), so the
integral is `≤ Σ_l ‖x‖^{1-2n}` against a mean-zero function; using the mean-zero condition
(the spherical means of `bmKernel l` vanish — `integral_bmKernel_eucShell_eq_zero` /
`integral_bmDzKernel_eucShell_eq_zero`) one may subtract the average and gain one power of
`‖z‖`, giving `O(‖z‖^{-2n})`.

In this file the route is followed literally: the statement
`Work.NN.Core.bmPotential_decay_zero_mean` is proved here directly (as
`czbL2p_decay_zero_mean`, since the module holding it does not currently build), together with the
two ingredients it needs -- the integration by parts `czbL2_integral_dCoord_eq_zero` for the
mean-zero condition, and the pointwise derivative bound `czbL2p_norm_fderiv_bmKernel_le` used in
the mean value inequality that gains the extra power of `‖z‖`. -/
theorem czbL2_dCoord_decay {n : ℕ} (hn : 0 < n) {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh : ∀ j, ContDiff ℝ 2 (h j)) (hcs : ∀ j, HasCompactSupport (h j)) :
    ∃ C R₀ : ℝ, 0 < C ∧ ∀ z : Fin n → ℂ, R₀ ≤ ‖z‖ → ∀ k : Fin n,
      ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ C * ‖z‖ ^ (-(2 * (n : ℝ))) := by
  have hbdd : ∀ j : Fin n, ∃ M : ℝ, tsupport (h j) ⊆ eucClosedBall (n := n) M := by
    intro j
    obtain ⟨D, hD⟩ := (hcs j).isCompact.exists_bound_of_continuousOn
      (continuous_eucNorm (n := n)).continuousOn
    exact ⟨D, fun x hx => by
      have h1 := hD x hx
      rw [Real.norm_eq_abs] at h1
      rw [mem_eucClosedBall]
      exact (le_abs_self _).trans h1⟩
  choose M hM using hbdd
  set R : ℝ := 1 + ∑ j : Fin n, max (M j) 0 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hMj : ∀ j : Fin n, M j < R := by
    intro j
    have h1 : M j ≤ max (M j) 0 := le_max_left _ _
    have h2 : max (M j) 0 ≤ ∑ i : Fin n, max (M i) 0 :=
      Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j)
    rw [hRdef]; linarith
  have hsub : ∀ j : Fin n, tsupport (h j) ⊆ eucClosedBall (n := n) (M j) := hM
  have hsm : ∀ j : Fin n, ContDiff ℝ 1 (h j) := fun j => (hh j).of_le (by norm_num)
  obtain ⟨C, hCnn, hC⟩ := czbL2p_decay_zero_mean (n := n) hn hRpos
  set S : ℝ := ∑ k : Fin n, ∑ l : Fin n, ∫ x : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (h l) x‖
    with hSdef
  refine ⟨max (C * S) 0 + 1, 4 * R, by positivity, ?_⟩
  intro z hz k
  have hd : Work.CR.Flat.dCoord k (bmPotential h) z
      = bmPotential (fun l => Work.CR.Flat.dCoord k (h l)) z := by
    rw [bmPotential_dCoord_eq hn hsm hcs k z, bmPotential_eq_bmPot]
    rfl
  rw [hd]
  have hInt : ∀ l : Fin n, Integrable ((fun l => Work.CR.Flat.dCoord k (h l)) l) := fun l =>
    (czbL2_continuous_dCoord (hsm l) k).integrable_of_hasCompactSupport
      (czbL2_hasCompactSupport_dCoord (hsub l) k)
  have hCont : ∀ l : Fin n, Continuous ((fun l => Work.CR.Flat.dCoord k (h l)) l) := fun l =>
    czbL2_continuous_dCoord (hsm l) k
  have hSupp : ∀ l : Fin n, ∀ x : Fin n → ℂ,
      R ≤ eucNorm x → (fun l => Work.CR.Flat.dCoord k (h l)) l x = 0 := fun l x hx =>
    czbL2_dCoord_eq_zero_of_ge_eucNorm (hsub l) (hMj l) k hx
  have hZero : ∀ l : Fin n, ∫ x, (fun l => Work.CR.Flat.dCoord k (h l)) l x = 0 := fun l =>
    czbL2_integral_dCoord_eq_zero (hsm l) (hsub l) k
  have hbound := hC (fun l => Work.CR.Flat.dCoord k (h l)) hInt hCont hSupp hZero z hz
  have hr : 0 ≤ ‖z‖ ^ (-(2 * (n : ℝ))) := Real.rpow_nonneg (norm_nonneg z) _
  have hTnn : 0 ≤ ∑ l : Fin n, ∫ x : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (h l) x‖ :=
    Finset.sum_nonneg fun l _ => integral_nonneg fun x => norm_nonneg _
  have hle : ∑ l : Fin n, ∫ x : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (h l) x‖ ≤ S := by
    rw [hSdef]
    refine Finset.single_le_sum (f := fun k' : Fin n =>
      ∑ l : Fin n, ∫ x : Fin n → ℂ, ‖Work.CR.Flat.dCoord k' (h l) x‖) (fun k' _ => ?_)
      (Finset.mem_univ k)
    exact Finset.sum_nonneg fun l _ => integral_nonneg fun x => norm_nonneg _
  calc ‖bmPotential (fun l => Work.CR.Flat.dCoord k (h l)) z‖
      ≤ (C * ∑ l : Fin n, ∫ x : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (h l) x‖)
          * ‖z‖ ^ (-(2 * (n : ℝ))) := hbound
    _ ≤ (max (C * S) 0 + 1) * ‖z‖ ^ (-(2 * (n : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ hr
        have h1 : C * (∑ l : Fin n, ∫ x : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (h l) x‖)
            ≤ max (C * S) 0 :=
          le_trans (mul_le_mul_of_nonneg_left hle hCnn) (le_max_left _ _)
        linarith

end Work.NN.Core
