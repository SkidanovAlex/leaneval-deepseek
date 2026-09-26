import Mathlib
import Submission.Work.Drive.needleDevDefs

/-!
# The Taylor bound for the deviation of a retained arc

This module proves `Work.Drive.dev_taylor_le`: for a smooth knot `r` and every `j ≥ 2` there are
constants `C, w₀ > 0` such that, uniformly over all band-arc sweep data `D` and all sweep
parameters `σ` whose retained arc is shorter than `w₀`, the deviation

  `dev r D σ ξ = r (a + ξ w) - ((1 - ξ) r a + ξ r (a + w))`,  `a = taR D σ`, `w = sweepW' D σ`,

satisfies the `j`-th order Taylor estimate

  `‖dev r D σ ξ + ξ (1-ξ) ∑_{2 ≤ k ≤ j} ((∑_{m<k-1} ξ^m) w^k / k!) r^{(k)}(a)‖ ≤ C w^{j+1}`

for every `ξ ∈ [0,1]`.

The proof is the elementary Taylor computation: writing `g t = r (a + t w)` and `P` for the
`j`-th Taylor polynomial of `g` at `0`, the bracket equals `(g ξ - P ξ) - ξ (g 1 - P 1)`
(a purely algebraic identity, proved in `Work.Drive.dev_taylor_algebra`), and both remainders are
estimated by the Lagrange remainder bound (`taylor_mean_remainder_bound`) using the global bound
`Work.Drive.exists_bound_iteratedDeriv_knot` on the `(j+1)`-st derivative, which follows from the
periodicity of the knot.

## Main results

* `Work.Drive.periodic_iteratedDeriv_of_periodic`
* `Work.Drive.exists_bound_iteratedDeriv_knot`
* `Work.Drive.iteratedDeriv_comp_affine`
* `Work.Drive.dev_taylor_algebra`
* `Work.Drive.dev_taylor_le`
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

/-! ## A global bound for the iterated derivatives of a periodic curve -/

/-- The iterated derivatives of a periodic function are periodic with the same period. -/
theorem periodic_iteratedDeriv_of_periodic {r : ℝ → Space}
    (hper : Function.Periodic r period) (m : ℕ) :
    Function.Periodic (iteratedDeriv m r) period := by
  intro x
  have h := congrFun (iteratedDeriv_comp_add_const m r period) x
  rw [show (fun z : ℝ => r (z + period)) = r from funext (fun z => hper z)] at h
  exact h.symm

/-- **A global bound for the iterated derivatives of a smooth knot.**  Because `r` is periodic, all
of its iterated derivatives are periodic, hence bounded. -/
theorem exists_bound_iteratedDeriv_knot {r : ℝ → Space} (hr : IsSmoothKnot r) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖iteratedDeriv m r x‖ ≤ B := by
  have hper := periodic_iteratedDeriv_of_periodic hr.periodic m
  have hcont : Continuous (iteratedDeriv m r) := hr.smooth.continuous_iteratedDeriv m le_top
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, period_pos.le⟩)
  refine ⟨C, hC0, fun x => ?_⟩
  set n : ℤ := ⌊x / period⌋ with hn
  set y : ℝ := x - (n : ℝ) * period with hy
  have hxl : (n : ℝ) ≤ x / period := by rw [hn]; exact Int.floor_le _
  have hxu : x / period < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have hT : (0:ℝ) < period := period_pos
  have hyl : 0 ≤ y := by
    have h1 : (n : ℝ) * period ≤ (x / period) * period := mul_le_mul_of_nonneg_right hxl hT.le
    rw [div_mul_cancel₀ x (ne_of_gt hT)] at h1
    rw [hy]; linarith
  have hyu : y < period := by
    have h1 : x / period * period < ((n : ℝ) + 1) * period := mul_lt_mul_of_pos_right hxu hT
    rw [div_mul_cancel₀ x (ne_of_gt hT)] at h1
    rw [hy]; nlinarith
  have hfx : iteratedDeriv m r x = iteratedDeriv m r y := by
    have hxy : x = y + (n : ℝ) * period := by rw [hy]; ring
    rw [hxy]
    exact (hper.int_mul n) y
  rw [hfx]
  exact hC y ⟨hyl, hyu.le⟩

/-! ## The iterated derivatives of an affine reparametrisation -/

/-- The `m`-th iterated derivative of `t ↦ r (A + t * W)` is `t ↦ W^m • r^{(m)} (A + t * W)`. -/
theorem iteratedDeriv_comp_affine {r : ℝ → Space} (h : ContDiff ℝ ⊤ r) (m : ℕ) (A W : ℝ) :
    iteratedDeriv m (fun t : ℝ => r (A + t * W)) =
      fun t : ℝ => W ^ m • iteratedDeriv m r (A + t * W) := by
  have hm : ContDiff ℝ (↑m) r := h.of_le le_top
  have hshift : ContDiff ℝ (↑m) (fun z : ℝ => r (A + z)) := by
    have hlin : ContDiff ℝ (↑m) (fun z : ℝ => A + z) := by fun_prop
    exact hm.comp hlin
  have h1 := iteratedDeriv_comp_const_smul (n := m) (f := fun z : ℝ => r (A + z)) hshift W
  have h2 := iteratedDeriv_comp_const_add m r A
  rw [h2] at h1
  rw [show (fun t : ℝ => r (A + t * W)) = (fun x : ℝ => r (A + W * x)) from by
        funext t; rw [mul_comm]]
  rw [h1]
  funext t
  rw [mul_comm]

/-! ## The elementary algebra of the Taylor correction -/

/-- The scalar identity turning the difference of the two Taylor coefficients into the correction
coefficient. -/
theorem dev_taylor_scalar_idA (k : ℕ) (ξ W : ℝ) :
    ξ * ((k.factorial : ℝ)⁻¹ * W ^ k) - (k.factorial : ℝ)⁻¹ * ξ ^ k * W ^ k
      = (ξ - ξ ^ k) * (W ^ k / (k.factorial : ℝ)) := by
  have h : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- The scalar identity identifying the geometric sum with the Taylor coefficient difference. -/
theorem dev_taylor_scalar_idB (k : ℕ) (hk : 1 ≤ k) (ξ W : ℝ) :
    (ξ * (1 - ξ)) * ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * W ^ k / (k.factorial : ℝ))
      = (ξ - ξ ^ k) * (W ^ k / (k.factorial : ℝ)) := by
  have hgeo := geom_sum_mul_neg ξ (k - 1)
  have hpow : ξ ^ k = ξ ^ (k - 1) * ξ := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  have h2 : ξ * (1 - ξ) * ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * W ^ k / (k.factorial : ℝ))
      = (ξ * ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * (1 - ξ)))
          * (W ^ k / (k.factorial : ℝ)) := by
    ring
  have key : ξ * ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * (1 - ξ)) = ξ - ξ ^ k := by
    rw [hgeo, hpow]; ring
  rw [h2, key]

/-- Splitting a sum over `range (j+1)` at its first two terms. -/
theorem sum_range_split_two {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : 2 ≤ j) (f : ℕ → M) :
    ∑ k ∈ Finset.range (j+1), f k = f 0 + f 1 + ∑ k ∈ Finset.Icc 2 j, f k := by
  have h1 : ∑ k ∈ Finset.range (j+1), f k
      = ∑ k ∈ Finset.range 2, f k + ∑ k ∈ Finset.range (j-1), f (2+k) := by
    rw [show j + 1 = 2 + (j - 1) by omega, Finset.sum_range_add]
  rw [h1]
  have h2 : ∑ k ∈ Finset.range 2, f k = f 0 + f 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h3 : ∑ k ∈ Finset.range (j-1), f (2+k) = ∑ k ∈ Finset.Icc 2 j, f k := by
    rw [show (j-1) = (j+1-2) by omega, ← Finset.sum_Ico_eq_sum_range (f := f) (m := 2) (n := j+1)]
    rw [show Finset.Ico 2 (j+1) = Finset.Icc 2 j from by
      rw [show (j+1 : ℕ) = Order.succ j from Order.succ_eq_add_one j, Finset.Ico_succ_right_eq_Icc]]
  rw [h2, h3]

/-- **The algebraic identity behind `dev_taylor_le`.**  The `j`-th Taylor polynomial identity
`ξ • P(1) - P(ξ) - ξ(1-ξ) • (correction) = (ξ-1) • c 0`, where `P` is the Taylor polynomial
`P(t) = ∑_{k ≤ j} (t^k/k!) W^k c_k` and the correction is the geometric sum of the statement. -/
theorem dev_taylor_algebra {j : ℕ} (hj : 2 ≤ j) (ξ W : ℝ) (c : ℕ → Space) :
    ξ • (∑ k ∈ Finset.range (j + 1), ((k.factorial : ℝ)⁻¹) • (W ^ k • c k))
      - (∑ k ∈ Finset.range (j + 1), ((k.factorial : ℝ)⁻¹ * ξ ^ k) • (W ^ k • c k))
      - (ξ * (1 - ξ)) • (∑ k ∈ Finset.Icc 2 j,
          ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * W ^ k / (k.factorial : ℝ)) • c k)
    = (ξ - 1) • c 0 := by
  have hA : ξ • (∑ k ∈ Finset.range (j + 1), ((k.factorial : ℝ)⁻¹) • (W ^ k • c k))
      - (∑ k ∈ Finset.range (j + 1), ((k.factorial : ℝ)⁻¹ * ξ ^ k) • (W ^ k • c k))
      = ∑ k ∈ Finset.range (j+1), ((ξ - ξ^k) * (W^k / (k.factorial : ℝ))) • c k := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [smul_smul]
    rw [← sub_smul]
    congr 1
    exact dev_taylor_scalar_idA k ξ W
  have hB : (ξ * (1 - ξ)) • (∑ k ∈ Finset.Icc 2 j,
        ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * W ^ k / (k.factorial : ℝ)) • c k)
      = ∑ k ∈ Finset.Icc 2 j, ((ξ - ξ^k) * (W^k / (k.factorial : ℝ))) • c k := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [smul_smul]
    congr 1
    exact dev_taylor_scalar_idB k (by have := (Finset.mem_Icc.mp hk).1; omega) ξ W
  have hG0 : ((ξ - ξ^0) * (W^0 / ((0:ℕ).factorial : ℝ))) • c 0 = (ξ - 1) • c 0 := by
    norm_num
  have hG1 : ((ξ - ξ^1) * (W^1 / ((1:ℕ).factorial : ℝ))) • c 1 = 0 := by
    norm_num
  rw [hA, hB, sum_range_split_two hj (fun k => ((ξ - ξ^k) * (W^k / (k.factorial : ℝ))) • c k),
    hG0, hG1]
  abel

/-! ## The Taylor bound for the deviation -/

theorem dev_taylor_le {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C w₀ : ℝ, 0 < C ∧ 0 < w₀ ∧
      ∀ {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
        {σ : ℝ}, Work.Drive.sweepW' D σ ∈ Set.Ioc (0:ℝ) w₀ →
        ∀ ξ ∈ Set.Icc (0:ℝ) 1,
        ‖Work.Drive.dev r D σ ξ + (ξ * (1 - ξ)) •
            (∑ k ∈ Finset.Icc 2 j,
              ((∑ m ∈ Finset.range (k - 1), ξ ^ m) *
                  (Work.Drive.sweepW' D σ) ^ k / (k.factorial : ℝ)) •
                iteratedDeriv k r (Work.Drive.taR D σ))‖
          ≤ C * (Work.Drive.sweepW' D σ) ^ (j + 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_iteratedDeriv_knot hr (j+1)
  have hfact : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  refine ⟨2 * B / (j.factorial : ℝ) + 1, 1, ?_, one_pos, ?_⟩
  · have h : (0:ℝ) ≤ 2 * B / (j.factorial : ℝ) := div_nonneg (by linarith) hfact.le
    linarith
  · intro d D σ hW ξ hξ
    obtain ⟨hWpos, hWle⟩ := hW
    rw [dev_apply]
    set A : ℝ := taR D σ with hA
    set W : ℝ := sweepW' D σ with hWdef
    have htb : A + W = tbR D σ := by
      rw [hA, hWdef]
      simp only [sweepW']
      ring
    rw [← htb]
    set S : Space := ∑ k ∈ Finset.Icc 2 j,
        ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * W ^ k / (k.factorial : ℝ)) •
          iteratedDeriv k r A with hS
    set g : ℝ → Space := fun t => r (A + t * W) with hg
    set T : ℝ → Space := fun t => taylorWithinEval g j (Set.Icc (0:ℝ) 1) 0 t with hT
    have hWpos' : 0 < W := hWpos
    have hgC : ContDiff ℝ ⊤ g := by
      rw [hg]; exact hr.smooth.comp (by fun_prop)
    have hgderiv : ∀ m : ℕ, iteratedDeriv m g =
        fun t => W ^ m • iteratedDeriv m r (A + t * W) := by
      intro m
      rw [hg]
      exact iteratedDeriv_comp_affine hr.smooth m A W
    have hTξ : T ξ = taylorWithinEval g j (Set.Icc (0:ℝ) 1) 0 ξ := by rw [hT]
    have hTone : T 1 = taylorWithinEval g j (Set.Icc (0:ℝ) 1) 0 1 := by rw [hT]
    have hgTraw : ∀ t : ℝ, taylorWithinEval g j (Set.Icc (0:ℝ) 1) 0 t =
        ∑ k ∈ Finset.range (j+1),
          ((k.factorial : ℝ)⁻¹ * t ^ k) • (W ^ k • iteratedDeriv k r A) := by
      intro t
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [sub_zero]
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc one_pos)
            ((hgC.of_le (le_top : (↑k : WithTop ℕ∞) ≤ ⊤)).contDiffAt)
            (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)]
      rw [congrFun (hgderiv k) 0, zero_mul, add_zero]
    have hgT : ∀ t : ℝ, T t =
        ∑ k ∈ Finset.range (j+1),
          ((k.factorial : ℝ)⁻¹ * t ^ k) • (W ^ k • iteratedDeriv k r A) :=
      fun t => by rw [hT]; exact hgTraw t
    have hT1 : T 1 = ∑ k ∈ Finset.range (j+1),
        ((k.factorial : ℝ)⁻¹) • (W ^ k • iteratedDeriv k r A) := by
      rw [hgT 1]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [one_pow, mul_one]
    have hc0 : iteratedDeriv 0 r A = g 0 := by
      rw [iteratedDeriv_zero, hg]; simp
    have halg : ξ • T 1 - T ξ - (ξ * (1 - ξ)) • S = (ξ - 1) • g 0 := by
      have h0 := dev_taylor_algebra hj ξ W (fun k : ℕ => iteratedDeriv k r A)
      rw [← hT1, ← hgT ξ, ← hS] at h0
      rwa [hc0] at h0
    have hcorr : (ξ * (1 - ξ)) • S = ξ • T 1 - T ξ - (ξ - 1) • g 0 := by
      rw [← halg]; abel
    have hmaster : g ξ - (1 - ξ) • g 0 - ξ • g 1 + (ξ * (1 - ξ)) • S
        = (g ξ - T ξ) - ξ • (g 1 - T 1) := by
      rw [hcorr]; module
    have hdev : r (A + ξ * W) - ((1 - ξ) • r A + ξ • r (A + W))
        = g ξ - (1 - ξ) • g 0 - ξ • g 1 := by
      rw [hg]
      simp only [zero_mul, add_zero, one_mul]
      abel
    have hmain : r (A + ξ * W) - ((1 - ξ) • r A + ξ • r (A + W)) + (ξ * (1 - ξ)) • S
        = (g ξ - T ξ) - ξ • (g 1 - T 1) := by
      rw [hdev, hmaster]
    rw [hmain]
    have hConIcc : ContDiffOn ℝ (↑j + 1) g (Set.Icc (0:ℝ) 1) :=
      (hgC.of_le (le_top : (↑j + 1 : WithTop ℕ∞) ≤ ⊤)).contDiffOn
    have hCbd : ∀ y ∈ Set.Icc (0:ℝ) 1,
        ‖iteratedDerivWithin (j+1) g (Set.Icc (0:ℝ) 1) y‖ ≤ B * W ^ (j+1) := by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc one_pos)
        ((hgC.of_le (le_top : (↑(j+1) : WithTop ℕ∞) ≤ ⊤)).contDiffAt) hy]
      rw [congrFun (hgderiv (j+1)) y, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hWpos' _)]
      calc W ^ (j+1) * ‖iteratedDeriv (j+1) r (A + y * W)‖ ≤ W ^ (j+1) * B :=
            mul_le_mul_of_nonneg_left (hB _) (pow_nonneg hWpos'.le _)
        _ = B * W ^ (j+1) := by ring
    have htayξ := taylor_mean_remainder_bound (f := g) (a := (0:ℝ)) (b := 1)
        (C := B * W ^ (j+1)) (x := ξ) (n := j) zero_le_one hConIcc hξ hCbd
    have htay1 := taylor_mean_remainder_bound (f := g) (a := (0:ℝ)) (b := 1)
        (C := B * W ^ (j+1)) (x := 1) (n := j) zero_le_one hConIcc (by norm_num) hCbd
    rw [sub_zero] at htayξ
    rw [sub_zero, one_pow, mul_one] at htay1
    have h1 : ‖g ξ - T ξ‖ ≤ (B * W ^ (j+1)) * ξ ^ (j+1) / (j.factorial : ℝ) := by
      rw [hTξ]; exact htayξ
    have h2 : ‖g 1 - T 1‖ ≤ (B * W ^ (j+1)) / (j.factorial : ℝ) := by
      rw [hTone]; exact htay1
    have hstep : ‖(g ξ - T ξ) - ξ • (g 1 - T 1)‖
        ≤ (B * W ^ (j+1)) * ξ ^ (j+1) / (j.factorial : ℝ)
            + ξ * ((B * W ^ (j+1)) / (j.factorial : ℝ)) := by
      calc ‖(g ξ - T ξ) - ξ • (g 1 - T 1)‖
          ≤ ‖g ξ - T ξ‖ + ‖ξ • (g 1 - T 1)‖ := norm_sub_le _ _
        _ = ‖g ξ - T ξ‖ + ξ * ‖g 1 - T 1‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ.1]
        _ ≤ _ := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hξ.1)
    have hnum : (B * W ^ (j+1)) * ξ ^ (j+1) / (j.factorial : ℝ)
        + ξ * ((B * W ^ (j+1)) / (j.factorial : ℝ))
          ≤ (2 * B / (j.factorial : ℝ) + 1) * W ^ (j+1) := by
      have hξp : ξ ^ (j+1) ≤ 1 := pow_le_one₀ hξ.1 hξ.2
      have hK : 0 ≤ B * W ^ (j+1) / (j.factorial : ℝ) :=
        div_nonneg (mul_nonneg hB0 (pow_nonneg hWpos'.le _)) hfact.le
      have e1 : (B * W ^ (j+1)) * ξ ^ (j+1) / (j.factorial : ℝ)
          = (B * W ^ (j+1) / (j.factorial : ℝ)) * ξ ^ (j+1) := by ring
      have e2 : ξ * ((B * W ^ (j+1)) / (j.factorial : ℝ))
          = (B * W ^ (j+1) / (j.factorial : ℝ)) * ξ := by ring
      have e3 : (2 * B / (j.factorial : ℝ) + 1) * W ^ (j+1)
          = 2 * (B * W ^ (j+1) / (j.factorial : ℝ)) + W ^ (j+1) := by ring
      rw [e1, e2, e3]
      nlinarith [hK, hξp, hξ.2, pow_nonneg hWpos'.le (j+1)]
    exact le_trans hstep hnum

end Work.Drive
