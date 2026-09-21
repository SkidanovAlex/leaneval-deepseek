import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.JetBound
import Submission.Work.OddVolterra.Existence.exists_bound_comp_pair_sub_param
import Submission.Work.OddVolterra.Existence.IteratedDerivSection
import Submission.Work.OddVolterra.Existence.E1_E2_model

/-!
# Uniform smallness of the odd inhomogeneities `E₁`, `E₂` at `h = 0`

This file proves `Work.OddVolterra.Existence.E1_E2_diff_bounds`: if the perturbation `h` is
`C^∞` with all derivatives up to order `n + 2` bounded by `δ` (for `δ` small), then on the
slope window `[c, 1 - τ]` both differences `E₁ n h - E₁ n 0` and `E₂ n h - E₂ n 0` are bounded
by `C δ` and are `C δ`-Lipschitz.

The `E₁` part is proved here: `mE1_eq` writes `E₁ n h v` as the `t`-integral of the graph
composite `u ↦ mPhiF n (u, h u, t)`, and the three-variable jet tool
`exists_bound_comp_pair_sub_param` bounds the difference of the order-`(n+1)` and
order-`(n+2)` composites by `C δ`; integrating gives the bound and the mean value theorem
(with `hasDerivAt_iteratedDeriv_section`) gives the Lipschitz estimate.

The `E₂` part is proved here as well: `mE2_eq` writes `E₂ n h v` as the `t`-integral of
`u ↦ mPhiB n (u, h u, t) · (t + deriv h u)`, which splits as `t · Φ + deriv h · Φ`; the first
piece is estimated by the difference tool applied to the model function `mPhiB n`, and the
second by the Leibniz formula `iteratedDeriv_mul` together with the uniform bound
`E2_comp_bound_all` for the graph composite of `mPhiB n` (difference tool at each order, plus
the ball bound `m_ball_slice_bounds`).  The Lipschitz estimates are again obtained with the
mean value theorem (`hasDerivAt_iteratedDeriv_section`).  The same `E₂` estimate is available
as the standalone lemma `Work.OddVolterra.Existence.E2_diff_bounds`.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Commons.Geometry.Ulam
open Work.OddVolterra.DiffBounds

/-! ## Integrability of the `E₁` graph composites -/

/-- The `h`-dependent `E₁`-composite is interval integrable in the section parameter. -/
private lemma integrable_E1_slice (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {v : ℝ} (hv : v ∈ Set.Icc c (1 - tau))
    {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hjet : ∀ j ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ) :
    IntervalIntegrable
      (fun t : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v) volume
      (-(profileX 1)) (profileX 1) := by
  have hmem : ∀ t ∈ Set.uIcc (-(profileX 1)) (profileX 1), (v, t) ∈ graphPos h := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith [profileX_one_pos'])] at ht
    rw [mem_graphPos]
    refine m_box_pos hc hc1 hv ?_ (abs_le.mpr ht)
    simpa using le_trans (hjet 0 (Nat.zero_le _) v hv) hδ
  exact intervalIntegrable_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
    (contDiffOn_graphPhiF n hh) (n + 1) hmem

/-- The pointwise difference of the `h`- and the ball `E₁`-composites is interval integrable. -/
private lemma integrable_E1_pair (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {v : ℝ} (hv : v ∈ Set.Icc c (1 - tau))
    {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hjet : ∀ j ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ) :
    IntervalIntegrable
      (fun t : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
        - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v) volume
      (-(profileX 1)) (profileX 1) := by
  have h2 : ∀ j ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau),
      |iteratedDeriv j (0 : ℝ → ℝ) u| ≤ (0 : ℝ) := by
    intro j _ u _
    have hz : iteratedDeriv j (0 : ℝ → ℝ) u = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split_ifs <;> rfl
    rw [hz, abs_zero]
  exact (integrable_E1_slice n hh hc hc1 hv hδ hjet).sub
    (integrable_E1_slice n (contDiff_const (c := (0 : ℝ))) hc hc1 hv (by norm_num) h2)

/-- `E₁ n h v - E₁ n 0 v` is the integral of the pointwise difference of the graph composites. -/
private lemma E1_diff_eq_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {v : ℝ} (hv : v ∈ Set.Icc c (1 - tau))
    {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hjet : ∀ j ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ) :
    E1 n h v - E1 n 0 v =
      ∫ t in (-(profileX 1))..(profileX 1),
        (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
          - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v) := by
  have h2 : ∀ j ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau),
      |iteratedDeriv j (0 : ℝ → ℝ) u| ≤ (0 : ℝ) := by
    intro j _ u _
    have hz : iteratedDeriv j (0 : ℝ → ℝ) u = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split_ifs <;> rfl
    rw [hz, abs_zero]
  have hIh := integrable_E1_slice n hh hc hc1 hv hδ hjet
  have hI0 : IntervalIntegrable
      (fun t : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v) volume
      (-(profileX 1)) (profileX 1) :=
    integrable_E1_slice n (contDiff_const (c := (0 : ℝ))) hc hc1 hv (by norm_num) h2
  rw [mE1_eq n h v, mE1_eq n 0 v]
  simp only [Pi.zero_apply]
  rw [← intervalIntegral.integral_sub hIh hI0]

/-! ## Pointwise Lipschitz bound for the `E₁` composite -/

/-- For each section parameter `t`, the difference of the order-`(n+1)` composites is
`C δ`-Lipschitz in the first variable. -/
private lemma E1_pointwise_lipschitz (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hjet : ∀ j ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ)
    {C₂ : ℝ}
    (hC₂ : ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      |iteratedDeriv (n + 2) (fun u : ℝ => mPhiF n (u, h u, t)) x
        - iteratedDeriv (n + 2) (fun u : ℝ => mPhiF n (u, 0, t)) x| ≤ C₂ * δ)
    {v v' : ℝ} (hv : v ∈ Set.Icc c (1 - tau)) (hv' : v' ∈ Set.Icc c (1 - tau))
    {t : ℝ} (ht : t ∈ Set.Icc (-(profileX 1)) (profileX 1)) :
    |(iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
        - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
      - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
        - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')| ≤ C₂ * δ * |v - v'| := by
  have hmemh : ∀ x ∈ Set.Icc c (1 - tau), (x, t) ∈ graphPos h := by
    intro x hx
    rw [mem_graphPos]
    refine m_box_pos hc hc1 hx ?_ ?_
    · simpa using le_trans (hjet 0 (Nat.zero_le _) x hx) hδ
    · exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hmem0 : ∀ x ∈ Set.Icc c (1 - tau), (x, t) ∈ graphPos 0 := by
    intro x hx
    rw [mem_graphPos]
    exact m_box_pos hc hc1 hx (by norm_num)
      (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
  have hd1 : ∀ x ∈ Set.Icc c (1 - tau),
      HasDerivAt (fun s : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s)
        (iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, h u, t)) x) x := by
    intro x hx
    exact hasDerivAt_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
      (contDiffOn_graphPhiF n hh) (n + 1) (hmemh x hx)
  have hd0 : ∀ x ∈ Set.Icc c (1 - tau),
      HasDerivAt (fun s : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)
        (iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, 0, t)) x) x := by
    intro x hx
    exact hasDerivAt_iteratedDeriv_section (V := graphPos 0)
      (isOpen_graphPos (contDiff_const (c := (0 : ℝ))))
      (contDiffOn_graphPhiF n (contDiff_const (c := (0 : ℝ)))) (n + 1) (hmem0 x hx)
  have hdiff : ∀ x ∈ Set.Icc c (1 - tau),
      DifferentiableAt ℝ (fun s : ℝ =>
        (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
          - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)) x :=
    fun x hx => (hd1 x hx).differentiableAt.sub (hd0 x hx).differentiableAt
  have hbd : ∀ x ∈ Set.Icc c (1 - tau),
      ‖deriv (fun s : ℝ =>
        (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
          - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)) x‖ ≤ C₂ * δ := by
    intro x hx
    have hderiv : deriv (fun s : ℝ =>
        (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
          - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)) x
        = iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, h u, t)) x
          - iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, 0, t)) x :=
      ((hd1 x hx).sub (hd0 x hx)).deriv
    rw [hderiv, Real.norm_eq_abs]
    simpa [show n + 2 = (n + 1) + 1 from by omega] using hC₂ x hx t ht
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun s : ℝ =>
      (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
        - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s))
    hdiff hbd (convex_Icc c (1 - tau)) hv' hv
  simpa only [Real.norm_eq_abs] using h


/-! ## The `E₂` estimate

`E₂ n h v = ∫_t ∂_u^n (mPhiB n (u, h u, t) · (t + h'(u)))|_{u=v} dt`.  The integrand is a
product of the graph composite `u ↦ mPhiB n (u, h u, t)` of the fixed smooth model function
`mPhiB n` with the linear expression `t + deriv h u`, so splitting it by the Leibniz rule
(`iteratedDeriv_mul`) reduces the estimate to (i) the difference tool
`exists_bound_comp_pair_sub_param` for the composite itself and (ii) a *uniform* bound for the
composite at all orders `≤ n + 1`, which is the difference tool at the corresponding order plus
the ball bound `m_ball_slice_bounds`. -/

/-- Uniform bound for the graph composite of `mPhiB` on the window box. -/
private lemma E2_comp_bound (n : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → δ ≤ 1 / 100 →
      ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k ≤ j, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ) →
      ∀ v ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v| ≤ M := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := exists_bound_comp_pair_sub_param (i := j) (Φ := mPhiB n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := mUpos) isOpen_mUpos
    (m_box_subset_mUpos (R := 1 / 100) (p := profileX 1) hc hc1 le_rfl rfl)
    (contDiffOn_mPhiB n) hc1 (by norm_num) (le_of_lt profileX_one_pos')
  obtain ⟨M₀, hM₀nn, hM₀⟩ := m_ball_slice_bounds n hc hc1 j
  refine ⟨C₁ + M₀, add_nonneg hC₁nn hM₀nn, ?_⟩
  intro h δ hδnn hδ1 hδR hh hjet v hv t ht
  have h1 := hC₁ h δ hδnn hδ1 hδR hh hjet v hv t ht
  have h2 := hM₀ v hv t ht
  have htri : |iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v|
      ≤ |iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v
          - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v|
        + |iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v| := by
    have h := abs_add_le (iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v
      - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v)
      (iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v)
    simpa using h
  calc |iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v|
      ≤ C₁ * δ + M₀ := le_trans htri (add_le_add h1 h2)
    _ ≤ C₁ + M₀ := by
        have hle : C₁ * δ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left hδ1 hC₁nn
        linarith

/-- A single uniform bound for all orders `≤ j` of the graph composite of `mPhiB`. -/
private lemma E2_comp_bound_all (n : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → δ ≤ 1 / 100 →
      ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k ≤ j, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ) →
      ∀ i ≤ j, ∀ v ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv i (fun u : ℝ => mPhiB n (u, h u, t)) v| ≤ M := by
  choose Mb hMb0 hMb using fun i => E2_comp_bound n hc hc1 i
  refine ⟨∑ i ∈ Finset.range (j + 1), Mb i, Finset.sum_nonneg fun i _ => hMb0 i, ?_⟩
  intro h δ hδnn hδ1 hδR hh hjet i hi v hv t ht
  refine le_trans (hMb i h δ hδnn hδ1 hδR hh (fun k hk u hu => hjet k (le_trans hk hi) u hu)
    v hv t ht) ?_
  exact Finset.single_le_sum (f := Mb) (fun i _ => hMb0 i)
    (by simp only [Finset.mem_range]; omega)

/-- Integrability of the `E₂` graph composite in the section parameter. -/
private lemma integrable_E2_slice (n j : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {v : ℝ} (hv : v ∈ Set.Icc c (1 - tau))
    {δ : ℝ} (hδR : δ ≤ 1 / 100)
    (hjet : ∀ k ≤ j, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ) :
    IntervalIntegrable
      (fun t : ℝ => iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v)
      volume (-(profileX 1)) (profileX 1) := by
  have hmem : ∀ t ∈ Set.uIcc (-(profileX 1)) (profileX 1), (v, t) ∈ graphPos h := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith [profileX_one_pos'])] at ht
    refine mem_graphPos_of_box hc hc1 hv ?_ (abs_le.mpr ht)
    have h₁ := hjet 0 (Nat.zero_le j) v hv
    simpa using le_trans h₁ hδR
  exact intervalIntegrable_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
    (contDiffOn_graphPhiH n hh) j hmem

/-- The pointwise difference of the `h`- and the ball `E₂` composites is interval integrable. -/
private lemma integrable_E2_pair (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {v : ℝ} (hv : v ∈ Set.Icc c (1 - tau))
    {δ : ℝ} (hδR : δ ≤ 1 / 100)
    (hjet : ∀ k ≤ n, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ) :
    IntervalIntegrable
      (fun t : ℝ => iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
        - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v) volume
      (-(profileX 1)) (profileX 1) := by
  have h2 : ∀ k ≤ n, ∀ u ∈ Set.Icc c (1 - tau),
      |iteratedDeriv k (0 : ℝ → ℝ) u| ≤ (0 : ℝ) := by
    intro k _ u _
    have hz : iteratedDeriv k (0 : ℝ → ℝ) u = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split_ifs <;> rfl
    rw [hz, abs_zero]
  exact (integrable_E2_slice n n hh hc hc1 hv hδR hjet).sub
    (integrable_E2_slice n n (contDiff_const (c := (0 : ℝ))) hc hc1 hv (by norm_num) h2)

/-- Pointwise bound for the difference of the `E₂` integrands, at an arbitrary order `j`. -/
private lemma E2_pointwise_sub (n j : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {δ : ℝ} (hδnn : 0 ≤ δ) (hδR : δ ≤ 1 / 100)
    (hjet : ∀ k ≤ j, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ)
    (hjetd : ∀ k ≤ j, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv (k + 1) h u| ≤ δ)
    {C₁ M : ℝ}
    (hC₁ : ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      |iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) x
        - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) x| ≤ C₁ * δ)
    (hM : ∀ i ≤ j, ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      |iteratedDeriv i (fun u : ℝ => mPhiB n (u, h u, t)) x| ≤ M)
    {v : ℝ} (hv : v ∈ Set.Icc c (1 - tau)) {t : ℝ}
    (ht : t ∈ Set.Icc (-(profileX 1)) (profileX 1)) :
    |iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
      - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v|
      ≤ (|t| * C₁ + (∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ)) * M) * δ := by
  have htabs : |t| ≤ profileX 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hxv : |h v| ≤ 1 / 100 := by
    have h₁ := hjet 0 (Nat.zero_le j) v hv
    simpa using le_trans h₁ hδR
  have hcc0 : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) := contDiff_const
  have hmemh : (v, t) ∈ graphPos h := mem_graphPos_of_box hc hc1 hv hxv htabs
  have hmem0 : (v, t) ∈ graphPos (0 : ℝ → ℝ) :=
    mem_graphPos_of_box hc hc1 hv (by norm_num) htabs
  have hBh : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => mPhiB n (u, h u, t)) v :=
    DiffBounds.contDiffAt_graphPhiB_slice n hh hmemh
  have hB0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => mPhiB n (u, 0, t)) v :=
    DiffBounds.contDiffAt_graphPhiB_slice n hcc0 hmem0
  have hdh : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := DiffBounds.contDiff_deriv_of_contDiff hh
  have hle_top : ((j : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
    exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hsmul : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => t * mPhiB n (u, h u, t)) v :=
    ContDiffAt.const_smul t hBh
  have hprod_smooth : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) v :=
    hdh.contDiffAt.mul hBh
  have hsplit_h : (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t)
      = (fun u : ℝ => t * mPhiB n (u, h u, t))
        + (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) := by
    funext u
    simp only [lineSlope, Pi.add_apply]
    ring
  have hsplit_0 : (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t)
      = (fun u : ℝ => t * mPhiB n (u, 0, t)) := by
    funext u
    simp only [lineSlope]
    rw [show deriv (0 : ℝ → ℝ) u = 0 from deriv_const u 0]
    ring
  have hprod : iteratedDeriv j (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) v
      = ∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
          * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v :=
    iteratedDeriv_mul (hdh.contDiffAt.of_le hle_top) (hBh.of_le hle_top)
  have hident : iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
        - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v
      = t * (iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v
              - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v)
        + (∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
            * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v) := by
    rw [hsplit_h, hsplit_0, iteratedDeriv_add (hsmul.of_le hle_top) (hprod_smooth.of_le hle_top),
      iteratedDeriv_const_mul t (hB0.of_le hle_top),
      iteratedDeriv_const_mul t (hBh.of_le hle_top), hprod]
    ring
  rw [hident]
  have hA : |t * (iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v
      - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v)| ≤ |t| * (C₁ * δ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC₁ v hv t ht) (abs_nonneg t)
  have hP : |∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
        * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v|
      ≤ (∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ)) * M * δ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ Finset.range (j + 1),
        |((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
          * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v|
        ≤ ((j.choose k : ℕ) : ℝ) * M * δ := by
      intro k hk
      have hkj : k ≤ j := by
        have := Finset.mem_range.mp hk
        omega
      have hb1 : |iteratedDeriv k (deriv h) v| ≤ δ := by
        simpa [iteratedDeriv_succ'] using hjetd k hkj v hv
      have hb2 : |iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v| ≤ M :=
        hM (j - k) (Nat.sub_le j k) v hv t ht
      have hc0 : (0 : ℝ) ≤ ((j.choose k : ℕ) : ℝ) := Nat.cast_nonneg _
      calc |((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
              * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v|
          = ((j.choose k : ℕ) : ℝ) * |iteratedDeriv k (deriv h) v|
              * |iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hc0]
        _ ≤ ((j.choose k : ℕ) : ℝ) * δ * M :=
            mul_le_mul (mul_le_mul_of_nonneg_left hb1 hc0) hb2 (abs_nonneg _)
              (mul_nonneg hc0 hδnn)
        _ = ((j.choose k : ℕ) : ℝ) * M * δ := by ring
    calc ∑ k ∈ Finset.range (j + 1),
            |((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
              * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v|
        ≤ ∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ) * M * δ :=
          Finset.sum_le_sum hterm
      _ = (∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ)) * M * δ := by
          rw [Finset.sum_mul, Finset.sum_mul]
  calc |t * (iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v
            - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v)
          + ∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
              * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v|
      ≤ |t * (iteratedDeriv j (fun u : ℝ => mPhiB n (u, h u, t)) v
            - iteratedDeriv j (fun u : ℝ => mPhiB n (u, 0, t)) v)|
        + |∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ) * iteratedDeriv k (deriv h) v
              * iteratedDeriv (j - k) (fun u : ℝ => mPhiB n (u, h u, t)) v| := abs_add_le _ _
    _ ≤ |t| * (C₁ * δ) + (∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ)) * M * δ :=
        add_le_add hA hP
    _ = (|t| * C₁ + (∑ k ∈ Finset.range (j + 1), ((j.choose k : ℕ) : ℝ)) * M) * δ := by ring

/-- `E₂ n h v - E₂ n 0 v` is the integral of the pointwise difference of the `E₂` composites. -/
private lemma E2_diff_eq_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 - tau) {v : ℝ} (hv : v ∈ Set.Icc c (1 - tau))
    {δ : ℝ} (hδR : δ ≤ 1 / 100)
    (hjet : ∀ k ≤ n, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ) :
    E2 n h v - E2 n 0 v =
      ∫ t in (-(profileX 1))..(profileX 1),
        (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
          - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v) := by
  have h2 : ∀ k ≤ n, ∀ u ∈ Set.Icc c (1 - tau),
      |iteratedDeriv k (0 : ℝ → ℝ) u| ≤ (0 : ℝ) := by
    intro k _ u _
    have hz : iteratedDeriv k (0 : ℝ → ℝ) u = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split_ifs <;> rfl
    rw [hz, abs_zero]
  have hIh := integrable_E2_slice n n hh hc hc1 hv hδR hjet
  have hI0 : IntervalIntegrable
      (fun t : ℝ => iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v)
      volume (-(profileX 1)) (profileX 1) :=
    integrable_E2_slice n n (contDiff_const (c := (0 : ℝ))) hc hc1 hv (by norm_num) h2
  rw [mE2_eq n h v, mE2_eq n 0 v]
  simp only [Pi.zero_apply]
  rw [← intervalIntegral.integral_sub hIh hI0]

/-- The `E₂` half of the main estimate, with the fixed smallness threshold `1/100`. -/
private lemma E2_bound_aux (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      (∀ v ∈ Set.Icc c (1 - tau), |E2 n h v - E2 n 0 v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc c (1 - tau), ∀ v' ∈ Set.Icc c (1 - tau),
        |(E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')| ≤ C * δ * |v - v'|) := by
  obtain ⟨Cn, hCnnn, hCn⟩ := exists_bound_comp_pair_sub_param (i := n) (Φ := mPhiB n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := mUpos) isOpen_mUpos
    (m_box_subset_mUpos (R := 1 / 100) (p := profileX 1) hc hc1 le_rfl rfl)
    (contDiffOn_mPhiB n) hc1 (by norm_num) (le_of_lt profileX_one_pos')
  obtain ⟨Cn', hCn'nn, hCn'⟩ := exists_bound_comp_pair_sub_param (i := n + 1) (Φ := mPhiB n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := mUpos) isOpen_mUpos
    (m_box_subset_mUpos (R := 1 / 100) (p := profileX 1) hc hc1 le_rfl rfl)
    (contDiffOn_mPhiB n) hc1 (by norm_num) (le_of_lt profileX_one_pos')
  obtain ⟨M, hMnn, hMall⟩ := E2_comp_bound_all n hc hc1 n
  obtain ⟨M', hM'nn, hM'all⟩ := E2_comp_bound_all n hc hc1 (n + 1)
  have hp : (0 : ℝ) < profileX 1 := profileX_one_pos'
  have hp2 : (0 : ℝ) ≤ 2 * profileX 1 := by linarith
  have hp1 : (1 : ℝ) ≤ 2 * profileX 1 := by linarith [half_lt_profileX_one]
  have hS : (∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ℝ)) = (2 : ℝ) ^ n := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  have hS' : (∑ k ∈ Finset.range (n + 1 + 1), (((n + 1).choose k : ℕ) : ℝ))
      = (2 : ℝ) ^ (n + 1) := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  have hA0 : (0 : ℝ) ≤ profileX 1 * Cn + (2 : ℝ) ^ n * M :=
    add_nonneg (mul_nonneg hp.le hCnnn) (mul_nonneg (pow_nonneg (by norm_num) n) hMnn)
  have hB0 : (0 : ℝ) ≤ profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M' :=
    add_nonneg (mul_nonneg hp.le hCn'nn) (mul_nonneg (pow_nonneg (by norm_num) (n + 1)) hM'nn)
  have hAB0 : (0 : ℝ) ≤ profileX 1 * Cn + (2 : ℝ) ^ n * M
      + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') := by linarith
  refine ⟨(profileX 1 * Cn + (2 : ℝ) ^ n * M
      + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (add_nonneg hA0 hB0) hp2) zero_le_one
  · intro h δ hh hδpos hδR hjet
    have hδnn : 0 ≤ δ := le_of_lt hδpos
    have hδ1 : δ ≤ 1 := le_trans hδR (by norm_num)
    have hjetn : ∀ k ≤ n, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ :=
      fun k hk u hu => hjet k (le_trans hk (by omega)) u
    have hjetn' : ∀ k ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv k h u| ≤ δ :=
      fun k hk u hu => hjet k (le_trans hk (by omega)) u
    have hjetdn : ∀ k ≤ n, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv (k + 1) h u| ≤ δ :=
      fun k hk u hu => hjet (k + 1) (by omega) u
    have hjetdn' : ∀ k ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau),
        |iteratedDeriv (k + 1) h u| ≤ δ :=
      fun k hk u hu => hjet (k + 1) (by omega) u
    have hCn'inst : ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t)) x
          - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t)) x| ≤ Cn * δ :=
      fun x hx t ht => hCn h δ hδnn hδ1 hδR hh hjetn x hx t ht
    have hCn''inst : ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, h u, t)) x
          - iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, 0, t)) x| ≤ Cn' * δ :=
      fun x hx t ht => hCn' h δ hδnn hδ1 hδR hh hjetn' x hx t ht
    have hMinst : ∀ i ≤ n, ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv i (fun u : ℝ => mPhiB n (u, h u, t)) x| ≤ M :=
      fun i hi x hx t ht => hMall h δ hδnn hδ1 hδR hh hjetn i hi x hx t ht
    have hM'inst : ∀ i ≤ n + 1, ∀ x ∈ Set.Icc c (1 - tau),
        ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv i (fun u : ℝ => mPhiB n (u, h u, t)) x| ≤ M' :=
      fun i hi x hx t ht => hM'all h δ hδnn hδ1 hδR hh hjetn' i hi x hx t ht
    have hab : -(profileX 1) ≤ profileX 1 := by linarith
    refine ⟨?_, ?_⟩
    · -- value bound
      intro v hv
      have hkey := E2_diff_eq_integral n hh hc hc1 hv hδR hjetn
      have hIv := integrable_E2_pair n hh hc hc1 hv hδR hjetn
      have hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
          |iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
            - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v|
          ≤ (profileX 1 * Cn + (2 : ℝ) ^ n * M) * δ := by
        intro t ht
        have h1 := E2_pointwise_sub n n hh hc hc1 hδnn hδR hjetn hjetdn hCn'inst hMinst hv ht
        have htabs : |t| ≤ profileX 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        calc |iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
              - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v|
            ≤ (|t| * Cn + (∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ℝ)) * M) * δ := h1
          _ = (|t| * Cn + (2 : ℝ) ^ n * M) * δ := by rw [hS]
          _ ≤ (profileX 1 * Cn + (2 : ℝ) ^ n * M) * δ := by
              refine mul_le_mul_of_nonneg_right ?_ hδnn
              have hle := mul_le_mul_of_nonneg_right htabs hCnnn
              linarith
      have h1 : |E2 n h v - E2 n 0 v| ≤
          ∫ t in (-(profileX 1))..(profileX 1),
            |iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
              - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v| := by
        rw [hkey]
        exact intervalIntegral.abs_integral_le_integral_abs hab
      have h2 : (∫ t in (-(profileX 1))..(profileX 1),
            |iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
              - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v|)
          ≤ ∫ t in (-(profileX 1))..(profileX 1), ((profileX 1 * Cn + (2 : ℝ) ^ n * M) * δ) :=
        intervalIntegral.integral_mono_on hab hIv.abs intervalIntegrable_const hpt
      have h3 : (∫ t in (-(profileX 1))..(profileX 1), ((profileX 1 * Cn + (2 : ℝ) ^ n * M) * δ))
          = ((profileX 1 * Cn + (2 : ℝ) ^ n * M) * δ) * (2 * profileX 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      have h4 : ((profileX 1 * Cn + (2 : ℝ) ^ n * M) * δ) * (2 * profileX 1)
          ≤ ((profileX 1 * Cn + (2 : ℝ) ^ n * M
              + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1) * δ := by
        have hstep : (profileX 1 * Cn + (2 : ℝ) ^ n * M) * (2 * profileX 1)
            ≤ (profileX 1 * Cn + (2 : ℝ) ^ n * M
              + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1 := by
          have hAB : profileX 1 * Cn + (2 : ℝ) ^ n * M
              ≤ profileX 1 * Cn + (2 : ℝ) ^ n * M
                + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') :=
            le_add_of_nonneg_right hB0
          have h1 := mul_le_mul_of_nonneg_right hAB hp2
          linarith
        calc ((profileX 1 * Cn + (2 : ℝ) ^ n * M) * δ) * (2 * profileX 1)
            = (profileX 1 * Cn + (2 : ℝ) ^ n * M) * (2 * profileX 1) * δ := by ring
          _ ≤ ((profileX 1 * Cn + (2 : ℝ) ^ n * M
                + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1) * δ :=
              mul_le_mul_of_nonneg_right hstep hδnn
      exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) h4))
    · -- Lipschitz bound
      intro v hv v' hv'
      have hkey_v := E2_diff_eq_integral n hh hc hc1 hv hδR hjetn
      have hkey_v' := E2_diff_eq_integral n hh hc hc1 hv' hδR hjetn
      have hIv := integrable_E2_pair n hh hc hc1 hv hδR hjetn
      have hIv' := integrable_E2_pair n hh hc hc1 hv' hδR hjetn
      have hsub : (E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v') =
          ∫ t in (-(profileX 1))..(profileX 1),
            ((iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v)
              - (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v'
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v')) := by
        rw [hkey_v, hkey_v', ← intervalIntegral.integral_sub hIv hIv']
      have hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
          |(iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
              - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v)
            - (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v'
              - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v')|
          ≤ (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ * |v - v'| := by
        intro t ht
        have htabs : |t| ≤ profileX 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        have hmemh : ∀ s ∈ Set.Icc c (1 - tau), (s, t) ∈ graphPos h := by
          intro s hs
          refine mem_graphPos_of_box hc hc1 hs ?_ htabs
          have h₁ := hjet 0 (by omega) s
          simpa using le_trans h₁ hδR
        have hmem0 : ∀ s ∈ Set.Icc c (1 - tau), (s, t) ∈ graphPos (0 : ℝ → ℝ) := by
          intro s hs
          exact mem_graphPos_of_box hc hc1 hs (by norm_num) htabs
        have hd1 : ∀ s ∈ Set.Icc c (1 - tau),
            HasDerivAt (fun s' : ℝ =>
              iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s')
              (iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s) s :=
          fun s hs => hasDerivAt_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
            (contDiffOn_graphPhiH n hh) n (hmemh s hs)
        have hd0 : ∀ s ∈ Set.Icc c (1 - tau),
            HasDerivAt (fun s' : ℝ =>
              iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s')
              (iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s) s :=
          fun s hs => hasDerivAt_iteratedDeriv_section (V := graphPos (0 : ℝ → ℝ))
            (isOpen_graphPos (contDiff_const (c := (0 : ℝ))))
            (contDiffOn_graphPhiH n (contDiff_const (c := (0 : ℝ)))) n (hmem0 s hs)
        have hdiff : ∀ s ∈ Set.Icc c (1 - tau),
            DifferentiableAt ℝ (fun s' : ℝ =>
              (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s'
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s')) s :=
          fun s hs => (hd1 s hs).differentiableAt.sub (hd0 s hs).differentiableAt
        have hbd : ∀ s ∈ Set.Icc c (1 - tau),
            ‖deriv (fun s' : ℝ =>
              (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s'
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s')) s‖
              ≤ (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ := by
          intro s hs
          have hderiv : deriv (fun s' : ℝ =>
              (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s'
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s')) s
              = iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s :=
            ((hd1 s hs).sub (hd0 s hs)).deriv
          rw [hderiv, Real.norm_eq_abs]
          have h1 := E2_pointwise_sub n (n + 1) hh hc hc1 hδnn hδR hjetn' hjetdn'
            hCn''inst hM'inst hs ht
          calc |iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s|
              ≤ (|t| * Cn' + (∑ k ∈ Finset.range (n + 1 + 1), (((n + 1).choose k : ℕ) : ℝ))
                  * M') * δ := h1
            _ = (|t| * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ := by rw [hS']
            _ ≤ (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ := by
                refine mul_le_mul_of_nonneg_right ?_ hδnn
                have hle := mul_le_mul_of_nonneg_right htabs hCn'nn
                linarith
        have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun s' : ℝ =>
            (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) s'
              - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) s'))
          hdiff hbd (convex_Icc c (1 - tau)) hv' hv
        simpa only [Real.norm_eq_abs] using hmv
      have h1 : |(E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')| ≤
          ∫ t in (-(profileX 1))..(profileX 1),
            |(iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v)
              - (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v'
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v')| := by
        rw [hsub]
        exact intervalIntegral.abs_integral_le_integral_abs hab
      have h2 : (∫ t in (-(profileX 1))..(profileX 1),
            |(iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v)
              - (iteratedDeriv n (fun u : ℝ => mPhiB n (u, h u, t) * lineSlope h u t) v'
                - iteratedDeriv n (fun u : ℝ => mPhiB n (u, 0, t) * lineSlope 0 u t) v')|)
          ≤ ∫ t in (-(profileX 1))..(profileX 1),
              ((profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ * |v - v'|) :=
        intervalIntegral.integral_mono_on hab (hIv.sub hIv').abs intervalIntegrable_const hpt
      have h3 : (∫ t in (-(profileX 1))..(profileX 1),
            ((profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ * |v - v'|))
          = ((profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ * |v - v'|) * (2 * profileX 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      have h4 : ((profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ * |v - v'|) * (2 * profileX 1)
          ≤ ((profileX 1 * Cn + (2 : ℝ) ^ n * M
              + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1)
              * δ * |v - v'| := by
        have hnn : (0 : ℝ) ≤ |v - v'| := abs_nonneg _
        have hstep : (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * (2 * profileX 1)
            ≤ (profileX 1 * Cn + (2 : ℝ) ^ n * M
              + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1 := by
          have hAB : profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M'
              ≤ profileX 1 * Cn + (2 : ℝ) ^ n * M
                + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') :=
            le_add_of_nonneg_left hA0
          have h1 := mul_le_mul_of_nonneg_right hAB hp2
          linarith
        calc ((profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * δ * |v - v'|) * (2 * profileX 1)
            = (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M') * (2 * profileX 1)
                * (δ * |v - v'|) := by ring
          _ ≤ ((profileX 1 * Cn + (2 : ℝ) ^ n * M
                + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1)
                * (δ * |v - v'|) := mul_le_mul_of_nonneg_right hstep (mul_nonneg hδnn hnn)
          _ = ((profileX 1 * Cn + (2 : ℝ) ^ n * M
                + (profileX 1 * Cn' + (2 : ℝ) ^ (n + 1) * M')) * (2 * profileX 1) + 1)
                * δ * |v - v'| := by ring
      exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) h4))

/-! ## The main theorem -/

theorem E1_E2_diff_bounds (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau) :
    ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ δ₀ →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      (∀ v ∈ Set.Icc c (1 - tau), |E1 n h v - E1 n 0 v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc c (1 - tau), ∀ v' ∈ Set.Icc c (1 - tau),
        |(E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')| ≤ C * δ * |v - v'|) ∧
      (∀ v ∈ Set.Icc c (1 - tau), |E2 n h v - E2 n 0 v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc c (1 - tau), ∀ v' ∈ Set.Icc c (1 - tau),
        |(E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')| ≤ C * δ * |v - v'|) := by
  have hbox : Set.Icc c (1 - tau) ×ˢ Set.Icc (-(1 / 100 : ℝ)) (1 / 100) ×ˢ
      Set.Icc (-(profileX 1)) (profileX 1) ⊆ mUpos :=
    m_box_subset_mUpos (R := 1 / 100) (p := profileX 1) hc hc1 le_rfl rfl
  obtain ⟨C₁, hC₁nn, hC₁⟩ := exists_bound_comp_pair_sub_param (i := n + 1) (Φ := mPhiF n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := mUpos) isOpen_mUpos hbox
    (contDiffOn_mPhiF n) hc1 (by norm_num) (le_of_lt profileX_one_pos')
  obtain ⟨C₂, hC₂nn, hC₂⟩ := exists_bound_comp_pair_sub_param (i := n + 2) (Φ := mPhiF n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := mUpos) isOpen_mUpos hbox
    (contDiffOn_mPhiF n) hc1 (by norm_num) (le_of_lt profileX_one_pos')
  obtain ⟨C₃, hC₃nn, hC₃⟩ := E2_bound_aux n hn hc hc1
  have hp : (0 : ℝ) < profileX 1 := profileX_one_pos'
  have hp2 : (0 : ℝ) ≤ 2 * profileX 1 := by linarith
  have hp1 : (1 : ℝ) ≤ 2 * profileX 1 := by linarith [half_lt_profileX_one]
  refine ⟨max (max C₁ (max C₂ C₃) * (2 * profileX 1)) C₃, 1 / 100, ?_, ?_, ?_⟩
  · exact le_trans (mul_nonneg (le_trans hC₁nn (le_max_left _ _)) hp2) (le_max_left _ _)
  · norm_num
  · intro h δ hh hδpos hδR hjet
    have hδ1 : δ ≤ 1 := by linarith
    have hδnn : 0 ≤ δ := le_of_lt hδpos
    have hjet1 : ∀ j ≤ n + 1, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ :=
      fun j hj u hu => hjet j (le_trans hj (by omega)) u
    have hjet2 : ∀ j ≤ n + 2, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ :=
      fun j hj u hu => hjet j hj u
    have hC₂' : ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv (n + 2) (fun u : ℝ => mPhiF n (u, h u, t)) x
          - iteratedDeriv (n + 2) (fun u : ℝ => mPhiF n (u, 0, t)) x| ≤ C₂ * δ :=
      fun x hx t ht => hC₂ h δ hδnn hδ1 hδR hh hjet2 x hx t ht
    have hab : -(profileX 1) ≤ profileX 1 := by linarith
    set Ct : ℝ := max C₁ (max C₂ C₃) * (2 * profileX 1) with hCt
    set Cf : ℝ := max Ct C₃ with hCf
    have hC₁le : C₁ ≤ max C₁ (max C₂ C₃) := le_max_left _ _
    have hC₂le : C₂ ≤ max C₁ (max C₂ C₃) := le_trans (le_max_left C₂ C₃) (le_max_right _ _)
    have hCtCf : Ct ≤ Cf := by rw [hCf]; exact le_max_left _ _
    have hC₃Cf : C₃ ≤ Cf := by rw [hCf]; exact le_max_right _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `E₁`: the value bound
      intro v hv
      have hkey := E1_diff_eq_integral n hh hc hc1 hv hδR hjet1
      have hIv := integrable_E1_pair n hh hc hc1 hv hδR hjet1
      have hmono : |E1 n h v - E1 n 0 v| ≤
          ∫ t in (-(profileX 1))..(profileX 1),
            |iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v| := by
        rw [hkey]
        exact intervalIntegral.abs_integral_le_integral_abs hab
      have hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
          |iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v| ≤ C₁ * δ :=
        fun t ht => hC₁ h δ hδnn hδ1 hδR hh hjet1 v hv t ht
      have hmono2 : (∫ t in (-(profileX 1))..(profileX 1),
            |iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v|)
          ≤ ∫ t in (-(profileX 1))..(profileX 1), C₁ * δ :=
        intervalIntegral.integral_mono_on hab hIv.abs intervalIntegrable_const hpt
      have hint : (∫ t in (-(profileX 1))..(profileX 1), (C₁ * δ))
          = C₁ * δ * (2 * profileX 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      calc |E1 n h v - E1 n 0 v| ≤ C₁ * δ * (2 * profileX 1) :=
            le_trans hmono (le_trans hmono2 (le_of_eq hint))
        _ ≤ Ct * δ := by
            rw [hCt]
            have h1 : C₁ * δ ≤ max C₁ (max C₂ C₃) * δ :=
              mul_le_mul_of_nonneg_right hC₁le hδnn
            calc C₁ * δ * (2 * profileX 1) ≤ (max C₁ (max C₂ C₃) * δ) * (2 * profileX 1) :=
                  mul_le_mul_of_nonneg_right h1 hp2
              _ = max C₁ (max C₂ C₃) * (2 * profileX 1) * δ := by ring
        _ ≤ Cf * δ := mul_le_mul_of_nonneg_right hCtCf hδnn
    · -- `E₁`: the Lipschitz bound
      intro v hv v' hv'
      have hkey_v := E1_diff_eq_integral n hh hc hc1 hv hδR hjet1
      have hkey_v' := E1_diff_eq_integral n hh hc hc1 hv' hδR hjet1
      have hIv := integrable_E1_pair n hh hc hc1 hv hδR hjet1
      have hIv' := integrable_E1_pair n hh hc hc1 hv' hδR hjet1
      have hsub : (E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v') =
          ∫ t in (-(profileX 1))..(profileX 1),
            ((iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
              - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')) := by
        rw [hkey_v, hkey_v', ← intervalIntegral.integral_sub hIv hIv']
      have hmono : |(E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')| ≤
          ∫ t in (-(profileX 1))..(profileX 1),
            |(iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
              - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')| := by
        rw [hsub]
        exact intervalIntegral.abs_integral_le_integral_abs hab
      have hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
          |(iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
            - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')|
              ≤ C₂ * δ * |v - v'| :=
        fun t ht => E1_pointwise_lipschitz n hh hc hc1 hδR hjet1 hC₂' hv hv' ht
      have hmono2 : (∫ t in (-(profileX 1))..(profileX 1),
            |(iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
              - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')|)
          ≤ ∫ t in (-(profileX 1))..(profileX 1), C₂ * δ * |v - v'| :=
        intervalIntegral.integral_mono_on hab (hIv.sub hIv').abs intervalIntegrable_const hpt
      have hint : (∫ t in (-(profileX 1))..(profileX 1), (C₂ * δ * |v - v'|))
          = (C₂ * δ * |v - v'|) * (2 * profileX 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      calc |(E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')|
            ≤ (C₂ * δ * |v - v'|) * (2 * profileX 1) :=
            le_trans hmono (le_trans hmono2 (le_of_eq hint))
        _ ≤ Ct * δ * |v - v'| := by
            rw [hCt]
            have h1 : C₂ * δ * |v - v'| ≤ max C₁ (max C₂ C₃) * δ * |v - v'| :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂le hδnn) (abs_nonneg _)
            calc (C₂ * δ * |v - v'|) * (2 * profileX 1)
                ≤ (max C₁ (max C₂ C₃) * δ * |v - v'|) * (2 * profileX 1) :=
                  mul_le_mul_of_nonneg_right h1 hp2
              _ = max C₁ (max C₂ C₃) * (2 * profileX 1) * δ * |v - v'| := by ring
        _ ≤ Cf * δ * |v - v'| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtCf hδnn) (abs_nonneg _)
    · -- `E₂`: the value bound
      intro v hv
      have hE2 := (hC₃ h δ hh hδpos hδR hjet).1 v hv
      exact le_trans hE2 (mul_le_mul_of_nonneg_right hC₃Cf hδnn)
    · -- `E₂`: the Lipschitz bound
      intro v hv v' hv'
      have hE2 := (hC₃ h δ hh hδpos hδR hjet).2 v hv v' hv'
      exact le_trans hE2
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₃Cf hδnn) (abs_nonneg _))

end

end Work.OddVolterra.Existence
