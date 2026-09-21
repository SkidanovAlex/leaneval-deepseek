import Mathlib
import Submission.Work.OddVolterra.Window.TW2_defs
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddExistence.Manifest.thetaM_continuous
import Submission.Work.OddExistence.Manifest.ThetaMBridge
import Submission.Work.OddExistence.Manifest.hasDerivAt_G2M_apply
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.Window.WindowFed
import Submission.Work.OddVolterra.Existence.Theta_integrand_intervalIntegrable
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.Anchor.ThetaM_contDiffOn

namespace Work.OddVolterra.Window

/-
Uniform bound and state-Lipschitz estimate for the manifest odd `Θ`-datum `KernelExt.ThetaM` on
the transition window, *given* the corresponding data for the manifest Abel kernel vector
`KernelExt.KvecM` (`KvecMStateData n M C`, defined in
`Submission/Work/OddVolterra/Window/TW2_defs.lean`: a uniform bound `C` and state-Lipschitz
constant `M` for `KvecM` **and** for its first-slot derivative, on the square
`a, σ ∈ [7/10, 19/20]` and states in the ball of radius `9/20` around `baseState σ`).
`ThetaMStateData n M' B'` is the analogous package for `ThetaM`: bound `B'` and state-Lipschitz
`M'` for `s, σ ∈ [7/10, 19/20]` and states in the ball of radius `9/20` around `baseState σ`.

This is a well-defined step because `KernelExt.ThetaM n h s σ z = ![-z 2, -z 3,
-(∂_u KernelExt.G2M n h u σ z) s, -(∂_u KernelExt.G2M n h u σ z) s]`, so rows 0 and 1 contribute
the bound `2` and Lipschitz constant `1`, and rows 2 and 3 are the first-slot derivative of the
`τ`-average `G2M` of `KvecM`.

Strategy.  Let `B' = max 2 (Real.pi * C)` and `M' = max 1 (Real.pi * M)`.

* Rows 0, 1: immediate since `|z i| ≤ 2` and `|z i - z' i| ≤ ‖z - z'‖` on the ball.
* Rows 2, 3: `Work.OddExistence.Manifest.deriv_G2M_eq_integral_on_RcM` gives, on the region
  `RcM wLeft wRight (9/20)`,
  `deriv (fun u => (Work.OddBridge.G2M n h u σ z) j) s = ∫_0^1 (√(τ(1-τ)))⁻¹ (1-τ)
      ∂_u (Work.OddBridge.KvecM n h · σ z) j (s + τ (σ - s)) dτ`,
  and `Work.OddExistence.Manifest.ThetaMBridge.G2M_eq_KernelExt` / `KvecM_eq_KernelExt` move it to
  the `KernelExt` objects (`ThetaM_eq_KernelExt` for the last-row identifications).  The region
  hypotheses are: `KdenPosOn h wLeft wRight` (positivity of the Abel radicand on the window square
  for `|t| ≥ 1/5` — from `krad_pos_of_region`, using only `|h|, |h'| ≤ 1/100`), and the state
  conditions of `RcM`, supplied by `mem_RcM_facts` from `z ∈ closedBall (baseState σ) (9/20)`
  (`9/20 ≤ 1/2`).
* Integrand: `s + τ(σ-s) ∈ [wLeft, wRight]` for `τ ∈ [0,1]` (both endpoints lie in the window), so
  `hkvec` gives `‖∂_u KvecM‖ ≤ C` and
  `‖∂_u KvecM(·,z) - ∂_u KvecM(·,z')‖ ≤ M ‖z - z'‖` pointwise on `(0,1)`; `1 - τ ≤ 1` and
  `∫_0^1 (√(τ(1-τ)))⁻¹ dτ = Real.pi` (`Work.OddVolterra.Existence.Theta_integrand_intervalIntegrable`
  proves this; `Commons.Geometry.Ulam.intervalIntegrable_abel_weight` gives integrability of the
  weight), so both integrals are bounded by `Real.pi * C` resp. `Real.pi * M * ‖z - z'‖`.
* The difference of the two derivatives is handled by rewriting both with the integral formula
  (using `ThetaM_eq_KernelExt` so that both sides are the same function), subtracting the
  integrands (`intervalIntegral.integral_sub`, with both integrands dominated by the integrable
  `(√(τ(1-τ)))⁻¹ * C`), and bounding the resulting integral by `Real.pi * M * ‖z - z'‖`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-! ## Auxiliary estimates for the manifest kernel `KvecM` -/

/-- `deriv` of a component is the corresponding component of the vector `deriv`. -/
private lemma deriv_apply_eq_fin2 {F : ℝ → Fin 2 → ℝ} {x : ℝ}
    (hF : DifferentiableAt ℝ F x) (j : Fin 2) :
    deriv (fun u : ℝ => F u j) x = (deriv F x) j := by
  rw [deriv_pi (𝕜 := ℝ) (x := x) (φ := F) (fun i => (differentiableAt_pi.mp hF) i)]

/-- Differentiability in the first slot of the manifest kernel `KernelExt.KvecM`, at a point of
`(1/2, 1)` with the second slope in `[7/10, 1]` and the two chord endpoints of modulus `≥ 1/5`. -/
private lemma differentiableAt_KvecM_vec {n : ℕ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {a σ : ℝ} (ha : (1 : ℝ) / 2 < a) (ha1 : a < 1) (hσ : (7 : ℝ) / 10 ≤ σ)
    {z : St} (hz0 : (1 / 5 : ℝ) ≤ z 0) (hz1 : (1 / 5 : ℝ) ≤ z 1) :
    DifferentiableAt ℝ
      (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a := by
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3))
      (Set.Ioo ((1 : ℝ) / 2) 1) :=
    Work.Anchor.contDiffOn_KvecM_comp (n := n) (hh := hh) (B := Set.Ioo ((1 : ℝ) / 2) 1)
      (s := fun u : ℝ => u) (σ := fun _ => σ) (x := fun _ => z 0) (y := fun _ => z 1)
      (x' := fun _ => z 2) (y' := fun _ => z 3)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun u hu => krad_pos_of_region hsm1 (by linarith [hσ, hu.1])
        (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hz0))
      (fun u hu => krad_pos_of_region hsm1 (by linarith [hσ, hu.1])
        (by rw [abs_of_nonneg (by linarith)]; exact hz1))
  exact (hcd.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds ⟨ha, ha1⟩)

/-- Pointwise bound for the first-slot derivative of a component of `KvecM`. -/
private lemma KvecM_deriv_component_le {n : ℕ} {h : ℝ → ℝ} {C : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (hdC : ∀ a ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C)
    {a σ : ℝ} (ha : a ∈ Set.Icc wLeft wRight) (hσ : σ ∈ Set.Icc wLeft wRight)
    (z : St) (hz : z ∈ Metric.closedBall (baseState σ) (9 / 20)) (j : Fin 2) :
    ‖deriv (fun u : ℝ => (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) a‖ ≤ C := by
  have hσ7 : (7 : ℝ) / 10 ≤ σ := by have h := hσ.1; simp only [wLeft] at h; linarith
  have hσ1 : σ ≤ 1 := by have h := hσ.2; simp only [wRight] at h; linarith
  have ha_half : (1 : ℝ) / 2 < a := by have h := ha.1; simp only [wLeft] at h; linarith
  have ha_one : a < 1 := by have h := ha.2; simp only [wRight] at h; linarith
  obtain ⟨hz0, hz1, _⟩ :=
    Work.OddVolterra.Existence.state_ball_box wLeft_pos (by norm_num [wLeft]) σ ⟨hσ7, hσ1⟩ z
      (Metric.closedBall_subset_closedBall (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hz)
  have hF := differentiableAt_KvecM_vec (n := n) hh hsm1 ha_half ha_one hσ7 hz0 hz1
  calc ‖deriv (fun u : ℝ => (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) a‖
      = ‖(deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a) j‖ := by
        rw [deriv_apply_eq_fin2 hF j]
    _ ≤ ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ :=
        norm_le_pi_norm _ _
    _ ≤ C := hdC a ha σ hσ z hz

/-- Difference bound for the first-slot derivative of a component of `KvecM`, in the state. -/
private lemma KvecM_deriv_component_diff_le {n : ℕ} {h : ℝ → ℝ} {M : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (hdM : ∀ a ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a -
       deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a‖
        ≤ M * ‖z - z'‖)
    {a σ : ℝ} (ha : a ∈ Set.Icc wLeft wRight) (hσ : σ ∈ Set.Icc wLeft wRight)
    (z : St) (hz : z ∈ Metric.closedBall (baseState σ) (9 / 20))
    (z' : St) (hz' : z' ∈ Metric.closedBall (baseState σ) (9 / 20)) (j : Fin 2) :
    ‖deriv (fun u : ℝ => (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) a -
     deriv (fun u : ℝ => (KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) j) a‖
      ≤ M * ‖z - z'‖ := by
  have hσ7 : (7 : ℝ) / 10 ≤ σ := by have h := hσ.1; simp only [wLeft] at h; linarith
  have hσ1 : σ ≤ 1 := by have h := hσ.2; simp only [wRight] at h; linarith
  have ha_half : (1 : ℝ) / 2 < a := by have h := ha.1; simp only [wLeft] at h; linarith
  have ha_one : a < 1 := by have h := ha.2; simp only [wRight] at h; linarith
  obtain ⟨hz0, hz1, _⟩ :=
    Work.OddVolterra.Existence.state_ball_box wLeft_pos (by norm_num [wLeft]) σ ⟨hσ7, hσ1⟩ z
      (Metric.closedBall_subset_closedBall (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hz)
  obtain ⟨hz'0, hz'1, _⟩ :=
    Work.OddVolterra.Existence.state_ball_box wLeft_pos (by norm_num [wLeft]) σ ⟨hσ7, hσ1⟩ z'
      (Metric.closedBall_subset_closedBall (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hz')
  have hF := differentiableAt_KvecM_vec (n := n) hh hsm1 ha_half ha_one hσ7 hz0 hz1
  have hG := differentiableAt_KvecM_vec (n := n) hh hsm1 ha_half ha_one hσ7 hz'0 hz'1
  rw [deriv_apply_eq_fin2 hF j, deriv_apply_eq_fin2 hG j, ← Pi.sub_apply]
  exact le_trans (norm_le_pi_norm _ _) (hdM a ha σ hσ z hz z' hz')

/-! ## The target -/

theorem TW2_thetaM_state_unif_of_kvec (n : ℕ) (hn : 1 ≤ n) (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hkvec : Work.OddVolterra.Window.KvecMStateData n M C) :
    ∃ M' B' : ℝ, 0 ≤ M' ∧ 0 ≤ B' ∧ Work.OddVolterra.Window.ThetaMStateData n M' B' := by
  refine ⟨max 1 (Real.pi * M), max 2 (Real.pi * C),
    le_trans zero_le_one (le_max_left (1 : ℝ) (Real.pi * M)),
    le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left (2 : ℝ) (Real.pi * C)), ?_⟩
  intro h hh hsupp hsmall
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (le_trans hk (by omega)) s
  have hpos : Work.OddExistence.KdenPosOn h wLeft wRight := by
    intro u hu σ hσ t ht
    rw [Kden_eq_sqrt_krad]
    refine Real.sqrt_pos.mpr (krad_pos_of_region hsm1 ?_ ht)
    have h1 : (7 : ℝ) / 10 ≤ u := by have h := hu.1; simp only [wLeft] at h; linarith
    have h2 : (7 : ℝ) / 10 ≤ σ := by have h := hσ.1; simp only [wLeft] at h; linarith
    linarith
  have hdC : ∀ a ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C :=
    fun a ha σ hσ z hz => (hkvec h hh hsupp hsmall a ha σ hσ z hz z hz).2.2.1
  have hdM : ∀ a ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a -
       deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a‖
        ≤ M * ‖z - z'‖ :=
    fun a ha σ hσ z hz z' hz' => (hkvec h hh hsupp hsmall a ha σ hσ z hz z' hz').2.2.2
  intro s hs σ hσ z hz
  -- the integral representation of the first-slot derivative of `G2M`
  have hform : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) s =
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ => (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j)
            (s + τ * (σ - s))) := by
    intro j w hw
    have hraw := Work.OddExistence.Manifest.deriv_G2M_eq_integral_on_RcM (n := n) (h := h) hh
      wLeft_pos wLeft_le_wRight (le_of_lt wRight_lt_one) (by norm_num : (0 : ℝ) < 9 / 20)
      (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hpos j (s, (σ, w)) ⟨hs, hσ, hw⟩
    have hL : (fun u : ℝ => (Work.OddBridge.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j)
        = (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) := by
      funext u
      exact congrFun
        (Work.OddExistence.Manifest.G2M_eq_KernelExt n hh u σ (w 0) (w 1) (w 2) (w 3)) j
    have hR : (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (Work.OddBridge.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))))
        = (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))) := by
      funext τ
      have hKe : (fun u : ℝ => (Work.OddBridge.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j)
          = (fun u : ℝ => (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) := by
        funext u
        exact congrFun
          (Work.OddExistence.Manifest.KvecM_eq_KernelExt n hh u σ (w 0) (w 1) (w 2) (w 3)) j
      rw [hKe]
    rw [hL, hR] at hraw
    exact hraw
  -- pointwise bound of the integrand
  have hptC : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ∀ τ : ℝ, τ ∈ Set.Ioc (0 : ℝ) 1 →
        ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))‖
          ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by
    intro j w hw τ hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      simp
    · have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, le_of_lt h1⟩
      have hpt : s + τ * (σ - s) ∈ Set.Icc wLeft wRight := by
        refine ⟨?_, ?_⟩ <;> nlinarith [hs.1, hs.2, hσ.1, hσ.2, hτIcc.1, hτIcc.2]
      have hb := KvecM_deriv_component_le (n := n) hh hsm1 hdC hpt hσ w hw j
      have hw0 : (0 : ℝ) ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ :=
        inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτIcc.1]
      calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
            ((1 - τ) * deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))‖
          = (Real.sqrt (τ * (1 - τ)))⁻¹ *
            ((1 - τ) * ‖deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))‖) := by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg hw0, Real.norm_of_nonneg hτle]
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * C) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hτle) hw0
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C :=
            mul_le_mul_of_nonneg_left (by nlinarith [hτIcc.1, hC]) hw0
  -- value bound for the components of the `G2M`-derivative
  have hA : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) s‖
        ≤ Real.pi * C := by
    intro j w hw
    rw [hform j w hw]
    calc ‖∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))‖
        ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * C :=
          intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
            (Filter.Eventually.of_forall (fun τ hτ => hptC j w hw τ hτ))
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const C)
      _ = (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) * C := by
          rw [intervalIntegral.integral_mul_const]
      _ = Real.pi * C := by rw [Work.OddVolterra.Existence.abel_weight_integral]
  -- interval integrability of the integrand
  have hint : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))))
        volume (0 : ℝ) 1 := by
    intro j w hw
    refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const C).mono_fun' ?_ ?_
    · have hm : Measurable (fun τ : ℝ => deriv (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))) :=
        (measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j)).comp
          (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
      have hw' : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
        ((Real.continuous_sqrt.measurable).comp
          (measurable_id.mul (measurable_const.sub measurable_id))).inv
      exact (hw'.mul ((measurable_const.sub measurable_id).mul hm)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      exact hptC j w hw τ ⟨hτ.1, hτ.2⟩
  -- Lipschitz bound for the components of the `G2M`-derivative
  have hB : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ∀ (w' : St), w' ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) s -
       deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j) s‖
        ≤ Real.pi * M * ‖w - w'‖ := by
    intro j w hw w' hw'
    rw [hform j w hw, hform j w' hw',
      ← intervalIntegral.integral_sub (hint j w hw) (hint j w' hw')]
    have hseq : (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))
        - (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j) (s + τ * (σ - s))))
        = (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * (deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
            - deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
              (s + τ * (σ - s))))) := by
      funext τ; ring
    rw [hseq]
    have hpoint : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0 : ℝ) 1 →
        ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * (deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
            - deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
              (s + τ * (σ - s))))‖
          ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (M * ‖w - w'‖) := by
      filter_upwards with τ hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · subst h1; simp
      · have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, le_of_lt h1⟩
        have hpt : s + τ * (σ - s) ∈ Set.Icc wLeft wRight := by
          refine ⟨?_, ?_⟩ <;> nlinarith [hs.1, hs.2, hσ.1, hσ.2, hτIcc.1, hτIcc.2]
        have hb := KvecM_deriv_component_diff_le (n := n) hh hsm1 hdM hpt hσ w hw w' hw' j
        have hw0 : (0 : ℝ) ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ :=
          inv_nonneg.mpr (Real.sqrt_nonneg _)
        have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτIcc.1]
        have hMnn : (0 : ℝ) ≤ M * ‖w - w'‖ := mul_nonneg hM (norm_nonneg _)
        calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
              ((1 - τ) * (deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
                - deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
                  (s + τ * (σ - s))))‖
            = (Real.sqrt (τ * (1 - τ)))⁻¹ *
              ((1 - τ) * ‖deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
                - deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
                  (s + τ * (σ - s))‖) := by
              rw [norm_mul, norm_mul, Real.norm_of_nonneg hw0, Real.norm_of_nonneg hτle]
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * (M * ‖w - w'‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hτle) hw0
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (M * ‖w - w'‖) :=
              mul_le_mul_of_nonneg_left (by nlinarith [hτIcc.1, hMnn]) hw0
    calc ‖∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * (deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
            - deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
              (s + τ * (σ - s))))‖
        ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (M * ‖w - w'‖) :=
          intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
            hpoint
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (M * ‖w - w'‖))
      _ = (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) * (M * ‖w - w'‖) := by
          rw [intervalIntegral.integral_mul_const]
      _ = Real.pi * M * ‖w - w'‖ := by
          rw [Work.OddVolterra.Existence.abel_weight_integral]; ring
  -- assembly: the uniform bound
  constructor
  · rw [pi_norm_le_iff_of_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left (2 : ℝ) (Real.pi * C)))]
    intro i
    have hzmem : (s, (σ, z)) ∈ Work.OddExistence.Manifest.RcM wLeft wRight (9 / 20) :=
      ⟨hs, hσ, hz⟩
    fin_cases i
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (0 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (0 : Fin 4) = -z 2 := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg, Real.norm_eq_abs]
        have hz2 : |z 2| ≤ 2 :=
          (Work.OddExistence.Manifest.mem_RcM_facts wLeft_pos wLeft_le_wRight
            (le_of_lt wRight_lt_one) (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hzmem).2.2 2
        calc |z 2| ≤ 2 := hz2
          _ ≤ max 2 (Real.pi * C) := le_max_left _ _
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (1 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (1 : Fin 4) = -z 3 := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg, Real.norm_eq_abs]
        have hz3 : |z 3| ≤ 2 :=
          (Work.OddExistence.Manifest.mem_RcM_facts wLeft_pos wLeft_le_wRight
            (le_of_lt wRight_lt_one) (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hzmem).2.2 3
        calc |z 3| ≤ 2 := hz3
          _ ≤ max 2 (Real.pi * C) := le_max_left _ _
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (2 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (2 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg]
        calc ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s‖
            ≤ Real.pi * C := hA 0 z hz
          _ ≤ max 2 (Real.pi * C) := le_max_right _ _
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (3 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (3 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg]
        calc ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s‖
            ≤ Real.pi * C := hA 1 z hz
          _ ≤ max 2 (Real.pi * C) := le_max_right _ _
      simpa using hthis
  -- assembly: the state-Lipschitz estimate
  · intro z' hz'
    rw [pi_norm_le_iff_of_nonneg
      (mul_nonneg (le_trans zero_le_one (le_max_left (1 : ℝ) (Real.pi * M))) (norm_nonneg _))]
    intro i
    fin_cases i
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (0 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (0 : Fin 4) = -z 2 := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (0 : Fin 4) = -z' 2 := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        have hcoord : |z 2 - z' 2| ≤ ‖z - z'‖ := by
          have h := dist_le_pi_dist z z' (2 : Fin 4)
          rwa [Real.dist_eq] at h
        rw [show -z 2 - -z' 2 = -(z 2 - z' 2) by ring, norm_neg, Real.norm_eq_abs]
        calc |z 2 - z' 2| ≤ ‖z - z'‖ := hcoord
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (1 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (1 : Fin 4) = -z 3 := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (1 : Fin 4) = -z' 3 := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        have hcoord : |z 3 - z' 3| ≤ ‖z - z'‖ := by
          have h := dist_le_pi_dist z z' (3 : Fin 4)
          rwa [Real.dist_eq] at h
        rw [show -z 3 - -z' 3 = -(z 3 - z' 3) by ring, norm_neg, Real.norm_eq_abs]
        calc |z 3 - z' 3| ≤ ‖z - z'‖ := hcoord
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (2 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (2 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (2 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s) := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        rw [show -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
              - -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s)
              = -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s
                  - deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s)
              by ring, norm_neg]
        calc ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s
              - deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s‖
            ≤ Real.pi * M * ‖z - z'‖ := hB 0 z hz z' hz'
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (3 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (3 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (3 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s) := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        rw [show -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
              - -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s)
              = -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s
                  - deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s)
              by ring, norm_neg]
        calc ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s
              - deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s‖
            ≤ Real.pi * M * ‖z - z'‖ := hB 1 z hz z' hz'
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      simpa using hthis

end

end Work.OddVolterra.Window
