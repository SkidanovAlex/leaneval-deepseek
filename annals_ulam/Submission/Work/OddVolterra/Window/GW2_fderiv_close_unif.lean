import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.Window.GW_fderiv_close_unif

/-!
# Uniform closeness of the differential of the *smooth* cut-off datum `GW2`

`Work.OddVolterra.Window.GW2 n h s z = chiG2 s z • Godd n h s z` is the variant of the state
datum of the long-interval Volterra engine in which the state cut-off is the bump composed with
the *squared* Euclidean distance `wsq` (`WindowDefs`).  Unlike `GW`, the datum `GW2 n h s` is
smooth in the state on the whole window, which is what the engine asks for.

This file proves the uniform estimate

`‖fderiv (GW2 n h s ·) z - fderiv (GW2 n 0 s ·) (baseState s)‖ ≤ Cg ‖z - baseState s‖ + C₃ δ`

for `s ∈ [7/10, 19/20]`, `z` in the ball of radius `1` around `baseState s`, with constants
`Cg, C₃ ≥ 0` independent of the perturbation `h`, whose jets up to order `n + 2` are bounded
by `δ ≤ 1/100`, and whose support lies in `[1 - 2τ, 1 - τ]`.

The argument is the same two-case splitting as for `GW` (`GW_fderiv_close_unif`), with the two
cut-off thresholds shifted from `1/5` to `1/100`:

* `‖z - baseState s‖ < 1/100`: the smooth cut-off `chiG2` is locally `1`
  (`chiG2_eq_one_of_sq_le`), so `GW2 n h s` agrees with `Godd n h s` near `z` and near
  `baseState s`, and `Work.Anchor.deriv_close` gives the estimate with the uniform constants
  `C₁` (state slope) and `C₂` (slope in `δ`);
* `‖z - baseState s‖ ≥ 1/100`: both differentials are bounded by the uniform Lipschitz constant
  `M` of `GW2` on the tube `‖z - baseState s‖ ≤ 7/16` — directly when
  `‖z - baseState s‖ ≤ 2/5`, and through the vanishing of the cut-off
  (`chiG2_eq_zero_of_far`) when `‖z - baseState s‖ > 2/5` — and the slope constant
  `Cg = 200 M + 1` absorbs the factor `1/100`.

The Lipschitz constant of `GW2` on the tube comes from the Lipschitz property of the bump `cz2`
composed with the *squared* distance: `|wsq s u - wsq s v| ≤ (7/2) ‖u - v‖` on the tube.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## 1. The bump `cz2` is globally Lipschitz -/

lemma deriv_cz2_zero_of_one_lt_abs {x : ℝ} (hx : 1 < |x|) : deriv (cz2 : ℝ → ℝ) x = 0 := by
  have hopen : IsOpen {y : ℝ | 1 < |y|} := isOpen_lt continuous_const continuous_abs
  have hev : (cz2 : ℝ → ℝ) =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => ?_
    have hy' : 1 < |y| := hy
    exact cz2_eq_zero (by linarith [hy'])
  rw [hev.deriv_eq]
  simp

lemma exists_deriv_cz2_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖deriv (cz2 : ℝ → ℝ) x‖ ≤ C := by
  have hcont : Continuous (deriv (cz2 : ℝ → ℝ)) :=
    (ContDiffBump.contDiff cz2 : ContDiff ℝ (⊤ : ℕ∞) (cz2 : ℝ → ℝ)).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · exact le_trans (hC x hx) (le_max_left _ _)
  · have hx' : 1 < |x| := by
      rw [Set.mem_Icc, not_and_or] at hx
      rcases hx with h | h
      · have h1 : ¬((-1 : ℝ) ≤ x) := h
        rw [abs_of_neg (by linarith [not_le.mp h1])]
        linarith [not_le.mp h1]
      · have h1 : ¬(x ≤ (1 : ℝ)) := h
        rw [abs_of_pos (by linarith [not_le.mp h1])]
        linarith [not_le.mp h1]
    rw [deriv_cz2_zero_of_one_lt_abs hx', norm_zero]
    exact le_max_right _ _

/-- The squared-distance bump `cz2` is globally Lipschitz. -/
theorem cz2_lipschitz : ∃ L : NNReal, LipschitzWith L (cz2 : ℝ → ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_deriv_cz2_bound
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le
    ((ContDiffBump.contDiff cz2 : ContDiff ℝ (⊤ : ℕ∞) (cz2 : ℝ → ℝ)).differentiable (by simp))
    (fun x => ?_)⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC0]
  exact hC x

/-! ## 2. The Lipschitz property of the smooth state cut-off -/

/-- The real value of the Lipschitz constant `L * 7/2`. -/
lemma coe_mul_seven_halves (L : NNReal) :
    ((L * ((7 : ℝ) / 2).toNNReal : NNReal) : ℝ) = (7 / 2) * (L : ℝ) := by
  rw [NNReal.coe_mul, Real.coe_toNNReal ((7 : ℝ) / 2) (by norm_num)]
  ring

/-- The elementary factorisation of the difference of the squared distances. -/
lemma wsq_sub_wsq (s : ℝ) (u v : St) :
    wsq s u - wsq s v = ∑ i : Fin 4, (u i - v i) * (u i + v i - 2 * baseState s i) := by
  rw [wsq, wsq, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- On the tube `‖· - baseState s‖ ≤ 7/16` the squared distance is Lipschitz with constant
`7/2`. -/
lemma abs_wsq_sub_le {s : ℝ} {u v : St} (hu : ‖u - baseState s‖ ≤ 7 / 16)
    (hv : ‖v - baseState s‖ ≤ 7 / 16) :
    |wsq s u - wsq s v| ≤ (7 / 2) * ‖u - v‖ := by
  have hcoord : ∀ i : Fin 4, |u i - v i| ≤ ‖u - v‖ := by
    intro i
    have h := norm_le_pi_norm (u - v) i
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have hcoordb : ∀ i : Fin 4, |u i + v i - 2 * baseState s i| ≤ 7 / 8 := by
    intro i
    have h1 : |u i - baseState s i| ≤ 7 / 16 := by
      have h := norm_le_pi_norm (u - baseState s) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact le_trans h hu
    have h2 : |v i - baseState s i| ≤ 7 / 16 := by
      have h := norm_le_pi_norm (v - baseState s) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact le_trans h hv
    have h3 : u i + v i - 2 * baseState s i
        = (u i - baseState s i) + (v i - baseState s i) := by ring
    rw [h3]
    refine le_trans (abs_add_le _ _) ?_
    linarith
  rw [wsq_sub_wsq]
  calc |∑ i : Fin 4, (u i - v i) * (u i + v i - 2 * baseState s i)|
      ≤ ∑ i : Fin 4, |(u i - v i) * (u i + v i - 2 * baseState s i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin 4, |u i - v i| * |u i + v i - 2 * baseState s i| :=
        Finset.sum_congr rfl fun i _ => by rw [abs_mul]
    _ ≤ ∑ _i : Fin 4, ‖u - v‖ * (7 / 8) :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hcoord i) (hcoordb i) (abs_nonneg _)
          (norm_nonneg _)
    _ = 4 * (‖u - v‖ * (7 / 8)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ = (7 / 2) * ‖u - v‖ := by ring

/-- The cut-off `z ↦ cz2 (wsq s z)` is Lipschitz on the tube with constant `(7/2) L`, where `L`
is a Lipschitz constant of the bump `cz2`. -/
lemma cz2_comp_wsq_lipschitzOn {L : NNReal} (hL : LipschitzWith L (cz2 : ℝ → ℝ)) (s : ℝ) :
    LipschitzOnWith (L * ((7 : ℝ) / 2).toNNReal)
      (fun z : St => (cz2 : ℝ → ℝ) (wsq s z)) (tube s) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  have hu' : ‖u - baseState s‖ ≤ 7 / 16 := by
    rw [tube, Metric.mem_closedBall, dist_eq_norm] at hu; exact hu
  have hv' : ‖v - baseState s‖ ≤ 7 / 16 := by
    rw [tube, Metric.mem_closedBall, dist_eq_norm] at hv; exact hv
  have h1 : dist ((cz2 : ℝ → ℝ) (wsq s u)) ((cz2 : ℝ → ℝ) (wsq s v))
      ≤ (L : ℝ) * |wsq s u - wsq s v| := by
    have h := hL.dist_le_mul (wsq s u) (wsq s v)
    simpa only [Real.dist_eq] using h
  have h2 : |wsq s u - wsq s v| ≤ (7 / 2) * dist u v := by
    simpa only [dist_eq_norm] using abs_wsq_sub_le hu' hv'
  calc dist ((cz2 : ℝ → ℝ) (wsq s u)) ((cz2 : ℝ → ℝ) (wsq s v))
      ≤ (L : ℝ) * |wsq s u - wsq s v| := h1
    _ ≤ (L : ℝ) * ((7 / 2) * dist u v) := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
    _ = ((L * ((7 : ℝ) / 2).toNNReal : NNReal) : ℝ) * dist u v := by
        rw [coe_mul_seven_halves L]
        ring

/-! ## 3. The uniform Lipschitz constant of `GW2` on the tube -/

/-- **The smooth cut-off datum `GW2 n h s` is Lipschitz on the tube with a constant uniform
in `h`.**  On the window `GW2 n h s = cz2 (wsq s ·) • Godd n h s`, so the Lipschitz constant is
the one of `Godd n h s` on the tube plus the Lipschitz constant of `z ↦ cz2 (wsq s z)` times
the bound on `‖Godd n h s‖`; both are uniform in `h` by `Godd_tube_unif` (through
`cz2_comp_wsq_lipschitzOn` and `cz2_lipschitz`). -/
theorem GW2_lipschitz_tube_unif (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : NNReal, ∀ h : ℝ → ℝ, (∀ x : ℝ, |h x| ≤ 1 / 100) →
      (∀ x : ℝ, |deriv h x| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc wLeft wRight, LipschitzOnWith M (fun z => GW2 n h s z) (tube s) := by
  obtain ⟨K, hK0, hK⟩ := Godd_tube_unif n hn
  obtain ⟨L, hL⟩ := cz2_lipschitz
  have hK0' : (0 : ℝ) ≤ K + (7 / 2) * (L : ℝ) * K := by positivity
  refine ⟨(K + (7 / 2) * (L : ℝ) * K).toNNReal, fun h hb0 hb1 s hs => ?_⟩
  obtain ⟨hLipG, hbnd⟩ := hK h hb0 hb1 s hs
  have hKnn : ((K.toNNReal : NNReal) : ℝ) = K := Real.coe_toNNReal K hK0
  have hcs : (cs : ℝ → ℝ) s = 1 := cs_eq_one_of_mem hs
  have hcl : LipschitzOnWith (L * ((7 : ℝ) / 2).toNNReal)
      (fun z : St => (cz2 : ℝ → ℝ) (wsq s z)) (tube s) := cz2_comp_wsq_lipschitzOn hL s
  refine lipschitzOnWith_iff_norm_sub_le.mpr fun u hu v hv => ?_
  have hGWu : GW2 n h s u = (cz2 : ℝ → ℝ) (wsq s u) • Godd n h s u := by
    rw [GW2, chiG2, hcs, one_mul]
  have hGWv : GW2 n h s v = (cz2 : ℝ → ℝ) (wsq s v) • Godd n h s v := by
    rw [GW2, chiG2, hcs, one_mul]
  rw [hGWu, hGWv]
  have hsplit : (cz2 : ℝ → ℝ) (wsq s u) • Godd n h s u -
        (cz2 : ℝ → ℝ) (wsq s v) • Godd n h s v
      = (cz2 : ℝ → ℝ) (wsq s u) • (Godd n h s u - Godd n h s v) +
        ((cz2 : ℝ → ℝ) (wsq s u) - (cz2 : ℝ → ℝ) (wsq s v)) • Godd n h s v := by
    rw [smul_sub, sub_smul]
    abel
  rw [hsplit]
  have hcU : |(cz2 : ℝ → ℝ) (wsq s u)| ≤ 1 := abs_cz2_le_one _
  have hcd : ‖(cz2 : ℝ → ℝ) (wsq s u) - (cz2 : ℝ → ℝ) (wsq s v)‖
      ≤ (7 / 2) * (L : ℝ) * ‖u - v‖ := by
    have h := hcl.dist_le_mul u hu v hv
    rw [dist_eq_norm, coe_mul_seven_halves L] at h
    exact h
  have hgd : ‖Godd n h s u - Godd n h s v‖ ≤ K * ‖u - v‖ := by
    have h := hLipG.dist_le_mul u hu v hv
    rw [dist_eq_norm, hKnn] at h
    exact h
  have hgv : ‖Godd n h s v‖ ≤ K := (hbnd v hv).1
  calc ‖(cz2 : ℝ → ℝ) (wsq s u) • (Godd n h s u - Godd n h s v) +
        ((cz2 : ℝ → ℝ) (wsq s u) - (cz2 : ℝ → ℝ) (wsq s v)) • Godd n h s v‖
      ≤ ‖(cz2 : ℝ → ℝ) (wsq s u) • (Godd n h s u - Godd n h s v)‖ +
        ‖((cz2 : ℝ → ℝ) (wsq s u) - (cz2 : ℝ → ℝ) (wsq s v)) • Godd n h s v‖ :=
        norm_add_le _ _
    _ ≤ |(cz2 : ℝ → ℝ) (wsq s u)| * ‖Godd n h s u - Godd n h s v‖ +
        ‖(cz2 : ℝ → ℝ) (wsq s u) - (cz2 : ℝ → ℝ) (wsq s v)‖ * ‖Godd n h s v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * (K * ‖u - v‖) + ((7 / 2) * (L : ℝ) * ‖u - v‖) * K :=
        add_le_add (mul_le_mul hcU hgd (norm_nonneg _) (by norm_num))
          (mul_le_mul hcd hgv (norm_nonneg _) (by positivity))
    _ = (K + (7 / 2) * (L : ℝ) * K) * ‖u - v‖ := by ring
    _ = (((K + (7 / 2) * (L : ℝ) * K).toNNReal : NNReal) : ℝ) * ‖u - v‖ := by
        rw [Real.coe_toNNReal (K + (7 / 2) * (L : ℝ) * K) hK0']

/-! ## 4. The cut-off is locally `1` near the base state and locally `0` far from it -/

/-- Pointwise form of the locality of the smooth cut-off near the base state. -/
lemma GW2_eq_Godd_of_norm_le {n : ℕ} {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight)
    {z : St} (hz : ‖z - baseState s‖ ≤ 1 / 100) : GW2 n h s z = Godd n h s z := by
  rw [GW2, chiG2_eq_one_of_sq_le hs hz, one_smul]

/-- Pointwise form of the vanishing of the smooth cut-off far from the base state. -/
lemma GW2_eq_zero_of_norm_ge {n : ℕ} {h : ℝ → ℝ} {s : ℝ} {z : St}
    (hz : 2 / 5 ≤ ‖z - baseState s‖) : GW2 n h s z = 0 := by
  rw [GW2, chiG2_eq_zero_of_far hz, zero_smul]

lemma eventuallyEq_GW2_Godd {n : ℕ} {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight)
    {z : St} (hz : ‖z - baseState s‖ < 1 / 100) :
    (fun w : St => GW2 n h s w) =ᶠ[𝓝 z] (fun w : St => Godd n h s w) := by
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds z (by linarith : 0 < (1 / 100 - ‖z - baseState s‖) / 2))
    fun w hw => ?_
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : ‖w - baseState s‖ ≤ 1 / 100 := by
    calc ‖w - baseState s‖ ≤ ‖w - z‖ + ‖z - baseState s‖ := by
          rw [show w - baseState s = (w - z) + (z - baseState s) by abel]
          exact norm_add_le _ _
      _ ≤ 1 / 100 := by linarith
  exact GW2_eq_Godd_of_norm_le hs h1

lemma eventuallyEq_GW2_zero {n : ℕ} {h : ℝ → ℝ} {s : ℝ} {z : St}
    (hz : 2 / 5 < ‖z - baseState s‖) :
    (fun w : St => GW2 n h s w) =ᶠ[𝓝 z] (fun _ => 0) := by
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds z (by linarith : 0 < (‖z - baseState s‖ - 2 / 5) / 2))
    fun w hw => ?_
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : 2 / 5 ≤ ‖w - baseState s‖ := by
    have h2 := abs_norm_sub_norm_le (z - baseState s) (z - w)
    rw [show (z - baseState s) - (z - w) = w - baseState s by abel] at h2
    have h3 : ‖z - baseState s‖ - ‖z - w‖ ≤ ‖w - baseState s‖ := (le_abs_self _).trans h2
    have h4 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev _ _
    linarith [hw, h4]
  exact GW2_eq_zero_of_norm_ge h1

/-! ## 5. The uniform estimate -/

theorem GW2_fderiv_close_unif (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cg C₃ : ℝ, 0 ≤ Cg ∧ 0 ≤ C₃ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc Work.OddVolterra.Window.wLeft Work.OddVolterra.Window.wRight,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
        ‖fderiv ℝ (fun w => Work.OddVolterra.Window.GW2 n h s w) z -
           fderiv ℝ (fun w => Work.OddVolterra.Window.GW2 n 0 s w)
             (Work.OddVolterra.baseState s)‖
          ≤ Cg * ‖z - Work.OddVolterra.baseState s‖ + C₃ * δ := by
  obtain ⟨C₁, C₂, hC1, hC2, hdc⟩ := Work.Anchor.deriv_close n hn
  obtain ⟨M, hM⟩ := GW2_lipschitz_tube_unif n hn
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  refine ⟨max (C₁ + 1) (200 * (M : ℝ) + 1), C₂, le_max_of_le_left (by linarith), hC2.le, ?_⟩
  intro δ hδ hδ100 h hh hsupp hjet s hs z hz
  -- the two pointwise jet bounds, and those for the zero perturbation
  have hb0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => by
    have h0 := hjet 0 (Nat.zero_le _) x
    rw [iteratedDeriv_zero] at h0
    exact le_trans h0 hδ100
  have hb1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := fun x => by
    have h1 := hjet 1 (by omega) x
    rw [iteratedDeriv_one] at h1
    exact le_trans h1 hδ100
  have hz0 : ∀ x : ℝ, |(0 : ℝ → ℝ) x| ≤ 1 / 100 := fun x => by simp
  have hz1 : ∀ x : ℝ, |deriv (0 : ℝ → ℝ) x| ≤ 1 / 100 := fun x => by simp
  have hMh : LipschitzOnWith M (fun z => GW2 n h s z) (tube s) := hM h hb0 hb1 s hs
  have hM0 : LipschitzOnWith M (fun z => GW2 n 0 s z) (tube s) :=
    hM (fun _ => (0 : ℝ)) hz0 hz1 s hs
  have hs' : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20) :=
    ⟨by have h := hs.1; rw [wLeft] at h; linarith,
     by have h := hs.2; rw [wRight] at h; linarith⟩
  have hr1 : ‖z - baseState s‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
  rcases lt_or_ge ‖z - baseState s‖ (1 / 100) with hlt | hge
  · -- close to the base state: use the estimate of `deriv_close` with `ε = C₂ δ`
    have heq1 : (fun w : St => GW2 n h s w) =ᶠ[𝓝 z] (fun w => Godd n h s w) :=
      eventuallyEq_GW2_Godd hs hlt
    have heq0 : (fun w : St => GW2 n 0 s w) =ᶠ[𝓝 (baseState s)] (fun w => Godd n 0 s w) :=
      eventuallyEq_GW2_Godd hs (by simp)
    rw [heq1.fderiv_eq, heq0.fderiv_eq]
    have hb := hdc h hh hsupp δ hδ hδ100 hjet s hs' z (by linarith)
    have hCgle : C₁ ≤ max (C₁ + 1) (200 * (M : ℝ) + 1) :=
      le_trans (by linarith) (le_max_left _ _)
    have h1 : C₁ * ‖z - baseState s‖ ≤ max (C₁ + 1) (200 * (M : ℝ) + 1) *
        ‖z - baseState s‖ :=
      mul_le_mul_of_nonneg_right hCgle (norm_nonneg _)
    linarith
  · -- far from the base state: both differentials are bounded by the Lipschitz constant
    have hbndh : ‖fderiv ℝ (fun w : St => GW2 n h s w) z‖ ≤ (M : ℝ) := by
      by_cases hr : ‖z - baseState s‖ ≤ 2 / 5
      · have hnb : tube s ∈ 𝓝 z := by
          refine Filter.mem_of_superset
            (Metric.ball_mem_nhds z (by linarith : 0 < 7 / 16 - ‖z - baseState s‖)) ?_
          intro w hw
          rw [Metric.mem_ball, dist_eq_norm] at hw
          rw [tube, Metric.mem_closedBall, dist_eq_norm]
          calc ‖w - baseState s‖ ≤ ‖w - z‖ + ‖z - baseState s‖ := by
                rw [show w - baseState s = (w - z) + (z - baseState s) by abel]
                exact norm_add_le _ _
            _ ≤ 7 / 16 := by linarith
        exact norm_fderiv_le_of_lipschitzOn ℝ hnb hMh
      · have hr' : 2 / 5 < ‖z - baseState s‖ := lt_of_not_ge hr
        rw [(eventuallyEq_GW2_zero (h := h) hr').fderiv_eq]
        simp
    have hbnd0 : ‖fderiv ℝ (fun w : St => GW2 n 0 s w) (baseState s)‖ ≤ (M : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (Metric.closedBall_mem_nhds _ (by norm_num : (0 : ℝ) < 7 / 16)) hM0
    have hsum : ‖fderiv ℝ (fun w : St => GW2 n h s w) z -
        fderiv ℝ (fun w : St => GW2 n 0 s w) (baseState s)‖ ≤ (M : ℝ) + (M : ℝ) :=
      le_trans (norm_sub_le _ _) (add_le_add hbndh hbnd0)
    have hmax : 200 * (M : ℝ) + 1 ≤ max (C₁ + 1) (200 * (M : ℝ) + 1) := le_max_right _ _
    have hmax0 : (0 : ℝ) ≤ max (C₁ + 1) (200 * (M : ℝ) + 1) := by
      refine le_trans ?_ (le_max_right _ _); linarith
    have hr : (1 / 100 : ℝ) ≤ ‖z - baseState s‖ := hge
    have hkey : (M : ℝ) + (M : ℝ) ≤ max (C₁ + 1) (200 * (M : ℝ) + 1) *
        ‖z - baseState s‖ := by
      have h1 : (200 * (M : ℝ) + 1) * (1 / 100) ≤ max (C₁ + 1) (200 * (M : ℝ) + 1) *
          ‖z - baseState s‖ :=
        mul_le_mul hmax hr (by norm_num) hmax0
      nlinarith [h1, hMnn]
    linarith [hsum, hkey, mul_nonneg hC2.le hδ.le]

end

end Work.OddVolterra.Window

