import Mathlib
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.Existence.window_deriv_close_core

/-!
# Derivative closeness of the clamped state datum `Gcl`

The clamped state datum of the odd window construction is

`Gcl n h s z = wChiG s z • diagForm n h s z`,

`wChiG s z = wCs s · wCz (z - baseState s)` being the product of the slope and state cut-offs and
`diagForm` the explicit diagonal form of the paper's state datum `𝐆`.

This file proves `Work.OddVolterra.WinData.gcl_deriv_close`: with constants `C, L` independent of
`h`, for every smooth `h` whose first three derivatives are bounded by `δ ≤ 1/100`, every slope
`s ∈ [1/4, 19/20]` and every pair of states `z, z'` in the ball of radius `9/20` around
`baseState s`, the clamped data are `C`-`δ`-close to the unperturbed ones, both in value and in
the slope derivative, and both value and slope derivative are `L`-Lipschitz in the state.

The proof has two halves.

* **The state ball lies inside the inner ball of the state cut-off.**  Since `9/20 < wRho = 1/2`,
  on the ball `wCz (z - baseState s) = 1`, and the slope cut-off is `1` on the whole window
  (`wCs` is `1` on the closed ball of radius `7/20` around `3/5`, i.e. on `[1/4, 19/20]`).  Hence
  `Gcl n g s z = diagForm n g s z` at the base slope `s`; and — because the state cut-off is `1`
  on a *two-sided* neighbourhood of `s` — the function `u ↦ Gcl n g u z` agrees on a neighbourhood
  of `s` with `u ↦ wCs u • diagForm n g u z`.
* **Estimates for `diagForm`.**  The four estimates for the unclamped diagonal form (`h`-closeness
  of value and of the slope derivative, `z`-Lipschitz continuity of each) are proved here from the
  already established `Existence.DiagClose.diagForm_component_estimates` and an application of
  `Window.JetCurve_box` to the two smooth outer functions `Phi1`, `Phi2` of the diagonal form.

The extra factor `wCs` is then peeled off with the product rule: the slope derivative of
`Gcl n g · z` at `s` is `wCs s • deriv (diagForm n g · z) s + deriv wCs s • diagForm n g s z`, and
the additional term is controlled by the value estimate and the bound `|deriv wCs s| ≤ B` on the
window.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff

noncomputable section

namespace GclClose

open Work.OddVolterra.Existence.DiagClose

/-! ## Elementary facts about the base state and the cut-offs -/

/-- The base state is smooth. -/
lemma contDiff_baseState : ContDiff ℝ (⊤ : ℕ∞) (baseState : ℝ → St) :=
  Existence.contDiff_baseState_comp.comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : St))))

lemma continuous_baseState : Continuous (baseState : ℝ → St) :=
  Existence.contDiff_baseState_comp.continuous.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => (0 : St))))

/-- The derivative of the slope cut-off is bounded on the window. -/
lemma exists_bound_deriv_wCs :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      |deriv (wCs : ℝ → ℝ) s| ≤ B := by
  have hcont : Continuous (deriv (wCs : ℝ → ℝ)) := by
    have h := wCs_contDiff.iterate_deriv 1
    simpa [Function.iterate_one] using h.continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
  have h := hB s hs
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- The state cut-off equals `1` on a two-sided neighbourhood of `s`, for every state `z` in the
ball of radius `9/20` around `baseState s`. -/
lemma eventually_wCz_eq_one {s : ℝ} {z : St} (hz : ‖z - baseState s‖ ≤ 9 / 20) :
    ∀ᶠ u in 𝓝 s, (wCz : St → ℝ) (z - baseState u) = 1 := by
  have hcont : Continuous (fun u : ℝ => ‖z - baseState u‖) :=
    (continuous_const.sub continuous_baseState).norm
  have hopen : IsOpen {u : ℝ | ‖z - baseState u‖ < wCz.rIn} :=
    isOpen_lt hcont continuous_const
  have hlt : ‖z - baseState s‖ < wCz.rIn := by rw [wCz_rIn, wRho]; linarith
  filter_upwards [hopen.mem_nhds hlt] with u hu
  exact ContDiffBump.one_of_mem_closedBall wCz
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hu)

/-- The zero function has vanishing iterated derivatives. -/
lemma iteratedDeriv_zero_fun : ∀ k : ℕ, iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => 0
  | 0 => by funext y; simp
  | (k + 1) => by
      rw [iteratedDeriv_succ, iteratedDeriv_zero_fun k]
      funext y
      simp [deriv_const]

lemma abs_iteratedDeriv_zero_fun_le {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x| ≤ δ := by
  intro k _ x
  rw [congrFun (iteratedDeriv_zero_fun k) x]
  simpa using hδ

/-! ## Undoing the cut-offs -/

/-- At the base slope the clamped datum equals the unclamped diagonal form. -/
lemma Gcl_eq_diagForm {n : ℕ} {g : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20))
    {z : St} (hz : ‖z - baseState s‖ ≤ 9 / 20) : Gcl n g s z = diagForm n g s z := by
  have hs' : s ∈ Set.Icc wLo wHi := by rw [wLo, wHi]; exact hs
  have hz' : ‖z - baseState s‖ ≤ wRho := by rw [wRho]; linarith
  rw [Gcl_eq_Godd hs' hz', Godd_eq_diagForm]

/-- The clamped datum, as a function of the slope, agrees with the slope cut-off times the
unclamped diagonal form on a neighbourhood of the base slope. -/
lemma Gcl_eventuallyEq_smul {n : ℕ} {g : ℝ → ℝ} {s : ℝ} {z : St}
    (hz : ‖z - baseState s‖ ≤ 9 / 20) :
    (fun u : ℝ => Gcl n g u z) =ᶠ[𝓝 s] (fun u : ℝ => (wCs : ℝ → ℝ) u • diagForm n g u z) := by
  filter_upwards [eventually_wCz_eq_one hz] with u hu
  rw [Gcl, wChiG, hu, mul_one]

/-! ## Differentiability of the diagonal form in the slope -/

/-- The diagonal form is differentiable in the slope variable at the base slope. -/
lemma differentiableAt_diagForm (n : ℕ) {h : ℝ → ℝ} {δ : ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) {z : St}
    (hz : ‖z - baseState s‖ ≤ 9 / 20) :
    DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z) s := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hjet 0 (by norm_num) s)
  have hmem : jet h z s ∈ K := jet_mem_K hδ0 hδ1 hjet hs hz
  have hUK : jet h z s ∈ U := K_subset_U hmem
  have hcomp : ∀ (F : Jet → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F U →
      DifferentiableAt ℝ (fun u : ℝ => F (jet h z u)) s := by
    intro F hF
    have hFa : ContDiffAt ℝ (⊤ : ℕ∞) F (jet h z s) := hF.contDiffAt (isOpen_U.mem_nhds hUK)
    exact (hFa.comp s (contDiff_jet hh z).contDiffAt).differentiableAt (by simp)
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · show DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z (0 : Fin 4)) s
    rw [show (fun u : ℝ => diagForm n h u z (0 : Fin 4)) = fun _ : ℝ => z 0 from by
      funext u; simp [diagForm]]
    exact differentiableAt_const _
  · show DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z (1 : Fin 4)) s
    rw [show (fun u : ℝ => diagForm n h u z (1 : Fin 4)) = fun _ : ℝ => z 1 from by
      funext u; simp [diagForm]]
    exact differentiableAt_const _
  · show DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z (2 : Fin 4)) s
    rw [show (fun u : ℝ => diagForm n h u z (2 : Fin 4)) = fun u => Phi1 n (jet h z u) from
      (Phi1_comp n h z).symm]
    exact hcomp (Phi1 n) (contDiffOn_Phi1 n)
  · show DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z (3 : Fin 4)) s
    rw [show (fun u : ℝ => diagForm n h u z (3 : Fin 4)) = fun u => Phi2 n (jet h z u) from
      (Phi2_comp n h z).symm]
    exact hcomp (Phi2 n) (contDiffOn_Phi2 n)

/-! ## The value Lipschitz estimate for the diagonal form -/

/-- The value of the diagonal form is Lipschitz in the state, componentwise.  This complements
`Existence.DiagClose.diagForm_component_estimates`, which controls the *slope derivative* in `z`,
and is proved with `Window.JetCurve_box` applied to the jet curves of the two states. -/
lemma diagForm_value_z_lip (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ →
      δ ≤ 1 / 100 → (∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState s) (9 / 20), ∀ i : Fin 4,
      |(diagForm n h s z) i - (diagForm n h s z') i| ≤ C * dist z z' := by
  obtain ⟨C1, hC10, hC1⟩ := Window.JetCurve_box (Phi1 n) isOpen_U convex_K isCompact_K
    K_subset_U (contDiffOn_Phi1 n) (B' := 1) (by norm_num)
  obtain ⟨C2, hC20, hC2⟩ := Window.JetCurve_box (Phi2 n) isOpen_U convex_K isCompact_K
    K_subset_U (contDiffOn_Phi2 n) (B' := 1) (by norm_num)
  refine ⟨max (max C1 C2) 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro h δ hh hδ hδ1 hjet s hs z hz z' hz' i
  have hδnn : 0 ≤ δ := hδ.le
  have hC1le : C1 ≤ max (max C1 C2) 1 := le_trans (le_max_left C1 C2) (le_max_left _ _)
  have hC2le : C2 ≤ max (max C1 C2) 1 := le_trans (le_max_right C1 C2) (le_max_left _ _)
  have h1le : (1 : ℝ) ≤ max (max C1 C2) 1 := le_max_right _ _
  have hzd : ‖z - baseState s‖ ≤ 9 / 20 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hz'd : ‖z' - baseState s‖ ≤ 9 / 20 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hhd : DifferentiableAt ℝ h s := (hh.differentiable (by simp)).differentiableAt
  have hhd2 : DifferentiableAt ℝ (deriv h) s := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
      simpa [Function.iterate_one] using hh.iterate_deriv 1
    exact (hd.differentiable (by simp)).differentiableAt
  have hb1 : |deriv h s| ≤ δ := by
    have := hjet 1 (by norm_num) s; rwa [iteratedDeriv_one] at this
  have hb2 : |deriv (deriv h) s| ≤ δ := by
    have := hjet 2 (by norm_num) s
    rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at this
  have hb1' : |deriv h s| ≤ 1 := le_trans hb1 (le_trans hδ1 (by norm_num))
  have hb2' : |deriv (deriv h) s| ≤ 1 := le_trans hb2 (le_trans hδ1 (by norm_num))
  have hd1 : ‖deriv (jet h z) s‖ ≤ 1 :=
    norm_deriv_jet_le hhd hhd2 z (by norm_num) (by norm_num) hb1' hb2'
  have hd0 : ‖deriv (jet h z') s‖ ≤ 1 :=
    norm_deriv_jet_le hhd hhd2 z' (by norm_num) (by norm_num) hb1' hb2'
  have hmem1 : jet h z s ∈ K := jet_mem_K hδnn hδ1 hjet hs hzd
  have hmem0 : jet h z' s ∈ K := jet_mem_K hδnn hδ1 hjet hs hz'd
  have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (jet h z) := contDiff_jet hh z
  have hcd0 : ContDiff ℝ (⊤ : ℕ∞) (jet h z') := contDiff_jet hh z'
  have hsub : ‖jet h z s - jet h z' s‖ ≤ dist z z' := norm_jet_sub_state z z' s
  have hdsub : ‖deriv (jet h z) s - deriv (jet h z') s‖ ≤ dist z z' := by
    rw [deriv_jet hhd hhd2 z, deriv_jet hhd hhd2 z', sub_self, norm_zero]
    exact dist_nonneg
  have app1 : |Phi1 n (jet h z s) - Phi1 n (jet h z' s)| ≤ C1 * dist z z' :=
    (hC1 (jet h z) (jet h z') s (dist z z') dist_nonneg hcd1 hcd0 hmem1 hmem0 hd1 hd0 hsub
      hdsub).2.2.2.2.1
  have app2 : |Phi2 n (jet h z s) - Phi2 n (jet h z' s)| ≤ C2 * dist z z' :=
    (hC2 (jet h z) (jet h z') s (dist z z') dist_nonneg hcd1 hcd0 hmem1 hmem0 hd1 hd0 hsub
      hdsub).2.2.2.2.1
  have hzcomp0 : |z 0 - z' 0| ≤ dist z z' := by
    have h := norm_le_pi_norm (z - z') 0
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    rw [dist_eq_norm]
    exact h
  have hzcomp1 : |z 1 - z' 1| ≤ dist z z' := by
    have h := norm_le_pi_norm (z - z') 1
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    rw [dist_eq_norm]
    exact h
  have h2 : (diagForm n h s z) (2 : Fin 4) = Phi1 n (jet h z s) :=
    congrFun (Phi1_comp n h z).symm s
  have h2' : (diagForm n h s z') (2 : Fin 4) = Phi1 n (jet h z' s) :=
    congrFun (Phi1_comp n h z').symm s
  have h3 : (diagForm n h s z) (3 : Fin 4) = Phi2 n (jet h z s) :=
    congrFun (Phi2_comp n h z).symm s
  have h3' : (diagForm n h s z') (3 : Fin 4) = Phi2 n (jet h z' s) :=
    congrFun (Phi2_comp n h z').symm s
  fin_cases i
  · show |(diagForm n h s z) (0 : Fin 4) - (diagForm n h s z') (0 : Fin 4)| ≤
      max (max C1 C2) 1 * dist z z'
    have h0 : (diagForm n h s z) (0 : Fin 4) = z 0 := by simp [diagForm]
    have h0' : (diagForm n h s z') (0 : Fin 4) = z' 0 := by simp [diagForm]
    rw [h0, h0']
    exact le_trans hzcomp0 (le_mul_of_one_le_left dist_nonneg h1le)
  · show |(diagForm n h s z) (1 : Fin 4) - (diagForm n h s z') (1 : Fin 4)| ≤
      max (max C1 C2) 1 * dist z z'
    have h1 : (diagForm n h s z) (1 : Fin 4) = z 1 := by simp [diagForm]
    have h1' : (diagForm n h s z') (1 : Fin 4) = z' 1 := by simp [diagForm]
    rw [h1, h1']
    exact le_trans hzcomp1 (le_mul_of_one_le_left dist_nonneg h1le)
  · show |(diagForm n h s z) (2 : Fin 4) - (diagForm n h s z') (2 : Fin 4)| ≤
      max (max C1 C2) 1 * dist z z'
    rw [h2, h2']
    exact le_trans app1 (mul_le_mul_of_nonneg_right hC1le dist_nonneg)
  · show |(diagForm n h s z) (3 : Fin 4) - (diagForm n h s z') (3 : Fin 4)| ≤
      max (max C1 C2) 1 * dist z z'
    rw [h3, h3']
    exact le_trans app2 (mul_le_mul_of_nonneg_right hC2le dist_nonneg)

/-! ## The four estimates for the diagonal form -/

/-- The four estimates for the diagonal form: `h`-closeness of the value and of the slope
derivative, and `z`-Lipschitz continuity of both. -/
lemma diagForm_estimates (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState s) (9 / 20),
      (dist (diagForm n h s z) (diagForm n 0 s z) ≤ C * δ ∧
       dist (deriv (fun u : ℝ => diagForm n h u z) s)
            (deriv (fun u : ℝ => diagForm n 0 u z) s) ≤ C * δ ∧
       dist (deriv (fun u : ℝ => diagForm n h u z) s)
            (deriv (fun u : ℝ => diagForm n h u z') s) ≤ C * dist z z' ∧
       dist (diagForm n h s z) (diagForm n h s z') ≤ C * dist z z') := by
  obtain ⟨C0, hC00, hC0⟩ := Existence.DiagClose.diagForm_component_estimates n hn
  obtain ⟨Cl, hCl0, hCl⟩ := diagForm_value_z_lip n
  refine ⟨max C0 Cl, le_trans hC00 (le_max_left _ _), ?_⟩
  intro h δ hh hδ hδ1 hjet s hs z hz z' hz'
  have hδnn : 0 ≤ δ := hδ.le
  have hC0le : C0 ≤ max C0 Cl := le_max_left _ _
  have hClle : Cl ≤ max C0 Cl := le_max_right _ _
  have hCnn : (0 : ℝ) ≤ max C0 Cl := le_trans hC00 hC0le
  have hzd : ‖z - baseState s‖ ≤ 9 / 20 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hz'd : ‖z' - baseState s‖ ≤ 9 / 20 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hDh : DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z) s :=
    differentiableAt_diagForm n hh hδ1 hjet hs hzd
  have hD0 : DifferentiableAt ℝ (fun u : ℝ => diagForm n 0 u z) s :=
    differentiableAt_diagForm n contDiff_const hδ1 (abs_iteratedDeriv_zero_fun_le hδnn) hs hzd
  have hDh' : DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z') s :=
    differentiableAt_diagForm n hh hδ1 hjet hs hz'd
  have hcomp : ∀ i : Fin 4,
      (|(diagForm n h s z) i - (diagForm n 0 s z) i| ≤ C0 * δ ∧
       |deriv (fun u : ℝ => diagForm n h u z i) s -
          deriv (fun u : ℝ => diagForm n 0 u z i) s| ≤ C0 * δ ∧
       |deriv (fun u : ℝ => diagForm n h u z i) s -
          deriv (fun u : ℝ => diagForm n h u z' i) s| ≤ C0 * dist z z') :=
    fun i => hC0 h δ hh hδ hδ1 hjet s hs z hz z' hz' i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, pi_norm_le_iff_of_nonneg (mul_nonneg hCnn hδnn)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact le_trans (hcomp i).1 (mul_le_mul_of_nonneg_right hC0le hδnn)
  · rw [dist_eq_norm, deriv_pi (differentiableAt_pi.mp hDh),
      deriv_pi (differentiableAt_pi.mp hD0),
      pi_norm_le_iff_of_nonneg (mul_nonneg hCnn hδnn)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact le_trans (hcomp i).2.1 (mul_le_mul_of_nonneg_right hC0le hδnn)
  · rw [dist_eq_norm, deriv_pi (differentiableAt_pi.mp hDh),
      deriv_pi (differentiableAt_pi.mp hDh'),
      pi_norm_le_iff_of_nonneg (mul_nonneg hCnn dist_nonneg)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact le_trans (hcomp i).2.2 (mul_le_mul_of_nonneg_right hC0le dist_nonneg)
  · rw [dist_eq_norm, pi_norm_le_iff_of_nonneg (mul_nonneg hCnn dist_nonneg)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact le_trans (hCl h δ hh hδ hδ1 hjet s hs z hz z' hz' i)
      (mul_le_mul_of_nonneg_right hClle dist_nonneg)

end GclClose

/-! ## The target -/

theorem gcl_deriv_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      (dist (deriv (fun u : ℝ => Work.OddVolterra.WinData.Gcl n h u z) s)
            (deriv (fun u : ℝ => Work.OddVolterra.WinData.Gcl n 0 u z) s) ≤ C * δ ∧
       dist (deriv (fun u : ℝ => Work.OddVolterra.WinData.Gcl n h u z) s)
            (deriv (fun u : ℝ => Work.OddVolterra.WinData.Gcl n h u z') s)
          ≤ L * dist z z' ∧
       dist (Work.OddVolterra.WinData.Gcl n h s z) (Work.OddVolterra.WinData.Gcl n 0 s z)
          ≤ C * δ ∧
       dist (Work.OddVolterra.WinData.Gcl n h s z) (Work.OddVolterra.WinData.Gcl n h s z')
          ≤ L * dist z z') := by
  obtain ⟨C0, hC0nn, hC0⟩ := GclClose.diagForm_estimates n hn
  obtain ⟨B, hBnn, hB⟩ := GclClose.exists_bound_deriv_wCs
  have hKnn : 0 ≤ (B + 1) * C0 := mul_nonneg (by linarith) hC0nn
  refine ⟨(B + 1) * C0, (B + 1) * C0, hKnn, hKnn, ?_⟩
  intro h δ hh hδ hδ1 hjet s hs z hz z' hz'
  have hδnn : 0 ≤ δ := hδ.le
  have hC0le : C0 ≤ (B + 1) * C0 := by nlinarith [hBnn, hC0nn]
  have hzd : ‖z - baseState s‖ ≤ 9 / 20 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hz'd : ‖z' - baseState s‖ ≤ 9 / 20 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hE := hC0 h δ hh hδ hδ1 hjet s hs z hz z' hz'
  have hE1 : ‖diagForm n h s z - diagForm n 0 s z‖ ≤ C0 * δ := by
    rw [← dist_eq_norm]; exact hE.1
  have hE2 : ‖deriv (fun u : ℝ => diagForm n h u z) s -
      deriv (fun u : ℝ => diagForm n 0 u z) s‖ ≤ C0 * δ := by
    rw [← dist_eq_norm]; exact hE.2.1
  have hE3 : ‖deriv (fun u : ℝ => diagForm n h u z) s -
      deriv (fun u : ℝ => diagForm n h u z') s‖ ≤ C0 * dist z z' := by
    rw [← dist_eq_norm]; exact hE.2.2.1
  have hE4 : ‖diagForm n h s z - diagForm n h s z'‖ ≤ C0 * dist z z' := by
    rw [← dist_eq_norm]; exact hE.2.2.2
  have hDh : DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z) s :=
    GclClose.differentiableAt_diagForm n hh hδ1 hjet hs hzd
  have hD0 : DifferentiableAt ℝ (fun u : ℝ => diagForm n 0 u z) s :=
    GclClose.differentiableAt_diagForm n contDiff_const hδ1
      (GclClose.abs_iteratedDeriv_zero_fun_le hδnn) hs hzd
  have hDh' : DifferentiableAt ℝ (fun u : ℝ => diagForm n h u z') s :=
    GclClose.differentiableAt_diagForm n hh hδ1 hjet hs hz'd
  have hwCs : HasDerivAt (fun u : ℝ => (wCs : ℝ → ℝ) u) (deriv (wCs : ℝ → ℝ) s) s :=
    (wCs_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hderh : deriv (fun u : ℝ => Gcl n h u z) s
      = (wCs : ℝ → ℝ) s • deriv (fun u : ℝ => diagForm n h u z) s
        + deriv (wCs : ℝ → ℝ) s • diagForm n h s z := by
    rw [Filter.EventuallyEq.deriv_eq (GclClose.Gcl_eventuallyEq_smul (n := n) (g := h) hzd)]
    exact (hwCs.smul hDh.hasDerivAt).deriv
  have hev0 : (fun u : ℝ => Gcl n 0 u z)
      =ᶠ[𝓝 s] (fun u : ℝ => (wCs : ℝ → ℝ) u • diagForm n 0 u z) :=
    GclClose.Gcl_eventuallyEq_smul (n := n) (g := (0 : ℝ → ℝ)) hzd
  have hder0 : deriv (fun u : ℝ => Gcl n 0 u z) s
      = (wCs : ℝ → ℝ) s • deriv (fun u : ℝ => diagForm n 0 u z) s
        + deriv (wCs : ℝ → ℝ) s • diagForm n 0 s z := by
    rw [Filter.EventuallyEq.deriv_eq hev0]
    exact (hwCs.smul hD0.hasDerivAt).deriv
  have hderh' : deriv (fun u : ℝ => Gcl n h u z') s
      = (wCs : ℝ → ℝ) s • deriv (fun u : ℝ => diagForm n h u z') s
        + deriv (wCs : ℝ → ℝ) s • diagForm n h s z' := by
    rw [Filter.EventuallyEq.deriv_eq (GclClose.Gcl_eventuallyEq_smul (n := n) (g := h) hz'd)]
    exact (hwCs.smul hDh'.hasDerivAt).deriv
  have hwsle : |(wCs : ℝ → ℝ) s| ≤ 1 := by
    rw [abs_of_nonneg (wCs_nonneg s)]; exact wCs_le_one s
  have hbound : ∀ (x y : St) (a : ℝ), ‖x‖ ≤ a → ‖y‖ ≤ a → 0 ≤ a →
      ‖(wCs : ℝ → ℝ) s • x + deriv (wCs : ℝ → ℝ) s • y‖ ≤ (B + 1) * a := by
    intro x y a hx hy ha
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |(wCs : ℝ → ℝ) s| * ‖x‖ ≤ 1 * a :=
      mul_le_mul hwsle hx (norm_nonneg _) (by norm_num)
    have h2 : |deriv (wCs : ℝ → ℝ) s| * ‖y‖ ≤ B * a :=
      mul_le_mul (hB s hs) hy (norm_nonneg _) hBnn
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]
    have hsplit : deriv (fun u : ℝ => Gcl n h u z) s - deriv (fun u : ℝ => Gcl n 0 u z) s
        = (wCs : ℝ → ℝ) s • (deriv (fun u : ℝ => diagForm n h u z) s
              - deriv (fun u : ℝ => diagForm n 0 u z) s)
          + deriv (wCs : ℝ → ℝ) s • (diagForm n h s z - diagForm n 0 s z) := by
      rw [hderh, hder0, smul_sub, smul_sub]
      abel
    rw [hsplit]
    refine le_trans (hbound _ _ (C0 * δ) hE2 hE1 (mul_nonneg hC0nn hδnn)) ?_
    exact le_of_eq (by ring)
  · rw [dist_eq_norm]
    have hsplit : deriv (fun u : ℝ => Gcl n h u z) s - deriv (fun u : ℝ => Gcl n h u z') s
        = (wCs : ℝ → ℝ) s • (deriv (fun u : ℝ => diagForm n h u z) s
              - deriv (fun u : ℝ => diagForm n h u z') s)
          + deriv (wCs : ℝ → ℝ) s • (diagForm n h s z - diagForm n h s z') := by
      rw [hderh, hderh', smul_sub, smul_sub]
      abel
    rw [hsplit]
    refine le_trans (hbound _ _ (C0 * dist z z') hE3 hE4 (mul_nonneg hC0nn dist_nonneg)) ?_
    exact le_of_eq (by ring)
  · rw [dist_eq_norm, GclClose.Gcl_eq_diagForm hs hzd, GclClose.Gcl_eq_diagForm hs hzd]
    exact le_trans hE1 (mul_le_mul_of_nonneg_right hC0le hδnn)
  · rw [dist_eq_norm, GclClose.Gcl_eq_diagForm hs hzd, GclClose.Gcl_eq_diagForm hs hz'd]
    exact le_trans hE4 (mul_le_mul_of_nonneg_right hC0le dist_nonneg)

end

end Work.OddVolterra.WinData
