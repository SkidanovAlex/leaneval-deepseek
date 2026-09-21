import Mathlib
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.WinData.win_lines
import Submission.Work.OddVolterra.WinData.source_contDiffOn
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddExistence.Manifest.thetaM_lipschitz
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint
import Submission.Work.OddVolterra.WinData.gcl_contDiffOn
import Submission.Work.OddVolterra.WinData.tcl_contDiffOn

/-!
# The smooth upgrade of a continuous solution of the odd Volterra system

The window construction of the odd case produces a *continuous* `Z : ℝ → St` solving the paper's
Volterra system

`Godd n h s (Z s) = ∫_σ in s..1, Theta n h s σ (Z σ) + Xi n h s`   on `(1/4, 1)`

with `Z = baseState` for `s ≥ 1 - τ` and `dist (Z s) (baseState s) ≤ 1/2` on `[1/4, 19/20]`.
This file upgrades `Z` to a `C^∞` function on `[1/4, 19/20]`.

The route is the general fixed-point bootstrap
`Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint`, applied to the *clamped*
data `Gcl`, `Tcl`, `Xcl` of `WinData/win_data.lean`:

* `Gcl`, `Tcl`, `Xcl` are globally `C^∞` (the clamps cut the data off inside the region where the
  Abel radicands are positive, see the modules `gcl_contDiffOn`, `tcl_contDiffOn` and
  `contDiffOn_Xcl` below);
* on `[1/4, 19/20]` the state `Z s` lies in the ball where the clamps are `1`, so the clamped
  system is *the same* equation as the paper's system there (the `ThetaM = Theta` conversion off
  the diagonal, the tail `Z σ = baseState σ` on `σ ≥ 19/20`, and the frozen-tail summand of `Xcl`);
* the linearization `fderiv ℝ (fun z => Gcl n h s z) (Z s)` is invertible: `Godd` is `1/2`-close
  to `baseState` with a modulus on the state ball
  (`godd_injective_modulus_state_ball_compat`), and this injectivity survives the clamping and the
  passage to the boundary of the ball (`fderiv_injective_of_modulus_on_ball`).
-/

set_option maxHeartbeats 800000

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The source `Xcl` is `C^∞` everywhere -/

lemma contDiffOn_Xcl (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Xcl n h s) Set.univ := by
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => Work.OddVolterra.Xi n h s +
        ∫ σ in wHi..(1 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ
          (Work.OddVolterra.baseState σ))
      (Set.Ioo (1 / 8 : ℝ) (99 / 100)) :=
    source_contDiffOn n hn h hh hsupp hsmall
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => wChiX s) := wCs_contDiff
  have hts : tsupport (wCs : ℝ → ℝ) = Metric.closedBall (3 / 5 : ℝ) wCs.rOut :=
    ContDiffBump.tsupport_eq wCs
  have hsub : tsupport (wCs : ℝ → ℝ) ⊆ Set.Ioo (1 / 8 : ℝ) (99 / 100) := by
    intro s hs
    rw [hts, Metric.mem_closedBall, Real.dist_eq, wCs_rOut, abs_le] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hprod : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => wChiX s •
        (Work.OddVolterra.Xi n h s +
          ∫ σ in wHi..(1 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ
            (Work.OddVolterra.baseState σ))) Set.univ := by
    refine contDiffOn_of_locally_contDiffOn (fun s _ => ?_)
    by_cases hs : s ∈ tsupport (wCs : ℝ → ℝ)
    · exact ⟨Set.Ioo (1 / 8 : ℝ) (99 / 100), isOpen_Ioo, hsub hs,
        (hC.contDiffOn.smul hF).mono Set.inter_subset_right⟩
    · refine ⟨(tsupport (wCs : ℝ → ℝ))ᶜ, (isClosed_tsupport _).isOpen_compl, hs, ?_⟩
      refine (contDiffOn_const (c := (0 : Work.OddVolterra.St))).congr (fun x hx => ?_)
      have hx0 : wChiX x = 0 := by
        by_contra hcon
        exact hx.2 (subset_tsupport _ (Function.mem_support.mpr hcon))
      rw [hx0, zero_smul]
  have hfun : (fun s : ℝ => Xcl n h s) = fun s : ℝ => wChiX s •
      (Work.OddVolterra.Xi n h s +
        ∫ σ in wHi..(1 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ
          (Work.OddVolterra.baseState σ)) := by
    funext s
    rw [Xcl]
  rw [hfun]
  exact hprod


/-! ## Endpoint bounds and the interval integrability of the manifest kernel -/

/-- Inside the state ball of radius `1/2` around `baseState σ`, for `σ ∈ [1/4, 1]`, the two chord
endpoints `z 0 = x`, `z 1 = y` are at distance `> 1/5` from the axis. -/
lemma one_fifth_lt_abs_coord {σ : ℝ} (h1 : (1 : ℝ) / 4 ≤ σ) (h2 : σ ≤ 1)
    {z : Work.OddVolterra.St} (hz : ‖z - Work.OddVolterra.baseState σ‖ ≤ 1 / 2) :
    ∀ i : Fin 4, i = 0 ∨ i = 1 → 1 / 5 < |z i| := by
  have hpx : (1 : ℝ) / √2 ≤ Commons.Geometry.Ulam.profileX σ :=
    Work.OddVolterra.Existence.profileX_lower_c (by rw [abs_le]; constructor <;> linarith)
  have hgt := Work.OddVolterra.Existence.one_div_sqrt_two_sub_half_gt_one_fifth_c
  intro i hi
  have hb : Work.OddVolterra.baseState σ i = Commons.Geometry.Ulam.profileX σ := by
    rcases hi with rfl | rfl <;> rfl
  have h4 : |z i - Commons.Geometry.Ulam.profileX σ| ≤ 1 / 2 := by
    have h := norm_le_pi_norm (z - Work.OddVolterra.baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs, hb] at h
    exact le_trans h hz
  have h9 : (1 : ℝ) / 5 < z i := by
    have h10 := (abs_le.mp h4).1
    linarith
  rw [abs_of_pos (by linarith)]
  exact h9

/-- **Interval integrability of the manifest kernel along a state curve.**  If the slopes `s`, `σ`
lie in `(1/8, 99/100)`, `(1/8, 21/20)` and the chord endpoints of the state have modulus `> 1/5`,
the Abel radicand is positive, so `ΘM` is `C^∞` there; a continuous state curve therefore gives an
interval-integrable integrand. -/
lemma intervalIntegrable_thetaM_of_curve (n : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s a b : ℝ} (hs : 1 / 8 < s) (hs' : s < 99 / 100) (hab : a ≤ b)
    {c : ℝ → Work.OddVolterra.St} (hc : ContinuousOn c (Set.Icc a b))
    (hmem : ∀ σ ∈ Set.Icc a b, 1 / 8 < σ ∧ σ < 21 / 20 ∧
      1 / 5 < |c σ 0| ∧ 1 / 5 < |c σ 1|) :
    IntervalIntegrable (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (c σ))
      volume a b := by
  set U : Set (ℝ × (ℝ × Work.OddVolterra.St)) := {q | 1 / 8 < q.1 ∧ q.1 < 99 / 100 ∧
    1 / 8 < q.2.1 ∧ q.2.1 < 21 / 20 ∧ 1 / 5 < |q.2.2 0| ∧ 1 / 5 < |q.2.2 1|} with hUdef
  have hUopen : IsOpen U := by
    have hcont : Continuous (fun q : ℝ × (ℝ × Work.OddVolterra.St) =>
        (q.1, q.2.1, |q.2.2 0|, |q.2.2 1|)) := by fun_prop
    have hset : U = (fun q : ℝ × (ℝ × Work.OddVolterra.St) =>
        (q.1, q.2.1, |q.2.2 0|, |q.2.2 1|)) ⁻¹'
        (Set.Ioo (1 / 8) (99 / 100) ×ˢ (Set.Ioo (1 / 8) (21 / 20) ×ˢ
          (Set.Ioi (1 / 5 : ℝ) ×ˢ Set.Ioi (1 / 5 : ℝ)))) := by
      rw [hUdef]
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi]
      tauto
    rw [hset]
    exact (isOpen_Ioo.prod (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioi))).preimage hcont
  have hposU : ∀ q ∈ U, 0 < Work.OddVolterra.krad h q.2.1 (-(q.2.2 0)) q.1 ∧
      0 < Work.OddVolterra.krad h q.2.1 (q.2.2 1) q.1 := by
    intro q hq
    rw [hUdef] at hq
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp hsmall (a := q.1) (σ := q.2.1)
        (t := -(q.2.2 0)) (by linarith) (by rw [abs_neg]; exact le_of_lt h5),
      Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp hsmall (a := q.1) (σ := q.2.1)
        (t := q.2.2 1) (by linarith) (le_of_lt h6)⟩
  have hposτ : ∀ q ∈ U, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < Work.OddVolterra.krad h q.2.1 (-(q.2.2 0)) (q.1 + τ * (q.2.1 - q.1)) ∧
      0 < Work.OddVolterra.krad h q.2.1 (q.2.2 1) (q.1 + τ * (q.2.1 - q.1)) := by
    intro q hq τ hτ
    rw [hUdef] at hq
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    obtain ⟨hτ0, hτ1⟩ := hτ
    have ha1 : 1 / 8 < q.1 + τ * (q.2.1 - q.1) := by
      rcases le_total q.1 q.2.1 with hle | hle
      · have hnn : 0 ≤ τ * (q.2.1 - q.1) := mul_nonneg hτ0 (by linarith)
        linarith
      · have hge : τ * (q.2.1 - q.1) ≥ q.2.1 - q.1 := by
          have := mul_le_mul_of_nonpos_right hτ1 (by linarith : q.2.1 - q.1 ≤ 0)
          linarith
        linarith
    exact ⟨Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp hsmall
        (a := q.1 + τ * (q.2.1 - q.1)) (σ := q.2.1) (t := -(q.2.2 0))
        (by linarith) (by rw [abs_neg]; exact le_of_lt h5),
      Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp hsmall
        (a := q.1 + τ * (q.2.1 - q.1)) (σ := q.2.1) (t := q.2.2 1)
        (by linarith) (le_of_lt h6)⟩
  have hsm := Work.OddExistence.Manifest.contDiffOn_KernelExtThetaM_of_pos n hh hUopen hposU hposτ
  have hcurve : ContinuousOn (fun σ : ℝ => (s, (σ, c σ))) (Set.Icc a b) :=
    continuousOn_const.prodMk (continuousOn_id.prodMk hc)
  have hmemU : ∀ σ ∈ Set.Icc a b, (s, (σ, c σ)) ∈ U := by
    intro σ hσ
    obtain ⟨h1, h2, h3, h4⟩ := hmem σ hσ
    exact ⟨hs, hs', h1, h2, h3, h4⟩
  have hcont : ContinuousOn (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (c σ))
      (Set.Icc a b) := hsm.continuousOn.comp hcurve hmemU
  have hcont' : ContinuousOn (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (c σ))
      (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  exact hcont'.intervalIntegrable


/-! ## The clamped equation -/

/-- On `(1/4, 19/20)` the clamped data `Gcl`, `Tcl`, `Xcl` solve the clamped Volterra system
`Gcl n h s (Z s) = ∫_σ in s..(19/20), Tcl n h s σ (Z σ) + Xcl n h s`.
Indeed the clamps are `1` on the region of use, `ΘM = Θ` off the diagonal, `Z σ = baseState σ` for
`σ ≥ 1 - τ`, and the frozen tail `∫_{19/20}^1 ΘM n h s σ (baseState σ)` is exactly the extra
summand of `Xcl`. -/
lemma clamped_eq_of_Ioo (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → Work.OddVolterra.St} (hZc : ContinuousOn Z (Set.Icc (1 / 4) (19 / 20)))
    (hZeq : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Z s) =
        (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
          Work.OddVolterra.Xi n h s)
    (hZtail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s)
    (hZd : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2) :
    ∀ s ∈ Set.Ioo (1 / 4 : ℝ) (19 / 20),
      Gcl n h s (Z s) = (∫ σ in s..(19 / 20 : ℝ), Tcl n h s σ (Z σ)) + Xcl n h s := by
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1 / 100 :=
    fun k hk t => hsmall k (by omega) t
  intro s hs
  have hsI : s ∈ Set.Icc wLo wHi := by
    show (1 : ℝ) / 4 ≤ s ∧ s ≤ 19 / 20
    exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hmemI : ∀ σ : ℝ, (1 / 4 : ℝ) ≤ σ → σ ≤ 19 / 20 → σ ∈ Set.Icc wLo wHi := by
    intro σ h1 h2
    show (1 : ℝ) / 4 ≤ σ ∧ σ ≤ 19 / 20
    exact ⟨h1, h2⟩
  have hab1 : s ≤ 19 / 20 := le_of_lt hs.2
  have hs1 : s < 1 := by linarith [hs.2]
  -- the state stays in the ball on the whole of `[1/4, 1]`
  have hZb : ∀ σ ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ 1 / 2 := by
    intro σ hσ
    by_cases h : σ ≤ 19 / 20
    · have h1 := hZd σ ⟨hσ.1, h⟩
      rwa [dist_eq_norm] at h1
    · have h2 : Z σ = Work.OddVolterra.baseState σ :=
        hZtail σ (by rw [Work.OddVolterra.tau]; linarith)
      rw [h2]; simp
  have hZs : ‖Z s - Work.OddVolterra.baseState s‖ ≤ 1 / 2 := by
    have h1 := hZd s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    rwa [dist_eq_norm] at h1
  -- `Gcl = Godd` at the state
  have hGcl : Gcl n h s (Z s) = Work.OddVolterra.Godd n h s (Z s) :=
    Gcl_eq_Godd hsI (by show ‖Z s - Work.OddVolterra.baseState s‖ ≤ wRho; exact hZs)
  -- `Θ = ΘM` off the diagonal, on `(s, 1)`
  have hTheta : ∀ σ ∈ Set.Ioo s 1,
      Work.OddVolterra.Theta n h s σ (Z σ) = Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ) := by
    intro σ hσ
    have hσI : σ ∈ Set.Ioo (1 / 4 : ℝ) 1 := ⟨lt_trans hs.1 hσ.1, hσ.2⟩
    have hb := hZb σ ⟨le_of_lt hσI.1, le_of_lt hσI.2⟩
    have hz0 := one_fifth_lt_abs_coord (le_of_lt hσI.1) (le_of_lt hσI.2) hb 0 (Or.inl rfl)
    have hz1 := one_fifth_lt_abs_coord (le_of_lt hσI.1) (le_of_lt hσI.2) hb 1 (Or.inr rfl)
    rw [← Work.OddVolterra.Window.ThetaM_eq_Theta n hn hh hσ.1 (δ := s - 1 / 4)
      (by linarith [hs.1]) (Z σ)]
    · intro a ha
      exact Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp hsmall1 (a := a) (σ := σ)
        (t := -(Z σ 0)) (by linarith [ha.1, hs.1, hσ.1]) (by rw [abs_neg]; exact le_of_lt hz0)
    · intro a ha
      exact Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp hsmall1 (a := a) (σ := σ)
        (t := Z σ 1) (by linarith [ha.1, hs.1, hσ.1]) (le_of_lt hz1)
  have hman : (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) =
      ∫ σ in s..(1 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ) :=
    intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs1) hTheta
  -- interval integrability of the manifest integrand
  have hI1 : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume s (19 / 20) :=
    intervalIntegrable_thetaM_of_curve n hh hsupp hsmall1 (hs := by linarith [hs.1])
      (hs' := by linarith [hs.2]) hab1
      (hZc.mono (fun σ hσ => ⟨le_trans (le_of_lt hs.1) hσ.1, le_trans hσ.2 (by norm_num)⟩))
      (fun σ hσ => by
        have hσ4 : (1 / 4 : ℝ) ≤ σ := le_trans (le_of_lt hs.1) hσ.1
        have hσ1 : σ ≤ 1 := by linarith [hσ.2]
        have hb := hZb σ ⟨hσ4, hσ1⟩
        exact ⟨by linarith, by linarith,
          one_fifth_lt_abs_coord hσ4 hσ1 hb 0 (Or.inl rfl),
          one_fifth_lt_abs_coord hσ4 hσ1 hb 1 (Or.inr rfl)⟩)
  have hI2b : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ
        (Work.OddVolterra.baseState σ)) volume (19 / 20) 1 :=
    intervalIntegrable_thetaM_of_curve n hh hsupp hsmall1 (hs := by linarith [hs.1])
      (hs' := by linarith [hs.2]) (by norm_num)
      (Work.Anchor.contDiff_baseState_eng.continuous.continuousOn)
      (fun σ hσ => by
        have hσ4 : (1 / 4 : ℝ) ≤ σ := by linarith [hσ.1]
        have hσ1 : σ ≤ 1 := hσ.2
        have hb0 : Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
        have hb1 : Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
        have hpx : (1 : ℝ) / √2 ≤ Commons.Geometry.Ulam.profileX σ :=
          Work.OddVolterra.Existence.profileX_lower_c (by rw [abs_le]; constructor <;> linarith)
        have hgt := Work.OddVolterra.Existence.one_div_sqrt_two_sub_half_gt_one_fifth_c
        refine ⟨by linarith, by linarith, ?_, ?_⟩
        · rw [hb0, abs_of_nonneg (by linarith)]; linarith
        · rw [hb1, abs_of_nonneg (by linarith)]; linarith)
  have hI2 : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume (19 / 20) 1 :=
    hI2b.congr_uIoo (fun σ hσ => by
      rw [Set.uIoo_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] at hσ
      have h2 : Z σ = Work.OddVolterra.baseState σ :=
        hZtail σ (by rw [Work.OddVolterra.tau]; linarith [hσ.1])
      rw [h2])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  -- the middle piece is the clamped kernel
  have hTcl : ∀ σ ∈ Set.Ioo s (19 / 20),
      Tcl n h s σ (Z σ) = Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ) := by
    intro σ hσ
    have hσ4 : (1 / 4 : ℝ) ≤ σ := by linarith [hσ.1, hs.1]
    have hσ1 : σ ≤ 1 := by linarith [hσ.2]
    exact Tcl_eq_ThetaM hsI (hmemI σ hσ4 (le_of_lt hσ.2))
      (by show ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ wRho; exact hZb σ ⟨hσ4, hσ1⟩)
  have hMid : (∫ σ in s..(19 / 20 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) =
      ∫ σ in s..(19 / 20 : ℝ), Tcl n h s σ (Z σ) :=
    intervalIntegral.integral_congr_Ioo_of_le hab1 (fun σ hσ => (hTcl σ hσ).symm)
  have hTail : (∫ σ in (19 / 20 : ℝ)..1, Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) =
      ∫ σ in (19 / 20 : ℝ)..1,
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ) :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun σ hσ => by
      rw [hZtail σ (by rw [Work.OddVolterra.tau]; linarith [hσ.1])])
  have hXcl := Xcl_eq (n := n) (h := h) hsI
  have hgiven := hZeq s ⟨hs.1, hs1⟩
  rw [hGcl, hgiven, hman, ← hsplit, hMid, hTail, hXcl]
  simp only [wHi]
  abel

/-! ## The linearization of the clamped state datum is invertible -/

/-- If a smooth map `f` agrees with `g` on the closed ball `closedBall cen r`, `g` has a lower
modulus `c` there, and `x` lies in that ball, then `fderiv f x` has the same lower modulus `c`.
For interior points `y` of the ball this is the standard "difference quotient along a segment"
argument, using `f = g` on the segment through `x`; the boundary points follow by continuity of
`y ↦ fderiv f y`, since the modulus condition `c‖v‖ ≤ ‖fderiv f y v‖` defines a closed set. -/
lemma fderiv_injective_of_modulus_on_ball
    (f g : Work.OddVolterra.St → Work.OddVolterra.St)
    (cen x : Work.OddVolterra.St) (r c : ℝ)
    (hr : 0 < r) (hc : 0 < c)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfg : ∀ y ∈ Metric.closedBall cen r, f y = g y)
    (hmod : ∀ y ∈ Metric.closedBall cen r, ∀ z ∈ Metric.closedBall cen r,
      c * ‖y - z‖ ≤ ‖g y - g z‖)
    (hx : x ∈ Metric.closedBall cen r) :
    ∀ v, c * ‖v‖ ≤ ‖(fderiv ℝ f x) v‖ := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hinterior : ∀ y ∈ Metric.ball cen r, ∀ v, c * ‖v‖ ≤ ‖(fderiv ℝ f y) v‖ := by
    intro y hy v
    rcases eq_or_ne v 0 with hv | hv
    · subst hv; simp
    set L : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St := fderiv ℝ f y with hL
    have hδ : 0 < r - ‖y - cen‖ := by
      have := Metric.mem_ball.mp hy
      rw [dist_eq_norm] at this; linarith
    have hε : 0 < (r - ‖y - cen‖) / (1 + ‖v‖) := by positivity
    have hcurve : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y)
    have hd : HasDerivAt (fun t : ℝ => f (y + t • v)) (L v) 0 := by
      simpa [Function.comp_def, hL] using
        ((hdiff.differentiableAt.hasFDerivAt).comp_hasDerivAt 0 hcurve)
    have htend : Tendsto (fun t : ℝ => ‖t⁻¹ • (f (y + t • v) - f y)‖)
        (𝓝[>] (0 : ℝ)) (𝓝 ‖L v‖) := by
      have h2 : Tendsto (fun t : ℝ => t⁻¹ • (f (y + t • v) - f y))
          (𝓝[≠] (0 : ℝ)) (𝓝 (L v)) := by
        simpa using hd.tendsto_slope_zero
      have h3 : Tendsto (fun t : ℝ => t⁻¹ • (f (y + t • v) - f y))
          (𝓝[>] (0 : ℝ)) (𝓝 (L v)) :=
        h2.mono_left (nhdsWithin_mono 0 (by
          intro t ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt ht))
      simpa using h3.norm
    have hev : ∀ᶠ t in (𝓝[>] (0 : ℝ)),
        c * ‖v‖ ≤ ‖t⁻¹ • (f (y + t • v) - f y)‖ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht htp
      have htabs : |t| < (r - ‖y - cen‖) / (1 + ‖v‖) := by
        have := Metric.mem_ball.mp ht; rwa [Real.dist_eq, sub_zero] at this
      have htnorm : t * ‖v‖ < r - ‖y - cen‖ := by
        have h1 : t < (r - ‖y - cen‖) / (1 + ‖v‖) :=
          lt_of_le_of_lt (le_abs_self t) htabs
        have h2 : 0 < 1 + ‖v‖ := by positivity
        have h3 : t * ‖v‖ < (r - ‖y - cen‖) / (1 + ‖v‖) * ‖v‖ :=
          mul_lt_mul_of_pos_right h1 (norm_pos_iff.mpr hv)
        have h4 : (r - ‖y - cen‖) / (1 + ‖v‖) * ‖v‖ < r - ‖y - cen‖ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ h2]; linarith [norm_nonneg v]
        linarith
      have hy1 : y + t • v ∈ Metric.closedBall cen r := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : y + t • v - cen = (y - cen) + t • v := by abel
        rw [h1]
        calc ‖(y - cen) + t • v‖ ≤ ‖y - cen‖ + ‖t • v‖ := norm_add_le _ _
          _ = ‖y - cen‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos htp]
          _ ≤ r := by linarith
      have hy0 : y ∈ Metric.closedBall cen r := Metric.ball_subset_closedBall hy
      have hmod' := hmod (y + t • v) hy1 y hy0
      rw [← hfg _ hy1, ← hfg _ hy0] at hmod'
      have hnorm : ‖y + t • v - y‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htp]
      rw [hnorm] at hmod'
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htp), inv_mul_eq_div,
        le_div_iff₀ htp]
      linarith
    exact ge_of_tendsto htend hev
  have hclosed : IsClosed {y : Work.OddVolterra.St | ∀ v, c * ‖v‖ ≤ ‖(fderiv ℝ f y) v‖} := by
    have heq : {y : Work.OddVolterra.St | ∀ v, c * ‖v‖ ≤ ‖(fderiv ℝ f y) v‖}
        = ⋂ v : Work.OddVolterra.St,
            {y : Work.OddVolterra.St | c * ‖v‖ ≤ ‖(fderiv ℝ f y) v‖} := by
      ext y; simp
    rw [heq]
    refine isClosed_iInter (fun v => ?_)
    have hcont : Continuous (fun y : Work.OddVolterra.St => ‖(fderiv ℝ f y) v‖) := by
      have h2 := hf.continuous_fderiv_apply (by simp)
      exact continuous_norm.comp (h2.comp (continuous_id.prodMk continuous_const))
    exact isClosed_le continuous_const hcont
  have hcl : x ∈ closure {y : Work.OddVolterra.St | ∀ v, c * ‖v‖ ≤ ‖(fderiv ℝ f y) v‖} :=
    closure_mono (fun y hy => hinterior y hy)
      (by rw [closure_ball cen (ne_of_gt hr)]; exact hx)
  rw [hclosed.closure_eq] at hcl
  exact hcl

/-- **The linearization of the clamped state datum at the state is invertible.**  `Gcl` agrees with
`Godd` on the state ball of radius `1/2`, where `Godd` has the lower modulus of
`Existence.godd_injective_modulus_state_ball_compat`; hence `fderiv (Gcl n h s ·) (Z s)` is
injective, and therefore a continuous linear equivalence (`St` is finite dimensional). -/
lemma fderiv_Gcl_isEquiv (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (hGcl_cont : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Work.OddVolterra.St => Gcl n h p.1 p.2) Set.univ)
    {Z : ℝ → Work.OddVolterra.St}
    (hZd : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) :
    ∃ e : Work.OddVolterra.St ≃L[ℝ] Work.OddVolterra.St,
      fderiv ℝ (fun z => Gcl n h s z) (Z s) = e.toContinuousLinearMap := by
  obtain ⟨c, hc, hmod⟩ :=
    Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat n hn hh hsupp
      (fun k hk => hsmall k (by omega)) (b := 1 / 4) (by norm_num) (by norm_num)
  have hs1 : s ∈ Set.Icc (1 / 4 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun z : Work.OddVolterra.St => Gcl n h s z) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Work.OddVolterra.St => (s, z)) :=
      contDiff_const.prodMk contDiff_id
    have h2 := (contDiffOn_univ.mp hGcl_cont).comp h1
    simpa [Function.comp_def] using h2
  have hfg : ∀ y ∈ Metric.closedBall (Work.OddVolterra.baseState s) (1 / 2),
      (fun z : Work.OddVolterra.St => Gcl n h s z) y =
        (fun z : Work.OddVolterra.St => Work.OddVolterra.Godd n h s z) y := by
    intro y hy
    have hy' : ‖y - Work.OddVolterra.baseState s‖ ≤ 1 / 2 := by
      rwa [Metric.mem_closedBall, dist_eq_norm] at hy
    exact Gcl_eq_Godd hs (by show ‖y - Work.OddVolterra.baseState s‖ ≤ wRho; exact hy')
  have hmod' : ∀ y ∈ Metric.closedBall (Work.OddVolterra.baseState s) (1 / 2),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) (1 / 2),
      c * ‖y - z‖ ≤ ‖(fun z : Work.OddVolterra.St => Work.OddVolterra.Godd n h s z) y -
        (fun z : Work.OddVolterra.St => Work.OddVolterra.Godd n h s z) z‖ :=
    fun y hy z hz => hmod s hs1 y hy z hz
  have hx : Z s ∈ Metric.closedBall (Work.OddVolterra.baseState s) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hZd s hs
  have hkey := fderiv_injective_of_modulus_on_ball
    (fun z : Work.OddVolterra.St => Gcl n h s z)
    (fun z : Work.OddVolterra.St => Work.OddVolterra.Godd n h s z)
    (Work.OddVolterra.baseState s) (Z s) (1 / 2) c (by norm_num) hc hf hfg hmod' hx
  have hinj : Function.Injective
      (fderiv ℝ (fun z : Work.OddVolterra.St => Gcl n h s z) (Z s)) := by
    intro u v huv
    have h1 : (fderiv ℝ (fun z : Work.OddVolterra.St => Gcl n h s z) (Z s)) (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    have h2 := hkey (u - v)
    rw [h1, norm_zero] at h2
    have h3 : ‖u - v‖ = 0 := by
      have h4 : ‖u - v‖ ≤ 0 := by nlinarith [h2, hc, norm_nonneg (u - v)]
      exact le_antisymm h4 (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hsurj : Function.Surjective
      (fderiv ℝ (fun z : Work.OddVolterra.St => Gcl n h s z) (Z s)) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective
    (fderiv ℝ (fun z : Work.OddVolterra.St => Gcl n h s z) (Z s))
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj), rfl⟩

/-! ## The clamped equation on the closed window -/

/-- The clamped equation extends from `(1/4, 19/20)` to `[1/4, 19/20]`: both sides are continuous
on the closed interval (the left one because `Gcl` is smooth and `Z` continuous, the right one
because of the parametric-integral smoothing `volterraFixedPoint_contDiffOn_volterra_integral`),
and `(1/4, 19/20)` is dense. -/
lemma clamped_eq_of_Icl (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → Work.OddVolterra.St} (hZc : ContinuousOn Z (Set.Icc (1 / 4) (19 / 20)))
    (hZeq : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Z s) =
        (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
          Work.OddVolterra.Xi n h s)
    (hZtail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s)
    (hZd : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2)
    (hGcl_cont : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Work.OddVolterra.St => Gcl n h p.1 p.2) Set.univ)
    (hTcl_cont : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × Work.OddVolterra.St) => Tcl n h q.1 q.2.1 q.2.2) Set.univ)
    (hXcl_cont : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Xcl n h s) Set.univ) :
    ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      Gcl n h s (Z s) = (∫ σ in s..(19 / 20 : ℝ), Tcl n h s σ (Z σ)) + Xcl n h s := by
  have hIoo := clamped_eq_of_Ioo n hn hh hsupp hsmall hZc hZeq hZtail hZd
  have hcont1 : ContinuousOn (fun s : ℝ => Gcl n h s (Z s)) (Set.Icc (1 / 4) (19 / 20)) :=
    hGcl_cont.continuousOn.comp (continuousOn_id.prodMk hZc) (fun x _ => Set.mem_univ _)
  have hInt : ContDiffOn ℝ 1
      (fun s : ℝ => ∫ σ in s..(19 / 20 : ℝ), Tcl n h s σ (Z σ)) (Set.Icc (1 / 4) (19 / 20)) :=
    Commons.Analysis.Calculus.volterraFixedPoint_contDiffOn_volterra_integral
      (E := Work.OddVolterra.St) (K := fun s σ z => Tcl n h s σ z) (z := Z)
      (a := 1 / 4) (b := 19 / 20) (n := 0) (by norm_num) hTcl_cont
      ((contDiffOn_zero (𝕜 := ℝ)).mpr hZc)
  have hcont2 : ContinuousOn
      (fun s : ℝ => (∫ σ in s..(19 / 20 : ℝ), Tcl n h s σ (Z σ)) + Xcl n h s)
      (Set.Icc (1 / 4) (19 / 20)) :=
    hInt.continuousOn.add (hXcl_cont.continuousOn.mono (fun x _ => Set.mem_univ x))
  intro x hx
  have hdense : x ∈ closure (Set.Ioo (1 / 4 : ℝ) (19 / 20)) := by
    rw [closure_Ioo (by norm_num : (1 / 4 : ℝ) ≠ 19 / 20)]
    exact hx
  have hne : (𝓝[Set.Ioo (1 / 4 : ℝ) (19 / 20)] x).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hdense
  have hsub : Set.Ioo (1 / 4 : ℝ) (19 / 20) ⊆ Set.Icc (1 / 4 : ℝ) (19 / 20) :=
    fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have h1 : Tendsto (fun s : ℝ => Gcl n h s (Z s))
      (𝓝[Set.Ioo (1 / 4 : ℝ) (19 / 20)] x) (𝓝 (Gcl n h x (Z x))) :=
    (hcont1 x hx).mono_left (nhdsWithin_mono x hsub)
  have h2 : Tendsto (fun s : ℝ => (∫ σ in s..(19 / 20 : ℝ), Tcl n h s σ (Z σ)) + Xcl n h s)
      (𝓝[Set.Ioo (1 / 4 : ℝ) (19 / 20)] x)
      (𝓝 ((∫ σ in x..(19 / 20 : ℝ), Tcl n h x σ (Z σ)) + Xcl n h x)) :=
    (hcont2 x hx).mono_left (nhdsWithin_mono x hsub)
  have hev : (fun s : ℝ => Gcl n h s (Z s)) =ᶠ[𝓝[Set.Ioo (1 / 4 : ℝ) (19 / 20)] x]
      (fun s : ℝ => (∫ σ in s..(19 / 20 : ℝ), Tcl n h s σ (Z σ)) + Xcl n h s) :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun s hs => hIoo s hs)
  have := tendsto_nhds_unique (h1.congr' hev) h2
  exact this

theorem smooth_upgrade (n : ℕ) (hn : 1 ≤ n) :
    ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
        s < 1 - 2 * Work.OddVolterra.tau + η₀ → h s = 0) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ Z : ℝ → Work.OddVolterra.St,
        ContinuousOn Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) →
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) →
        (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s) →
        (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2) →
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) := by
  intro h hh hsupp _hflat hsmall Z hZc hZeq hZtail hZd
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (by omega) s
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (by omega) s
  have hGcl_cont := gcl_contDiffOn n hh hsupp hsmall2
  have hTcl_cont := tcl_contDiffOn n hh hsupp hsmall2
  have hXcl_cont := contDiffOn_Xcl n hn hh hsupp hsmall1
  have hZeq' := clamped_eq_of_Icl n hn hh hsupp hsmall hZc hZeq hZtail hZd
    hGcl_cont hTcl_cont hXcl_cont
  exact Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint
    (E := Work.OddVolterra.St) (a := 1 / 4) (b := 19 / 20) (by norm_num)
    (G := fun s z => Gcl n h s z) (Θ := fun s σ z => Tcl n h s σ z)
    (Ξ := fun s => Xcl n h s) (Z := Z) hZc hZeq' hGcl_cont hTcl_cont hXcl_cont
    (fun s hs => fderiv_Gcl_isEquiv n hn hh hsupp hsmall hGcl_cont hZd hs)

end

end Work.OddVolterra.WinData
