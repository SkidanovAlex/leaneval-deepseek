import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.WinData.Specs
import Submission.Work.OddVolterra.WinData.LowClamp
import Submission.Work.OddVolterra.WinData.manifest_locality_low
import Submission.Work.OddVolterra.WinData.frozen_tail_close_low
import Submission.Work.OddVolterra.WinData.source_contDiffOn
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.WinData.win_lines
import Submission.Work.OddCurveB.Est.exists_linearization
import Submission.Work.OddCurveB.Engine.volterra_long_exists_ball

/-!
# Auxiliary definitions for the low-slope piece `lc_low_piece`

This file collects the objects used by `Work.OddVolterra.WinData.lc_low_piece`: the source of the
low-slope Volterra system with the glue point `7/10`, its continuous extension to the whole line
(via the clamp `lcClamp`), and the conversion lemmas that identify the clamped data `lcGodd`,
`lcTheta` of `WinData/LowClamp` with the paper's data `Godd n h`, `Theta n h` on the low window.
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-- The glue point of the low piece: the left end of the middle piece of the window. -/
def lcGlue : ℝ := 7 / 10

/-- The source of the low-slope system: the paper's `Ξ n h` plus the `σ`-integral of the kernel
from the glue point `7/10` to `1`, evaluated on the middle piece `Z`. -/
def lcSrc (n : ℕ) (h : ℝ → ℝ) (Z : ℝ → St) (s : ℝ) : St :=
  Xi n h s + ∫ σ in (7 / 10 : ℝ)..(1 : ℝ), Theta n h s σ (Z σ)

/-- The unperturbed source of the low-slope system. -/
def lcSrc0 (n : ℕ) (s : ℝ) : St :=
  Xi n 0 s + ∫ σ in (7 / 10 : ℝ)..(1 : ℝ), Theta n 0 s σ (baseState σ)

/-- The clamp onto the low window `[1/4, 7/10]`. -/
def lcClamp (s : ℝ) : ℝ := max (1 / 4) (min (7 / 10) s)

lemma lcGlue_eq : lcGlue = 7 / 10 := rfl

lemma lcClamp_continuous : Continuous lcClamp := by
  unfold lcClamp; fun_prop

lemma lcClamp_mem (s : ℝ) : lcClamp s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10) := by
  rw [lcClamp]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma lcClamp_eq_self {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) : lcClamp s = s := by
  rw [lcClamp, min_eq_right hs.2, max_eq_right hs.1]

/-- The continuous global extension of the low source: it is the identity on the low window. -/
def lcXiClamp (n : ℕ) (h : ℝ → ℝ) (Z : ℝ → St) (s : ℝ) : St := lcSrc n h Z (lcClamp s)

/-- The continuous global extension of the unperturbed low source. -/
def lcXi0Clamp (n : ℕ) (s : ℝ) : St := lcSrc0 n (lcClamp s)

lemma continuous_lcXiClamp {n : ℕ} {h : ℝ → ℝ} {Z : ℝ → St}
    (hc : ContinuousOn (lcSrc n h Z) (Set.Icc (1 / 4 : ℝ) (7 / 10))) :
    Continuous (lcXiClamp n h Z) :=
  hc.comp_continuous lcClamp_continuous (fun s => lcClamp_mem s)

lemma continuous_lcXi0Clamp {n : ℕ}
    (hc : ContinuousOn (lcSrc0 n) (Set.Icc (1 / 4 : ℝ) (7 / 10))) :
    Continuous (lcXi0Clamp n) :=
  hc.comp_continuous lcClamp_continuous (fun s => lcClamp_mem s)

lemma lcXiClamp_eq {n : ℕ} {h : ℝ → ℝ} {Z : ℝ → St} {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) : lcXiClamp n h Z s = lcSrc n h Z s := by
  rw [lcXiClamp, lcClamp_eq_self hs]

lemma lcXi0Clamp_eq {n : ℕ} {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) :
    lcXi0Clamp n s = lcSrc0 n s := by
  rw [lcXi0Clamp, lcClamp_eq_self hs]

/-! ## Facts about the zero perturbation -/

lemma small_zero_two : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ,
    |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
  intro k hk s
  have h0 : iteratedDeriv k (0 : ℝ → ℝ) s = 0 := by
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split <;> simp
  rw [h0, abs_zero]; norm_num

/-- Membership in the low window implies membership in the low slope interval `[1/4, 4/5]`. -/
lemma mem_lcAB_of_mem_low {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) :
    s ∈ Set.Icc lcA lcB := by
  rw [show lcA = (1 / 4 : ℝ) from rfl, show lcB = (4 / 5 : ℝ) from rfl]
  exact ⟨hs.1, by linarith [hs.2]⟩

/-- The cut-off in the state is `1` when the state is within `1/100` of the base state. -/
lemma cz2_wsq_eq_one {s : ℝ} {z : St} (hz : ‖z - baseState s‖ ≤ 1 / 100) :
    (Window.cz2 : ℝ → ℝ) (Window.wsq s z) = 1 := by
  have hz1 : Window.wsq s z ≤ 1 / 100 := by
    refine le_trans (Window.wsq_le_four_mul_sq_norm s z) ?_
    nlinarith [norm_nonneg (z - baseState s), hz]
  exact Window.cz2_eq_one_of_le hz1 (Window.wsq_nonneg s z)

/-- On the low window, with the state within `1/100` of the base state, the clamped state datum
is the paper's state datum for the perturbation `h` (which vanishes below `4/5`). -/
lemma lcGodd_eq_Godd_of_supp {n : ℕ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 100) :
    lcGodd n s z = Godd n h s z := by
  have hS : lcS s = 1 := lcS_eq_one_of_mem (mem_lcAB_of_mem_low hs)
  have hC : (Window.cz2 : ℝ → ℝ) (Window.wsq s z) = 1 := cz2_wsq_eq_one hz
  have h1 : lcGodd n s z = KernelExt.GoddM n 0 s z := by
    simp only [lcGodd, lcChiG, hS, hC, mul_one, one_smul]
  have hG0 : Godd n h s z = Godd n 0 s z :=
    Godd_eq_of_lt n (fun x hx => h_eq_zero_of_lt_window hsupp hx) (by linarith [hs.2]) z
  calc lcGodd n s z = KernelExt.GoddM n 0 s z := h1
    _ = Godd n 0 s z := Window.GoddM_eq_Godd n contDiff_const s z
    _ = Godd n h s z := hG0.symm

/-- The two chord endpoints of a state within `1/100` of `baseState σ`, for `σ ∈ [1/4, 7/10]`,
have modulus `≥ 1/5`. -/
lemma abs_coord_ge_fifth {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) {z : St}
    (hz : ‖z - baseState σ‖ ≤ 1 / 100) : (1 / 5 : ℝ) ≤ |z 0| ∧ (1 / 5 : ℝ) ≤ |z 1| := by
  have hbase : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX σ :=
    seven_tenths_le_profileX (by linarith [hσ.1]) (by linarith [hσ.2])
  have hcoord : ∀ i : Fin 4, |z i - baseState σ i| ≤ 1 / 100 := by
    intro i
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hz
  constructor
  · have hb : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
    have h := hcoord 0
    rw [hb] at h
    have hle := (abs_le.mp h).1
    have hpos : (0 : ℝ) < z 0 := by linarith
    rw [abs_of_pos hpos]; linarith
  · have hb : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
    have h := hcoord 1
    rw [hb] at h
    have hle := (abs_le.mp h).1
    have hpos : (0 : ℝ) < z 1 := by linarith
    rw [abs_of_pos hpos]; linarith

/-- On the low window, with the state within `1/100` of the base state, the clamped kernel datum
is the paper's kernel datum for the perturbation `h`. -/
lemma lcTheta_eq_Theta_of_supp {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ))
    (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) (hsσ : s < σ) {z : St}
    (hz : ‖z - baseState σ‖ ≤ 1 / 100) :
    lcTheta n s σ z = Theta n h s σ z := by
  have hS : lcS s = 1 := lcS_eq_one_of_mem (mem_lcAB_of_mem_low hs)
  have hS' : lcS σ = 1 := lcS_eq_one_of_mem (mem_lcAB_of_mem_low hσ)
  have hC : (Window.cz2 : ℝ → ℝ) (Window.wsq σ z) = 1 := cz2_wsq_eq_one hz
  have h1 : lcTheta n s σ z = KernelExt.ThetaM n 0 s σ z := by
    simp only [lcTheta, lcChiT, hS, hS', hC, mul_one, one_smul]
  have hzlow : ∀ x : ℝ, x < 4 / 5 → h x = 0 := fun x hx => h_eq_zero_of_lt_window hsupp hx
  have h2 : KernelExt.ThetaM n 0 s σ z = KernelExt.ThetaM n h s σ z :=
    (ThetaM_eq_of_lt n hzlow (by linarith [hs.2]) (by linarith [hσ.2]) z).symm
  obtain ⟨hz0, hz1⟩ := abs_coord_ge_fifth hσ hz
  have hpos1 : ∀ a ∈ Set.Icc (s - 1 / 8) σ, 0 < krad h σ (-(z 0)) a := by
    intro a ha
    refine krad_pos_of_add_pos' hsupp hsmall ?_ ?_
    · linarith [hs.1, ha.1]
    · rw [abs_neg]; exact hz0
  have hpos2 : ∀ a ∈ Set.Icc (s - 1 / 8) σ, 0 < krad h σ (z 1) a := by
    intro a ha
    exact krad_pos_of_add_pos' hsupp hsmall (by linarith [hs.1, ha.1]) hz1
  have h3 : KernelExt.ThetaM n h s σ z = Theta n h s σ z :=
    Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn hh hsσ (by norm_num) z hpos1 hpos2
  rw [h1, h2, h3]

/-- The clamped state datum agrees with `Godd n 0` on the ball of radius `1/20`. -/
lemma lcGodd_eq_Godd_zero_of_close {n : ℕ} {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 20) : lcGodd n s z = Godd n 0 s z := by
  have hS : lcS s = 1 := lcS_eq_one_of_mem (mem_lcAB_of_mem_low hs)
  have hC : (Window.cz2 : ℝ → ℝ) (Window.wsq s z) = 1 := by
    refine Window.cz2_eq_one_of_le ?_ (Window.wsq_nonneg s z)
    calc Window.wsq s z ≤ 4 * ‖z - baseState s‖ ^ 2 := Window.wsq_le_four_mul_sq_norm s z
      _ ≤ 4 * (1 / 20 : ℝ) ^ 2 := by
          have h0 : (0:ℝ) ≤ ‖z - baseState s‖ := norm_nonneg _
          nlinarith
      _ ≤ 1 / 100 := by norm_num
  have h1 : lcGodd n s z = KernelExt.GoddM n 0 s z := by
    rw [lcGodd, lcChiG, hS, hC, mul_one, one_smul]
  rw [h1]
  exact Window.GoddM_eq_Godd (h := (0 : ℝ → ℝ)) n contDiff_const s z

/-- `lcGodd n s` is eventually equal to `Godd n 0 s` at every point of the ball of radius
`1/100` around the base state. -/
lemma lcGodd_eventuallyEq_Godd_zero {n : ℕ} {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) :
    lcGodd n s =ᶠ[𝓝 (baseState s)] Godd n 0 s := by
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ) < 1/100)) ?_
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  exact lcGodd_eq_Godd_zero_of_close hs (le_trans (le_of_lt hz) (by norm_num))

/-- `lcGodd n s` is eventually equal to `Godd n 0 s` at every point within `1/100` of the base
state. -/
lemma lcGodd_eventuallyEq_Godd_zero_at {n : ℕ} {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 100) : lcGodd n s =ᶠ[𝓝 z] Godd n 0 s := by
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1/100)) ?_
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : ‖w - baseState s‖ ≤ 1 / 20 := by
    calc ‖w - baseState s‖ ≤ ‖w - z‖ + ‖z - baseState s‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle w z (baseState s)
      _ ≤ 1 / 100 + 1 / 100 := add_le_add hw.le hz
      _ ≤ 1 / 20 := by norm_num
  exact lcGodd_eq_Godd_zero_of_close hs h1

/-- **The linearization closeness of the engine.**  On the ball of radius `1/100` around the base
state the linearization of the clamped datum `lcGodd n` is `O(‖z - baseState s‖) + O(δ)` close to
the unperturbed linearization at `baseState s`. -/
theorem lc_low_hder (n : ℕ) (hn : 1 ≤ n)
    (hL4 : FderivGoddCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ)) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ (h : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h →
        Function.support h ⊆
          Set.Icc (1 - 2 * tau) (1 - tau) →
        ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 100 →
        (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
        ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
        ∀ z ∈ Metric.closedBall (baseState s) (1 / 100),
          ‖fderiv ℝ (fun w => lcGodd n s w) z -
            fderiv ℝ (fun w => Godd n 0 s w) (baseState s)‖
          ≤ Cg * ‖z - baseState s‖ + Cg * δ := by
  obtain ⟨C₄, hC₄0, hC₄⟩ := hL4
  refine ⟨C₄, hC₄0.le, ?_⟩
  intro h hh hsupp δ hδ hδ100 hsmall s hs z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hz5 : ‖z - baseState s‖ ≤ 1 / 2 := by linarith
  have hzlow : ∀ x : ℝ, x < 4 / 5 → h x = 0 := fun x hx => h_eq_zero_of_lt_window hsupp hx
  have hs45 : s < 4 / 5 := by linarith [hs.2]
  have hz100 : ‖z - baseState s‖ ≤ 1 / 100 := by
    rw [← dist_eq_norm]; exact hz
  have hgerm1 : fderiv ℝ (fun w => lcGodd n s w) z = fderiv ℝ (fun w => Godd n 0 s w) z :=
    (lcGodd_eventuallyEq_Godd_zero_at (n := n) hs hz100).fderiv_eq
  have hev2 : (fun w => Godd n 0 s w) =ᶠ[𝓝 z] (fun w => Godd n h s w) :=
    Filter.Eventually.of_forall (fun w => (Godd_eq_of_lt n hzlow hs45 w).symm)
  have hgerm2 : fderiv ℝ (fun w => Godd n 0 s w) z = fderiv ℝ (fun w => Godd n h s w) z :=
    hev2.fderiv_eq
  rw [hgerm1, hgerm2]
  exact hC₄ h hh hsupp δ hδ hδ100 hsmall s ⟨hs.1, by linarith [hs.2]⟩ z
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz5)

/-- The clamped state datum is eventually equal to `Godd n h` at every point of the low window. -/
lemma lcGodd_eventuallyEq_Godd {n : ℕ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) :
    lcGodd n s =ᶠ[𝓝 (baseState s)] Godd n h s := by
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ) < 1/100)) ?_
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  exact lcGodd_eq_Godd_of_supp hsupp hs (le_of_lt hz)

/-! ## The low region of the manifest kernel -/

/-- The open region of `(s,σ,z)`-space on which the manifest kernel is smooth along the low
piece of the window. -/
def lcRegion : Set (ℝ × ℝ × St) :=
  {q | 1 / 8 < q.1 ∧ q.1 < 99 / 100 ∧ 1 / 8 < q.2.1 ∧ q.2.1 < 102 / 100 ∧
    ‖q.2.2 - baseState q.2.1‖ < 9 / 20}

lemma isOpen_lcRegion : IsOpen lcRegion := by
  have heq : lcRegion = {q : ℝ × ℝ × St | 1 / 8 < q.1} ∩ {q | q.1 < 99 / 100} ∩
      {q | 1 / 8 < q.2.1} ∩ {q | q.2.1 < 102 / 100} ∩
      {q | ‖q.2.2 - baseState q.2.1‖ < 9 / 20} := by
    rw [lcRegion]
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [heq]
  refine IsOpen.inter (IsOpen.inter (IsOpen.inter (IsOpen.inter ?_ ?_) ?_) ?_) ?_
  · exact isOpen_lt continuous_const continuous_fst
  · exact isOpen_lt continuous_fst continuous_const
  · exact isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  · exact isOpen_lt (continuous_fst.comp continuous_snd) continuous_const
  · exact isOpen_lt (continuous_norm.comp ((continuous_snd.comp continuous_snd).sub
      (Work.Anchor.contDiff_baseState_eng.continuous.comp
        (continuous_fst.comp continuous_snd)))) continuous_const

/-- The chord endpoints of a state inside the region have modulus `≥ 1/5`. -/
lemma abs_coord_ge_fifth_of_region {σ : ℝ} {z : St} (hσ1 : 1 / 8 < σ)
    (hσ2 : σ < 102 / 100) (hz : ‖z - baseState σ‖ < 9 / 20) :
    (1 / 5 : ℝ) ≤ |z 0| ∧ (1 / 5 : ℝ) ≤ |z 1| := by
  have hσabs : |σ| ≤ 21 / 20 := by rw [abs_le]; constructor <;> linarith
  have hprof : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ := profileX_ge_17_25' hσabs
  have hcoord : ∀ i : Fin 4, |z i - baseState σ i| < 9 / 20 := by
    intro i
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact lt_of_le_of_lt h hz
  constructor
  · have h := hcoord 0
    have hb : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
    rw [hb] at h
    have h' := (abs_le.mp (le_of_lt h)).1
    have hpos : (0 : ℝ) < z 0 := by linarith
    rw [abs_of_pos hpos]; linarith
  · have h := hcoord 1
    have hb : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
    rw [hb] at h
    have h' := (abs_le.mp (le_of_lt h)).1
    have hpos : (0 : ℝ) < z 1 := by linarith
    rw [abs_of_pos hpos]; linarith

/-- The manifest kernel is `C^∞` on the low region. -/
theorem contDiffOn_lcRegion_ThetaM (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => KernelExt.ThetaM n h q.1 q.2.1 q.2.2) lcRegion := by
  refine Work.OddExistence.Manifest.contDiffOn_KernelExtThetaM_of_pos n hh isOpen_lcRegion ?_ ?_
  · intro q hq
    rw [lcRegion] at hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    obtain ⟨hz0, hz1⟩ := abs_coord_ge_fifth_of_region h3 h4 h5
    exact ⟨krad_pos_of_add_pos' hsupp hsmall1 (by linarith) (by rwa [abs_neg]),
      krad_pos_of_add_pos' hsupp hsmall1 (by linarith) hz1⟩
  · intro q hq τ hτ
    rw [lcRegion] at hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    obtain ⟨hz0, hz1⟩ := abs_coord_ge_fifth_of_region h3 h4 h5
    have h1' : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
    have hcomb : q.1 + τ * (q.2.1 - q.1) = (1 - τ) * q.1 + τ * q.2.1 := by ring
    have hlow : 1 / 8 < q.1 + τ * (q.2.1 - q.1) := by
      rw [hcomb]
      rcases eq_or_lt_of_le hτ.1 with hτ0 | hτpos
      · rw [← hτ0]; linarith [h1]
      · have hA : τ * (1 / 8) < τ * q.2.1 := mul_lt_mul_of_pos_left h3 hτpos
        have hB : (1 - τ) * (1 / 8) ≤ (1 - τ) * q.1 := mul_le_mul_of_nonneg_left h1.le h1'
        linarith
    have hhigh : q.1 + τ * (q.2.1 - q.1) < 102 / 100 := by
      rw [hcomb]
      rcases eq_or_lt_of_le hτ.2 with hτ1 | hτ1
      · rw [hτ1]; linarith [h4]
      · have hA : τ * q.2.1 ≤ τ * (102 / 100) := mul_le_mul_of_nonneg_left h4.le hτ.1
        have hB : (1 - τ) * q.1 < (1 - τ) * (102 / 100) :=
          mul_lt_mul_of_pos_left (lt_trans h2 (by norm_num)) (by linarith)
        nlinarith [hA, hB]
    exact ⟨krad_pos_of_add_pos' hsupp hsmall1 (by linarith) (by rwa [abs_neg]),
      krad_pos_of_add_pos' hsupp hsmall1 (by linarith) hz1⟩

/-- Positivity of the unperturbed Abel radicand along the segment of a low slope. -/
lemma krad_zero_pos_of_low {σ a t : ℝ} (hσ : 1 / 8 ≤ σ) (ha : 1 / 8 ≤ a)
    (ht : (1 / 5 : ℝ) ≤ |t|) : 0 < krad (0 : ℝ → ℝ) σ t a :=
  krad_pos_of_add_pos' supp_zero_subset small_zero (by linarith) ht

lemma abs_profileX_ge_fifth {σ : ℝ} (hσ : |σ| ≤ 21 / 20) :
    (1 / 5 : ℝ) ≤ |Commons.Geometry.Ulam.profileX σ| := by
  have h := profileX_ge_17_25' hσ
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Positivity of the unperturbed Abel radicand at the two chord endpoints of the base state. -/
lemma krad_zero_pos_base {σ a : ℝ} (hσ : (1 / 8 : ℝ) ≤ σ) (hσ2 : σ ≤ 1) (ha : 1 / 8 ≤ a) :
    0 < krad (0 : ℝ → ℝ) σ (-(baseState σ 0)) a ∧
      0 < krad (0 : ℝ → ℝ) σ (baseState σ 1) a := by
  have hσabs : |σ| ≤ 21 / 20 := by
    rw [abs_le]; constructor <;> linarith [hσ]
  have h5 := abs_profileX_ge_fifth hσabs
  exact ⟨krad_zero_pos_of_low hσ ha (by rw [abs_neg]; exact h5),
    krad_zero_pos_of_low hσ ha h5⟩

lemma abs_coord_ge_fifth_of_dist {σ : ℝ} (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) 1) {z : St}
    (hz : dist z (baseState σ) ≤ 1 / 4) : (1 / 5 : ℝ) ≤ |z 0| ∧ (1 / 5 : ℝ) ≤ |z 1| := by
  have hσabs : |σ| ≤ 21 / 20 := by
    rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
  have hprof : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ := profileX_ge_17_25' hσabs
  have hd : ‖z - baseState σ‖ ≤ 1 / 4 := by rwa [dist_eq_norm] at hz
  have hcoord : ∀ i : Fin 4, |z i - baseState σ i| ≤ 1 / 4 := by
    intro i
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hd
  constructor
  · have h := hcoord 0
    have hb : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
    rw [hb] at h
    have h' := (abs_le.mp h).1
    have hpos : (0 : ℝ) < z 0 := by linarith
    rw [abs_of_pos hpos]; linarith
  · have h := hcoord 1
    have hb : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
    rw [hb] at h
    have h' := (abs_le.mp h).1
    have hpos : (0 : ℝ) < z 1 := by linarith
    rw [abs_of_pos hpos]; linarith

/-! ## Continuity of the two kernel integrands -/

/-- The manifest kernel along the base state is continuous on a low slope interval. -/
lemma continuousOn_thetaM_base_of_small (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) :
    ContinuousOn (fun σ : ℝ => KernelExt.ThetaM n h s σ (baseState σ)) (Set.Icc s 1) := by
  have hcd := contDiffOn_lcRegion_ThetaM n hh hsupp hsmall1
  have hpsi : Continuous (fun σ : ℝ => (s, σ, baseState σ)) :=
    continuous_const.prodMk (continuous_id.prodMk Work.Anchor.contDiff_baseState_eng.continuous)
  have hmap : Set.MapsTo (fun σ : ℝ => (s, σ, baseState σ)) (Set.Icc s 1) lcRegion := by
    intro σ hσ
    have hσ' : s ≤ σ ∧ σ ≤ 1 := hσ
    rw [lcRegion]
    exact ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hσ'.1, hs.1],
      by linarith [hσ'.2], by rw [sub_self, norm_zero]; norm_num⟩
  exact hcd.continuousOn.comp hpsi.continuousOn hmap

/-- The manifest kernel along a continuous state `Z` is continuous on the glue window. -/
lemma continuousOn_thetaM_state_of_small (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) {Z : ℝ → St}
    (hZ : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1))
    (hZd : ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, dist (Z σ) (baseState σ) ≤ 1 / 4) :
    ContinuousOn (fun σ : ℝ => KernelExt.ThetaM n h s σ (Z σ)) (Set.Icc (7 / 10 : ℝ) 1) := by
  have hcd := contDiffOn_lcRegion_ThetaM n hh hsupp hsmall1
  have hpsi : ContinuousOn (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc (7 / 10 : ℝ) 1) :=
    continuousOn_const.prodMk (continuousOn_id.prodMk hZ)
  have hmap : Set.MapsTo (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc (7 / 10 : ℝ) 1) lcRegion := by
    intro σ hσ
    have hσ' : (7 / 10 : ℝ) ≤ σ ∧ σ ≤ 1 := hσ
    have hd := hZd σ hσ
    rw [dist_eq_norm] at hd
    rw [lcRegion]
    exact ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hσ'.1], by linarith [hσ'.2],
      lt_of_le_of_lt hd (by norm_num)⟩
  exact hcd.continuousOn.comp hpsi hmap

/-- The clamp onto the `σ`-window `[7/10, 1]`. -/
def lcClampT (σ : ℝ) : ℝ := max (7 / 10) (min 1 σ)

lemma lcClampT_continuous : Continuous lcClampT := by unfold lcClampT; fun_prop

lemma lcClampT_mem (σ : ℝ) : lcClampT σ ∈ Set.Icc (7 / 10 : ℝ) 1 := by
  rw [lcClampT]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma lcClampT_eq_self {σ : ℝ} (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) 1) : lcClampT σ = σ := by
  rw [lcClampT, min_eq_right hσ.2, max_eq_right hσ.1]


/-- Interval integrability of a function continuous on a closed interval. -/
lemma intervalIntegrable_of_continuousOn_Icc {f : ℝ → St} {a b : ℝ} (hab : a ≤ b)
    (h : ContinuousOn f (Set.Icc a b)) : IntervalIntegrable f volume a b := by
  rw [← Set.uIcc_of_le hab] at h
  exact h.intervalIntegrable

/-! ## Continuity of the source -/

theorem lcSrc_continuousOn (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → St} (hZ : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1))
    (hZd : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, dist (Z s) (baseState s) ≤ 1 / 4) :
    ContinuousOn (lcSrc n h Z) (Set.Icc (1 / 4 : ℝ) (7 / 10)) := by
  have hXi : ContinuousOn (fun s : ℝ => Xi n h s) (Set.Icc (1 / 4 : ℝ) (7 / 10)) :=
    (Xi_contDiffOn_window n hn hh hsupp hsmall1).continuousOn.mono
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hZc : Continuous (fun σ : ℝ => Z (lcClampT σ)) :=
    hZ.comp_continuous lcClampT_continuous lcClampT_mem
  have hpsi : Continuous (fun p : ℝ × ℝ =>
      KernelExt.ThetaM n h (lcClamp p.1) (lcClampT p.2) (Z (lcClampT p.2))) := by
    have h2 : Continuous (fun p : ℝ × ℝ => (lcClamp p.1, lcClampT p.2, Z (lcClampT p.2))) :=
      (lcClamp_continuous.comp continuous_fst).prodMk
        ((lcClampT_continuous.comp continuous_snd).prodMk (hZc.comp continuous_snd))
    refine (contDiffOn_lcRegion_ThetaM n hh hsupp hsmall1).continuousOn.comp_continuous h2 ?_
    intro p
    obtain ⟨hp1, hp2⟩ := lcClamp_mem p.1
    obtain ⟨hp3, hp4⟩ := lcClampT_mem p.2
    have hd := hZd _ (lcClampT_mem p.2)
    rw [dist_eq_norm] at hd
    rw [lcRegion]
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      lt_of_le_of_lt hd (by norm_num)⟩
  have hint_cont : Continuous (fun x : ℝ =>
      ∫ t in (7 / 10 : ℝ)..(1 : ℝ),
        KernelExt.ThetaM n h (lcClamp x) (lcClampT t) (Z (lcClampT t))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (7 / 10 : ℝ))
      (f := fun x t => KernelExt.ThetaM n h (lcClamp x) (lcClampT t) (Z (lcClampT t)))
      (s := fun _ : ℝ => 1) hpsi continuous_const
  have hint : ContinuousOn (fun x : ℝ => ∫ t in (7 / 10 : ℝ)..(1 : ℝ),
      KernelExt.ThetaM n h x t (Z t)) (Set.Icc (1 / 4 : ℝ) (7 / 10)) := by
    refine hint_cont.continuousOn.congr ?_
    intro x hx
    show (∫ t in (7 / 10 : ℝ)..(1 : ℝ),
      KernelExt.ThetaM n h x t (Z t)) = (∫ t in (7 / 10 : ℝ)..(1 : ℝ),
      KernelExt.ThetaM n h (lcClamp x) (lcClampT t) (Z (lcClampT t)))
    rw [lcClamp_eq_self hx]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (7 : ℝ) / 10 ≤ 1)] at ht
    rw [lcClampT_eq_self ht]
  have hmain : ContinuousOn (fun s : ℝ => Xi n h s + ∫ t in (7 / 10 : ℝ)..(1 : ℝ),
      KernelExt.ThetaM n h s t (Z t)) (Set.Icc (1 / 4 : ℝ) (7 / 10)) := hXi.add hint
  refine hmain.congr ?_
  intro s hs
  rw [lcSrc]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with σ hσ
  rw [Set.uIoc_of_le (by norm_num : (7 : ℝ) / 10 ≤ 1)] at hσ
  have hsσ : s < σ := by linarith [hs.2, hσ.1]
  have hσI : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨le_of_lt hσ.1, hσ.2⟩
  have hcoord := abs_coord_ge_fifth_of_dist hσI (hZd σ hσI)
  exact (Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn hh hsσ (by norm_num) (Z σ)
    (fun a ha => krad_pos_of_add_pos' hsupp hsmall1 (by linarith [ha.1, hs.1])
      (by rw [abs_neg]; exact hcoord.1))
    (fun a ha => krad_pos_of_add_pos' hsupp hsmall1 (by linarith [ha.1, hs.1]) hcoord.2)).symm

/-! ## Closeness of the source to its unperturbed value -/

theorem lcXi_close_of_small (n : ℕ) (hn : 1 ≤ n)
    (hL1 : ThetaMCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 100 ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧
      ∀ (h : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h →
        Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
        (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
        ∀ Z : ℝ → St, ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1) →
          (∀ s : ℝ, 9 / 10 ≤ s → Z s = baseState s) →
          (∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, dist (Z s) (baseState s) ≤ θ) →
          ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10), dist (lcSrc n h Z s) (lcSrc0 n s) < ε := by
  obtain ⟨C1, hC1pos, hC1⟩ := hL1
  obtain ⟨K, hK0, hK⟩ := thetaM_tail_bound_low n hn
  obtain ⟨L₀, hL₀0, C₀, hC₀pos, hLip0, -, -⟩ :=
    Work.OddVolterra.Existence.theta_lipschitz_state_ball n hn (h := fun _ : ℝ => (0 : ℝ))
      contDiff_const supp_zero_subset small_zero_two (b := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num)
  obtain ⟨δxi, hδxi0, hδxif⟩ :=
    Work.OddVolterra.Existence.xi_close_of_small n hn (1 / 4) (by norm_num) (by norm_num)
      (ε / 6) (by linarith)
  set δ : ℝ := min (1 / 100) (min δxi (min (ε / (12 * (C1 + 1))) (ε / (12 * (K + 1)))))
    with hδdef
  set θ : ℝ := min (1 / 4) (ε / (12 * (L₀ + 1))) with hθdef
  have hC1p : (0 : ℝ) < C1 + 1 := by linarith
  have hKp : (0 : ℝ) < K + 1 := by linarith
  have hLp : (0 : ℝ) < L₀ + 1 := by linarith
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by norm_num) (lt_min hδxi0
      (lt_min (div_pos hε (by positivity)) (div_pos hε (by positivity))))
  have hδ100 : δ ≤ 1 / 100 := by rw [hδdef]; exact min_le_left _ _
  have hδxi : δ ≤ δxi := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδC1 : C1 * δ ≤ ε / 12 := by
    have hle : δ ≤ ε / (12 * (C1 + 1)) := by
      rw [hδdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have h1 : C1 * δ ≤ C1 * (ε / (12 * (C1 + 1))) := mul_le_mul_of_nonneg_left hle hC1pos.le
    have h2 : C1 * (ε / (12 * (C1 + 1))) = (C1 / (C1 + 1)) * (ε / 12) := by
      field_simp
    have h3 : C1 / (C1 + 1) ≤ 1 := by
      rw [div_le_one hC1p]; linarith
    have h4 : (C1 / (C1 + 1)) * (ε / 12) ≤ 1 * (ε / 12) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith [h1, h2, h4]
  have hδK : K * δ ≤ ε / 12 := by
    have hle : δ ≤ ε / (12 * (K + 1)) := by
      rw [hδdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have h1 : K * δ ≤ K * (ε / (12 * (K + 1))) := mul_le_mul_of_nonneg_left hle hK0
    have h2 : K * (ε / (12 * (K + 1))) = (K / (K + 1)) * (ε / 12) := by
      field_simp
    have h3 : K / (K + 1) ≤ 1 := by rw [div_le_one hKp]; linarith
    have h4 : (K / (K + 1)) * (ε / 12) ≤ 1 * (ε / 12) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith [h1, h2, h4]
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact lt_min (by norm_num) (div_pos hε (by positivity))
  have hθ4 : θ ≤ 1 / 4 := by rw [hθdef]; exact min_le_left _ _
  have hθL : L₀ * θ ≤ ε / 12 := by
    have hle : θ ≤ ε / (12 * (L₀ + 1)) := by rw [hθdef]; exact min_le_right _ _
    have h1 : L₀ * θ ≤ L₀ * (ε / (12 * (L₀ + 1))) := mul_le_mul_of_nonneg_left hle hL₀0
    have h2 : L₀ * (ε / (12 * (L₀ + 1))) = (L₀ / (L₀ + 1)) * (ε / 12) := by
      field_simp
    have h3 : L₀ / (L₀ + 1) ≤ 1 := by rw [div_le_one hLp]; linarith
    have h4 : (L₀ / (L₀ + 1)) * (ε / 12) ≤ 1 * (ε / 12) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith [h1, h2, h4]
  refine ⟨δ, hδpos, hδ100, θ, hθpos, hθ4, ?_⟩
  intro h hh hsupp hsmall Z hZ hZbase hZd s hs
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hsmall k (by omega) x) hδ100
  have hXi : ‖Xi n h s - Xi n 0 s‖ < ε / 6 :=
    hδxif h hh hsupp (fun k hk x => le_trans (hsmall k hk x) hδxi) s
      ⟨hs.1, by linarith [hs.2]⟩
  -- integrability of the two kernel integrands
  have hMi1 : IntervalIntegrable (fun σ : ℝ => KernelExt.ThetaM n h s σ (Z σ)) volume
      (7 / 10) 1 :=
    intervalIntegrable_of_continuousOn_Icc (by norm_num)
      (continuousOn_thetaM_state_of_small n hh hsupp hsm1 hs hZ
        (fun σ hσ => le_trans (hZd σ hσ) hθ4))
  have hMi2 : IntervalIntegrable (fun σ : ℝ => KernelExt.ThetaM n 0 s σ (baseState σ)) volume
      (7 / 10) 1 :=
    intervalIntegrable_of_continuousOn_Icc (by norm_num)
      ((continuousOn_thetaM_base_of_small (h := (0 : ℝ → ℝ)) n contDiff_const
        supp_zero_subset small_zero hs).mono
        (fun σ hσ => ⟨le_trans hs.2 hσ.1, hσ.2⟩))
  have hIi1 : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Z σ)) volume (7 / 10) 1 := by
    refine hMi1.congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with σ hσ
    rw [Set.uIoc_of_le (by norm_num : (7 : ℝ) / 10 ≤ 1)] at hσ
    have hsσ : s < σ := by linarith [hs.2, hσ.1]
    have hσI : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨le_of_lt hσ.1, hσ.2⟩
    have hcoord := abs_coord_ge_fifth_of_dist hσI (le_trans (hZd σ hσI) hθ4)
    exact (Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn hh hsσ (by norm_num) (Z σ)
      (fun a ha => krad_pos_of_add_pos' hsupp hsm1 (by linarith [ha.1, hs.1])
        (by rw [abs_neg]; exact hcoord.1))
      (fun a ha => krad_pos_of_add_pos' hsupp hsm1 (by linarith [ha.1, hs.1])
        hcoord.2))
  have hIi2 : IntervalIntegrable (fun σ : ℝ => Theta n 0 s σ (baseState σ)) volume (7 / 10) 1 := by
    refine hMi2.congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with σ hσ
    rw [Set.uIoc_of_le (by norm_num : (7 : ℝ) / 10 ≤ 1)] at hσ
    have hsσ : s < σ := by linarith [hs.2, hσ.1]
    have hσI : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨le_of_lt hσ.1, hσ.2⟩
    exact (Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn contDiff_const hsσ (by norm_num) (baseState σ)
      (fun a ha => krad_zero_pos_of_low (by linarith [hσI.1])
        (by linarith [ha.1, hs.1]) (by rw [abs_neg]; exact abs_profileX_ge_fifth (by
          rw [abs_le]; constructor <;> linarith [hσI.1, hσI.2])))
      (fun a ha => krad_zero_pos_of_low (by linarith [hσI.1])
        (by linarith [ha.1, hs.1]) (abs_profileX_ge_fifth (by
          rw [abs_le]; constructor <;> linarith [hσI.1, hσI.2]))))
  -- the pointwise bound on the integrand
  have hbound : ∀ σ ∈ Set.uIoc (7 / 10 : ℝ) 1,
      ‖Theta n h s σ (Z σ) - Theta n 0 s σ (baseState σ)‖ ≤ C1 * δ + L₀ * θ + K * δ := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num : (7 : ℝ) / 10 ≤ 1)] at hσ
    have hσI : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨le_of_lt hσ.1, hσ.2⟩
    have hsσ : s < σ := by linarith [hs.2, hσ.1]
    by_cases hσ19 : σ ≤ 19 / 20
    · -- the middle part: the state is close to the base state
      have hσb : σ ∈ Set.Icc (7 / 10 : ℝ) (19 / 20) := ⟨hσI.1, hσ19⟩
      have hcoord := abs_coord_ge_fifth_of_dist hσI (le_trans (hZd σ hσI) hθ4)
      have hpos1 : ∀ a ∈ Set.Icc (s - 1 / 8) σ, 0 < krad h σ (-(Z σ 0)) a :=
        fun a ha => krad_pos_of_add_pos' hsupp hsm1 (by linarith [ha.1, hs.1])
          (by rw [abs_neg]; exact hcoord.1)
      have hpos2 : ∀ a ∈ Set.Icc (s - 1 / 8) σ, 0 < krad h σ (Z σ 1) a :=
        fun a ha => krad_pos_of_add_pos' hsupp hsm1 (by linarith [ha.1, hs.1]) hcoord.2
      have hpos1' : ∀ a ∈ Set.Icc (s - 1 / 8) σ, 0 < krad (0 : ℝ → ℝ) σ (-(Z σ 0)) a :=
        fun a ha => krad_pos_of_add_pos' supp_zero_subset small_zero (by linarith [ha.1, hs.1])
          (by rw [abs_neg]; exact hcoord.1)
      have hpos2' : ∀ a ∈ Set.Icc (s - 1 / 8) σ, 0 < krad (0 : ℝ → ℝ) σ (Z σ 1) a :=
        fun a ha => krad_pos_of_add_pos' supp_zero_subset small_zero (by linarith [ha.1, hs.1])
          hcoord.2
      have e1 : KernelExt.ThetaM n h s σ (Z σ) = Theta n h s σ (Z σ) :=
        Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn hh hsσ (by norm_num) (Z σ) hpos1 hpos2
      have e2 : KernelExt.ThetaM n 0 s σ (Z σ) = Theta n 0 s σ (Z σ) :=
        Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn contDiff_const hsσ (by norm_num) (Z σ) hpos1' hpos2'
      have hzball : Z σ ∈ Metric.closedBall (baseState σ) (1 / 2) := by
        rw [Metric.mem_closedBall]
        exact le_trans (hZd σ hσI) (by linarith [hθ4])
      have hCL : ‖KernelExt.ThetaM n h s σ (Z σ) - KernelExt.ThetaM n 0 s σ (Z σ)‖ ≤ C1 * δ :=
        hC1 h hh hsupp δ hδpos hδ100 hsmall s ⟨hs.1, by linarith [hs.2]⟩ σ
          ⟨by linarith [hσI.1], hσ19⟩ (Z σ) hzball
      have hLip : ‖Theta n 0 s σ (Z σ) - Theta n 0 s σ (baseState σ)‖ ≤ L₀ * θ := by
        have h1 := hLip0 s ⟨hs.1, by linarith [hs.2]⟩ σ ⟨hsσ, by linarith [hσI.2]⟩
          (Z σ) hzball (baseState σ)
          (by rw [Metric.mem_closedBall, dist_self]; norm_num)
        have h2 : ‖Z σ - baseState σ‖ ≤ θ := by
          rw [← dist_eq_norm]; exact hZd σ hσI
        calc ‖Theta n 0 s σ (Z σ) - Theta n 0 s σ (baseState σ)‖
            ≤ L₀ * ‖Z σ - baseState σ‖ := h1
          _ ≤ L₀ * θ := mul_le_mul_of_nonneg_left h2 hL₀0
      have htri : ‖Theta n h s σ (Z σ) - Theta n 0 s σ (baseState σ)‖ ≤
          ‖Theta n h s σ (Z σ) - Theta n 0 s σ (Z σ)‖ +
            ‖Theta n 0 s σ (Z σ) - Theta n 0 s σ (baseState σ)‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle _ _ _
      calc ‖Theta n h s σ (Z σ) - Theta n 0 s σ (baseState σ)‖
          ≤ ‖Theta n h s σ (Z σ) - Theta n 0 s σ (Z σ)‖ +
              ‖Theta n 0 s σ (Z σ) - Theta n 0 s σ (baseState σ)‖ := htri
        _ = ‖KernelExt.ThetaM n h s σ (Z σ) - KernelExt.ThetaM n 0 s σ (Z σ)‖ +
              ‖Theta n 0 s σ (Z σ) - Theta n 0 s σ (baseState σ)‖ := by rw [← e1, ← e2]
        _ ≤ C1 * δ + L₀ * θ := add_le_add hCL hLip
        _ ≤ C1 * δ + L₀ * θ + K * δ := by nlinarith [mul_nonneg hK0 hδpos.le]
    · -- the frozen tail: the state is the base state, and `Z = baseState`
      push_neg at hσ19
      have h9 : (9 / 10 : ℝ) ≤ σ := by linarith
      rw [hZbase σ h9]
      have hσI' : σ ∈ Set.Icc (19 / 20 : ℝ) 1 := ⟨le_of_lt hσ19, hσ.2⟩
      have habs : |σ| ≤ 21 / 20 := by rw [abs_le]; constructor <;> linarith [hσI'.1, hσI'.2]
      have hp1 : (1 / 5 : ℝ) ≤ |baseState σ 0| := abs_profileX_ge_fifth habs
      have hp2 : (1 / 5 : ℝ) ≤ |baseState σ 1| := abs_profileX_ge_fifth habs
      have e1 : KernelExt.ThetaM n h s σ (baseState σ) = Theta n h s σ (baseState σ) :=
        Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn hh hsσ (by norm_num) (baseState σ)
          (fun a ha => krad_pos_of_add_pos' hsupp hsm1 (by linarith [ha.1, hs.1]) (by rw [abs_neg]; exact hp1))
          (fun a ha => krad_pos_of_add_pos' hsupp hsm1 (by linarith [ha.1, hs.1]) hp2)
      have e2 : KernelExt.ThetaM n 0 s σ (baseState σ) = Theta n 0 s σ (baseState σ) :=
        Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn contDiff_const hsσ (by norm_num) (baseState σ)
          (fun a ha => krad_pos_of_add_pos' supp_zero_subset small_zero (by linarith [ha.1, hs.1]) (by rw [abs_neg]; exact hp1))
          (fun a ha => krad_pos_of_add_pos' supp_zero_subset small_zero (by linarith [ha.1, hs.1]) hp2)
      have hKb := hK h δ hh hδpos hδ100 hsupp hsmall s hs σ hσI'
      rw [← e1, ← e2]
      calc ‖KernelExt.ThetaM n h s σ (baseState σ) - KernelExt.ThetaM n 0 s σ (baseState σ)‖
          ≤ K * δ := hKb
        _ ≤ C1 * δ + L₀ * θ + K * δ := by
            nlinarith [hθL, mul_nonneg hC1pos.le hδpos.le, mul_nonneg hL₀0 hθpos.le]
  -- the integral estimate
  have hint : ‖∫ σ in (7 / 10 : ℝ)..1, Theta n h s σ (Z σ) - Theta n 0 s σ (baseState σ)‖
      ≤ (C1 * δ + L₀ * θ + K * δ) * (3 / 10) := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbound) ?_
    have h3 : |(1 : ℝ) - 7 / 10| = 3 / 10 := by norm_num
    rw [h3]
  -- assemble
  have hsub : (∫ σ in (7 / 10 : ℝ)..1, Theta n h s σ (Z σ)) -
      (∫ σ in (7 / 10 : ℝ)..1, Theta n 0 s σ (baseState σ)) =
      ∫ σ in (7 / 10 : ℝ)..1, Theta n h s σ (Z σ) - Theta n 0 s σ (baseState σ) :=
    (intervalIntegral.integral_sub hIi1 hIi2).symm
  have hmain : dist (lcSrc n h Z s) (lcSrc0 n s) ≤
      ‖Xi n h s - Xi n 0 s‖ + (C1 * δ + L₀ * θ + K * δ) * (3 / 10) := by
    have hdiff : Xi n h s + (∫ σ in (7 / 10 : ℝ)..1, Theta n h s σ (Z σ)) -
        (Xi n 0 s + ∫ σ in (7 / 10 : ℝ)..1, Theta n 0 s σ (baseState σ)) =
        (Xi n h s - Xi n 0 s) +
          ((∫ σ in (7 / 10 : ℝ)..1, Theta n h s σ (Z σ)) -
            ∫ σ in (7 / 10 : ℝ)..1, Theta n 0 s σ (baseState σ)) := by abel
    rw [dist_eq_norm, lcSrc, lcSrc0, hdiff, hsub]
    refine le_trans (norm_add_le _ _) (add_le_add le_rfl hint)
  refine lt_of_le_of_lt hmain ?_
  have h14 : (C1 * δ + L₀ * θ + K * δ) ≤ ε / 4 := by linarith [hδC1, hθL, hδK]
  have : (C1 * δ + L₀ * θ + K * δ) * (3 / 10) ≤ ε / 6 := by
    calc (C1 * δ + L₀ * θ + K * δ) * (3 / 10) ≤ (ε / 4) * (3 / 10) := by
          exact mul_le_mul_of_nonneg_right h14 (by norm_num)
      _ ≤ ε / 6 := by linarith
  linarith [hXi, this]



/-- The state slot of the clamped data is `C^∞` in the state at every point. -/
lemma contDiffAt_lcGodd_snd (n : ℕ) (s : ℝ) (z : St) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w : St => lcGodd n s w) z := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : St => (s, w)) z := by fun_prop
  have hc := (contDiff_lcGodd n).contDiffAt.comp z h1
  have h' : (fun p : ℝ × St => lcGodd n p.1 p.2) ∘ (fun w : St => (s, w)) =
      fun w : St => lcGodd n s w := by funext w; rfl
  rwa [h'] at hc

lemma differentiableAt_lcGodd_snd (n : ℕ) (s : ℝ) (z : St) :
    DifferentiableAt ℝ (fun w : St => lcGodd n s w) z :=
  (contDiffAt_lcGodd_snd n s z).differentiableAt (by simp)

/-- **The unperturbed ball solves the low-slope system.** -/
theorem lc_low_hbase (n : ℕ) (hn : 1 ≤ n) :
    ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      lcGodd n s (baseState s) =
        (∫ σ in s..(7 / 10 : ℝ), lcTheta n s σ (baseState σ)) + lcSrc0 n s := by
  intro s hs
  have hsAB : s ∈ Set.Icc lcA lcB := mem_lcAB_of_mem_low hs
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_Ioo]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbase := Work.OddVolterra.Existence.base_volterra n hn s hs01
  have hbase' : Godd n 0 s (baseState s) =
      (∫ σ in s..(1 : ℝ), Theta n 0 s σ (baseState σ)) + Xi n 0 s := hbase
  set g : ℝ → St := fun σ => KernelExt.ThetaM n 0 s σ (baseState σ) with hgdef
  have hcont_g : ContinuousOn g (Set.Icc s 1) :=
    continuousOn_thetaM_base_of_small (n := n) (h := (0 : ℝ → ℝ)) contDiff_const
      supp_zero_subset small_zero hs
  have hint_g : IntervalIntegrable g volume s 1 :=
    intervalIntegrable_of_continuousOn_Icc (le_of_lt hs01.2) hcont_g
  have hsub1 : Set.uIcc s (7 / 10 : ℝ) ⊆ Set.uIcc s 1 := by
    rw [Set.uIcc_of_le hs.2, Set.uIcc_of_le (by linarith [hs.2])]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hsub2 : Set.uIcc (7 / 10 : ℝ) 1 ⊆ Set.uIcc s 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by linarith [hs.2])]
    exact Set.Icc_subset_Icc (by linarith [hs.2]) le_rfl
  have hint_g2 : IntervalIntegrable g volume s (7 / 10) := hint_g.mono_set hsub1
  have hint_g3 : IntervalIntegrable g volume (7 / 10) 1 := hint_g.mono_set hsub2
  have hsplit : (∫ σ in s..(7 / 10 : ℝ), g σ) + (∫ σ in (7 / 10 : ℝ)..1, g σ) =
      ∫ σ in s..(1 : ℝ), g σ :=
    intervalIntegral.integral_add_adjacent_intervals hint_g2 hint_g3
  have hA : (∫ σ in s..(1 : ℝ), Theta n 0 s σ (baseState σ)) = ∫ σ in s..(1 : ℝ), g σ := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    rw [Set.uIoc_of_le (by linarith [hs.2] : s ≤ 1)] at hσ
    have hsσ : s < σ := hσ.1
    have hσ1 : (1 / 8 : ℝ) ≤ σ := by linarith [hs.1, hsσ.le]
    exact (Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn contDiff_const hsσ (by norm_num) (baseState σ)
      (fun a ha => (krad_zero_pos_base hσ1 hσ.2 (by linarith [ha.1, hs.1])).1)
      (fun a ha => (krad_zero_pos_base hσ1 hσ.2 (by linarith [ha.1, hs.1])).2)).symm
  have hC : (∫ σ in s..(7 / 10 : ℝ), g σ) =
      ∫ σ in s..(7 / 10 : ℝ), lcTheta n s σ (baseState σ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    rw [Set.uIoc_of_le hs.2] at hσ
    have hsσ : s < σ := hσ.1
    have hσAB : σ ∈ Set.Icc lcA lcB :=
      mem_lcAB_of_mem_low ⟨le_trans hs.1 hsσ.le, hσ.2⟩
    exact (lcTheta_baseState n hsAB hσAB).symm
  have hD : (∫ σ in (7 / 10 : ℝ)..1, g σ) =
      ∫ σ in (7 / 10 : ℝ)..1, Theta n 0 s σ (baseState σ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    rw [Set.uIoc_of_le (by norm_num : (7 : ℝ) / 10 ≤ 1)] at hσ
    have hsσ : s < σ := by linarith [hs.2, hσ.1]
    have hσ1 : (1 / 8 : ℝ) ≤ σ := by linarith [hσ.1]
    exact Window.ThetaM_eq_Theta (δ := (1 / 8 : ℝ)) n hn contDiff_const hsσ (by norm_num) (baseState σ)
      (fun a ha => (krad_zero_pos_base hσ1 hσ.2 (by linarith [ha.1, hs.1])).1)
      (fun a ha => (krad_zero_pos_base hσ1 hσ.2 (by linarith [ha.1, hs.1])).2)
  have hmain : (∫ σ in s..(1 : ℝ), Theta n 0 s σ (baseState σ)) =
      (∫ σ in s..(7 / 10 : ℝ), lcTheta n s σ (baseState σ)) +
        (∫ σ in (7 / 10 : ℝ)..1, Theta n 0 s σ (baseState σ)) := by
    rw [hA, ← hsplit, hC, hD]
  rw [lcGodd_baseState n hsAB, hbase', hmain, lcSrc0]
  abel

/-! ## The low piece of the window construction -/

set_option maxHeartbeats 1000000 in
/-- **The low-slope piece of the odd window construction.**  The Volterra system on
`[1/4, 7/10]` with the frozen data of the unperturbed ball and the source
`Ξ n h + ∫_{7/10}^{1} Θ n h s σ (Z σ)` has a solution close to `baseState`. -/
theorem lc_low_piece_aux (n : ℕ) (hn : 1 ≤ n) (ν : ℝ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 100)
    (hL1 : ThetaMCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ))
    (hL4 : FderivGoddCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100 ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s →
        s < 1 - 2 * tau + η₀ → h s = 0) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      h 0 = 0 → h ≠ 0 →
      ∀ Z : ℝ → St,
        ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1) →
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
          Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ)) +
              Xi n h s) →
        (∀ s : ℝ, 9 / 10 ≤ s → Z s = baseState s) →
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, dist (Z s) (baseState s) ≤ θ) →
        ∃ ZL : ℝ → St,
          ContinuousOn ZL (Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) ∧
          (∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ),
            Godd n h s (ZL s) =
              (∫ σ in s..(7 / 10 : ℝ), Theta n h s σ (ZL σ)) +
                (∫ σ in (7 / 10 : ℝ)..(1 : ℝ), Theta n h s σ (Z σ)) +
                Xi n h s) ∧
          (∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ),
            dist (ZL s) (baseState s) ≤ ν) := by
  classical
  obtain ⟨Cg, hCg0, hCg⟩ := lc_low_hder n hn hL4
  obtain ⟨A, B, hB, hAspec, hAcont, hAb⟩ :=
    Work.OddCurveB.Est.exists_linearization n hn (a := (1 / 4 : ℝ)) (b := (7 / 10 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨⟨Lg, hLg0, hLg⟩, -⟩ := lc_godd_lipschitz_constants n hn
  -- the engine constants
  set ρ : ℝ := 1 / 100 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; norm_num
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; norm_num
  set M : ℝ := 2 + ((7 / 10 : ℝ) - 1 / 4) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; norm_num
  set lam : ℝ := 4 * B * Lg + 1 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; nlinarith [hB, hLg0]
  set EE : ℝ := Real.exp (lam * ((7 / 10 : ℝ) - 1 / 4)) with hEEdef
  have hEEpos : 0 < EE := by rw [hEEdef]; exact Real.exp_pos _
  have hEEdef' : EE = Real.exp ((4 * B * Lg + 1) * ((7 / 10 : ℝ) - 1 / 4)) := by
    rw [hEEdef, hlamdef]
  have hBM : 0 < 2 * B * M * EE := by positivity
  have hBM4 : 0 < 4 * B * M * EE := by positivity
  have hBM2 : 0 < 8 * B * (2 * ρ * B * Cg * M * EE + 1) := by
    have : 0 < 2 * ρ * B * Cg * M * EE + 1 := by positivity
    positivity
  set εeng : ℝ := min (1 / 100) (min (1 / 2) (min (ν / (4 * B * M * EE))
    (min (ρ / (4 * B * M * EE)) (ρ / (8 * B * (2 * ρ * B * Cg * M * EE + 1))))))
    with hεengdef
  have hεeng_100 : εeng ≤ 1 / 100 := by rw [hεengdef]; exact min_le_left _ _
  have hεeng_half : εeng ≤ 1 / 2 := by
    rw [hεengdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεengA : εeng ≤ min (1 / 2) (min (ν / (4 * B * M * EE))
      (min (ρ / (4 * B * M * EE)) (ρ / (8 * B * (2 * ρ * B * Cg * M * EE + 1))))) := by
    rw [hεengdef]
    exact min_le_right _ _
  have hεengB : εeng ≤ min (ν / (4 * B * M * EE))
      (min (ρ / (4 * B * M * EE)) (ρ / (8 * B * (2 * ρ * B * Cg * M * EE + 1)))) :=
    le_trans hεengA (min_le_right _ _)
  have hεengC : εeng ≤ min (ρ / (4 * B * M * EE))
      (ρ / (8 * B * (2 * ρ * B * Cg * M * EE + 1))) :=
    le_trans hεengB (min_le_right _ _)
  have hεengν : εeng ≤ ν / (4 * B * M * EE) := le_trans hεengB (min_le_left _ _)
  have hεengρ : εeng ≤ ρ / (4 * B * M * EE) := le_trans hεengC (min_le_left _ _)
  have hεeng3 : εeng ≤ ρ / (8 * B * (2 * ρ * B * Cg * M * EE + 1)) :=
    le_trans hεengC (min_le_right _ _)
  have hεengpos : 0 < εeng := by
    rw [hεengdef]
    refine lt_min (by norm_num) (lt_min (by norm_num) (lt_min (div_pos hν hBM4)
      (lt_min (div_pos hρpos hBM4) (div_pos hρpos hBM2))))
  have hεeng1 : εeng < 1 := by linarith [hεeng_half]
  have hεeng2 : εeng < ρ / (2 * B * M * EE) := by
    have h1 : ρ / (4 * B * M * EE) < ρ / (2 * B * M * EE) := by
      rw [div_lt_div_iff₀ hBM4 hBM]
      nlinarith [hρpos, hBM]
    linarith [hεengρ]
  have hεeng3' : εeng < ρ / (4 * B * (2 * ρ * B * Cg * M * EE + 1)) := by
    have h1 : ρ / (8 * B * (2 * ρ * B * Cg * M * EE + 1)) <
        ρ / (4 * B * (2 * ρ * B * Cg * M * EE + 1)) := by
      rw [div_lt_div_iff₀ hBM2 (by positivity)]
      nlinarith [hρpos, hBM2, hB]
    linarith [hεeng3]
  -- the source threshold and the state radius
  obtain ⟨δL, hδLpos, hδL100, θL, hθLpos, hθL4, hδLc⟩ :=
    lcXi_close_of_small n hn hL1 εeng hεengpos
  set εexp : ℝ := min (1 / 100) (min δL (εeng / (Cg + 1))) with hεexpdef
  have hCg1 : (0 : ℝ) < Cg + 1 := by linarith
  have hεexp_pos : 0 < εexp := by
    rw [hεexpdef]
    exact lt_min (by norm_num) (lt_min hδLpos (div_pos hεengpos hCg1))
  have hεexp_100 : εexp ≤ 1 / 100 := by rw [hεexpdef]; exact min_le_left _ _
  have hεexp_δL : εexp ≤ δL := by
    rw [hεexpdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεexp_Cg : εexp ≤ εeng / (Cg + 1) := by
    rw [hεexpdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hCg_ε : Cg * (εeng / (Cg + 1)) ≤ εeng := by
    have h1 : Cg * (εeng / (Cg + 1)) = (Cg / (Cg + 1)) * εeng := by field_simp
    have h2 : Cg / (Cg + 1) ≤ 1 := by rw [div_le_one hCg1]; linarith
    calc Cg * (εeng / (Cg + 1)) = (Cg / (Cg + 1)) * εeng := h1
      _ ≤ 1 * εeng := mul_le_mul_of_nonneg_right h2 hεengpos.le
      _ = εeng := one_mul _
  have hεeng_le_100 : εeng ≤ 1 / 100 := hεeng_100
  refine ⟨εexp, hεexp_pos, hεexp_100, θL, hθLpos, by linarith, ?_⟩
  intro h hh hsupp hflat hsmall h0 hne Z hZc hZeq hZtail hZd
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hsmall k (by omega) x) hεexp_100
  have hsmL : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δL :=
    fun k hk x => le_trans (hsmall k hk x) hεexp_δL
  have hsmCg : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ εeng / (Cg + 1) :=
    fun k hk x => le_trans (hsmall k hk x) hεexp_Cg
  have hZθL : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, dist (Z s) (baseState s) ≤ θL :=
    fun s hs => hZd s hs
  -- the engine hypotheses
  have hΞcont : Continuous (lcXiClamp n h Z) :=
    continuous_lcXiClamp (lcSrc_continuousOn n hn hh hsupp hsm1 hZc
      (fun s hs => le_trans (hZθL s hs) hθL4))
  have hΞ0cont : Continuous (lcXi0Clamp n) :=
    continuous_lcXi0Clamp (lcSrc_continuousOn (n := n) (hn := hn) (h := (0 : ℝ → ℝ))
      (Z := baseState) contDiff_const supp_zero_subset small_zero
      (Work.Anchor.contDiff_baseState_eng.continuous.continuousOn)
      (fun s _ => by rw [dist_self]; norm_num))
  have hGcont : Continuous (fun p : ℝ × St => lcGodd n p.1 p.2) :=
    (contDiff_lcGodd n).continuous
  have hΘcont : Continuous (fun p : ℝ × ℝ × St => lcTheta n p.1 p.2.1 p.2.2) :=
    (contDiff_lcTheta n).continuous
  have hZ₀cont : ContinuousOn baseState (Set.Icc (1 / 4 : ℝ) (7 / 10)) :=
    Work.Anchor.contDiff_baseState_eng.continuous.continuousOn
  have hG0diff : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      DifferentiableAt ℝ (fun z : St => lcGodd n s z) (baseState s) :=
    fun s _ => differentiableAt_lcGodd_snd n s (baseState s)
  have hdiff : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      ∀ z ∈ Metric.closedBall (baseState s) ρ, DifferentiableAt ℝ (fun w : St => lcGodd n s w) z :=
    fun s _ z _ => differentiableAt_lcGodd_snd n s z
  have hAspec' : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      ((A s) : St →L[ℝ] St) = fderiv ℝ (fun z : St => lcGodd n s z) (baseState s) := by
    intro s hs
    have h1 := hAspec s ⟨hs.1, by linarith [hs.2]⟩
    have h2 : fderiv ℝ (fun w : St => lcGodd n s w) (baseState s) =
        fderiv ℝ (fun w : St => Godd n 0 s w) (baseState s) :=
      (lcGodd_eventuallyEq_Godd_zero (n := n) hs).fderiv_eq
    rw [h1]
    exact h2.symm
  have hbase : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      lcGodd n s (baseState s) =
        (∫ σ in s..(7 / 10 : ℝ), lcTheta n s σ (baseState σ)) + lcXi0Clamp n s := by
    intro s hs
    rw [lcXi0Clamp_eq (show s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10) from hs)]
    exact lc_low_hbase n hn s hs
  have hΘlip : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      ∀ z ∈ Metric.closedBall (baseState σ) ρ, ∀ z' ∈ Metric.closedBall (baseState σ) ρ,
      ‖lcTheta n s σ z - lcTheta n s σ z'‖ ≤ Lg * ‖z - z'‖ :=
    fun s _ σ _ z _ z' _ => hLg s σ z z'
  have hΞc : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      dist (lcXiClamp n h Z s) (lcXi0Clamp n s) < εeng := by
    intro s hs
    have h1 : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10) := hs
    rw [lcXiClamp_eq h1, lcXi0Clamp_eq h1]
    exact hδLc h hh hsupp hsmL Z hZc hZtail hZθL s hs
  have hGc : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      ∀ z ∈ Metric.closedBall (baseState s) ρ, dist (lcGodd n s z) (lcGodd n s z) < εeng :=
    fun s _ z _ => by rw [dist_self]; exact hεengpos
  have hΘc : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      ∀ z ∈ Metric.closedBall (baseState σ) ρ,
      dist (lcTheta n s σ z) (lcTheta n s σ z) < εeng :=
    fun s _ σ _ z _ => by rw [dist_self]; exact hεengpos
  have hder : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10),
      ∀ z ∈ Metric.closedBall (baseState s) ρ,
      ‖fderiv ℝ (fun w : St => lcGodd n s w) z - ((A s) : St →L[ℝ] St)‖
        ≤ Cg * ‖z - baseState s‖ + εeng := by
    intro s hs z hz
    have h1 := hCg h hh hsupp (εeng / (Cg + 1)) (div_pos hεengpos hCg1)
      (le_trans (div_le_self hεengpos.le (by linarith [hCg0])) hεeng_100) hsmCg s hs z hz
    rw [hAspec s ⟨hs.1, by linarith [hs.2]⟩]
    have h2 : Cg * (εeng / (Cg + 1)) ≤ εeng := hCg_ε
    linarith
  -- the engine
  obtain ⟨Zc, hZcc, hZcsol, hZcdist⟩ :=
    Work.OddCurveB.Engine.volterra_long_exists_ball (E := St) (a := (1 / 4 : ℝ))
      (b := (7 / 10 : ℝ)) (by norm_num) ρ hρpos hρ1 A
      (fun s z => lcGodd n s z) (fun s z => lcGodd n s z)
      (fun s σ z => lcTheta n s σ z) (fun s σ z => lcTheta n s σ z)
      (lcXi0Clamp n) (lcXiClamp n h Z) baseState
      hB hLg0 hCg0 hG0diff hAspec' hAcont hAb hGcont hΘcont hΞcont hZ₀cont hΘcont
      hbase hΘlip hdiff M EE hMdef hEEdef' hεengpos hεeng1 hεeng2 hεeng3' hΞc hGc hΘc hder
  have hdistν : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10), dist (Zc s) (baseState s) ≤ ν := by
    intro s hs
    have h1 : 2 * B * M * EE * εeng ≤ 2 * B * M * EE * (ν / (4 * B * M * EE)) :=
      mul_le_mul_of_nonneg_left hεengν (by positivity)
    have h2 : 2 * B * M * EE * (ν / (4 * B * M * EE)) = ν / 2 := by field_simp; ring
    have h3 : dist (Zc s) (baseState s) ≤ ν / 2 := by
      rw [← h2]
      exact le_trans (hZcdist s hs) h1
    linarith [h3, hν]
  refine ⟨Zc, hZcc, ?_, hdistν⟩
  intro s hs
  have hsc : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10) := hs
  have hzν : ‖Zc s - baseState s‖ ≤ 1 / 100 := by
    rw [← dist_eq_norm]
    exact le_trans (hdistν s hs) hν2
  have hdist100 : ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (7 / 10), dist (Zc σ) (baseState σ) ≤ 1 / 100 := by
    intro σ hσ
    exact le_trans (hdistν σ hσ) hν2
  have hsol := hZcsol s hs
  change lcGodd n s (Zc s) =
      (∫ σ in s..(7 / 10 : ℝ), lcTheta n s σ (Zc σ)) + lcXiClamp n h Z s at hsol
  rw [lcXiClamp_eq hsc, lcSrc] at hsol
  rw [lcGodd_eq_Godd_of_supp hsupp hs hzν] at hsol
  have hcongr : (∫ σ in s..(7 / 10 : ℝ), lcTheta n s σ (Zc σ)) =
      ∫ σ in s..(7 / 10 : ℝ), Theta n h s σ (Zc σ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    rw [Set.uIoc_of_le hs.2] at hσ
    have hsσ : s < σ := hσ.1
    have hσI : σ ∈ Set.Icc (1 / 4 : ℝ) (7 / 10) := ⟨le_trans hs.1 hσ.1.le, hσ.2⟩
    have hd : dist (Zc σ) (baseState σ) ≤ 1 / 100 := hdist100 σ hσI
    rw [dist_eq_norm] at hd
    exact lcTheta_eq_Theta_of_supp (n := n) hn hh hsupp hsm1 hs hσI hsσ hd
  rw [hcongr] at hsol
  rw [hsol]
  abel

end

end Work.OddVolterra.WinData
