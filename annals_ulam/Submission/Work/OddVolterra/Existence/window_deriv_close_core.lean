import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.Window.JetCurve_box
import Submission.Work.OddVolterra.Window.volterra_unique
import Submission.Work.OddVolterra.Existence.data_eq_zero_of_eventuallyEq_zero
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.OddVolterra.WinData.gcl_contDiffOn
import Submission.Work.OddVolterra.WinData.tcl_contDiffOn
import Submission.Work.OddVolterra.WinData.source_contDiffOn
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat
import Submission.Work.VolterraLong.volterra_long_exists_C1
import Submission.Work.OddVolterra.Existence.wdc_aux
import Submission.Work.OddVolterra.Existence.window_state_close_core
import Submission.Work.OddVolterra.Existence.xscl_close
import Submission.Work.OddVolterra.WinData.fderiv_godd_close_box
import Submission.Work.OddVolterra.WinData.clamped_base_identity
import Submission.Work.OddVolterra.WinData.xi_deriv_close
import Submission.Work.OddVolterra.Existence.aw_frozen_tail_close
import Submission.Work.Anchor.Xi_close
import Submission.Work.OddVolterra.Window.TW2_thetaM_state_unif_of_kvec
import Submission.Work.OddVolterra.WinData.deriv2_main
import Submission.Work.OddVolterra.WinData.deriv2_hkv
import Submission.Work.OddExistence.Estimates.linearization
import Submission.Work.OddVolterra.WinData.deriv_row_of_identity

/-!
# Derivative closeness of the odd Volterra transition-window solution (core)

Auxiliary estimates on the *explicit diagonal form* of the state datum
(`Work.OddVolterra.WinData.diagForm`) and the assembly of the target
`Work.OddVolterra.Existence.window_deriv_close_core`.

`diagForm n h s z` is `Godd n h s z` in terms of `h s` and `deriv h s` only; its third and fourth
components are `π` times the explicit functions `K1d`, `K2d`.  Hence
`diagForm n h s z = Φ (s, h s, h' s, z)` for a *fixed* smooth `Φ`, and every estimate on `diagForm`
and its `s`-derivative is an instance of `Work.OddVolterra.Window.JetCurve_box` applied to `Φ`
along the curve `u ↦ (u, h u, h' u, z)`.

## Status

* proved here: the jet encoding, its compact convex box `K`, the positivity region `U`, the
  smoothness of the two diagonal outer functions `Phi1`, `Phi2`, the `s`-derivative of the jet
  curve, and `jet_curve_estimate` (a `JetCurve_box` application giving value closeness,
  `s`-derivative closeness and the `z`-Lipschitz bound with one constant);
* `diagForm_component_estimates`: the componentwise diagonal-form estimates;
* the target itself is stated at the bottom of the file (still to be assembled from the `C¹`
  chain of `WinData/thetaM_deriv_close_ext`, `WinData/thetaM_state_lipschitz_ext`,
  `WinData/xi_deriv_close`, `VolterraLong/volterra_long_exists_C1_r`, `clamped_base_identity`,
  the estimates above and the uniqueness lemma `Window.eqOn_of_solves_win`).
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

namespace DiagClose

open Work.OddVolterra.WinData

/-- The jet of the diagonal data: `(s, h s, h' s, z 0, z 1, z 2, z 3)`. -/
abbrev Jet := Fin 7 → ℝ

/-- The scalar outer function of the third component of `diagForm`. -/
def Phi1 (n : ℕ) (v : Jet) : ℝ :=
  Real.pi * (K1d n (v 0) (v 1) (v 2) (-(v 3)) * (v 5) +
    K1d n (v 0) (v 1) (v 2) (v 4) * (v 6))

/-- The scalar outer function of the fourth component of `diagForm`. -/
def Phi2 (n : ℕ) (v : Jet) : ℝ :=
  Real.pi * (K2d n (v 0) (v 1) (v 2) (-(v 3)) * (v 5) +
    K2d n (v 0) (v 1) (v 2) (v 4) * (v 6))

/-- The open region where both diagonal radicands are positive. -/
def U : Set Jet :=
  {v | 0 < ((-(v 3)) + v 2) * (2 * (v 0 * (-(v 3)) + v 1)) ∧
       0 < (v 4 + v 2) * (2 * (v 0 * v 4 + v 1))}

/-- The compact convex box in which the jets of the window lie. -/
def K : Set Jet :=
  Set.Icc (![1 / 4, -(1 / 100), -(1 / 100), 1 / 5, 1 / 5, -2, -2] : Jet)
    (![19 / 20, 1 / 100, 1 / 100, 2, 2, 2, 2] : Jet)

/-- The jet curve of the diagonal form: `u ↦ (u, h u, h' u, z 0, …, z 3)`. -/
def jet (h : ℝ → ℝ) (z : St) : ℝ → Jet :=
  fun u => ![u, h u, deriv h u, z 0, z 1, z 2, z 3]

@[simp] lemma jet_zero (h : ℝ → ℝ) (z : St) (u : ℝ) : jet h z u 0 = u := by
  simp [jet]
@[simp] lemma jet_one (h : ℝ → ℝ) (z : St) (u : ℝ) : jet h z u 1 = h u := by
  simp [jet]
@[simp] lemma jet_two (h : ℝ → ℝ) (z : St) (u : ℝ) : jet h z u 2 = deriv h u := by
  simp [jet]
@[simp] lemma jet_three (h : ℝ → ℝ) (z : St) (u : ℝ) : jet h z u 3 = z 0 := by
  simp [jet]
@[simp] lemma jet_four (h : ℝ → ℝ) (z : St) (u : ℝ) : jet h z u 4 = z 1 := by
  simp [jet]
@[simp] lemma jet_five (h : ℝ → ℝ) (z : St) (u : ℝ) : jet h z u 5 = z 2 := by
  simp [jet]
@[simp] lemma jet_six (h : ℝ → ℝ) (z : St) (u : ℝ) : jet h z u 6 = z 3 := by
  simp [jet]

lemma Phi1_comp (n : ℕ) (h : ℝ → ℝ) (z : St) :
    (fun u : ℝ => Phi1 n (jet h z u)) = fun u : ℝ => (diagForm n h u z) 2 := by
  funext u
  simp [Phi1, jet, diagForm]

lemma Phi2_comp (n : ℕ) (h : ℝ → ℝ) (z : St) :
    (fun u : ℝ => Phi2 n (jet h z u)) = fun u : ℝ => (diagForm n h u z) 3 := by
  funext u
  simp [Phi2, jet, diagForm]

lemma continuous_rad1 :
    Continuous (fun v : Jet => ((-(v 3)) + v 2) * (2 * (v 0 * (-(v 3)) + v 1))) := by
  fun_prop

lemma continuous_rad2 :
    Continuous (fun v : Jet => (v 4 + v 2) * (2 * (v 0 * v 4 + v 1))) := by
  fun_prop

lemma isOpen_U : IsOpen U := by
  unfold U
  exact IsOpen.inter (isOpen_lt continuous_const continuous_rad1)
    (isOpen_lt continuous_const continuous_rad2)

lemma convex_K : Convex ℝ K := by
  unfold K
  exact convex_Icc _ _

lemma isCompact_K : IsCompact K := by
  unfold K
  exact isCompact_Icc

lemma K_subset_U : K ⊆ U := by
  intro v hv
  have hv' := hv
  simp only [K, Set.mem_Icc, Pi.le_def] at hv'
  obtain ⟨hlo, hhi⟩ := hv'
  have h0lo : (1 / 4 : ℝ) ≤ v 0 := by simpa using hlo 0
  have h0hi : v 0 ≤ 19 / 20 := by simpa using hhi 0
  have h1lo : (-(1 / 100) : ℝ) ≤ v 1 := by simpa using hlo 1
  have h1hi : v 1 ≤ 1 / 100 := by simpa using hhi 1
  have h2lo : (-(1 / 100) : ℝ) ≤ v 2 := by simpa using hlo 2
  have h2hi : v 2 ≤ 1 / 100 := by simpa using hhi 2
  have h3lo : (1 / 5 : ℝ) ≤ v 3 := by simpa using hlo 3
  have h3hi : v 3 ≤ 2 := by simpa using hhi 3
  have h4lo : (1 / 5 : ℝ) ≤ v 4 := by simpa using hlo 4
  have h4hi : v 4 ≤ 2 := by simpa using hhi 4
  rw [U, Set.mem_setOf_eq]
  constructor
  · have ht2 : -(v 3) ≤ -(1 / 5 : ℝ) := by linarith
    have hA : (-(v 3)) + v 2 < 0 := by linarith
    have hst1 : v 0 * (-(v 3)) ≤ v 0 * (-(1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left ht2 (by linarith)
    have hst2 : v 0 * (-(1 / 5 : ℝ)) ≤ (1 / 4 : ℝ) * (-(1 / 5 : ℝ)) :=
      mul_le_mul_of_nonpos_right h0lo (by norm_num)
    have h20 : (1 / 4 : ℝ) * (-(1 / 5 : ℝ)) = -(1 / 20 : ℝ) := by norm_num
    have hsA : v 0 * (-(v 3)) + v 1 < 0 := by linarith
    nlinarith [hA, hsA]
  · have hA : 0 < v 4 + v 2 := by linarith
    have hst : (1 / 4 : ℝ) * (1 / 5 : ℝ) ≤ v 0 * v 4 :=
      mul_le_mul h0lo h4lo (by norm_num) (by linarith)
    have hsA : 0 < v 0 * v 4 + v 1 := by linarith
    nlinarith [hA, hsA]

lemma contDiffOn_K1d_neg (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K1d n (v 0) (v 1) (v 2) (-(v 3)))
      {v | 0 < ((-(v 3)) + v 2) * (2 * (v 0 * (-(v 3)) + v 1))} := by
  unfold K1d
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      ((-(v 3)) + v 2) * (2 * (v 0 * (-(v 3)) + v 1))) Set.univ := by
    fun_prop
  have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      (Nat.doubleFactorial (2 * n + 1) : ℝ) *
        (-((v 0 * (-(v 3)) + v 1) * ((-(v 3)) + v 2))) ^ (n + 1)) Set.univ := by
    fun_prop
  refine ContDiffOn.div ?_ ?_ ?_
  · exact hnum.mono (Set.subset_univ _)
  · exact (hrad.mono (Set.subset_univ _)).sqrt (fun v hv => ne_of_gt hv)
  · intro v hv
    exact ne_of_gt (Real.sqrt_pos.mpr hv)

lemma contDiffOn_K1d_pos (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K1d n (v 0) (v 1) (v 2) (v 4))
      {v | 0 < (v 4 + v 2) * (2 * (v 0 * v 4 + v 1))} := by
  unfold K1d
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      (v 4 + v 2) * (2 * (v 0 * v 4 + v 1))) Set.univ := by
    fun_prop
  have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      (Nat.doubleFactorial (2 * n + 1) : ℝ) *
        (-((v 0 * v 4 + v 1) * (v 4 + v 2))) ^ (n + 1)) Set.univ := by
    fun_prop
  refine ContDiffOn.div ?_ ?_ ?_
  · exact hnum.mono (Set.subset_univ _)
  · exact (hrad.mono (Set.subset_univ _)).sqrt (fun v hv => ne_of_gt hv)
  · intro v hv
    exact ne_of_gt (Real.sqrt_pos.mpr hv)

lemma contDiffOn_K2d_neg (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K2d n (v 0) (v 1) (v 2) (-(v 3)))
      {v | 0 < ((-(v 3)) + v 2) * (2 * (v 0 * (-(v 3)) + v 1))} := by
  unfold K2d
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      ((-(v 3)) + v 2) * (2 * (v 0 * (-(v 3)) + v 1))) Set.univ := by
    fun_prop
  have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      (Nat.doubleFactorial (2 * n - 1) : ℝ) *
        (-((v 0 * (-(v 3)) + v 1) * ((-(v 3)) + v 2))) ^ n *
        ((-(v 3)) + v 2)) Set.univ := by
    fun_prop
  refine ContDiffOn.div ?_ ?_ ?_
  · exact hnum.mono (Set.subset_univ _)
  · exact (hrad.mono (Set.subset_univ _)).sqrt (fun v hv => ne_of_gt hv)
  · intro v hv
    exact ne_of_gt (Real.sqrt_pos.mpr hv)

lemma contDiffOn_K2d_pos (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K2d n (v 0) (v 1) (v 2) (v 4))
      {v | 0 < (v 4 + v 2) * (2 * (v 0 * v 4 + v 1))} := by
  unfold K2d
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      (v 4 + v 2) * (2 * (v 0 * v 4 + v 1))) Set.univ := by
    fun_prop
  have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      (Nat.doubleFactorial (2 * n - 1) : ℝ) *
        (-((v 0 * v 4 + v 1) * (v 4 + v 2))) ^ n *
        (v 4 + v 2)) Set.univ := by
    fun_prop
  refine ContDiffOn.div ?_ ?_ ?_
  · exact hnum.mono (Set.subset_univ _)
  · exact (hrad.mono (Set.subset_univ _)).sqrt (fun v hv => ne_of_gt hv)
  · intro v hv
    exact ne_of_gt (Real.sqrt_pos.mpr hv)

lemma contDiffOn_Phi1 (n : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (Phi1 n) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K1d n (v 0) (v 1) (v 2) (-(v 3))) U :=
    (contDiffOn_K1d_neg n).mono (fun v hv => hv.1)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K1d n (v 0) (v 1) (v 2) (v 4)) U :=
    (contDiffOn_K1d_pos n).mono (fun v hv => hv.2)
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => (v 5)) U := by fun_prop
  have h4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => (v 6)) U := by fun_prop
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      K1d n (v 0) (v 1) (v 2) (-(v 3)) * (v 5) +
        K1d n (v 0) (v 1) (v 2) (v 4) * (v 6)) U :=
    ContDiffOn.add (ContDiffOn.mul h1 h3) (ContDiffOn.mul h2 h4)
  have hpi : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Jet => Real.pi) U := contDiffOn_const
  refine (ContDiffOn.mul hpi hsum).congr ?_
  intro v hv
  simp [Phi1]

lemma contDiffOn_Phi2 (n : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (Phi2 n) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K2d n (v 0) (v 1) (v 2) (-(v 3))) U :=
    (contDiffOn_K2d_neg n).mono (fun v hv => hv.1)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => K2d n (v 0) (v 1) (v 2) (v 4)) U :=
    (contDiffOn_K2d_pos n).mono (fun v hv => hv.2)
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => (v 5)) U := by fun_prop
  have h4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet => (v 6)) U := by fun_prop
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Jet =>
      K2d n (v 0) (v 1) (v 2) (-(v 3)) * (v 5) +
        K2d n (v 0) (v 1) (v 2) (v 4) * (v 6)) U :=
    ContDiffOn.add (ContDiffOn.mul h1 h3) (ContDiffOn.mul h2 h4)
  have hpi : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Jet => Real.pi) U := contDiffOn_const
  refine (ContDiffOn.mul hpi hsum).congr ?_
  intro v hv
  simp [Phi2]

/-- Bounds for the ball profile and its slope on the window. -/
lemma profileX_bounds {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) :
    (13 / 20 : ℝ) ≤ Commons.Geometry.Ulam.profileX s ∧
      Commons.Geometry.Ulam.profileX s ≤ 1 ∧
      |deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 2 := by
  have hs0 : (0:ℝ) < s := by linarith [hs.1]
  have hsq : s ^ 2 ≤ (19 / 20 : ℝ) ^ 2 := by nlinarith [hs.1, hs.2]
  have hle1 : Commons.Geometry.Ulam.profileX s ≤ 1 := by
    rw [Work.OddVolterra.Existence.profileX_eq_inv]
    refine inv_le_one_of_one_le₀ ?_
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + s ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have hge : (13 / 20 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
    rw [Work.OddVolterra.Existence.profileX_eq_inv, inv_eq_one_div, le_div_iff₀ (by positivity)]
    have h2 : Real.sqrt (1 + s ^ 2) ≤ 20 / 13 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith⟩
    linarith
  refine ⟨hge, hle1, ?_⟩
  rw [Commons.Geometry.Ulam.deriv_profileX_eq]
  have hratio : s / (1 + s ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (s - 1)]
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
  nlinarith [hratio, hle1, hge]

/-- The components of a state in the ball of radius `9/20` around `baseState s`. -/
lemma state_components {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) {z : St}
    (hz : ‖z - Work.OddVolterra.baseState s‖ ≤ 9 / 20) :
    z 0 ∈ Set.Icc (1 / 5 : ℝ) 2 ∧ z 1 ∈ Set.Icc (1 / 5 : ℝ) 2 ∧
      z 2 ∈ Set.Icc (-2 : ℝ) 2 ∧ z 3 ∈ Set.Icc (-2 : ℝ) 2 := by
  have hp := profileX_bounds hs
  have h0 : |z 0 - Commons.Geometry.Ulam.profileX s| ≤ 9 / 20 := by
    have h := norm_le_pi_norm (z - Work.OddVolterra.baseState s) 0
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    have hb : Work.OddVolterra.baseState s 0 = Commons.Geometry.Ulam.profileX s := rfl
    rw [hb] at h
    exact le_trans h hz
  have h1 : |z 1 - Commons.Geometry.Ulam.profileX s| ≤ 9 / 20 := by
    have h := norm_le_pi_norm (z - Work.OddVolterra.baseState s) 1
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    have hb : Work.OddVolterra.baseState s 1 = Commons.Geometry.Ulam.profileX s := rfl
    rw [hb] at h
    exact le_trans h hz
  have h2 : |z 2 - deriv Commons.Geometry.Ulam.profileX s| ≤ 9 / 20 := by
    have h := norm_le_pi_norm (z - Work.OddVolterra.baseState s) 2
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    have hb : Work.OddVolterra.baseState s 2 = deriv Commons.Geometry.Ulam.profileX s := rfl
    rw [hb] at h
    exact le_trans h hz
  have h3 : |z 3 - deriv Commons.Geometry.Ulam.profileX s| ≤ 9 / 20 := by
    have h := norm_le_pi_norm (z - Work.OddVolterra.baseState s) 3
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    have hb : Work.OddVolterra.baseState s 3 = deriv Commons.Geometry.Ulam.profileX s := rfl
    rw [hb] at h
    exact le_trans h hz
  have hd : |deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 2 := hp.2.2
  refine ⟨⟨by linarith [(abs_le.mp h0).1, hp.1], by linarith [(abs_le.mp h0).2, hp.2.1]⟩,
    ⟨by linarith [(abs_le.mp h1).1, hp.1], by linarith [(abs_le.mp h1).2, hp.2.1]⟩, ?_, ?_⟩
  · have h2' := abs_le.mp h2
    constructor <;> linarith [h2'.1, h2'.2, hd, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s),
      le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]
  · have h3' := abs_le.mp h3
    constructor <;> linarith [h3'.1, h3'.2, hd, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s),
      le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]

/-- The jet of the window data lies in the compact box `K`. -/
lemma jet_mem_K {h : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) {z : St}
    (hz : ‖z - Work.OddVolterra.baseState s‖ ≤ 9 / 20) :
    jet h z s ∈ K := by
  have hz' := state_components hs hz
  have h1 : |h s| ≤ δ := by
    have := hjet 0 (by norm_num) s
    rwa [iteratedDeriv_zero] at this
  have h2 : |deriv h s| ≤ δ := by
    have := hjet 1 (by norm_num) s
    rwa [iteratedDeriv_one] at this
  have hmem : jet h z s = ![s, h s, deriv h s, z 0, z 1, z 2, z 3] := rfl
  have h1a : -(1 / 100 : ℝ) ≤ h s := by linarith [hδ1, (abs_le.mp h1).1]
  have h1b : h s ≤ 1 / 100 := by linarith [hδ1, (abs_le.mp h1).2]
  have h2a : -(1 / 100 : ℝ) ≤ deriv h s := by linarith [hδ1, (abs_le.mp h2).1]
  have h2b : deriv h s ≤ 1 / 100 := by linarith [hδ1, (abs_le.mp h2).2]
  rw [hmem, K, Set.mem_Icc, Pi.le_def, Pi.le_def]
  constructor
  · intro i
    fin_cases i
    · simpa using hs.1
    · simpa using h1a
    · simpa using h2a
    · simpa using hz'.1.1
    · simpa using hz'.2.1.1
    · simpa using hz'.2.2.1.1
    · simpa using hz'.2.2.2.1
  · intro i
    fin_cases i
    · simpa using hs.2
    · simpa using h1b
    · simpa using h2b
    · simpa using hz'.1.2
    · simpa using hz'.2.1.2
    · simpa using hz'.2.2.1.2
    · simpa using hz'.2.2.2.2

/-- The jet curve is smooth. -/
lemma contDiff_jet {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (z : St) :
    ContDiff ℝ (⊤ : ℕ∞) (jet h z) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa [Function.iterate_one] using hh.iterate_deriv 1
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_id
  · simpa using hh
  · simpa using hd
  · simpa using contDiff_const (c := z 0)
  · simpa using contDiff_const (c := z 1)
  · simpa using contDiff_const (c := z 2)
  · simpa using contDiff_const (c := z 3)

/-- The derivative of the jet curve. -/
lemma deriv_jet {h : ℝ → ℝ} {s : ℝ} (hd1 : DifferentiableAt ℝ h s)
    (hd2 : DifferentiableAt ℝ (deriv h) s) (z : St) :
    deriv (jet h z) s = ![1, deriv h s, deriv (deriv h) s, 0, 0, 0, 0] := by
  have hdiff : ∀ i : Fin 7, DifferentiableAt ℝ (fun u => jet h z u i) s := by
    intro i
    fin_cases i
    · simpa using differentiableAt_id (x := s)
    · simpa using hd1
    · simpa using hd2
    · simpa using differentiableAt_const (c := z 0)
    · simpa using differentiableAt_const (c := z 1)
    · simpa using differentiableAt_const (c := z 2)
    · simpa using differentiableAt_const (c := z 3)
  rw [deriv_pi hdiff]
  funext i
  fin_cases i <;> simp [jet]

/-- Norm bound for the derivative of the jet curve. -/
lemma norm_deriv_jet_le {h : ℝ → ℝ} {s : ℝ} (hd1 : DifferentiableAt ℝ h s)
    (hd2 : DifferentiableAt ℝ (deriv h) s) (z : St) {C : ℝ} (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (h1 : |deriv h s| ≤ C) (h2 : |deriv (deriv h) s| ≤ C) :
    ‖deriv (jet h z) s‖ ≤ C := by
  rw [deriv_jet hd1 hd2 z, pi_norm_le_iff_of_nonneg hC]
  intro i
  fin_cases i
  · simpa using hC1
  · simpa [Real.norm_eq_abs] using h1
  · simpa [Real.norm_eq_abs] using h2
  · simpa using hC
  · simpa using hC
  · simpa using hC
  · simpa using hC

/-- The jet difference of two perturbations. -/
lemma norm_jet_sub_le {h : ℝ → ℝ} {s δ : ℝ} (hδ : 0 ≤ δ) (z : St)
    (h1 : |h s| ≤ δ) (h2 : |deriv h s| ≤ δ) :
    ‖jet h z s - jet 0 z s‖ ≤ δ := by
  rw [pi_norm_le_iff_of_nonneg hδ]
  intro i
  fin_cases i
  · simpa using hδ
  · simpa [Real.norm_eq_abs] using h1
  · simpa [Real.norm_eq_abs] using h2
  · simpa using hδ
  · simpa using hδ
  · simpa using hδ
  · simpa using hδ

/-- The jet difference at two states with the same perturbation. -/
lemma norm_jet_sub_state {h : ℝ → ℝ} (z z' : St) (s : ℝ) :
    ‖jet h z s - jet h z' s‖ ≤ dist z z' := by
  rw [pi_norm_le_iff_of_nonneg (dist_nonneg)]
  intro i
  fin_cases i
  · simpa using dist_nonneg (x := z) (y := z')
  · simpa using dist_nonneg (x := z) (y := z')
  · simpa using dist_nonneg (x := z) (y := z')
  · rw [dist_eq_norm]; simpa [Pi.sub_apply] using norm_le_pi_norm (z - z') 0
  · rw [dist_eq_norm]; simpa [Pi.sub_apply] using norm_le_pi_norm (z - z') 1
  · rw [dist_eq_norm]; simpa [Pi.sub_apply] using norm_le_pi_norm (z - z') 2
  · rw [dist_eq_norm]; simpa [Pi.sub_apply] using norm_le_pi_norm (z - z') 3

/-- `JetCurve_box` applied to a diagonal outer function: value closeness, `s`-derivative closeness
and the `z`-Lipschitz bound for the derivative, with the same constant. -/
lemma jet_curve_estimate {F : Jet → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      (|F (jet h z s) - F (jet 0 z s)| ≤ C * δ ∧
       |deriv (fun u : ℝ => F (jet h z u)) s - deriv (fun u : ℝ => F (jet 0 z u)) s| ≤ C * δ ∧
       |deriv (fun u : ℝ => F (jet h z u)) s - deriv (fun u : ℝ => F (jet h z' u)) s|
         ≤ C * dist z z') := by
  obtain ⟨C, hC0, hC⟩ :=
    Work.OddVolterra.Window.JetCurve_box F isOpen_U convex_K isCompact_K K_subset_U hF
      (B' := 1) (by norm_num)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro h δ hh hδ hδ1 hjet s hs z hz z' hz'
  have hδnn : 0 ≤ δ := hδ.le
  have hCd : C ≤ max C 0 := le_max_left _ _
  have hzero : ∀ k : ℕ, iteratedDeriv k (fun _ : ℝ => (0:ℝ)) = fun _ : ℝ => (0:ℝ) := by
    intro k
    induction k with
    | zero => funext y; simp
    | succ k ih => rw [iteratedDeriv_succ, ih]; funext y; simp [deriv_const]
  have hjet0 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k (fun _ : ℝ => (0:ℝ)) x| ≤ δ := by
    intro k hk x
    rw [congrFun (hzero k) x]; simpa using hδnn
  have hb0 : |h s| ≤ δ := hjet 0 (by norm_num) s
  have hb1 : |deriv h s| ≤ δ := by
    have := hjet 1 (by norm_num) s; rwa [iteratedDeriv_one] at this
  have hb2 : |deriv (deriv h) s| ≤ δ := by
    have := hjet 2 (by norm_num) s
    rwa [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at this
  have hb1' : |deriv h s| ≤ 1 := le_trans hb1 (le_trans hδ1 (by norm_num))
  have hb2' : |deriv (deriv h) s| ≤ 1 := le_trans hb2 (le_trans hδ1 (by norm_num))
  have hhd : DifferentiableAt ℝ h s := (hh.differentiable (by simp)).differentiableAt
  have hhd2 : DifferentiableAt ℝ (deriv h) s := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
      simpa [Function.iterate_one] using hh.iterate_deriv 1
    exact (hd.differentiable (by simp)).differentiableAt
  have h0d : DifferentiableAt ℝ (fun _ : ℝ => (0:ℝ)) s := differentiableAt_const 0
  have h0d2 : DifferentiableAt ℝ (deriv (fun _ : ℝ => (0:ℝ))) s := by
    rw [show deriv (fun _ : ℝ => (0:ℝ)) = fun _ : ℝ => (0:ℝ) from
      funext (fun u => deriv_const u 0)]
    exact differentiableAt_const 0
  have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (jet h z) := contDiff_jet hh z
  have hcd0 : ContDiff ℝ (⊤ : ℕ∞) (jet (fun _ : ℝ => (0:ℝ)) z) :=
    contDiff_jet contDiff_const z
  have hcdz : ContDiff ℝ (⊤ : ℕ∞) (jet h z') := contDiff_jet hh z'
  have hmem1 : jet h z s ∈ K := jet_mem_K hδnn hδ1 hjet hs hz
  have hmem0 : jet (fun _ : ℝ => (0:ℝ)) z s ∈ K := jet_mem_K hδnn hδ1 hjet0 hs hz
  have hmemz : jet h z' s ∈ K := jet_mem_K hδnn hδ1 hjet hs hz'
  have hd1 : ‖deriv (jet h z) s‖ ≤ 1 :=
    norm_deriv_jet_le hhd hhd2 z (by norm_num) (by norm_num) hb1' hb2'
  have hz0 : deriv (jet (fun _ : ℝ => (0:ℝ)) z) s = ![1, 0, 0, 0, 0, 0, 0] := by
    rw [deriv_jet h0d h0d2 z]
    funext i; fin_cases i <;> simp [deriv_const]
  have hd0 : ‖deriv (jet (fun _ : ℝ => (0:ℝ)) z) s‖ ≤ 1 := by
    rw [hz0, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i; fin_cases i <;> simp
  have hdz : ‖deriv (jet h z') s‖ ≤ 1 :=
    norm_deriv_jet_le hhd hhd2 z' (by norm_num) (by norm_num) hb1' hb2'
  have hcl : ‖jet h z s - jet (fun _ : ℝ => (0:ℝ)) z s‖ ≤ δ :=
    norm_jet_sub_le hδnn z hb0 hb1
  have hvl : ‖deriv (jet h z) s - deriv (jet (fun _ : ℝ => (0:ℝ)) z) s‖ ≤ δ := by
    rw [hz0, deriv_jet hhd hhd2 z, pi_norm_le_iff_of_nonneg hδnn]
    intro i
    fin_cases i
    · simpa using hδnn
    · simpa [Real.norm_eq_abs] using hb1
    · simpa [Real.norm_eq_abs] using hb2
    · simpa using hδnn
    · simpa using hδnn
    · simpa using hδnn
    · simpa using hδnn
  have hclz : ‖jet h z s - jet h z' s‖ ≤ dist z z' := norm_jet_sub_state z z' s
  have hvlz : ‖deriv (jet h z) s - deriv (jet h z') s‖ ≤ dist z z' := by
    rw [deriv_jet hhd hhd2 z, deriv_jet hhd hhd2 z',
      pi_norm_le_iff_of_nonneg dist_nonneg]
    intro i
    fin_cases i <;> simpa using dist_nonneg (x := z) (y := z')
  obtain ⟨-, -, -, -, hv1, hd1'⟩ := hC (jet h z) (jet (fun _ : ℝ => (0:ℝ)) z) s δ hδnn hcd1 hcd0
    hmem1 hmem0 hd1 hd0 hcl hvl
  obtain ⟨-, -, -, -, -, hd2'⟩ := hC (jet h z) (jet h z') s (dist z z') dist_nonneg hcd1 hcdz
    hmem1 hmemz hd1 hdz hclz hvlz
  refine ⟨?_, ?_, ?_⟩
  · calc |F (jet h z s) - F (jet (fun _ : ℝ => (0:ℝ)) z s)| ≤ C * δ := hv1
      _ ≤ max C 0 * δ := by
          have := mul_le_mul_of_nonneg_right hCd hδnn; linarith [this]
  · calc |deriv (fun u : ℝ => F (jet h z u)) s
          - deriv (fun u : ℝ => F (jet (fun _ : ℝ => (0:ℝ)) z u)) s| ≤ C * δ := hd1'
      _ ≤ max C 0 * δ := by
          have := mul_le_mul_of_nonneg_right hCd hδnn; linarith [this]
  · calc |deriv (fun u : ℝ => F (jet h z u)) s - deriv (fun u : ℝ => F (jet h z' u)) s|
        ≤ C * dist z z' := hd2'
      _ ≤ max C 0 * dist z z' := mul_le_mul_of_nonneg_right hCd dist_nonneg

/-- Componentwise diagonal-form estimates: value closeness, `s`-derivative closeness and the
`z`-Lipschitz bound of the `s`-derivative. -/
lemma diagForm_component_estimates (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      ∀ i : Fin 4,
      (|(diagForm n h s z) i - (diagForm n 0 s z) i| ≤ C * δ ∧
       |deriv (fun u : ℝ => (diagForm n h u z) i) s -
          deriv (fun u : ℝ => (diagForm n 0 u z) i) s| ≤ C * δ ∧
       |deriv (fun u : ℝ => (diagForm n h u z) i) s -
          deriv (fun u : ℝ => (diagForm n h u z') i) s| ≤ C * dist z z') := by
  obtain ⟨C1, hC1⟩ := jet_curve_estimate (contDiffOn_Phi1 n)
  obtain ⟨C2, hC2⟩ := jet_curve_estimate (contDiffOn_Phi2 n)
  refine ⟨max C1 C2 + 1, by linarith [hC1.1, le_max_left C1 C2], ?_⟩
  intro h δ hh hδ hδ1 hjet s hs z hz z' hz' i
  have hδnn : 0 ≤ δ := hδ.le
  have hC1le : C1 ≤ max C1 C2 + 1 := by linarith [le_max_left C1 C2]
  have hC2le : C2 ≤ max C1 C2 + 1 := by linarith [le_max_right C1 C2]
  have hCnn : (0:ℝ) ≤ max C1 C2 + 1 := by linarith [hC1.1, le_max_left C1 C2]
  obtain ⟨hv1, hd1v, hz1v⟩ := hC1.2 h δ hh hδ hδ1 hjet s hs z hz z' hz'
  obtain ⟨hv2, hd2v, hz2v⟩ := hC2.2 h δ hh hδ hδ1 hjet s hs z hz z' hz'
  have hconst1 : (diagForm n h s z) 0 = (diagForm n 0 s z) 0 := by
    simp [Work.OddVolterra.WinData.diagForm]
  have hconst2 : (diagForm n h s z) 1 = (diagForm n 0 s z) 1 := by
    simp [Work.OddVolterra.WinData.diagForm]
  have hthree : ∀ (g : ℝ → ℝ) (w : St), (fun u : ℝ => (diagForm n g u w) 2)
      = fun u : ℝ => Phi1 n (jet g w u) := by
    intro g w; exact (Phi1_comp n g w).symm
  have hfour : ∀ (g : ℝ → ℝ) (w : St), (fun u : ℝ => (diagForm n g u w) 3)
      = fun u : ℝ => Phi2 n (jet g w u) := by
    intro g w; exact (Phi2_comp n g w).symm
  have hval2 : (diagForm n h s z) 2 = Phi1 n (jet h z s) := congrFun (hthree h z) s
  have hval2' : (diagForm n 0 s z) 2 = Phi1 n (jet 0 z s) := congrFun (hthree 0 z) s
  have hval3 : (diagForm n h s z) 3 = Phi2 n (jet h z s) := congrFun (hfour h z) s
  have hval3' : (diagForm n 0 s z) 3 = Phi2 n (jet 0 z s) := congrFun (hfour 0 z) s
  have hder0 : ∀ (g : ℝ → ℝ) (w : St), deriv (fun u : ℝ => (diagForm n g u w) 0) s = 0 := by
    intro g w
    have hfun : (fun u : ℝ => (diagForm n g u w) 0) = fun _ : ℝ => w 0 := by
      funext u; simp [Work.OddVolterra.WinData.diagForm]
    rw [hfun, deriv_const]
  have hder1 : ∀ (g : ℝ → ℝ) (w : St), deriv (fun u : ℝ => (diagForm n g u w) 1) s = 0 := by
    intro g w
    have hfun : (fun u : ℝ => (diagForm n g u w) 1) = fun _ : ℝ => w 1 := by
      funext u; simp [Work.OddVolterra.WinData.diagForm]
    rw [hfun, deriv_const]
  have hmult : ∀ {a b c : ℝ}, a ≤ b → 0 ≤ c → a * c ≤ b * c :=
    fun h hc => mul_le_mul_of_nonneg_right h hc
  fin_cases i
  · have h0 : |(diagForm n h s z) 0 - (diagForm n 0 s z) 0| ≤ (max C1 C2 + 1) * δ := by
      rw [hconst1, sub_self, abs_zero]; exact mul_nonneg hCnn hδnn
    have hd : |deriv (fun u : ℝ => (diagForm n h u z) 0) s
        - deriv (fun u : ℝ => (diagForm n 0 u z) 0) s| ≤ (max C1 C2 + 1) * δ := by
      rw [hder0 h z, hder0 0 z, sub_zero, abs_zero]; exact mul_nonneg hCnn hδnn
    have hdz : |deriv (fun u : ℝ => (diagForm n h u z) 0) s
        - deriv (fun u : ℝ => (diagForm n h u z') 0) s| ≤ (max C1 C2 + 1) * dist z z' := by
      rw [hder0 h z, hder0 h z', sub_zero, abs_zero]; exact mul_nonneg hCnn dist_nonneg
    exact ⟨h0, hd, hdz⟩
  · have h1 : |(diagForm n h s z) 1 - (diagForm n 0 s z) 1| ≤ (max C1 C2 + 1) * δ := by
      rw [hconst2, sub_self, abs_zero]; exact mul_nonneg hCnn hδnn
    have hd : |deriv (fun u : ℝ => (diagForm n h u z) 1) s
        - deriv (fun u : ℝ => (diagForm n 0 u z) 1) s| ≤ (max C1 C2 + 1) * δ := by
      rw [hder1 h z, hder1 0 z, sub_zero, abs_zero]; exact mul_nonneg hCnn hδnn
    have hdz : |deriv (fun u : ℝ => (diagForm n h u z) 1) s
        - deriv (fun u : ℝ => (diagForm n h u z') 1) s| ≤ (max C1 C2 + 1) * dist z z' := by
      rw [hder1 h z, hder1 h z', sub_zero, abs_zero]; exact mul_nonneg hCnn dist_nonneg
    exact ⟨h1, hd, hdz⟩
  · have hd1' : deriv (fun u : ℝ => (diagForm n h u z) 2) s
        = deriv (fun u : ℝ => Phi1 n (jet h z u)) s := by rw [hthree h z]
    have hd2' : deriv (fun u : ℝ => (diagForm n 0 u z) 2) s
        = deriv (fun u : ℝ => Phi1 n (jet 0 z u)) s := by rw [hthree 0 z]
    have hd3' : deriv (fun u : ℝ => (diagForm n h u z') 2) s
        = deriv (fun u : ℝ => Phi1 n (jet h z' u)) s := by rw [hthree h z']
    have hv : |(diagForm n h s z) 2 - (diagForm n 0 s z) 2| ≤ (max C1 C2 + 1) * δ := by
      rw [hval2, hval2']; exact le_trans hv1 (hmult hC1le hδnn)
    have hd : |deriv (fun u : ℝ => (diagForm n h u z) 2) s
        - deriv (fun u : ℝ => (diagForm n 0 u z) 2) s| ≤ (max C1 C2 + 1) * δ := by
      rw [hd1', hd2']; exact le_trans hd1v (hmult hC1le hδnn)
    have hdz : |deriv (fun u : ℝ => (diagForm n h u z) 2) s
        - deriv (fun u : ℝ => (diagForm n h u z') 2) s| ≤ (max C1 C2 + 1) * dist z z' := by
      rw [hd1', hd3']; exact le_trans hz1v (hmult hC1le dist_nonneg)
    exact ⟨hv, hd, hdz⟩
  · have hd1' : deriv (fun u : ℝ => (diagForm n h u z) 3) s
        = deriv (fun u : ℝ => Phi2 n (jet h z u)) s := by rw [hfour h z]
    have hd2' : deriv (fun u : ℝ => (diagForm n 0 u z) 3) s
        = deriv (fun u : ℝ => Phi2 n (jet 0 z u)) s := by rw [hfour 0 z]
    have hd3' : deriv (fun u : ℝ => (diagForm n h u z') 3) s
        = deriv (fun u : ℝ => Phi2 n (jet h z' u)) s := by rw [hfour h z']
    have hv : |(diagForm n h s z) 3 - (diagForm n 0 s z) 3| ≤ (max C1 C2 + 1) * δ := by
      rw [hval3, hval3']; exact le_trans hv2 (hmult hC2le hδnn)
    have hd : |deriv (fun u : ℝ => (diagForm n h u z) 3) s
        - deriv (fun u : ℝ => (diagForm n 0 u z) 3) s| ≤ (max C1 C2 + 1) * δ := by
      rw [hd1', hd2']; exact le_trans hd2v (hmult hC2le hδnn)
    have hdz : |deriv (fun u : ℝ => (diagForm n h u z) 3) s
        - deriv (fun u : ℝ => (diagForm n h u z') 3) s| ≤ (max C1 C2 + 1) * dist z z' := by
      rw [hd1', hd3']; exact le_trans hz2v (hmult hC2le dist_nonneg)
    exact ⟨hv, hd, hdz⟩

end DiagClose

/-! ## The `s`-derivative data of the clamped data on the closed window -/

namespace WDC

/-- The function-level `smul` is the pointwise `smul`. -/
lemma smul_fun_eq_wdc (f : ℝ → ℝ) (g : ℝ → St) : (fun u => f u • g u) = f • g := by
  funext u; rfl

/-- The slope cut-off `wCs` has vanishing derivative on its plateau `[wLo, wHi]`. -/
lemma deriv_wCs_eq_zero {s : ℝ} (hs : s ∈ Set.Icc WinData.wLo WinData.wHi) :
    deriv (WinData.wCs : ℝ → ℝ) s = 0 := by
  have hmax : IsLocalMax (WinData.wCs : ℝ → ℝ) s := by
    filter_upwards with x
    rw [WinData.wCs_eq_one hs]
    exact WinData.wCs_le_one x
  exact hmax.deriv_eq_zero

lemma wCs_ne_zero_of_mem {u : ℝ} (hu : u ∈ Set.Icc WinData.wLo WinData.wHi) :
    WinData.wCs u ≠ 0 := by
  rw [WinData.wCs_eq_one hu]; norm_num

/-- Componentwise differentiability of the slope-slice of the explicit diagonal form. -/
lemma differentiableAt_diagForm_slice (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20))
    {z : St} (hz : ‖z - Work.OddVolterra.baseState s‖ ≤ 9 / 20) :
    DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z) s := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hjet 0 (by norm_num) s)
  have hmem : DiagClose.jet h z s ∈ DiagClose.K := DiagClose.jet_mem_K hδ0 hδ1 hjet hs hz
  have hUK : DiagClose.jet h z s ∈ DiagClose.U := DiagClose.K_subset_U hmem
  have hcomp : ∀ (F : DiagClose.Jet → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F DiagClose.U →
      DifferentiableAt ℝ (fun u : ℝ => F (DiagClose.jet h z u)) s := by
    intro F hF
    exact (((hF.contDiffAt (DiagClose.isOpen_U.mem_nhds hUK)).comp s
      ((DiagClose.contDiff_jet hh z).contDiffAt)).differentiableAt (by simp))
  have h0 : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z (0 : Fin 4)) s := by
    have he : (fun u : ℝ => WinData.diagForm n h u z (0 : Fin 4)) = fun _ : ℝ => z 0 := by
      funext u; simp [WinData.diagForm]
    rw [he]
    exact differentiableAt_const _
  have h1 : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z (1 : Fin 4)) s := by
    have he : (fun u : ℝ => WinData.diagForm n h u z (1 : Fin 4)) = fun _ : ℝ => z 1 := by
      funext u; simp [WinData.diagForm]
    rw [he]
    exact differentiableAt_const _
  have h2 : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z (2 : Fin 4)) s := by
    have he : (fun u : ℝ => WinData.diagForm n h u z (2 : Fin 4))
        = fun u => DiagClose.Phi1 n (DiagClose.jet h z u) := (DiagClose.Phi1_comp n h z).symm
    rw [he]
    exact hcomp (DiagClose.Phi1 n) (DiagClose.contDiffOn_Phi1 n)
  have h3 : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z (3 : Fin 4)) s := by
    have he : (fun u : ℝ => WinData.diagForm n h u z (3 : Fin 4))
        = fun u => DiagClose.Phi2 n (DiagClose.jet h z u) := (DiagClose.Phi2_comp n h z).symm
    rw [he]
    exact hcomp (DiagClose.Phi2 n) (DiagClose.contDiffOn_Phi2 n)
  refine differentiableAt_pi.mpr (fun i => ?_)
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

lemma iteratedDeriv_zero_fun_wdc (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  simp

lemma hjet_zero_wdc {δ : ℝ} (hδ0 : 0 ≤ δ) :
    ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x| ≤ δ := by
  intro k hk x
  rw [iteratedDeriv_zero_fun_wdc]; simpa using hδ0

lemma support_zero_wdc :
    Function.support (fun _ : ℝ => (0 : ℝ)) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
  fun x hx => absurd rfl hx

/-- **On the slope plateau the `s`-derivative of `Gcl` is that of the diagonal form.** -/
lemma gsCl_eq_diagForm (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Icc WinData.wLo WinData.wHi)
    {z : St} (hz : ‖z - Work.OddVolterra.baseState s‖ ≤ 9 / 20) :
    GsCl n h s z = deriv (fun u : ℝ => WinData.diagForm n h u z) s := by
  have hs14 : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := hs
  set Ψ : ℝ → St := fun u =>
    WinData.wCz (z - Work.OddVolterra.baseState u) • WinData.diagForm n h u z with hΨ
  have hwc : ∀ᶠ u in 𝓝 s, WinData.wCz (z - Work.OddVolterra.baseState u) = 1 := by
    have hc : ContinuousAt (fun u : ℝ => ‖z - Work.OddVolterra.baseState u‖) s :=
      ((continuous_const.sub continuous_baseState).norm).continuousAt
    filter_upwards [hc.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio
      (show ‖z - Work.OddVolterra.baseState s‖ < WinData.wCz.rIn by
        rw [WinData.wCz_rIn, show WinData.wRho = (1 : ℝ) / 2 from rfl]; linarith))] with u hu
    exact WinData.wCz_eq_one (le_of_lt hu)
  have hev : Ψ =ᶠ[𝓝 s] (fun u : ℝ => WinData.diagForm n h u z) := by
    filter_upwards [hwc] with u hu
    show WinData.wCz (z - Work.OddVolterra.baseState u) • WinData.diagForm n h u z
      = WinData.diagForm n h u z
    rw [hu, one_smul]
  have hD : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z) s :=
    differentiableAt_diagForm_slice n hh (by norm_num) h2 hs14 hz
  have hDΨ : DifferentiableAt ℝ Ψ s := hD.congr_of_eventuallyEq hev
  have hdΨ : deriv Ψ s = deriv (fun u : ℝ => WinData.diagForm n h u z) s :=
    Filter.EventuallyEq.deriv_eq hev
  have h2' : HasDerivAt Ψ (deriv Ψ s) s := hDΨ.hasDerivAt
  have hfun : (fun u : ℝ => WinData.Gcl n h u z) = fun u => WinData.wCs u • Ψ u := by
    funext u
    rw [hΨ, WinData.Gcl, WinData.wChiG, mul_smul]
  have hprod : deriv (fun u : ℝ => WinData.wCs u • Ψ u) s
      = WinData.wCs s • deriv Ψ s + deriv (WinData.wCs : ℝ → ℝ) s • Ψ s := by
    have h := ((((WinData.wCs_contDiff.differentiable (by simp)).differentiableAt).hasDerivAt).smul
      h2').deriv
    rwa [← smul_fun_eq_wdc] at h
  have hderiv : GsCl n h s z = deriv (fun u : ℝ => WinData.Gcl n h u z) s :=
    (gsCl_hasDerivAt hn hh hsupp h2 s z).deriv.symm
  rw [hderiv, hfun, hprod, WinData.wCs_eq_one hs, one_smul, deriv_wCs_eq_zero hs, zero_smul,
    add_zero, hdΨ]

/-- **On the slope plateau the `s`-derivative of `Tcl` is that of the manifest `Θ`-datum.** -/
lemma tsCl_eq_thetaM (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Icc WinData.wLo WinData.wHi)
    {σ : ℝ} (hσ : σ ∈ Set.Icc WinData.wLo WinData.wHi)
    {z : St} (hz : ‖z - Work.OddVolterra.baseState σ‖ ≤ 9 / 20) :
    TsCl n h s σ z = deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s := by
  have hzR : WinData.wCz (z - Work.OddVolterra.baseState σ) = 1 :=
    WinData.wCz_eq_one (le_trans hz (by rw [show WinData.wRho = (1 : ℝ) / 2 from rfl]; norm_num))
  set Φ : ℝ → St := fun u => WinData.wCs σ • (WinData.wCz (z - Work.OddVolterra.baseState σ) •
      Work.OddVolterra.KernelExt.ThetaM n h u σ z) with hΦ
  have hfun : (fun u : ℝ => WinData.Tcl n h u σ z) = fun u => WinData.wCs u • Φ u := by
    funext u
    rw [hΦ, WinData.Tcl, WinData.wChiT, mul_smul, mul_smul]
  have hTcl_d : DifferentiableAt ℝ (fun u : ℝ => WinData.Tcl n h u σ z) s :=
    (tsCl_hasDerivAt hn hh hsupp h2 s σ z).differentiableAt
  have hwne : ∀ᶠ u in 𝓝 s, WinData.wCs u ≠ 0 :=
    WinData.wCs_contDiff.continuous.continuousAt.eventually_ne (wCs_ne_zero_of_mem hs)
  have hev : (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z)
      =ᶠ[𝓝 s] (fun u => (WinData.wCs u)⁻¹ • WinData.Tcl n h u σ z) := by
    filter_upwards [hwne] with u hu
    have hcoef : WinData.wCs u * WinData.wCs σ * WinData.wCz (z - Work.OddVolterra.baseState σ)
        = WinData.wCs u := by
      rw [WinData.wCs_eq_one hσ, hzR, mul_one, mul_one]
    rw [WinData.Tcl, WinData.wChiT, hcoef, inv_smul_smul₀ hu]
  have hw_inv : DifferentiableAt ℝ (fun u : ℝ => (WinData.wCs u)⁻¹) s :=
    ((WinData.wCs_contDiff.differentiable (by simp)).differentiableAt).inv (wCs_ne_zero_of_mem hs)
  have hTh_d : DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s := by
    rw [hev.differentiableAt_iff]
    exact hw_inv.smul hTcl_d
  have hΦd : DifferentiableAt ℝ Φ s := by
    rw [hΦ]
    exact (hTh_d.const_smul (WinData.wCz (z - Work.OddVolterra.baseState σ))).const_smul
      (WinData.wCs σ)
  have hprod : deriv (fun u : ℝ => WinData.wCs u • Φ u) s
      = WinData.wCs s • deriv Φ s + deriv (WinData.wCs : ℝ → ℝ) s • Φ s := by
    have h := ((((WinData.wCs_contDiff.differentiable (by simp)).differentiableAt).hasDerivAt).smul
      hΦd.hasDerivAt).deriv
    rwa [← smul_fun_eq_wdc] at h
  have hderiv : TsCl n h s σ z = deriv (fun u : ℝ => WinData.Tcl n h u σ z) s :=
    (tsCl_hasDerivAt hn hh hsupp h2 s σ z).deriv.symm
  have hΦeq : Φ = fun u : ℝ => (WinData.wCs σ *
      WinData.wCz (z - Work.OddVolterra.baseState σ)) •
        Work.OddVolterra.KernelExt.ThetaM n h u σ z := by
    rw [hΦ]; funext u; rw [mul_smul]
  have hcm : ((WinData.wCs σ * WinData.wCz (z - Work.OddVolterra.baseState σ)) •
      (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z))
      = (fun u : ℝ => (WinData.wCs σ * WinData.wCz (z - Work.OddVolterra.baseState σ)) •
          Work.OddVolterra.KernelExt.ThetaM n h u σ z) := by
    funext u; rfl
  have hcs : deriv (fun u : ℝ => (WinData.wCs σ * WinData.wCz (z - Work.OddVolterra.baseState σ)) •
      Work.OddVolterra.KernelExt.ThetaM n h u σ z) s
      = (WinData.wCs σ * WinData.wCz (z - Work.OddVolterra.baseState σ)) •
        deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s := by
    rw [← hcm]
    exact (hTh_d.hasDerivAt.const_smul
      (WinData.wCs σ * WinData.wCz (z - Work.OddVolterra.baseState σ))).deriv
  rw [hderiv, hfun, hprod, WinData.wCs_eq_one hs, one_smul, hΦeq, hcs, WinData.wCs_eq_one hσ, hzR,
    mul_one, one_smul, deriv_wCs_eq_zero hs, zero_smul, add_zero]

/-- **On the slope plateau the derivative of the clamped source is that of the paper's source
plus the frozen tail.** -/
lemma xsCl_eq_model (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Icc WinData.wLo WinData.wHi) :
    XsCl n h s = deriv (fun u : ℝ => Work.OddVolterra.Xi n h u +
      ∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n h u σ (Work.OddVolterra.baseState σ)) s := by
  set F : ℝ → St := fun u => Work.OddVolterra.Xi n h u +
      ∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n h u σ (Work.OddVolterra.baseState σ) with hF
  have hfun : (fun u : ℝ => WinData.Xcl n h u) = fun u => WinData.wCs u • F u := by
    funext u
    rw [hF, WinData.Xcl, WinData.wChiX]
  have hXcl_d : DifferentiableAt ℝ (fun u : ℝ => WinData.Xcl n h u) s :=
    ((WinData.contDiffOn_Xcl n hn hh hsupp h1).contDiffAt (Filter.univ_mem)).differentiableAt
      (by simp)
  have hwne : ∀ᶠ u in 𝓝 s, WinData.wCs u ≠ 0 :=
    WinData.wCs_contDiff.continuous.continuousAt.eventually_ne (wCs_ne_zero_of_mem hs)
  have hev : F =ᶠ[𝓝 s] (fun u => (WinData.wCs u)⁻¹ • WinData.Xcl n h u) := by
    filter_upwards [hwne] with u hu
    rw [hF, WinData.Xcl, WinData.wChiX, inv_smul_smul₀ hu]
  have hw_inv : DifferentiableAt ℝ (fun u : ℝ => (WinData.wCs u)⁻¹) s :=
    ((WinData.wCs_contDiff.differentiable (by simp)).differentiableAt).inv (wCs_ne_zero_of_mem hs)
  have hF_d : DifferentiableAt ℝ F s := by
    rw [hev.differentiableAt_iff]
    exact hw_inv.smul hXcl_d
  have hprod : deriv (fun u : ℝ => WinData.wCs u • F u) s
      = WinData.wCs s • deriv F s + deriv (WinData.wCs : ℝ → ℝ) s • F s := by
    have h := ((((WinData.wCs_contDiff.differentiable (by simp)).differentiableAt).hasDerivAt).smul
      hF_d.hasDerivAt).deriv
    rwa [← smul_fun_eq_wdc] at h
  have hderiv : XsCl n h s = deriv (fun u : ℝ => WinData.Xcl n h u) s := rfl
  rw [hderiv, hfun, hprod, WinData.wCs_eq_one hs, one_smul, deriv_wCs_eq_zero hs, zero_smul, add_zero]

/-- The `s`-derivative data of the clamped state datum `Gcl`: closeness in `h` and
`z`-Lipschitz, on the closed slope window. -/
theorem gscl_data (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      (‖GsCl n h s z - GsCl n 0 s z‖ ≤ C * δ ∧
       ‖GsCl n h s z - GsCl n h s z'‖ ≤ C * dist z z') := by
  obtain ⟨C0, hC00, hC0⟩ := DiagClose.diagForm_component_estimates n hn
  refine ⟨C0, hC00, ?_⟩
  intro h δ hh hδ hδ1 hsupp hjet s hs z hz z' hz'
  have hδnn : 0 ≤ δ := hδ.le
  have hs14 : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := ⟨by linarith [hs.1], hs.2⟩
  have hsW : s ∈ Set.Icc WinData.wLo WinData.wHi := hs14
  have h2_100 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k hk x) hδ1
  have h2_100_0 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x| ≤ 1 / 100 := by
    intro k hk x
    rw [iteratedDeriv_zero_fun_wdc]; norm_num
  have hg1 : GsCl n h s z = deriv (fun u : ℝ => WinData.diagForm n h u z) s :=
    gsCl_eq_diagForm n hn hh hsupp h2_100 hsW hz
  have hg0 : GsCl n 0 s z = deriv (fun u : ℝ => WinData.diagForm n 0 u z) s :=
    gsCl_eq_diagForm n hn contDiff_const support_zero_wdc h2_100_0 hsW hz
  have hgz : GsCl n h s z' = deriv (fun u : ℝ => WinData.diagForm n h u z') s :=
    gsCl_eq_diagForm n hn hh hsupp h2_100 hsW hz'
  have hd1 : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z) s :=
    differentiableAt_diagForm_slice n hh hδ1 hjet hs14 hz
  have hd0 : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n 0 u z) s :=
    differentiableAt_diagForm_slice n contDiff_const hδ1 (hjet_zero_wdc hδnn) hs14 hz
  have hdz : DifferentiableAt ℝ (fun u : ℝ => WinData.diagForm n h u z') s :=
    differentiableAt_diagForm_slice n hh hδ1 hjet hs14 hz'
  refine ⟨?_, ?_⟩
  · rw [hg1, hg0, deriv_pi (differentiableAt_pi.mp hd1), deriv_pi (differentiableAt_pi.mp hd0),
      pi_norm_le_iff_of_nonneg (mul_nonneg hC00 hδnn)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (hC0 h δ hh hδ hδ1 hjet s hs14 z hz z' hz' i).2.1
  · rw [hg1, hgz, deriv_pi (differentiableAt_pi.mp hd1), deriv_pi (differentiableAt_pi.mp hdz),
      pi_norm_le_iff_of_nonneg (mul_nonneg hC00 dist_nonneg)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (hC0 h δ hh hδ hδ1 hjet s hs14 z hz z' hz' i).2.2

end WDC



/-! ## The right-hand side difference of the linearised equation -/

/-- The difference of the right-hand sides of the linearised clamped equation (perturbed state
`Z` against the base state) is `O(δ)`, with a constant uniform in `h` and `δ`. -/
theorem rhs_diff (n : ℕ) (hn : 1 ≤ n) (Kc : ℝ) (hKc : 0 ≤ Kc) (CX : ℝ) (hCX : 0 ≤ CX)
    (hXscl : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        ‖XsCl n h s - XsCl n 0 s‖ ≤ CX * δ) :
    ∃ Mrhs : ℝ, 0 ≤ Mrhs ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      Kc * δ ≤ 9 / 20 →
      ∀ Z : ℝ → St, ContinuousOn Z (Set.Icc (7 / 10 : ℝ) (19 / 20)) →
      (∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), dist (Z s) (baseState s) ≤ Kc * δ) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        ‖(- GsCl n h s (Z s) - WinData.Tcl n h s s (Z s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) + XsCl n h s)
          - (- GsCl n 0 s (baseState s) - WinData.Tcl n 0 s s (baseState s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)) + XsCl n 0 s)‖
          ≤ Mrhs * δ := by
  obtain ⟨Cgs, hCgsnn, hGscl⟩ := WDC.gscl_data n hn
  obtain ⟨CTh, hCThpos, hTclc⟩ := WinData.thetaM_close_box n hn (a := 7 / 10) (b := 1)
    (ρ := 9 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Mk, Ck, hMknn, hCknn, hkvec⟩ := Work.OddVolterra.Window.TW2_kvecM_state_unif n hn
  obtain ⟨MTh, BTh, hMThnn, hBThnn, hTcls⟩ :=
    Work.OddVolterra.Window.TW2_thetaM_state_unif_of_kvec n hn Mk Ck hMknn hCknn hkvec
  obtain ⟨CD, LD, hCDpos, hLDpos, hTder⟩ :=
    WinData.thetaM_deriv_close_of_KvecM n hn (WinData.KvecM_deriv2_ext n hn)
  refine ⟨(Cgs * Kc + Cgs) + (MTh * Kc + CTh) + ((1 / 4) * (LD * Kc + CD)) + CX + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Cgs * Kc := mul_nonneg hCgsnn hKc
    have h2 : 0 ≤ MTh * Kc := mul_nonneg hMThnn hKc
    have h3 : 0 ≤ LD * Kc := mul_nonneg hLDpos.le hKc
    have h4 : 0 ≤ (1 / 4) * (LD * Kc + CD) := by
      have h5 : 0 ≤ LD * Kc + CD := by linarith [h3, hCDpos.le]
      positivity
    linarith [h1, h2, h3, h4, hCgsnn, hCThpos.le, hCDpos.le, hCX]
  · intro h δ hh hδpos hδ100 hjet hsupp hKc9 Z hZc hZdist s hs
    have hδnn : 0 ≤ δ := hδpos.le
    have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
      fun k hk x => le_trans (hjet k (by omega) x) hδ100
    have hδ2 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ :=
      fun k hk x => hjet k (by omega) x
    have hδn2 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ :=
      fun k hk x => hjet k (by omega) x
    have h100n2 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
      fun k hk x => le_trans (hjet k (by omega) x) hδ100
    have hZm : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), ‖Z u - baseState u‖ ≤ 9 / 20 := by
      intro u hu
      have h1 := hZdist u hu
      rw [dist_eq_norm] at h1
      linarith [hKc9]
    have hZm9 : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        Z u ∈ Metric.closedBall (baseState u) (9 / 20) :=
      fun u hu => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hZm u hu
    have hbm : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        baseState u ∈ Metric.closedBall (baseState u) (9 / 20) :=
      fun u _ => Metric.mem_closedBall_self (by norm_num)
    have hW : s ∈ Set.Icc WinData.wLo WinData.wHi := by
      rw [WinData.wLo, WinData.wHi]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have htwice : ‖Z s - baseState s‖ ≤ Kc * δ := by
      have h1 := hZdist s hs; rwa [dist_eq_norm] at h1
    -- term 1: the state datum
    have hterm1 : ‖GsCl n h s (Z s) - GsCl n 0 s (baseState s)‖ ≤ (Cgs * Kc + Cgs) * δ := by
      have hA := (hGscl h δ hh hδpos hδ100 hsupp hδ2 s hs (Z s) (hZm9 s hs)
        (baseState s) (hbm s hs))
      have hB := (hGscl h δ hh hδpos hδ100 hsupp hδ2 s hs (baseState s) (hbm s hs)
        (baseState s) (hbm s hs))
      have ht := dist_triangle (GsCl n h s (Z s)) (GsCl n h s (baseState s))
        (GsCl n 0 s (baseState s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      have hA2 : ‖GsCl n h s (Z s) - GsCl n h s (baseState s)‖ ≤ Cgs * ‖Z s - baseState s‖ := by
        have h := hA.2
        rwa [dist_eq_norm] at h
      have h2 : Cgs * ‖Z s - baseState s‖ ≤ Cgs * (Kc * δ) :=
        mul_le_mul_of_nonneg_left htwice hCgsnn
      nlinarith [ht, hA2, hB.1, h2, hCgsnn, hKc, hδnn]
    -- term 2: the diagonal datum
    have hterm2 : ‖WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)‖
        ≤ (MTh * Kc + CTh) * δ := by
      have hA := (hTcls h hh hsupp h100n2 s hs s hs (Z s) (hZm9 s hs))
      have hTcl1 : WinData.Tcl n h s s (Z s) = Work.OddVolterra.KernelExt.ThetaM n h s s (Z s) :=
        WinData.Tcl_eq_ThetaM hW hW
          (by rw [show WinData.wRho = (1 : ℝ) / 2 from rfl]; linarith [hZm s hs])
      have hTcl0 : WinData.Tcl n 0 s s (baseState s) =
          Work.OddVolterra.KernelExt.ThetaM n 0 s s (baseState s) :=
        WinData.Tcl_eq_ThetaM hW hW
          (by rw [show WinData.wRho = (1 : ℝ) / 2 from rfl]; norm_num)
      have hTclb : WinData.Tcl n h s s (baseState s) =
          Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s) :=
        WinData.Tcl_eq_ThetaM hW hW
          (by rw [show WinData.wRho = (1 : ℝ) / 2 from rfl]; norm_num)
      have hB := hTclc h hh hsupp δ hδpos hδ100 hδn2 s ⟨hs.1, by linarith [hs.2]⟩ s
        ⟨hs.1, by linarith [hs.2]⟩ (baseState s) (hbm s hs)
      have ht := dist_triangle (Work.OddVolterra.KernelExt.ThetaM n h s s (Z s))
        (Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s))
        (Work.OddVolterra.KernelExt.ThetaM n 0 s s (baseState s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      have h4 : ‖Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s) -
          Work.OddVolterra.KernelExt.ThetaM n 0 s s (baseState s)‖ ≤ CTh * δ := by
        rw [← dist_eq_norm]; exact hB
      have hA2 : ‖Work.OddVolterra.KernelExt.ThetaM n h s s (Z s) -
          Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s)‖
          ≤ MTh * ‖Z s - baseState s‖ :=
        hA.2 (baseState s) (hbm s hs)
      have h2 : MTh * ‖Z s - baseState s‖ ≤ MTh * (Kc * δ) :=
        mul_le_mul_of_nonneg_left htwice hMThnn
      rw [hTcl1, hTcl0]
      nlinarith [ht, hA2, h4, h2, hMThnn, hCThpos.le, hKc, hδnn]
    -- term 3: the integral
    have hcontT : ContinuousOn (fun σ : ℝ => TsCl n h s σ (Z σ)) (Set.Icc s (19 / 20)) := by
      have hcurve : ContinuousOn (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc s (19 / 20)) :=
        continuousOn_const.prodMk (continuousOn_id.prodMk
          (hZc.mono (by intro x hx; exact ⟨le_trans hs.1 hx.1, hx.2⟩)))
      exact (tsCl_continuous (n := n) hn hh hsupp hsmall2).comp_continuousOn' hcurve
    have hI1 : IntervalIntegrable (fun σ : ℝ => TsCl n h s σ (Z σ)) volume s (19 / 20) :=
      hcontT.intervalIntegrable_of_Icc hs.2
    have hcontT0 : ContinuousOn (fun σ : ℝ => TsCl n 0 s σ (baseState σ)) (Set.Icc s (19 / 20)) := by
      have hcurve : ContinuousOn (fun σ : ℝ => (s, σ, baseState σ)) (Set.Icc s (19 / 20)) :=
        continuousOn_const.prodMk (continuousOn_id.prodMk
          (Work.OddVolterra.Existence.continuous_baseState.continuousOn.mono (Set.subset_univ _)))
      exact (tsCl_continuous (n := n) hn contDiff_const WDC.support_zero_wdc
        (WDC.hjet_zero_wdc (by norm_num))).comp_continuousOn' hcurve
    have hI2 : IntervalIntegrable (fun σ : ℝ => TsCl n 0 s σ (baseState σ)) volume s (19 / 20) :=
      hcontT0.intervalIntegrable_of_Icc hs.2
    have hpt : ∀ σ ∈ Set.Icc s (19 / 20),
        ‖TsCl n h s σ (Z σ) - TsCl n 0 s σ (baseState σ)‖ ≤ (LD * Kc + CD) * δ := by
      intro σ hσ
      have hσ9 : σ ∈ Set.Icc (7 / 10 : ℝ) (19 / 20) := ⟨le_trans hs.1 hσ.1, hσ.2⟩
      have hσW : σ ∈ Set.Icc WinData.wLo WinData.wHi := by
        rw [WinData.wLo, WinData.wHi]
        exact ⟨by linarith [hσ9.1], by linarith [hσ9.2]⟩
      have hZm9' : Z σ ∈ Metric.closedBall (baseState σ) (9 / 20) := hZm9 σ hσ9
      have hbm' : baseState σ ∈ Metric.closedBall (baseState σ) (9 / 20) := hbm σ hσ9
      have e1 : TsCl n h s σ (Z σ) =
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (Z σ)) s :=
        WDC.tsCl_eq_thetaM n hn hh hsupp hsmall2 hW hσW hZm9'
      have e2 : TsCl n h s σ (baseState σ) =
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (baseState σ)) s :=
        WDC.tsCl_eq_thetaM n hn hh hsupp hsmall2 hW hσW hbm'
      have e3 : TsCl n 0 s σ (baseState σ) =
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n 0 u σ (baseState σ)) s :=
        WDC.tsCl_eq_thetaM n hn contDiff_const WDC.support_zero_wdc
          (WDC.hjet_zero_wdc (by norm_num)) hW hσW hbm'
      have hA := (hTder h δ hh hδpos hδ100 hjet hsupp s ⟨by linarith [hs.1], hs.2⟩ σ
        ⟨by linarith [hσ9.1], by linarith [hσ.2]⟩ (Z σ) hZm9' (baseState σ) hbm')
      have hA0 := (hTder h δ hh hδpos hδ100 hjet hsupp s ⟨by linarith [hs.1], hs.2⟩ σ
        ⟨by linarith [hσ9.1], by linarith [hσ.2]⟩ (baseState σ) hbm' (baseState σ) hbm')
      have ht := dist_triangle (TsCl n h s σ (Z σ)) (TsCl n h s σ (baseState σ))
        (TsCl n 0 s σ (baseState σ))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      rw [e1, e2, e3] at ht
      rw [e1, e3]
      have hA2 : ‖deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (Z σ)) s -
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (baseState σ)) s‖
          ≤ LD * ‖Z σ - baseState σ‖ := hA.2
      have h2 : LD * ‖Z σ - baseState σ‖ ≤ LD * (Kc * δ) :=
        mul_le_mul_of_nonneg_left (by have h1 := hZdist σ hσ9; rwa [dist_eq_norm] at h1) hLDpos.le
      nlinarith [ht, hA2, hA0.1, h2, hLDpos.le, hCDpos.le, hKc, hδnn]
    have hterm3 : ‖(∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
        (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))‖
        ≤ ((1 / 4) * (LD * Kc + CD)) * δ := by
      rw [← intervalIntegral.integral_sub hI1 hI2]
      have hb : ∀ σ ∈ Set.uIoc s (19 / 20),
          ‖TsCl n h s σ (Z σ) - TsCl n 0 s σ (baseState σ)‖ ≤ (LD * Kc + CD) * δ := by
        intro σ hσ
        rw [Set.uIoc_of_le hs.2] at hσ
        exact hpt σ (Set.Ioc_subset_Icc_self hσ)
      have hC : 0 ≤ (LD * Kc + CD) * δ := by
        have h1 : 0 ≤ LD * Kc := mul_nonneg hLDpos.le hKc
        nlinarith [h1, hCDpos.le, hδnn]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hb) ?_
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 19 / 20 - s)]
      have hbs : 19 / 20 - s ≤ 19 / 20 - 7 / 10 := by linarith [hs.1]
      have hK3 : 0 ≤ LD * Kc + CD := by
        have h1 : 0 ≤ LD * Kc := mul_nonneg hLDpos.le hKc
        linarith [h1, hCDpos.le]
      calc (LD * Kc + CD) * δ * (19 / 20 - s)
          ≤ (LD * Kc + CD) * δ * (19 / 20 - 7 / 10) :=
            mul_le_mul_of_nonneg_left hbs (mul_nonneg hK3 hδnn)
        _ = ((1 / 4) * (LD * Kc + CD)) * δ := by ring
    -- term 4: the source
    have hterm4 : ‖XsCl n h s - XsCl n 0 s‖ ≤ CX * δ := hXscl h δ hh hδpos hδ100 hjet hsupp s hs
    -- assemble
    have hsplit : (- GsCl n h s (Z s) - WinData.Tcl n h s s (Z s) +
          (∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) + XsCl n h s)
        - (- GsCl n 0 s (baseState s) - WinData.Tcl n 0 s s (baseState s) +
          (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)) + XsCl n 0 s)
        = (-(GsCl n h s (Z s) - GsCl n 0 s (baseState s)))
          + (-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
          + (((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
              (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)))
            + (XsCl n h s - XsCl n 0 s)) := by abel
    have h5 : ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))‖ ≤ (Cgs * Kc + Cgs) * δ := by
      rw [norm_neg]; exact hterm1
    have h6 : ‖-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
        ≤ (MTh * Kc + CTh) * δ := by rw [norm_neg]; exact hterm2
    have h1 := norm_add_le (-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))
        + -(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
      (((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
          (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))) + (XsCl n h s - XsCl n 0 s))
    have h2 := norm_add_le (-(GsCl n h s (Z s) - GsCl n 0 s (baseState s)))
      (-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
    have h3 := norm_add_le ((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
        (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))) (XsCl n h s - XsCl n 0 s)
    have h7 : ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))‖
        + ‖-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
        + (‖(∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
            (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))‖
          + ‖XsCl n h s - XsCl n 0 s‖)
        ≤ ((Cgs * Kc + Cgs) + (MTh * Kc + CTh) + ((1 / 4) * (LD * Kc + CD)) + CX + 1) * δ := by
      nlinarith [h5, h6, hterm3, hterm4, hCgsnn, hMThnn, hCDpos.le, hLDpos.le, hCX, hCThpos.le,
        hKc, hδnn]
    calc ‖(- GsCl n h s (Z s) - WinData.Tcl n h s s (Z s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) + XsCl n h s)
          - (- GsCl n 0 s (baseState s) - WinData.Tcl n 0 s s (baseState s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)) + XsCl n 0 s)‖
        = ‖(-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))
            + -(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
            + (((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
                (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)))
              + (XsCl n h s - XsCl n 0 s))‖ := by rw [hsplit]
      _ ≤ ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))
            + -(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
          + ‖((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
              (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)))
            + (XsCl n h s - XsCl n 0 s)‖ := h1
      _ ≤ ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))‖
            + ‖-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
          + (‖(∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
              (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))‖
            + ‖XsCl n h s - XsCl n 0 s‖) := by linarith [h2, h3]
      _ ≤ ((Cgs * Kc + Cgs) + (MTh * Kc + CTh) + ((1 / 4) * (LD * Kc + CD)) + CX + 1) * δ := h7

/-! ## The right-hand side of the differentiated clamped equation -/

/-- The right-hand side of the differentiated clamped equation along a state curve `c`: this is
the expression whose `h = 0` versus `h ≠ 0` difference is bounded by `rhs_diff`. -/
def winRHS (n : ℕ) (g : ℝ → ℝ) (c : ℝ → St) (s : ℝ) : St :=
  - GsCl n g s (c s) - WinData.Tcl n g s s (c s) +
    (∫ σ in s..(19 / 20 : ℝ), TsCl n g s σ (c σ)) + XsCl n g s

/-- **The differentiated clamped base identity, separated.**  For the base state `baseState` and
the linearisation `A` of the unperturbed state datum, the left-hand side of the differentiated
clamped identity is the right-hand side `winRHS` of the linearised equation. -/
theorem winRHS_base (n : ℕ) (hn : 1 ≤ n) (A : ℝ → St ≃L[ℝ] St)
    (hA : ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
      (A s : St →L[ℝ] St) = fderiv ℝ (fun z => Godd n 0 s z) (baseState s)) :
    ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), (A s) (deriv baseState s) = winRHS n 0 baseState s := by
  intro s hs
  have hsW : s ∈ Set.Icc WinData.wLo WinData.wHi := by
    rw [WinData.wLo, WinData.wHi]
    exact ⟨by linarith [hs.1], hs.2⟩
  have hb := (WinData.clamped_base_identity n hn).2 s ⟨by linarith [hs.1], hs.2⟩
  have hjet0 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x| ≤ 1 / 100 :=
    WDC.hjet_zero_wdc (by norm_num)
  have e1 : deriv (fun u : ℝ => WinData.Gcl n 0 u (baseState s)) s
      = GsCl n 0 s (baseState s) :=
    (gsCl_hasDerivAt (n := n) (h := 0) hn contDiff_const WDC.support_zero_wdc hjet0 s
      (baseState s)).deriv
  have e4 : fderiv ℝ (fun z : St => WinData.Gcl n 0 s z) (baseState s) = (A s : St →L[ℝ] St) := by
    have hev : (fun z : St => WinData.Gcl n 0 s z) =ᶠ[𝓝 (baseState s)]
        (fun z : St => Godd n 0 s z) := by
      filter_upwards [Metric.ball_mem_nhds (baseState s) (show (0 : ℝ) < 1 / 2 by norm_num)]
        with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact WinData.Gcl_eq_Godd hsW (le_of_lt hz)
    rw [hev.fderiv_eq, ← hA s hs]
  have e5 : (∫ σ in s..(19 / 20 : ℝ),
        deriv (fun u : ℝ => WinData.Tcl n 0 u σ (baseState σ)) s)
      = ∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ) := by
    refine intervalIntegral.integral_congr fun σ _ => ?_
    exact (tsCl_hasDerivAt (n := n) (h := 0) hn contDiff_const WDC.support_zero_wdc hjet0 s σ
      (baseState σ)).deriv
  have e3 : deriv (fun u : ℝ => WinData.Xcl n 0 u) s = XsCl n 0 s := rfl
  rw [e1, e4, e5, e3] at hb
  have h1 : (A s) (deriv baseState s) =
      (-WinData.Tcl n 0 s s (baseState s) +
        (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))) + XsCl n 0 s
        - GsCl n 0 s (baseState s) := by
    rw [← hb]; abel
  rw [winRHS, h1]; abel

/-- **L-2 core lemma.**  The `C¹`-closeness (NRZ Lemma 8) of the odd transition-window solution:
every smooth solution `Z` of the paper's system in the `C^{n+3}` bump class which agrees with the
ball's state beyond `9/10` has `deriv Z` within `C ε` of `deriv baseState` on `[7/10, 9/10]`.

The proof is the linearised comparison: on the window `[7/10, 19/20]` the given `Z` solves the
*clamped* system (`clamped_solves_of_paper`), whose linearisation about the base state is
`A s = D_z 𝐆 n 0 s (baseState s)`.  The difference of the two right-hand sides is `O(ε)` by
`rhs_diff`, the defect `‖D_z 𝐆 n h s (Z s) - A s‖` is `O(ε)` by `fderiv_godd_close_box` and the
`C⁰`-closeness `window_state_close_core`, and the perturbed inverse `solve_near_equiv` then bounds
the solution of the linearised equation; `deriv_from_solution_linearized` identifies it with
`deriv Z`. -/
theorem window_deriv_close_core (n : ℕ) (hn : 1 ≤ n) :
    ∃ C ε₁ : ℝ, 0 < C ∧ 0 < ε₁ ∧ ε₁ ≤ 1 / 100 ∧
      ∀ (h : ℝ → ℝ) (Z : ℝ → Work.OddVolterra.St) (ε : ℝ), 0 < ε → ε ≤ ε₁ →
        Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)) →
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) →
        (∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s) →
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2) →
        ∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
          dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s)
            ≤ C * ε
:= by
  -- the `C⁰`-closeness of an arbitrary solution
  obtain ⟨Kc, εc, hKcpos, hεcpos, hεc100, hclose⟩ := window_state_close_core n hn
  -- the closeness of the derivative of the clamped source
  obtain ⟨CX, hCXnn, hXscl⟩ := xscl_close n hn
  -- the `O(ε)` bound on the difference of the right-hand sides
  obtain ⟨Mrhs, hMrhsnn, hRdiff⟩ := rhs_diff n hn Kc hKcpos.le CX hCXnn hXscl
  -- the linearisation of the unperturbed datum about the base solution
  obtain ⟨A, B, hBpos, hAeq, _hAcont, hAinv⟩ :=
    Work.OddExistence.Estimates.linearization n hn (a := (7 / 10 : ℝ)) (b := (19 / 20 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  -- the closeness of the differential of the datum
  obtain ⟨Cg, hCgpos, hCgclose⟩ :=
    WinData.fderiv_godd_close_box n hn (a := (7 / 10 : ℝ)) (b := (19 / 20 : ℝ))
      (ρ := (9 / 20 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- the base state is smooth, and its derivative is bounded on the window
  have hcb : ContDiff ℝ (⊤ : ℕ∞) (baseState : ℝ → St) :=
    contDiff_baseState_comp.comp
      (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : St))))
  have hcd : Continuous (deriv (baseState : ℝ → St)) := hcb.continuous_deriv (by simp)
  obtain ⟨S, hSpos, hSbd⟩ : ∃ S : ℝ, 0 < S ∧
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), ‖deriv (baseState : ℝ → St) s‖ ≤ S := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcd.continuousOn
      (f := deriv (baseState : ℝ → St))
    exact ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
      fun s hs => le_trans (hC s hs) (le_max_left _ _)⟩
  obtain ⟨KK, hKKdef⟩ : ∃ K : ℝ, K = 2 * B * (Cg * (Kc + 1) * S + Mrhs) := ⟨_, rfl⟩
  have hKKpos : 0 < KK := by
    rw [hKKdef]
    have h1 : 0 < Cg * (Kc + 1) * S := mul_pos (mul_pos hCgpos (by linarith)) hSpos
    have h2 : 0 < Cg * (Kc + 1) * S + Mrhs := by linarith [h1, hMrhsnn]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hBpos) h2
  have hε₁pos : 0 < min (1 / 100) (min εc (min (9 / (20 * Kc)) (1 / (2 * B * Cg * (Kc + 1))))) := by
    refine lt_min (by norm_num) (lt_min hεcpos (lt_min ?_ ?_))
    · positivity
    · positivity
  refine ⟨KK, _, hKKpos, hε₁pos, min_le_left _ _, ?_⟩
  intro h Z ε hεpos hεε₁ hbump hZsm heq htail hball s hs
  -- ## unpacking the hypotheses
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hbump.1
  have hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) :=
    fun x hx => ⟨le_of_lt (hbump.2.1 hx).1, le_of_lt (hbump.2.1 hx).2⟩
  have hjet : ∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ ε :=
    fun k hk x => hbump.2.2.1 k hk x
  have hε100 : ε ≤ 1 / 100 := le_trans hεε₁ (min_le_left _ _)
  have hεεc : ε ≤ εc := le_trans hεε₁ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε9 : ε ≤ 9 / (20 * Kc) :=
    le_trans hεε₁ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεB : ε ≤ 1 / (2 * B * Cg * (Kc + 1)) :=
    le_trans hεε₁ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k (by omega) x) hε100
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k (by omega) x) hε100
  have hjetn2 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ ε :=
    fun k hk x => hjet k (by omega) x
  -- ## the smallness conditions on `ε`
  have hKc9 : Kc * ε ≤ 9 / 20 := by
    have h1 : Kc * ε ≤ Kc * (9 / (20 * Kc)) := mul_le_mul_of_nonneg_left hε9 hKcpos.le
    have h2 : Kc * (9 / (20 * Kc)) = 9 / 20 := by field_simp
    linarith [h1, h2]
  have hκB : B * (Cg * (Kc + 1) * ε) ≤ 1 / 2 := by
    have h1 : Cg * (Kc + 1) * ε ≤ Cg * (Kc + 1) * (1 / (2 * B * Cg * (Kc + 1))) :=
      mul_le_mul_of_nonneg_left hεB (by positivity)
    have h2 : Cg * (Kc + 1) * (1 / (2 * B * Cg * (Kc + 1))) = 1 / (2 * B) := by field_simp
    have h3 : B * (Cg * (Kc + 1) * ε) ≤ B * (1 / (2 * B)) := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hBpos.le
    have h4 : B * (1 / (2 * B)) = 1 / 2 := by field_simp
    linarith [h3, h4]
  -- ## the state closeness on the whole window
  have hZdist : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), dist (Z u) (baseState u) ≤ Kc * ε := by
    intro u hu
    by_cases h9 : u ≤ 9 / 10
    · exact hclose h Z ε hεpos hεεc hbump hZsm heq htail hball u ⟨hu.1, h9⟩
    · push_neg at h9
      rw [htail u (le_of_lt h9), dist_self]
      exact mul_nonneg hKcpos.le hεpos.le
  have hZcont : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) (19 / 20)) :=
    (hZsm.continuousOn).mono fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1])
  have hsol : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), WinData.Gcl n h u (Z u) =
      (∫ σ in u..WinData.wHi, WinData.Tcl n h u σ (Z σ)) + WinData.Xcl n h u :=
    fun u hu => clamped_solves_of_paper (n := n) (Z := Z) hn hh hsupp hsmall1 hZsm heq htail
      hball hu
  have hZm9 : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
      Z u ∈ Metric.closedBall (baseState u) (9 / 20) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := hZdist u hu
    rw [dist_eq_norm] at h1
    linarith [h1, hKc9]
  -- ## the defect of the differential
  have hJκ : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
      ‖fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u) - (A u : St →L[ℝ] St)‖
        ≤ Cg * (Kc + 1) * ε := by
    intro u hu
    have huW : u ∈ Set.Icc WinData.wLo WinData.wHi := by
      rw [WinData.wLo, WinData.wHi]
      exact ⟨by linarith [hu.1], hu.2⟩
    have hAcl : fderiv ℝ (fun w : St => Godd n h u w) (Z u) =
        fderiv ℝ (fun w : St => WinData.Gcl n h u w) (Z u) := by
      have hev : (fun w : St => WinData.Gcl n h u w) =ᶠ[𝓝 (Z u)]
          (fun w : St => Godd n h u w) := by
        filter_upwards [Metric.ball_mem_nhds (Z u) (show (0 : ℝ) < 1 / 20 by norm_num)]
          with w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have h2 := hZm9 u hu
        rw [Metric.mem_closedBall, dist_eq_norm] at h2
        refine WinData.Gcl_eq_Godd huW ?_
        rw [WinData.wRho]
        have h3 : ‖w - baseState u‖ ≤ ‖w - Z u‖ + ‖Z u - baseState u‖ := by
          have ht := dist_triangle w (Z u) (baseState u)
          rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
        linarith [h3, hw, h2]
      exact hev.fderiv_eq.symm
    have hmain := hCgclose h hh hsupp ε hεpos hε100 hjetn2 u hu (Z u) (hZm9 u hu)
    rw [← hAeq u hu, hAcl] at hmain
    have h2 : ‖Z u - baseState u‖ ≤ Kc * ε := by
      have h1 := hZdist u hu; rwa [dist_eq_norm] at h1
    have h3 : Cg * ‖Z u - baseState u‖ ≤ Cg * (Kc * ε) :=
      mul_le_mul_of_nonneg_left h2 hCgpos.le
    have h4 : Cg * (Kc * ε) + Cg * ε = Cg * (Kc + 1) * ε := by ring
    linarith [hmain, h3, h4]
  -- ## the base identity in the separated form
  have hv0 : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
      (A u) (deriv baseState u) = winRHS n 0 baseState u :=
    winRHS_base n hn A hAeq
  -- ## the pointwise solution of the linearised equation with its bound
  have hVex : ∀ u, u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20) → ∃ v : St,
      (fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u)) v = winRHS n h Z u ∧
      ‖v - deriv baseState u‖ ≤ KK * ε := by
    intro u hu
    have hδs : ‖winRHS n h Z u - winRHS n 0 baseState u‖ ≤ Mrhs * ε :=
      hRdiff h ε hh hεpos hε100 hjet hsupp hKc9 Z hZcont hZdist u hu
    obtain ⟨v, hv1, hv2⟩ := Work.VolterraLong.C1.solve_near_equiv (E := St)
      (A := A u) (J := fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u))
      (B := B) (κ := Cg * (Kc + 1) * ε) (δ := Mrhs * ε)
      hBpos (hAinv u hu) (hJκ u hu) hκB (R := winRHS n h Z u) (R₀ := winRHS n 0 baseState u)
      (v₀ := deriv baseState u) (hv0 u hu) hδs
    refine ⟨v, hv1, ?_⟩
    have hS' := hSbd u hu
    have hκnn : 0 ≤ Cg * (Kc + 1) * ε := by positivity
    have hb1 : Cg * (Kc + 1) * ε * ‖deriv baseState u‖ ≤ Cg * (Kc + 1) * ε * S :=
      mul_le_mul_of_nonneg_left hS' hκnn
    have hb2 : Cg * (Kc + 1) * ε * ‖deriv baseState u‖ + Mrhs * ε ≤
        (Cg * (Kc + 1) * S + Mrhs) * ε := by
      have hb3 : Cg * (Kc + 1) * ε * S + Mrhs * ε = (Cg * (Kc + 1) * S + Mrhs) * ε := by ring
      linarith [hb1, hb3]
    have hb4 := mul_le_mul_of_nonneg_left hb2 (by linarith [hBpos] : (0 : ℝ) ≤ 2 * B)
    have hb5 : 2 * B * ((Cg * (Kc + 1) * S + Mrhs) * ε) = KK * ε := by rw [hKKdef]; ring
    linarith [hv2, hb4, hb5]
  obtain ⟨V, hV1, hV2⟩ : ∃ V : ℝ → St,
      (∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        (fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u)) (V u) = winRHS n h Z u) ∧
      (∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), ‖V u - deriv baseState u‖ ≤ KK * ε) := by
    refine ⟨fun u => if hu : u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20)
        then Classical.choose (hVex u hu) else 0, ?_, ?_⟩
    · intro u hu
      simp only [dif_pos hu]
      exact (Classical.choose_spec (hVex u hu)).1
    · intro u hu
      simp only [dif_pos hu]
      exact (Classical.choose_spec (hVex u hu)).2
  -- ## `deriv Z` solves the linearised equation
  have hderiv := Work.VolterraLong.deriv_from_solution_linearized (E := St)
    (a := (7 / 10 : ℝ)) (b := (19 / 20 : ℝ))
    (G := fun u (z : St) => WinData.Gcl n h u z)
    (Θ := fun u (σ : ℝ) (z : St) => WinData.Tcl n h u σ z)
    (Ξ := fun u : ℝ => WinData.Xcl n h u)
    (Gs := fun u (z : St) => GsCl n h u z)
    (Θs := fun u (σ : ℝ) (z : St) => TsCl n h u σ z)
    (Ξs := fun u : ℝ => XsCl n h u)
    (Z := Z) (V := V) (A := A) (B := B) (κ := Cg * (Kc + 1) * ε)
    (by norm_num) hBpos hAinv hZcont hκB hsol
    (gcl_continuous (n := n) hn hh hsupp hsmall2)
    (tcl_continuous (n := n) hn hh hsupp hsmall2)
    (xcl_continuous (n := n) hn hh hsupp hsmall1)
    (fun u _ z => gsCl_hasDerivAt (n := n) hn hh hsupp hsmall2 u z)
    (gsCl_continuous (n := n) hn hh hsupp hsmall2)
    (fun u _ σ z => tsCl_hasDerivAt (n := n) hn hh hsupp hsmall2 u σ z)
    (tsCl_continuous (n := n) hn hh hsupp hsmall2)
    (fun u => xsCl_hasDerivAt (n := n) hn hh hsupp hsmall1 u)
    (xsCl_continuous (n := n) hn hh hsupp hsmall1)
    (fun u _ => ((gcl_contDiff (n := n) hh hsupp hsmall2).comp
        (contDiff_prodMk_right (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (e₀ := u))).differentiable
        (by simp) |>.differentiableAt)
    hJκ hV1
  -- ## conclusion
  have hmain : ∀ u ∈ Set.Ioo (7 / 10 : ℝ) (19 / 20),
      dist (deriv Z u) (deriv (baseState : ℝ → St) u) ≤ KK * ε := by
    intro u hu
    have huI : u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20) := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hd : HasDerivAt Z (V u) u := (hderiv u huI).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
    rw [hd.deriv, dist_eq_norm]
    exact hV2 u huI
  rcases eq_or_lt_of_le hs.1 with h7 | h7
  · -- the left endpoint: continuity of `deriv Z` and of `deriv baseState`
    subst h7
    haveI : (𝓝[>] (7 / 10 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
    have hZc : ContinuousAt (deriv Z) (7 / 10 : ℝ) :=
      (hZsm.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num))
    have hbc : ContinuousAt (deriv (baseState : ℝ → St)) (7 / 10 : ℝ) := hcd.continuousAt
    have htend : Tendsto (fun u : ℝ => dist (deriv Z u) (deriv (baseState : ℝ → St) u))
        (𝓝[>] (7 / 10 : ℝ))
        (𝓝 (dist (deriv Z (7 / 10)) (deriv (baseState : ℝ → St) (7 / 10)))) :=
      (hZc.tendsto.dist hbc.tendsto).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (7 / 10 : ℝ) < 19 / 20 by norm_num)] with u hu hgt
    exact hmain u ⟨hgt, hu⟩
  · exact hmain s ⟨h7, by linarith [hs.2]⟩

end

end Work.OddVolterra.Existence
