import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.WinData.Basic
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat

/-!
# The clamped data of the odd-case window construction

This file sets up the window `[1/4, 19/20]`, the cut-offs that localise the paper's data
(`Godd`, `Θ`, `Ξ`) to a neighbourhood of the state region where the kernels are smooth, and the
clamped data `Gcl`, `Tcl`, `Xcl` used by the Volterra engine of
`Work.OddVolterra.WinData.window_state_solution`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff

noncomputable section

/-! ## The window and its cut-offs -/

/-- Left end of the window. -/
def wLo : ℝ := 1 / 4

/-- Right end of the window. -/
def wHi : ℝ := 19 / 20

/-- The state ball radius of the window construction. -/
def wRho : ℝ := 1 / 2

/-- The radius of the support of the state cut-off. -/
def wCzR : ℝ := 101 / 200

lemma wLo_pos : 0 < wLo := by norm_num [wLo]
lemma wLo_le_wHi : wLo ≤ wHi := by norm_num [wLo, wHi]
lemma wHi_lt_one : wHi < 1 := by norm_num [wHi]
lemma wRho_pos : 0 < wRho := by norm_num [wRho]
lemma wCzR_pos : 0 < wCzR := by norm_num [wCzR]
lemma wRho_lt_wCzR : wRho < wCzR := by norm_num [wRho, wCzR]
lemma wCzR_lt_half : wCzR ≤ 51 / 100 := by norm_num [wCzR]

/-- The slope cut-off: `C^∞`, equal to `1` on `[1/4, 19/20]` and vanishing off
`(1/4 - 1/100, 19/20 + 1/100)`. -/
def wCs : ContDiffBump (3 / 5 : ℝ) :=
  ⟨7 / 20, 7 / 20 + 1 / 100, by norm_num, by norm_num⟩

/-- The state cut-off: `C^∞` on `St`, equal to `1` on the ball of radius `1/2` and vanishing off
the ball of radius `101/200`. -/
def wCz : ContDiffBump (0 : St) :=
  ⟨wRho, wCzR, wRho_pos, wRho_lt_wCzR⟩

lemma wCs_rIn : wCs.rIn = 7 / 20 := rfl
lemma wCs_rOut : wCs.rOut = 7 / 20 + 1 / 100 := rfl
lemma wCz_rIn : wCz.rIn = wRho := rfl
lemma wCz_rOut : wCz.rOut = wCzR := rfl

lemma wCs_eq_one {s : ℝ} (hs : s ∈ Set.Icc wLo wHi) : (wCs : ℝ → ℝ) s = 1 := by
  refine ContDiffBump.one_of_mem_closedBall wCs ?_
  rw [wCs_rIn, Metric.mem_closedBall, Real.dist_eq]
  rw [abs_le]
  rw [Set.mem_Icc] at hs
  constructor <;> norm_num [wLo, wHi] at hs ⊢ <;> linarith

lemma wCs_nonneg (s : ℝ) : 0 ≤ (wCs : ℝ → ℝ) s := ContDiffBump.nonneg wCs
lemma wCs_le_one (s : ℝ) : (wCs : ℝ → ℝ) s ≤ 1 := ContDiffBump.le_one wCs
lemma wCs_contDiff : ContDiff ℝ (⊤ : ℕ∞) (wCs : ℝ → ℝ) := ContDiffBump.contDiff wCs

lemma wCs_tsupport_subset :
    tsupport (wCs : ℝ → ℝ) ⊆ Set.Icc (1 / 4 - 1 / 100) (19 / 20 + 1 / 100) := by
  rw [ContDiffBump.tsupport_eq, wCs_rOut]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  constructor <;> linarith

lemma wCz_eq_one {z : St} (hz : ‖z‖ ≤ wRho) : (wCz : St → ℝ) z = 1 := by
  refine ContDiffBump.one_of_mem_closedBall wCz ?_
  rwa [wCz_rIn, Metric.mem_closedBall, dist_zero_right]

lemma wCz_eq_zero {z : St} (hz : wCzR ≤ ‖z‖) : (wCz : St → ℝ) z = 0 := by
  refine ContDiffBump.zero_of_le_dist wCz ?_
  rwa [wCz_rOut, dist_zero_right]

lemma wCz_nonneg (z : St) : 0 ≤ (wCz : St → ℝ) z := ContDiffBump.nonneg wCz
lemma wCz_le_one (z : St) : (wCz : St → ℝ) z ≤ 1 := ContDiffBump.le_one wCz
lemma wCz_contDiff : ContDiff ℝ (⊤ : ℕ∞) (wCz : St → ℝ) := ContDiffBump.contDiff wCz

lemma wCz_tsupport_subset :
    tsupport (wCz : St → ℝ) ⊆ Metric.closedBall (0 : St) wCzR := by
  rw [ContDiffBump.tsupport_eq, wCz_rOut]

/-! ## The localising cut-offs of the data -/

/-- The cut-off multiplying the state data. -/
def wChiG (s : ℝ) (z : St) : ℝ := (wCs : ℝ → ℝ) s * (wCz : St → ℝ) (z - baseState s)

/-- The cut-off multiplying the `Θ` data. -/
def wChiT (s σ : ℝ) (z : St) : ℝ :=
  (wCs : ℝ → ℝ) s * (wCs : ℝ → ℝ) σ * (wCz : St → ℝ) (z - baseState σ)

/-- The cut-off multiplying the source. -/
def wChiX (s : ℝ) : ℝ := (wCs : ℝ → ℝ) s

lemma wChiG_eq_one {s : ℝ} (hs : s ∈ Set.Icc wLo wHi) {z : St}
    (hz : ‖z - baseState s‖ ≤ wRho) : wChiG s z = 1 := by
  rw [wChiG, wCs_eq_one hs, wCz_eq_one hz, mul_one]

lemma wChiT_eq_one {s σ : ℝ} (hs : s ∈ Set.Icc wLo wHi) (hσ : σ ∈ Set.Icc wLo wHi)
    {z : St} (hz : ‖z - baseState σ‖ ≤ wRho) : wChiT s σ z = 1 := by
  rw [wChiT, wCs_eq_one hs, wCs_eq_one hσ, wCz_eq_one hz, mul_one, one_mul]

lemma wChiX_eq_one {s : ℝ} (hs : s ∈ Set.Icc wLo wHi) : wChiX s = 1 := wCs_eq_one hs

lemma wChiG_nonneg (s : ℝ) (z : St) : 0 ≤ wChiG s z :=
  mul_nonneg (wCs_nonneg s) (wCz_nonneg _)

lemma wChiG_le_one (s : ℝ) (z : St) : wChiG s z ≤ 1 := by
  rw [wChiG]
  calc (wCs : ℝ → ℝ) s * (wCz : St → ℝ) (z - baseState s) ≤ 1 * 1 :=
        mul_le_mul (wCs_le_one s) (wCz_le_one _) (wCz_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma wChiT_nonneg (s σ : ℝ) (z : St) : 0 ≤ wChiT s σ z :=
  mul_nonneg (mul_nonneg (wCs_nonneg s) (wCs_nonneg σ)) (wCz_nonneg _)

lemma wChiT_le_one (s σ : ℝ) (z : St) : wChiT s σ z ≤ 1 := by
  rw [wChiT]
  have h1 : (wCs : ℝ → ℝ) s * (wCs : ℝ → ℝ) σ ≤ 1 := by
    calc (wCs : ℝ → ℝ) s * (wCs : ℝ → ℝ) σ ≤ 1 * 1 :=
          mul_le_mul (wCs_le_one s) (wCs_le_one σ) (wCs_nonneg σ) (by norm_num)
      _ = 1 := by ring
  calc (wCs : ℝ → ℝ) s * (wCs : ℝ → ℝ) σ * (wCz : St → ℝ) (z - baseState σ) ≤ 1 * 1 :=
        mul_le_mul h1 (wCz_le_one _) (wCz_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma wChiX_nonneg (s : ℝ) : 0 ≤ wChiX s := wCs_nonneg s
lemma wChiX_le_one (s : ℝ) : wChiX s ≤ 1 := wCs_le_one s

/-! ## The explicit diagonal form of `Godd` -/

/-- The explicit diagonal value of the first Abel kernel, as a function of the slope, of the
values `h σ`, `h' σ` and of the chord parameter `t`. -/
def K1d (n : ℕ) (σ hσ hσ' t : ℝ) : ℝ :=
  (Nat.doubleFactorial (2 * n + 1) : ℝ) *
    (-((σ * t + hσ) * (t + hσ'))) ^ (n + 1) /
    Real.sqrt ((t + hσ') * (2 * (σ * t + hσ)))

/-- The explicit diagonal value of the second Abel kernel. -/
def K2d (n : ℕ) (σ hσ hσ' t : ℝ) : ℝ :=
  (Nat.doubleFactorial (2 * n - 1) : ℝ) *
    (-((σ * t + hσ) * (t + hσ'))) ^ n * (t + hσ') /
    Real.sqrt ((t + hσ') * (2 * (σ * t + hσ)))

/-- The explicit diagonal form of the state datum `𝐆`: it depends on the perturbation only
through the two numbers `h s`, `h' s`. -/
def diagForm (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St :=
  ![z 0, z 1,
    Real.pi * (K1d n s (h s) (deriv h s) (-(z 0)) * z 2 +
      K1d n s (h s) (deriv h s) (z 1) * z 3),
    Real.pi * (K2d n s (h s) (deriv h s) (-(z 0)) * z 2 +
      K2d n s (h s) (deriv h s) (z 1) * z 3)]

/-- `diagForm` is the paper's `𝐆`. -/
theorem Godd_eq_diagForm (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) :
    Godd n h s z = diagForm n h s z := by
  rw [Existence.Godd_eq_diag_c]
  ext i
  fin_cases i <;>
    simp [diagForm, K1d, K2d, Existence.K1_eq_K1d_c, Existence.K2_eq_K2d_c,
      Existence.K1d_c, Existence.K2d_c, line, lineSlope]

/-! ## The clamped data of the window construction -/

/-- The clamped state datum: the explicit diagonal form `diagForm`, localised with `wChiG`. -/
def Gcl (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St := wChiG s z • diagForm n h s z

/-- The clamped `Θ` datum: the manifest kernel `KernelExt.ThetaM`, localised with `wChiT`. -/
def Tcl (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  wChiT s σ z • KernelExt.ThetaM n h s σ z

/-- The clamped source: the paper's `Ξ` plus the frozen tail from `19/20` to `1`, localised. -/
def Xcl (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : St :=
  wChiX s • (Xi n h s +
    ∫ σ in wHi..(1 : ℝ), KernelExt.ThetaM n h s σ (baseState σ))

lemma Gcl_eq_Godd {n : ℕ} {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc wLo wHi) {z : St}
    (hz : ‖z - baseState s‖ ≤ wRho) : Gcl n h s z = Godd n h s z := by
  rw [Gcl, wChiG_eq_one hs hz, one_smul, ← Godd_eq_diagForm]

lemma Tcl_eq_ThetaM {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} (hs : s ∈ Set.Icc wLo wHi)
    (hσ : σ ∈ Set.Icc wLo wHi) {z : St} (hz : ‖z - baseState σ‖ ≤ wRho) :
    Tcl n h s σ z = KernelExt.ThetaM n h s σ z := by
  rw [Tcl, wChiT_eq_one hs hσ hz, one_smul]

lemma Xcl_eq {n : ℕ} {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc wLo wHi) :
    Xcl n h s = Xi n h s +
      ∫ σ in wHi..(1 : ℝ), KernelExt.ThetaM n h s σ (baseState σ) := by
  rw [Xcl, wChiX_eq_one hs, one_smul]

end

end Work.OddVolterra.WinData
