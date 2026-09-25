/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Smoothness of the logarithmic chart

This file proves that all the ingredients of the logarithmic chart of
`Work/NN/Final/Chart.lean` (in one coordinate of `ℂⁿ`) are smooth (`C^∞`) as maps of
real normed spaces:

* `chartU ρ i` — the angular coordinate `z i / ‖z i‖`, cut off near `z i = 0`;
* `chartT ρ i` — the logarithmic modulus `log (ρ i / ‖z i‖)`, clamped near `z i = 0`;
* `chartPoint ρ i` — the pair `(u, t)`, i.e. the chart itself;
* `expChart ρ i` — the inverse chart `(x, t) ↦ x[i ↦ ρ i * exp (-t) * x i]`.

The only delicate points are those where `z i = 0`: there the naive expressions `z i / ‖z i‖`
and `log ‖z i‖` are not smooth, but the radial cutoffs `radialStep` used in the definitions
vanish identically on the open ball `{‖z i‖ < ρ i / 8}`, so the composed maps are *constant*
on a neighbourhood of `{z i = 0}` and therefore smooth there as well.
-/
import Mathlib
import Submission.Work.NN.Final.Chart

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Final.ChartSmooth

/-! ## Some general smoothness lemmas -/

/-- The radial step `radialStep a b` is smooth, as a function of its (real) argument. -/
lemma contDiff_radialStep (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.radialStep a b) := by
  unfold Work.NN.Final.radialStep Work.NN.Final.smoothCut
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (b - a))

/-- If `g : E → (ι → α)` is smooth and `v : E → α` is smooth then
`x ↦ Function.update (g x) i (v x)` is smooth. -/
lemma contDiff_update_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [NormedAddCommGroup α] [NormedSpace 𝕜 α] {n : ℕ∞} {g : E → ι → α}
    {v : E → α} (i : ι) (hg : ContDiff 𝕜 n g) (hv : ContDiff 𝕜 n v) :
    ContDiff 𝕜 n (fun x => Function.update (g x) i (v x)) := by
  rw [contDiff_pi]
  intro j
  by_cases hj : j = i
  · subst hj
    simpa only [Function.update_self] using hv
  · have hcomp : (fun x => Function.update (g x) i (v x) j) = fun x => g x j := by
      funext x
      rw [Function.update_apply, ite_eq_right hj]
    rw [hcomp]
    exact (contDiff_pi.mp hg) j

/-! ## The two "core" pieces, smooth away from `0`

Here we isolate the local smoothness statements about functions of a single complex variable.
The cutoff `radialStep a b` is applied to `‖y‖`, and we are away from the exceptional set
`y = 0`, so that the norm (hence also `log ‖y‖` and `y / ‖y‖`) is smooth. -/

/-- Away from `y = 0`, the angular piece `y ↦ radialStep a b ‖y‖ * (y / ‖y‖)` is smooth. -/
lemma contDiffAt_radial_mul_div_norm {a b : ℝ} {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℂ => (Work.NN.Final.radialStep a b ‖y‖ : ℂ) * (y / ((‖y‖ : ℝ) : ℂ))) w := by
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => ‖y‖) w := contDiffAt_norm ℂ hw
  have hstep : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℂ => ((Work.NN.Final.radialStep a b ‖y‖ : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w ((contDiff_radialStep a b).contDiffAt.comp w hnorm)
  have hofR : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => ((‖y‖ : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hnorm
  have hne : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
    simp [norm_ne_zero_iff.mpr hw]
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => (((‖y‖ : ℝ) : ℂ))⁻¹) w := hofR.inv hne
  have hid : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => y) w := contDiffAt_id
  have hmul : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => y * (((‖y‖ : ℝ) : ℂ))⁻¹) w := hid.mul hinv
  simpa [div_eq_mul_inv] using hstep.mul hmul

/-- Away from `y = 0`, the logarithmic piece
`y ↦ (1 - radialStep a b ‖y‖) * log 4 + radialStep a b ‖y‖ * (c - log ‖y‖)` is smooth. -/
lemma contDiffAt_radial_log_norm {a b c : ℝ} {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => (1 - Work.NN.Final.radialStep a b ‖y‖) * Real.log 4
      + Work.NN.Final.radialStep a b ‖y‖ * (c - Real.log ‖y‖)) w := by
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => ‖y‖) w := contDiffAt_norm ℂ hw
  have hstep : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => Work.NN.Final.radialStep a b ‖y‖) w :=
    (contDiff_radialStep a b).contDiffAt.comp w hnorm
  have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => Real.log ‖y‖) w :=
    ((Real.contDiffAt_log (x := ‖w‖)).mpr (norm_ne_zero_iff.mpr hw)).comp w hnorm
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℂ => (1 - Work.NN.Final.radialStep a b ‖y‖) * Real.log 4) w :=
    (contDiffAt_const.sub hstep).mul contDiffAt_const
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℂ => Work.NN.Final.radialStep a b ‖y‖ * (c - Real.log ‖y‖)) w :=
    hstep.mul (contDiffAt_const.sub hlog)
  exact h1.add h2

/-! ## The neighbourhood of `{z i = 0}`

On the open ball `{‖z i‖ < ρ i / 8}` both cutoffs vanish, so the chart coordinates are
*constant* there: `chartU ρ i = 0` and `chartT ρ i = log 4`. -/

lemma eventually_chartU_eq_zero {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i)
    {z : Fin n → ℂ} (hz : z i = 0) : ∀ᶠ w in 𝓝 z, Work.NN.Final.chartU ρ i w = 0 := by
  have hlt : ρ i / 8 < ρ i / 3 := by linarith
  have hcont : Continuous (fun w : Fin n → ℂ => ‖w i‖) := continuous_norm.comp (continuous_apply i)
  have hopen : IsOpen {w : Fin n → ℂ | ‖w i‖ < ρ i / 8} := isOpen_lt hcont continuous_const
  have hmem : z ∈ {w : Fin n → ℂ | ‖w i‖ < ρ i / 8} := by
    show ‖z i‖ < ρ i / 8
    rw [hz, norm_zero]; linarith
  filter_upwards [hopen.mem_nhds hmem] with w hw
  have hstep : Work.NN.Final.radialStep (ρ i / 8) (ρ i / 3) ‖w i‖ = 0 :=
    Work.NN.Final.radialStep_of_le hlt (le_of_lt hw)
  simp [Work.NN.Final.chartU, hstep]

lemma eventually_chartT_eq {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i)
    {z : Fin n → ℂ} (hz : z i = 0) : ∀ᶠ w in 𝓝 z, Work.NN.Final.chartT ρ i w = Real.log 4 := by
  have hlt : ρ i / 8 < ρ i / 4 := by linarith
  have hcont : Continuous (fun w : Fin n → ℂ => ‖w i‖) := continuous_norm.comp (continuous_apply i)
  have hopen : IsOpen {w : Fin n → ℂ | ‖w i‖ < ρ i / 8} := isOpen_lt hcont continuous_const
  have hmem : z ∈ {w : Fin n → ℂ | ‖w i‖ < ρ i / 8} := by
    show ‖z i‖ < ρ i / 8
    rw [hz, norm_zero]; linarith
  filter_upwards [hopen.mem_nhds hmem] with w hw
  have hstep : Work.NN.Final.radialStep (ρ i / 8) (ρ i / 4) ‖w i‖ = 0 :=
    Work.NN.Final.radialStep_of_le hlt (le_of_lt hw)
  simp [Work.NN.Final.chartT, hstep]

/-! ## Smoothness of the four maps -/

theorem contDiff_chartU {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.chartU ρ i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z i = 0
  · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (eventually_chartU_eq_zero hρ hz)
  · have hcore := contDiffAt_radial_mul_div_norm (a := ρ i / 8) (b := ρ i / 3) (w := z i) hz
    have hproj : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin n → ℂ => w i) z :=
      (contDiff_apply ℝ ℂ i).contDiffAt
    show ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin n → ℂ =>
      (Work.NN.Final.radialStep (ρ i / 8) (ρ i / 3) ‖w i‖ : ℂ) * (w i / ((‖w i‖ : ℝ) : ℂ))) z
    exact hcore.comp z hproj

theorem contDiff_chartT {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.chartT ρ i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z i = 0
  · exact (contDiffAt_const (c := Real.log 4)).congr_of_eventuallyEq
      (eventually_chartT_eq hρ hz)
  · have hcore := contDiffAt_radial_log_norm (a := ρ i / 8) (b := ρ i / 4) (c := Real.log (ρ i))
      (w := z i) hz
    have hproj : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin n → ℂ => w i) z :=
      (contDiff_apply ℝ ℂ i).contDiffAt
    show ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin n → ℂ =>
      (1 - Work.NN.Final.radialStep (ρ i / 8) (ρ i / 4) ‖w i‖) * Real.log 4
        + Work.NN.Final.radialStep (ρ i / 8) (ρ i / 4) ‖w i‖
          * (Real.log (ρ i) - Real.log ‖w i‖)) z
    exact hcore.comp z hproj

theorem contDiff_chartPoint {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.chartPoint ρ i) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin n → ℂ => Function.update z i (Work.NN.Final.chartU ρ i z)) :=
    contDiff_update_comp i contDiff_id (contDiff_chartU hρ)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℂ => Work.NN.Final.chartT ρ i z) :=
    contDiff_chartT hρ
  show ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℂ =>
    (Function.update z i (Work.NN.Final.chartU ρ i z), Work.NN.Final.chartT ρ i z))
  exact h1.prodMk h2

theorem contDiff_expChart {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} :
    ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.expChart ρ i) := by
  have hexp : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin n → ℂ) × ℝ => Complex.exp (-(p.2))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp contDiff_snd).neg
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin n → ℂ) × ℝ => (ρ i : ℂ) * Complex.exp (-(p.2)) * p.1 i) :=
    ((contDiff_const (c := (ρ i : ℂ))).mul hexp).mul
      ((contDiff_apply ℝ ℂ i).comp contDiff_fst)
  show ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℂ) × ℝ =>
    Function.update p.1 i ((ρ i : ℂ) * Complex.exp (-(p.2)) * p.1 i))
  exact contDiff_update_comp i contDiff_fst hv

theorem contDiff_chart {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.chartPoint ρ i)
      ∧ ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.expChart ρ i) ∧
      ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.chartU ρ i)
      ∧ ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.chartT ρ i) :=
  ⟨contDiff_chartPoint hρ, contDiff_expChart, contDiff_chartU hρ, contDiff_chartT hρ⟩

end Work.NN.Final.ChartSmooth
