import Mathlib
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddVolterra.WinData.win_data

/-!
# The estimate interface for the `C¹`-closeness of the odd window solution

`Work.OddVolterra.Existence.window_C1_state` is proved from the estimate interface collected
here: the uniformity-in-`h` bounds for the *clamped* data `Gcl`, `Tcl`, `Xcl` of the odd window
construction (values, first-slot derivatives, and Lipschitz constants in the state), the
`z`-derivative closeness of the clamped state datum on the unit ball, and the clamped base
identity together with its `s`-derivative.

Every field is proved elsewhere in `Submission/Work/OddVolterra/`; this module only *names* the
interface so that the assembly can be stated and proved independently.

**Provenance of the fields** (all in this workspace, all sorry-free unless noted):

* `Tval` — `Work.OddVolterra.WinData.thetaM_close_box` (proved) + the transfer
  `WinData.Tcl_eq_ThetaM` (the `wChiT` cut-off is `1` on `[1/4,19/20]² × ball(9/20)`);
* `Tlip`, `Tbnd` — `Work.OddVolterra.WinData.thetaM_state_lipschitz_ext` + the same transfer
  (boundedness uses `wChiT_le_one`);
* `Tder`, `Tderlip` — `Work.OddVolterra.WinData.thetaM_deriv_close_ext` + the product rule for
  `Tcl = wChiT • ThetaM` (the cut-off is `h`-independent, so its derivative difference only meets
  the already-bounded `ThetaM` defect);
* `Sval` — `Work.Anchor.Xi_close` / `Work.OddVolterra.WinData.Xi_close_modulus` for the `Xi`
  part plus `thetaM_close_box` integrated over `σ ∈ [19/20,1]` for the frozen tail;
* `Sder` — `Work.OddVolterra.WinData.xi_deriv_close` plus the same integral for the tail, where
  the `s`-derivative of the frozen tail is `∫_{19/20}^1 ∂_s ThetaM` and is controlled by
  `thetaM_deriv_close_ext` (whose `σ`-range is `[1/4,1]`);
* `Gval`, `Gder`, `Gderlip` — `Work.OddVolterra.WinData.gcl_deriv_close` (proved);
* `hder` — `Work.OddVolterra.WinData.clamped_hder_unit` (proved);
* `hbase` — `Work.OddVolterra.WinData.clamped_base_identity` (proved).

The assembly that consumes this interface is sketched in the workspace file `_c1_asm.lean`
(a scratch file, not part of the build): it runs the `C⁰` long-interval engine
`Work.OddCurveB.Engine.volterra_long_exists_ball` on `[1/4,19/20]` with the clamped data and
state-ball radius `9/20` to obtain a solution `Ze` with `dist (Ze s) (baseState s) ≤ 2 B M EE ε`,
identifies it with the given `Z` by `Work.VolterraLong.GronwallUnique` (both solve the same
clamped system), and then applies `Work.VolterraLong.deriv_from_equation_eps` with the pointwise
solution of the linearised equation produced by `Work.VolterraLong.C1.solve_near_equiv` and the
`R - R₀` bound `Work.OddVolterra.Existence.data_diff_bound_r` (which is proved in
`Existence/window_C1_state.lean`, a parameterised copy of `Work.VolterraLong.C1.data_diff_bound`
with the state ball of radius `ρ`).
-/

set_option maxHeartbeats 4000000

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence.C1Bounds

open Work.OddVolterra
open Work.OddVolterra.Existence

noncomputable section

structure Est (n : ℕ) where
  Cb : ℝ
  Lb : ℝ
  hCb : 0 < Cb
  hLb : 0 < Lb
  Tval : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖WinData.Tcl n h s σ z - WinData.Tcl n 0 s σ z‖ ≤ Cb * δ
  Tlip : ∀ (h : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖WinData.Tcl n h s σ z - WinData.Tcl n h s σ z'‖ ≤ Lb * ‖z - z'‖
  Tbnd : ∀ (h : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖WinData.Tcl n h s σ z‖ ≤ Cb
  Tder : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖deriv (fun u : ℝ => WinData.Tcl n h u σ z) s -
          deriv (fun u : ℝ => WinData.Tcl n 0 u σ z) s‖ ≤ Cb * δ
  Tderlip : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖deriv (fun u : ℝ => WinData.Tcl n h u σ z) s -
          deriv (fun u : ℝ => WinData.Tcl n h u σ z') s‖ ≤ Lb * ‖z - z'‖
  Sval : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ‖WinData.Xcl n h s - WinData.Xcl n 0 s‖ ≤ Cb * δ
  Sder : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        ‖deriv (fun u : ℝ => WinData.Xcl n h u) s -
          deriv (fun u : ℝ => WinData.Xcl n 0 u) s‖ ≤ Cb * δ
  Gval : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ z ∈ Metric.closedBall (baseState s) (9 / 20),
        ‖WinData.Gcl n h s z - WinData.Gcl n 0 s z‖ ≤ Cb * δ
  Gder : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ z ∈ Metric.closedBall (baseState s) (9 / 20),
        ‖deriv (fun u : ℝ => WinData.Gcl n h u z) s -
          deriv (fun u : ℝ => WinData.Gcl n 0 u z) s‖ ≤ Cb * δ
  Gderlip : ∀ (h : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ z ∈ Metric.closedBall (baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState s) (9 / 20),
        ‖deriv (fun u : ℝ => WinData.Gcl n h u z) s -
          deriv (fun u : ℝ => WinData.Gcl n h u z') s‖ ≤ Lb * ‖z - z'‖
  hder : ∃ Cg : ℝ, 0 < Cg ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ z ∈ Metric.closedBall (baseState s) 1,
        ‖fderiv ℝ (fun w => WinData.Gcl n h s w) z -
          fderiv ℝ (fun w => WinData.Gcl n 0 s w) (baseState s)‖
          ≤ Cg * ‖z - baseState s‖ + Cg * δ
  hbase : (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      WinData.Gcl n 0 s (baseState s) =
        (∫ σ in s..(19 / 20 : ℝ), WinData.Tcl n 0 s σ (baseState σ)) + WinData.Xcl n 0 s) ∧
    (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      deriv (fun u => WinData.Gcl n 0 u (baseState s)) s +
        fderiv ℝ (fun z => WinData.Gcl n 0 s z) (baseState s) (deriv baseState s)
      = - WinData.Tcl n 0 s s (baseState s) +
        (∫ σ in s..(19 / 20 : ℝ),
          deriv (fun u => WinData.Tcl n 0 u σ (baseState σ)) s) +
        deriv (fun u => WinData.Xcl n 0 u) s)
end

end Work.OddVolterra.Existence.C1Bounds
