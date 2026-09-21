import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# The data of the odd transition-slope window (`odd_volterra_window2`)

This file sets up the *modified* data used to prove
`Work.OddVolterra.Existence.odd_volterra_window2`.

The raw odd data (`Godd`, `Theta`, `Xi` of `Work.OddVolterra.Defs`) is not regular enough for the
long-interval fixed-point engine `Work.VolterraLong.volterra_long_exists_bump`: the Abel kernel
`Kvec` is discontinuous at the diagonal and strongly singular where the radicand `Kden` vanishes,
the source `Xi` is only regular on compacts, and the state-differentiability of `Godd` fails where
`line h s t * lineSlope h s t = 0`.

The remedy, following the `Work.OddVolterra.KernelExt` chapter, is

* to use the *manifest* smooth representative `KvecM`/`G2M`/`GoddM`/`ThetaM` of the kernels
  (which agrees with the paper's kernel on the triangle `s ≤ σ` where the radicand is positive),
  and
* to localise everything to the window `[1 - 3τ, 1 - τ/2] = [7/10, 19/20]` by an explicit smooth
  cutoff, so that all data becomes smooth with compact support.

On the window of use the modified data coincides with the paper's data, so a solution of the
modified system is a solution of the paper's system on the window.

## How this file is meant to be used

The state-level window statement `Work.OddVolterra.Existence.odd_volterra_window2` is obtained from
two ingredients:

1. **The window core.**  A solution `Z` on `[wA, wC]` of the *truncated* system
   `Godd n h s (Z s) = ∫_s^{wC} Θ n h s σ (Z σ) dσ + Xi n h s + ∫_{wC}^{1} Θ n h s σ (baseState σ) dσ`
   which stays `1/100`-close to `baseState` and equals `baseState` at `wC`.  This is the paper's
   Step 2, obtained from the long-interval fixed point engine
   `Work.VolterraLong.volterra_long_exists_bump` applied to the **modified data** `GoddW`, `ThetaW`,
   `XiW` defined below, with base solution `baseState` and interval `[wA, wC]`.

   The hypotheses of that engine are, for the modified data:

   * global continuity of `GoddW n h`, `ThetaW n h`, `XiW n h` and of `ThetaW n 0` — automatic for
     smooth compactly supported functions;
   * Lipschitz-in-state and differentiability in the state — automatic from smoothness with compact
     support (`ContDiff.lipschitzWith_of_hasCompactSupport`);
   * the base identity `GoddW n 0 s (baseState s) = ∫_s^{wC} ThetaW n 0 s σ (baseState σ) dσ + XiW n 0 s`
     — this is `Work.OddVolterra.Existence.base_volterra_on_Ioo` (the unperturbed identity with
     upper limit `1`) combined with the splitting `∫_s^1 = ∫_s^{wC} + ∫_{wC}^1` (the cutoff is `1`
     on the window, and `wC < 1`);
   * the linearisation `A s = fderiv (GoddW n 0 s) (baseState s)` with a uniform bound on `‖A s⁻¹‖`
     — since the cutoff is `1` near `baseState s` this is the linearisation of the *true* `Godd n 0`,
     and is what `Work.OddVolterra.Existence.odd_linearization` provides;
   * the `C^{n+2}`-closeness of the modified data to the base data — the diagonal (`Godd`) part is
     `Work.OddVolterra.Existence.data_close_of_small`, the `Θ` part uses the agreement of `ThetaM`
     with the true `Theta` for `σ > s` (`Work.OddVolterra.KernelExt.KvecM_eq_Kvec`,
     `Work.OddVolterra.Existence.deriv_G2_apply_eq_integral`).

   The two facts that make this work are

   * `Work.OddVolterra.KernelExt.KvecM_eq_Kvec`: on the triangle `s ≤ σ` with positive radicands the
     manifest kernel equals the paper's kernel — so on the region of use the modified data is the
     paper's data, up to the single point `σ = s` (measure zero for the `σ`-integral);
   * `Work.OddVolterra.KernelExt.JM_diag`: on the diagonal the two kernels agree, so
     `GoddW n h s z = Godd n h s z` whenever the cutoff equals `1`.

   The endpoint value `Z wC = baseState wC` follows from the equation at `s = wC` (rows `0,1` fix the
   first two components, rows `2,3` are an invertible `2 × 2` system) together with the fact that
   `h` vanishes in a *neighbourhood* of `wC > 1 - τ = 9/10`, so that the perturbed data equals the
   unperturbed data there (`Work.OddVolterra.Existence.data_eq_zero_of_eventuallyEq_zero`), and the
   injectivity modulus `Work.OddVolterra.Existence.godd_injective_modulus_state_ball`.

2. **The tail.**  On `s > 9/10 = 1 - τ` the bump vanishes in a neighbourhood of the relevant
   arguments, so the perturbed system and the unperturbed system have the same data; by uniqueness
   (`Work.OddVolterra.Existence.eqOn_of_solves`) the glued curve agrees with `baseState` on
   `[9/10, 1]`.  Then `∫_s^{wC} + ∫_{wC}^{1} = ∫_s^{1}` gives the statement's equation.

## Workspace hygiene warning (duplicate names)

Two modules of this workspace both define the auxiliary name
`Work.OddVolterra.Existence.h_eq_zero_of_lt`:

* `Submission.Work.OddVolterra.Existence.theta_integrable` (and hence everything importing it,
  such as `...Existence.base_volterra` and `...Existence.base_volterra_on_Ioo`),
* `Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball` (and hence everything
  importing it, such as `...Existence.K1d_K2d_bounds` and `...Existence.glue_local_solutions`).

Importing one module from each side makes the environment inconsistent and the build fails.  A file
that needs both the unperturbed identity (from the first side) and the state injectivity modulus
(from the second side) must therefore either re-prove the needed fact on its own, or avoid one of
the imports.

## Known failure modes (do not rediscover)

* the `σ`-integral of the statement may not be extended to `1` for `s > 1 - τ/2` with the *raw*
  data, because the unperturbed identity fails at `s = 1`;
* `Work.OddVolterra.Kvec` is discontinuous at the diagonal and `Work.OddVolterra.Theta` is
  discontinuous where a radicand vanishes, so the fixed point engine cannot be fed the raw data;
* the state-differentiability of the raw `Godd` fails where `line h s t * lineSlope h s t = 0`
  (the cutoff keeps the state away from that set).

## The constants

`wA = 1 - 3τ = 7/10`, `wB = 1 - τ = 9/10` (the right end of the statement's window),
`wC = 1 - τ/2 = 19/20` (the splice point, strictly between `wB` and `1`).

## The cutoff

`cs` is a `C^∞` bump on `ℝ` with centre `wCenter = 33/40`, inner radius `3/20` and outer radius
`4/25`; `cz` is a `C^∞` bump on `ℝ` with centre `0`, inner radius `1/2500` and outer radius `4/25`,
applied to the squared Euclidean distance `wsq σ z = Σ_i (z i - baseState σ i)²` (the squared
distance, rather than the sup norm, so that the cut-off is smooth — the sup norm of `St` is not
differentiable at points where two coordinates tie).
The outer radius of `cs` is kept below `1 - wCenter = 7/40`, so that the support of `cs` — and hence
that of `XiW` — stays strictly inside `(0, 1)`, where the source `Xi` is continuous.
Thus `cs s = 1` for `|s - 33/40| ≤ 3/20` (in particular on all of `[7/10, 19/20]`) and
`cz (‖z - baseState σ‖) = 1` for `‖z - baseState σ‖ ≤ 1/5`.
-/

namespace Work.OddVolterra.Existence

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Constants -/

/-- The centre of the cutoff windows. -/
def wCenter : ℝ := 33 / 40

/-- The left end of the window: `1 - 3τ`. -/
def wA : ℝ := 7 / 10

/-- The right end of the statement's window: `1 - τ`. -/
def wB : ℝ := 9 / 10

/-- The splice point `1 - τ/2`, strictly between `wB` and `1`. -/
def wC : ℝ := 19 / 20

lemma wA_eq : wA = 1 - 3 * tau := by norm_num [wA, tau]
lemma wB_eq : wB = 1 - tau := by norm_num [wB, tau]
lemma wC_eq : wC = 1 - tau / 2 := by norm_num [wC, tau]
lemma wA_pos : 0 < wA := by norm_num [wA]
lemma wA_le_wB : wA ≤ wB := by norm_num [wA, wB]
lemma wB_lt_wC : wB < wC := by norm_num [wB, wC]
lemma wB_lt_one : wB < 1 := by norm_num [wB]
lemma wC_lt_one : wC < 1 := by norm_num [wC]

/-! ## The cutoffs -/

-- The outer radius of `cs` is chosen so that its support `(0.665, 0.985)` stays strictly below
-- `1`: the source `Xi` is only continuous on compacts inside `(0, 1)`
-- (`Qtilde n h s = -Q(1)/√(1-s) + …` blows up at `s = 1⁻` when `Q 1 ≠ 0`).
/-- The bump in the slope variables: `= 1` on `|s - 33/40| ≤ 3/20`, supported in
`|s - 33/40| < 4/25` (in particular strictly below `1`). -/
def cs : ContDiffBump wCenter := ⟨3 / 20, 4 / 25, by norm_num, by norm_num⟩

-- The state variable enters through the *sum of squares* `Σ_i (z i - baseState σ i)²` rather
-- than through the sup norm `‖z - baseState σ‖`: the sup norm is not differentiable at "tie"
-- points of `St = Fin 4 → ℝ`, and the fixed-point engine asks for the state-differentiability of
-- the (cut-off) data on the whole ball of radius `1`.
/-- The squared Euclidean distance between the state `z` and `baseState σ` (a polynomial, hence
smooth, in `(σ, z)`). -/
def wsq (σ : ℝ) (z : St) : ℝ := ∑ i : Fin 4, (z i - baseState σ i) ^ 2

/-- The bump in the state variable, applied to the squared distance `wsq σ z`: `= 1` on
`wsq σ z ≤ 1/2500` (which contains every state within sup-distance `1/100` of `baseState σ`). -/
def cz : ContDiffBump (0 : ℝ) := ⟨1 / 2500, 4 / 25, by norm_num, by norm_num⟩

lemma cs_rIn : cs.rIn = 3 / 20 := rfl
lemma cs_rOut : cs.rOut = 4 / 25 := rfl
lemma cz_rIn : cz.rIn = 1 / 2500 := rfl
lemma cz_rOut : cz.rOut = 4 / 25 := rfl

lemma cs_one {s : ℝ} (hs : |s - wCenter| ≤ 3 / 20) : (cs : ℝ → ℝ) s = 1 := by
  refine ContDiffBump.one_of_mem_closedBall cs ?_
  rw [cs_rIn, Metric.mem_closedBall, Real.dist_eq]
  simpa [wCenter] using hs

lemma cz_one {w : ℝ} (hw : |w| ≤ 1 / 2500) : (cz : ℝ → ℝ) w = 1 := by
  refine ContDiffBump.one_of_mem_closedBall cz ?_
  rw [cz_rIn, Metric.mem_closedBall, Real.dist_eq]
  simpa using hw

lemma cs_zero {s : ℝ} (hs : 4 / 25 ≤ |s - wCenter|) : (cs : ℝ → ℝ) s = 0 := by
  refine ContDiffBump.zero_of_le_dist cs ?_
  rw [cs_rOut, Real.dist_eq]
  simpa [wCenter] using hs

lemma cz_zero {w : ℝ} (hw : 4 / 25 ≤ |w|) : (cz : ℝ → ℝ) w = 0 := by
  refine ContDiffBump.zero_of_le_dist cz ?_
  rw [cz_rOut, Real.dist_eq]
  simpa using hw

lemma cs_nonneg (s : ℝ) : 0 ≤ (cs : ℝ → ℝ) s := ContDiffBump.nonneg cs

lemma cs_le_one (s : ℝ) : (cs : ℝ → ℝ) s ≤ 1 := ContDiffBump.le_one cs

lemma cz_nonneg (w : ℝ) : 0 ≤ (cz : ℝ → ℝ) w := ContDiffBump.nonneg cz

lemma cz_le_one (w : ℝ) : (cz : ℝ → ℝ) w ≤ 1 := ContDiffBump.le_one cz

/-! ## The modified data -/

/-- The cutoff multiplying the state data. -/
def chiG (s : ℝ) (z : St) : ℝ := (cs : ℝ → ℝ) s * (cz : ℝ → ℝ) (wsq s z)

/-- The cutoff multiplying the `Θ` data. -/
def chiT (s σ : ℝ) (z : St) : ℝ :=
  (cs : ℝ → ℝ) s * (cs : ℝ → ℝ) σ * (cz : ℝ → ℝ) (wsq σ z)

/-- The modified state data: the manifest representative `GoddM`, cut off to the window. -/
def GoddW (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St :=
  chiG s z • Work.OddVolterra.KernelExt.GoddM n h s z

/-- The modified `Θ` data: the manifest representative `ThetaM`, cut off to the window. -/
def ThetaW (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  chiT s σ z • Work.OddVolterra.KernelExt.ThetaM n h s σ z

/-- The modified source: the paper's `Ξ` plus the frozen tail integral from `wC` to `1`,
cut off to the window. -/
def XiW (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : St :=
  (cs : ℝ → ℝ) s •
    (Work.OddVolterra.Xi n h s +
      ∫ σ in wC..(1 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ (baseState σ))

/-! ## The boxes on which the data is regular -/

/-- The box for the state data. -/
def w2BoxG : Set (ℝ × St) :=
  {p | |p.1 - wCenter| < 3 / 10 ∧ ‖p.2 - baseState p.1‖ < 5 / 12}

/-- The box for the `Θ` data. -/
def w2BoxT : Set ((ℝ × ℝ) × St) :=
  {p | |p.1.1 - wCenter| < 3 / 10 ∧ |p.1.2 - wCenter| < 3 / 10 ∧
        ‖p.2 - baseState p.1.2‖ < 5 / 12}

/-- The `C¹` smallness of the bump used for the positivity of the kernel radicands. -/
def w2Small (h : ℝ → ℝ) : Prop := ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100

/-! ## Elementary consequences of the cutoffs -/

lemma wsq_nonneg (σ : ℝ) (z : St) : 0 ≤ wsq σ z :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

lemma wsq_le_of_sup_le {σ : ℝ} {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 100) :
    wsq σ z ≤ 1 / 2500 := by
  have h1 : ∀ i : Fin 4, |z i - baseState σ i| ≤ 1 / 100 := by
    intro i
    have := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply] at this
    have h2 : ‖z - baseState σ‖ ≤ 1 / 100 := hz
    rw [Real.norm_eq_abs] at this
    linarith
  have h2 : wsq σ z ≤ ∑ _i : Fin 4, (1 / 100 : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := h1 i
    nlinarith [abs_nonneg (z i - baseState σ i), sq_nonneg (z i - baseState σ i),
      abs_le.mp this |>.1, abs_le.mp this |>.2]
  calc wsq σ z ≤ ∑ _i : Fin 4, (1 / 100 : ℝ) ^ 2 := h2
    _ = 1 / 2500 := by norm_num

lemma chiG_eq_one {s : ℝ} (hs : |s - wCenter| ≤ 3 / 20) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 100) : chiG s z = 1 := by
  rw [chiG, cs_one hs, cz_one (w := wsq s z) (by
    rw [abs_of_nonneg (wsq_nonneg s z)]
    exact wsq_le_of_sup_le hz), one_mul]

lemma chiT_eq_one {s σ : ℝ} (hs : |s - wCenter| ≤ 3 / 20) (hσ : |σ - wCenter| ≤ 3 / 20)
    {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 100) : chiT s σ z = 1 := by
  rw [chiT, cs_one hs, cs_one hσ, cz_one (w := wsq σ z) (by
    rw [abs_of_nonneg (wsq_nonneg σ z)]
    exact wsq_le_of_sup_le hz)]
  ring

lemma abs_sub_wCenter_le_of_mem_window {s : ℝ} (hs : s ∈ Set.Icc wA wB) :
    |s - wCenter| ≤ 3 / 20 := by
  rw [abs_le]
  dsimp only [wA, wB, wCenter] at hs ⊢
  constructor
  · linarith [hs.1]
  · linarith [hs.2]

end

end Work.OddVolterra.Existence
