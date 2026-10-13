/-
# `Work.FTS_LocDatum3a.FM_jet8safe`

The `D_z`-jets of the fundamental-model profile `F_*(z) = 2z/(1+z)²` decay like `1/z` at
infinity, uniformly for the orders `j ≤ 8`:

  `∃ C > 0, ∀ j ≤ 8, ∀ z ≥ 1, ∀ θ, |D_z^j F_*(z)| ≤ C/z`,   `D_z = z ∂_z`.

## Why this file does not import the existing order-`8` proof

The delivered proof (`Submission/Work/FTS_LocDatum3a/FM_Fstar_jet_le8.lean`) rests on
`Submission.Work.FTS.LocData.FstarAux` (via `LocData/hasDerivAt_Gker` and
`LocData/DzIter_FM_Fstar_abs_le`), which defines a **second**
`Work.FTS.LocData.T1`, colliding in the environment with the `T1` of
`Work.FTS.LocData.DzIter_bumpZ_bound` (already in the import cone of this file through
`LocDataExt.Majorant5`).  So the content is reproduced here instead: the closed form

  `Gk k z = 2·(-1)^k·k!·(z - k)/(1+z)^(k+2)`

of the `k`-th plain derivative is defined **locally** (namespace `LocFM8s`) and its one-step
recursion `deriv (Gk k) = Gk (k+1)` is proved by the same quotient-rule computation.

## The route

The `θ`-variable of the profile is a dummy, so `D_z^b` acts through the one-variable operator
`T1 = z ∂_z`.  The Stirling expansion

  `D_z^b φ = ∑_{k≤b} S(b,k) z^k ∂_z^k φ`   (`Work.Spaces.DzIter_eq_sum_scoef`),

the closed form `∂_z^k F_* = Gk k` and the far-field bound `|z^k Gk k z| ≤ 2·k!·(k+1)/z`
(for `z ≥ 1`, **every** `k`) give, through `Work.Spaces.abs_sum_scoef_mul_le`,

  `|D_z^b F_*(z)| ≤ bell b · 2·b!·(b+1)/z   (z ≥ 1)`.

For `j ≤ 8`, `bell j ≤ 9000` (in fact `B_8 = 4140`), `j! ≤ 8!` and `j+1 ≤ 9`, so the single
constant `9000·2·8!·9 = 6531840000` absorbs the order dependence.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocDataExt.FMJet5
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/- The auxiliary lemmas of the jet bound, in their own namespace so that the *local* copy of
`Gker` cannot be confused with the (unimportable) `Work.FTS.LocData.Gker`. -/
namespace LocFM8s

set_option maxHeartbeats 1600000

/-! ## The local closed forms of the iterated derivatives -/

/-- **The closed form of the `k`-th derivative of the profile** `F_* (z) = 2z/(1+z)²`:

  `Gk k z = 2·(-1)^k·k!·(z - k)/(1+z)^(k+2)`.

For `k = 0` this is `F_*` itself; in general `deriv^[k] F_* = Gk k` off `z = -1`.  This is a
*local* copy of `Work.FTS.LocData.Gker`, which lives in the unimportable `FstarAux`. -/
noncomputable def Gk (k : ℕ) (z : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2)

@[simp] theorem Gk_apply (k : ℕ) (z : ℝ) :
    Gk k z = 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2) := rfl

/-- `Gk 0` is the profile itself. -/
theorem Gk_zero (z : ℝ) : Gk 0 z = Work.FM.Fstar z := by
  simp only [Gk_apply, Work.FM.Fstar]
  norm_num

/-- **The one-step recursion `deriv (Gk k) = Gk (k+1)` off the pole `z = -1`**, by the
quotient/product rule on `(2·(-1)^k·k!·(z-k)) / (1+z)^(k+2)`. -/
theorem hasDerivAt_Gk (k : ℕ) (z : ℝ) (hz : 1 + z ≠ 0) :
    HasDerivAt (Gk k) (Gk (k + 1) z) z := by
  -- derivative of the numerator `2·(-1)^k·k!·(w - k)`
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1:ℝ)^k * (k.factorial:ℝ) * (w - k))
      (2 * (-1:ℝ)^k * (k.factorial:ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - (k:ℝ)) 1 z := by
      simpa using (hasDerivAt_id z).sub_const (k:ℝ)
    have h2 := h.const_mul (2 * (-1:ℝ)^k * (k.factorial:ℝ))
    simpa using h2
  -- derivative of the denominator `(1 + w)^(k+2)`
  have hden2 : HasDerivAt (fun w : ℝ => (1 + w) ^ (k + 2))
      (((k+2 : ℕ) : ℝ) * (1+z)^(k+1)) z := by
    have h : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h2 := h.pow (k+2)
    rw [show (fun w : ℝ => (1 + w) ^ (k + 2)) = (fun w : ℝ => 1 + w) ^ (k+2) from by
          funext w; simp [Pi.pow_apply]]
    simpa using h2
  have hden : (1+z)^(k+2) ≠ 0 := pow_ne_zero _ hz
  have hdiv := hnum.div hden2 hden
  -- the value produced by the quotient rule is `Gk (k+1) z`
  have hval : (2 * (-1:ℝ)^k * (k.factorial:ℝ) * (1+z)^(k+2)
        - 2 * (-1:ℝ)^k * (k.factorial:ℝ) * (z - k) * (((k+2:ℕ):ℝ) * (1+z)^(k+1)))
        / ((1+z)^(k+2))^2 = Gk (k+1) z := by
    rw [Gk_apply]
    rw [show (k+1)+2 = k+3 by omega]
    -- rewrite every power of `1 + z` through `(1+z)^(k+1)`
    have h1 : (1 + z) ^ (k + 2) = (1 + z) ^ (k + 1) * (1 + z) := by
      rw [show k + 2 = (k+1) + 1 by omega, pow_succ]
    have h2 : (1 + z) ^ (k + 3) = (1 + z) ^ (k + 1) * (1 + z) ^ 2 := by
      rw [show k + 3 = (k+1) + 2 by omega, pow_add]
    have h3 : ((1 + z) ^ (k + 2)) ^ 2 = ((1 + z) ^ (k + 1)) ^ 2 * (1 + z) ^ 2 := by
      rw [h1, mul_pow]
    rw [h3, h1, h2]
    have hu : (1+z)^(k+1) ≠ 0 := pow_ne_zero _ hz
    have ht : (1+z) ≠ 0 := hz
    field_simp
    rw [show (-1:ℝ)^(k+1) = -(-1)^k by rw [pow_succ]; ring]
    rw [show ((k+1).factorial : ℝ) = ((k:ℝ)+1) * (k.factorial:ℝ) by
          rw [Nat.factorial_succ]; push_cast; ring]
    push_cast
    ring
  exact hdiv.congr_deriv hval

/-! ## The `θ`-variable is a dummy -/

/-- For a function of `z` alone, every `D_z`-iterate is independent of `θ`. -/
theorem DzIter_zonly_theta_indep (Φ : ℝ → ℝ) (b : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter b (fun z _ => Φ z) z θ = Work.Spaces.DzIter b (fun z _ => Φ z) z θ' := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ)
          = (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ') from
        funext fun z' => ih z']

/-- The iterated plain derivative of a function of `z` alone, as a `pzIter`. -/
theorem pzIter_zonly_eq_deriv_iter (Φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Φ z) z θ = deriv^[k] Φ z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      congr 1
      funext z'
      exact ih z'

/-! ## The closed forms of the iterated derivatives -/

/-- **The `k`-th plain derivative of the profile is `Gk k`**: the one-step recursion
`deriv (Gk k) = Gk (k+1)` started at `Gk 0 = F_*`. -/
theorem deriv_iter_Fstar_eq_Gk :
    ∀ k : ℕ, ∀ z ∈ Set.Ioi (-1),
      deriv^[k] (fun z => Work.FM.Fstar z) z = Gk k z := by
  intro k
  induction k with
  | zero => intro z _; exact (Gk_zero z).symm
  | succ k ih =>
      intro z hz
      have hlt : (-1 : ℝ) < z := hz
      have hev : (fun w => deriv^[k] (fun z => Work.FM.Fstar z) w)
          =ᶠ[𝓝 z] Gk k := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih w hw
      rw [Function.iterate_succ_apply', Filter.EventuallyEq.deriv_eq hev]
      exact (hasDerivAt_Gk k z (by linarith)).deriv

/-- The `pzIter` of the profile is the closed form `Gk`. -/
theorem pzIter_Fstar_eq_Gk (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z θ = Gk k z := by
  rw [pzIter_zonly_eq_deriv_iter]
  exact deriv_iter_Fstar_eq_Gk k z hz

/-- The `z`-slices of the profile are smooth on `(-1,∞)` (the only pole of `2z/(1+z)²` is
`z = -1`).  This is the smoothness hypothesis of `DzIter_eq_sum_scoef`. -/
theorem contDiffOn_Fstar : ContDiffOn ℝ ⊤ (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hne : ∀ z : ℝ, z ∈ Set.Ioi (-1) → (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hlt : (-1 : ℝ) < z := hz
    exact pow_ne_zero 2 (by linarith)
  refine (hnum.div hden hne).congr ?_
  intro z _
  simp only [Pi.div_apply, Work.FM.Fstar]

/-! ## The far-field decay of the closed forms -/

/-- **The far-field decay of `z^k·Gk k z`, at every order `k`.**  For `z ≥ 1` and all `k`,

  `|z^k · Gk k z| ≤ 2·k!·(k+1)/z`.

Since `Gk k z = 2(-1)^k k!(z-k)/(1+z)^(k+2)` and `(1+z)^(k+2) ≥ z^(k+2)`, while
`|z - k| ≤ (k+1)z` for `z ≥ 1`, this is immediate arithmetic. -/
theorem abs_zpow_mul_Gk_le_all (k : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |z ^ k * Gk k z| ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hzpow : (0 : ℝ) ≤ z ^ k := pow_nonneg hz0.le k
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos hz1 _
  have hkR : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * z := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [hz]
  have hsign : z ^ k * Gk k z =
      (-1 : ℝ) ^ k * (2 * (k.factorial : ℝ) * z ^ k * (z - (k : ℝ)) / (1 + z) ^ (k + 2)) := by
    rw [Gk_apply]
    ring
  rw [hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_of_nonneg hfac,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hzpow]
  have step1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2) := by
    gcongr
  have step2 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
    rw [div_le_div_iff₀ hden hz0]
    have h1 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) * z
        = 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) * z ^ (k + 2) := by
      rw [pow_add]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.le (by linarith) (k + 2))
      (by positivity)
  linarith

/-! ## The far-field bound for every `D_z`-iterate of the profile -/

/-- **The far-field bound for every `D_z`-iterate of the profile.**  For `z ≥ 1` and every
order `b`,

  `|D_z^b F_*(z)| ≤ bell b · 2·b!·(b+1)/z`.

This is `DzIter_eq_sum_scoef` (`D_z^b φ = ∑_{k≤b} S(b,k) z^k ∂_z^k φ`), the identification
`∂_z^k φ = Gk k` of `pzIter_Fstar_eq_Gk`, and the coefficient bound of
`abs_sum_scoef_mul_le` applied to `abs_zpow_mul_Gk_le_all`. -/
theorem DzIter_Fstar_le (b : ℕ) {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ|
      ≤ (Work.Spaces.bell b : ℝ) * (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z) := by
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hsm : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ ⊤
      (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun θ _ => contDiffOn_Fstar
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_rfl, by positivity⟩
  rw [DzIter_zonly_theta_indep (fun z => Work.FM.Fstar z) b z θ 0]
  rw [Work.Spaces.DzIter_eq_sum_scoef hsm b z hzmem 0 h0I]
  refine Work.Spaces.abs_sum_scoef_mul_le b (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z)
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) ?_
  intro k hk
  rw [pzIter_Fstar_eq_Gk k hzmem 0]
  refine (abs_zpow_mul_Gk_le_all k hz).trans ?_
  have hkfac : (k.factorial : ℝ) ≤ (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hk
  have hk1 : (k : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
  gcongr

/-! ## The Bell numbers of the rows `j ≤ 8` -/

/-- The Bell numbers of the rows `j ≤ 8` are at most `9000` (`B_8 = 4140`). -/
theorem bell_le_eight (j : ℕ) (hj : j ≤ 8) : Work.Spaces.bell j ≤ 9000 := by
  interval_cases j <;> decide

end LocFM8s

/-- **The `D_z`-jets of the fundamental-model profile decay like `1/z`, up to order `8`.** -/
theorem FM_jet8safe :
    ∃ CF : ℝ, 0 < CF ∧ ∀ j : ℕ, j ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z := by
  refine ⟨6531840000, by norm_num, fun j hj z hz θ => ?_⟩
  have hzpos : (0 : ℝ) < z := by linarith
  refine (LocFM8s.DzIter_Fstar_le j hz θ).trans ?_
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 9000 := by
    exact_mod_cast LocFM8s.bell_le_eight j hj
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 40320 := by
    have h := Nat.factorial_le hj
    have h8 : (Nat.factorial 8 : ℕ) = 40320 := by decide
    rw [h8] at h
    exact_mod_cast h
  have hj1 : (j : ℝ) + 1 ≤ 9 := by
    have h : j + 1 ≤ 8 + 1 := Nat.succ_le_succ hj
    have hR : ((j + 1 : ℕ) : ℝ) ≤ ((8 + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    linarith
  have hfac0 : (0 : ℝ) ≤ ((j.factorial : ℕ) : ℝ) := by positivity
  have hj10 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hnum : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 725760 := by
    have h1 : ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 40320 * 9 :=
      mul_le_mul hfac hj1 hj10 (by norm_num)
    nlinarith [h1]
  have hB : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z ≤ 725760 / z :=
    div_le_div_of_nonneg_right hnum hzpos.le
  have hBnn : 0 ≤ 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z := by positivity
  calc (Work.Spaces.bell j : ℝ) * (2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z)
      ≤ 9000 * (725760 / z) := mul_le_mul hbell hB hBnn (by norm_num)
    _ = 6531840000 / z := by ring

end Work.FTS_LocDatum3a
