import Mathlib
import Submission.Work.Lattice.CnormLevel
import Submission.Work.Lattice.FlowRateAsymptotic
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.FlowDataMax
import Submission.Work.Lattice.AccountingOneSided

/-!
# The active block of a flowed wedge, and the capacity criterion of §3

The §3 extraction (de Saxcé, Prop. 5) assigns to every flag member `V` of the flowed lattice
`Λ_t = a_t Λ₀` a number of vectors it can supply: the number of directions of `V` that are
"nearly contained in `L = modelX ℓ`".  The accounting (`Submission.AccountingOneSided`, i.e.
Lemma 4 of the paper) computes the *capacities* `effPos` from the level derivatives of the
Grayson polygon.  The link that lets the accounting bound the wedge `‖v₁∧…∧v_ℓ‖` is the
inequality

`effPos_s ≤ (number of directions the member can supply)`,

equivalently (both are `σ`-images of a real number) `sig k ℓ u ≤ r_s` for an *active block* `u` of
the member, where `r_s` is the level derivative `ċ_t(j_s)`.

This module proves the analytic core of that inequality in the algebraic framework of the max
norm (`MaxNorm.cnorm`), for which the level function of a fixed wedge

`flowLevel x = log (cnorm (⋀^k a_x w))`

is the logarithm of a supremum of exponentials (`MaxNorm.cnorm_map_flow`), hence (locally, near
any time at which a block dominates) the maximum of finitely many affine functions:

* `block_mul_le_level` / `block_log_le_level` — a single block's flowed mass is at most the level;
* `exists_attaining` / `flowLevel_eq_of_attaining` — at every time the supremum is attained, so
  the level equals the affine function of an attaining ("active") block;
* `IsActiveBlock` / `IsFirstActiveBlock` — a block is active at `t` when its flowed mass attains
  the level; "first active" means no strictly lower nonvanishing block is active;
* **`flowLevel_eventually_le_sig_left`** — for a first-active block `u`, for `x` to the left of
  `t` close enough to `t`, `flowLevel x − flowLevel t ≤ (x − t)·σ_u` (the *deficit* argument);
* **`sig_le_deriv_of_le_flowLevel`** — the criterion: if `g ≤ flowLevel` pointwise with
  `g t = flowLevel t` and `g` differentiable at `t` with derivative `r`, then `σ_u ≤ r`;
* **`effPos_le_of_sig_le`** — the transfer to the accounting vocabulary: `σ_u ≤ r` gives
  `effPos d j ℓ jb r s ≤ j − u`.

Module `Submission.Work.Lattice.ActiveBlock`, namespace `Submission.ActiveBlock`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.ActiveBlock

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax

variable {d : ℕ}

/-- The log-level function of the flowed wedge of a fixed `k`-vector `w`. -/
noncomputable def flowLevel {k : ℕ} (ℓ : ℕ) (hk : k ≤ d) (w : WK d k) (x : ℝ) : ℝ :=
  Real.log (cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ x) w))

/-! ## The level and its attaining block -/

/-- **A block's flowed mass is at most the level.** -/
lemma block_mul_le_level {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : k ≤ d) (w : WK d k)
    {u : ℕ} (hu : u ≤ k) (x : ℝ) :
    Real.exp (x * sig (d := d) k ℓ u) * cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≤
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ x) w) := by
  rw [eFlow_eq, cnorm_map_flow (d := d) hℓ0 hℓd x hk w]
  exact Finset.le_sup' (f := fun u => Real.exp (x * sig (d := d) k ℓ u) *
      cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u))
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hu))

/-- **At every time the level is attained by a nonvanishing block.** -/
lemma exists_attaining {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : k ≤ d) {w : WK d k}
    (hw : w ≠ 0) (x : ℝ) :
    ∃ u ≤ k, cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≠ 0 ∧
      Real.exp (x * sig (d := d) k ℓ u) * cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) =
        cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ x) w) := by
  obtain ⟨u, hu, hatt⟩ := Finset.exists_mem_eq_sup' (α := ℝ) (ι := ℕ)
    (s := Finset.range (k + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
    (fun u => Real.exp (x * sig (d := d) k ℓ u) *
      cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u))
  have huk : u ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
  have hinj : Function.Injective (fun w : WK d k => exteriorPower.map k (eFlow (d := d) ℓ x) w) := by
    intro a b hab
    exact Submission.ModelCone.map_twoScale_injective (d := d) (k := k) _ _ ℓ
      (Real.exp_ne_zero _) (Real.exp_ne_zero _) (by simpa [eFlow_eq] using hab)
  have hmap : exteriorPower.map k (eFlow (d := d) ℓ x) w ≠ 0 := by
    intro hz
    exact hw (hinj (hz.trans (map_zero _).symm))
  have hpos : 0 < cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ x) w) :=
    cnorm_pos_of_ne_zero hk _ hmap
  have heq : Real.exp (x * sig (d := d) k ℓ u) *
      cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) =
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ x) w) := by
    rw [eFlow_eq, cnorm_map_flow (d := d) hℓ0 hℓd x hk w]
    exact hatt.symm
  refine ⟨u, huk, ?_, heq⟩
  intro h0
  rw [h0, mul_zero] at heq
  exact absurd heq.symm (ne_of_gt hpos)

/-- The level at a time at which the block `u` attains it. -/
lemma flowLevel_eq_of_attaining {k ℓ : ℕ} (hk : k ≤ d) {w : WK d k} {u : ℕ}
    (hc : cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≠ 0) {x : ℝ}
    (hatt : Real.exp (x * sig (d := d) k ℓ u) *
        cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) =
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ x) w)) :
    flowLevel (d := d) ℓ hk w x =
      x * sig (d := d) k ℓ u + Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) := by
  have hcpos : 0 < cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) :=
    lt_of_le_of_ne (cnorm_nonneg hk _) (Ne.symm hc)
  rw [flowLevel, ← hatt, Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hcpos), Real.log_exp]

/-- **A block's log-mass (including its growth rate) is at most the level.** -/
lemma block_log_le_level {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : k ≤ d) (w : WK d k)
    {u : ℕ} (hu : u ≤ k) (hc : cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≠ 0)
    (x : ℝ) :
    x * sig (d := d) k ℓ u + Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) ≤
      flowLevel (d := d) ℓ hk w x := by
  have hcpos : 0 < cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) :=
    lt_of_le_of_ne (cnorm_nonneg hk _) (Ne.symm hc)
  rw [flowLevel]
  calc x * sig (d := d) k ℓ u + Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u))
      = Real.log (Real.exp (x * sig (d := d) k ℓ u) *
          cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) := by
        rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hcpos), Real.log_exp]
    _ ≤ Real.log (cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ x) w)) :=
        Real.log_le_log (by positivity) (block_mul_le_level (d := d) hℓ0 hℓd hk w hu x)

/-! ## Active blocks -/

/-- The block `u` is **active** at time `t` for the wedge `w`: its flowed mass attains the level
`cnorm (⋀^k a_t w)`. -/
def IsActiveBlock {k : ℕ} (ℓ : ℕ) (hk : k ≤ d) (t : ℝ) (w : WK d k) (u : ℕ) : Prop :=
  u ≤ k ∧ cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≠ 0 ∧
    Real.exp (t * sig (d := d) k ℓ u) * cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) =
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) w)

/-- The block `u` is the **first active** block at time `t`: it is active, and every strictly
lower nonvanishing block is *strictly* inactive. -/
def IsFirstActiveBlock {k : ℕ} (ℓ : ℕ) (hk : k ≤ d) (t : ℝ) (w : WK d k) (u : ℕ) : Prop :=
  IsActiveBlock (d := d) ℓ hk t w u ∧
    ∀ u' ≤ k, u' < u → cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u') ≠ 0 →
      Real.exp (t * sig (d := d) k ℓ u') *
        cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u') <
        cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) w)

/-- There always exists a first active block. -/
lemma exists_isFirstActive {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : k ≤ d) {w : WK d k}
    (hw : w ≠ 0) (t : ℝ) : ∃ u, IsFirstActiveBlock (d := d) ℓ hk t w u := by
  classical
  have hex : ∃ u ≤ k, cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≠ 0 ∧
      Real.exp (t * sig (d := d) k ℓ u) *
        cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) =
        cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) w) :=
    exists_attaining (d := d) hℓ0 hℓd hk hw t
  refine ⟨Nat.find hex, Nat.find_spec hex, fun u' hu'k hu'lt hc' => ?_⟩
  by_contra hcon
  push Not at hcon
  have heq : Real.exp (t * sig (d := d) k ℓ u') *
      cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u') =
      cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) w) :=
    le_antisymm (block_mul_le_level (d := d) hℓ0 hℓd hk w hu'k t) hcon
  have hle : Nat.find hex ≤ u' := Nat.find_le ⟨hu'k, hc', heq⟩
  omega

/-! ## The deficit argument -/

/-- **A one-sided slope bound at `0` bounds the derivative.** -/
theorem le_deriv_of_eventually_slope_zero_left {g : ℝ → ℝ} {r c : ℝ} (hg : HasDerivAt g r 0)
    (h : ∀ᶠ h' in 𝓝[<] (0 : ℝ), c ≤ (g h' - g 0) / h') : c ≤ r := by
  have ht : Tendsto (fun h' : ℝ => (g h' - g 0) / h') (𝓝[<] (0 : ℝ)) (𝓝 r) := by
    have h0 := hg.tendsto_slope_zero_left
    simpa [zero_add, div_eq_inv_mul, smul_eq_mul] using h0
  exact ge_of_tendsto ht h

/-- **A one-sided slope bound at `t` bounds the derivative.** -/
theorem le_deriv_of_eventually_slope_left {g : ℝ → ℝ} {t r c : ℝ} (hg : HasDerivAt g r t)
    (h : ∀ᶠ x in 𝓝[<] t, c ≤ (g x - g t) / (x - t)) : c ≤ r := by
  have ht : Tendsto (fun x : ℝ => (g x - g t) / (x - t)) (𝓝[<] t) (𝓝 r) := by
    have h1 := (hasDerivAt_iff_tendsto_slope_left_right.mp hg).1
    refine h1.congr' ?_
    filter_upwards with x
    show _root_.slope g t x = (g x - g t) / (x - t)
    rw [_root_.slope, div_eq_inv_mul, smul_eq_mul]
    simp [vsub_eq_sub]
  exact ge_of_tendsto ht h

/-- **The deficit lemma.**  For the first active block `u` at time `t` the level function grows
to the left of `t` at most at rate `σ_u`. -/
theorem flowLevel_eventually_le_sig_left {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : k ≤ d)
    {w : WK d k} (hw : w ≠ 0) {t : ℝ} {u : ℕ} (hu : IsFirstActiveBlock (d := d) ℓ hk t w u) :
    ∀ᶠ x in 𝓝[<] t,
      flowLevel (d := d) ℓ hk w x - flowLevel (d := d) ℓ hk w t ≤
        (x - t) * sig (d := d) k ℓ u := by
  classical
  obtain ⟨⟨huk, hcu, hacteq⟩, hfirst⟩ := hu
  have hcu_pos : 0 < cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) :=
    lt_of_le_of_ne (cnorm_nonneg hk _) (Ne.symm hcu)
  have hlevelt := flowLevel_eq_of_attaining (d := d) (ℓ := ℓ) hk hcu hacteq
  -- the blocks strictly below `u` with nonvanishing norm
  set T : Finset ℕ := (Finset.range (k + 1)).filter
    (fun u' => cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u') ≠ 0 ∧ u' < u) with hT
  -- the deficit function
  set dv : ℕ → ℝ := fun u' =>
    (t * (sig (d := d) k ℓ u - sig (d := d) k ℓ u') -
        (Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u')) -
          Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)))) /
      (sig (d := d) k ℓ u - sig (d := d) k ℓ u') with hdv
  have hdvpos : ∀ u' ∈ T, 0 < dv u' := by
    intro u' hu'T
    obtain ⟨hran, hc', hu'lt⟩ := Finset.mem_filter.mp (hT ▸ hu'T)
    have hc'pos : 0 < cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u') :=
      lt_of_le_of_ne (cnorm_nonneg hk _) (Ne.symm hc')
    have hu'k : u' ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hran)
    have hstrict := hfirst u' hu'k hu'lt hc'
    rw [← hacteq] at hstrict
    have hlog : t * sig (d := d) k ℓ u' +
        Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u')) <
        t * sig (d := d) k ℓ u +
          Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) := by
      have h1 := Real.log_lt_log (mul_pos (Real.exp_pos _) hc'pos) hstrict
      rwa [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hc'pos), Real.log_exp,
        Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hcu_pos), Real.log_exp] at h1
    have hnum : 0 < t * (sig (d := d) k ℓ u - sig (d := d) k ℓ u') -
        (Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u')) -
          Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u))) := by linarith
    rw [hdv]
    exact div_pos hnum (by
      have := sig_strict (d := d) hℓ0 hℓd hu'lt huk
      linarith)
  set δ : ℝ := if hTne : T.Nonempty then (T.image dv).min' (hTne.image dv) else 1 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    by_cases hTne : T.Nonempty
    · rw [dif_pos hTne]
      refine (Finset.lt_min'_iff (s := T.image dv) (H := hTne.image dv)).mpr (fun b hb => ?_)
      obtain ⟨u', hu'T, rfl⟩ := Finset.mem_image.mp hb
      exact hdvpos u' hu'T
    · rw [dif_neg hTne]; exact one_pos
  have hδle : ∀ u' ∈ T, δ ≤ dv u' := by
    intro u' hu'T
    rw [hδdef]
    by_cases hTne : T.Nonempty
    · rw [dif_pos hTne]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨u', hu'T, rfl⟩)
    · exact absurd ⟨u', hu'T⟩ hTne
  refine Filter.mem_of_superset (Ioo_mem_nhdsLT (show t - δ < t by linarith)) ?_
  intro x hh
  obtain ⟨hxgt, hxlt⟩ := hh
  obtain ⟨u₀, hu₀k, hc₀, hatt₀⟩ := exists_attaining (d := d) hℓ0 hℓd hk hw x
  have hc₀_pos : 0 < cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) :=
    lt_of_le_of_ne (cnorm_nonneg hk _) (Ne.symm hc₀)
  have hlevelx := flowLevel_eq_of_attaining (d := d) (ℓ := ℓ) hk hc₀ hatt₀
  -- the key logarithmic inequality
  have hkey : Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀)) -
      Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) ≤
      x * (sig (d := d) k ℓ u - sig (d := d) k ℓ u₀) := by
    rcases lt_or_ge u₀ u with hlt | hge
    · -- `u₀` is a strictly lower nonvanishing block: the deficit applies
      have hmemT : u₀ ∈ T := by
        rw [hT]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hu₀k), hc₀, hlt⟩
      have hdvle := hδle u₀ hmemT
      have hsig : 0 < sig (d := d) k ℓ u - sig (d := d) k ℓ u₀ := by
        have := sig_strict (d := d) hℓ0 hℓd hlt huk
        linarith
      have htx : t - x < dv u₀ := lt_of_lt_of_le (by linarith) hdvle
      have hdvval : dv u₀ = (t * (sig (d := d) k ℓ u - sig (d := d) k ℓ u₀) -
          (Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀)) -
            Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)))) /
          (sig (d := d) k ℓ u - sig (d := d) k ℓ u₀) := rfl
      rw [hdvval, lt_div_iff₀ hsig] at htx
      nlinarith [htx]
    · -- `u₀ ≥ u`: use that `u` is active at `t`
      have hle' : Real.exp (t * sig (d := d) k ℓ u₀) *
          cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) ≤
          Real.exp (t * sig (d := d) k ℓ u) *
            cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) := by
        calc Real.exp (t * sig (d := d) k ℓ u₀) *
              cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀)
            ≤ cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ t) w) :=
              block_mul_le_level (d := d) hℓ0 hℓd hk w hu₀k t
          _ = Real.exp (t * sig (d := d) k ℓ u) *
              cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) := hacteq.symm
      have hlog : t * sig (d := d) k ℓ u₀ +
          Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀)) ≤
          t * sig (d := d) k ℓ u +
            Real.log (cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) := by
        have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hc₀_pos) hle'
        rwa [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hc₀_pos), Real.log_exp,
          Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hcu_pos), Real.log_exp] at h1
      have hxle : t * (sig (d := d) k ℓ u - sig (d := d) k ℓ u₀) ≤
          x * (sig (d := d) k ℓ u - sig (d := d) k ℓ u₀) := by
        refine mul_le_mul_of_nonpos_right hxlt.le ?_
        have := sig_mono (d := d) (k := k) hℓ0 hℓd hge
        linarith
      linarith [hlog, hxle]
  change flowLevel (d := d) ℓ hk w x - flowLevel (d := d) ℓ hk w t ≤
    (x - t) * sig (d := d) k ℓ u
  rw [hlevelx, hlevelt]
  nlinarith [hkey]

/-! ## The criterion, and the transfer to the accounting capacities -/

/-- **The capacity criterion.**  If a function `g` is differentiable at `t` with derivative `r`,
bounds the level function from below, and touches it at `t`, then `r` is at least the flow rate
`σ_u` of any *first active* block `u`.  Since the accounting capacity `effPos` is the `σ`-inverse
of the level derivative, this says that the member can supply at least `j - u` directions. -/
theorem sig_le_deriv_of_le_flowLevel {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : k ≤ d)
    {w : WK d k} (hw : w ≠ 0) {g : ℝ → ℝ} {t r : ℝ} (hg : HasDerivAt g r t)
    (hle : ∀ x, g x ≤ flowLevel (d := d) ℓ hk w x)
    (heq : g t = flowLevel (d := d) ℓ hk w t)
    {u : ℕ} (hu : IsFirstActiveBlock (d := d) ℓ hk t w u) :
    sig (d := d) k ℓ u ≤ r := by
  refine le_deriv_of_eventually_slope_left hg ?_
  filter_upwards [flowLevel_eventually_le_sig_left (d := d) hℓ0 hℓd hk hw hu,
    self_mem_nhdsWithin] with x hx hxt
  have hxg : g x - g t ≤ (x - t) * sig (d := d) k ℓ u := by
    have h1 : g x - g t ≤
        flowLevel (d := d) ℓ hk w x - flowLevel (d := d) ℓ hk w t := by
      rw [heq]; linarith [hle x]
    linarith [hx]
  have hxt' : x - t < 0 := by
    simp only [Set.mem_Iio] at hxt
    linarith
  rw [le_div_iff_of_neg hxt']
  nlinarith [hxg]

/-- The `σ`-inverse identity for the accounting capacity. -/
lemma sig_eq_sub_div {ℓ : ℕ} (hℓd : ℓ ≤ d) {j u : ℕ} (hu : u ≤ j) :
    sig (d := d) j ℓ u =
      (j : ℝ) / ((d : ℝ) - (ℓ : ℝ)) - ((j : ℝ) - (u : ℝ)) * slope (d := d) ℓ := by
  rw [sig, FlowRateAsymptotic.slope]
  field_simp
  ring

/-- **The transfer to the accounting capacity.**  If the level derivative `r s` is at least the
rate `σ_u` of a block `u ≤ j`, then the effective position (capacity) `effPos` at the rank
`jb s = j` supplied by the accounting is at most `j - u`, i.e. the number of directions the
member can supply. -/
theorem effPos_le_of_sig_le {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {u : ℕ} (hu : u ≤ j)
    {jb r : ℕ → ℝ} {s : ℕ} (hjb : jb s = (j : ℝ)) (h : sig (d := d) j ℓ u ≤ r s) :
    AccountingOneSided.effPos d ℓ jb r s ≤ (j : ℝ) - (u : ℝ) := by
  have hrate0 : 0 < slope (d := d) ℓ := FlowRateAsymptotic.slope_pos (d := d) hℓ0 hℓd
  have hsig := sig_eq_sub_div (d := d) (le_of_lt hℓd) hu
  rw [AccountingOneSided.effPos_apply, hjb, div_le_iff₀ hrate0]
  linarith [hsig, h]

end Submission.ActiveBlock
