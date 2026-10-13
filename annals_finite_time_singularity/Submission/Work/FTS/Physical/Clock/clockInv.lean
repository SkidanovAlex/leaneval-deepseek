/-
# `Work.FTS.Physical.Clock.clockInv` — the inverse clock, extended across the endpoints

The clock `t(τ) = ∫₀^τ A` of the dynamic rescaling is strictly increasing on `[0,∞)` with
`t(0) = 0` and `t(τ) → T = ∫₀^∞ A`; every physical time `t ∈ [0,T)` is therefore `t = t(τ)`
for a unique fake time `τ = τ(t) ≥ 0` (`Work.FTS.Physical.Clock.exists_inverse_clock`).

The reconstruction of node N8 evaluates the physical vorticity along a *single* clock
`t ↦ τ(t)` defined on the whole blow-up interval.  The natural inverse of `t` is differentiable
on the **open** interval `(0,T)` only: at the endpoints `0` and `T` the inverse map is defined
by the strict monotonicity of `t` and no one-sided derivative information is available from the
inverse-function theorem.  The two consumers of the clock, however, ask for more:

* the strip transport `Work.FTS.Physical.bsAdmissibleStripFull_comp_clock` needs a *two-sided*
  `HasDerivAt` of the clock at **every** point of the closed strip `[0,S]`, including `t = 0`;
* the compact support and the profile lower bound are evaluated at physical times arbitrarily
  close to `0`.

This module therefore produces the **extended inverse clock** `clockInv C`:

  `clockInv C t = if t ≤ 0 then t · A(0)⁻¹ else τ(t)`,

i.e. the inverse clock continued to the left of `0` by its tangent line at `0`.  The tangent
matches on the right because the *right* slope of the clock at `0` is `A(0) > 0`
(`Clock.clock_slope_tendsto`, proved from the fundamental theorem of calculus), so `clockInv C`
is genuinely differentiable at `0` with derivative `A(0)⁻¹` — the endpoint datum the transport
lemma needs.  Everything is proved on `[0,T)`; nothing is assumed at or past the blow-up time
`T`, where the clock is not defined.

The main export of this module is

  `Work.FTS.Physical.clockInv_eqs`, which collects the five properties of `clockInv C` used by
  the reconstruction: the clock identity `t(τ(t)) = t`, nonnegativity, the comparison
  `T - t ≤ 2A(τ(t))`, monotonicity, and the two differentiability statements.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Clock.exists_inverse_clock
import Submission.Work.FTS.Physical.Clock.tail_le_two_mul
import Submission.Work.FTS.Physical.Clock.T_pos
import Submission.Work.FTS.Physical.Clock.t_strictMonoOn
import Submission.Work.FTS.Physical.Clock.clock_slope_tendsto
import Mathlib.Analysis.Calculus.Deriv.Slope

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

open PhysClock

/-! ## The inverse clock of `Clock.exists_inverse_clock` -/

/-- The inverse clock selected by `Work.FTS.Physical.Clock.exists_inverse_clock`: the (unique)
fake time `τ(t)` with `t(τ(t)) = t` for `t ∈ [0,T)`. -/
noncomputable def tauInv (C : PhysClock) : ℝ → ℝ :=
  (Work.FTS.Physical.Clock.exists_inverse_clock C).choose

/-- The defining properties of `tauInv`: the clock identity, nonnegativity, the clock comparison
`T - t ≤ 2A(τ(t))` and differentiability on the open interval `(0,T)`. -/
theorem tauInv_spec (C : PhysClock) :
    (∀ t ∈ Set.Ico 0 C.T, C.t (tauInv C t) = t) ∧
      (∀ t ∈ Set.Ico 0 C.T, 0 ≤ tauInv C t) ∧
      (∀ t ∈ Set.Ico 0 C.T, C.T - t ≤ 2 * C.A (tauInv C t)) ∧
      ∀ t ∈ Set.Ioo 0 C.T, HasDerivAt (tauInv C) ((C.A (tauInv C t))⁻¹) t :=
  (Work.FTS.Physical.Clock.exists_inverse_clock C).choose_spec

/-- `t(τ(t)) = t` for every physical time `t < T`. -/
theorem tauInv_clock (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    C.t (tauInv C t) = t :=
  (tauInv_spec C).1 t ht

/-- The inverse clock takes nonnegative values. -/
theorem tauInv_nonneg (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) : 0 ≤ tauInv C t :=
  (tauInv_spec C).2.1 t ht

/-- The clock comparison `T - t ≤ 2A(τ(t))` at the inverse clock. -/
theorem tauInv_tail (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    C.T - t ≤ 2 * C.A (tauInv C t) :=
  (tauInv_spec C).2.2.1 t ht

/-- The inverse clock is differentiable on `(0,T)`, with derivative `1/A(τ(t))`. -/
theorem tauInv_hasDerivAt (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (tauInv C) ((C.A (tauInv C t))⁻¹) t :=
  (tauInv_spec C).2.2.2 t ht

/-- The inverse clock is *strictly* positive on `(0,T)`: if `τ(t) = 0` then `t = t(0) = 0`. -/
theorem tauInv_pos (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) : 0 < tauInv C t := by
  have hmem : t ∈ Set.Ico 0 C.T := ⟨ht.1.le, ht.2⟩
  rcases lt_or_eq_of_le (tauInv_nonneg C hmem) with h | h
  · exact h
  · exfalso
    have h1 : C.t (tauInv C t) = 0 := by rw [← h]; exact PhysClock.t_zero C
    rw [tauInv_clock C hmem] at h1
    exact absurd h1 (ne_of_gt ht.1)

/-- `τ(t) → 0` as `t → 0⁺` (the inverse clock is continuous at `0` from the right). -/
theorem tauInv_tendsto_zero (C : PhysClock) :
    Tendsto (tauInv C) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (Work.FTS.Physical.Clock.T_pos C)] with y hy
    have hmem : y ∈ Set.Ico 0 C.T := ⟨hy.1.le, hy.2⟩
    linarith [tauInv_nonneg C hmem, hb]
  · have hTb : 0 < C.t b := by
      have h := (Work.FTS.Physical.Clock.t_strictMonoOn C) (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr hb.le) hb
      rwa [PhysClock.t_zero] at h
    filter_upwards [Ioo_mem_nhdsGT (lt_min hTb (Work.FTS.Physical.Clock.T_pos C))] with y hy
    have hy' : y ∈ Set.Ico 0 C.T := ⟨hy.1.le, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩
    have hylt : y < C.t b := lt_of_lt_of_le hy.2 (min_le_left _ _)
    have hiff := (Work.FTS.Physical.Clock.t_strictMonoOn C).lt_iff_lt
      (Set.mem_Ici.mpr (tauInv_nonneg C hy'))
      (show b ∈ Set.Ici (0 : ℝ) from hb.le)
    rw [tauInv_clock C hy'] at hiff
    exact hiff.mp hylt

/-- `τ(t) > 0` eventually as `t → 0⁺`. -/
theorem eventually_tauInv_pos (C : PhysClock) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), tauInv C t ∈ Set.Ioi 0 := by
  filter_upwards [Ioo_mem_nhdsGT (Work.FTS.Physical.Clock.T_pos C)] with y hy
  exact tauInv_pos C hy

/-- **The inverse clock converges to `0` in `𝓝[>] 0`**: it maps right-neighbourhoods of `0` to
right-neighbourhoods of `0`.  This is what allows the slope limit of the clock to be composed
with the inverse clock. -/
theorem tauInv_tendsto_nhdsGT (C : PhysClock) :
    Tendsto (tauInv C) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tauInv_tendsto_zero C, eventually_tauInv_pos C⟩

/-! ## The extended inverse clock -/

/-- **The extended inverse clock.**  The inverse clock `τ(·)` of the dynamic rescaling, continued
to the left of `0` by its tangent line `t ↦ t·A(0)⁻¹` at `0`.  The point of the extension is that
the resulting function has a genuine (two-sided) derivative `A(0)⁻¹` at `t = 0`, which the strip
transport `Work.FTS.Physical.bsAdmissibleStripFull_comp_clock` demands.

For `t ∈ [0,T)` the value is the true inverse clock; for `t ≥ T` the value is irrelevant (the
reconstruction never evaluates it there). -/
noncomputable def clockInv (C : PhysClock) (t : ℝ) : ℝ :=
  if t ≤ 0 then t * (C.A 0)⁻¹ else tauInv C t

theorem clockInv_of_nonpos {C : PhysClock} {t : ℝ} (h : t ≤ 0) :
    clockInv C t = t * (C.A 0)⁻¹ :=
  if_pos h

theorem clockInv_of_pos {C : PhysClock} {t : ℝ} (h : 0 < t) : clockInv C t = tauInv C t :=
  if_neg (not_le.mpr h)

@[simp] theorem clockInv_zero (C : PhysClock) : clockInv C 0 = 0 := by
  rw [clockInv_of_nonpos le_rfl, zero_mul]

/-- On `[0,T)` the extended clock is the true inverse clock: `t(τ(t)) = t`. -/
theorem clockInv_clock (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    C.t (clockInv C t) = t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, clockInv_zero, PhysClock.t_zero]
  · rw [clockInv_of_pos h]; exact tauInv_clock C ht

/-- The extended clock is nonnegative on `[0,T)`. -/
theorem clockInv_nonneg (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    0 ≤ clockInv C t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, clockInv_zero]
  · rw [clockInv_of_pos h]; exact tauInv_nonneg C ht

/-- The clock comparison `T - t ≤ 2A(τ(t))` for the extended clock. -/
theorem clockInv_tail (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    C.T - t ≤ 2 * C.A (clockInv C t) := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, clockInv_zero]
    simpa [PhysClock.t_zero] using Work.FTS.Physical.Clock.tail_le_two_mul C (le_refl (0 : ℝ))
  · rw [clockInv_of_pos h]; exact tauInv_tail C ht

/-- The extended clock is strictly positive on `(0,T)`. -/
theorem clockInv_pos_of_pos (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) :
    0 < clockInv C t := by
  rw [clockInv_of_pos ht.1]
  exact tauInv_pos C ht

/-- **The extended clock is monotone**: `t ≤ t'` implies `τ(t) ≤ τ(t')` on `[0,T)`. -/
theorem clockInv_mono (C : PhysClock) {t t' : ℝ} (ht : t ∈ Set.Ico 0 C.T)
    (ht' : t' ∈ Set.Ico 0 C.T) (htt' : t ≤ t') : clockInv C t ≤ clockInv C t' := by
  have h1 := clockInv_clock C ht
  have h2 := clockInv_clock C ht'
  by_contra hcon
  push_neg at hcon
  have hlt := (Work.FTS.Physical.Clock.t_strictMonoOn C (clockInv_nonneg C ht')
    (clockInv_nonneg C ht) hcon)
  rw [h2, h1] at hlt
  exact absurd hlt (not_lt.mpr htt')

/-- The extended clock is differentiable on `(0,T)`, with derivative `1/A(τ(t))`. -/
theorem clockInv_hasDerivAt (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (clockInv C) ((C.A (clockInv C t))⁻¹) t := by
  have heq : clockInv C =ᶠ[𝓝 t] tauInv C := by
    filter_upwards [isOpen_Ioi.mem_nhds ht.1] with s hs using clockInv_of_pos hs
  have hder : HasDerivAt (tauInv C) ((C.A (tauInv C t))⁻¹) t := tauInv_hasDerivAt C ht
  rw [clockInv_of_pos ht.1]
  exact hder.congr_of_eventuallyEq heq

/-! ## The derivative of the extended clock at `t = 0`

The left branch is the tangent line, so the left derivative is `A(0)⁻¹` outright; the right
derivative is the limit of the slopes `τ(t)/t = τ(t)/t(τ(t))`, which is `A(0)⁻¹` by the slope
limit of the clock (`Clock.clock_slope_tendsto`) composed with `τ(·) → 0⁺`
(`tauInv_tendsto_nhdsGT`). -/

/-- **The extended clock is differentiable at `0` with derivative `A(0)⁻¹`.**

This is the endpoint datum that makes the strip transport applicable: the natural inverse clock
has no derivative at `t = 0`, whereas the extension by the tangent line does.  The two one-sided
derivatives are computed separately and glued with `HasDerivWithinAt.union` along
`Iic 0 ∪ Ioi 0 = univ`. -/
theorem clockInv_hasDerivAt_zero (C : PhysClock) :
    HasDerivAt (clockInv C) ((C.A 0)⁻¹) 0 := by
  have hleft : HasDerivWithinAt (clockInv C) ((C.A 0)⁻¹) (Set.Iic 0) 0 := by
    have hlin : HasDerivWithinAt (fun s : ℝ => s * (C.A 0)⁻¹) ((C.A 0)⁻¹) (Set.Iic (0 : ℝ)) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).hasDerivWithinAt (s := Set.Iic (0 : ℝ))).mul_const
        ((C.A 0)⁻¹)
      simpa using h
    refine hlin.congr (fun y hy => ?_) ?_
    · rw [clockInv_of_nonpos hy]
    · rw [clockInv_of_nonpos le_rfl]
  have hright : HasDerivWithinAt (clockInv C) ((C.A 0)⁻¹) (Set.Ioi 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)]
    have hslope : slope (clockInv C) 0 = fun y : ℝ => clockInv C y / y := by
      funext y
      rw [slope_fun_def_field]
      simp [clockInv_zero]
    rw [hslope]
    have hsl := (Work.FTS.Physical.Clock.clock_slope_tendsto C).2.comp (tauInv_tendsto_nhdsGT C)
    refine Filter.Tendsto.congr' ?_ hsl
    filter_upwards [Ioo_mem_nhdsGT (Work.FTS.Physical.Clock.T_pos C)] with y hy
    have hmem : y ∈ Set.Ico 0 C.T := ⟨hy.1.le, hy.2⟩
    rw [Function.comp_apply, tauInv_clock C hmem, clockInv_of_pos hy.1]
  have hglue : HasDerivWithinAt (clockInv C) ((C.A 0)⁻¹) (Set.Iic 0 ∪ Set.Ioi 0) 0 :=
    hleft.union hright
  rw [Set.Iic_union_Ioi] at hglue
  exact hasDerivWithinAt_univ.mp hglue

/-- **The collected clock data of the reconstruction.**  The extended inverse clock
`clockInv C` satisfies, for every physical time in the blow-up interval:

* `t(τ(t)) = t` and `τ(t) ≥ 0` on `[0,T)`;
* the comparison `T - t ≤ 2A(τ(t))`;
* monotonicity;
* differentiability with derivative `A(τ(t))⁻¹` at `0` and at every interior point. -/
theorem clockInv_eqs (C : PhysClock) :
    (∀ t ∈ Set.Ico 0 C.T, C.t (clockInv C t) = t) ∧
      (∀ t ∈ Set.Ico 0 C.T, 0 ≤ clockInv C t) ∧
      (∀ t ∈ Set.Ico 0 C.T, C.T - t ≤ 2 * C.A (clockInv C t)) ∧
      (∀ t ∈ Set.Ioo 0 C.T, HasDerivAt (clockInv C) ((C.A (clockInv C t))⁻¹) t) ∧
      HasDerivAt (clockInv C) ((C.A 0)⁻¹) 0 :=
  ⟨fun _ ht => clockInv_clock C ht, fun _ ht => clockInv_nonneg C ht,
    fun _ ht => clockInv_tail C ht, fun _ ht => clockInv_hasDerivAt C ht,
    clockInv_hasDerivAt_zero C⟩

end Work.FTS.Physical
