import Submission.NBody.Dominated
import Submission.NBody.Minimizer
import Mathlib

/-!
# Calibrating curves

Chapter 2 of the paper.  A curve `γ : ℝ → Eᴺ` is **`h`-calibrating for `u`** on `[a,b]` when
`A_{L+h}(γ|[a,b]) = u(γ b) - u(γ a)`; a curve is an **`h`-minimiser** when its action equals the
action potential of its endpoints.  The main facts proved here are

* every `h`-calibrating curve of a function `u` dominated by `L + h` is an `h`-minimiser
  (`IsCalibrating.isHMinimizer`),
* non-degenerate sub-curves of an `h`-calibrating curve are again `h`-calibrating
  (`IsCalibrating.sub`),
* concatenations of `h`-calibrating curves are `h`-calibrating (`IsCalibrating.concat`),
* `h`-minimisers calibrate the functions `u_p(x) = φ_h(x,p)` (`IsHMinimizer.isCalibrating_actionPot`),
* the "splitting" identity `φ_h(γ a, γ b) = A(γ|[a,c]) + φ_h(γ c, γ b)` along an `h`-minimiser
  (`IsHMinimizer.actionPot_eq_actionOn_add`).

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **`h`-calibrating curves.**  `γ` is `u`-calibrating on `[a,b]` when its action on `[a,b]`
equals the variation `u (γ b) - u (γ a)`. -/
def IsCalibrating (m : Fin N → ℝ) (h : ℝ) (u : EN E N → ℝ) (γ : ℝ → EN E N)
    (a b : ℝ) : Prop :=
  actionOn m h γ a b = ENNReal.ofReal (u (γ b) - u (γ a))

/-- The action of a calibrating curve is finite. -/
lemma IsCalibrating.actionOn_lt_top {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {γ : ℝ → EN E N} {a b : ℝ} (hcal : IsCalibrating m h u γ a b) :
    actionOn m h γ a b < ⊤ := by
  rw [IsCalibrating] at hcal
  rw [hcal]
  exact ENNReal.ofReal_lt_top

/-- **Every calibrating curve of a dominated function is an `h`-minimiser.** -/
theorem IsCalibrating.isHMinimizer {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {γ : ℝ → EN E N} {a b : ℝ} (hd : Dominated m h u) (hcal : IsCalibrating m h u γ a b)
    (hab : a < b) (hac : AbsolutelyContinuousOnInterval γ a b) :
    IsHMinimizer m h γ a b := by
  have hle : actionOn m h γ a b ≤ actionPot m h (γ a) (γ b) := by
    rw [hcal]
    exact hd (γ a) (γ b)
  exact le_antisymm hle (actionPot_le_of_interval hab rfl rfl hac)

/-- **Splitting identity for `h`-minimisers.**  If `γ` is an `h`-minimiser with finite action on
`[a,b]` and `c ∈ (a,b)`, then `φ_h(γ a, γ b) = A(γ|[a,c]) + φ_h(γ c, γ b)`. -/
theorem IsHMinimizer.actionPot_eq_actionOn_add {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b c : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : actionOn m h γ a b < ⊤)
    (hac' : a < c) (hcb : c < b) :
    actionPot m h (γ a) (γ b) = actionOn m h γ a c + actionPot m h (γ c) (γ b) := by
  rw [← hmin, actionOn_add γ hac'.le hcb.le,
    IsHMinimizer.sub_right hac hmin hfin hac' hcb]

/-- **Splitting identity for `h`-minimisers** (initial part). -/
theorem IsHMinimizer.actionOn_add_actionPot_eq {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b c : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : actionOn m h γ a b < ⊤)
    (hac' : a < c) (hcb : c < b) :
    actionPot m h (γ a) (γ b) = actionPot m h (γ a) (γ c) + actionOn m h γ c b := by
  rw [← hmin, actionOn_add γ hac'.le hcb.le,
    IsHMinimizer.sub_left hac hmin hfin hac' hcb]

/-- **Sub-curves of `u`-calibrating curves are `u`-calibrating.** -/
theorem IsCalibrating.sub {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {γ : ℝ → EN E N}
    {a b c : ℝ} (hd : Dominated m h u) (hcal : IsCalibrating m h u γ a b)
    (hac : AbsolutelyContinuousOnInterval γ a b) (hac' : a < c) (hcb : c < b) :
    IsCalibrating m h u γ a c := by
  have hfin : actionOn m h γ a b < ⊤ := hcal.actionOn_lt_top
  have hsum : actionOn m h γ a b = actionOn m h γ a c + actionOn m h γ c b :=
    actionOn_add γ hac'.le hcb.le
  have hX : actionOn m h γ a c < ⊤ := by
    rw [hsum] at hfin; exact (ENNReal.add_lt_top.mp hfin).1
  have hY : actionOn m h γ c b < ⊤ := by
    rw [hsum] at hfin; exact (ENNReal.add_lt_top.mp hfin).2
  have hac_ac : AbsolutelyContinuousOnInterval γ a c :=
    hac.mono (by
      rw [uIcc_of_le hac'.le, uIcc_of_le (hac'.le.trans hcb.le)]
      exact Set.Icc_subset_Icc_right hcb.le)
  have hac_cb : AbsolutelyContinuousOnInterval γ c b :=
    hac.mono (by
      rw [uIcc_of_le hcb.le, uIcc_of_le (hac'.le.trans hcb.le)]
      exact Set.Icc_subset_Icc_left hac'.le)
  have h1 : ENNReal.ofReal (u (γ c) - u (γ a)) ≤ actionOn m h γ a c :=
    (dominated_iff_le_actionOn.mp hd hac' hac_ac)
  have h2 : ENNReal.ofReal (u (γ b) - u (γ c)) ≤ actionOn m h γ c b :=
    (dominated_iff_le_actionOn.mp hd hcb hac_cb)
  set α := u (γ c) - u (γ a) with hαdef
  set β := u (γ b) - u (γ c) with hβdef
  have hαβ : u (γ b) - u (γ a) = α + β := by rw [hαdef, hβdef]; ring
  rw [IsCalibrating] at hcal
  have htot : (actionOn m h γ a c).toReal + (actionOn m h γ c b).toReal = max (α + β) 0 := by
    rw [← ENNReal.toReal_add hX.ne hY.ne, ← hsum, hcal, hαβ, ENNReal.toReal_ofReal']
  have hto1 : max α 0 ≤ (actionOn m h γ a c).toReal := by
    have := ENNReal.toReal_mono hX.ne h1
    rwa [ENNReal.toReal_ofReal'] at this
  have hto2 : max β 0 ≤ (actionOn m h γ c b).toReal := by
    have := ENNReal.toReal_mono hY.ne h2
    rwa [ENNReal.toReal_ofReal'] at this
  have hmax_ge : max (α + β) 0 ≤ max α 0 + max β 0 := by
    refine max_le (by linarith [le_max_left α 0, le_max_left β 0]) (by positivity)
  have hEqX : (actionOn m h γ a c).toReal = max α 0 := by
    have hkey : max α 0 + max β 0 = (actionOn m h γ a c).toReal + (actionOn m h γ c b).toReal :=
      le_antisymm (add_le_add hto1 hto2) (by rw [htot]; exact hmax_ge)
    linarith [hto1]
  show actionOn m h γ a c = ENNReal.ofReal (u (γ c) - u (γ a))
  rw [← ENNReal.ofReal_toReal hX.ne, hEqX]
  rcases le_total 0 α with ha | ha
  · rw [max_eq_left ha, ← hαdef]
  · rw [max_eq_right ha, ← hαdef, ENNReal.ofReal_eq_zero.mpr ha, ENNReal.ofReal_zero]

/-- **Concatenation of calibrating curves.** -/
theorem IsCalibrating.concat {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {γ₁ γ₂ : ℝ → EN E N} {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hjoin : γ₁ τ₁ = γ₂ 0)
    (hmono₁ : u (γ₁ 0) ≤ u (γ₁ τ₁)) (hmono₂ : u (γ₂ 0) ≤ u (γ₂ τ₂))
    (hcal₁ : IsCalibrating m h u γ₁ 0 τ₁) (hcal₂ : IsCalibrating m h u γ₂ 0 τ₂) :
    IsCalibrating m h u (fun t => if t ≤ τ₁ then γ₁ t else γ₂ (t - τ₁)) 0 (τ₁ + τ₂) := by
  rw [IsCalibrating] at hcal₁ hcal₂ ⊢
  rw [actionOn_concat hτ₁ hτ₂, hcal₁, hcal₂]
  have hval : (if (τ₁ + τ₂) ≤ τ₁ then γ₁ (τ₁ + τ₂) else γ₂ (τ₁ + τ₂ - τ₁)) = γ₂ τ₂ := by
    rw [if_neg (by linarith)]
    congr 1
    ring
  have hval0 : (if (0 : ℝ) ≤ τ₁ then γ₁ 0 else γ₂ (0 - τ₁)) = γ₁ 0 := by
    rw [if_pos hτ₁.le]
  rw [hval, hval0]
  have hd₁ : (0:ℝ) ≤ u (γ₁ τ₁) - u (γ₁ 0) := by linarith
  have hd₂ : (0:ℝ) ≤ u (γ₂ τ₂) - u (γ₂ 0) := by linarith
  rw [← ENNReal.ofReal_add hd₁ hd₂, hjoin]
  ring

/-- **`h`-minimisers calibrate the functions `u_p(x) = φ_h(x,p)`.** -/
theorem IsHMinimizer.isCalibrating_actionPot {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b : ℝ} {p : EN E N} (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : actionOn m h γ a b < ⊤) (hp : γ a = p)
    (hpnc : WithoutCollisions p) (hup : 0 ≤ U m p + h) :
    IsCalibrating m h (fun x => (actionPot m h x p).toReal) γ a b := by
  rw [IsCalibrating]
  have hpp : actionPot m h (γ a) p = 0 := by
    rw [hp]; exact actionPot_self_eq_zero hpnc hup
  have hb : actionPot m h (γ b) p = actionOn m h γ a b := by
    rw [← hp, actionPot_comm, ← hmin]
  rw [hpp, ENNReal.toReal_zero, sub_zero, hb]
  rw [ENNReal.ofReal_toReal hfin.ne]

end Submission.NBody
