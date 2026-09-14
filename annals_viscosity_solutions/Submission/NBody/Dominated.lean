import Submission.NBody.ActionTau
import Mathlib

/-!
# Functions dominated by `L + h`

A function `u : Eᴺ → ℝ` is **dominated by `L + h`** (the paper's notation `u ≺ L + h`) when
`u(y) - u(x) ≤ φ_h(x,y)` for all configurations `x, y`.  This is the class `𝓢_h` of the paper in
its "integral" form; it will be used to define the Lax--Oleinik semigroup and the horofunctions.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- `u` is **dominated by `L + h`**: `u(y) - u(x) ≤ φ_h(x,y)` for all configurations. -/
def Dominated (m : Fin N → ℝ) (h : ℝ) (u : EN E N → ℝ) : Prop :=
  ∀ x y : EN E N, ENNReal.ofReal (u y - u x) ≤ actionPot m h x y

theorem dominated_iff_le_actionOn {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} :
    Dominated m h u ↔ ∀ {γ : ℝ → EN E N} {a b : ℝ}, a < b →
      AbsolutelyContinuousOnInterval γ a b →
        ENNReal.ofReal (u (γ b) - u (γ a)) ≤ actionOn m h γ a b := by
  constructor
  · intro hu γ a b hab hac
    exact (hu (γ a) (γ b)).trans (actionPot_le_of_interval hab rfl rfl hac)
  · intro hu x y
    refine le_iInf fun p => ?_
    obtain ⟨hτ, h0, h1, hac⟩ := p.2
    have := hu hτ hac
    rwa [h0, h1] at this

/-- Adding a constant preserves domination. -/
theorem Dominated.add_const {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    (hu : Dominated m h u) (c : ℝ) : Dominated m h (fun x => u x + c) := by
  intro x y
  rw [show (fun x => u x + c) y - (fun x => u x + c) x = u y - u x from by ring]
  exact hu x y

/-- Constant functions are dominated. -/
theorem Dominated.const (m : Fin N → ℝ) (h : ℝ) (c : ℝ) :
    Dominated m h (fun _ : EN E N => c) := by
  intro x y
  have h0 : (fun _ : EN E N => c) y - (fun _ : EN E N => c) x = 0 := by simp
  rw [h0, ENNReal.ofReal_zero]
  exact bot_le

/-- Domination is monotone in the energy level. -/
theorem Dominated.mono {m : Fin N → ℝ} {h h' : ℝ} (hh : h ≤ h') {u : EN E N → ℝ}
    (hu : Dominated m h u) : Dominated m h' u :=
  fun x y => (hu x y).trans (actionPot_mono hh x y)

/-- Pointwise maximum of dominated functions is dominated. -/
theorem Dominated.sup {m : Fin N → ℝ} {h : ℝ} {u v : EN E N → ℝ}
    (hu : Dominated m h u) (hv : Dominated m h v) :
    Dominated m h (fun x => max (u x) (v x)) := by
  intro x y
  have hle : max (u y) (v y) - max (u x) (v x) ≤ max (u y - u x) (v y - v x) := by
    have h1 : max (u y) (v y) ≤ max (u x) (v x) + max (u y - u x) (v y - v x) := by
      refine max_le ?_ ?_
      · linarith [le_max_left (u y - u x) (v y - v x), le_max_left (u x) (v x)]
      · linarith [le_max_right (u y - u x) (v y - v x), le_max_right (u x) (v x)]
    linarith
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  rw [ENNReal.ofReal_max]
  exact max_le (hu x y) (hv x y)

/-- Domination passes to positive scalar multiples with factor at most `1`. -/
theorem Dominated.const_mul {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    (hu : Dominated m h u) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Dominated m h (fun x => c * u x) := by
  intro x y
  have hval : (fun x => c * u x) y - (fun x => c * u x) x = c * (u y - u x) := by ring
  rw [hval]
  rcases le_total 0 (u y - u x) with ht | ht
  · refine (ENNReal.ofReal_le_ofReal ?_).trans (hu x y)
    nlinarith
  · rw [ENNReal.ofReal_eq_zero.mpr (by nlinarith)]
    exact bot_le

/-- **Domination in the `h`-action-potential form**: the two standard formulations agree. -/
theorem dominated_actionPot_toReal {m : Fin N → ℝ} {h : ℝ} {p : EN E N}
    (hfin : ∀ x : EN E N, actionPot m h x p ≠ ⊤) :
    Dominated m h (fun x => (actionPot m h x p).toReal) := by
  intro x y
  by_cases hxy : actionPot m h x y = ⊤
  · rw [hxy]; exact le_top
  · have htri : actionPot m h y p ≤ actionPot m h x y + actionPot m h x p := by
      have htri0 := actionPot_triangle m h y x p
      rwa [actionPot_comm m h y x] at htri0
    have h1 : (actionPot m h y p).toReal
        ≤ (actionPot m h x y).toReal + (actionPot m h x p).toReal := by
      have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxy, hfin x⟩) htri
      rwa [ENNReal.toReal_add hxy (hfin x)] at hmono
    have h2 : (actionPot m h y p).toReal - (actionPot m h x p).toReal
        ≤ (actionPot m h x y).toReal := by linarith
    exact (ENNReal.ofReal_le_ofReal h2).trans ENNReal.ofReal_toReal_le

/-- A pointwise limit of dominated functions is dominated. -/
theorem Dominated.of_tendsto {m : Fin N → ℝ} {h : ℝ} {u : ℕ → EN E N → ℝ} {U : EN E N → ℝ}
    (hu : ∀ n, Dominated m h (u n))
    (hconv : ∀ x : EN E N, Tendsto (fun n => u n x) atTop (𝓝 (U x))) :
    Dominated m h U := by
  intro x y
  by_cases hxy : actionPot m h x y = ⊤
  · rw [hxy]; exact le_top
  · have hle : ∀ n, u n y - u n x ≤ (actionPot m h x y).toReal :=
      fun n => (ENNReal.ofReal_le_iff_le_toReal hxy).mp (hu n x y)
    have hlim : Tendsto (fun n => u n y - u n x) atTop (𝓝 (U y - U x)) :=
      (hconv y).sub (hconv x)
    have hfinal : U y - U x ≤ (actionPot m h x y).toReal :=
      le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hle
    exact (ENNReal.ofReal_le_ofReal hfinal).trans ENNReal.ofReal_toReal_le

end Submission.NBody
