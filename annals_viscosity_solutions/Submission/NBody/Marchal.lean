import Submission.NBody.Assembly
import Submission.NBody.ActionTau
import Mathlib

/-!
# Marchal's theorem: the shape of the input, and its reduction to the fixed-time form

**Marchal's theorem** (Marchal 2002; complete proofs by Chenciner and by Ferrario--Terracini) says
that for `dim E ≥ 2` an action-minimising curve of the Newtonian `N`-body problem has **no interior
collisions**.  It is the single deep input of the whole Maderna--Venturelli construction (see
`Submission.NBody.MarchalProperty` in `Assembly.lean`), and this file records its *decomposition*.

## The statement used here

`MarchalProperty m h` is the free-time form needed by the paper:

> an `h`-minimiser of `A_{L+h}` has no interior collisions.

The literature (Marchal, Chenciner, Ferrario--Terracini) states and proves the **fixed-time** form:

> a minimiser of `A_L` over curves of a fixed time `τ = b - a` joining `γ a` to `γ b` has no
> interior collisions.

The two are *equivalent* for our purposes, and the reduction (fixed-time ⟹ free-time) is proved
here as `marchalProperty_of_fixedTime`.  The key point is the identity
`A_{L+h}(γ|[a,b]) = A_L(γ|[a,b]) + h (b-a)` together with
`φ_h(x,y) = ⨅_{τ>0} (φ(x,y,τ) + h τ)` (`actionPot_eq_iInf_actionPotTau`), which shows that an
`h`-minimiser *is* a fixed-time minimiser at its own travel time.

## The proof of the fixed-time form (plan, from the literature)

Following Marchal (and the expositions of Chenciner and of Ferrario--Terracini), suppose `γ` is a
fixed-time minimiser with an interior collision at `t₀`.

1. **Blow-up.**  Rescaling `γ` around `t₀` (space by `λ`, time by `λ^{3/2}`) and passing to a
   subsequence, the rescaled curves converge to a **parabolic collision-ejection trajectory**
   `q̄(t) = t^{2/3} ξ` of the Kepler problem.  (This is the hard analytic part: compactness of the
   rescaled minimisers plus the fact that the limit is a minimiser of the limit problem.)
2. **Marchal's averaging estimate.**  Smearing the colliding particle over a *circle* of radius `ρ`
   centred on the parabolic trajectory, the potential integral strictly decreases:
   `∫₀^∞ [ avg_{|δ|=ρ} ‖t^{2/3}ξ - δ‖⁻¹ - ‖t^{2/3}ξ‖⁻¹ ] dt < 0`.
   In dimension `3` this follows from the harmonicity of `1/‖x‖`; in the plane it is Marchal's
   explicit computation.  The *general* dimension reduces to the planar case by smearing in a
   2-plane containing `ξ` (Ferrario--Terracini, `remark` after their `theorem 5.1`).
   The commons lemmas `Commons.Analysis.Integral.planar_circle_average_parabolic_neg`,
   `integral_inv_sqrt_eq_two_div_max`, `integral_parabolic_average_neg` and
   `integrableOn_parabolic_difference` supply these estimates.
3. **Standard variation.**  Truncate the smearing to a small interval around the collision with a
   smooth cut-off, producing a competitor whose action is *strictly smaller* once
   `ρ` is chosen small — contradicting minimality (the kinetic cost of the cut-off is `O(ρ)` while
   the potential gain is `Θ(√ρ)`, so the gain dominates).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The Lagrangian action with level `h` is the action at level `0` plus `h` times the length of
the time interval. -/
lemma actionOn_eq_actionOn_zero_add {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {h : ℝ} (hh : 0 ≤ h)
    {γ : ℝ → EN E N} {a b : ℝ} :
    actionOn m h γ a b = actionOn m 0 γ a b + ENNReal.ofReal h * ENNReal.ofReal (b - a) := by
  unfold actionOn
  have hpt : ∀ t : ℝ, lagrangian m h (γ t) (deriv γ t)
      = lagrangian m 0 (γ t) (deriv γ t) + ENNReal.ofReal h := by
    intro t
    by_cases hc : WithoutCollisions (γ t)
    · rw [lagrangian, if_pos hc, lagrangian, if_pos hc]
      simp only [add_zero]
      have hKU : 0 ≤ 1 / 2 * ∑ i, m i * ‖(deriv γ t).ofLp i‖ ^ 2 + U m (γ t) :=
        add_nonneg (mul_nonneg (by norm_num)
          (Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _))) (U_nonneg hm (γ t))
      rw [← ENNReal.ofReal_add hKU hh]
    · rw [lagrangian, if_neg hc, lagrangian, if_neg hc, top_add]
  simp only [hpt]
  rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc]

/-- **Marchal's theorem in the fixed-time form of the literature.**  For `dim E ≥ 2`, any curve
minimising the Lagrangian action `A_L` among curves of time `b - a` joining `γ a` to `γ b` has no
interior collisions.  (Stated with our `φ(x,y,τ) = actionPotTau m x y τ`.) -/
def MarchalFixedTime (m : Fin N → ℝ) (h : ℝ) : Prop :=
  ∀ (γ : ℝ → EN E N) (a b : ℝ), a < b →
    actionOn m h γ a b = actionPotTau m (γ a) (γ b) (b - a)
        + ENNReal.ofReal h * ENNReal.ofReal (b - a) →
    ∀ t ∈ Set.Ioo a b, WithoutCollisions (γ t)

/-- **The free-time form of Marchal's theorem follows from the fixed-time form.**  An `h`-minimiser
is a fixed-time minimiser for its own travel time. -/
theorem marchalProperty_of_fixedTime {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hfix : MarchalFixedTime (E := E) m h) : MarchalProperty (E := E) m h := by
  intro γ a b hab hac hmin t ht
  have heq : actionOn m h γ a b = actionPotTau m (γ a) (γ b) (b - a)
      + ENNReal.ofReal h * ENNReal.ofReal (b - a) := by
    have hmin' : actionOn m h γ a b = actionPot m h (γ a) (γ b) := hmin
    have hshift : actionOn m 0 (fun s : ℝ => γ (s + a)) 0 (b - a) = actionOn m 0 γ a b :=
      actionOn_comp_add_const' (m := m) (h := 0) (γ := γ) (c := a) (d := b)
    have hac' : AbsolutelyContinuousOnInterval (fun s : ℝ => γ (s + a)) 0 (b - a) := by
      have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
        (f := γ) (a := a) (b := b) (c := 1) (d := a) one_ne_zero hac
      simpa using h
    refine le_antisymm ?_ ?_
    · rw [hmin', actionPot_eq_iInf_actionPotTau hm hh]
      exact iInf_le (f := fun τ : {τ : ℝ // 0 < τ} =>
        actionPotTau m (γ a) (γ b) τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1)
        ⟨b - a, sub_pos.mpr hab⟩
    · rw [actionOn_eq_actionOn_zero_add hm hh]
      have hφ : actionPotTau m (γ a) (γ b) (b - a) ≤ actionOn m 0 γ a b := by
        refine (actionPotTau_le_of (x := γ a) (y := γ b) (τ := b - a) (γ := fun s : ℝ => γ (s + a))
          ?_ ?_ hac').trans_eq hshift
        · simp
        · rw [sub_add_cancel]
      exact add_le_add hφ le_rfl
  exact hfix γ a b hab heq t ht

end Submission.NBody
