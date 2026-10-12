import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.exists_fibre_bound`

A uniform (in the frozen configuration `r ∈ abox n ℓ`) bound for the slot-`i` fibre
`z ↦ Φ (kcInsN n i (z, r))` of a smooth `(n+1)`-particle state, together with a uniform bound for
its first derivatives along the standard basis directions.

Both bounds are pure compactness: the insertion `kcInsN n i` maps `acube ℓ × abox n ℓ` into the
compact box `abox (n+1) ℓ`, on which a `C^∞` function and its derivative are bounded.  The chain
rule `Submission.BoseGases.fiber_fderiv` identifies the fibre derivative with the master
derivative evaluated on `Function.update 0 i (kcStdBasis k)`, a vector of norm `1`.
-/

noncomputable section

open Submission.BoseGases

set_option autoImplicit false

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Inserting `v` in slot `i` of the zero configuration has the same norm as `v`: the only nonzero
coordinate of `Function.update 0 i v` is the `i`-th, so the sup-norm is `‖v‖`. -/
lemma norm_update_zero (n : ℕ) (i : Fin (n + 1)) (v : ℝ³) :
    ‖Function.update (0 : Submission.BoseGases.X (n + 1)) i v‖ = ‖v‖ := by
  rw [show Function.update (0 : Submission.BoseGases.X (n + 1)) i v = Pi.single i v from rfl,
    Pi.norm_single]

/-- The insertion `kcInsN n i (z, r)` of `z ∈ acube ℓ` into `r ∈ abox n ℓ` lies in `abox (n+1) ℓ`;
coordinatewise, slot `i` receives `z` and every other slot a coordinate of `r`. -/
lemma kcInsN_mem_abox {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) {r : Submission.BoseGases.X n}
    (hr : r ∈ Submission.BoseGases.abox n ℓ) {z : ℝ³}
    (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Submission.BoseGases.kcInsN n i (z, r) ∈ Submission.BoseGases.abox (n + 1) ℓ := by
  intro j
  by_cases hj : j = i
  · subst hj
    rw [Submission.BoseGases.kc_insN_apply_same]
    exact hz
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    rw [Submission.BoseGases.kc_insN_apply_succ]
    exact hr j'

theorem exists_fibre_bound {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ S S1 : ℝ, 0 ≤ S ∧ 0 ≤ S1 ∧
      ∀ (i : Fin (n + 1)) (r : Submission.BoseGases.X n),
        r ∈ Submission.BoseGases.abox n ℓ →
        (∀ z ∈ Submission.BoseGases.acube ℓ,
            |Φ (Submission.BoseGases.kcInsN n i (z, r))| ≤ S) ∧
        (∀ z ∈ Submission.BoseGases.acube ℓ, ∀ k : Fin 3,
          |fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
              Φ (Submission.BoseGases.kcInsN n i (w, r))) z
            (Submission.BoseGases.kcStdBasis k)| ≤ S1) := by
  -- the target box is compact and contains every insertion `kcInsN n i (z, r)`
  have hK : IsCompact (Submission.BoseGases.abox (n + 1) ℓ) :=
    Submission.BoseGases.abox_compact (n + 1) hℓ
  -- bound for `Φ` itself on the box
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuous.continuousOn
  -- bound for the total derivative `fderiv ℝ Φ` on the box
  have hfdcont : Continuous (fun x : Submission.BoseGases.X (n + 1) => fderiv ℝ Φ x) :=
    hΦ.continuous_fderiv (by simp)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hfdcont.continuousOn
  refine ⟨max C 0, max D 0, le_max_right C 0, le_max_right D 0, ?_⟩
  intro i r hr
  constructor
  · intro z hz
    have h1 : ‖Φ (Submission.BoseGases.kcInsN n i (z, r))‖ ≤ C :=
      hC _ (kcInsN_mem_abox i hr hz)
    simpa [Real.norm_eq_abs] using h1.trans (le_max_left C 0)
  · intro z hz k
    -- chain rule: the fibre derivative is the master derivative on a fixed unit vector
    rw [Submission.BoseGases.fiber_fderiv i hΦ r z (Submission.BoseGases.kcStdBasis k)]
    have hL : ‖Function.update (0 : Submission.BoseGases.X (n + 1)) i
        (Submission.BoseGases.kcStdBasis k)‖ = 1 := by
      rw [norm_update_zero, Submission.BoseGases.kcStdBasis]
      simp
    have hop : ‖fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
        (Function.update (0 : Submission.BoseGases.X (n + 1)) i
          (Submission.BoseGases.kcStdBasis k))‖ ≤ D := by
      calc ‖fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
              (Function.update (0 : Submission.BoseGases.X (n + 1)) i
                (Submission.BoseGases.kcStdBasis k))‖
          ≤ ‖fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))‖ *
            ‖Function.update (0 : Submission.BoseGases.X (n + 1)) i
              (Submission.BoseGases.kcStdBasis k)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))‖ := by rw [hL, mul_one]
        _ ≤ D := hD _ (kcInsN_mem_abox i hr hz)
    simpa [Real.norm_eq_abs] using hop.trans (le_max_left D 0)

end Work.BSKinetic
