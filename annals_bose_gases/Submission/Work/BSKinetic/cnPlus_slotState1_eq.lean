import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

open MeasureTheory
open scoped ContDiff Topology Real BigOperators
open Submission.BoseGases

set_option autoImplicit false

/-! `Submission.BoseGases.cnPlus ℓ φ = Σ_{j : Fin 1} ∫_{x ∈ abox 1 ℓ} (aQ ℓ j φ x)²` is the excited
count of a one-particle state.  At the slot fibre `slotState1 i Φ r = fun x => Φ (kcInsN n i (x 0, r))`
it must be the mean-free square of the inserted fibre over the centred cube — this is the `N = 1`
term that pairs with `Work.BSKinetic.cnPlus_eq_slotSum` to decompose `cnPlus ℓ Φ` over slots.

Route: `φ x = Φ (kcInsN n i (x 0, r))` and `φ (update x 0 y) = Φ (kcInsN n i (y, r))` definitionally;
`Σ_{j : Fin 1}` is a single term; the only real step is that the pushforward of
`volume.restrict (abox 1 ℓ)` under `x ↦ x 0` is `volume.restrict (acube ℓ)` (via
`Submission.BoseGases.abox_integral_peel` at `n = 0`, or `MeasurableEquiv.funUnique`). -/

/-- Integrals over the one-particle centred box of a function of the single coordinate `x 0`
equal integrals over the centred cube: the pushforward of `volume.restrict (abox 1 ℓ)` under
evaluation at the unique index of `Fin 1` is `volume.restrict (acube ℓ)`.  (This is
`Work.MGroupInput.integral_abox_one`, restated in the vocabulary of this chapter.) -/
lemma integral_abox1_eval {ℓ : ℝ} (g : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x in abox 1 ℓ, g (x 0)) = ∫ z in acube ℓ, g z :=
  Work.MGroupInput.integral_abox_one ℓ g

theorem cnPlus_slotState1_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    Submission.BoseGases.cnPlus ℓ (Work.BSKinetic.slotState1 i Φ r)
      = ∫ z in Submission.BoseGases.acube ℓ,
          (Φ (Submission.BoseGases.kcInsN n i (z, r))
            - (ℓ ^ 3)⁻¹ * ∫ w in Submission.BoseGases.acube ℓ,
                Φ (Submission.BoseGases.kcInsN n i (w, r))) ^ 2 := by
  -- the condensate mean `aP ℓ 0 φ` of the fibre is the constant `c`
  set c : ℝ := (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, Φ (kcInsN n i (w, r)) with hc
  have hA : ∀ x : X 1, aP ℓ (0 : Fin 1) (slotState1 i Φ r) x = c := by
    intro x
    rw [hc]
    -- averaging the fibre `y ↦ φ (x_{0←y}) = Φ(x_{i←y})` returns the inserted fibre
    have hinner : (∫ y in acube ℓ, slotState1 i Φ r (Function.update x 0 y))
        = ∫ w in acube ℓ, Φ (kcInsN n i (w, r)) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [slotState1]
      rw [Function.update_self]
    simp only [aP, one_div, hinner]
  -- `cnPlus` at `N = 1` is the single slot-`0` term, whose integrand is the mean-free square
  have hmain : cnPlus ℓ (slotState1 i Φ r)
      = ∫ x in abox 1 ℓ, (Φ (kcInsN n i (x 0, r)) - c) ^ 2 := by
    unfold cnPlus
    rw [Fin.sum_univ_one]
    apply integral_congr_ae
    filter_upwards with x
    simp only [aQ, hA x, slotState1]
  -- peel the single coordinate out of the box `abox 1 ℓ`
  rw [hmain, hc]
  exact integral_abox1_eval (fun z => (Φ (kcInsN n i (z, r))
    - (ℓ ^ 3)⁻¹ * ∫ w in acube ℓ, Φ (kcInsN n i (w, r))) ^ 2)

end Work.BSKinetic
