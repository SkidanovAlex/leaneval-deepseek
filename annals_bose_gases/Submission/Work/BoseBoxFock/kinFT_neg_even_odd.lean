import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.farEven_le_uniformBound
import Submission.Work.BoseBoxFock.farImageSum_eq_integral_farEven
import Submission.Work.BoseBoxFock.farImage_lift_tendsto
import Submission.Work.BoseBoxFock.kinFirst_le_of_heatSpec_closed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kinFT_neg_even_odd` — parity of the `p`-convention Fourier transform

The `p`-convention Fourier transform of `Submission.Work.SmallBoxBridge.Defs` is

    `kinFT u p = ∫_y e^{−i⟪p,y⟫} u(y) dy`

(`Submission.BoseGases.kinFT`).  The argument `p ↦ −p` may be undone by the *measure preserving*
substitution `y ↦ −y` (the Lebesgue measure on `EuclideanSpace ℝ (Fin 3)` is invariant under
negation), which yields the exact identity

    `kinFT u (−p) = kinFT (fun y => u (−y)) p`            (`kinFT_neg_eq`)

— no smoothness, support or integrability hypothesis is needed, the Bochner integral absorbing
everything.  Consequently the parity of `u` is inherited by `kinFT u`:

* `u` even (`u(−x) = u x`)  ⟹  `kinFT u` even,
* `u` odd  (`u(−x) = −u x`) ⟹  `kinFT u` odd.

This is the parity input for the even/odd reduction of the anisotropy budget
(`Submission/Work/BoseBoxFock/anisoSplitDefs.lean`, `evenPart`/`oddPart`): the anisotropy pairing
`anisoPair ℓ ·` and the kinetic content `kinFirst ·` are functions of `a ↦ ‖kinFT a‖`, and the
claims above are what let the even and odd parts be treated separately.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Change of variables `p ↦ −p` for `kinFT`**: negating the frequency is the same as negating
the argument of the function. -/
lemma kinFT_neg_eq (u : E3 → ℂ) (p : E3) :
    Submission.BoseGases.kinFT u (-p) = Submission.BoseGases.kinFT (fun y => u (-y)) p := by
  rw [Submission.BoseGases.kinFT, Submission.BoseGases.kinFT]
  rw [← MeasureTheory.integral_neg_eq_self (fun y : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ (-p) y : ℂ))) * u y) (volume : Measure E3)]
  apply integral_congr_ae
  filter_upwards with y
  simp

theorem kinFT_neg_even_odd {e o : EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ x, e (-x) = e x) (ho : ∀ x, o (-x) = - o x) :
    (∀ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinFT e (-p) = Submission.BoseGases.kinFT e p) ∧
      (∀ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinFT o (-p) = - Submission.BoseGases.kinFT o p) := by
  constructor
  · intro p
    rw [kinFT_neg_eq]
    congr 1
    funext y
    exact he y
  · intro p
    rw [kinFT_neg_eq]
    have h1 : (fun y => o (-y)) = fun y => -(o y) := funext ho
    rw [h1]
    simp only [Submission.BoseGases.kinFT, mul_neg, integral_neg]

end Work.BoseBoxFock
