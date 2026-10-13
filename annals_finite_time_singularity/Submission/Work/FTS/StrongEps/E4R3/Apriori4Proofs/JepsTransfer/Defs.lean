import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/Defs.lean` — the log-coordinate vocabulary of the `IP6`-transfer estimate

The log-coordinate transfer estimate for the Friedrichs mollifier `J_ε` of
`Submission.Work.FTS.StrongEps.Basic` compares the two sides of the level-`k` pairing

  `⟨J_ε f, h⟩_ρ − ⟨f, J_ε h⟩_ρ`,   where `⟨u, v⟩_ρ = ∫_{Quad} ρ · u · v`,

and shows that it is `O(ε) ‖f‖ ‖h‖` **without any derivative loss**.  The mechanism is that in
the log coordinates `(s, ζ) = (log z, log tan θ)` the mollifier is an even convolution over the
plane, so after a change of variables the difference is the integral of `Q(y) − Q(y − p)` times
the two profiles, where `Q = logJac · ρ ∘ Ψ` is the log-coordinate version of the weight.  Every
weight of the pairing (`leafEta`, `leafOne`, `leafGam α = slotW α a`) is log-Lipschitz, which is
what makes the difference `O(|p|)` *without* differentiating the profiles.

This module collects the two definitions shared by the pieces of the argument:

* `logPull g` — the profile `g` pulled back to the log coordinates `(s,ζ)` by `Ψ`;
* `logW w` — the leaf weight `w` together with the Jacobian `logJac` of the substitution, i.e.
  the density of the quadrant measure `dz dθ` w.r.t. `ds dζ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The map `Ψ(s,ζ) = (e^s, arctan (e^ζ))` from the log plane onto the open quadrant. -/
def logPsi (y : ℝ × ℝ) : ℝ × ℝ := (Real.exp y.1, Real.arctan (Real.exp y.2))

/-- The pull-back of a profile to the log coordinates `(s,ζ) = (log z, log tan θ)`:
`logPull g s ζ = g (e^s) (arctan (e^ζ))`. -/
def logPull (g : Fn) : ℝ × ℝ → ℝ := fun y => g (Real.exp y.1) (Real.arctan (Real.exp y.2))

/-- The log-coordinate density of a leaf weight `w`: the quadrant weight `w(z,θ)` multiplied by
the Jacobian `logJac` of the substitution `(z,θ) = Ψ(s,ζ)`.  This is the function against which
the pulled-back pairings are integrated on the plane. -/
def logW (w : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
    * w (Real.exp y.1) (Real.arctan (Real.exp y.2))

/-- The log-coordinate pairing `∫_y Q y · G₁ y · G₂ y`, with `Q = logW w` the pulled-back
weight; it is the plane integral into which `slotPairing w a b` turns. -/
def logPair (Q : ℝ × ℝ → ℝ) (G₁ G₂ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ y : ℝ × ℝ, Q y * G₁ y * G₂ y

@[simp] theorem logPsi_apply (y : ℝ × ℝ) :
    logPsi y = (Real.exp y.1, Real.arctan (Real.exp y.2)) := rfl

@[simp] theorem logPull_apply (g : Fn) (y : ℝ × ℝ) :
    logPull g y = g (Real.exp y.1) (Real.arctan (Real.exp y.2)) := rfl

@[simp] theorem logW_apply (w : ℝ → ℝ → ℝ) (y : ℝ × ℝ) :
    logW w y = Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
      * w (Real.exp y.1) (Real.arctan (Real.exp y.2)) := rfl

@[simp] theorem logPair_apply (Q : ℝ × ℝ → ℝ) (G₁ G₂ : ℝ × ℝ → ℝ) :
    logPair Q G₁ G₂ = ∫ y : ℝ × ℝ, Q y * G₁ y * G₂ y := rfl

theorem logPsi_exp_pos (y : ℝ × ℝ) : 0 < (logPsi y).1 := Real.exp_pos y.1

theorem logPsi_mem (y : ℝ × ℝ) :
    (logPsi y).2 ∈ Set.Ioo 0 (π / 2) :=
  ⟨Real.arctan_pos.mpr (Real.exp_pos y.2),
    Real.arctan_lt_pi_div_two (Real.exp y.2)⟩

theorem logPsi_mem_quad (y : ℝ × ℝ) : logPsi y ∈ Work.FTS.StrongEps.Quad :=
  Work.FTS.StrongEps.mem_Quad.mpr ⟨Real.exp_pos y.1, logPsi_mem y⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
