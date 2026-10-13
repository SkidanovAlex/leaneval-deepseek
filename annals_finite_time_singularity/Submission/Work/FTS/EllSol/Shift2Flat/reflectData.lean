import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.SpecAux.timFlipData
import Submission.Work.FTS.EllSol.SpecAux.timFlipIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set
open scoped Real

/-! ## Pointwise derivative identities for the time reversal `t ↦ -t`

For `w = (t,θ) ↦ u (-t) θ` (the time reversal of the datum `u`) the partial derivatives obey

* `∂_t w (t,θ) = - ∂_t u (-t,θ)` (one sign flip),
* `∂_t² w (t,θ) = ∂_t²u (-t,θ)`   (two sign flips, hence none),
* `∂_θ w (t,θ) = ∂_θ u (-t,θ)` and `∂_θ² w (t,θ) = ∂_θ²u (-t,θ)`.

None of these needs a regularity hypothesis: `deriv` is total and `deriv_comp_neg` is
unconditional, and the `θ`-identities are definitional.  This is what turns each slot of the
reflected data into the time-reversal of the corresponding slot of the original datum, so that
the (measure preserving, see `SpecAux.timFlipIntegral`) reflection `(t,θ) ↦ (-t,θ)` transfers
the hypotheses to the conclusions. -/

/-- `∂_t` of the time-reversed datum picks up a sign. -/
theorem pz_timeReflect (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    Work.Spaces.pz (fun t θ => u (-t) θ) t θ = -Work.Spaces.pz u (-t) θ := by
  simp only [Work.Spaces.pz]
  exact deriv_comp_neg (f := fun s => u s θ) (x := t)

/-- `∂_t²` of the time-reversed datum does not pick up a sign (the two sign flips cancel). -/
theorem pz_pz_timeReflect (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    Work.Spaces.pz (Work.Spaces.pz (fun t θ => u (-t) θ)) t θ
      = Work.Spaces.pz (Work.Spaces.pz u) (-t) θ := by
  have hfun : (fun s => Work.Spaces.pz (fun t θ => u (-t) θ) s θ)
      = fun s => -(fun a => Work.Spaces.pz u a θ) (-s) := by
    funext s
    exact pz_timeReflect u s θ
  show deriv (fun s => Work.Spaces.pz (fun t θ => u (-t) θ) s θ) t
      = deriv (fun a => Work.Spaces.pz u a θ) (-t)
  rw [hfun]
  have hneg : deriv (fun s => -(fun a => Work.Spaces.pz u a θ) (-s)) t
      = -deriv (fun s => (fun a => Work.Spaces.pz u a θ) (-s)) t := deriv.neg
  have hcomp : deriv (fun s => (fun a => Work.Spaces.pz u a θ) (-s)) t
      = -deriv (fun a => Work.Spaces.pz u a θ) (-t) :=
    deriv_comp_neg (fun a => Work.Spaces.pz u a θ) t
  rw [hneg, hcomp, neg_neg]

/-- `∂_θ` of the time-reversed datum is the time-reversal of `∂_θu` (the reversal acts on the
first variable only). -/
theorem pth_timeReflect (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    Work.Spaces.pth (fun t θ => u (-t) θ) t θ = Work.Spaces.pth u (-t) θ := rfl

/-- `∂_θ²` of the time-reversed datum is the time-reversal of `∂_θ²u`. -/
theorem pth_pth_timeReflect (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    Work.Spaces.pth (Work.Spaces.pth (fun t θ => u (-t) θ)) t θ
      = Work.Spaces.pth (Work.Spaces.pth u) (-t) θ := rfl

/-- The reflection `(t,θ) ↦ (-t,θ)` transfers `IntegrableOn`-ness on the strip
`univ ×ˢ Iθ` to the reflected function (specialisation of `SpecAux.timFlipIntegral`). -/
theorem integrableOn_timeReflect {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F (-p.1, p.2))
      (Set.univ ×ˢ Work.Spaces.Iθ) :=
  (Work.FTS.EllSol.SpecAux.timFlipIntegral F hF).1

/-- **Time reflection of the data.**

Given `u` with the three `σ_η`-weighted slots of `(∂_t - b)u` finite on the strip
`ℝ × Iθ`, the time-reversed datum `(t,θ) ↦ u (-t) θ` satisfies the same hypotheses with
parameter `-b`: the operator `∂_t - b` becomes `-(∂_t + b)`, and since all slots are
*squares* the reflection transports them; the reflection also preserves the `C²`-regularity on
the open strip and the two boundary values. -/
theorem reflectData (b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ))
    (hZ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
          + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ContDiffOn ℝ 2 (Function.uncurry (fun t θ => u (-t) θ))
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ t : ℝ, (fun t θ => u (-t) θ) t 0 = 0) ∧
      (∀ t : ℝ, (fun t θ => u (-t) θ) t (Real.pi / 2) = 0) ∧
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
          - (-b) * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
          - 2 * (-b) * Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
          + (-b) ^ 2 * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (fun t θ => u (-t) θ)) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- joint `C²`-regularity is preserved by the (smooth, strip preserving) reversal
    have hfun : Function.uncurry (Work.FTS.EllSol.SpecAux.timFlip u)
        = Function.uncurry (fun t θ => u (-t) θ) := rfl
    rw [← hfun]
    exact Work.FTS.EllSol.SpecAux.timFlip_strip_contDiffOn u hu
  · intro t
    simpa using h0 (-t)
  · intro t
    simpa using hπ (-t)
  · -- `(∂_t + b)w` slot: the reflection of the `(∂_t - b)u` slot
    have h1 := integrableOn_timeReflect hV
    have heq : (fun p : ℝ × ℝ =>
          (Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
            - (-b) * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ =>
          (Work.Spaces.pz u (-p.1) p.2 - b * u (-p.1) p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2 := by
      funext p
      rw [pz_timeReflect u p.1 p.2]
      ring
    rw [heq]
    exact h1
  · -- `(∂_t + b)²w` slot: the reflection of the `(∂_t - b)²u` slot
    have h2 := integrableOn_timeReflect hZ
    have heq : (fun p : ℝ × ℝ =>
          (Work.Spaces.pz (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - 2 * (-b) * Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
            + (-b) ^ 2 * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ =>
          (Work.Spaces.pz (Work.Spaces.pz u) (-p.1) p.2
            - 2 * b * Work.Spaces.pz u (-p.1) p.2 + b ^ 2 * u (-p.1) p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2 := by
      funext p
      rw [pz_pz_timeReflect u p.1 p.2, pz_timeReflect u p.1 p.2]
      ring
    rw [heq]
    exact h2
  · -- `∂_θ²w` slot: the reversal acts on `t` only, so this is the reflection of the
    -- `∂_θ²u` slot verbatim
    have h3 := integrableOn_timeReflect hQ
    have heq : (fun p : ℝ × ℝ =>
          (Work.Spaces.pth (Work.Spaces.pth (fun t θ => u (-t) θ)) p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ =>
          (Work.Spaces.pth (Work.Spaces.pth u) (-p.1) p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2 := by
      funext p
      rw [pth_pth_timeReflect u p.1 p.2]
    rw [heq]
    exact h3

end Work.FTS.EllSol.Shift2Flat
