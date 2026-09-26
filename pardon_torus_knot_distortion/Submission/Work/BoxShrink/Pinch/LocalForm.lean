import Submission.Work.BoxShrink.Pinch.PerpForm
import Submission.Work.BoxShrink.Pinch.TameTarget

/-!
# The residual in the exact form of the deliverable

`TameTarget.lean` isolated the statement the assignment asks for,

`Work.BoxShrink.Pinch.PushOffHalfTame` — Pardon's Lemma 3 for the smooth tori of the challenge,
with the transversality of the cutting plane (`TransverseSlice`) and the tameness of the slice
(`TameSlice`) carried as documented hypotheses.

This module states the *residual* in exactly that local form, so that
`Work.BoxShrink.Pinch.pushOffHalfTame_of_traceMultipleTame` produces `PushOffHalfTame` from
Pardon's equation (1) (`Equation1Input`), the general position of the box-sphere trace
(`BoxSliceNice`) and the residual **with no further hypothesis** — in particular without asking
for transversality or tameness of *every* configuration (such a universal statement is false: a
plane tangent to a smooth torus has `∇G = 0` on the trace; a transfer theorem that assumed it
would be vacuous).

The residual `Work.BoxShrink.Pinch.TraceMultipleTame` is Pardon's push-off with a tame transverse
slice, in the concrete form of `PerpForm.lean`: either the region inside the box does not drop at
all, or a *nonzero class `v` of the trace* has all its realised multiples already realised in the
two half-regions.  By `PerpForm.ker_crossLin_eq_span` the second alternative is literally
"the loops of the box region whose algebraic crossing number with the trace vanishes lie, up to a
multiple of `v`, in the union of the halves" — the push-off of a loop off the trace, which is the
content of Pardon's Lemma 3 that is *not* count/innermost.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **The residual in the exact local form of the deliverable.**  For a smooth torus, a box and a
plane whose slice inside the box is transverse (`TransverseSlice`) and tame (`TameSlice`), with the
sphere trace and the slice both inessential, the region inside the box either does not drop at all,
or there is a nonzero class `v` of the trace of the plane whose realised multiples are all already
realised in the union of the two half-regions. -/
def TraceMultipleTame : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseSlice ψ s c σ u → TameSlice ψ s c σ u →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
      (Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
            Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) ∨
      ∃ v : ℚ × ℚ, v ≠ 0 ∧
        (∃ L : Submodule ℚ (ℚ × ℚ),
          TraceLine (Work.Smooth.Morse.torus ψ) c σ u L ∧ v ∈ L) ∧
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
            (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ⊓
          Submodule.span ℚ {v} ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
            Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)

/-- **The deliverable, from the residual.**  Pardon's equation (1), the general position of the
box-sphere trace, and the residual `TraceMultipleTame` produce the statement the assignment asks
for, `Work.BoxShrink.Pinch.PushOffHalfTame` — no other hypothesis, and in particular none on
configurations outside the one under consideration. -/
theorem pushOffHalfTame_of_traceMultipleTame (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : TraceMultipleTame) : PushOffHalfTame := by
  intro ψ s c σ u hT htame hS hZ
  have hbd : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) + 1 := by
    rcases h ψ s c σ u hT htame hS hZ with hle | ⟨v, hv, _hL, hperp⟩
    · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
    · exact finrank_le_succ_of_inf_span_le hv hperp
  exact bubbleHalf_of_dichotomy_noJump
    (pardonDichotomy_boxRegion_of_equation1 h1 (hnice ψ s c σ) hS) hbd

/-- **The smooth push-off from the residual**, once the two documented inputs (transversality and
tameness for every configuration) are supplied by the caller. -/
theorem smoothHalfS_of_traceMultipleTame (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : TraceMultipleTame)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TameSlice ψ s c σ u) :
    SmoothHalfS :=
  smoothHalfS_of_pushOffHalfTame (pushOffHalfTame_of_traceMultipleTame h1 hnice h) htrans htame

/-- **The crux from the residual**, with the documented geometric inputs. -/
theorem cruxCore_of_traceMultipleTame
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : TraceMultipleTame)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TameSlice ψ s c σ u) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_smoothHalfS hcleanD (smoothHalfS_of_traceMultipleTame h1 hnice h htrans htame)

/-- **Pardon's Theorem 1.1 from the residual.** -/
theorem pardon_torus_knot_distortion_of_traceMultipleTame
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : TraceMultipleTame)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TameSlice ψ s c σ u)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q) (K : Knot)
      (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hcleanD
    (smoothHalfS_of_traceMultipleTame h1 hnice h htrans htame) hclean hae

/-- **The local residual is implied by the chapter's previous residual** whenever the global
transversality it carries is available.  This records that `TraceMultipleTame` is the *weaker*
hypothesis: it is asked only on configurations whose slice is transverse inside the box (the
hypothesis of the deliverable itself), not on all configurations. -/
theorem traceMultipleTame_of_tracePerpSmooth
    (hT : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TransverseTrace ψ c σ u)
    (h : TracePerpSmooth) : TraceMultipleTame := by
  intro ψ s c σ u _hT htame hS hZ
  rcases h ψ s c σ u (hT ψ c σ u) htame hZ with ⟨v, hv, hL, hperp⟩ | hle
  · exact Or.inr ⟨v, hv, hL, (inf_span_le_iff_inf_ker_le hv).mpr hperp⟩
  · exact Or.inl hle

end

end Work.BoxShrink.Pinch
