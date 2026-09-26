import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer A3 — secant directions of the knot

Chords/secants of the knot are parametrized by (unordered) pairs of distinct
points of the parameter circle `AddCircle period`.  This module sets up the
ordered-pair domain and the *secant direction map* (Kuperberg's
`π_L`-style projection)

    secantDir r : OrderedPairs → Space
    secantDir r p = (knotMap r p.1.1 - knotMap r p.1.2) / ‖·‖

It is a continuous unit-vector field over the space of ordered pairs of
distinct parameters, and reversing the two parameters negates it — so it
descends to a map from the (unordered) Möbius strip of secants into the
projective sphere.  Continuity here (`continuous_secantDir`) is the analytic
atom out of which the structure of the trisecant locus will be built.
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- Ordered pairs of distinct points of the parameter circle. -/
abbrev OrderedPairs := {q : AddCircle period × AddCircle period // q.1 ≠ q.2}

/-- `v ↦ ‖v‖⁻¹ • v` (normalization towards the unit sphere), continuous away
from zero. -/
lemma continuousOn_inv_norm_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousOn (fun v : E => (‖v‖)⁻¹ • v) {v : E | v ≠ 0} := by
  intro v hv
  have hcont : ContinuousAt (fun w : E => (‖w‖)⁻¹ • w) v := by
    apply ContinuousAt.smul
    · exact ContinuousAt.inv₀ continuous_norm.continuousAt (by simpa using (norm_ne_zero_iff.mpr hv))
    · exact continuous_id.continuousAt
  exact hcont.continuousWithinAt

/-- Direction of the secant through two distinct points of the knot, as a
unit vector in `Space`. -/
noncomputable def secantDir (r : ℝ → Space) (_hinj : Function.Injective (knotMap r))
    (p : OrderedPairs) : Space :=
  (‖knotMap r p.1.1 - knotMap r p.1.2‖)⁻¹ • (knotMap r p.1.1 - knotMap r p.1.2)

/-- The secant direction depends continuously on the pair of parameters. -/
lemma continuous_secantDir (r : ℝ → Space) (h : IsSmoothKnot r) :
    Continuous (secantDir r (knotMap_injective h)) := by
  have hg : ContinuousOn (fun v : Space => (‖v‖)⁻¹ • v) {v : Space | v ≠ 0} :=
    continuousOn_inv_norm_smul
  let inner : OrderedPairs → Space := fun p => knotMap r p.1.1 - knotMap r p.1.2
  have hf : Continuous inner := by
    have hk : Continuous (knotMap r) := h.knotMap_continuous
    have hc1 : Continuous (fun p : OrderedPairs => (p : AddCircle period × AddCircle period).1) :=
      continuous_fst.comp continuous_subtype_val
    have hc2 : Continuous (fun p : OrderedPairs => (p : AddCircle period × AddCircle period).2) :=
      continuous_snd.comp continuous_subtype_val
    change Continuous (fun p : OrderedPairs => knotMap r ((p : AddCircle period × AddCircle period).1) -
        knotMap r ((p : AddCircle period × AddCircle period).2))
    exact (hk.comp hc1).sub (hk.comp hc2)
  have hs : ∀ p : OrderedPairs, inner p ∈ {v : Space | v ≠ 0} := by
    intro p
    change knotMap r p.1.1 - knotMap r p.1.2 ≠ 0
    exact sub_ne_zero.mpr ((knotMap_injective h).ne p.2)
  have hc := ContinuousOn.comp_continuous hg hf hs
  change Continuous ((fun v : Space => (‖v‖)⁻¹ • v) ∘ inner)
  exact hc

/-- `secantDir` has unit length. -/
lemma norm_secantDir (r : ℝ → Space) (hinj : Function.Injective (knotMap r))
    (p : OrderedPairs) : ‖secantDir r hinj p‖ = 1 := by
  unfold secantDir
  rw [norm_smul]
  have hne : ‖knotMap r p.1.1 - knotMap r p.1.2‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hinj.ne p.2))
  have hnn : 0 ≤ (‖knotMap r p.1.1 - knotMap r p.1.2‖)⁻¹ :=
    inv_nonneg.mpr (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact inv_mul_cancel₀ hne

/-- Swapping the two endpoints of an ordered secant pair. -/
def swapOrdered (p : OrderedPairs) : OrderedPairs :=
  ⟨(p.1.2, p.1.1), fun h => p.2 h.symm⟩

/-- Reversing the endpoints reverses the secant direction. -/
lemma secantDir_swap (r : ℝ → Space) (hinj : Function.Injective (knotMap r))
    (p : OrderedPairs) :
    secantDir r hinj (swapOrdered p) = -secantDir r hinj p := by
  unfold secantDir swapOrdered
  have hn : ‖knotMap r p.1.2 - knotMap r p.1.1‖ = ‖knotMap r p.1.1 - knotMap r p.1.2‖ := by
    exact (norm_sub_rev (knotMap r p.1.1) (knotMap r p.1.2)).symm
  rw [hn]
  rw [← neg_sub (a := knotMap r p.1.1) (b := knotMap r p.1.2)]
  rw [smul_neg]

end LeanEval.KnotTheory.Quadrisecant
