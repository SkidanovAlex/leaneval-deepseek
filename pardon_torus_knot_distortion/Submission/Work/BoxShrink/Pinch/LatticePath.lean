import Submission.Work.BoxShrink.Pinch.Bridge
import Submission.Work.BoxShrink.Bubble.Plane.descent

/-!
# The dictionary in the "translate pair" form

`Bridge.lean` reads the winding-span bookkeeping of the pinch in the parameter plane, where the only
notion involved is that of a path realising a lattice shift (`PeriodRealised`, the *periodic* form of
the dictionary).  This module adds the form the two-dimensional arguments actually produce:

  **a continuous path `q : [0,1] → ℝ²` whose image lies over `X` and whose endpoints differ by the
  lattice shift `2π(k,l) ≠ 0` gives an essential loop of `X`.**

This is the exact statement needed to pass from a "chain of pieces of the plane joining `q` to
`q + λ`" — the shape of every routing argument about the slice — to an essential loop of the surface.
It is a short corollary of the sibling chapter's `Work.BoxShrink.Bubble.Plane.descent` (which
descends such a path to a closed curve of the torus with the prescribed winding vector) together
with `Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero`.

* `planePreimage_add_period` — the preimage of `X` is invariant under the period lattice;
* `containsEssentialLoop_of_path_shift` — the translate-pair criterion for essentiality.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The preimage of a region is invariant under the period lattice.**  A consequence of
`Phi_add_lattice`, in the shape required by `Work.BoxShrink.Bubble.Plane.descent`. -/
theorem planePreimage_add_period {X : Set R3} :
    ∀ z ∈ planePreimage P X, ∀ a b : ℤ,
      (z.1 + (a : ℝ) * (2 * Real.pi), z.2 + (b : ℝ) * (2 * Real.pi)) ∈ planePreimage P X := by
  intro z hz a b
  simp only [mem_planePreimage, Phi_apply] at hz ⊢
  rw [show P.psi (z.1 + (a : ℝ) * (2 * Real.pi)) (z.2 + (b : ℝ) * (2 * Real.pi)) = P.psi z.1 z.2 from
    Phi_add_int (P := P) a b z.1 z.2]
  exact hz

/-- **A path of the plane joining two points differing by a nonzero lattice shift, and lying over
`X`, realises an essential loop of `X`.**  This is the "translate pair" form of the dictionary:
if two points of `Φ⁻¹ X` differ by a nonzero period and can be joined by a path of `Φ⁻¹ X`, then `X`
carries an essential loop.  (The converse is `Bridge`'s
`not_containsEssentialLoop_iff_forall_periodRealised`.) -/
theorem containsEssentialLoop_of_path_shift {X : Set R3} {k l : ℤ} {q : ℝ → ℝ × ℝ}
    (hq : Continuous q) (h1 : q 1 = q 0 + Work.TorusCover.periodShift (k, l))
    (hne : (k, l) ≠ 0)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, Phi P (q t) ∈ X) :
    P.ContainsEssentialLoop X := by
  let p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ) := ⟨fun t => q t, hq.comp continuous_subtype_val⟩
  have hpV : ∀ t : Set.Icc (0 : ℝ) 1, p t ∈ planePreimage P X := fun t => by
    simpa [p, mem_planePreimage] using hmem t t.2
  have hp1 : (p ⟨1, by norm_num⟩).1 = (p ⟨0, by norm_num⟩).1 + (k : ℝ) * (2 * Real.pi) ∧
      (p ⟨1, by norm_num⟩).2 = (p ⟨0, by norm_num⟩).2 + (l : ℝ) * (2 * Real.pi) := by
    have h := h1
    rw [Work.TorusCover.periodShift] at h
    refine ⟨?_, ?_⟩
    · simpa [p] using congrArg Prod.fst h
    · simpa [p] using congrArg Prod.snd h
  obtain ⟨γ, hγmem, hγwind⟩ :=
    Work.BoxShrink.Bubble.Plane.descent (P := P)
      (planePreimage_add_period (P := P) (X := X)) p hpV hp1
  refine ⟨γ, ?_, ?_⟩
  · rw [Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero, hγwind]
    exact hne
  · intro t
    obtain ⟨z, hz, hzγ⟩ := hγmem t
    rw [← hzγ]
    exact hz

end

end Work.BoxShrink.Pinch
