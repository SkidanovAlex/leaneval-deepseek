import Mathlib
import Submission.Work.EQ.SymDefs

/-! Symmetry of Rychlik's equichordal map `T = chordMap O₁ ∘ chordMap O₂` under complex
conjugation and under central reflection.  Writing `O₁ = -a/2` and `O₂ = a/2` for the two
foci (which are real, and satisfy `O₂ = -O₁`), the two elementary identities for the chord
involution are

* `chordMap (star c) (star P) = star (chordMap c P)`  (conjugation commutes),
* `chordMap (-c) (-P) = - chordMap c P`               (reflection anti-commutes),

from which the three stated identities for `eqT a` follow immediately. -/

namespace Work.EQ

open Complex

/-- The chord involution commutes with complex conjugation. -/
lemma chordMap_star (c P : ℂ) : chordMap (star c) (star P) = star (chordMap c P) := by
  simp only [chordMap]
  rw [show star P - star c = star (P - c) by simp, norm_star]
  simp

/-- The chord involution anti-commutes with central reflection. -/
lemma chordMap_neg (c P : ℂ) : chordMap (-c) (-P) = - chordMap c P := by
  simp only [chordMap]
  rw [show -P - -c = -(P - c) by ring, norm_neg]
  ring

theorem eqT_reflections (a : ℝ) :
    (∀ z : ℂ, eqT a (star z) = star (eqT a z)) ∧
    (∀ z : ℂ, eqT a (-z) = -(chordMap (O2_sym a) (chordMap (O1_sym a) z))) ∧
    (∀ z : ℂ, eqT a (-(star z)) = -(star (chordMap (O2_sym a) (chordMap (O1_sym a) z)))) := by
  have hO1 : star (O1_sym a) = O1_sym a := by simp [O1_sym]
  have hO2 : star (O2_sym a) = O2_sym a := by simp [O2_sym]
  have hO2neg : O2_sym a = -(O1_sym a) := by simp [O1_sym, O2_sym]
  have hstar1 : ∀ w : ℂ, chordMap (O1_sym a) (star w) = star (chordMap (O1_sym a) w) :=
    fun w => by simpa only [hO1] using chordMap_star (O1_sym a) w
  have hstar2 : ∀ w : ℂ, chordMap (O2_sym a) (star w) = star (chordMap (O2_sym a) w) :=
    fun w => by simpa only [hO2] using chordMap_star (O2_sym a) w
  have hneg1 : ∀ w : ℂ, chordMap (O2_sym a) (-w) = - chordMap (O1_sym a) w := fun w => by
    rw [hO2neg]; exact chordMap_neg (O1_sym a) w
  have hneg2 : ∀ w : ℂ, chordMap (O1_sym a) (-w) = - chordMap (O2_sym a) w := fun w => by
    rw [show O1_sym a = -(O2_sym a) by rw [hO2neg]; ring]; exact chordMap_neg (O2_sym a) w
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simp only [eqT]
    rw [hstar2 z, hstar1 (chordMap (O2_sym a) z)]
  · intro z
    simp only [eqT]
    rw [hneg1 z, hneg2 (chordMap (O1_sym a) z)]
  · intro z
    simp only [eqT]
    rw [hneg1 (star z), hstar1 z, hneg2 (star (chordMap (O1_sym a) z)),
        hstar2 (chordMap (O1_sym a) z)]

end Work.EQ
