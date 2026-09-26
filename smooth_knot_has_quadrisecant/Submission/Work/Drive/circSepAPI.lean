import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs

/-!
# The circular-separation API

Elementary facts about `Work.Drive.circSep` (the distance of two parameters on the knot circle),
shared by the assemblies of the generic reduction.
-/

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Topology

noncomputable section

lemma circSep_comm (x y : ℝ) : circSep x y = circSep y x :=
  dist_comm _ _

lemma continuous_circSep : Continuous (fun p : ℝ × ℝ => circSep p.1 p.2) :=
  (((AddCircle.continuous_mk' period).comp continuous_fst).dist
    ((AddCircle.continuous_mk' period).comp continuous_snd))

/-- **Positive circular separation gives distinct classes.** -/
lemma circSep_pos_ne {x y : ℝ} (h : 0 < circSep x y) :
    (x : AddCircle period) ≠ (y : AddCircle period) :=
  dist_pos.mp h

lemma SpreadQuad.quadDistinct {δ x y z w : ℝ} (hδ : 0 < δ) (h : SpreadQuad δ x y z w) :
    QuadDistinct (x : KnotParam) (y : KnotParam) (z : KnotParam) (w : KnotParam) := by
  obtain ⟨_, _, _, _, hxy, hxz, hxw, hyz, hyw, hzw⟩ := h
  exact ⟨circSep_pos_ne (lt_of_lt_of_le hδ hxy), circSep_pos_ne (lt_of_lt_of_le hδ hxz),
    circSep_pos_ne (lt_of_lt_of_le hδ hxw), circSep_pos_ne (lt_of_lt_of_le hδ hyz),
    circSep_pos_ne (lt_of_lt_of_le hδ hyw), circSep_pos_ne (lt_of_lt_of_le hδ hzw)⟩

/-- Six positive circular separations give four pairwise distinct classes. -/
lemma quadDistinct_of_circSep {a b z w : ℝ} (hab : 0 < circSep a b) (haz : 0 < circSep a z)
    (haw : 0 < circSep a w) (hbz : 0 < circSep b z) (hbw : 0 < circSep b w)
    (hzw : 0 < circSep z w) :
    QuadDistinct (a : KnotParam) (b : KnotParam) (z : KnotParam) (w : KnotParam) :=
  ⟨circSep_pos_ne hab, circSep_pos_ne haz, circSep_pos_ne haw, circSep_pos_ne hbz,
    circSep_pos_ne hbw, circSep_pos_ne hzw⟩

/-- The classes of a sequence of reals converge when the reals do. -/
lemma tendsto_coe_addCircle {f : ℕ → ℝ} {x : ℝ} (h : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n => (f n : AddCircle period)) atTop (𝓝 (x : AddCircle period)) :=
  (AddCircle.continuous_mk' period).tendsto x |>.comp h

end

end Work.Drive
