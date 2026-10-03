import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Cayley Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}

/-- The tail of the traversal of a positive generator edge is equivariant. -/
theorem edgeTailPos_smul (D : GeoData T t₀ P) (g a : G) (j : Fin P.n) :
    edgeTailPos D (g * a) j = (edgeTailPos D a j).map (fun v => g • v) := by
  unfold edgeTailPos
  by_cases h : D.L (j, true) = 0
  · rw [if_pos h, if_pos h]
    simp [baseV_smul, mul_assoc]
  · rw [if_neg h, if_neg h]
    rw [List.map_flatMap]
    refine List.flatMap_congr (fun k _ => ?_)
    simp [baseV_smul, midV_smul, pos_smul]

/-- The tail of the traversal of a negative generator edge is equivariant. -/
theorem edgeTailNeg_smul (D : GeoData T t₀ P) (g a : G) (j : Fin P.n) :
    edgeTailNeg D (g * a) j = (edgeTailNeg D a j).map (fun v => g • v) := by
  unfold edgeTailNeg
  dsimp only
  by_cases h : D.L (j, true) = 0
  · rw [if_pos h, if_pos h]
    simp [baseV_smul, mul_assoc]
  · rw [if_neg h, if_neg h]
    rw [List.map_flatMap]
    refine List.flatMap_congr (fun k _ => ?_)
    simp [baseV_smul, midV_smul, pos_smul, mul_assoc]

/-- The tail of the boundary walk is equivariant. -/
theorem faceAux_smul (D : GeoData T t₀ P) (g a : G) (w : List (Fin P.n × Bool)) :
    faceAux D (g * a) w = (faceAux D a w).map (fun v => g • v) := by
  induction w generalizing a with
  | nil => simp
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b
      · simp only [faceAux_false]
        rw [edgeTailNeg_smul, mul_assoc, ih, List.map_append]
      · simp only [faceAux_true]
        rw [edgeTailPos_smul, mul_assoc, ih, List.map_append]

theorem faceWalk_smul {G : Type u} [Group G] {V : Type u} [MulAction G V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (g c : G) (w : List (Fin P.n × Bool)) : Work.ORDunwoody.Dunwoody.faceWalk D (g * c) w = (Work.ORDunwoody.Dunwoody.faceWalk D c w).map (fun v => g • v) := by
  simp only [faceWalk_eq, faceAux_smul]
  simp [baseV_smul]

end Work.ORDunwoody
