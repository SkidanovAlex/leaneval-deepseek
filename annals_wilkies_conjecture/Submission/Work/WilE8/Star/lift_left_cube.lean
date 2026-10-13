/-
  WilE8 / Star — `lift_left_cube`: a `Star`-set lifted cylindrically along `Fin.tail` and cut
  by the cube is again a `Star`-set, of format `F+1` and the same degree.

  The cylinder over `Z ⊆ ℝⁿ` in the coordinates `1, …, n` is `{z : ℝⁿ⁺¹ | Fin.tail z ∈ Z}`;
  the target intersects it with `cubeC (n+1)`, which is automatic for the `tail` part but not
  for the new coordinate `z 0`.  The new coordinate is free inside `[-1,1]`, which is exactly
  what the cube provides, so no new complexity is needed: the semi-Pfaffian data is merely
  extended along the injection `shiftInj` (new coordinate at position `0`), the degree is
  unchanged, the format grows by one, and the connected components of the extended set are
  the cylinders over the connected components of the original one.
-/
import Mathlib
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.eaEval_extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Extend.semipf_deg_extend
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Star.LiftDefs
import Submission.Work.WilE8.Star.cylinder_component
import Submission.Work.WilE8.Star.projFirst_cylinder

set_option autoImplicit false

namespace Work.WilE8.Star

open WilkiesDesign

/-- The point set of the extended semi-Pfaffian set: the cylinder over `P.X.set` along
`tailM`, cut by the cube. -/
lemma liftPiece_X_set {n : ℕ} (P : WilkiesDesign.E.StarPiece n) :
    (Work.WilE8.SemiPf.extend (Work.WilE8.shiftInj n P.m) P.X).set
      = {x : Fin ((n + 1) + P.m) → ℝ | tailM n P.m x ∈ P.X.set} ∩
        WilkiesDesign.E.cubeC ((n + 1) + P.m) := by
  rw [Work.WilE8.Extend.semipf_set_extend (shiftInj_injective n P.m) P.X]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hc, hw⟩
    exact ⟨by simpa only [comp_shiftInj n P.m x] using hw, hc⟩
  · rintro ⟨hw, hc⟩
    exact ⟨hc, by simpa only [comp_shiftInj n P.m x] using hw⟩

/-- The format of the lift grows by exactly one. -/
lemma liftPiece_fmt {n : ℕ} (P : WilkiesDesign.E.StarPiece n) :
    (liftPiece P).X.fmt = P.X.fmt + 1 := by
  show ((n + 1) + P.m) + P.X.r = (n + P.m) + P.X.r + 1
  omega

/-- The degree of the lift is unchanged. -/
lemma liftPiece_deg {n : ℕ} (P : WilkiesDesign.E.StarPiece n) :
    (liftPiece P).X.deg = P.X.deg := by
  show (Work.WilE8.SemiPf.extend (Work.WilE8.shiftInj n P.m) P.X).deg = P.X.deg
  exact Work.WilE8.Extend.semipf_deg_extend (shiftInj_injective n P.m) P.X

/-- The point set of the lifted piece: the cylinder over `P.set`, cut by the cube. -/
lemma liftPiece_set {n : ℕ} (P : WilkiesDesign.E.StarPiece n) :
    (liftPiece P).set = {z : Fin (n + 1) → ℝ |
        z ∈ WilkiesDesign.E.cubeC (n + 1) ∧ Fin.tail z ∈ P.set} := by
  have hS : P.X.set ⊆ WilkiesDesign.E.cubeC (n + P.m) :=
    Work.WilE8.SemiPf.set_subset_cube P.X
  have hW : connectedComponentIn P.X.set P.p ⊆ WilkiesDesign.E.cubeC (n + P.m) :=
    fun x hx => hS (connectedComponentIn_subset P.X.set P.p hx)
  show WilkiesDesign.E.projFirst (n + 1) P.m ''
      connectedComponentIn (Work.WilE8.SemiPf.extend (Work.WilE8.shiftInj n P.m) P.X).set
        (liftPt n P.m P.p)
    = {z : Fin (n + 1) → ℝ | z ∈ WilkiesDesign.E.cubeC (n + 1) ∧ Fin.tail z ∈ P.set}
  rw [liftPiece_X_set P, cylinder_component hS P.p]
  have hset : {x : Fin ((n + 1) + P.m) → ℝ |
        x ∈ ({x : Fin ((n + 1) + P.m) → ℝ | tailM n P.m x ∈ P.X.set} ∩
              WilkiesDesign.E.cubeC ((n + 1) + P.m)) ∧
        tailM n P.m x ∈ connectedComponentIn P.X.set P.p}
      = ({x : Fin ((n + 1) + P.m) → ℝ | tailM n P.m x ∈ connectedComponentIn P.X.set P.p}
          ∩ WilkiesDesign.E.cubeC ((n + 1) + P.m)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨-, hxB⟩, hxW⟩
      exact ⟨hxW, hxB⟩
    · rintro ⟨hxW, hxB⟩
      exact ⟨⟨connectedComponentIn_subset P.X.set P.p hxW, hxB⟩, hxW⟩
  rw [hset, projFirst_cylinder hW, WilkiesDesign.E.StarPiece.set]

/-- Membership in `⋃ P ∈ L, (liftPiece P).set`, spelled out. -/
lemma mem_iUnion_lift {n : ℕ} {L : List (WilkiesDesign.E.StarPiece n)} {z : Fin (n + 1) → ℝ} :
    (z ∈ ⋃ P ∈ L, (liftPiece P).set) ↔ ∃ P, P ∈ L ∧ z ∈ (liftPiece P).set := by
  simp only [Set.mem_iUnion, exists_prop]

/-- The union over `L.map (fun P => liftPiece P)` is the union over `L` of the lifted pieces. -/
lemma iUnion_map_eq {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)) :
    (⋃ Q ∈ L.map (fun P => liftPiece P), Q.set) = ⋃ P ∈ L, (liftPiece P).set := by
  ext z
  constructor
  · intro hz
    rw [Work.WilE8.mem_list_iUnion] at hz
    obtain ⟨Q, hQ, hzQ⟩ := hz
    rw [List.mem_map] at hQ
    obtain ⟨P, hP, rfl⟩ := hQ
    exact mem_iUnion_lift.mpr ⟨P, hP, hzQ⟩
  · intro hz
    rw [mem_iUnion_lift] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    exact (Work.WilE8.mem_list_iUnion).mpr
      ⟨liftPiece P, List.mem_map.mpr ⟨P, hP, rfl⟩, hzP⟩

/-- The union of the lifted pieces is the cylinder over the union, cut by the cube. -/
lemma iUnion_liftPiece {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)) :
    (⋃ P ∈ L, (liftPiece P).set)
      = {z : Fin (n + 1) → ℝ | Fin.tail z ∈ ⋃ P ∈ L, P.set} ∩
        WilkiesDesign.E.cubeC (n + 1) := by
  ext z
  constructor
  · intro hz
    rw [mem_iUnion_lift] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    rw [liftPiece_set P] at hzP
    change z ∈ WilkiesDesign.E.cubeC (n + 1) ∧ Fin.tail z ∈ P.set at hzP
    obtain ⟨hzcube, hzp⟩ := hzP
    rw [Set.mem_inter_iff]
    exact ⟨(Work.WilE8.mem_list_iUnion).mpr ⟨P, hP, hzp⟩, hzcube⟩
  · intro hz
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hzZ, hzcube⟩ := hz
    change Fin.tail z ∈ ⋃ P ∈ L, P.set at hzZ
    rw [Work.WilE8.mem_list_iUnion] at hzZ
    obtain ⟨P, hP, hzp⟩ := hzZ
    refine mem_iUnion_lift.mpr ⟨P, hP, ?_⟩
    rw [liftPiece_set P]
    exact ⟨hzcube, hzp⟩

theorem lift_left_cube {F D n : ℕ} {Z : Set (Fin n → ℝ)} (h : WilkiesDesign.E.Star F D n Z) :
    WilkiesDesign.E.Star (F + 1) D (n + 1)
      ({z : Fin (n + 1) → ℝ | Fin.tail z ∈ Z} ∩ WilkiesDesign.E.cubeC (n + 1)) := by
  obtain ⟨L, hZ, hfmt, hdeg⟩ := h
  refine ⟨L.map (fun P => liftPiece P), ?_, ?_, ?_⟩
  · rw [hZ]
    exact ((iUnion_map_eq L).trans (iUnion_liftPiece L)).symm
  · intro Q hQ
    rw [List.mem_map] at hQ
    obtain ⟨P, hP, rfl⟩ := hQ
    rw [liftPiece_fmt P]
    exact Nat.add_le_add_right (hfmt P hP) 1
  · rw [List.map_map]
    have hcomp : ((fun P : WilkiesDesign.E.StarPiece (n + 1) => P.X.deg) ∘
        (fun P : WilkiesDesign.E.StarPiece n => liftPiece P)) =
        (fun P : WilkiesDesign.E.StarPiece n => P.X.deg) := by
      funext P
      exact liftPiece_deg P
    rw [hcomp]
    exact hdeg

end Work.WilE8.Star
