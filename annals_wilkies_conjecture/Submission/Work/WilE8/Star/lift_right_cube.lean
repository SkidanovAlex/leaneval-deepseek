/-
  WilE8 / Star — `lift_right_cube`: a `Star`-set lifted cylindrically along `Fin.init` and cut
  by the cube is again a `Star`-set, of format `F+1` and the same degree.

  The cylinder over `Z ⊆ ℝⁿ` in the coordinates `0, …, n-1` is `{z : ℝⁿ⁺¹ | Fin.init z ∈ Z}`;
  the target intersects it with `cubeC (n+1)`, which is automatic for the `init` part but not
  for the new coordinate `z n`.  The new coordinate is free inside `[-1,1]`, which is exactly
  what the cube provides, so no new complexity is needed: the semi-Pfaffian data is merely
  extended along the injection `skipInj` (new coordinate at position `n`, i.e. at the end of the
  projected block), the degree is unchanged, the format grows by one, and the connected
  components of the extended set are the cylinders over the connected components of the
  original one.

  The two "cylinder" facts in the middle —
  `isPreconnected_liftCyl` (a cylinder over a preconnected set is preconnected) and
  `connectedComponentIn_liftCyl` (the connected components of a cylinder are the cylinders of
  the connected components) — are the only topological input; everything else is the
  bookkeeping of `SemiPf.extend` / `projFirst` / `Fin.init`.
-/
import Mathlib
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.eaEval_extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Extend.semipf_deg_extend
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.WilE8.Star.projFirst_cyl

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE8.Star

open WilkiesDesign WilkiesDesign.E

/-- Drop the coordinate `n`: `Fin ((n+1)+m) → ℝ` to `Fin (n+m) → ℝ`.  This is the "forget"
map `x ↦ x ∘ skipInj`, whose section is `insCoord`. -/
def initM (n m : ℕ) (x : Fin ((n + 1) + m) → ℝ) : Fin (n + m) → ℝ :=
  fun i => x (Work.WilE8.skipInj n m i)

/-! ## The two cylinder facts -/

/-- A cylinder over a preconnected set, cut by the cube, is preconnected: it is the continuous
image of `C × [-1,1]` under `insCoord`. -/
lemma isPreconnected_liftCyl {n m : ℕ} {C : Set (Fin (n+m) → ℝ)} (hC : IsPreconnected C)
    (hCsub : C ⊆ WilkiesDesign.E.cubeC (n+m)) :
    IsPreconnected ({x : Fin (n + 1 + m) → ℝ |
        (fun i => x (Work.WilE8.skipInj n m i)) ∈ C} ∩
        WilkiesDesign.E.cubeC (n + 1 + m)) := by
  have himg : ({x : Fin (n + 1 + m) → ℝ |
        (fun i => x (Work.WilE8.skipInj n m i)) ∈ C} ∩
        WilkiesDesign.E.cubeC (n + 1 + m))
      = (fun p : (Fin (n+m) → ℝ) × ℝ => insCoord n m p.1 p.2) ''
          (C ×ˢ Set.Icc (-1 : ℝ) 1) := by
    ext x
    constructor
    · rintro ⟨hxC, hxcube⟩
      exact ⟨(initM n m x, x (Fin.castAdd m (Fin.last n))),
        ⟨hxC, Set.mem_Icc.mpr (abs_le.mp (hxcube _))⟩, insCoord_self n m x⟩
    · rintro ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
      refine ⟨?_, insCoord_cube n m (hCsub hw) (abs_le.mpr (Set.mem_Icc.mp ht))⟩
      show (fun i => insCoord n m w t (Work.WilE8.skipInj n m i)) ∈ C
      rw [funext (fun i => insCoord_skipInj n m w t i)]
      exact hw
  rw [himg]
  exact (IsPreconnected.prod hC isPreconnected_Icc).image _
    (continuous_insCoord n m).continuousOn

/-- The connected component of the cylinder at `q` is the cylinder over the connected component
of `S` at `p`. -/
lemma connectedComponentIn_liftCyl {n m : ℕ} (X : SemiPf (n+m)) (p : Fin (n+m) → ℝ)
    (q : Fin (n + 1 + m) → ℝ) (hq : ∀ i, q (Work.WilE8.skipInj n m i) = p i)
    (hcube : p ∈ X.set → q ∈ WilkiesDesign.E.cubeC (n + 1 + m)) :
    connectedComponentIn (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set q =
      {x : Fin (n + 1 + m) → ℝ |
        (fun i => x (Work.WilE8.skipInj n m i)) ∈ connectedComponentIn X.set p} ∩
        WilkiesDesign.E.cubeC (n + 1 + m) := by
  have hEset : (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set
      = {y : Fin (n + 1 + m) → ℝ | y ∈ WilkiesDesign.E.cubeC (n + 1 + m) ∧
          (fun i => y (Work.WilE8.skipInj n m i)) ∈ X.set} :=
    Work.WilE8.Extend.semipf_set_extend (skipInj_injective n m) X
  have hπq : (fun i : Fin (n+m) => q (Work.WilE8.skipInj n m i)) = p := funext hq
  by_cases hp : p ∈ X.set
  · have hqcube : q ∈ WilkiesDesign.E.cubeC (n + 1 + m) := hcube hp
    have hqE : q ∈ (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set := by
      rw [hEset]
      exact ⟨hqcube, by rw [hπq]; exact hp⟩
    have hsub : (fun y : Fin (n + 1 + m) → ℝ =>
          fun i => y (Work.WilE8.skipInj n m i)) ''
        (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set ⊆ X.set := by
      rintro y ⟨z, hz, rfl⟩
      rw [hEset] at hz
      exact hz.2
    have hCsub : connectedComponentIn X.set p ⊆ WilkiesDesign.E.cubeC (n + m) :=
      fun y hy => Work.WilE8.SemiPf.set_subset_cube X (connectedComponentIn_subset X.set p hy)
    have hqRHS : q ∈ {x : Fin (n + 1 + m) → ℝ |
        (fun i => x (Work.WilE8.skipInj n m i)) ∈ connectedComponentIn X.set p} ∩
        WilkiesDesign.E.cubeC (n + 1 + m) := by
      refine ⟨?_, hqcube⟩
      show (fun i => q (Work.WilE8.skipInj n m i)) ∈ connectedComponentIn X.set p
      rw [hπq]
      exact mem_connectedComponentIn hp
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hxE : x ∈ (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set :=
        connectedComponentIn_subset _ _ hx
      have hpc : IsPreconnected ((fun y : Fin (n + 1 + m) → ℝ =>
            fun i => y (Work.WilE8.skipInj n m i)) ''
          connectedComponentIn (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set q) :=
        isPreconnected_connectedComponentIn.image _
          ((continuous_pi fun i => continuous_apply (Work.WilE8.skipInj n m i)).continuousOn)
      have hsub2 : (fun y : Fin (n + 1 + m) → ℝ =>
            fun i => y (Work.WilE8.skipInj n m i)) ''
          connectedComponentIn (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set q
          ⊆ X.set :=
        (Set.image_mono (connectedComponentIn_subset
          (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set q)).trans hsub
      have hmem : p ∈ (fun y : Fin (n + 1 + m) → ℝ =>
            fun i => y (Work.WilE8.skipInj n m i)) ''
          connectedComponentIn (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set q :=
        ⟨q, mem_connectedComponentIn hqE, hπq⟩
      have hcc := hpc.subset_connectedComponentIn hmem hsub2
      rw [hEset] at hxE
      exact ⟨hcc ⟨x, hx, rfl⟩, hxE.1⟩
    · refine (isPreconnected_liftCyl (C := connectedComponentIn X.set p)
        isPreconnected_connectedComponentIn hCsub).subset_connectedComponentIn hqRHS ?_
      intro x hx
      rw [hEset]
      exact ⟨hx.2, connectedComponentIn_subset X.set p hx.1⟩
  · have hqE : q ∉ (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).set := by
      rw [hEset]
      rintro ⟨-, hπqmem⟩
      exact hp (by rw [← hπq]; exact hπqmem)
    rw [connectedComponentIn_eq_empty hqE, connectedComponentIn_eq_empty hp]
    ext x
    simp

/-! ## Lifting a `*`-piece -/

/-- The right lift of a `*`-piece: the semi-Pfaffian data is extended along `skipInj`,
which inserts the new coordinate at position `n`; the base point is the insertion of `0`
into `P.p`. -/
def liftPieceI {n : ℕ} (P : StarPiece n) : StarPiece (n + 1) :=
  ⟨P.m, Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n P.m) P.X, insCoord n P.m P.p 0⟩

/-- The point set of the extended semi-Pfaffian set: the cylinder over `P.X.set` along
`initM`, cut by the cube. -/
lemma liftPieceI_X_set {n : ℕ} (P : StarPiece n) :
    (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n P.m) P.X).set
      = {x : Fin ((n + 1) + P.m) → ℝ | initM n P.m x ∈ P.X.set} ∩
        WilkiesDesign.E.cubeC ((n + 1) + P.m) := by
  rw [Work.WilE8.Extend.semipf_set_extend (skipInj_injective n P.m) P.X]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact and_comm

/-- The format of the lift grows by exactly one. -/
lemma liftPieceI_fmt {n : ℕ} (P : StarPiece n) :
    (liftPieceI P).X.fmt = P.X.fmt + 1 := by
  show ((n + 1) + P.m) + P.X.r = (n + P.m) + P.X.r + 1
  omega

/-- The degree of the lift is unchanged. -/
lemma liftPieceI_deg {n : ℕ} (P : StarPiece n) :
    (liftPieceI P).X.deg = P.X.deg := by
  show (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n P.m) P.X).deg = P.X.deg
  exact Work.WilE8.Extend.semipf_deg_extend (skipInj_injective n P.m) P.X

/-- The point set of the lifted piece: the cylinder over `P.set`, cut by the cube. -/
lemma liftPieceI_set {n : ℕ} (P : StarPiece n) :
    (liftPieceI P).set = {z : Fin (n + 1) → ℝ | Fin.init z ∈ P.set} ∩
        WilkiesDesign.E.cubeC (n + 1) := by
  have hS : P.X.set ⊆ WilkiesDesign.E.cubeC (n + P.m) :=
    Work.WilE8.SemiPf.set_subset_cube P.X
  have hC : connectedComponentIn P.X.set P.p ⊆ WilkiesDesign.E.cubeC (n + P.m) :=
    fun x hx => hS (connectedComponentIn_subset P.X.set P.p hx)
  have hq : ∀ i, insCoord n P.m P.p 0 (Work.WilE8.skipInj n P.m i) = P.p i :=
    fun i => insCoord_skipInj n P.m P.p 0 i
  have hcube : P.p ∈ P.X.set → insCoord n P.m P.p 0 ∈ WilkiesDesign.E.cubeC ((n + 1) + P.m) :=
    fun hp => insCoord_cube n P.m (hS hp) (by norm_num)
  show WilkiesDesign.E.projFirst (n + 1) P.m ''
      connectedComponentIn (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n P.m) P.X).set
        (insCoord n P.m P.p 0)
    = {z : Fin (n + 1) → ℝ | Fin.init z ∈ P.set} ∩ WilkiesDesign.E.cubeC (n + 1)
  rw [connectedComponentIn_liftCyl (X := P.X) (p := P.p) (q := insCoord n P.m P.p 0) hq hcube]
  rw [projFirst_cyl hC]
  rw [StarPiece.set]

/-- Membership in `⋃ P ∈ L, (liftPieceI P).set`, spelled out. -/
lemma mem_iUnion_liftI {n : ℕ} {L : List (StarPiece n)} {z : Fin (n + 1) → ℝ} :
    (z ∈ ⋃ P ∈ L, (liftPieceI P).set) ↔ ∃ P, P ∈ L ∧ z ∈ (liftPieceI P).set := by
  simp only [Set.mem_iUnion, exists_prop]

/-- The union over `L.map liftPieceI` is the union over `L` of the lifted pieces. -/
lemma iUnion_map_eqI {n : ℕ} (L : List (StarPiece n)) :
    (⋃ Q ∈ L.map (fun P => liftPieceI P), Q.set) = ⋃ P ∈ L, (liftPieceI P).set := by
  ext z
  constructor
  · intro hz
    rw [Work.WilE8.mem_list_iUnion] at hz
    obtain ⟨Q, hQ, hzQ⟩ := hz
    rw [List.mem_map] at hQ
    obtain ⟨P, hP, rfl⟩ := hQ
    exact mem_iUnion_liftI.mpr ⟨P, hP, hzQ⟩
  · intro hz
    rw [mem_iUnion_liftI] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    exact (Work.WilE8.mem_list_iUnion).mpr
      ⟨liftPieceI P, List.mem_map.mpr ⟨P, hP, rfl⟩, hzP⟩

/-- The union of the lifted pieces is the cylinder over the union, cut by the cube. -/
lemma iUnion_liftPieceI {n : ℕ} (L : List (StarPiece n)) :
    (⋃ P ∈ L, (liftPieceI P).set)
      = {z : Fin (n + 1) → ℝ | Fin.init z ∈ ⋃ P ∈ L, P.set} ∩
        WilkiesDesign.E.cubeC (n + 1) := by
  ext z
  rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro hz
    rw [mem_iUnion_liftI] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    rw [liftPieceI_set P, Set.mem_inter_iff, Set.mem_ofPred_eq] at hzP
    exact ⟨(Work.WilE8.mem_list_iUnion).mpr ⟨P, hP, hzP.1⟩, hzP.2⟩
  · intro hz
    obtain ⟨hzZ, hzcube⟩ := hz
    rw [Work.WilE8.mem_list_iUnion] at hzZ
    obtain ⟨P, hP, hzp⟩ := hzZ
    refine mem_iUnion_liftI.mpr ⟨P, hP, ?_⟩
    rw [liftPieceI_set P, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨hzp, hzcube⟩

theorem lift_right_cube {F D n : ℕ} {Z : Set (Fin n → ℝ)} (h : WilkiesDesign.E.Star F D n Z) :
    WilkiesDesign.E.Star (F + 1) D (n + 1)
      ({z : Fin (n + 1) → ℝ | Fin.init z ∈ Z} ∩ WilkiesDesign.E.cubeC (n + 1)) := by
  obtain ⟨L, hZ, hfmt, hdeg⟩ := h
  refine ⟨L.map (fun P => liftPieceI P), ?_, ?_, ?_⟩
  · rw [hZ]
    exact ((iUnion_map_eqI L).trans (iUnion_liftPieceI L)).symm
  · intro Q hQ
    rw [List.mem_map] at hQ
    obtain ⟨P, hP, rfl⟩ := hQ
    rw [liftPieceI_fmt P]
    exact Nat.add_le_add_right (hfmt P hP) 1
  · rw [List.map_map]
    have hcomp : ((fun P : StarPiece (n + 1) => P.X.deg) ∘
        (fun P : StarPiece n => liftPieceI P)) = (fun P : StarPiece n => P.X.deg) := by
      funext P
      exact liftPieceI_deg P
    rw [hcomp]
    exact hdeg

end Work.WilE8.Star
