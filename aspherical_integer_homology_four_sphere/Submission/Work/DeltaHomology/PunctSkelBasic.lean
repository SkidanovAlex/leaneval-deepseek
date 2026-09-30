import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.barycenter_not_mem_skelSet_of_lt
import Submission.Work.DeltaHomology.exists_collar_punctStdSimplex
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The collar of the `k`-skeleton in the `(k+1)`-skeleton: point-set API

This file collects the point-set part of the proof that the collar
`χ.punctSkel (k+1) = X^{k+1} ∖ {barycentres}` deformation retracts onto `χ.skelSet k`:

* a choice of the radial collar of the boundary of the punctured standard simplex
  (`collarMap`, with its three defining properties);
* the unique open simplex `openSimplexAt` of a point of `X` and its basic API;
* rigidity of characteristic maps on interiors (`openSimplexAt_cls_of_pos`,
  `cls_collarMap_eq_of_cls_eq`), the barycentre criterion `cls_eq_barycenter_iff`
  and the boundary criterion `cls_mem_skelSet_of_exists_zero_weight`, all built on the
  realization axioms and on `Submission/Work/DeltaHomology/eq_of_cls_eq_of_pos`;
* the pointwise radial homotopy `homotopyPt` and the induced map `homotopyFun` on the
  collar, together with its key pointwise properties.

The continuity of `homotopyFun` (which uses the weak topology of the realization) is in
`Submission/Work/DeltaHomology/PunctSkelContinuous.lean`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial unitInterval

namespace Work.DeltaHomology

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K : DeltaCx} {X : TopCat}

/-! ## A choice of the collar of the punctured standard simplex -/

/-- A chosen radial collar of the boundary of the punctured standard simplex: a continuous
map `I × (Δ^k ∖ {barycentre}) → Δ^k ∖ {barycentre}` which is the identity at time `0`, lands on
the boundary at time `1`, and fixes the boundary pointwise. -/
def collarMap (k : ℕ) : C(I × ↥(punctStdSimplex k), ↥(punctStdSimplex k)) :=
  (exists_collar_punctStdSimplex k).choose

theorem collarMap_zero (k : ℕ) (u : ↥(punctStdSimplex k)) : collarMap k (0, u) = u :=
  (exists_collar_punctStdSimplex k).choose_spec.1 u

theorem collarMap_one_mem_boundary (k : ℕ) (u : ↥(punctStdSimplex k)) :
    ((collarMap k (1, u) : ↥(punctStdSimplex k)) : StdSimplex ℝ (Fin (k + 1)))
      ∈ StdSimplexBoundary k :=
  (exists_collar_punctStdSimplex k).choose_spec.2.1 u

theorem collarMap_eq_self_of_boundary (k : ℕ) (u : ↥(punctStdSimplex k))
    (hu : (u : StdSimplex ℝ (Fin (k + 1))) ∈ StdSimplexBoundary k) (t : I) :
    collarMap k (t, u) = u :=
  (exists_collar_punctStdSimplex k).choose_spec.2.2 u hu t

/-! ## The unique open simplex of a point -/

/-- The unique open simplex of `K` which is realized by the point `x`. -/
def DeltaRealization.openSimplexAt (R : DeltaRealization K X) (x : X) : OpenSimplex K :=
  (R.bij x).choose

theorem DeltaRealization.real_openSimplexAt (R : DeltaRealization K X) (x : X) :
    DeltaSimplexMap.real R.toDeltaSimplexMap (R.openSimplexAt x) = x :=
  (R.bij x).choose_spec.1

theorem DeltaRealization.openSimplexAt_eq_iff (R : DeltaRealization K X) (x : X)
    (p : OpenSimplex K) :
    R.openSimplexAt x = p ↔ DeltaSimplexMap.real R.toDeltaSimplexMap p = x :=
  ⟨fun h => h ▸ R.real_openSimplexAt x,
   fun h => (R.bij x).unique (R.real_openSimplexAt x) h⟩

theorem DeltaRealization.real_injective (R : DeltaRealization K X) :
    Function.Injective (DeltaSimplexMap.real R.toDeltaSimplexMap) := by
  intro p q h
  rw [← (R.openSimplexAt_eq_iff (DeltaSimplexMap.real R.toDeltaSimplexMap p) p).mpr rfl,
    ← (R.openSimplexAt_eq_iff (DeltaSimplexMap.real R.toDeltaSimplexMap q) q).mpr rfl, h]

/-- The open simplex of the image of an interior point of a closed simplex is that simplex
with that interior point. -/
theorem DeltaRealization.openSimplexAt_cls_of_pos (R : DeltaRealization K X) {n : ℕ}
    (idx : Fin (K.card n)) {y : StdSimplex ℝ (Fin (n + 1))} (hy : ∀ i, 0 < y.weights i) :
    R.openSimplexAt (R.toDeltaSimplexMap.cls n idx y) = ⟨n, idx, y, hy⟩ :=
  (R.openSimplexAt_eq_iff _ _).mpr rfl

/-! ## The barycentre and boundary criteria -/

/-- A point of a closed `n`-simplex of the realization is the barycentre of an `n`-simplex if
and only if it *is* the barycentre of the simplex `idx` it lies in. -/
theorem DeltaRealization.cls_eq_barycenter_iff (R : DeltaRealization K X) (n : ℕ)
    (idx : Fin (K.card n)) (y : StdSimplex ℝ (Fin (n + 1))) :
    (R.toDeltaSimplexMap.cls n idx y : X) ∈ R.toDeltaSimplexMap.barycenterSet n ↔
      y = simplexBarycenter n := by
  constructor
  · rintro ⟨idx', h'⟩
    obtain ⟨-, hy⟩ := eq_of_cls_eq_of_pos R (isOpenSimplexPoint_simplexBarycenter n) h'
    exact hy.symm
  · rintro rfl
    exact Set.mem_range_self idx

/-- The image of a boundary point of a closed `(n+1)`-simplex lies in the `n`-skeleton. -/
theorem DeltaRealization.cls_mem_skelSet_of_exists_zero_weight (R : DeltaRealization K X)
    (n : ℕ) (idx : Fin (K.card (n + 1))) {y : StdSimplex ℝ (Fin (n + 2))}
    (hy : ∃ i, y.weights i = 0) :
    (R.toDeltaSimplexMap.cls (n + 1) idx y : X) ∈ R.toDeltaSimplexMap.skelSet n := by
  obtain ⟨i, hi⟩ := hy
  obtain ⟨y', hy'⟩ := exists_stdSimplex_map_succAbove_eq i y hi
  have hfac := DeltaSimplexMap.cls_face R.toDeltaSimplexMap idx i y'
  rw [← hy', ← hfac]
  exact DeltaSimplexMap.cls_mem_skelSet _ le_rfl _ _

/-- The image of a point of the punctured standard `n`-simplex under a characteristic map
lies in the collar: it is never a barycentre. -/
theorem DeltaRealization.cls_mem_punctSkel (R : DeltaRealization K X) (n : ℕ)
    (idx : Fin (K.card n)) {y : StdSimplex ℝ (Fin (n + 1))} (hy : y ≠ simplexBarycenter n) :
    (R.toDeltaSimplexMap.cls n idx y : X) ∈ R.toDeltaSimplexMap.punctSkel n :=
  ⟨DeltaSimplexMap.cls_mem_skelSet _ le_rfl idx y,
   fun h => hy ((R.cls_eq_barycenter_iff n idx y).mp h)⟩

theorem DeltaSimplexMap.mem_punctSkel_iff (χ : DeltaSimplexMap K X) (n : ℕ) (x : X) :
    x ∈ χ.punctSkel n ↔ x ∈ χ.skelSet n ∧ x ∉ χ.barycenterSet n := Iff.rfl

/-- The `k`-skeleton is contained in the collar of the `(k+1)`-skeleton. -/
theorem DeltaSimplexMap.skelSet_subset_punctSkel_succ (R : DeltaRealization K X) (k : ℕ) :
    R.toDeltaSimplexMap.skelSet k ⊆ R.toDeltaSimplexMap.punctSkel (k + 1) := by
  intro x hx
  refine ⟨R.toDeltaSimplexMap.skelSet_mono (Nat.le_succ k) hx, ?_⟩
  rintro ⟨idx, hidx⟩
  rw [← hidx] at hx
  exact barycenter_not_mem_skelSet_of_lt R (Nat.lt_succ_self k) idx hx

/-- A point of a characteristic map which lands in the `k`-skeleton comes from a boundary point
of the standard `(k+1)`-simplex. -/
theorem DeltaRealization.boundary_of_cls_mem_skelSet (R : DeltaRealization K X) (k : ℕ)
    (τ : Fin (K.card (k + 1))) {y : StdSimplex ℝ (Fin (k + 2))}
    (hy : (R.toDeltaSimplexMap.cls (k + 1) τ y : X) ∈ R.toDeltaSimplexMap.skelSet k) :
    y ∈ StdSimplexBoundary (k + 1) := by
  by_contra hb
  have hpos : ∀ i, 0 < y.weights i := by
    intro i
    rcases lt_or_eq_of_le (y.weights_nonneg i) with h | h
    · exact h
    · exact absurd ⟨i, h.symm⟩ hb
  have hps := R.openSimplexAt_cls_of_pos τ hpos
  obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R k _).mp hy
  have hpeq : p = (⟨k + 1, τ, y, hpos⟩ : OpenSimplex K) := by
    rw [← (R.openSimplexAt_eq_iff _ p).mpr hp, hps]
  have : p.dim = k + 1 := by rw [hpeq]
  omega

/-- A point of the collar which is not in the `k`-skeleton is the image of a point of the
punctured standard `(k+1)`-simplex. -/
theorem DeltaRealization.exists_cls_eq_of_mem_punctSkel (R : DeltaRealization K X) {k : ℕ}
    {x : X} (hx : x ∈ R.toDeltaSimplexMap.punctSkel (k + 1))
    (hxk : x ∉ R.toDeltaSimplexMap.skelSet k) :
    ∃ (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))),
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) = x := by
  obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R (k + 1) x).mp hx.1
  obtain ⟨d, idx, pt, hpos⟩ := p
  have hd : d = k + 1 := by
    rcases lt_or_eq_of_le hpd with h | h
    · exact absurd ((mem_skelSet_iff R k x).mpr ⟨⟨d, idx, pt, hpos⟩, hp, Nat.lt_succ_iff.mp h⟩) hxk
    · exact h
  subst hd
  refine ⟨idx, ⟨pt, ?_⟩, hp⟩
  intro hb
  exact hx.2 ⟨idx, by rw [← hb]; exact hp⟩

/-- **Fiber compatibility of the collar.**  Two points of punctured standard `(k+1)`-simplices
which are realized to the same point of `X` remain equal after applying the collar: the collar
descends to the realization. -/
theorem DeltaRealization.cls_collarMap_eq_of_cls_eq (R : DeltaRealization K X) (k : ℕ)
    {τ τ' : Fin (K.card (k + 1))} {y y' : ↥(punctStdSimplex (k + 1))}
    (h : R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) =
      R.toDeltaSimplexMap.cls (k + 1) τ' (y' : StdSimplex ℝ (Fin (k + 2)))) (t : I) :
    R.toDeltaSimplexMap.cls (k + 1) τ
        (collarMap (k + 1) (t, y) : StdSimplex ℝ (Fin (k + 2))) =
      R.toDeltaSimplexMap.cls (k + 1) τ'
        (collarMap (k + 1) (t, y') : StdSimplex ℝ (Fin (k + 2))) := by
  by_cases hmem : (R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) : X) ∈
      R.toDeltaSimplexMap.skelSet k
  · have hy := R.boundary_of_cls_mem_skelSet k τ hmem
    have hmem' : (R.toDeltaSimplexMap.cls (k + 1) τ' (y' : StdSimplex ℝ (Fin (k + 2))) : X) ∈
        R.toDeltaSimplexMap.skelSet k := by rw [← h]; exact hmem
    have hy' := R.boundary_of_cls_mem_skelSet k τ' hmem'
    rw [collarMap_eq_self_of_boundary (k + 1) y hy t,
      collarMap_eq_self_of_boundary (k + 1) y' hy' t, h]
  · have hy : ∀ i, 0 < (y : StdSimplex ℝ (Fin (k + 2))).weights i := by
      intro i
      rcases lt_or_eq_of_le ((y : StdSimplex ℝ (Fin (k + 2))).weights_nonneg i) with hlt | heq
      · exact hlt
      · exact absurd (R.cls_mem_skelSet_of_exists_zero_weight k τ ⟨i, heq.symm⟩) hmem
    have hy' : ∀ i, 0 < (y' : StdSimplex ℝ (Fin (k + 2))).weights i := by
      intro i
      rcases lt_or_eq_of_le ((y' : StdSimplex ℝ (Fin (k + 2))).weights_nonneg i) with hlt | heq
      · exact hlt
      · refine absurd ?_ hmem
        rw [h]
        exact R.cls_mem_skelSet_of_exists_zero_weight k τ' ⟨i, heq.symm⟩
    obtain ⟨hτ, hyy⟩ := eq_of_cls_eq_of_pos R hy h
    subst hτ
    rw [show y = y' from Subtype.ext hyy]

/-! ## The radial homotopy -/

/-- The pointwise collar homotopy: a point which lies in the image of the punctured standard
`(k+1)`-simplex under a characteristic map is moved radially (inside its cell) by the collar
`collarMap (k+1)`; every other point is fixed. -/
def homotopyPt (R : DeltaRealization K X) (k : ℕ) (t : I) (x : X) : X :=
  if h : ∃ (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))),
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) = x then
    R.toDeltaSimplexMap.cls (k + 1) h.choose (collarMap (k + 1) (t, h.choose_spec.choose))
  else x

/-- A point of a punctured `(k+1)`-cell is moved by the collar inside its cell. -/
theorem homotopyPt_of_cls (R : DeltaRealization K X) (k : ℕ) (t : I)
    (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))) :
    homotopyPt R k t (R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2)))) =
      R.toDeltaSimplexMap.cls (k + 1) τ (collarMap (k + 1) (t, y)) := by
  rw [homotopyPt]
  split_ifs with h
  · exact R.cls_collarMap_eq_of_cls_eq k h.choose_spec.choose_spec t
  · exact absurd ⟨τ, y, rfl⟩ h

/-- A point which is not in any punctured `(k+1)`-cell is fixed by the homotopy. -/
theorem homotopyPt_of_not (R : DeltaRealization K X) (k : ℕ) (t : I) {x : X}
    (h : ¬ ∃ (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))),
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) = x) :
    homotopyPt R k t x = x := by
  rw [homotopyPt]
  exact dif_neg h

/-- The radial homotopy of the collar, as a function on `I × (X^{k+1} ∖ {barycentres})`. -/
def homotopyVal (R : DeltaRealization K X) (k : ℕ) :
    I × ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) → X :=
  fun p => homotopyPt R k p.1 p.2.1

theorem homotopyVal_apply (R : DeltaRealization K X) (k : ℕ)
    (p : I × ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    homotopyVal R k p = homotopyPt R k p.1 p.2.1 := rfl

/-- The radial homotopy stays inside the collar. -/
theorem homotopyVal_mem (R : DeltaRealization K X) (k : ℕ)
    (p : I × ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    homotopyVal R k p ∈ R.toDeltaSimplexMap.punctSkel (k + 1) := by
  obtain ⟨t, z⟩ := p
  rw [homotopyVal_apply]
  by_cases h : ∃ (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))),
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) = (z : X)
  · rw [homotopyPt, dif_pos h]
    exact R.cls_mem_punctSkel (k + 1) h.choose (collarMap (k + 1) (t, h.choose_spec.choose)).2
  · rw [homotopyPt, dif_neg h]
    exact z.2

/-- The radial homotopy of the collar of the `(k+1)`-skeleton, as a map of that collar into
itself. -/
def homotopyFun (R : DeltaRealization K X) (k : ℕ) :
    I × ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) →
      ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) :=
  fun p => ⟨homotopyVal R k p, homotopyVal_mem R k p⟩

theorem homotopyFun_apply (R : DeltaRealization K X) (k : ℕ)
    (p : I × ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    (homotopyFun R k p : X) = homotopyVal R k p := rfl

/-- The homotopy at time `0` is the identity. -/
theorem homotopyFun_zero (R : DeltaRealization K X) (k : ℕ)
    (z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) : homotopyFun R k (0, z) = z := by
  apply Subtype.ext
  show homotopyVal R k (0, z) = (z : X)
  rw [homotopyVal_apply]
  by_cases h : ∃ (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))),
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) = (z : X)
  · rw [homotopyPt, dif_pos h, collarMap_zero]
    exact h.choose_spec.choose_spec
  · rw [homotopyPt, dif_neg h]

/-- The homotopy fixes the `k`-skeleton pointwise. -/
theorem homotopyFun_fixes (R : DeltaRealization K X) (k : ℕ) (t : I)
    {z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))}
    (hz : (z : X) ∈ R.toDeltaSimplexMap.skelSet k) : homotopyFun R k (t, z) = z := by
  apply Subtype.ext
  show homotopyVal R k (t, z) = (z : X)
  rw [homotopyVal_apply]
  by_cases h : ∃ (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))),
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) = (z : X)
  · rw [homotopyPt, dif_pos h]
    have hb : ((h.choose_spec.choose : ↥(punctStdSimplex (k + 1))) :
        StdSimplex ℝ (Fin (k + 2))) ∈ StdSimplexBoundary (k + 1) :=
      R.boundary_of_cls_mem_skelSet k h.choose (by rw [h.choose_spec.choose_spec]; exact hz)
    rw [collarMap_eq_self_of_boundary (k + 1) h.choose_spec.choose hb t]
    exact h.choose_spec.choose_spec
  · rw [homotopyPt, dif_neg h]

/-- At time `1` the homotopy lands in the `k`-skeleton. -/
theorem homotopyVal_one_mem_skelSet (R : DeltaRealization K X) (k : ℕ)
    (z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    homotopyVal R k (1, z) ∈ R.toDeltaSimplexMap.skelSet k := by
  rw [homotopyVal_apply]
  by_cases h : ∃ (τ : Fin (K.card (k + 1))) (y : ↥(punctStdSimplex (k + 1))),
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) = (z : X)
  · rw [homotopyPt, dif_pos h]
    exact R.cls_mem_skelSet_of_exists_zero_weight k h.choose
      (collarMap_one_mem_boundary (k + 1) h.choose_spec.choose)
  · rw [homotopyPt, dif_neg h]
    by_contra hz
    exact h (R.exists_cls_eq_of_mem_punctSkel z.2 hz)


/-! ## The pieces of the collar carried by the `(k+1)`-simplices -/

/-- The piece of the collar of the `(k+1)`-skeleton carried by the simplex `τ`: the points of
the collar which lie in the image of the closed `(k+1)`-simplex `τ`. -/
def collarPiece (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1))) :
    Set ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) :=
  {z | (z : X) ∈ Set.range (R.toDeltaSimplexMap.cls (k + 1) τ)}

theorem mem_collarPiece_iff (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1)))
    (z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    z ∈ collarPiece R k τ ↔ (z : X) ∈ Set.range (R.toDeltaSimplexMap.cls (k + 1) τ) :=
  Iff.rfl

/-- The characteristic map of the simplex `τ`, restricted to the punctured standard
`(k+1)`-simplex and corestricted to the piece of the collar it carries. -/
def punctToPiece (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1))) :
    ↥(punctStdSimplex (k + 1)) → ↥(collarPiece R k τ) :=
  fun y => ⟨⟨R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))),
      R.cls_mem_punctSkel (k + 1) τ y.2⟩, ⟨y, rfl⟩⟩

theorem punctToPiece_apply (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1)))
    (y : ↥(punctStdSimplex (k + 1))) :
    (((punctToPiece R k τ y : ↥(collarPiece R k τ)) :
        ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) : X) =
      R.toDeltaSimplexMap.cls (k + 1) τ (y : StdSimplex ℝ (Fin (k + 2))) := rfl

end

end Work.DeltaHomology

