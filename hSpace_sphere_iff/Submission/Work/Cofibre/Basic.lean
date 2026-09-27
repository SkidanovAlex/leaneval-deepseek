/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The cofibre of a map between spheres

For a continuous map `f : S^{2b-1} ⟶ S^b` of spheres we construct the **cofibre**

`C_f = S^b ∪_f D^{2b}`,

the quotient of the disjoint union of the closed unit disk `D^{2b} ⊆ ℝ^{2b}` and the sphere
`S^b ⊆ ℝ^{b+1}` which identifies a boundary point `p` of the disk with `f p`.  This is the space
whose cohomology carries the *Hopf invariant* of `f`: `H^b(C_f; R) ≅ R`, `H^{2b}(C_f; R) ≅ R`,
and the Hopf invariant of `f` measures the cup square of a generator of `H^b(C_f; R)`.

The second half of the file records the open cover `C_f = U ∪ V` used for the Mayer–Vietoris
computation of `H^*(C_f)`:

* `U` is the open neighbourhood `{1/2 < ‖x‖} ∪ S^b` of the bottom sphere, which retracts onto
  `S^b` along the attaching map;
* `V` is the open top cell `{‖x‖ < 1}`, which is contractible;
* `U ∩ V` is the open annulus `{1/2 < ‖x‖ < 1}`, homotopy equivalent to `S^{2b-1}`.

The point-set work goes through the membership lemmas `mkq_inl_eq_inl_iff`, `mkq_inl_eq_inr_iff`,
`mkq_inr_eq_inr_iff` and the saturation lemmas `U₀_saturated`, `V₀_saturated`.
-/
import Mathlib
import Submission.Work.Sphere.Basic

open scoped Topology
open Set

namespace Submission.Cofibre

noncomputable section

variable {b : ℕ}

/-- The closed unit disk `D^{2b} ⊆ ℝ^{2b}`. -/
def diskSet (b : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * b))) := Metric.closedBall 0 1

/-- The boundary of the disk, i.e. the sphere `S^{2b-1} ⊆ ℝ^{2b}`. -/
def bdrySet (b : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * b))) := Metric.sphere 0 1

/-- The sphere `S^b ⊆ ℝ^{b+1}`, the target of the attaching map. -/
def tgtSet (b : ℕ) : Set (EuclideanSpace ℝ (Fin (b + 1))) := Metric.sphere 0 1

/-- The norm of a point of the disk is at most one. -/
lemma norm_le_one (x : ↥(diskSet b)) : ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ ≤ 1 := by
  have h := Metric.mem_closedBall.mp x.2
  rw [dist_eq_norm, sub_zero] at h
  exact h

/-- The norm of a boundary point is one. -/
lemma norm_eq_one (p : ↥(bdrySet b)) : ‖(p : EuclideanSpace ℝ (Fin (2 * b)))‖ = 1 := by
  have h := Metric.mem_sphere.mp p.2
  rw [dist_eq_norm, sub_zero] at h
  exact h

/-- The boundary of the disk, regarded as a point of the disk. -/
def bdryInDisk (b : ℕ) (p : ↥(bdrySet b)) : ↥(diskSet b) :=
  ⟨p.1, Metric.sphere_subset_closedBall p.2⟩

@[simp] lemma coe_bdryInDisk (p : ↥(bdrySet b)) :
    ((bdryInDisk b p : ↥(diskSet b)) : EuclideanSpace ℝ (Fin (2 * b))) = p.1 := rfl

@[simp] lemma norm_bdryInDisk (p : ↥(bdrySet b)) :
    ‖(bdryInDisk b p : EuclideanSpace ℝ (Fin (2 * b)))‖ = 1 := norm_eq_one p

/-- The map `bdryInDisk` is injective. -/
lemma bdryInDisk_injective {p q : ↥(bdrySet b)} (h : bdryInDisk b p = bdryInDisk b q) : p = q := by
  apply Subtype.ext
  exact congrArg (fun z : ↥(diskSet b) => (z : EuclideanSpace ℝ (Fin (2 * b)))) h

/-- The equivalence relation defining the cofibre of `f : S^{2b-1} → S^b`: it identifies a
boundary point of the disk with its image under `f`. -/
def cofRel (b : ℕ) (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) :
    Setoid (↥(diskSet b) ⊕ ↥(tgtSet b)) where
  r x y := x = y
    ∨ (∃ p : ↥(bdrySet b), x = Sum.inl (bdryInDisk b p) ∧ y = Sum.inr (f p))
    ∨ (∃ p : ↥(bdrySet b), y = Sum.inl (bdryInDisk b p) ∧ x = Sum.inr (f p))
    ∨ (∃ p q : ↥(bdrySet b), f p = f q ∧ x = Sum.inl (bdryInDisk b p)
        ∧ y = Sum.inl (bdryInDisk b q))
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with h | ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨p, q, hf, h1, h2⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr (Or.inl ⟨p, h1, h2⟩))
      · exact Or.inr (Or.inl ⟨p, h1, h2⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨q, p, hf.symm, h2, h1⟩))
    · intro x y z hxy hyz
      rcases hxy with rfl | ⟨p, hx, hy⟩ | ⟨p, hy, hx⟩ | ⟨p, q, hf, hx, hy⟩
      · exact hyz
      · subst hx; subst hy
        rcases hyz with hyz | ⟨r, h1, h2⟩ | ⟨r, h1, h2⟩ | ⟨r, s, hf', h1, h2⟩
        · rw [← hyz]; exact Or.inr (Or.inl ⟨p, rfl, rfl⟩)
        · exact absurd h1 (by simp)
        · refine Or.inr (Or.inr (Or.inr ⟨p, r, ?_, rfl, h1⟩))
          exact Sum.inr.inj h2
        · exact absurd h1 (by simp)
      · subst hx; subst hy
        rcases hyz with hyz | ⟨r, h1, h2⟩ | ⟨r, h1, h2⟩ | ⟨r, s, hf', h1, h2⟩
        · rw [← hyz]; exact Or.inr (Or.inr (Or.inl ⟨p, rfl, rfl⟩))
        · have hpr' : p = r := bdryInDisk_injective (Sum.inl.inj h1)
          rw [h2, hpr']; exact Or.inl rfl
        · exact absurd h2 (by simp)
        · have hpr' : p = r := bdryInDisk_injective (Sum.inl.inj h1)
          rw [h2, hpr']
          exact Or.inr (Or.inr (Or.inl ⟨s, rfl, by rw [hf']⟩))
      · subst hx; subst hy
        rcases hyz with hyz | ⟨r, h1, h2⟩ | ⟨r, h1, h2⟩ | ⟨r, s, hf', h1, h2⟩
        · rw [← hyz]; exact Or.inr (Or.inr (Or.inr ⟨p, q, hf, rfl, rfl⟩))
        · have hqr' : q = r := bdryInDisk_injective (Sum.inl.inj h1)
          rw [h2]
          refine Or.inr (Or.inl ⟨p, rfl, ?_⟩)
          rw [← hqr', ← hf]
        · exact absurd h2 (by simp)
        · have hqr' : q = r := bdryInDisk_injective (Sum.inl.inj h1)
          rw [h2]
          refine Or.inr (Or.inr (Or.inr ⟨p, s, ?_, rfl, rfl⟩))
          rw [hf, hqr', hf']

/-- The cofibre `C_f = S^b ∪_f D^{2b}` of `f : S^{2b-1} → S^b`, as a topological space. -/
def cofibre (b : ℕ) (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) : TopCat.{0} :=
  TopCat.of (Quotient (cofRel b f))

/-- The class map into the cofibre. -/
def mkq (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) :
    (↥(diskSet b) ⊕ ↥(tgtSet b)) → cofibre b f :=
  Quotient.mk (cofRel b f)

/-- A boundary point of the disk and its image under `f` have the same class in the cofibre. -/
lemma mkq_bdry (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) (p : ↥(bdrySet b)) :
    mkq f (Sum.inl (bdryInDisk b p)) = mkq f (Sum.inr (f p)) :=
  Quotient.sound (Or.inr (Or.inl ⟨p, rfl, rfl⟩))

/-- Two disk points have the same class iff they are equal or are two boundary points glued
by `f`. -/
lemma mkq_inl_eq_inl_iff (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b))
    (x y : ↥(diskSet b)) :
    mkq f (Sum.inl x) = mkq f (Sum.inl y) ↔
      x = y ∨ ∃ p q : ↥(bdrySet b), f p = f q ∧ x = bdryInDisk b p ∧ y = bdryInDisk b q := by
  constructor
  · intro h
    rcases Quotient.exact h with h | ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨p, q, hf, h1, h2⟩
    · exact Or.inl (Sum.inl.inj h)
    · exact absurd h2 (by simp)
    · exact absurd h2 (by simp)
    · exact Or.inr ⟨p, q, hf, Sum.inl.inj h1, Sum.inl.inj h2⟩
  · rintro (rfl | ⟨p, q, hf, rfl, rfl⟩)
    · rfl
    · exact Quotient.sound (Or.inr (Or.inr (Or.inr ⟨p, q, hf, rfl, rfl⟩)))

/-- A disk point and a sphere point have the same class iff the disk point lies on the boundary
and is glued to the sphere point. -/
lemma mkq_inl_eq_inr_iff (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b))
    (x : ↥(diskSet b)) (s : ↥(tgtSet b)) :
    mkq f (Sum.inl x) = mkq f (Sum.inr s) ↔
      ∃ p : ↥(bdrySet b), x = bdryInDisk b p ∧ f p = s := by
  constructor
  · intro h
    rcases Quotient.exact h with h | ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨p, q, hf, h1, h2⟩
    · exact absurd h (by simp)
    · exact ⟨p, Sum.inl.inj h1, (Sum.inr.inj h2).symm⟩
    · exact absurd h1 (by simp)
    · exact absurd h2 (by simp)
  · rintro ⟨p, rfl, rfl⟩
    exact Quotient.sound (Or.inr (Or.inl ⟨p, rfl, rfl⟩))

/-- Two sphere points have the same class iff they are equal. -/
lemma mkq_inr_eq_inr_iff (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b))
    (s t : ↥(tgtSet b)) : mkq f (Sum.inr s) = mkq f (Sum.inr t) ↔ s = t := by
  constructor
  · intro h
    rcases Quotient.exact h with h | ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨p, q, hf, h1, h2⟩
    · exact Sum.inr.inj h
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
  · rintro rfl; rfl

/-! ## The open cover of the cofibre -/

/-- The open neighbourhood of the bottom sphere: the part of the disk with `1/2 < ‖x‖`, together
with the whole bottom sphere. -/
def U₀ (b : ℕ) : Set (↥(diskSet b) ⊕ ↥(tgtSet b)) :=
  {z | match z with
    | Sum.inl x => 1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖
    | Sum.inr _ => True}

/-- The open top cell: the interior of the disk. -/
def V₀ (b : ℕ) : Set (↥(diskSet b) ⊕ ↥(tgtSet b)) :=
  {z | match z with
    | Sum.inl x => ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ < 1
    | Sum.inr _ => False}

@[simp] lemma mem_U₀_inl (x : ↥(diskSet b)) :
    (Sum.inl x : ↥(diskSet b) ⊕ ↥(tgtSet b)) ∈ U₀ b ↔
      1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ := Iff.rfl

@[simp] lemma mem_U₀_inr (s : ↥(tgtSet b)) :
    (Sum.inr s : ↥(diskSet b) ⊕ ↥(tgtSet b)) ∈ U₀ b := trivial

@[simp] lemma mem_V₀_inl (x : ↥(diskSet b)) :
    (Sum.inl x : ↥(diskSet b) ⊕ ↥(tgtSet b)) ∈ V₀ b ↔
      ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ < 1 := Iff.rfl

@[simp] lemma not_mem_V₀_inr (s : ↥(tgtSet b)) :
    ¬ ((Sum.inr s : ↥(diskSet b) ⊕ ↥(tgtSet b)) ∈ V₀ b) := id

/-- `U₀` is saturated for the gluing relation. -/
lemma U₀_saturated (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) ⦃z z'⦄
    (h : (cofRel b f).r z z') (hz : z ∈ U₀ b) : z' ∈ U₀ b := by
  rcases h with h | ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨p, q, hf, h1, h2⟩
  · exact h ▸ hz
  · rw [h2]; trivial
  · rw [h1, mem_U₀_inl, norm_bdryInDisk]; norm_num
  · rw [h2, mem_U₀_inl, norm_bdryInDisk]; norm_num

/-- `V₀` is saturated for the gluing relation. -/
lemma V₀_saturated (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) ⦃z z'⦄
    (h : (cofRel b f).r z z') (hz : z ∈ V₀ b) : z' ∈ V₀ b := by
  rcases h with h | ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨p, q, hf, h1, h2⟩
  · exact h ▸ hz
  · rw [h1, mem_V₀_inl, norm_bdryInDisk] at hz; norm_num at hz
  · rw [h2] at hz; simp at hz
  · rw [h1, mem_V₀_inl, norm_bdryInDisk] at hz; norm_num at hz

/-- The open neighbourhood `U` of the bottom sphere inside the cofibre. -/
def U (b : ℕ) (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) : Set (cofibre b f) :=
  mkq f '' U₀ b

/-- The open top cell `V` inside the cofibre. -/
def V (b : ℕ) (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) : Set (cofibre b f) :=
  mkq f '' V₀ b

lemma mem_U_iff (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b))
    (z : ↥(diskSet b) ⊕ ↥(tgtSet b)) : mkq f z ∈ U b f ↔ z ∈ U₀ b := by
  constructor
  · rintro ⟨z', hz', hzz'⟩
    exact U₀_saturated f (Quotient.exact hzz') hz'
  · intro hz; exact ⟨z, hz, rfl⟩

lemma mem_V_iff (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b))
    (z : ↥(diskSet b) ⊕ ↥(tgtSet b)) : mkq f z ∈ V b f ↔ z ∈ V₀ b := by
  constructor
  · rintro ⟨z', hz', hzz'⟩
    exact V₀_saturated f (Quotient.exact hzz') hz'
  · intro hz; exact ⟨z, hz, rfl⟩

lemma isOpen_U₀ (b : ℕ) : IsOpen (U₀ b) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, ?_⟩
  · have h : Sum.inl ⁻¹' U₀ b = {x : ↥(diskSet b) | 1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖} :=
      rfl
    rw [h]
    have h2 : {x : ↥(diskSet b) | 1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖}
        = Subtype.val ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * b))) (1 / 2))ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, Metric.mem_closedBall,
        dist_eq_norm, sub_zero, not_le]
    rw [h2]
    exact Metric.isClosed_closedBall.isOpen_compl.preimage continuous_subtype_val
  · have h : Sum.inr ⁻¹' U₀ b = univ := by ext s; simp
    rw [h]; exact isOpen_univ

lemma isOpen_V₀ (b : ℕ) : IsOpen (V₀ b) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, ?_⟩
  · have h : Sum.inl ⁻¹' V₀ b = {x : ↥(diskSet b) | ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ < 1} :=
      rfl
    rw [h]
    have h2 : {x : ↥(diskSet b) | ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ < 1}
        = Subtype.val ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * b))) 1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [h2]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  · have h : Sum.inr ⁻¹' V₀ b = (∅ : Set ↥(tgtSet b)) := by ext s; simp
    rw [h]; exact isOpen_empty

lemma isOpen_U (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) : IsOpen (U b f) := by
  have h : mkq f ⁻¹' U b f = U₀ b := by ext z; exact mem_U_iff f z
  rw [show IsOpen (U b f) ↔ IsOpen (mkq f ⁻¹' U b f) from isOpen_coinduced]
  rw [h]; exact isOpen_U₀ b

lemma isOpen_V (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) : IsOpen (V b f) := by
  have h : mkq f ⁻¹' V b f = V₀ b := by ext z; exact mem_V_iff f z
  rw [show IsOpen (V b f) ↔ IsOpen (mkq f ⁻¹' V b f) from isOpen_coinduced]
  rw [h]; exact isOpen_V₀ b

/-- The two pieces cover the cofibre. -/
lemma U_union_V (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) : U b f ∪ V b f = univ := by
  ext q
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  induction q using Quotient.ind with
  | _ z =>
    rcases z with x | s
    · rcases lt_or_ge ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ 1 with h | h
      · right; exact ⟨Sum.inl x, by simpa using h, rfl⟩
      · left; refine ⟨Sum.inl x, ?_, rfl⟩
        have hx : ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ = 1 := le_antisymm (norm_le_one x) h
        rw [mem_U₀_inl, hx]; norm_num
    · left; exact ⟨Sum.inr s, trivial, rfl⟩

/-- The intersection of the two pieces is the image of the open annulus. -/
lemma U_inter_V (f : ContinuousMap ↥(bdrySet b) ↥(tgtSet b)) :
    U b f ∩ V b f = mkq f '' (U₀ b ∩ V₀ b) := by
  ext q
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction q using Quotient.ind with
    | _ z => exact ⟨z, ⟨(mem_U_iff f z).mp h.1, (mem_V_iff f z).mp h.2⟩, rfl⟩
  · obtain ⟨z, ⟨hzU, hzV⟩, rfl⟩ := h
    exact ⟨⟨z, hzU, rfl⟩, ⟨z, hzV, rfl⟩⟩

/-- Explicit description of `U₀ ∩ V₀`: the open annulus inside the disk. -/
lemma U₀_inter_V₀ (b : ℕ) :
    U₀ b ∩ V₀ b = {z | ∃ x : ↥(diskSet b), z = Sum.inl x ∧
      1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ ∧
        ‖(x : EuclideanSpace ℝ (Fin (2 * b)))‖ < 1} := by
  ext z
  constructor
  · rintro ⟨hzU, hzV⟩
    rcases z with x | s
    · exact ⟨x, rfl, hzU, hzV⟩
    · exact absurd hzV (by simp)
  · rintro ⟨x, rfl, h1, h2⟩
    exact ⟨h1, h2⟩

end

end Submission.Cofibre
