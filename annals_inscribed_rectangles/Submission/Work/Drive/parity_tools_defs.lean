import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.boxParity

/-!
# Tool definitions for the mod-2 intersection route (node owner's lane)

This file collects small definitions shared by several pieces of the mod-2 intersection chapter:

* the general `(p,q)`-chain setup in `ℝ^{p+q-1}` — a `p`-chain `D` and a `q`-chain `N` (maps from
  the boxes `[0,1]^p` and `[0,1]^q` into the ambient space), their difference map `genDiff D N` on
  the `(p+q)`-box, and the two boundary intersection sets `meetD D N` (the `∂D ⋔ N` count) and
  `meetN D N` (the `D ⋔ ∂N` count).  `intersection_parity.lean` is the case `(p,q) = (2,3)` of this
  setup; the cases `(p,q) = (1,2)` and `(2,1)` in `ℝ²` are what the *surface* counts of
  `CHAIN_ROUTE_REDUCTION.md` §3–§4 need (two loops in a surface, or a loop against a filling
  surface).  Generalising once removes the dimension bookkeeping from every later use.

  The box is `Welcome.Drive.Amb (p+q-1)`, i.e. the box `[0,1]^{p+q}` carrying `ParityProp` with
  `m := p+q-1`, so that the general Leibniz rule is exactly a `ParityProp` instantiation.

* `SignChangeAt f t` — the hypothesis that a continuous `f` changes sign at its zero `t`.  It is the
  non-degeneracy hypothesis of the parity statement "an antisymmetric (periodic) continuous function
  on the circle has a number of zeros congruent to `2` modulo `4`", the analytic core of "two
  essential loops of `ℝP²` meet an odd number of times" (`CHAIN_ROUTE_REDUCTION.md` §4) and of the
  oddness inputs of Hugelmeyer's Lemma 2.
-/

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The general `(p,q)`-chain setup -/

/-- The `i`-th coordinate of the `p`-block inside the `(p+q)`-box `Amb (p+q-1)`. -/
def pqIdx (p q : ℕ) (i : Fin p) : Fin (p + q - 1 + 1) := ⟨i.val, by omega⟩

/-- The `j`-th coordinate of the `q`-block inside the `(p+q)`-box `Amb (p+q-1)`. -/
def qpIdx (p q : ℕ) (j : Fin q) : Fin (p + q - 1 + 1) := ⟨p + j.val, by omega⟩

@[simp] lemma pqIdx_val (p q : ℕ) (i : Fin p) :
    ((pqIdx p q i : Fin (p + q - 1 + 1)) : ℕ) = i.val := rfl

@[simp] lemma qpIdx_val (p q : ℕ) (j : Fin q) :
    ((qpIdx p q j : Fin (p + q - 1 + 1)) : ℕ) = p + j.val := rfl

lemma pqIdx_ne_qpIdx (p q : ℕ) (i : Fin p) (j : Fin q) : pqIdx p q i ≠ qpIdx p q j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [pqIdx_val, qpIdx_val] at h'
  have := i.isLt
  omega

/-- `n - 1 + 1 = n` for a positive natural number (truncated subtraction). -/
lemma sub_one_add_one {n : ℕ} (hn : 0 < n) : n - 1 + 1 = n := Nat.sub_add_cancel hn

/-- **Splitting the coordinates of the `(p+q)`-box.**  Every coordinate of the box `Amb (p+q-1)`
lies in one of the two blocks (`p` and `q` being the positive dimensions of the two chains). -/
lemma exists_fin_amb_iff (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (P : Fin (p + q - 1 + 1) → Prop) :
    (∃ i, P i) ↔ (∃ i : Fin p, P (pqIdx p q i)) ∨ (∃ j : Fin q, P (qpIdx p q j)) := by
  have hpq : 0 < p + q := by omega
  have hdim : p + q - 1 + 1 = p + q := sub_one_add_one hpq
  constructor
  · rintro ⟨i, hi⟩
    have hlt : i.val < p + q := lt_of_lt_of_eq i.isLt hdim
    by_cases hplt : i.val < p
    · refine Or.inl ⟨⟨i.val, hplt⟩, ?_⟩
      have heq : pqIdx p q ⟨i.val, hplt⟩ = i := by
        apply Fin.ext
        show (pqIdx p q ⟨i.val, hplt⟩).val = i.val
        rw [pqIdx_val]
      rwa [heq]
    · have hge : p ≤ i.val := not_lt.mp hplt
      have hsub : i.val - p < q := by
        rw [Nat.sub_lt_iff_lt_add hge]
        omega
      refine Or.inr ⟨⟨i.val - p, hsub⟩, ?_⟩
      have heq : qpIdx p q ⟨i.val - p, hsub⟩ = i := by
        apply Fin.ext
        show (qpIdx p q ⟨i.val - p, hsub⟩).val = i.val
        rw [qpIdx_val]
        exact Nat.add_sub_of_le hge
      rwa [heq]
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨pqIdx p q i, hi⟩
    · exact ⟨qpIdx p q j, hj⟩

/-- Projection of the `(p+q)`-box onto its `p`-block. -/
def pqPart (p q : ℕ) (x : Amb (p + q - 1)) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun i => x (pqIdx p q i)

/-- Projection of the `(p+q)`-box onto its `q`-block. -/
def qpPart (p q : ℕ) (x : Amb (p + q - 1)) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun j => x (qpIdx p q j)

@[simp] lemma pqPart_apply (p q : ℕ) (x : Amb (p + q - 1)) (i : Fin p) :
    pqPart p q x i = x (pqIdx p q i) := rfl

@[simp] lemma qpPart_apply (p q : ℕ) (x : Amb (p + q - 1)) (j : Fin q) :
    qpPart p q x j = x (qpIdx p q j) := rfl

/-- The box `[0,1]^{p+q}` (the same set as `Submission.Drive.unitBox (p+q-1)`, by definition). -/
def pqBox (p q : ℕ) : Set (Amb (p + q - 1)) := unitBox (p + q - 1)

/-- The boundary of `pqBox p q` (the same set as `Submission.Drive.unitBoxBdry (p+q-1)`). -/
def pqBoxBdry (p q : ℕ) : Set (Amb (p + q - 1)) := unitBoxBdry (p + q - 1)

/-- The `p`-part of the box boundary: some `p`-block coordinate is `0` or `1`. -/
def onPqFace (p q : ℕ) (x : Amb (p + q - 1)) : Prop :=
  ∃ i : Fin p, x (pqIdx p q i) = 0 ∨ x (pqIdx p q i) = 1

/-- The `q`-part of the box boundary: some `q`-block coordinate is `0` or `1`. -/
def onQpFace (p q : ℕ) (x : Amb (p + q - 1)) : Prop :=
  ∃ j : Fin q, x (qpIdx p q j) = 0 ∨ x (qpIdx p q j) = 1

/-- The boundary of the box is the union of the "`p`-faces" and the "`q`-faces". -/
lemma mem_pqBoxBdry_iff (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (x : Amb (p + q - 1)) :
    x ∈ pqBoxBdry p q ↔ x ∈ pqBox p q ∧ (onPqFace p q x ∨ onQpFace p q x) := by
  constructor
  · rintro ⟨hbox, i, hi⟩
    refine ⟨hbox, ?_⟩
    exact (exists_fin_amb_iff p q hp hq fun i => x i = 0 ∨ x i = 1).mp ⟨i, hi⟩
  · rintro ⟨hbox, h | h⟩
    · obtain ⟨i, hi⟩ := h
      exact ⟨hbox, pqIdx p q i, hi⟩
    · obtain ⟨j, hj⟩ := h
      exact ⟨hbox, qpIdx p q j, hj⟩

/-- The boundary of the box, stated with `unitBoxBdry` directly (the same statement as
`mem_pqBoxBdry_iff`, for rewriting). -/
lemma mem_unitBoxBdry_pq_iff (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (x : Amb (p + q - 1)) :
    x ∈ unitBoxBdry (p + q - 1) ↔
      x ∈ unitBox (p + q - 1) ∧ (onPqFace p q x ∨ onQpFace p q x) :=
  mem_pqBoxBdry_iff p q hp hq x

/-- The difference map of a `p`-chain `D` and a `q`-chain `N` in the ambient space `ℝ^{p+q-1}`:
`genDiff D N x = D (pqPart x) - N (qpPart x)`. -/
def genDiff {p q : ℕ}
    (D : EuclideanSpace ℝ (Fin p) → Tgt (p + q - 1))
    (N : EuclideanSpace ℝ (Fin q) → Tgt (p + q - 1)) (x : Amb (p + q - 1)) :
    Tgt (p + q - 1) :=
  D (pqPart p q x) - N (qpPart p q x)

/-- The boundary intersections of the form `∂D ⋔ N`. -/
def meetD {p q : ℕ}
    (D : EuclideanSpace ℝ (Fin p) → Tgt (p + q - 1))
    (N : EuclideanSpace ℝ (Fin q) → Tgt (p + q - 1)) : Set (Amb (p + q - 1)) :=
  {x | x ∈ pqBox p q ∧ onPqFace p q x ∧ genDiff D N x = 0}

/-- The boundary intersections of the form `D ⋔ ∂N`. -/
def meetN {p q : ℕ}
    (D : EuclideanSpace ℝ (Fin p) → Tgt (p + q - 1))
    (N : EuclideanSpace ℝ (Fin q) → Tgt (p + q - 1)) : Set (Amb (p + q - 1)) :=
  {x | x ∈ pqBox p q ∧ onQpFace p q x ∧ genDiff D N x = 0}

/-! ## Sign changes -/

/-- `f` changes sign at the zero `t`: on a left neighbourhood it is strictly of one sign and on a
right neighbourhood strictly of the opposite sign.  This is the non-degeneracy hypothesis under which
each zero of `f` counts once in the parity of the number of zeros (a zero of a smooth function whose
derivative does not vanish is a sign change). -/
def SignChangeAt (f : ℝ → ℝ) (t : ℝ) : Prop :=
  (∃ ε > 0, (∀ s, t - ε < s → s < t → f s < 0) ∧ (∀ s, t < s → s < t + ε → 0 < f s)) ∨
  (∃ ε > 0, (∀ s, t - ε < s → s < t → 0 < f s) ∧ (∀ s, t < s → s < t + ε → f s < 0))

end

end Work.Drive
