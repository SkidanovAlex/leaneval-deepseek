/-
  Area E7, "face cells": inserting a coordinate pinned at a constant level.

  The lemma `Work.WilE7.faceCell_star` needs the following operation on restricted
  semi-Pfaffian sets: given `X ⊆ ℝ^{p+q}` and a level `t ∈ [-1,1]`, view `X` as a
  semi-Pfaffian set in `ℝ^{(p+1)+q}` whose coordinate at position `p` is *pinned* to the value
  `t` and whose remaining coordinates are those of `X`.

  The construction is `SemiPf.extend` along the coordinate injection
  `Work.WilE8.skipInj p q : Fin (p+q) → Fin (p+1+q)` (which skips the new coordinate `p`),
  followed by adjoining the equation `x_new - t = 0` to every basic set.  The two pieces of the
  API below are

  * `addEq` — adjoining an equation to every basic set of a semi-Pfaffian set (the template is
    `Work.WilE7.critSet`), with its point set `addEq_set`;
  * `insertCoord` — the pinned extension, with its point set `insertCoord_set`, and the
    computation of the projection of the pinned cylinder (`projFirst_insertCoord`), which is the
    variant of `Work.WilE8.Star.projFirst_cyl` in which the new coordinate is fixed to `t`
    rather than free.

  Everything here is unconditional (no `Star`/`SubPf` input): it is the vocabulary that
  `FaceAux/component.lean` and `FaceAux/subPf_insert.lean`, and the target's assembly, use.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.WilE8.Star.projFirst_cyl

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.FaceAux

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The new coordinate and the pinning equation -/

/-- The position of the inserted coordinate in `Fin (p+1+q)`: coordinate `p`. -/
def newIdx (p q : ℕ) : Fin (p + 1 + q) := Fin.castAdd q (Fin.last p)

@[simp] theorem newIdx_val (p q : ℕ) : (newIdx p q : ℕ) = p := by
  simp [newIdx]

/-- The equation `x_new = t` pinning the inserted coordinate to the value `t`. -/
def pinPoly (p q r : ℕ) (t : ℝ) : EAPoly (p + 1 + q) r :=
  MvPolynomial.X (Sum.inl (newIdx p q)) - MvPolynomial.C t

/-- Evaluation of the pinning equation: it is `z (newIdx p q) - t`. -/
theorem eaEval_pinPoly {p q r : ℕ} (c : EAChain (p + 1 + q) r) (t : ℝ)
    (z : Fin (p + 1 + q) → ℝ) :
    eaEval c (pinPoly p q r t) z = z (newIdx p q) - t := by
  have hsub : eaEval c (MvPolynomial.X (Sum.inl (newIdx p q)) -
      MvPolynomial.C t : EAPoly (p + 1 + q) r) z
      = eaEval c (MvPolynomial.X (Sum.inl (newIdx p q)) : EAPoly (p + 1 + q) r) z
        - eaEval c (MvPolynomial.C t) z := by
    simp only [eaEval, map_sub]
  rw [pinPoly, hsub]
  simp only [eaEval, MvPolynomial.eval_X, Sum.elim_inl, MvPolynomial.eval_C]

/-! ## Adjoining an equation to every basic set -/

/-- Adjoin the equation `Q = 0` to every basic set of `X`, keeping the chain. -/
def addEq {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) : SemiPf k :=
  ⟨X.r, X.c, X.basics.map (fun B => (⟨B.eqs ++ [Q], B.pos⟩ : Basic k X.r))⟩

@[simp] theorem addEq_r {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) :
    (addEq X Q).r = X.r := rfl

@[simp] theorem addEq_c {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) :
    (addEq X Q).c = X.c := rfl

@[simp] theorem addEq_basics {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) :
    (addEq X Q).basics = X.basics.map (fun B => (⟨B.eqs ++ [Q], B.pos⟩ : Basic k X.r)) := rfl

@[simp] theorem addEq_fmt {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) :
    (addEq X Q).fmt = X.fmt := rfl

/-- The point set of `addEq X Q`: the points of `X` at which `Q` vanishes. -/
theorem addEq_set {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) :
    (addEq X Q).set = X.set ∩ {z | eaEval X.c Q z = 0} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, SemiPf.set, addEq_basics, addEq_c]
  constructor
  · rintro ⟨hc, B, hB, hBholds⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    exact ⟨⟨hc, B₀, hB₀, ⟨fun f hf => hBholds.1 f (List.mem_append.mpr (Or.inl hf)),
        hBholds.2⟩⟩,
      hBholds.1 Q (List.mem_append.mpr (Or.inr (List.mem_singleton_self Q)))⟩
  · rintro ⟨⟨hc, B₀, hB₀, hBholds⟩, hQ⟩
    refine ⟨hc, ⟨B₀.eqs ++ [Q], B₀.pos⟩, List.mem_map.mpr ⟨B₀, hB₀, rfl⟩, ?_, hBholds.2⟩
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hBholds.1 f hf
    · rw [List.mem_singleton.mp hf]; exact hQ

/-! ## The pinned extension -/

/-- The cylinder extension of `X` along the injection `skipInj`, which does not change the
chain but adds one free coordinate at position `p`. -/
def extendP {p q : ℕ} (X : SemiPf (p + q)) : SemiPf (p + 1 + q) :=
  Work.WilE8.SemiPf.extend (Work.WilE8.skipInj p q) X

@[simp] theorem extendP_r {p q : ℕ} (X : SemiPf (p + q)) : (extendP X).r = X.r := rfl

/-- `X` viewed in `ℝ^{(p+1)+q}` with the coordinate at position `p` pinned to `t` and the
remaining coordinates those of `X`. -/
def insertCoord {p q : ℕ} (X : SemiPf (p + q)) (t : ℝ) : SemiPf (p + 1 + q) :=
  addEq (extendP X) (pinPoly p q (extendP X).r t)

/-- The point set of the pinned extension: `(z ∘ skipInj) ∈ X.set` and `z` at the new
coordinate is `t`.  The level `t` must be in `[-1,1]`, since `SemiPf` sets live in the cube. -/
theorem insertCoord_set {p q : ℕ} (X : SemiPf (p + q)) {t : ℝ} (ht : |t| ≤ 1) :
    (insertCoord X t).set = {z : Fin (p + 1 + q) → ℝ |
      (fun i => z (Work.WilE8.skipInj p q i)) ∈ X.set ∧ z (newIdx p q) = t} := by
  rw [insertCoord, extendP]
  have hpin : ∀ z : Fin (p + 1 + q) → ℝ,
      eaEval (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj p q) X).c
        (pinPoly p q (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj p q) X).r t) z
      = z (newIdx p q) - t := fun z => eaEval_pinPoly _ t z
  rw [addEq_set,
    Work.WilE8.Extend.semipf_set_extend (Work.WilE8.Star.skipInj_injective p q) X]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hpin, sub_eq_zero]
  constructor
  · rintro ⟨⟨-, hX⟩, ht'⟩
    exact ⟨hX, ht'⟩
  · rintro ⟨hX, ht'⟩
    have hw : (fun i => z (Work.WilE8.skipInj p q i)) ∈ cubeC (p + q) :=
      Work.WilE8.SemiPf.set_subset_cube X hX
    have hz : Work.WilE8.Star.insCoord p q (fun i => z (Work.WilE8.skipInj p q i))
        (z (newIdx p q)) ∈ cubeC (p + 1 + q) :=
      Work.WilE8.Star.insCoord_cube p q hw (by rw [ht']; exact ht)
    refine ⟨⟨?_, hX⟩, ht'⟩
    rwa [newIdx, Work.WilE8.Star.insCoord_self p q z] at hz

/-- **The projection of the pinned cylinder.**  Projecting the pinned extension of `C` to the
first `p+1` coordinates gives the "face" of `C` at the level `t`: the points whose initial
`p` coordinates lie in `projFirst p q '' C` and whose last coordinate is `t`. -/
theorem projFirst_insertCoord {p q : ℕ} {C : Set (Fin (p + q) → ℝ)} (hC : C ⊆ cubeC (p + q))
    (t : ℝ) (ht : |t| ≤ 1) :
    projFirst (p + 1) q '' {x : Fin (p + 1 + q) → ℝ |
        (fun i => x (Work.WilE8.skipInj p q i)) ∈ C ∧ x (newIdx p q) = t}
      = {z : Fin (p + 1) → ℝ | Fin.init z ∈ projFirst p q '' C ∧ z (Fin.last p) = t} := by
  ext z
  constructor
  · rintro ⟨x, ⟨hxC, hxt⟩, rfl⟩
    refine ⟨⟨fun i => x (Work.WilE8.skipInj p q i), hxC, ?_⟩, ?_⟩
    · funext i
      show x (Work.WilE8.skipInj p q (Fin.castAdd q i))
        = projFirst (p + 1) q x (Fin.castSucc i)
      rw [Work.WilE8.Star.skipInj_castAdd_castSucc]
      rfl
    · show projFirst (p + 1) q x (Fin.last p) = t
      have h : projFirst (p + 1) q x (Fin.last p) = x (newIdx p q) := rfl
      rw [h, hxt]
  · rintro ⟨⟨c, hcC, hceq⟩, hzt⟩
    refine ⟨Work.WilE8.Star.insCoord p q c (z (Fin.last p)), ⟨?_, ?_⟩, ?_⟩
    · rw [show (fun i => Work.WilE8.Star.insCoord p q c (z (Fin.last p))
          (Work.WilE8.skipInj p q i)) = c
        from funext (Work.WilE8.Star.insCoord_skipInj p q c (z (Fin.last p)))]
      exact hcC
    · show Work.WilE8.Star.insCoord p q c (z (Fin.last p)) (newIdx p q) = t
      rw [newIdx, Work.WilE8.Star.insCoord_new, hzt]
    · rw [Work.WilE8.Star.projFirst_insCoord, hceq, Fin.snoc_init_self]

end Work.WilE7.FaceAux
