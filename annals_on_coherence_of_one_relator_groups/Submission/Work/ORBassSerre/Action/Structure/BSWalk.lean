import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSPresentation
import Submission.Work.ORBassSerre.Tree.Walk.exists_consecutive_backtrack_of_closed_walk

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver
open Classical

/-!
# Path words and their walk in a `G`-tree

Given the graph-of-groups datum `d : TreeDatum G V` of a cocompact action on a tree and the
presentation data `D : PresData d` (which builds the group `Γ = Gamma d D` and the map
`Φ : Γ →* G`), a *path word* is a combinatorial description of a walk in `V` together with a
choice of element of the vertex group at every vertex of the walk and of an edge orbit for every
step:

* `orb k` is the vertex orbit of the `k`-th vertex of the walk,
* `letter k` is an element of the vertex group `vgroup (orb k)`,
* `stepE k`, `stepB k` describe the step from `orb k` to `orb (k+1)`: the `move` along the edge
  orbit `stepE k` in the direction `stepB k`.

From this data we build

* `pre k`, the product in `G` of the letters and stable letters before position `k`,
* `z k = pre k • vert (orb k)`, the `k`-th vertex of the walk (a vertex of `V`),
* `F k = (pre k * letter k) • move (stepE k) (stepB k)`, the `k`-th arrow of the walk, an arrow of
  `V` from `z k` to `z (k+1)`,
* `tpre k` and `elt`, the corresponding products in `Γ`, so that `Φ (elt)` is the total product of
  the letters and stable letters.

The main point (proved at the end of this file) is that a *reduced* closed path word whose `elt`
lies in the kernel of `Φ` must be trivial: `elt_eq_one_of_reduced_closed`.
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- The action on arrows, phrased as a rewrite rule for the source. -/
theorem total_smul_left (g : G) (X : Quiver.Total V) : (g • X).left = g • X.left :=
  Work.ORBassSerre.GraphAction.smul_left g X

/-- The action on arrows, phrased as a rewrite rule for the target. -/
theorem total_smul_right (g : G) (X : Quiver.Total V) : (g • X).right = g • X.right :=
  Work.ORBassSerre.GraphAction.smul_right g X

namespace TreeDatum

section Defs

variable (d : TreeDatum G V)

/-- A letter of a path word: the choice of a vertex orbit together with an element of the vertex
group at that orbit. -/
abbrev Letter : Type _ := Σ A : Work.ORBassSerre.orbitV G V, ↥(d.vgroup A)

/-- The element of `G` carried by a letter lies in the vertex group of its orbit. -/
theorem Letter.coe_mem (l : Letter d) : (l.2 : G) ∈ d.vgroup l.1 := l.2.2

/-- A letter fixes the lifted vertex of its orbit. -/
theorem Letter.smul_vert (l : Letter d) : (l.2 : G) • d.vert l.1 = d.vert l.1 :=
  MulAction.mem_stabilizer_iff.mp l.2.2

/-- A *path word*: a walk in the quotient graph together with a vertex-group letter at every
vertex of the walk.  The walk has `len` steps; the letters are indexed by `0, …, len`. -/
structure PathWord where
  /-- the number of steps of the walk -/
  len : ℕ
  /-- the vertex orbits of the walk -/
  orb : ℕ → Work.ORBassSerre.orbitV G V
  /-- the vertex-group letters -/
  letter : ℕ → Letter d
  /-- the orbit of the `k`-th letter is the `k`-th vertex orbit -/
  letter_orbit : ∀ k, k ≤ len → (letter k).1 = orb k
  /-- the edge orbit of the `k`-th step -/
  stepE : ℕ → Work.ORBassSerre.orbitE G V
  /-- the direction of the `k`-th step -/
  stepB : ℕ → Bool
  /-- the `k`-th step starts at the `k`-th vertex orbit -/
  step_src : ∀ k, k < len → moveSrc (stepE k) (stepB k) = orb k
  /-- the `k`-th step ends at the `(k+1)`-st vertex orbit -/
  step_tgt : ∀ k, k < len → moveTgt (stepE k) (stepB k) = orb (k + 1)

end Defs

section Walk

variable [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]

/-- The element of `Γ` attached to a letter: the image of the corresponding element of the vertex
group under `gEltHom`. -/
noncomputable def Letter.gam {d : TreeDatum G V} (l : Letter d) (D : PresData d) : Gamma d D :=
  d.gEltHom D l.1 l.2

/-- The letter of `Γ` attached to a letter of `G` maps back to that element of `G`. -/
theorem Letter.Φ_gam {d : TreeDatum G V} (l : Letter d) (D : PresData d) :
    Φ d D (l.gam D) = (l.2 : G) :=
  d.Φ_gEltHom D l.1 l.2

/-- The stable-letter part of a step: the element of `Γ` corresponding to the move along an edge
orbit.  For a tree edge it is `1`; for a non-tree edge it is the stable letter or its inverse. -/
noncomputable def stepGam {d : TreeDatum G V} (D : PresData d)
    (E : Work.ORBassSerre.orbitE G V) (b : Bool) : Gamma d D :=
  if h : d.IsTreeEdge E then 1
  else if b then PresentedGroup.of (Sum.inr ⟨E, h⟩)
  else (PresentedGroup.of (Sum.inr ⟨E, h⟩))⁻¹

/-- The stable-letter part of a step maps to the corresponding group element. -/
theorem Φ_stepGam {d : TreeDatum G V} (D : PresData d)
    (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    Φ d D (stepGam D E b) = d.moveElt E b := by
  by_cases h : d.IsTreeEdge E
  · rw [stepGam, dif_pos h, map_one]
    cases b
    · rw [d.moveElt_false, d.sElt_eq_one h, inv_one]
    · rw [d.moveElt_true, d.sElt_eq_one h]
  · rw [stepGam, dif_neg h]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_inv, Φ_of_inr, d.moveElt_false]
    · simp only [↓reduceIte, Φ_of_inr, d.moveElt_true]

/-- The word-level stable letter of a step represents the stable letter of that step in `Γ`. -/
theorem mk_stepWord {d : TreeDatum G V} (D : PresData d)
    (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    PresentedGroup.mk (rels d D) (stepWord d D E b) = stepGam D E b := by
  rw [stepWord, stepGam]
  by_cases h : d.IsTreeEdge E
  · rw [dif_pos h, dif_pos h, map_one]
  · rw [dif_neg h, dif_neg h]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_inv]
      rfl
    · simp only [↓reduceIte]
      rfl

/-- **The stable letter of the reversed edge orbit in `Γ`.**  The stable letter attached to the
reversed orbit is the inverse of the stable letter of the orbit, conjugated by the vertex group
elements `linkK E` and `linkH E` of the linking identity of `EdgeLink`.  This is the
`Γ`-statement of the additional linking relator of the presentation `Gamma`. -/
theorem linkGamma {d : TreeDatum G V} (D : PresData d)
    (E : Work.ORBassSerre.orbitE G V) :
    stepGam D (Work.ORBassSerre.orbitEReverse E) true =
      d.gEltHom D (srcE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E)) (d.linkK E) *
        (stepGam D E true)⁻¹ *
        d.gEltHom D (tgtE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E))
          (d.linkH E) := by
  have h1 : PresentedGroup.mk (rels d D) (linkRel d D E) = 1 :=
    PresentedGroup.one_of_mem (linkRel_mem_rels d D E)
  have h2 : d.gEltHom D (srcE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E))
        (d.linkK E) * (stepGam D E true)⁻¹ *
        d.gEltHom D (tgtE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E)) (d.linkH E) =
      stepGam D (Work.ORBassSerre.orbitEReverse E) true := by
    rw [linkRel, map_mul, map_inv, map_mul, map_mul, map_inv, mk_stepWord, mk_stepWord] at h1
    exact mul_inv_eq_one.mp h1
  exact h2.symm

/-- The orbit of the move along `E` from the source end to the target end is the orbit `E`. -/
theorem orbit_move_true {d : TreeDatum G V} (E : Work.ORBassSerre.orbitE G V) :
    (Quotient.mk'' (d.move E true) : Work.ORBassSerre.orbitE G V) = E := by
  rw [show d.move E true = d.elift E from rfl, d.elift_orbit]

/-- The orbit of the move along `E` from the target end to the source end is the reversed
orbit `orbitEReverse E`. -/
theorem orbit_move_false {d : TreeDatum G V} (E : Work.ORBassSerre.orbitE G V) :
    (Quotient.mk'' (d.move E false) : Work.ORBassSerre.orbitE G V) =
      Work.ORBassSerre.orbitEReverse E := by
  have hmove : d.move E false = (((d.sElt E)⁻¹ • d.elift E).reverse) := rfl
  have hE : Work.ORBassSerre.orbitEReverse E = Quotient.mk'' ((d.elift E).reverse) := by
    conv_lhs => rw [← d.elift_orbit E]
    rw [Work.ORBassSerre.orbitEReverse_mk]
  rw [hmove, hE]
  refine Quotient.sound (MulAction.orbitRel_apply.mpr ⟨(d.sElt E)⁻¹, ?_⟩)
  exact GraphAction.smul_reverse_apply (d.sElt E)⁻¹ (d.elift E)

namespace PathWord

variable {d : TreeDatum G V}

/-- The letter at position `k` fixes the `k`-th vertex of the walk. -/
theorem letter_smul_vert (W : PathWord d) (k : ℕ) (hk : k ≤ W.len) :
    ((W.letter k).2 : G) • d.vert (W.orb k) = d.vert (W.orb k) := by
  rw [← W.letter_orbit k hk]
  exact Letter.smul_vert d (W.letter k)

/-- The product in `G` of the letters and stable letters of the walk before position `k`. -/
noncomputable def pre (W : PathWord d) : ℕ → G
  | 0 => 1
  | (k + 1) => W.pre k * ((W.letter k).2 : G) * d.moveElt (W.stepE k) (W.stepB k)

@[simp] theorem pre_zero (W : PathWord d) : W.pre 0 = 1 := rfl

/-- The recursion for `pre`. -/
theorem pre_succ (W : PathWord d) (k : ℕ) :
    W.pre (k + 1) = W.pre k * ((W.letter k).2 : G) * d.moveElt (W.stepE k) (W.stepB k) := rfl

/-- The `k`-th vertex of the walk. -/
noncomputable def z (W : PathWord d) (k : ℕ) : V := W.pre k • d.vert (W.orb k)

/-- The `k`-th arrow of the walk. -/
noncomputable def F (W : PathWord d) (k : ℕ) : Quiver.Total V :=
  (W.pre k * ((W.letter k).2 : G)) • d.move (W.stepE k) (W.stepB k)

/-- The `k`-th arrow of the walk starts at the `k`-th vertex. -/
theorem F_left (W : PathWord d) (k : ℕ) (hk : k < W.len) : (W.F k).left = W.z k := by
  rw [F, total_smul_left, d.move_left, W.step_src k hk, mul_smul,
    W.letter_smul_vert k (le_of_lt hk), z]

/-- The `k`-th arrow of the walk ends at the `(k+1)`-st vertex. -/
theorem F_right (W : PathWord d) (k : ℕ) (hk : k < W.len) : (W.F k).right = W.z (k + 1) := by
  rw [F, total_smul_right, d.move_right, W.step_tgt k hk, ← mul_smul, ← pre_succ, z]

/-- The product in `Γ` of the letters and stable letters of the walk before position `k`. -/
noncomputable def tpre (W : PathWord d) (D : PresData d) : ℕ → Gamma d D
  | 0 => 1
  | (k + 1) => W.tpre D k * Letter.gam (W.letter k) D * stepGam D (W.stepE k) (W.stepB k)

@[simp] theorem tpre_zero (W : PathWord d) (D : PresData d) : W.tpre D 0 = 1 := rfl

/-- The recursion for `tpre`. -/
theorem tpre_succ (W : PathWord d) (D : PresData d) (k : ℕ) :
    W.tpre D (k + 1) =
      W.tpre D k * Letter.gam (W.letter k) D * stepGam D (W.stepE k) (W.stepB k) := rfl

/-- The element of `Γ` attached to the word. -/
noncomputable def elt (W : PathWord d) (D : PresData d) : Gamma d D :=
  W.tpre D W.len * Letter.gam (W.letter W.len) D

/-- The image in `G` of `tpre k` is `pre k`. -/
theorem Φ_tpre (W : PathWord d) (D : PresData d) (k : ℕ) :
    Φ d D (W.tpre D k) = W.pre k := by
  induction k with
  | zero => simp [tpre, pre]
  | succ k ih => rw [tpre_succ, pre_succ, map_mul, map_mul, ih, Letter.Φ_gam, Φ_stepGam]

/-- The image in `G` of `elt` is the total product of the letters and stable letters. -/
theorem Φ_elt (W : PathWord d) (D : PresData d) :
    Φ d D (W.elt D) = W.pre W.len * ((W.letter W.len).2 : G) := by
  rw [elt, map_mul, Φ_tpre, Letter.Φ_gam]

/-- A path word is *closed* if its walk is a loop in the quotient graph. -/
def Closed (W : PathWord d) : Prop := W.orb W.len = W.orb 0

/-- A path word is *reduced* if no two consecutive arrows of its walk are mutually inverse. -/
def Reduced (W : PathWord d) : Prop := ∀ k, k + 1 < W.len → W.F (k + 1) ≠ (W.F k).reverse

/-- If the `elt` of a closed path word is trivial in `G`, then the walk is closed in `V`. -/
theorem z_closed (W : PathWord d) (D : PresData d) (hcl : W.Closed)
    (hΦ : Φ d D (W.elt D) = 1) : W.z W.len = W.z 0 := by
  have h : W.pre W.len * ((W.letter W.len).2 : G) = 1 := by
    rw [← Φ_elt]; exact hΦ
  have hpre : W.pre W.len = ((W.letter W.len).2 : G)⁻¹ := by
    calc W.pre W.len
        = W.pre W.len * ((W.letter W.len).2 : G) * (((W.letter W.len).2 : G))⁻¹ := by
          rw [mul_inv_cancel_right]
      _ = 1 * (((W.letter W.len).2 : G))⁻¹ := by rw [h]
      _ = (((W.letter W.len).2 : G))⁻¹ := by rw [one_mul]
  have hmem : ((W.letter W.len).2 : G) ∈ d.vgroup (W.orb W.len) := by
    rw [← W.letter_orbit W.len le_rfl]; exact (W.letter W.len).2.2
  have hfix : (((W.letter W.len).2 : G))⁻¹ • d.vert (W.orb W.len) = d.vert (W.orb W.len) :=
    MulAction.mem_stabilizer_iff.mp (inv_mem hmem)
  rw [z, hpre, hfix, z, hcl, pre_zero, one_smul]

/-- **The walk lemma.**  A reduced closed path word whose `elt` lies in the kernel of `Φ` is
trivial. -/
theorem elt_eq_one_of_reduced_closed (D : PresData d) (hT : Work.ORBassSerre.IsTree V)
    (W : PathWord d) (hred : W.Reduced) (hcl : W.Closed) (hΦ : Φ d D (W.elt D) = 1) :
    W.elt D = 1 := by
  rcases Nat.eq_zero_or_pos W.len with hlen | hlen
  · have h1 : ((W.letter 0).2 : G) = 1 := by
      have h := hΦ
      rw [elt, hlen, tpre_zero, map_mul, map_one, one_mul, Letter.Φ_gam] at h
      exact h
    have h2 : (W.letter 0).2 = 1 := Subtype.ext h1
    rw [elt, hlen, tpre_zero, one_mul]
    show Letter.gam (W.letter 0) D = 1
    rw [Letter.gam, h2, map_one]
  · obtain ⟨k, hk, hback⟩ :=
      Work.ORBassSerre.Tree.Walk.exists_consecutive_backtrack_of_closed_walk (hT := hT)
        W.len hlen (z := fun k => W.z k) (F := fun k => W.F k)
        (fun k hk => W.F_left k hk) (fun k hk => W.F_right k hk) (W.z_closed D hcl hΦ)
    exact absurd hback (hred k hk)

end PathWord

end Walk

end TreeDatum

end Work.ORBassSerre.Action.Structure
