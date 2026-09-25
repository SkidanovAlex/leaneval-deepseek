/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Addition in the `μ_p` colimit `MuColim p V`

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

`NK.HassePrinciple.MuColim p V` (`MuColimit.lean`) is the filtered colimit of the level
cohomologies `L ↦ MuLevelH2 p V L = H²(LevelGroup V L, μ_p(L))` along the transition maps
`muLevelMap`.  Every level is a `ModuleCat CoeffInt`, and the transition maps are `CoeffInt`-linear
(hence additive), so the additive structure descends to the colimit: two classes represented at
levels `L` and `L'` are added by inflating both to the join `L ⊔ L'` — which dominates both, the
finite Galois intermediate fields being directed under `⊔` — and adding there.

This file contains the *definitions* of the operations and the elementary evaluation rules; the
group axioms are recorded separately (`exists_addCommGroup_MuColim.lean` builds the requested
`AddCommGroup` instance from them).

* `muJoinSumAux L a L' b = ofLevel (L ⊔ L') (map le_sup_left a + map le_sup_right b)`;
* `muJoinSumAux_congr` — the expression is compatible with the transition maps in both variables;
* two applications of the universal property `LevelSystem.lift` turn it into the binary map
  `muJoinAdd`, with the `rfl`-level computation rule `muJoinAdd_ofLevel`;
* `muJoinAdd_ofLevel_le` — the sum may be evaluated at *any* common upper bound of the two levels;
* `muJoinAdd_ofLevel_self` — on a single level, `muJoinAdd` is the level-wise addition;
* `muColimZero = ofLevel ⊥ 0`, with `muColimZero_ofLevel : ofLevel L 0 = muColimZero`;
* `muColimNeg`, with `muColimNeg_ofLevel : muColimNeg (ofLevel L a) = ofLevel L (-a)`.

A remark on the types (`(muLevelSystem p V).obj L` versus `MuLevelH2 p V L`): the two are
definitionally equal (`muLevelSystem`'s `obj` field *is* `MuLevelH2 p V ·`), but type class
search does not unfold the `def` `muLevelSystem`, and neither does the matcher of `rw` at the
transparency it uses.  The `LevelSystem` API (`lift`, `map`, `ofLevel`, `map_comp`, …) is stated
with `(muLevelSystem p V).obj L`, so all the lemmas below use that form as well; the instance
`instAddCommGroupMuLevelObj` transports the `ModuleCat CoeffInt`-structure of `MuLevelH2 p V L` to
it, and the defeq conversion at the boundary (e.g. in the final theorem, whose statement uses
`MuLevelH2 p V L`) is handled by `exact`/`convert` at default transparency.
-/

import Mathlib
import Submission.NK.HassePrinciple.MuColimit

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

variable (p : ℕ) (V : Subgroup Gal(K'/K))

/-- The level objects of the `μ_p` level system, in the projection form used by the `LevelSystem`
API, carry the `ModuleCat CoeffInt`-structure of `MuLevelH2 p V L`.  (They are definitionally
equal, but type class search does not unfold the `def` `muLevelSystem`, so the instance has to be
installed under the projection form as well.) -/
noncomputable instance instAddCommGroupMuLevelObj (L : FiniteGaloisIntermediateField K K') :
    AddCommGroup ((muLevelSystem p V).obj L) :=
  inferInstanceAs (AddCommGroup (MuLevelH2 p V L))

/-! ## The transition maps of the level system are additive -/

lemma muLevelSystem_map_add {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x y : (muLevelSystem p V).obj L) :
    (muLevelSystem p V).map h (x + y) =
      (muLevelSystem p V).map h x + (muLevelSystem p V).map h y :=
  map_add _ x y

lemma muLevelSystem_map_zero {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    (muLevelSystem p V).map h (0 : (muLevelSystem p V).obj L) = 0 :=
  map_zero _

lemma muLevelSystem_map_neg {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : (muLevelSystem p V).obj L) :
    (muLevelSystem p V).map h (-x) = -(muLevelSystem p V).map h x :=
  map_neg _ x

lemma muLevelSystem_map_refl_apply {L : FiniteGaloisIntermediateField K K'}
    (x : (muLevelSystem p V).obj L) :
    (muLevelSystem p V).map (le_rfl : L ≤ L) x = x :=
  (muLevelSystem p V).map_refl L x

lemma muLevelSystem_map_trans_apply {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'}
    (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) (x : (muLevelSystem p V).obj L₁) :
    (muLevelSystem p V).map h₂ ((muLevelSystem p V).map h₁ x) =
      (muLevelSystem p V).map (h₁.trans h₂) x :=
  (muLevelSystem p V).map_comp h₁ h₂ x

lemma muLevelSystem_map_congr_apply {L L' : FiniteGaloisIntermediateField K K'}
    {h h' : L ≤ L'} (x : (muLevelSystem p V).obj L) :
    (muLevelSystem p V).map h x = (muLevelSystem p V).map h' x := by
  rw [Subsingleton.elim h h']

/-! ## The sum of two level classes, taken at the join of the levels -/

/-- **The sum of two level classes, taken at the join of the two levels**: both classes are
inflated to `L ⊔ L'`, which dominates both, and added there. -/
noncomputable def muJoinSumAux (L : FiniteGaloisIntermediateField K K')
    (a : (muLevelSystem p V).obj L) (L' : FiniteGaloisIntermediateField K K')
    (b : (muLevelSystem p V).obj L') : MuColim p V :=
  MuColim.ofLevel p V (L ⊔ L')
    ((muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L') a +
     (muLevelSystem p V).map (le_sup_right : L' ≤ L ⊔ L') b)

/-- **Well-definedness of `muJoinSumAux` with respect to the transition maps.**  Replacing `a` by
its inflation to a larger level `L₂ ≥ L₁` and `b` by its inflation to a larger level `L₂' ≥ L₁'`
does not change the value of `muJoinSumAux`; this is exactly the compatibility required by the
universal property `LevelSystem.lift` of the colimit.

Both sides are compared at the common level `L₂ ⊔ L₂'`, where the two summands agree by
`muLevelSystem_map_trans_apply` (composition of the inflations) together with proof irrelevance of
the inclusions. -/
lemma muJoinSumAux_congr {L₁ L₂ L₁' L₂' : FiniteGaloisIntermediateField K K'}
    (h : L₁ ≤ L₂) (h' : L₁' ≤ L₂') (a : (muLevelSystem p V).obj L₁)
    (b : (muLevelSystem p V).obj L₁') :
    muJoinSumAux p V L₂ ((muLevelSystem p V).map h a) L₂' ((muLevelSystem p V).map h' b) =
      muJoinSumAux p V L₁ a L₁' b := by
  have hi : L₁ ⊔ L₁' ≤ L₂ ⊔ L₂' := sup_le_sup h h'
  have key : (muLevelSystem p V).map (le_sup_left : L₂ ≤ L₂ ⊔ L₂')
        ((muLevelSystem p V).map h a)
      + (muLevelSystem p V).map (le_sup_right : L₂' ≤ L₂ ⊔ L₂')
        ((muLevelSystem p V).map h' b)
      = (muLevelSystem p V).map hi
          ((muLevelSystem p V).map (le_sup_left : L₁ ≤ L₁ ⊔ L₁') a
            + (muLevelSystem p V).map (le_sup_right : L₁' ≤ L₁ ⊔ L₁') b) := by
    rw [muLevelSystem_map_add]
    congr 1
    · rw [muLevelSystem_map_trans_apply (p := p) (V := V) (le_sup_left : L₁ ≤ L₁ ⊔ L₁') hi a,
          muLevelSystem_map_trans_apply (p := p) (V := V) h (le_sup_left : L₂ ≤ L₂ ⊔ L₂') a]
    · rw [muLevelSystem_map_trans_apply (p := p) (V := V) (le_sup_right : L₁' ≤ L₁ ⊔ L₁') hi b,
          muLevelSystem_map_trans_apply (p := p) (V := V) h' (le_sup_right : L₂' ≤ L₂ ⊔ L₂') b]
  rw [muJoinSumAux, muJoinSumAux, key]
  exact (muLevelSystem p V).ofLevel_map hi _

/-! ## The two-fold lift to the colimit -/

/-- **Addition of a fixed class of a finite level.**  For `a` a class of the level `L` the
compatible family `L' ↦ b ↦ muJoinSumAux L a L' b` (compatible by `muJoinSumAux_congr` with
`h = le_rfl`) descends to the colimit `MuColim p V`. -/
noncomputable def muJoinSumLeft (L : FiniteGaloisIntermediateField K K')
    (a : (muLevelSystem p V).obj L) : MuColim p V → MuColim p V :=
  (muLevelSystem p V).lift (fun L' b => muJoinSumAux p V L a L' b) (by
    intro L'₁ L'₂ h b
    simpa only [muLevelSystem_map_refl_apply] using
      (muJoinSumAux_congr (p := p) (V := V) (L₁ := L) (L₂ := L) (L₁' := L'₁) (L₂' := L'₂)
        (le_rfl : L ≤ L) h a b))

/-- `muJoinSumLeft` is compatible with the transition maps in its first variable: the family
`L ↦ a ↦ muJoinSumLeft L a` is compatible on the levels, so it descends to the colimit. -/
lemma muJoinSumLeft_congr {L₁ L₂ : FiniteGaloisIntermediateField K K'} (h : L₁ ≤ L₂)
    (a : (muLevelSystem p V).obj L₁) :
    muJoinSumLeft p V L₂ ((muLevelSystem p V).map h a) = muJoinSumLeft p V L₁ a := by
  funext x
  obtain ⟨L', b, rfl⟩ := (muLevelSystem p V).ofLevel_surjective x
  change muJoinSumAux p V L₂ ((muLevelSystem p V).map h a) L' b =
    muJoinSumAux p V L₁ a L' b
  simpa only [muLevelSystem_map_refl_apply] using
    (muJoinSumAux_congr (p := p) (V := V) (L₁ := L₁) (L₂ := L₂) (L₁' := L') (L₂' := L')
      h (le_rfl : L' ≤ L') a b)

/-! ## The addition -/

/-- **Addition in the `μ_p` colimit `MuColim p V`.**  The compatible family
`L ↦ a ↦ muJoinSumLeft L a` descends to a binary map on the colimit: two classes represented at
levels `L` and `L'` are added by inflating both to the join `L ⊔ L'` and adding there
(`muJoinAdd_ofLevel`). -/
noncomputable def muJoinAdd : MuColim p V → MuColim p V → MuColim p V :=
  (muLevelSystem p V).lift (fun L a => muJoinSumLeft p V L a) (by
    intro L₁ L₂ h a
    exact muJoinSumLeft_congr p V h a)

/-- **The computation rule of `muJoinAdd` on level representatives.** -/
theorem muJoinAdd_ofLevel (L L' : FiniteGaloisIntermediateField K K')
    (a : (muLevelSystem p V).obj L) (b : (muLevelSystem p V).obj L') :
    muJoinAdd p V (MuColim.ofLevel p V L a) (MuColim.ofLevel p V L' b) =
      MuColim.ofLevel p V (L ⊔ L')
        ((muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L') a +
         (muLevelSystem p V).map (le_sup_right : L' ≤ L ⊔ L') b) := rfl

/-- **The sum of two level classes may be evaluated at any common upper bound of the two
levels.**  For `M` dominating both `L` and `L'`, the sum of a class of level `L` and a class of
level `L'` is the class, at level `M`, of the sum of their inflations to `M`. -/
theorem muJoinAdd_ofLevel_le {L L' M : FiniteGaloisIntermediateField K K'} (h₁ : L ≤ M)
    (h₂ : L' ≤ M) (a : (muLevelSystem p V).obj L) (b : (muLevelSystem p V).obj L') :
    muJoinAdd p V (MuColim.ofLevel p V L a) (MuColim.ofLevel p V L' b) =
      MuColim.ofLevel p V M
        ((muLevelSystem p V).map h₁ a + (muLevelSystem p V).map h₂ b) := by
  have h : L ⊔ L' ≤ M := sup_le h₁ h₂
  have key : (muLevelSystem p V).map h
        ((muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L') a
          + (muLevelSystem p V).map (le_sup_right : L' ≤ L ⊔ L') b)
      = (muLevelSystem p V).map h₁ a + (muLevelSystem p V).map h₂ b := by
    rw [muLevelSystem_map_add]
    congr 1
    · rw [muLevelSystem_map_trans_apply (p := p) (V := V) (le_sup_left : L ≤ L ⊔ L') h a]
    · rw [muLevelSystem_map_trans_apply (p := p) (V := V) (le_sup_right : L' ≤ L ⊔ L') h b]
  rw [muJoinAdd_ofLevel, ← key]
  exact ((muLevelSystem p V).ofLevel_map h _).symm

/-- **`muJoinAdd` restricted to a single level is the level-wise addition.** -/
theorem muJoinAdd_ofLevel_self (L : FiniteGaloisIntermediateField K K')
    (a b : (muLevelSystem p V).obj L) :
    muJoinAdd p V (MuColim.ofLevel p V L a) (MuColim.ofLevel p V L b) =
      MuColim.ofLevel p V L (a + b) := by
  have hb : (muLevelSystem p V).map (le_sup_right : L ≤ L ⊔ L) b =
      (muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L) b :=
    muLevelSystem_map_congr_apply (p := p) (V := V) b
  have key : (muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L) a
        + (muLevelSystem p V).map (le_sup_right : L ≤ L ⊔ L) b =
      (muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L) (a + b) := by
    rw [muLevelSystem_map_add, hb]
  rw [muJoinAdd_ofLevel, key]
  exact (muLevelSystem p V).ofLevel_map (le_sup_left : L ≤ L ⊔ L) (a + b)

/-! ## Zero and negation -/

/-- **The distinguished zero of the `μ_p` colimit**: the class of `0` at the bottom level. -/
noncomputable def muColimZero : MuColim p V :=
  MuColim.ofLevel p V ⊥ 0

/-- The class of `0` at any level is the distinguished zero. -/
theorem muColimZero_ofLevel (L : FiniteGaloisIntermediateField K K') :
    MuColim.ofLevel p V L (0 : (muLevelSystem p V).obj L) = muColimZero p V := by
  refine ((muLevelSystem p V).ofLevel_eq_iff
    (0 : (muLevelSystem p V).obj L) (0 : (muLevelSystem p V).obj ⊥)).mpr
    ⟨L, le_rfl, bot_le, ?_⟩
  rw [muLevelSystem_map_refl_apply, muLevelSystem_map_zero]

/-- **Negation in the `μ_p` colimit**, defined through the universal property of the colimit: the
negative of the class of `a` at the level `L` is the class of `-a` at the same level. -/
noncomputable def muColimNeg : MuColim p V → MuColim p V :=
  (muLevelSystem p V).lift (fun L a => MuColim.ofLevel p V L (-a)) (by
    intro L L' h a
    refine ((muLevelSystem p V).ofLevel_eq_iff _ _).mpr ⟨L', le_rfl, h, ?_⟩
    rw [muLevelSystem_map_refl_apply, muLevelSystem_map_neg])

/-- **The computation rule of `muColimNeg` on level representatives.** -/
theorem muColimNeg_ofLevel (L : FiniteGaloisIntermediateField K K')
    (a : (muLevelSystem p V).obj L) :
    muColimNeg p V (MuColim.ofLevel p V L a) = MuColim.ofLevel p V L (-a) := rfl

end NK.HassePrinciple
