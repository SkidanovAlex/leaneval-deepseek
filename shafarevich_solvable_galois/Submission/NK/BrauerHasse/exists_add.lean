/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Addition in the profinite cohomology `H²(U, Z/p)`

`NK.BrauerHasse.H2Profinite p U` is the filtered colimit of the finite levels
`NK.BrauerHasse.LevelH2 p U L = H²(U/(U ∩ Gal(K'/L)), Z/p)` along the inflation maps
`NK.BrauerHasse.levelMap`.  Since every level is a `Z/p`-module and the transition maps are
additive, the additive structure survives to the colimit: two classes represented at levels `L`
and `L'` are added by inflating both to the join `L ⊔ L'` — which dominates both, because the
finite Galois intermediate fields form a directed lattice (`L ⊔ L'` is the compositum, again
finite and Galois over `K`) — and adding the two inflated level classes there.

The content of this file is the *well-definedness* of this operation.

* The value on level representatives is
  `joinSumAux L a L' b = ofLevel (L ⊔ L') ((levelMap le_sup_left) a + (levelMap le_sup_right) b)`.
* `joinSumAux_congr` shows that this expression is compatible with the inflation maps in *both*
  variables; this is exactly the hypothesis required by the universal property
  `H2Profinite.lift` of the colimit.
* Two applications of `H2Profinite.lift` (first in the second variable, then in the first) turn
  the level-wise formula into the binary map `H2Profinite.joinAdd p U` of the colimit, whose
  defining property is `H2Profinite.joinAdd_ofLevel`.
* `NK.BrauerHasse.exists_add` records that *some* binary map of `H2Profinite p U` has the
  expected value on level representatives.  Its witness here is `H2Profinite.joinAdd p U`.

Two consequences of the defining property are recorded as well, since the value of the sum is of
course independent of the level at which it is computed:

* `H2Profinite.joinAdd_ofLevel_le` — the sum may be evaluated at *any* common upper bound
  `M ≥ L, L'` of the two levels (not only at the join `L ⊔ L'`);
* `H2Profinite.joinAdd_ofLevel_self` — for two classes of the *same* level the operation is the
  level-wise addition.

Everything except `exists_add`, `H2Profinite.joinAdd` and its two evaluation rules is `private`:
the auxiliary names are an implementation detail of this file.
-/

import Mathlib
import Submission.NK.BrauerHasse.Profinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

set_option maxHeartbeats 1600000

set_option autoImplicit false

universe u

namespace NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {p : ℕ} {U : Subgroup Gal(K'/K)}

/-! ## Compatibility lemmas for the inflation maps -/

/-- The inflation map between two levels depends only on the inclusion, not on the proof of it. -/
private lemma levelMap_congr_apply {L L' : FiniteGaloisIntermediateField K K'} {h h' : L ≤ L'}
    (x : LevelH2 p U L) :
    (levelMap p (U := U) h) x = (levelMap p (U := U) h') x := by
  rw [Subsingleton.elim h h']

/-- **Composition of the inflation maps, element-wise**: inflating along `h₁` and then along `h₂`
is inflating along `h₁.trans h₂`. -/
private lemma levelMap_trans_apply {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'}
    (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) (x : LevelH2 p U L₁) :
    (levelMap p (U := U) h₂) ((levelMap p (U := U) h₁) x) =
      (levelMap p (U := U) (h₁.trans h₂)) x := by
  have h := congrArg (fun (f : LevelH2 p U L₁ ⟶ LevelH2 p U L₃) => f x)
    (levelMap_comp p (U := U) h₁ h₂)
  simpa [CategoryTheory.comp_apply] using h

/-- The quotient map attached to the identity inclusion is the identity. -/
private lemma levelQuotHom_self (L : FiniteGaloisIntermediateField K K') :
    levelQuotHom (U := U) (le_rfl : L ≤ L) = MonoidHom.id (LevelGroup U L) := by
  simp only [levelQuotHom]
  exact QuotientGroup.map_id _ _

/-- **The inflation map of the identity inclusion is the identity.** -/
private lemma levelMap_self (L : FiniteGaloisIntermediateField K K') :
    levelMap p (U := U) (le_rfl : L ≤ L) = 𝟙 (LevelH2 p U L) := by
  simp only [levelMap]
  rw [levelQuotHom_self, H2.map_id]

/-- Element-wise form of `levelMap_self`. -/
private lemma levelMap_self_apply {L : FiniteGaloisIntermediateField K K'} (x : LevelH2 p U L) :
    (levelMap p (U := U) (le_rfl : L ≤ L)) x = x := by
  rw [levelMap_self]
  exact ConcreteCategory.id_apply x

/-! ## The sum of two level classes, computed at the join of the two levels -/

/-- **The sum of two level classes, taken at the join of the levels**: both classes are first
inflated to `L ⊔ L'`, which dominates both, and then added there. -/
private noncomputable def joinSumAux (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L)
    (L' : FiniteGaloisIntermediateField K K') (b : LevelH2 p U L') : H2Profinite p U :=
  H2Profinite.ofLevel (L ⊔ L')
    ((levelMap p (U := U) (le_sup_left : L ≤ L ⊔ L')) a +
     (levelMap p (U := U) (le_sup_right : L' ≤ L ⊔ L')) b)

/-- **Well-definedness of `joinSumAux` with respect to the inflation maps.**  Replacing `a` by its
inflation to a larger level `L₂ ≥ L₁` and `b` by its inflation to a larger level `L₂' ≥ L₁'` does
not change the value of `joinSumAux`; this is exactly the compatibility required by the universal
property `H2Profinite.lift` of the colimit.

Both sides are compared at the common level `L₂ ⊔ L₂'`, where the two summands agree by
`levelMap_trans_apply` (composition of the inflations) together with proof irrelevance of the
inclusions. -/
private lemma joinSumAux_congr {L₁ L₂ L₁' L₂' : FiniteGaloisIntermediateField K K'}
    (h : L₁ ≤ L₂) (h' : L₁' ≤ L₂') (a : LevelH2 p U L₁) (b : LevelH2 p U L₁') :
    joinSumAux L₂ ((levelMap p (U := U) h) a) L₂' ((levelMap p (U := U) h') b) =
      joinSumAux L₁ a L₁' b := by
  have hi : L₁ ⊔ L₁' ≤ L₂ ⊔ L₂' := sup_le_sup h h'
  -- Both sums agree after inflation to the common level `L₂ ⊔ L₂'`.
  have key : (levelMap p (U := U) (le_sup_left : L₂ ≤ L₂ ⊔ L₂')) ((levelMap p (U := U) h) a)
        + (levelMap p (U := U) (le_sup_right : L₂' ≤ L₂ ⊔ L₂')) ((levelMap p (U := U) h') b)
      = (levelMap p (U := U) hi)
          ((levelMap p (U := U) (le_sup_left : L₁ ≤ L₁ ⊔ L₁')) a
            + (levelMap p (U := U) (le_sup_right : L₁' ≤ L₁ ⊔ L₁')) b) := by
    rw [map_add]
    congr 1
    · rw [levelMap_trans_apply (le_sup_left : L₁ ≤ L₁ ⊔ L₁') hi a,
        levelMap_trans_apply h (le_sup_left : L₂ ≤ L₂ ⊔ L₂') a]
    · rw [levelMap_trans_apply (le_sup_right : L₁' ≤ L₁ ⊔ L₁') hi b,
        levelMap_trans_apply h' (le_sup_right : L₂' ≤ L₂ ⊔ L₂') b]
  rw [joinSumAux, joinSumAux, key]
  exact H2Profinite.ofLevel_levelMap hi _

/-! ## The two-fold lift to the colimit -/

/-- **Addition of a fixed class of a finite level.**  For `a : LevelH2 p U L` the compatible
family `L' ↦ b ↦ joinSumAux L a L' b` (compatible by `joinSumAux_congr` with `h = le_rfl`)
descends to the colimit `H2Profinite p U`. -/
private noncomputable def joinSumLeft (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) : H2Profinite p U → H2Profinite p U :=
  H2Profinite.lift (p := p) (U := U) (fun L' b => joinSumAux L a L' b) (by
    intro L'₁ L'₂ h b
    simpa only [levelMap_self_apply] using
      (joinSumAux_congr (p := p) (U := U) (L₁ := L) (L₂ := L) (L₁' := L'₁) (L₂' := L'₂)
        (le_rfl : L ≤ L) h a b))

/-- `joinSumLeft` is compatible with the inflation maps in its first variable: the family
`L ↦ a ↦ joinSumLeft L a` is compatible on the levels, so it descends to the colimit. -/
private lemma joinSumLeft_congr {L₁ L₂ : FiniteGaloisIntermediateField K K'} (h : L₁ ≤ L₂)
    (a : LevelH2 p U L₁) :
    joinSumLeft L₂ ((levelMap p (U := U) h) a) = joinSumLeft L₁ a := by
  funext x
  obtain ⟨L', b, rfl⟩ := H2Profinite.ofLevel_surjective x
  change joinSumAux L₂ ((levelMap p (U := U) h) a) L' b = joinSumAux L₁ a L' b
  simpa only [levelMap_self_apply] using
    (joinSumAux_congr (p := p) (U := U) (L₁ := L₁) (L₂ := L₂) (L₁' := L') (L₂' := L')
      h (le_rfl : L' ≤ L') a b)

/-! ## The addition -/

/-- **Addition in the profinite cohomology `H²(U, Z/p)`.**  The compatible family
`L ↦ a ↦ joinSumLeft L a` descends to a binary map on the colimit: two classes represented at
finite levels `L` and `L'` are added by inflating both to the join `L ⊔ L'` and adding there
(`H2Profinite.joinAdd_ofLevel`).  This is a witness of `NK.BrauerHasse.exists_add`. -/
noncomputable def H2Profinite.joinAdd (p : ℕ) (U : Subgroup Gal(K'/K)) :
    H2Profinite p U → H2Profinite p U → H2Profinite p U :=
  H2Profinite.lift (p := p) (U := U) (fun L a => joinSumLeft L a) (by
    intro L₁ L₂ h a
    exact joinSumLeft_congr h a)

/-- **The computation rule of `H2Profinite.joinAdd` on level representatives.** -/
theorem H2Profinite.joinAdd_ofLevel (p : ℕ) (U : Subgroup Gal(K'/K))
    (L L' : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) (b : LevelH2 p U L') :
    H2Profinite.joinAdd p U (H2Profinite.ofLevel L a) (H2Profinite.ofLevel L' b) =
      H2Profinite.ofLevel (L ⊔ L')
        ((levelMap p (U := U) (le_sup_left : L ≤ L ⊔ L')) a +
         (levelMap p (U := U) (le_sup_right : L' ≤ L ⊔ L')) b) := rfl

/-- **The sum of two level classes may be evaluated at any common upper bound of the two
levels.**  For `M` dominating both `L` and `L'`, the sum of a class of level `L` and a class of
level `L'` is the class, at level `M`, of the sum of their inflations to `M`.

(One may take `M = L ⊔ L'`: this is `H2Profinite.joinAdd_ofLevel`.  The point here is that the
value does not depend on the choice of a dominating level.) -/
theorem H2Profinite.joinAdd_ofLevel_le (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' M : FiniteGaloisIntermediateField K K'} (h₁ : L ≤ M) (h₂ : L' ≤ M)
    (a : LevelH2 p U L) (b : LevelH2 p U L') :
    H2Profinite.joinAdd p U (H2Profinite.ofLevel L a) (H2Profinite.ofLevel L' b) =
      H2Profinite.ofLevel M ((levelMap p (U := U) h₁) a + (levelMap p (U := U) h₂) b) := by
  have h : L ⊔ L' ≤ M := sup_le h₁ h₂
  have key : (levelMap p (U := U) h)
        ((levelMap p (U := U) (le_sup_left : L ≤ L ⊔ L')) a +
          (levelMap p (U := U) (le_sup_right : L' ≤ L ⊔ L')) b)
      = (levelMap p (U := U) h₁) a + (levelMap p (U := U) h₂) b := by
    rw [map_add]
    congr 1
    · rw [levelMap_trans_apply (le_sup_left : L ≤ L ⊔ L') h a]
    · rw [levelMap_trans_apply (le_sup_right : L' ≤ L ⊔ L') h b]
  rw [H2Profinite.joinAdd_ofLevel, ← key]
  exact (H2Profinite.ofLevel_levelMap (p := p) (U := U) h _).symm

/-- **`H2Profinite.joinAdd` restricted to a single level is the level-wise addition.** -/
theorem H2Profinite.joinAdd_ofLevel_self (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a b : LevelH2 p U L) :
    H2Profinite.joinAdd p U (H2Profinite.ofLevel L a) (H2Profinite.ofLevel L b) =
      H2Profinite.ofLevel L (a + b) := by
  have hb : (levelMap p (U := U) (le_sup_right : L ≤ L ⊔ L)) b =
      (levelMap p (U := U) (le_sup_left : L ≤ L ⊔ L)) b := levelMap_congr_apply b
  have key : (levelMap p (U := U) (le_sup_left : L ≤ L ⊔ L)) a +
        (levelMap p (U := U) (le_sup_right : L ≤ L ⊔ L)) b =
      (levelMap p (U := U) (le_sup_left : L ≤ L ⊔ L)) (a + b) := by
    rw [map_add, hb]
  rw [H2Profinite.joinAdd_ofLevel, key]
  exact H2Profinite.ofLevel_levelMap (p := p) (U := U)
    (le_sup_left : L ≤ L ⊔ L) (a + b)

/-! ## The requested statement -/

/-- **`H²(U, Z/p)` admits addition of classes living on different finite levels.**

For a closed subgroup `U ≤ Gal(K'/K)` there is a binary operation on the profinite cohomology
`H2Profinite p U` whose value on classes represented at finite levels `L`, `L'` is computed by
inflating both classes to the join `L ⊔ L'` — the compositum inside `K'`, which is again finite
and Galois over `K` — and adding the two inflated level classes there.

The operation is exhibited as `H2Profinite.joinAdd p U`, obtained by two applications of the
universal property `H2Profinite.lift` of the colimit; the compatibility of the level-wise formula
(`joinSumAux_congr`) is what makes the definition well-defined on the quotient. -/
theorem exists_add {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (U : Subgroup Gal(K'/K)) :
    ∃ f : NK.BrauerHasse.H2Profinite p U → NK.BrauerHasse.H2Profinite p U →
        NK.BrauerHasse.H2Profinite p U,
      ∀ (L L' : FiniteGaloisIntermediateField K K') (a : NK.BrauerHasse.LevelH2 p U L)
        (b : NK.BrauerHasse.LevelH2 p U L'),
        f (NK.BrauerHasse.H2Profinite.ofLevel L a) (NK.BrauerHasse.H2Profinite.ofLevel L' b) =
          NK.BrauerHasse.H2Profinite.ofLevel (L ⊔ L')
            ((NK.BrauerHasse.levelMap p (U := U) (le_sup_left)) a +
             (NK.BrauerHasse.levelMap p (U := U) (le_sup_right)) b) := by
  exact ⟨H2Profinite.joinAdd p U, fun L L' a b => rfl⟩

end NK.BrauerHasse
