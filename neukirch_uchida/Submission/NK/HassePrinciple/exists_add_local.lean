/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Addition in the local colimit `LocalH2 p U A`

The local cohomology `NK.BrauerHasse.LocalH2 p U A` is the filtered colimit of the local level
cohomologies `NK.BrauerHasse.LocalLevelH2 p U A L = H²((U ∩ D_A)/((U ∩ D_A) ∩ Gal(K'/L)), Z/p)`
along the local inflation maps `NK.BrauerHasse.localLevelMap`, the colimit running over the
finite Galois intermediate fields `L` of `K'/K`.  Since every local level is a `Z/p`-module and
the transition maps are additive, the additive structure survives to the colimit: two classes
represented at levels `L`, `L'` are added by inflating both to the join `L ⊔ L'` (dominating both,
because the finite Galois intermediate fields form a directed lattice) and adding there.

This is *verbatim* the situation of `Submission/Work/BrauerHasse/exists_add.lean` for the global
colimit `H2Profinite p U`, and the argument is the same:

* the value on level representatives is
  `localJoinSumAux L a L' b = ofLevel (L ⊔ L') ((localLevelMap le_sup_left) a +
    (localLevelMap le_sup_right) b)`;
* `localJoinSumAux_congr` shows that this expression is compatible with the local inflation maps
  in *both* variables;
* two applications of the universal property of the local colimit (`localLift`, proved here in
  the same way as `H2Profinite.lift`) turn the level-wise formula into the binary map
  `localJoinAdd p U A`, whose defining property is `localJoinAdd_ofLevel`.

The universal property of the local colimit is *not* stated in `Submission/Work/BrauerHasse/` (only
the global one is), so `localLift` is developed here.
-/

import Mathlib
import Submission.NK.BrauerHasse.All

open CategoryTheory

set_option maxHeartbeats 1600000

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {p : ℕ} {U : Subgroup Gal(K'/K)} {A : ValuationSubring K'}

/-! ## Compatibility lemmas for the local inflation maps -/

/-- The local inflation map between two levels depends only on the inclusion, not on its proof. -/
private lemma localLevelMap_congr_apply {L L' : FiniteGaloisIntermediateField K K'}
    {h h' : L ≤ L'} (x : LocalLevelH2 p U A L) :
    (localLevelMap p U A h) x = (localLevelMap p U A h') x := by
  rw [Subsingleton.elim h h']

/-- **Composition of the local inflation maps, element-wise**: inflating along `h₁` and then along
`h₂` is inflating along `h₁.trans h₂`. -/
private lemma localLevelMap_trans_apply {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'}
    (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) (x : LocalLevelH2 p U A L₁) :
    (localLevelMap p U A h₂) ((localLevelMap p U A h₁) x) =
      (localLevelMap p U A (h₁.trans h₂)) x := by
  have h := congrArg (fun (f : LocalLevelH2 p U A L₁ ⟶ LocalLevelH2 p U A L₃) => f x)
    (localLevelMap_comp p U A h₁ h₂)
  simpa [CategoryTheory.comp_apply] using h

/-- The quotient map attached to the identity inclusion is the identity. -/
private lemma localLevelQuotHom_self (L : FiniteGaloisIntermediateField K K') :
    localLevelQuotHom U A (le_rfl : L ≤ L) = MonoidHom.id (LocalLevelGroup U A L) := by
  simp only [localLevelQuotHom]
  exact QuotientGroup.map_id _ _

/-- **The local inflation map of the identity inclusion is the identity.** -/
private lemma localLevelMap_self (L : FiniteGaloisIntermediateField K K') :
    localLevelMap p U A (le_rfl : L ≤ L) = 𝟙 (LocalLevelH2 p U A L) := by
  simp only [localLevelMap]
  rw [localLevelQuotHom_self, H2.map_id]

/-- Element-wise form of `localLevelMap_self`. -/
private lemma localLevelMap_self_apply {L : FiniteGaloisIntermediateField K K'}
    (x : LocalLevelH2 p U A L) :
    (localLevelMap p U A (le_rfl : L ≤ L)) x = x := by
  rw [localLevelMap_self]
  exact ConcreteCategory.id_apply x

/-! ## The universal property of the local colimit -/

/-- **The universal property of the local colimit `LocalH2 p U A`**: a compatible family of maps on
the local levels descends to the colimit.  This is the local analogue of
`NK.BrauerHasse.H2Profinite.lift`, proved in the same way directly from the definition of
`LocalH2` as a quotient. -/
private noncomputable def localLift {β : Sort*}
    (f : ∀ L : FiniteGaloisIntermediateField K K', LocalLevelH2 p U A L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L')
      (a : LocalLevelH2 p U A L), f L' ((localLevelMap p U A h) a) = f L a) :
    LocalH2 p U A → β :=
  Quot.lift
    (fun x : Σ L : FiniteGaloisIntermediateField K K', LocalLevelH2 p U A L => f x.1 x.2)
    (by
      intro x y hxy
      induction hxy with
      | rel x y hxy => exact (hf x.1 y.1 hxy.1 x.2).symm.trans (congrArg (f y.1) hxy.2).symm
      | refl x => rfl
      | symm x y hxy ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)

@[simp]
private lemma localLift_ofLevel {β : Sort*}
    (f : ∀ L : FiniteGaloisIntermediateField K K', LocalLevelH2 p U A L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L')
      (a : LocalLevelH2 p U A L), f L' ((localLevelMap p U A h) a) = f L a)
    (L : FiniteGaloisIntermediateField K K') (a : LocalLevelH2 p U A L) :
    localLift f hf (LocalH2.ofLevel p U A L a) = f L a := rfl

/-- **Every element of `LocalH2 p U A` comes from a local level.** -/
theorem local_ofLevel_surjective (x : LocalH2 p U A) :
    ∃ (L : FiniteGaloisIntermediateField K K') (a : LocalLevelH2 p U A L),
      LocalH2.ofLevel p U A L a = x := by
  induction x using Quot.ind with
  | _ y => exact ⟨y.1, y.2, rfl⟩

/-! ## The sum of two local level classes, computed at the join of the two levels -/

/-- **The sum of two local level classes, taken at the join of the levels**: both classes are first
inflated to `L ⊔ L'`, which dominates both, and then added there. -/
private noncomputable def localJoinSumAux (L : FiniteGaloisIntermediateField K K')
    (a : LocalLevelH2 p U A L) (L' : FiniteGaloisIntermediateField K K')
    (b : LocalLevelH2 p U A L') : LocalH2 p U A :=
  LocalH2.ofLevel p U A (L ⊔ L')
    ((localLevelMap p U A (le_sup_left : L ≤ L ⊔ L')) a +
     (localLevelMap p U A (le_sup_right : L' ≤ L ⊔ L')) b)

/-- **Well-definedness of `localJoinSumAux` with respect to the local inflation maps.**  Replacing
`a` by its inflation to a larger level `L₂ ≥ L₁` and `b` by its inflation to a larger level
`L₂' ≥ L₁'` does not change the value of `localJoinSumAux`; this is exactly the compatibility
required by the universal property of the local colimit.

Both sides are compared at the common level `L₂ ⊔ L₂'`, where the two summands agree by
`localLevelMap_trans_apply` (composition of the inflations) together with proof irrelevance of the
inclusions. -/
private lemma localJoinSumAux_congr {L₁ L₂ L₁' L₂' : FiniteGaloisIntermediateField K K'}
    (h : L₁ ≤ L₂) (h' : L₁' ≤ L₂') (a : LocalLevelH2 p U A L₁) (b : LocalLevelH2 p U A L₁') :
    localJoinSumAux L₂ ((localLevelMap p U A h) a) L₂' ((localLevelMap p U A h') b) =
      localJoinSumAux L₁ a L₁' b := by
  have hi : L₁ ⊔ L₁' ≤ L₂ ⊔ L₂' := sup_le_sup h h'
  -- Both sums agree after inflation to the common level `L₂ ⊔ L₂'`.
  have key : (localLevelMap p U A (le_sup_left : L₂ ≤ L₂ ⊔ L₂')) ((localLevelMap p U A h) a)
        + (localLevelMap p U A (le_sup_right : L₂' ≤ L₂ ⊔ L₂')) ((localLevelMap p U A h') b)
      = (localLevelMap p U A hi)
          ((localLevelMap p U A (le_sup_left : L₁ ≤ L₁ ⊔ L₁')) a
            + (localLevelMap p U A (le_sup_right : L₁' ≤ L₁ ⊔ L₁')) b) := by
    rw [map_add]
    congr 1
    · rw [localLevelMap_trans_apply (le_sup_left : L₁ ≤ L₁ ⊔ L₁') hi a,
        localLevelMap_trans_apply h (le_sup_left : L₂ ≤ L₂ ⊔ L₂') a]
    · rw [localLevelMap_trans_apply (le_sup_right : L₁' ≤ L₁ ⊔ L₁') hi b,
        localLevelMap_trans_apply h' (le_sup_right : L₂' ≤ L₂ ⊔ L₂') b]
  rw [localJoinSumAux, localJoinSumAux, key]
  exact LocalH2.ofLevel_levelMap p U A hi _

/-! ## The two-fold lift to the local colimit -/

/-- **Addition of a fixed local level class.**  For `a : LocalLevelH2 p U A L` the compatible family
`L' ↦ b ↦ localJoinSumAux L a L' b` (compatible by `localJoinSumAux_congr` with `h = le_rfl`)
descends to the colimit `LocalH2 p U A`. -/
private noncomputable def localJoinSumLeft (L : FiniteGaloisIntermediateField K K')
    (a : LocalLevelH2 p U A L) : LocalH2 p U A → LocalH2 p U A :=
  localLift (fun L' b => localJoinSumAux L a L' b) (by
    intro L'₁ L'₂ h b
    simpa only [localLevelMap_self_apply] using
      (localJoinSumAux_congr (L₁ := L) (L₂ := L) (L₁' := L'₁) (L₂' := L'₂)
        (le_rfl : L ≤ L) h a b))

/-- `localJoinSumLeft` is compatible with the local inflation maps in its first variable: the
family `L ↦ a ↦ localJoinSumLeft L a` is compatible on the levels, so it descends to the colimit. -/
private lemma localJoinSumLeft_congr {L₁ L₂ : FiniteGaloisIntermediateField K K'} (h : L₁ ≤ L₂)
    (a : LocalLevelH2 p U A L₁) :
    localJoinSumLeft L₂ ((localLevelMap p U A h) a) = localJoinSumLeft L₁ a := by
  funext x
  obtain ⟨L', b, rfl⟩ := local_ofLevel_surjective x
  change localJoinSumAux L₂ ((localLevelMap p U A h) a) L' b = localJoinSumAux L₁ a L' b
  simpa only [localLevelMap_self_apply] using
    (localJoinSumAux_congr (L₁ := L₁) (L₂ := L₂) (L₁' := L') (L₂' := L')
      h (le_rfl : L' ≤ L') a b)

/-! ## The addition -/

/-- **Addition in the local cohomology `LocalH2 p U A`.**  The compatible family
`L ↦ a ↦ localJoinSumLeft L a` descends to a binary map on the colimit: two classes represented at
finite levels `L` and `L'` are added by inflating both to the join `L ⊔ L'` and adding there
(`localJoinAdd_ofLevel`).  This is a witness of `NK.HassePrinciple.exists_add_local`. -/
noncomputable def localJoinAdd (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') :
    LocalH2 p U A → LocalH2 p U A → LocalH2 p U A :=
  localLift (fun L a => localJoinSumLeft L a) (by
    intro L₁ L₂ h a
    exact localJoinSumLeft_congr h a)

/-- **The computation rule of `localJoinAdd` on level representatives.** -/
theorem localJoinAdd_ofLevel (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L L' : FiniteGaloisIntermediateField K K') (a : LocalLevelH2 p U A L)
    (b : LocalLevelH2 p U A L') :
    localJoinAdd p U A (LocalH2.ofLevel p U A L a) (LocalH2.ofLevel p U A L' b) =
      LocalH2.ofLevel p U A (L ⊔ L')
        ((localLevelMap p U A (le_sup_left : L ≤ L ⊔ L')) a +
         (localLevelMap p U A (le_sup_right : L' ≤ L ⊔ L')) b) := rfl

/-! ## The requested statement -/

/-- **Addition in the local colimit `LocalH2 p U A`.**

The local cohomology `LocalH2 p U A` is the filtered colimit of the local level cohomologies
`LocalLevelH2 p U A L = H²((U ⊓ stabSubgroup A)/((U ⊓ stabSubgroup A) ⊓ Gal(K'/L)), Z/p)` along the
local inflation maps `localLevelMap`, and every local level is a `Z/p`-module, so the additive
structure survives to the colimit: two classes represented at local levels `L` and `L'` are added by
inflating both to the join `L ⊔ L'` and adding there.  The content is the well-definedness of this
operation, exactly as in `NK.BrauerHasse.exists_add` for the global colimit `H2Profinite p U`:
two applications of the universal property `H2Profinite.lift` (applied to the local filtered system,
whose universal property is proved in the same way) give the binary map, and the compatibility of
the level-wise formula with the local inflation maps is the hypothesis of that universal property. -/
theorem exists_add_local {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') :
    ∃ f : NK.BrauerHasse.LocalH2 p U A → NK.BrauerHasse.LocalH2 p U A →
        NK.BrauerHasse.LocalH2 p U A,
      ∀ (L L' : FiniteGaloisIntermediateField K K') (a : NK.BrauerHasse.LocalLevelH2 p U A L)
        (b : NK.BrauerHasse.LocalLevelH2 p U A L'),
        f (NK.BrauerHasse.LocalH2.ofLevel p U A L a)
            (NK.BrauerHasse.LocalH2.ofLevel p U A L' b) =
          NK.BrauerHasse.LocalH2.ofLevel p U A (L ⊔ L')
            ((NK.BrauerHasse.localLevelMap p U A (le_sup_left)) a +
             (NK.BrauerHasse.localLevelMap p U A (le_sup_right)) b) :=
  ⟨localJoinAdd p U A, fun L L' a b => rfl⟩

end NK.HassePrinciple
