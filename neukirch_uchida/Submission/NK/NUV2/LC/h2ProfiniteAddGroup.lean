import Mathlib
import Submission.NK.LocalDecomposition.loc_joinAdd
import Submission.NK.LocalDecomposition.joinAdd_laws

/-!
# The additive group structure of `H²(U, Z/p)`

`NK.BrauerHasse.H2Profinite p U` is the profinite cohomology `H²(U, Z/p)` of a closed subgroup
`U ≤ Gal(K'/K)`, defined as the filtered colimit of the finite levels
`NK.BrauerHasse.LevelH2 p U L = H²(U/(U ⊓ Gal(K'/L)), Z/p)` along the inflation maps
`NK.BrauerHasse.levelMap`.  The addition of two classes represented at different levels is
`NK.BrauerHasse.H2Profinite.joinAdd`, and its group laws (commutativity, associativity, the unit,
the existence of inverses) are on disk as `NK.LocalDecomposition.joinAdd_laws`
(`Submission/Work/LocalDecomposition/joinAdd_laws.lean`), as is the compatibility of `joinAdd` with
the restriction and the localisation (`NK.LocalDecomposition.H2Profinite.res_joinAdd`,
`NK.LocalDecomposition.loc_joinAdd`).

What was *not* on disk is the packaging of those laws as an `AddCommGroup` structure, which is what
this file provides:

* `NK.NUV2.LC.instAddCommGroupH2Profinite` — an `AddCommGroup` structure on `H2Profinite p U`
  whose addition **is** `H2Profinite.joinAdd` (the structure literal is transparent, and its zero is
  the very term of the pre-existing `NK.BrauerHasse.instZeroH2Profinite`, so that nothing already
  proved about `0` or about `joinAdd` changes meaning);
* `NK.BrauerHasse.exists_addCommGroup_H2Profinite` — the same structure in the existential form
  used elsewhere in the workspace for `H2Units` and `MuColim`
  (`NK.HassePrinciple.exists_addCommGroup_H2Units`), with the compatibility
  `H2Profinite.ofLevel_add` of the structure maps with the addition;
* `NK.BrauerHasse.H2Profinite.add_ofLevel_le` (the sum of two classes of different levels,
  computed at any common upper bound), `...add_ofLevel`, `...joinAdd_eq_add`,
  `...res_add` and `...loc_add` (the restriction and the localisation are additive),
  `...ofLevel_nsmul` and `...nsmul_p_eq_zero` (`H²(U, Z/p)` is `p`-torsion);
* `NK.NUV2.LC.instModuleZModH2Profinite` — the induced `Module (ZMod p)` structure (the
  "`F_p`-vector space" used by the rank counts of Neukirch's argument).
-/

open CategoryTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.NUV2.LC

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The additive commutative group structure on `H²(U, Z/p)`.**  Its addition is
`NK.BrauerHasse.H2Profinite.joinAdd` (the level-wise addition of the colimit), its zero is the
class of the zero of the bottom level (the term of the pre-existing
`NK.BrauerHasse.instZeroH2Profinite`), and its negation is the (chosen) inverse of
`NK.LocalDecomposition.joinAdd_laws`.

The structure is written as a *literal* (not through `Classical.choose`) so that its projections
reduce: `+` is definitionally `joinAdd` and `0` is definitionally the old zero, and hence no
statement already proved in the workspace changes meaning. -/
noncomputable instance instAddCommGroupH2Profinite (p : ℕ) (U : Subgroup Gal(K'/K)) :
    AddCommGroup (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) := by
  letI : Add (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) :=
    ⟨NK.BrauerHasse.H2Profinite.joinAdd p U⟩
  letI : Neg (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) :=
    ⟨fun x => Classical.choose
      ((NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).2.2.2 x)⟩
  letI : Zero (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) :=
    ⟨Quot.mk (Relation.EqvGen (NK.BrauerHasse.colimitGen (K := K) (K' := K') p U))
      ⟨(⊥ : FiniteGaloisIntermediateField K K'), (0 : NK.BrauerHasse.LevelH2 p U ⊥)⟩⟩
  exact
    { add_assoc := (NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).2.1
      zero_add := fun a =>
        ((NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).1 _ a).trans
          ((NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).2.2.1 a)
      add_zero := (NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).2.2.1
      neg_add_cancel := fun a =>
        ((NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).1 _ a).trans
          (Classical.choose_spec
            ((NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).2.2.2 a))
      add_comm := (NK.LocalDecomposition.joinAdd_laws (K := K) (K' := K') p U).1
      nsmul := nsmulRec
      zsmul := zsmulRec }

/-- The additive group structure on the *local* cohomology `LocalH2 p U A`, transported from
`H2Profinite p (U ⊓ D_A)`: the two types are definitionally equal
(`NK.LocalDecomposition.LocalH2.eq_profinite`), but they are `def`s, so type class search does not
unfold them, and the instance has to be installed under both forms. -/
noncomputable instance instAddCommGroupLocalH2 (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') :
    AddCommGroup (NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U A) :=
  inferInstanceAs (AddCommGroup (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
    (U ⊓ NK.BrauerHasse.stabSubgroup A)))

end NK.NUV2.LC

namespace NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **`H²(U, Z/p)` is an additive commutative group** under the level-wise addition
`H2Profinite.joinAdd`, with zero the class `ofLevel ⊥ 0` and with `ofLevel` additive.

This is the existential form of the instance `NK.NUV2.LC.instAddCommGroupH2Profinite`, in the
shape used elsewhere in the workspace for the colimits `H2Units` and `MuColim`
(`NK.HassePrinciple.exists_addCommGroup_H2Units`, `..._MuColim`). -/
theorem exists_addCommGroup_H2Profinite (p : ℕ) (U : Subgroup Gal(K'/K)) :
    ∃ inst : AddCommGroup (H2Profinite p U),
      letI := inst
      ∀ (L : FiniteGaloisIntermediateField K K') (a b : LevelH2 p U L),
        H2Profinite.ofLevel L (a + b) = H2Profinite.ofLevel L a + H2Profinite.ofLevel L b :=
  ⟨NK.NUV2.LC.instAddCommGroupH2Profinite (K := K) (K' := K') p U, fun L a b =>
    (H2Profinite.joinAdd_ofLevel_self p U L a b).symm⟩

/-- The structure maps of the colimit `H²(U, Z/p)` are additive. -/
theorem H2Profinite.ofLevel_add (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a b : LevelH2 p U L) :
    H2Profinite.ofLevel L (a + b) = H2Profinite.ofLevel L a + H2Profinite.ofLevel L b :=
  (H2Profinite.joinAdd_ofLevel_self p U L a b).symm

/-- **`H2Profinite.joinAdd` is the addition of the instance.** -/
theorem H2Profinite.joinAdd_eq_add (p : ℕ) (U : Subgroup Gal(K'/K)) (x y : H2Profinite p U) :
    H2Profinite.joinAdd p U x y = x + y := rfl

/-- **The sum of two classes of different levels, evaluated at any common upper bound.** -/
theorem H2Profinite.add_ofLevel_le (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' M : FiniteGaloisIntermediateField K K'} (h₁ : L ≤ M) (h₂ : L' ≤ M)
    (a : LevelH2 p U L) (b : LevelH2 p U L') :
    H2Profinite.ofLevel L a + H2Profinite.ofLevel L' b =
      H2Profinite.ofLevel M ((levelMap p (U := U) h₁) a + (levelMap p (U := U) h₂) b) := by
  rw [← H2Profinite.ofLevel_levelMap (p := p) (U := U) h₁ a,
    ← H2Profinite.ofLevel_levelMap (p := p) (U := U) h₂ b, H2Profinite.ofLevel_add]

/-- **The sum of two classes of different levels**, computed at the join of the two levels. -/
theorem H2Profinite.add_ofLevel (p : ℕ) (U : Subgroup Gal(K'/K))
    (L L' : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) (b : LevelH2 p U L') :
    H2Profinite.ofLevel L a + H2Profinite.ofLevel L' b =
      H2Profinite.ofLevel (L ⊔ L')
        ((levelMap p (U := U) (le_sup_left : L ≤ L ⊔ L')) a +
         (levelMap p (U := U) (le_sup_right : L' ≤ L ⊔ L')) b) :=
  H2Profinite.add_ofLevel_le p U le_sup_left le_sup_right a b

/-- **The restriction is additive.** -/
theorem H2Profinite.res_add (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (x y : H2Profinite p U) :
    NK.LocalDecomposition.H2Profinite.res p h (x + y) =
      NK.LocalDecomposition.H2Profinite.res p h x +
        NK.LocalDecomposition.H2Profinite.res p h y := by
  rw [← H2Profinite.joinAdd_eq_add p U x y, NK.LocalDecomposition.H2Profinite.res_joinAdd,
    H2Profinite.joinAdd_eq_add p V (NK.LocalDecomposition.H2Profinite.res p h x)
      (NK.LocalDecomposition.H2Profinite.res p h y)]

/-- **The localisation is additive.** -/
theorem H2Profinite.loc_add (p : ℕ) (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K')
    (x y : H2Profinite p U) :
    (H2Profinite.loc p U (x + y) A : H2Profinite p (U ⊓ stabSubgroup A.1)) =
      (H2Profinite.loc p U x A : H2Profinite p (U ⊓ stabSubgroup A.1)) +
        (H2Profinite.loc p U y A : H2Profinite p (U ⊓ stabSubgroup A.1)) := by
  rw [NK.LocalDecomposition.loc_eq_res p U A (x + y),
    NK.LocalDecomposition.loc_eq_res p U A x,
    NK.LocalDecomposition.loc_eq_res p U A y]
  exact H2Profinite.res_add p (inf_le_left : U ⊓ stabSubgroup A.1 ≤ U) x y

/-- **`ofLevel` commutes with the natural number action.** -/
theorem H2Profinite.ofLevel_nsmul (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (k : ℕ) (a : LevelH2 p U L) :
    H2Profinite.ofLevel L (k • a) = k • (H2Profinite.ofLevel L a) := by
  induction k with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      exact NK.BrauerHasse.ofLevel_zero (K := K) (K' := K') (p := p) (U := U) L
  | succ k ih => rw [succ_nsmul, succ_nsmul, ← ih, ← H2Profinite.ofLevel_add]

/-- **`H²(U, Z/p)` is `p`-torsion.**  Every level is a module over `Coeff p = ULift (ZMod p)`,
where `p = 0`, and `ofLevel` commutes with the naturals, so the scalar `p` acts as zero on the
colimit. -/
theorem H2Profinite.nsmul_p_eq_zero (p : ℕ) (U : Subgroup Gal(K'/K)) (x : H2Profinite p U) :
    p • x = 0 := by
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [← H2Profinite.ofLevel_nsmul p U L p a]
  have ha : p • a = 0 := by
    have h1 : (((p : ℕ)) : Coeff.{u} p) = 0 := by
      ext
      simp
    rw [← Nat.cast_smul_eq_nsmul (Coeff.{u} p) p a, h1, zero_smul]
  rw [ha]
  exact NK.BrauerHasse.ofLevel_zero (K := K) (K' := K') (p := p) (U := U) L

end NK.BrauerHasse

namespace NK.NUV2.LC

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **`H²(U, Z/p)` is a module over `ZMod p`** (the "`F_p`-vector space structure" used by the rank
counts of Neukirch's argument): it is an additive commutative group killed by `p`
(`NK.BrauerHasse.H2Profinite.nsmul_p_eq_zero`). -/
noncomputable instance instModuleZModH2Profinite (p : ℕ) (U : Subgroup Gal(K'/K)) :
    Module (ZMod p) (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) :=
  AddCommGroup.zmodModule (fun x => NK.BrauerHasse.H2Profinite.nsmul_p_eq_zero p U x)

end NK.NUV2.LC
