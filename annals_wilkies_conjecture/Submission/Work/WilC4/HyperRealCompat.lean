/-
  WilC4/HyperRealCompat : the frozen typeclass instances of the hyperreal model.

  `HR` already carries `Field`, `LinearOrder` and `IsStrictOrderedRing` (Mathlib's germ
  instances).  The missing piece for `WilkiesDesign.CG.OMinModels` is
  `Ring.CompatibleRing HR`, i.e. the agreement of the ring operations of the field with the
  ring language structure `instRingHR` (which was read off from the `LRc`-structure).  Each of
  the five equations is proved on representatives: reduce the tuple to germs `↑(y i)`, move the
  language `funMap` inside the germ (`funMap_rep_hyper`), evaluate pointwise (`pwStruc_apply`),
  use the corresponding compatibility on `ℝ`, and return to germs (`Filter.Germ.coe_add` etc.).
-/
import Mathlib
import Submission.Work.WilC4.HyperRealSetup

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open FirstOrder.Ring

namespace Work.WilC4


/-- The ring funMap on `ℝ` is the ring funMap inside `LRc` (definitional). -/
theorem funMap_ring_real (n : ℕ) (f : Language.ring.Functions n) (x : Fin n → ℝ) :
    @Structure.funMap LRc ℝ inferInstance n (Sum.inl (Sum.inl f)) x =
      @Structure.funMap Language.ring ℝ inferInstance n f x := rfl

/-- Pointwise evaluation of the prestructure funMap. -/
theorem pwStruc_apply (n : ℕ) (f : LRc.Functions n) (x : Fin n → ℕ → ℝ) (a : ℕ) :
    @Structure.funMap LRc (ℕ → ℝ) pwStruc n f x a =
      @Structure.funMap LRc ℝ inferInstance n f (fun i => x i a) := rfl

theorem addHR (x : Fin 2 → HR) :
    @Structure.funMap Language.ring HR instRingHR 2 Ring.addFunc x = x 0 + x 1 := by
  obtain ⟨y, rfl⟩ := exists_rep_tuple x
  refine (funMap_rep_hyper 2 (Sum.inl (Sum.inl Ring.addFunc)) y).trans ?_
  have hfun : @Structure.funMap LRc (ℕ → ℝ) pwStruc 2 (Sum.inl (Sum.inl Ring.addFunc)) y =
      fun a => y 0 a + y 1 a := by
    funext a
    exact (pwStruc_apply 2 (Sum.inl (Sum.inl Ring.addFunc)) y a).trans
      ((funMap_ring_real 2 Ring.addFunc (fun i => y i a)).trans
        (Ring.CompatibleRing.funMap_add (fun i => y i a)))
  exact hfun ▸ (Filter.Germ.coe_add (y 0) (y 1)).symm

theorem mulHR (x : Fin 2 → HR) :
    @Structure.funMap Language.ring HR instRingHR 2 Ring.mulFunc x = x 0 * x 1 := by
  obtain ⟨y, rfl⟩ := exists_rep_tuple x
  refine (funMap_rep_hyper 2 (Sum.inl (Sum.inl Ring.mulFunc)) y).trans ?_
  have hfun : @Structure.funMap LRc (ℕ → ℝ) pwStruc 2 (Sum.inl (Sum.inl Ring.mulFunc)) y =
      fun a => y 0 a * y 1 a := by
    funext a
    exact (pwStruc_apply 2 (Sum.inl (Sum.inl Ring.mulFunc)) y a).trans
      ((funMap_ring_real 2 Ring.mulFunc (fun i => y i a)).trans
        (Ring.CompatibleRing.funMap_mul (fun i => y i a)))
  exact hfun ▸ (Filter.Germ.coe_mul (y 0) (y 1)).symm

theorem negHR (x : Fin 1 → HR) :
    @Structure.funMap Language.ring HR instRingHR 1 Ring.negFunc x = -x 0 := by
  obtain ⟨y, rfl⟩ := exists_rep_tuple x
  refine (funMap_rep_hyper 1 (Sum.inl (Sum.inl Ring.negFunc)) y).trans ?_
  have hfun : @Structure.funMap LRc (ℕ → ℝ) pwStruc 1 (Sum.inl (Sum.inl Ring.negFunc)) y =
      fun a => -y 0 a := by
    funext a
    exact (pwStruc_apply 1 (Sum.inl (Sum.inl Ring.negFunc)) y a).trans
      ((funMap_ring_real 1 Ring.negFunc (fun i => y i a)).trans
        (Ring.CompatibleRing.funMap_neg (fun i => y i a)))
  exact hfun ▸ (Filter.Germ.coe_neg (y 0)).symm

theorem zeroHR (x : Fin 0 → HR) :
    @Structure.funMap Language.ring HR instRingHR 0 Ring.zeroFunc x = 0 := by
  obtain ⟨y, rfl⟩ := exists_rep_tuple x
  refine (funMap_rep_hyper 0 (Sum.inl (Sum.inl Ring.zeroFunc)) y).trans ?_
  have hfun : @Structure.funMap LRc (ℕ → ℝ) pwStruc 0 (Sum.inl (Sum.inl Ring.zeroFunc)) y =
      (0 : ℕ → ℝ) := by
    funext a
    exact (pwStruc_apply 0 (Sum.inl (Sum.inl Ring.zeroFunc)) y a).trans
      (Ring.CompatibleRing.funMap_zero (fun i => y i a))
  exact hfun ▸ rfl

theorem oneHR (x : Fin 0 → HR) :
    @Structure.funMap Language.ring HR instRingHR 0 Ring.oneFunc x = 1 := by
  obtain ⟨y, rfl⟩ := exists_rep_tuple x
  refine (funMap_rep_hyper 0 (Sum.inl (Sum.inl Ring.oneFunc)) y).trans ?_
  have hfun : @Structure.funMap LRc (ℕ → ℝ) pwStruc 0 (Sum.inl (Sum.inl Ring.oneFunc)) y =
      (1 : ℕ → ℝ) := by
    funext a
    exact (pwStruc_apply 0 (Sum.inl (Sum.inl Ring.oneFunc)) y a).trans
      (Ring.CompatibleRing.funMap_one (fun i => y i a))
  exact hfun ▸ rfl

noncomputable def compatRing_hyper : Ring.CompatibleRing HR where
  __ := instRingHR
  funMap_add := addHR
  funMap_mul := mulHR
  funMap_neg := negHR
  funMap_zero := zeroHR
  funMap_one := oneHR


/-- The model's ring structure is compatible with its field operations. -/
noncomputable instance instCompatHR : Ring.CompatibleRing HR := compatRing_hyper


/-! ## The sum-shaped language structure

`WilkiesDesign.CG.OMinModels` (like every consumer of `Set.Definable`) builds the `LRc`-structure
of a model from the *typeclass arguments* `Ring.CompatibleRing M`, `rexpL.Structure M` and
`(constantsOn ℝ).Structure M`, i.e. as Mathlib's `withConstantsStructure` applied to the sum of
the ring, `rexp` and constant structures.  Our `instLRcHR` is instead the quotient structure of
the pointwise structure, and the two disagree *syntactically*.  `lrcSum` names the sum-shaped
structure and `lrcSum_eq` records the (definitional, symbol-by-symbol) agreement, so that
statements can be moved between the two shapes.
-/

/-- The `LRc`-structure of `HR` built the way the frozen statements build it. -/
noncomputable def lrcSum : LRc.Structure HR :=
  Language.withConstantsStructure (L := LR) (α := ℝ) (M := HR)

/-- The sum-shaped structure and the quotient structure agree; symbol by symbol this is
definitional, and `LRc` has no relation symbols. -/
theorem lrcSum_eq : lrcSum = instLRcHR := by
  ext n f x
  · rcases f with g | r
    · rcases g with h | g
      · rfl
      · rfl
    · rfl
  · rcases f with g | r
    · rcases g with h | g
      · exact isEmptyElim h
      · exact isEmptyElim g
    · exact isEmptyElim r

end Work.WilC4
