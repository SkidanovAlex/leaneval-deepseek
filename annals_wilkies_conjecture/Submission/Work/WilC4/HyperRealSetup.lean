/-
  WilC4/HyperRealSetup : the nonstandard model of `TR` used by `unifFinite_of_omin`.

  The carrier is the space of germs `HR = Germ (hyperfilter ℕ) ℝ` of real sequences modulo
  agreement on a set of the nonprincipal ultrafilter `hyperfilter ℕ` — the hyperreal numbers.
  `Mathlib/Order/Filter/FilterProduct.lean` supplies the ordered-field instances
  (`Filter.Germ.instField`, `instLinearOrder`, `instIsStrictOrderedRing`), so the only
  additional data is the `LRc`-structure: it is the quotient structure of the *pointwise*
  `LRc`-structure on `ℕ → ℝ` (so that Łoś's theorem can be proved by induction on formulas).

  This file contains the construction and the term-level Łoś lemma; the formula-level transfer,
  the compatibility `Ring.CompatibleRing HR`, the square-root property and `HR ⊨ TR` are in the
  sibling modules `realize_bd_hyper`, `compatRing_hyper`, `hsq_hyper`, `TR_hyper`.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open FirstOrder.Ring

namespace Work.WilC4

/-- The hyperreals: real sequences modulo agreement on the hyperfilter. -/
abbrev HR : Type := Filter.Germ (Filter.hyperfilter ℕ : Filter ℕ) ℝ

/-- The setoid defining `HR`. -/
abbrev gset : Setoid ((_ : ℕ) → ℝ) :=
  Filter.germSetoid (Filter.hyperfilter ℕ : Filter ℕ) ℝ

/-- The *pointwise* `LRc`-structure on `ℕ → ℝ` (`LRc` has no relation symbols, so the `RelMap`
field is arbitrary; it is set to `False`). -/
noncomputable def pwStruc : LRc.Structure (ℕ → ℝ) where
  funMap {n} f := fun x => fun a => @Structure.funMap LRc ℝ inferInstance n f (fun i => x i a)
  RelMap {_n} _ _ := False

noncomputable instance psGset : LRc.Prestructure gset where
  toStructure := pwStruc
  fun_equiv := by
    intro n f x y hxy
    have h : ∀ᶠ a in (Filter.hyperfilter ℕ : Filter ℕ), ∀ i : Fin n, x i a = y i a := by
      rw [Filter.eventually_all]
      intro i
      exact hxy i
    filter_upwards [h] with a ha
    exact congrArg (fun z => @Structure.funMap LRc ℝ inferInstance n f z) (funext ha)
  rel_equiv := by
    intro n r x y _
    rfl

/-- The `LRc`-structure of the model, as the quotient of the pointwise structure. -/
noncomputable instance instLRcHR : LRc.Structure HR :=
  Language.quotientStructure (L := LRc) (s := gset)

/-- **Term-level Łoś**: the value of a term at germs is the germ of the pointwise values. -/
theorem term_realize_hyper {β : Type*} (t : LRc.Term β) (x : β → ℕ → ℝ) :
    @Term.realize LRc HR instLRcHR β (fun i => (↑(x i) : HR)) t =
      (↑(@Term.realize LRc (ℕ → ℝ) pwStruc β x t) : HR) :=
  Language.Term.realize_quotient_mk' (L := LRc) (s := gset) (ps := psGset) t x

/-- The `ring`-structure of the model, read off from the `LRc`-structure. -/
noncomputable instance instRingHR : Language.ring.Structure HR where
  funMap {n} f := fun x => @Structure.funMap LRc HR instLRcHR n (Sum.inl (Sum.inl f)) x
  RelMap {_n} _ _ := False

/-- The `rexpL`-structure of the model. -/
noncomputable instance instRexpLHR : rexpL.Structure HR where
  funMap {n} f := fun x => @Structure.funMap LRc HR instLRcHR n (Sum.inl (Sum.inr f)) x
  RelMap {_n} _ _ := False

/-- The `constantsOn ℝ`-structure of the model. -/
noncomputable instance instConstHR : (constantsOn ℝ).Structure HR where
  funMap {n} f := fun x => @Structure.funMap LRc HR instLRcHR n (Sum.inr f) x
  RelMap {_n} _ _ := False

/-- The `LRc`-structure is the join of the ring, `rexp` and constant structures. -/
theorem funMap_LRc_hyper {n : ℕ} (f : LRc.Functions n) (x : Fin n → HR) :
    @Structure.funMap LRc HR instLRcHR n f x =
      @Structure.funMap LRc HR inferInstance n f x := rfl

/-- The language `funMap` at representatives. -/
theorem funMap_rep_hyper (n : ℕ) (f : LRc.Functions n) (x : Fin n → ℕ → ℝ) :
    @Structure.funMap LRc HR instLRcHR n f (fun i => (↑(x i) : HR)) =
      (↑(@Structure.funMap LRc (ℕ → ℝ) pwStruc n f x) : HR) :=
  Language.funMap_quotient_mk' (L := LRc) (s := gset) (ps := psGset) f x

theorem exists_rep_tuple {n : ℕ} (x : Fin n → HR) :
    ∃ y : Fin n → ℕ → ℝ, x = fun i => (↑(y i) : HR) :=
  ⟨fun i => Quotient.out (x i), by
    funext i
    exact (Quotient.out_eq (x i)).symm⟩

end Work.WilC4
