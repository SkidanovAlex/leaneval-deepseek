/-
  WilC5 — the `Language.ring`, `rexpL` and `constantsOn ℝ`-reducts of an `LRc`-structure.

  `LRc = (ring.sum rexpL)[[ℝ]]`, so an `LRc`-structure restricts to the language of rings (along
  `Sum.inl (Sum.inl ·)`), to `rexpL` (along `Sum.inl (Sum.inr ·)`) and to the constants (along
  `Sum.inr ·`).  These instances are what let Mathlib's `Theory.field` / `fieldOfModelField` /
  `CompatibleRing` machinery, and this directory's `OMinModels`/`cut_determines_type_of_omin`
  (whose hypotheses are stated with the ring, `rexpL` and constant structures separately), be used
  at a structure that is only given as an `LRc`-structure — in particular at the `κ`-saturated
  elementary extensions produced by `Work.WilC5.ExistsSaturated`, which are the amalgamation tool
  for the two-model cut/type comparison used by vdDMM Lemmas 4.2–4.3.
-/
import Submission.Work.WilC5.LRcOps
import Mathlib.ModelTheory.Algebra.Field.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The `Language.ring`-reduct of an `LRc`-structure**, as a global instance. -/
instance lrcRingReduct (M : Type) [LRc.Structure M] : Language.ring.Structure M where
  funMap := fun {n} f xs => @Structure.funMap LRc M _ n (Sum.inl (Sum.inl f)) xs
  RelMap := fun {n} r _ => isEmptyElim r

/-- **The `rexpL`-reduct of an `LRc`-structure**, as a global instance. -/
instance lrcRexpReduct (M : Type) [LRc.Structure M] : rexpL.Structure M where
  funMap := fun {n} f xs =>
    match n, f with
    | 1, rexpFunc.rexp => @Structure.funMap LRc M _ 1 (Sum.inl (Sum.inr rexpFunc.rexp)) xs
  RelMap := fun {n} r _ => nomatch r

/-- **The `constantsOn ℝ`-reduct of an `LRc`-structure**, as a global instance. -/
instance lrcConstReduct (M : Type) [LRc.Structure M] : (constantsOn ℝ).Structure M where
  funMap := fun {n} f xs => @Structure.funMap LRc M _ n (Sum.inr f) xs
  RelMap := fun {n} r _ => nomatch r

@[simp] theorem lrcRingReduct_funMap (M : Type) [LRc.Structure M] {n : ℕ}
    (f : Language.ring.Functions n) (xs : Fin n → M) :
    @Structure.funMap Language.ring M (lrcRingReduct M) n f xs =
      @Structure.funMap LRc M _ n (Sum.inl (Sum.inl f)) xs :=
  rfl

@[simp] theorem lrcRexpReduct_funMap (M : Type) [LRc.Structure M] (xs : Fin 1 → M) :
    @Structure.funMap rexpL M (lrcRexpReduct M) 1 rexpFunc.rexp xs =
      @Structure.funMap LRc M _ 1 (Sum.inl (Sum.inr rexpFunc.rexp)) xs :=
  rfl

@[simp] theorem lrcConstReduct_funMap (M : Type) [LRc.Structure M] {n : ℕ}
    (f : (constantsOn ℝ).Functions n) (xs : Fin n → M) :
    @Structure.funMap (constantsOn ℝ) M (lrcConstReduct M) n f xs =
      @Structure.funMap LRc M _ n (Sum.inr f) xs :=
  rfl

end Work.WilC5
