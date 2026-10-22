/-
AREA RESOL — from the telescope retraction to B5.

Assembling `RESOL/B5Tower.lean` (the retraction `ψ K ≫ φ K = 𝟙 K`) with the closure properties
`CofibrantClosure` and the induction on the truncation degree, this file proves:

* `solidCofibrant_of_isZero` : a zero complex is solid-cofibrant;
* `isZero_trunc_of_boundedAbove` : the high truncations of a bounded-above complex vanish, so
  they are solid-cofibrant;
* `solidCofibrant_trunc_all` : *every* truncation `trunc j K` of a bounded-above complex of
  atoms is solid-cofibrant (downward induction from the vanishing ones);
* `solidCofibrant_T` : the telescope `T K` of the tower of truncations is solid-cofibrant;
* `solidCofibrant_of_boundedAbove_atomic_aux`: a bounded-above complex of atoms is
  solid-cofibrant, by the retraction `K ⟶ T K ⟶ K`.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.Retract
import Submission.Work.RESOL.B5Tower
import Submission.Work.RESOL.solidCofibrant_telescope

open CategoryTheory Limits LightCondensed
open HomologicalComplex

noncomputable section

namespace Work.RESOL

/-! ## Zero complexes -/

/-- A complex which is a zero object is solid-cofibrant (both sides of the bijectivity
statement are singletons). -/
theorem solidCofibrant_of_isZero (K : Cpx) (h : IsZero K) : Submission.Blueprint.SolidCofibrant K := by
  intro N
  have h1 : IsZero (Submission.Blueprint.hq K) :=
    Functor.map_isZero hqF h
  have h2 : IsZero (DerivedCategory.Qh.obj (Submission.Blueprint.hq K)) :=
    Functor.map_isZero DerivedCategory.Qh h1
  refine ⟨fun f g _ => h1.eq_of_src f g, fun y => ⟨0, h2.eq_of_src _ _⟩⟩

/-- A complex all of whose terms are zero objects is a zero object. -/
lemma isZero_of_isZero_X (L : Cpx) (h : ∀ n : ℤ, IsZero (L.X n)) : IsZero L := by
  rw [IsZero.iff_id_eq_zero]
  apply Hom.ext
  funext n
  rw [HomologicalComplex.id_f, HomologicalComplex.zero_f]
  exact (h n).eq_of_src _ _

/-- The high truncations of a bounded-above complex are zero (hence solid-cofibrant). -/
lemma isZero_trunc_of_isZero_high (K : Cpx) {N j : ℤ} (hN : ∀ n : ℤ, N < n → IsZero (K.X n))
    (hj : N < j) : IsZero (trunc j K) := by
  refine isZero_of_isZero_X _ fun n => ?_
  by_cases h : j ≤ n
  · rw [trunc_X_of_le K j h]
    exact hN n (by omega)
  · exact isZero_trunc_X K j h

/-! ## All truncations of a bounded-above complex of atoms are solid-cofibrant -/

/-- **Every truncation `trunc j K` of a bounded-above complex of atoms is solid-cofibrant.**

Above the bound of `K` the truncation is a zero complex; below it, we descend degree by degree
using `solidCofibrant_trunc`. -/
theorem solidCofibrant_trunc_all (hA : Submission.Blueprint.AtomProp)
    (hC : Work.RESOL.CofibrantClosure) (K : Work.RESOL.Cpx)
    (hbd : Work.RESOL.IsBoundedAbove K) (hat : Work.RESOL.HasAtomicTerms K) :
    ∀ j : ℤ, Submission.Blueprint.SolidCofibrant (Work.RESOL.trunc j K) := by
  obtain ⟨N, hN⟩ := hbd
  have hbase : Submission.Blueprint.SolidCofibrant (trunc (N + 1) K) :=
    solidCofibrant_of_isZero _ (isZero_trunc_of_isZero_high K hN (by omega))
  -- downward induction: the statement for `-n` for all `n ≥ -(N+1)`
  have hdesc : ∀ n : ℤ, -(N + 1) ≤ n → Submission.Blueprint.SolidCofibrant (trunc (-n) K) := by
    intro n hn
    refine Int.leInduction (motive := fun n _ =>
      Submission.Blueprint.SolidCofibrant (trunc (-n) K)) ?baseb ?stepb n hn
    · simpa using hbase
    · intro m hm ih
      have hh := solidCofibrant_trunc hA hC K hat (-m) ih
      rw [show -m - 1 = -(m + 1) from by omega] at hh
      exact hh
  intro j
  by_cases hj : j ≤ N + 1
  · have := hdesc (-j) (by omega)
    rwa [neg_neg] at this
  · exact solidCofibrant_of_isZero _ (isZero_trunc_of_isZero_high K hN (by omega))

/-! ## The telescope is solid-cofibrant -/

/-- The telescope `T K` of the tower of truncations is solid-cofibrant as soon as all the
truncations are. -/
theorem solidCofibrant_T (hC : Work.RESOL.CofibrantClosure) (K : Work.RESOL.Cpx)
    [HasCoproduct (U K)] (hT : ∀ j : ℤ, Submission.Blueprint.SolidCofibrant (trunc j K)) :
    Submission.Blueprint.SolidCofibrant (T K) :=
  solidCofibrant_telescope hC (U K) (Uinc K)
    (fun m n => by
      have h := hC.shift n (Submission.Blueprint.hq (U K m)) (hT (L m))
      rwa [HomotopyCategory.shift_quotient_obj (U K m) n] at h)

/-! ## B5 -/

/-- **A bounded-above complex of atoms is solid-cofibrant** (B5 of `REFS/02`). -/
theorem solidCofibrant_of_boundedAbove_atomic_aux (hA : Submission.Blueprint.AtomProp)
    (hC : Work.RESOL.CofibrantClosure) (K : Work.RESOL.Cpx)
    (hbd : Work.RESOL.IsBoundedAbove K) (hat : Work.RESOL.HasAtomicTerms K) :
    Submission.Blueprint.SolidCofibrant K := by
  haveI : HasCoproduct (U K) := inferInstance
  exact solidCofibrant_of_retract (ψ K) (φ K) (ψ_comp_φ K)
    (solidCofibrant_T hC K (solidCofibrant_trunc_all hA hC K hbd hat))

end Work.RESOL
