/-
# Galois-invariance of the valuation subring extending a Henselian valuation

This file collects the two facts of valuation theory that the Lubin–Tate evaluation layer needs.

* `NK.LocalReciprocityLubinTate.Eval.henselianLocalRing_integer` : the ring of integers `𝒪[F]` of
  a nonarchimedean local field is Henselian.  (Mathlib has `IsAdicComplete 𝓂[F] 𝒪[F]`
  (`Mathlib/NumberTheory/LocalField/Basic.lean`) and `IsAdicComplete.henselianRing`
  (`Mathlib/RingTheory/Henselian.lean`); this file only assembles the two.)

* `NK.LocalReciprocityLubinTate.Eval.algEquiv_comap_valuationSubring_eq` : if `V` is a Henselian
  valuation subring of `K` and `W` a valuation subring of an algebraic extension `L` restricting
  to `V`, then every `K`-automorphism of `L` preserves `W`.  This is the uniqueness of the
  extension of a Henselian valuation (`Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic`).

* `NK.LocalReciprocityLubinTate.Eval.algEquiv_valuation_eq` : consequently the valuation attached
  to `W` is invariant under `Gal(L/K)` — the arithmetic input behind Milne's Lemma I.3.5
  (`val_eq_of_algEquiv_of_comap_eq`).

## Main results

* `NK.LocalReciprocityLubinTate.Eval.henselianLocalRing_integer`
* `NK.LocalReciprocityLubinTate.Eval.algEquiv_comap_valuationSubring_eq`
* `NK.LocalReciprocityLubinTate.Eval.algEquiv_valuation_eq`
-/
import Mathlib
import Submission.Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic
import Submission.Commons.RingTheory.Valuation.val_eq_of_algEquiv_of_comap_eq

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Eval

universe u

/-- **The ring of integers of a nonarchimedean local field is Henselian.**

Mathlib supplies `IsAdicComplete 𝓂[F] 𝒪[F]` for `F` a nonarchimedean local field (with a compatible
uniform structure, which we install from the topological additive group structure), and an
`I`-adically complete ring is Henselian at `I`. -/
theorem henselianLocalRing_integer (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : HenselianLocalRing ↥(ValuativeRel.valuation F).integer := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer)
      ↥(ValuativeRel.valuation F).integer := inferInstance
  letI : HenselianRing ↥(ValuativeRel.valuation F).integer
      (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) :=
    IsAdicComplete.henselianRing _ _
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have h₂' : IsUnit ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer))
      (f.derivative.eval a₀)) := by
    simpa using (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer)).isUnit_map h₂
  exact (HenselianRing.is_henselian (R := ↥(ValuativeRel.valuation F).integer)
    (I := IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) f hf a₀ h₁ h₂')

/-- **Every `K`-automorphism of an algebraic extension preserves the valuation subring extending a
Henselian valuation.**  Both `W` and `W.comap σ` restrict to `V` on `K`, and a Henselian valuation
has at most one extension to an algebraic extension. -/
theorem algEquiv_comap_valuationSubring_eq {K L : Type u} [Field K] [Field L] [Algebra K L]
    (hKL : Algebra.IsAlgebraic K L) (V : ValuationSubring K) [HenselianLocalRing V]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) (σ : L ≃ₐ[K] L) :
    W.comap (σ : L →+* L) = W := by
  refine Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic V
    (W.comap (σ : L →+* L)) W ?_ hW
  rw [ValuationSubring.comap_comap]
  have hcomp : (σ : L →+* L).comp (algebraMap K L) = algebraMap K L := by
    ext x; exact σ.commutes x
  rw [hcomp]
  exact hW

/-- **The valuation of a Galois-stable valuation subring is Galois-invariant.** -/
theorem algEquiv_valuation_eq {K L : Type u} [Field K] [Field L] [Algebra K L]
    (hKL : Algebra.IsAlgebraic K L) (V : ValuationSubring K) [HenselianLocalRing V]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) (σ : L ≃ₐ[K] L) (x : L) :
    W.valuation (σ x) = W.valuation x :=
  Commons.RingTheory.Valuation.val_eq_of_algEquiv_of_comap_eq hKL W σ
    (algEquiv_comap_valuationSubring_eq hKL V W hW σ) x

end NK.LocalReciprocityLubinTate.Eval
