import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.AdjoinRoot

/-!
# Cardinality of the quotient `F[X] ⧸ span {g}` for a monic polynomial over a finite field

For a monic polynomial `g` of degree `n` over a finite field `F`, the quotient ring
`F[X] ⧸ Ideal.span {g}` is an `F`-vector space of dimension `n`, hence has
`Fintype.card F ^ n` elements.
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace Commons.FieldTheory.Polynomial

theorem natCard_quotient_span_monic {F : Type*} [Field F] [Fintype F] (g : F[X])
    (hg : g.Monic) :
    Nat.card (F[X] ⧸ Ideal.span ({g} : Set (F[X]))) = Fintype.card F ^ g.natDegree := by
  -- A monic polynomial gives a finitely generated quotient module.
  haveI : Module.Finite F (F[X] ⧸ Ideal.span ({g} : Set (F[X]))) := hg.finite_quotient
  calc
    Nat.card (F[X] ⧸ Ideal.span ({g} : Set (F[X]))) =
        Nat.card F ^ Module.finrank F (F[X] ⧸ Ideal.span ({g} : Set (F[X]))) :=
      Module.natCard_eq_pow_finrank (K := F) (V := F[X] ⧸ Ideal.span ({g} : Set (F[X])))
    _ = Fintype.card F ^ g.natDegree := by
      rw [finrank_quotient_span_eq_natDegree (K := F) (f := g), Nat.card_eq_fintype_card]

end Commons.FieldTheory.Polynomial