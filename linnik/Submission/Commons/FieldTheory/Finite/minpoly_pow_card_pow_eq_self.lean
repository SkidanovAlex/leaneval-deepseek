import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Finite

open IntermediateField

/-- If `E` is a finite `F`-algebra (with `F` a finite field) and `a : E`, then
`a ^ (|F| ^ deg (minpoly F a)) = a`. This holds because `a` lies in the finite
field `F⟮a⟯`, which is an `F`-vector space of dimension `deg (minpoly F a)`,
hence has `|F| ^ deg (minpoly F a)` elements. -/
theorem minpoly_pow_card_pow_eq_self {F E : Type*} [Field F] [Field E] [Fintype F]
    [Fintype E] [Algebra F E] (a : E) :
    a ^ (Fintype.card F ^ (minpoly F a).natDegree) = a := by
  set_option linter.style.haveILetI false in
  letI : Fintype ↥(F⟮a⟯ : IntermediateField F E) :=
    Fintype.ofFinite ↥(F⟮a⟯ : IntermediateField F E)
  have hcard : Fintype.card ↥(F⟮a⟯ : IntermediateField F E) =
      Fintype.card F ^ (minpoly F a).natDegree := by
    calc Fintype.card ↥(F⟮a⟯ : IntermediateField F E)
        = Fintype.card F ^ Module.finrank F ↥(F⟮a⟯ : IntermediateField F E) :=
          Module.card_eq_pow_finrank
      _ = Fintype.card F ^ (minpoly F a).natDegree := by
          rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite F a)]
  have hpow : (AdjoinSimple.gen F a) ^ (Fintype.card F ^ (minpoly F a).natDegree) =
      AdjoinSimple.gen F a := by
    rw [← hcard]
    exact FiniteField.pow_card _
  have h3 := congrArg (fun x : ↥(F⟮a⟯ : IntermediateField F E) => (x : E)) hpow
  simpa [AdjoinSimple.coe_gen] using h3

end Commons.FieldTheory.Finite