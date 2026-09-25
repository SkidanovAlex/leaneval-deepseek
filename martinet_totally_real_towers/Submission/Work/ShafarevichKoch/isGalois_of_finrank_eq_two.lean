import Mathlib
import Submission.Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two

/-!
# `Work.ShafarevichKoch.isGalois_of_finrank_eq_two`

**In characteristic zero every intermediate field of degree `2` is Galois over the base.**

This is the instance that makes "unramified quadratic level" a well-behaved notion: a
`Kc`-subextension of `F_∅` of degree `2` is automatically Galois over `Kc`, so it carries a
Galois group of order `2` and the restriction map `G_∅ → Gal(L/Kc)` is available (this is what
`Work.ShafarevichKoch.QuadraticLevel` and the character group `ProTwoChar` use).

It is a wrapper of the commons lemma `Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two`,
which needs `FiniteDimensional` and `(2 : F) ≠ 0`; here `FiniteDimensional` follows from
`Module.finrank F L = 2 ≠ 0`, and `(2 : F) ≠ 0` from `CharZero F`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.ShafarevichKoch

/-- **Every degree-`2` intermediate field is Galois** (characteristic zero). -/
theorem isGalois_of_finrank_eq_two (F E : Type*) [Field F] [CharZero F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (h2 : Module.finrank F L = 2) : IsGalois F ↥L := by
  haveI : FiniteDimensional F ↥L := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  exact Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two (F := F) (E := ↥L) h2
    (Nat.cast_ne_zero.mpr (by norm_num))

end Work.ShafarevichKoch
