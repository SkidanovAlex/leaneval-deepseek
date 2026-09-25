import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

/-- The `p`-adic completion of a number field has characteristic zero.  (Proof: the canonical
embedding `K → K_p` is injective, and injective additive monoid homomorphisms transport
`CharZero`; see `CharZero.of_addMonoidHom`.) -/
theorem charZero_adicCompletion {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharZero (p.adicCompletion K) := by
  exact CharZero.of_addMonoidHom
    (_root_.NumberField.FinitePlace.embedding p).toAddMonoidHom
    (by simp) (RingHom.injective _)

end Commons.NumberTheory.NumberField