import Mathlib
import Submission.NK.LocalStructure.Defs

namespace NK.LocalStructure.Tame

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

theorem tameStructureInput_of_core {p : ℕ} {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (h : NK.LocalStructure.TameCore p K 𝔭 K')
    (hpow : ∃ f : ℕ, 0 < f ∧ NK.LocalStructure.residueCard K 𝔭 = p ^ f)
    (hfrob : ∃ x : Gal(K'/𝔭.adicCompletion K),
      x ∉ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p) :
    NK.LocalTame.TameStructureInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  ⟨h.hp, hpow, h.isTameInertia.1, h.isTameInertia, h.isProPrimeToP_tameInertia,
    h.tameInertia_commutator_mem, h.unramifiedQuotient, hfrob⟩

end NK.LocalStructure.Tame
