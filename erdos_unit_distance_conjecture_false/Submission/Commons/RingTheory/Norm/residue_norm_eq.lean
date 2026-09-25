import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Norm.Basic
import Submission.Commons.RingTheory.Norm.norm_quotient_mk

namespace Commons.RingTheory.Norm

open IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] [Module.Free R S] [Module.Finite R S]

/-- **The residue of a norm is the norm of the residue** in the case where the maximal ideal of
`R` generates the maximal ideal of `S` (the unramified case `𝔪_R S = 𝔪_S`): for `u : S`,
`Algebra.norm` of the residue class of `u` over the residue field of `R` is the residue class of
`Algebra.norm R u`.

(Auxiliary input, whose proof the prover may use freely: Mathlib's `Algebra.trace_quotient_mk`
and its norm analogue
`Algebra.norm (R ⧸ 𝔪_R) (Ideal.Quotient.mk (𝔪_R S) x) = Ideal.Quotient.mk 𝔪_R (Algebra.norm R x)`,
which follows by the same proof with `RingHom.map_det` in place of `AddMonoidHom.map_trace`.) -/
theorem residue_norm_eq (h : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
    IsLocalRing.maximalIdeal S) (u : S) :
    Algebra.norm (IsLocalRing.ResidueField R) (IsLocalRing.residue S u) =
      IsLocalRing.residue R (Algebra.norm R u) := by
  have he : RingHom.comp (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
        ((RingEquiv.refl (R ⧸ IsLocalRing.maximalIdeal R)) :
          (R ⧸ IsLocalRing.maximalIdeal R) →+* (R ⧸ IsLocalRing.maximalIdeal R)) =
      RingHom.comp (Ideal.quotEquivOfEq h : (S ⧸ Ideal.map (algebraMap R S)
            (IsLocalRing.maximalIdeal R)) →+* (S ⧸ IsLocalRing.maximalIdeal S))
        (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
          (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))) := by
    apply Ideal.Quotient.ringHom_ext
    ext y
    change algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.residue R y)
      = Ideal.quotEquivOfEq h (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
          (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) y))
    rw [IsLocalRing.ResidueField.algebraMap_residue,
      Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.quotEquivOfEq_mk]
    rfl
  have key := Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl (R ⧸ IsLocalRing.maximalIdeal R)) (Ideal.quotEquivOfEq h) he
    (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) u)
  rw [Commons.RingTheory.Norm.norm_quotient_mk] at key
  exact key.symm

end Commons.RingTheory.Norm