import Submission.NK.LocalReciprocity.Prelude
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.LocalReciprocity.LocalSetup

/-!
# Norm functoriality in a tower of local fields

For a tower `K ⊆ L ⊆ M` of number fields and places `w | w|_L | p`, the completed local fields
`K_p ⊆ L_{w|_L} ⊆ M_w` form a tower, and the norm groups satisfy

  `N_{M_w/K_p}(M_wˣ) = N_{L_{w|_L}/K_p}(N_{M_w/L_{w|_L}}(M_wˣ))`,

the first axiom of a class formation (in the form in which it is used for the local side of
Neukirch–Uchida).  This is the concrete local-field instance of the abstract
`NK.LocalReciprocity.normGroup_trans`.

The second axiom, `N_{L₁L₂} = N_{L₁} ∩ N_{L₂}`, is *not* a purely formal consequence of the
definition of the norm: it needs the canonical reciprocity isomorphism as an input, and is proved
in `Submission/Work/LocalReciprocity/normGroup_sup_eq_inf.lean` from a
`NK.LocalReciprocity.LocalReciprocityDatum`.
-/

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalReciprocity

universe u

noncomputable section

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- **Transitivity of the local norm groups** in the tower `K_p ⊆ L_{w|_L} ⊆ M_w`. -/
theorem normGroup_adicCompletion_tower (L : IntermediateField K M) [Normal K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    [hw : w.asIdeal.LiesOver p.asIdeal]
    [hwL : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).asIdeal.LiesOver
      p.asIdeal]
    [hwLM : w.asIdeal.LiesOver
      (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).asIdeal]
    [IsScalarTower (p.adicCompletion K)
      ((Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
      (w.adicCompletion M)] :
    normGroup (p.adicCompletion K) (w.adicCompletion M) =
      (normGroup
        ((Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
        (w.adicCompletion M)).map
        (Units.map (Algebra.norm (p.adicCompletion K) :
          ((Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L) →*
            (p.adicCompletion K))) :=
  normGroup_trans

end

end NK.LocalReciprocity
