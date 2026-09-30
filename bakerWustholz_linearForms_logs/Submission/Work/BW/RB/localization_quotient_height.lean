import Mathlib
import Submission.Work.BW.RB.height_map_quotient_mk_eq_krullDim_Icc
import Submission.Work.BW.RB.krullDim_Icc_localization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

/-- For a localization `R → S` at a submonoid `M` and primes `P ≤ Q` of `S`, the height of the
image of `Q` in `S ⧸ P` equals the height of the image of `Q.under R` in `R ⧸ (P.under R)`.
Both sides are the "relative height" of `Q` over `P`, computed as the Krull dimension of the
interval of primes between `P` and `Q`; localization gives an order isomorphism between the
interval of primes between `P` and `Q` in `S` and that between `P.under R` and `Q.under R` in `R`.

This is the requested statement (with a localization at the maximal ideal `𝔪`). -/
theorem localization_quotient_height {A : Type*} [CommRing A] (𝔪 : Ideal A) [𝔪.IsMaximal]
    {P Q : Ideal (Localization.AtPrime 𝔪)} [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    (Q.map (Ideal.Quotient.mk P)).height
      = ((Q.under A).map (Ideal.Quotient.mk (P.under A))).height := by
  have h1 : ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)
      = Order.krullDim {J : Ideal (Localization.AtPrime 𝔪) // J.IsPrime ∧ P ≤ J ∧ J ≤ Q} :=
    height_map_quotient_mk_eq_krullDim_Icc P Q h
  have h2 : (((Q.under A).map (Ideal.Quotient.mk (P.under A))).height : WithBot ℕ∞)
      = Order.krullDim {J : Ideal A // J.IsPrime ∧ P.under A ≤ J ∧ J ≤ Q.under A} :=
    height_map_quotient_mk_eq_krullDim_Icc (P.under A) (Q.under A) (Ideal.comap_mono h)
  have h3 : Order.krullDim {J : Ideal (Localization.AtPrime 𝔪) // J.IsPrime ∧ P ≤ J ∧ J ≤ Q}
      = Order.krullDim {J : Ideal A // J.IsPrime ∧ P.under A ≤ J ∧ J ≤ Q.under A} :=
    krullDim_Icc_localization 𝔪.primeCompl (P := P) (Q := Q) h
  apply WithBot.coe_inj.mp
  rw [h1, h2, h3]

end Work.BW.RB
