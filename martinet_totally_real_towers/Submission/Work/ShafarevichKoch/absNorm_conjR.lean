import Mathlib
import Submission.Work.ShafarevichKoch.GenusConj

noncomputable section

namespace Work.ShafarevichKoch

open scoped Classical

/-- A ring equivalence `e` of a Dedekind domain `S` preserves the absolute norm of ideals.

`Ideal.absNorm I` is the cardinality of the quotient `S ⧸ I`, and `e` induces a ring equivalence
`S ⧸ I ≃+* S ⧸ e(I)` (`Ideal.quotientEquiv`), hence a bijection of the quotients. -/
theorem absNorm_map_ringEquiv {S : Type*} [CommRing S] [IsDedekindDomain S] [Infinite S]
    (e : S ≃+* S) (I : Ideal S) :
    Ideal.absNorm (Ideal.map (e : S →+* S) I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (Ideal.map (e : S →+* S) I) e rfl).toEquiv.symm

/-- The conjugation `conjR` of `𝓞 Kc = ℤ[√-30030]` (the restriction of the nontrivial
`ℚ`-automorphism of `Kc = ℚ(√-30030)`, sending `√-30030` to `-√-30030`) preserves the index of
ideals: `conjR` is a ring equivalence, so it induces a bijection `𝓞 Kc ⧸ I ≃ 𝓞 Kc ⧸ conjR I` and
`Ideal.absNorm` (a `Nat.card` of the quotient) is preserved. -/
theorem absNorm_conjR (I : Ideal (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)) :
    Ideal.absNorm (Ideal.map (Work.ShafarevichKoch.conjR : NumberField.RingOfIntegers Work.ClassFieldTower.Kc →+* NumberField.RingOfIntegers Work.ClassFieldTower.Kc) I) = Ideal.absNorm I :=
  absNorm_map_ringEquiv (Work.ShafarevichKoch.conjR) I

end Work.ShafarevichKoch
