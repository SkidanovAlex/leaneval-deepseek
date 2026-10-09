/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local invariants of a `p`-adic field

This is the conclusion (A) of the `NK.LocalAnabelian` chapter, in the form in which it
is actually true (see the discussion in `PadicField/Defs.lean`):

  the abelianised pro-`p` part of `Gal(κ̄/κ)` is `ℤ_p^d × (ℤ/p)^δ`, i.e. the number of
  **cyclic** degree-`p` extensions of `κ` is `(p^{[κ:ℚ_p]+1+δ} - 1)/(p-1)`, and hence
  `frattiniRank p (Gal(κ^{(p)}/κ)) = 1 + [κ:ℚ_p] + δ`.

`hasAbelianFrattiniRank_of_inputs` draws this from the bundled local inputs
(`PadicGaloisInputs`).  The `ζ_p ∈ κ` (`δ = 1`) case is then derived from the two
primitive arithmetic inputs — the power class count `|κˣ/(κˣ)^p| = p^{d+2}` and the
Kummer bridge `natCard_galois_finrank_eq_p` — by
`hasAbelianFrattiniRank_of_isPrimitiveRoot`; for `δ = 0` the corresponding statement is
the genuine additional input (Kummer theory over `κ(ζ_p)` plus Galois descent).

The non-abelian count (all degree-`p` extensions, not only the cyclic ones) is a
different number when `δ = 0`; the two coincide for `δ = 1` provided every degree-`p`
extension is Galois, which is the content of `hasFrattiniRank_of_isPrimitiveRoot`.
-/
import Submission.NK.LocalAnabelian.PadicField.Defs
import Submission.NK.LocalAnabelian.Kummer.Bridge
import Submission.NK.LocalAnabelian.GaloisCorrespondence.IndexP
import Submission.NK.LocalAnabelian.GaloisCorrespondence.numIndexSubgroups_abelianization_eq_natCard_galois
import Submission.NK.LocalAnabelian.Bridge.frattiniRank_eq_of_hasAbelianFrattiniRank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

noncomputable section

/-- **Part (A), from the bundled inputs.**  The abelianised pro-`p` part of the absolute
Galois group of a `p`-adic field `κ` with `[κ : ℚ_p] = d` and `δ = 1 ⟺ ζ_p ∈ κ` has
`p`-Frattini rank `d + 1 + δ`. -/
theorem hasAbelianFrattiniRank_of_inputs {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] {p d δ : ℕ} (h : PadicGaloisInputs p d δ κ K') :
    HasAbelianFrattiniRank p (d + 1 + δ) (Gal(K'/κ)) :=
  h.abelian_rank

/-- **Part (A), in the vocabulary of `NK.ProfiniteP`.**  The Frattini rank of
`Gal(κ̄/κ)` — the `𝔽_p`-dimension of its maximal elementary abelian `p`-quotient, which
agrees with that of the maximal pro-`p` quotient `Gal(κ^{(p)}/κ)` — is `1 + d + δ`:

  `frattiniRank p (Gal(κ̄/κ)) = 1 + [κ : ℚ_p] + δ`.

The hypothesis is that every normal index-`p` subgroup of `Gal(κ̄/κ)` is open, which holds
for the absolute Galois group of a `p`-adic field because it is topologically finitely
generated (Nikolov–Segal). -/
theorem frattiniRank_galois_of_inputs {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] {p d δ : ℕ} [Fact p.Prime] (_hp : p.Prime)
    (h : PadicGaloisInputs p d δ κ K')
    (hopen : ∀ H : Subgroup (Gal(K'/κ)), H.index = p → H.Normal →
      IsOpen (H : Set (Gal(K'/κ)))) :
    NK.ProfiniteP.frattiniRank p (Gal(K'/κ)) = d + 1 + δ :=
  Bridge.frattiniRank_eq_of_hasAbelianFrattiniRank hopen (hasAbelianFrattiniRank_of_inputs h)

/-- **Part (A), the Kummer case `ζ_p ∈ κ`.**  The only extra input here (besides the power
class count `|κˣ/(κˣ)^p| = p^{d+2}`) is that every *normal* index-`p` subgroup of
`Gal(K'/κ)` is closed, which holds for the absolute Galois group of a `p`-adic field
because it is topologically finitely generated and hence every finite-index subgroup is
open (Nikolov–Segal).  Then the Kummer bridge gives the abelian rank `d + 2`. -/
theorem hasAbelianFrattiniRank_of_isPrimitiveRoot {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] {p : ℕ} (hp : p.Prime) {ζ : κ}
    (hζ : IsPrimitiveRoot ζ p) [Finite (KummerGroup p κ)] {d : ℕ}
    (hpow : Nat.card (KummerGroup p κ) = p ^ (d + 2))
    (hclosed : ∀ H : Subgroup (Gal(K'/κ)), H.index = p → H.Normal →
      IsClosed (H : Set (Gal(K'/κ)))) :
    HasAbelianFrattiniRank p (d + 2) (Gal(K'/κ)) := by
  haveI : IsGalois κ K' := IsSepClosure.isGalois
  unfold HasAbelianFrattiniRank HasFrattiniRank
  rw [GaloisCorrespondence.numIndexSubgroups_abelianization_eq_natCard_galois
      (k := κ) (K' := K') p hp hclosed,
    natCard_galois_finrank_eq_p (k := κ) (K' := K') p hp hζ, hpow]

/-- **The Kummer count of degree-`p` Galois extensions of a `p`-adic field in the case
`ζ_p ∈ κ`**, from the power class count `|κˣ/(κˣ)^p| = p^{d+2}`. -/
theorem natCard_galois_finrank_eq_p_of_isPrimitiveRoot {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] {p : ℕ} (hp : p.Prime) {ζ : κ}
    (hζ : IsPrimitiveRoot ζ p) [Finite (KummerGroup p κ)] {d : ℕ}
    (hpow : Nat.card (KummerGroup p κ) = p ^ (d + 2)) :
    Nat.card {L : IntermediateField κ K' // IsGalois κ L ∧ Module.finrank κ L = p} =
      (p ^ (d + 2) - 1) / (p - 1) := by
  rw [natCard_galois_finrank_eq_p (k := κ) (K' := K') p hp hζ, hpow]

/-- **The `ζ_p ∈ κ` case of the local inputs, assembled from the primitive inputs.**
`galoisCount` is *derived* here (via the Kummer bridge); what remains as an input is the
reciprocity statement for the abelian rank, the `p`-torsion detection and Ivanov's
residue-characteristic detection. -/
theorem padicGaloisInputs_of_isPrimitiveRoot {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] {p d : ℕ} (hp : p.Prime) {ζ : κ}
    (hζ : IsPrimitiveRoot ζ p) (hpow : Nat.card (KummerGroup p κ) = p ^ (d + 2))
    (hab : HasAbelianFrattiniRank p (d + 2) (Gal(K'/κ)))
    (htor : HasPTorsionAbelianization p (Gal(K'/κ)))
    (hdetect : ResidueCharDetectedBy p (Gal(K'/κ))) :
    PadicGaloisInputs p d 1 κ K' where
  hp := hp
  hδ := le_refl 1
  zeta_iff := ⟨fun _ => ⟨ζ, hζ⟩, fun _ => rfl⟩
  powerQuotient_card := hpow
  abelian_rank := hab
  p_torsion_iff := ⟨fun _ => htor, fun _ => rfl⟩
  residueChar_detected := hdetect

/-- **The non-abelian count in the case `ζ_p ∈ κ`.**  If in addition every degree-`p`
extension of `κ` is Galois (true when `ζ_p ∈ κ`, where every degree-`p` extension is
Kummer) and every index-`p` subgroup of `Gal(κ̄/κ)` is closed (true because the group is
topologically finitely generated), then the *number of degree-`p` extensions* is
`(p^{d+2} - 1)/(p-1)`, i.e. `Gal(κ̄/κ)` has `p`-Frattini rank `d + 2`. -/
theorem hasFrattiniRank_of_isPrimitiveRoot {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] {p : ℕ} (hp : p.Prime) {ζ : κ}
    (hζ : IsPrimitiveRoot ζ p) [Finite (KummerGroup p κ)] {d : ℕ}
    (hpow : Nat.card (KummerGroup p κ) = p ^ (d + 2))
    (hgal : ∀ L : IntermediateField κ K', Module.finrank κ L = p → IsGalois κ L)
    (hclosed : ∀ H : Subgroup (Gal(K'/κ)), H.index = p → IsClosed (H : Set (Gal(K'/κ)))) :
    HasFrattiniRank p (d + 2) (Gal(K'/κ)) := by
  haveI : IsGalois κ K' := IsSepClosure.isGalois
  unfold HasFrattiniRank
  rw [numIndexSubgroups_eq_natCard_finrank_eq (k := κ) (K' := K') p hclosed]
  have heq : Nat.card {L : IntermediateField κ K' // Module.finrank κ L = p} =
      Nat.card {L : IntermediateField κ K' // IsGalois κ L ∧ Module.finrank κ L = p} :=
    Nat.card_congr
      { toFun := fun L => ⟨L.1, hgal L.1 L.2, L.2⟩
        invFun := fun L => ⟨L.1, L.2.2⟩
        left_inv := fun L => Subtype.ext rfl
        right_inv := fun L => Subtype.ext rfl }
  rw [heq, natCard_galois_finrank_eq_p_of_isPrimitiveRoot (K' := K') hp hζ hpow]

end

end NK.LocalAnabelian
