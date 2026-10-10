import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.CFTLib.ARL.transfer_of_auxField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The transfer of Artin's lemma (Lang, *Algebraic Number Theory*, X §2, Theorem 2)

This module establishes `NK.CFTLib.ArtinReciprocityIdeal.transferOfAuxField`: the **transfer**
step of the ideal-theoretic reciprocity law for a finite cyclic extension `L/K` of number fields.
From Artin's lemma in the corrected (per-prime) auxiliary-field form
`NK.CFTLib.ARL.AuxFieldHyp K L m` — one auxiliary field `E ⊇ E_𝔭` with `E ⊓ L = K`,
`E_𝔭 ⊔ ℚ(ζ_M) = Ω = L(ζ_M)` and `𝔭` splitting completely in `E_𝔭/K` for every prime `𝔭` in a
prescribed finite set `s` — together with the hypothesis `hram` that every prime ramified in `L/K`
divides `(m)`, it deduces the kernel containment

  `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)`,

i.e. every fractional ideal `A` of `K` coprime to `(m)` whose Artin symbol `ψ_{L/K}(A)` is trivial
lies in `principalRay K m ⊔ normRay K L m`.

## The proof

The transfer is the content of `NK.CFTLib.ARL.TFP.transferAux`
(`Submission/Work/CFTLib/ARL/transfer_of_auxField.lean`, Artin's trick, self-contained there and complete), and the statement below is that theorem in the `Gal(L/K)`-notation of this file:
`NK.CFTLib.ARL.transfer_of_auxField`.

Briefly (Childress, *Class Field Theory*, Prop. 2.2; Lang, *ANT* X §2): factor
`A = ∏_{𝔭 ∈ s} 𝔭^{e_𝔭}`, apply `haux` to `s` to obtain `M`, `E` and `E_𝔭`, and put `𝔪 := m·M`.
Choosing `𝔅 ∈ I(E)(𝔪)` with `ψ_{Ω/E}(𝔅)` restricting on `L` to a generator `σ` of `Gal(L/K)`
(surjectivity of the Artin symbol for the abelian extension `Ω/E` plus the isomorphism
`Gal(Ω/E) ≅ Gal(L/K)` for `E ⊓ L = K`), the ideal `𝔟 := N_{E/K}𝔅` satisfies `ψ_{L/K}(𝔟) = σ` by
the norm/restriction compatibility `ψ_{Ω/E}(𝔄)|_L = ψ_{L/K}(N_{E/K}𝔄)`.  For each `𝔭 ∈ s` the ideal
`𝔘_𝔭 := 𝔓_𝔭^{e_𝔭}·(N_{E/E_𝔭}𝔅)^{-e_𝔭 s_𝔭}` (with `𝔓_𝔭 | 𝔭` in `E_𝔭`, so `N_{E_𝔭/K}𝔓_𝔭 = 𝔭`, and
`σ^{s_𝔭} = ψ_{L/K}(𝔭)`) has trivial Artin symbol in `E_𝔭·L/E_𝔭`, hence lies in `P·𝔑` there by the
cyclotomic cell `NK.CFTLib.ARLAlt.cellAtAuxField`; its norm down is
`X_𝔭 = 𝔭^{e_𝔭}𝔟^{-e_𝔭s_𝔭}`, and the norm descent of `Submission/Work/CFTLib/ARLAlt/Descent.lean`
gives `X_𝔭 ∈ P_K(m)·𝔑_{L/K}(m)`.  Multiplying over `𝔭 ∈ s` and using the divisibility
`[L:K] ∣ Σ_𝔭 e_𝔭 s_𝔭` (which follows from `ψ_{L/K}(A) = 1` and the cyclicity of `L/K`), together
with `𝔟^{[L:K]} = N_{L/K}(𝔟·𝒪_L) ∈ 𝔑(m)`, gives `A ∈ P_K(m)·𝔑_{L/K}(m)`.
-/

namespace NK.CFTLib.ArtinReciprocityIdeal

theorem transferOfAuxField (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsMulCommutative (L ≃ₐ[K] L)] (m : ℕ) (hm : 0 < m)
    (haux : NK.CFTLib.ARL.AuxFieldHyp K L m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
  intro A hcop hsym
  exact NK.CFTLib.ARL.transfer_of_auxField K L m hm haux hram A hcop hsym

end NK.CFTLib.ArtinReciprocityIdeal
