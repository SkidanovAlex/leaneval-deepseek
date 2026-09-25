import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.Tower.Defs

/-!
# The Kummer description of the exponent-`p` extensions unramified outside `S`

This file states, in the vocabulary of this area, the Kummer-theoretic description of the abelian
extensions of exponent `p` unramified outside a finite set `S` of finite places, which underlies the
identification of the Selmer group `V_S` with the group of Kummer generators of the maximal such
extension (so that `G_S/Φ(G_S)` is the Pontryagin dual of `V_S/K^{×p}`).

The *statement* is recorded as the named hypothesis
`Work.CFT.Kummer.KummerUnramifiedCorrespondence`; the local-field-theoretic proof (the behaviour of
Kummer extensions `K(ᵖ√x)/K` at a place `v`: unramified as soon as `p ∣ v(x)` and `v ∤ p`, and
splitting completely at `v` exactly when `x ∈ K_v^{×p}`) is not formalised here — it belongs to the
local class field theory that this area deliberately takes as a hypothesis (see `README.md`).
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

/-- `L/K` is **unramified at every finite place outside `S`**: every prime `𝔓` of `𝓞 L` lying over
a prime `𝔭` of `𝓞 K` which is not one of the places in `S` is unramified.  (Unlike
`Work.Tower.IsUnramifiedExtension`, ramification at the places of `S` is allowed.) -/
def IsUnramifiedOutside (K : Type*) [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (L : Type*) [Field L] [Algebra K L] :
    Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (∀ w ∈ S, w.asIdeal ≠ v.asIdeal) →
    Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1

/-- **The Kummer description of the abelian exponent-`p` extensions unramified outside `S`.**
For a number field `K` containing a primitive `p`-th root of unity:

* the Kummer generators `b ∈ Lˣ^p ∩ Kˣ` of a finite Galois extension `L/K` which is abelian of
  exponent `p`, unramified outside `S` and in which every place of `S` splits completely, lie in
  `V_S = selmerGroupAt K p S` (`b ∈ K_v^{×p}` for `v ∈ S` is exactly complete splitting of `v` in
  the Kummer extension `K(ᵖ√b)`, and `v(b) ≡ 0 mod p` is unramifiedness at the places outside `S`);
* conversely every `x ∈ V_S` generates such an extension `K(ᵖ√x)/K` (carrying a `p`-th root of
  `x`), which is how `V_S/K^{×p}` is identified with the group of Kummer generators of the maximal
  exponent-`p` extension unramified outside `S` (the group-theoretic content behind the H¹ rank
  formula (b)). -/
def KummerUnramifiedCorrespondence (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Prop :=
  (∀ (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      (∀ σ : L ≃ₐ[K] L, σ ^ p = 1) → (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
      IsUnramifiedOutside K S L → (∀ v ∈ S, Work.Tower.SplitsCompletelyIn K L v.asIdeal) →
      kummerGenerators K L p ≤ selmerGroupAt K p S) ∧
    (∀ x : Kˣ, x ∈ selmerGroupAt K p S →
      ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
        (_ : IsGalois K L),
        (∀ σ : L ≃ₐ[K] L, σ ^ p = 1) ∧ (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
          IsUnramifiedOutside K S L ∧
          (∀ v ∈ S, Work.Tower.SplitsCompletelyIn K L v.asIdeal) ∧
          (∃ y : L, y ^ p = algebraMap K L (x : K)))

end Work.CFT.Kummer
