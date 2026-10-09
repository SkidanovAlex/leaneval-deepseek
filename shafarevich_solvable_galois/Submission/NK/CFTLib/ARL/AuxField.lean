import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.CyclotomicSubextension
import Submission.NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe
import Submission.NK.CFTLib.ARL.Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The auxiliary field of Artin's lemma

This module fixes the *interface* between the two halves of the proof of Lang, *Algebraic Number
Theory*, Ch. X §2, Theorem 2 (Childress, *Class Field Theory*, Prop. 2.2 and Lemma 2.8) for a
cyclic extension `L/K` of number fields:

* `NK.CFTLib.ARL.AuxFieldHyp K L m` — the **auxiliary-field hypothesis** of Artin's lemma, in
  the *corrected* (multi-prime) form needed by the transfer;
* `NK.CFTLib.ARL.auxField_exists_B` — the theorem that the hypothesis holds for every `m > 0`;
* `NK.CFTLib.ARL.kernelLe_of_auxField_B` — the transfer, which deduces
  `ker ψ ⊆ P(m)·𝔑(m)` from the hypothesis.

## Why the hypothesis is stated the way it is (a correction)

The naive interface asks, for a finite set `s` of primes and a single field `E ⊆ L(ζ_M)`
(depending on `s`), for

  `E ∩ L = K` and `E·ℚ(ζ_M) = L(ζ_M)` and `𝔭` splits completely in `E/K` for **all** `𝔭 ∈ s`.

**This is FALSE for `|s| ≥ 2`.**  Writing `Γ = Gal(L(ζ_M)/K) ≅ G × Δ` (`Δ = Gal(K(ζ_M)/K)`,
`G = Gal(L/K)`, valid when `L ∩ K(ζ_M) = K`) and `H = Gal(L(ζ_M)/E)`:
`E ∩ L = K` gives `proj_G(H) = G`, while `E·ℚ(ζ_M) = L(ζ_M)` gives `H ∩ (G×1) = 1`.  The
Frobenius element of `𝔭` in `Γ` is `Φ_𝔭 = ((𝔭,L/K), N𝔭 mod M)`, whose `Δ`-component depends only
on the *absolute* norm `N𝔭`; complete splitting of `𝔭` in `E/K` forces `Φ_𝔭 ∈ H`.  Two primes
`𝔭, 𝔭̄` with the same absolute norm but different Frobenius in `L/K` (e.g. for `K = ℚ(√2)`,
`L = ℚ(2^{1/4})`, the two primes above `7`: `𝔭` is inert, `𝔭̄` splits) then give
`Φ_𝔭 Φ_𝔭̄⁻¹ = (σ,1) ∈ H ∩ (G×1)`, `σ ≠ 1` — a contradiction.

The correct interface imposes the strong join condition only on **individual** auxiliary fields:
there is a single `M` and a single composite field `E ⊆ L(ζ_M)` with `E ∩ L = K`, and for every
`𝔭 ∈ s` a subfield `E_𝔭 ≤ E` with `E_𝔭·ℚ(ζ_M) = L(ζ_M)` and `𝔭` splitting completely in `E_𝔭/K`.
This is enough for the transfer: the cells `L·E_𝔭/E_𝔭` are subextensions of the cyclotomic
extensions `E_𝔭(ζ_M)/E_𝔭` (and are cyclic of degree `n`, because `E_𝔭 ∩ L = K`), `𝔭` is a norm
from `E_𝔭`, and the *composite* `E` supplies a single ideal `𝔟 = N_{E/K}(𝔟_E) ∈ I(m)` with
`ψ_{L/K}(𝔟) = σ` that is a norm from every `E_𝔭`, whence the final bookkeeping `𝔟^{Σ e𝔭 s𝔭} ∈ 𝔑(m)`.

## The complete construction plans

`Submission/Work/CFTLib/ARL/NOTES_artinLemma_and_transfer.md` (same directory) contains the full
plan of the two proofs that use this interface:

* `NK.CFTLib.ARL.auxField_exists_B` — the construction of `M`, `E` and the `E_𝔭`
  (CRT choice `M = q₀·∏_𝔭 q_𝔭`, the product decomposition `Gal(L(ζ_M)/K) ≅ G × (ℤ/M)^×`, and
  `E_𝔭 = Ω^{⟨(σ,τ_𝔭), Φ_𝔭⟩·Δ'_𝔭}`, `E = Ω^{⋂_𝔭 (⟨(σ,τ_𝔭),Φ_𝔭⟩·Δ'_𝔭)}`);
* `NK.CFTLib.ARL.kernelLe_of_auxField_B` — the transfer (`𝔟 = N_{E/K}𝔅_E`, the cells
  `L·E_𝔭/E_𝔭` and `NK.CFTLib.ARL.cyclotomicCellKernelLe_B`, the norm descent, and the final
  bookkeeping `𝔟^{Σ e𝔭 s𝔭} = (𝔟^n)^k ∈ 𝔑(m)`).

The interface is `NK.CFTLib.Existence.AuxFieldHypCorrected`
(`Submission/Work/CFTLib/Existence/AuxFieldCorrected.lean`); this module only fixes the name and
records the role.  The mathematics is recorded in
`Submission/Work/CFTLib/ARL/NOTES_exists_auxiliary_field.md` and in the docstring of
`Submission/Work/CFTLib/Existence/AuxFieldCorrected.lean` (the counterexample).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARL

/-- **The auxiliary-field hypothesis of Artin's lemma** (corrected, multi-prime form): for every
finite set `s` of primes of `K` prime to `(m)` and every finite set `S` of rational primes there
are `M ≥ 1` coprime to `m`, not divisible by any prime of `S`, and not divisible by any prime
dividing `N(𝔭)` (`𝔭 ∈ s`), together with a subfield `E ⊆ L(ζ_M)` with `L ∩ K(ζ_M) = K` and
`E ∩ L = K`, such that for every `𝔭 ∈ s` there is a subfield `E_𝔭 ≤ E` with
`E_𝔭·ℚ(ζ_M) = L(ζ_M)` and `𝔭` splitting completely in `E_𝔭/K`.

Literally the same statement is `NK.CFTLib.Existence.AuxFieldHypCorrected`
(`Submission/Work/CFTLib/Existence/AuxFieldCorrected.lean`); the two definitions are
interchangeable, and that file establishes the counterexample to the stronger form. -/
def AuxFieldHyp (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (m : ℕ) : Prop :=
  ∀ (s : Finset (NK.Chebotarev.PrimeIdeal K)) (hs : ∀ 𝔭 ∈ s, (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime),
    ∃ (M : ℕ) (_ : NeZero M), M.Coprime m ∧ (∀ p ∈ S, ¬ p ∣ M) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal) ∧
      Disjoint ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K)
        (IntermediateField.adjoin K
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))) ∧
      ∃ E : IntermediateField K (CyclotomicField M L),
        Disjoint E ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K) ∧
        (∀ 𝔭 ∈ s, ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
          E𝔭 ≤ E ∧
          (E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
            ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
              Set (CyclotomicField M L))) = ⊤ ∧
          NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭 1)

end NK.CFTLib.ARL
