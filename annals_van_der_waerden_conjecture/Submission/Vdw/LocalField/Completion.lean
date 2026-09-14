import Mathlib
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

open scoped NumberField
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (stone 1): the completion `K_P` of a number field at a prime

This is the first file of the local-field development that the S1 gate
(`wild_different_count_le`, Roadmap Sessions 42–47) needs.  Three fleet
verdicts (L78/L90/L91) established that the per-prime wild different bound is
equivalent to constructing a **wild trace witness**
(`y ∈ Q^(v_p(e)+1)` with `p^(v_p(e)+1) ∤ Tr(y)`), whose proof requires a
missing library chapter: the number-field completion `K_P` at a prime ideal,
its `ℚ_p`-extension structure, the maximal unramified subfield `W`, and the
local trace identity `Tr_{K_P/ℚ_p}(w) = e·Tr_{W/ℚ_p}(w)` for `w ∈ W`
(Teichmüller/unramified-lift API).

This module assembles the first concrete objects from Mathlib's modern adic
infrastructure (this revision has `IsDedekindDomain.HeightOneSpectrum`,
`v.adicCompletion K`, `ℚ_[p]` = `Padic p` with `ℤ_[p]` = `PadicInt p`, and
the identification `Rat.HeightOneSpectrum.padicEquiv` between the completion
of `ℚ` at a height-one prime and `ℚ_[p]`):

* `Completion.kprime p P` — the `HeightOneSpectrum (𝓞 K)` given by a maximal
  ideal `P` of `𝓞 K` lying over the rational prime `p`;
* `Completion.kpAdic p P` — the `P`-adic completion `K_P := v.adicCompletion K`
  (a complete non-archimedean valued field);
* `Completion.kpInt p P` — its ring of integers `v.adicCompletionIntegers K`.

**Goal structure (next stones, in dependency order):**
1. `Algebra ℚ_[p] K_P` — the `ℚ_p`-extension structure on `K_P`: the
   continuous extension of `ℚ ↪ K` (functoriality of `adicCompletion` under
   the Dedekind morphism `ℤ → 𝓞 K` pulling `P` back to `(p)`), followed by
   `Rat.HeightOneSpectrum.padicEquiv` to identify the base completion with
   `ℚ_[p]`;
2. `W :=` the maximal unramified subfield of `K_P/ℚ_p` — with residue field
   `κ_P = 𝓞 K/P` (degree `f := P.inertiaDeg ℤ` over `𝔽_p`), constructed via
   Teichmüller lifts of `κ_P`;
3. the local trace identity `Tr_{K_P/ℚ_p}(w) = e·Tr_{W/ℚ_p}(w)` (`e :=
   P.ramificationIdx ℤ`) and trace reduction mod `p` for unramified
   extensions — the ingredients the witness construction needs
   (test case: `ℚ(ζ₃,√2)` at `p = 2`, `e = f = 2`: witness `ζ₃` with
   `Tr = −2`, `y = 1` failing since `Tr(1) = 4`).

File header kept dependency-light; each new stone is a separate module in
`Submission/Vdw/LocalField/`.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The height-one prime ideal of `𝓞 K` given by a maximal ideal `P` lying
over the rational prime `p` (nonzero since `P` lies over the nonzero prime
ideal `(p)` of `ℤ`). -/
noncomputable def kprime (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) := by
  classical
  have hpZ : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by
    intro hz
    have hp0 : (p : ℤ) = 0 := (Ideal.span_singleton_eq_bot.mp hz)
    exact (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)) (by omega)
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpZ P
  exact ⟨P, ‹P.IsMaximal›.isPrime, hne⟩

/-- The `P`-adic completion `K_P := v.adicCompletion K` of the number field
`K` at the prime `P | (p)` (a complete, non-archimedean, locally compact
valued field; instance structure from Mathlib's `adicCompletion`). -/
abbrev kpAdic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] : Type u :=
  (kprime p P).adicCompletion K

/-- The ring of integers of `K_P` (the valuation subring of the completion). -/
abbrev kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] : Type u :=
  (kprime p P).adicCompletionIntegers K

-- sanity checks (verified): the completion is a field; K embeds into it as
-- an algebra; the ring of integers is a ℤ-algebra.  (Typeclass instances on
-- the `abbrev`s are synthesized by Mathlib's `adicCompletion` machinery.)

/-- The underlying ideal of the height-one prime `kprime p P` is `P` itself. -/
theorem kprime_asIdeal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (kprime p P).asIdeal = P := by
  rfl

/-- The canonical dense embedding of `K` into its completion `K_P`. -/
theorem kpAdic_algebraMap_eq_coe (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : K) :
    (algebraMap K (kpAdic p P) x : kpAdic p P) = (x : (kprime p P).adicCompletion K) := by
  rfl

end
end Submission.Vdw.LocalField
