/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

The Dedekind zeta functions of `L` and of `K`, with the primes over a modulus removed.  These are
the two "unramified" Euler products which occur in the factorisation
`∏_χ L(s, χ) = ζ_L(s)/ζ_K(s) · (finite correction)`.
-/
import Submission.NK.HeckeL.Artin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors Topology
open Filter

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

namespace NK.HeckeL

variable {K L : Type*}

/-- The Euler product over the primes of `K` outside the modulus `S`:
`∏_{𝔭 ∉ S} (1 - N𝔭^{-s})⁻¹`.  For `S` containing the ramified primes this is the Euler product of
the Dedekind zeta function of `K` with the Euler factors at `S` removed. -/
noncomputable def zetaUnramifiedK (K : Type*) [Field K] [NumberField K] (S : Finset (PrimeIdeal K))
    (s : ℝ) : ℂ :=
  ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
    (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹

/-- The Euler product over the primes of `L` which do not lie over any prime of the modulus `S`:
the Euler product of the Dedekind zeta function of `L` with the Euler factors at the primes above
`S` removed. -/
noncomputable def zetaUnramified (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (S : Finset (PrimeIdeal K)) (s : ℝ) : ℂ :=
  ∏' 𝔮 : {𝔮 : PrimeIdeal L // ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal},
    (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹

/-- The Euler factors at the primes above the modulus: the correction which turns
`zetaUnramified` into the full Dedekind zeta function of `L`. -/
noncomputable def zetaRamified (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (S : Finset (PrimeIdeal K)) (s : ℝ) : ℂ :=
  ∏' 𝔮 : {𝔮 : PrimeIdeal L // ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal},
    (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹

end NK.HeckeL
