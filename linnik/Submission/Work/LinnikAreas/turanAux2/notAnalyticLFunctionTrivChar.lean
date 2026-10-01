import Mathlib

namespace Work.LinnikAreas.turanAux2

open Filter
open scoped Topology

/-- The product `∏_{p ∣ q} (1 - p⁻¹)` is nonzero. -/
private lemma prod_one_sub_inv_ne_zero (q : ℕ) :
    (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hne : (p : ℂ)⁻¹ ≠ 1 := by
    rw [inv_ne_one]
    exact_mod_cast hp'.ne_one
  exact sub_ne_zero.mpr (Ne.symm hne)

/-- The trivial Dirichlet character's `L`-function has a simple pole at `s = 1`, hence is not
analytic there. -/
theorem notAnalyticLFunctionTrivChar (q : ℕ) [NeZero q] :
    ¬ AnalyticAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) 1 := by
  intro h
  have hcont : ContinuousAt (DirichletCharacter.LFunctionTrivChar q) 1 := h.continuousAt
  -- The residue limit: `(s - 1) * L(s, χ₀) → ∏_{p ∣ q} (1 - p⁻¹)`.
  have hres := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
  -- The same expression tends to `0` along the punctured neighbourhood.
  have hzero : Tendsto (fun s ↦ (s - 1) * DirichletCharacter.LFunctionTrivChar q s)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
      have hc : ContinuousAt (fun s : ℂ ↦ s - 1) (1 : ℂ) :=
        continuousAt_id.sub continuousAt_const
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (DirichletCharacter.LFunctionTrivChar q) (𝓝[≠] (1 : ℂ))
        (𝓝 (DirichletCharacter.LFunctionTrivChar q 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1.mul h2
  have hzero' : (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) = 0 :=
    tendsto_nhds_unique hres hzero
  exact prod_one_sub_inv_ne_zero q hzero'

end Work.LinnikAreas.turanAux2
