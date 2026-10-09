import Mathlib
import Submission.NK.HeckeL.Product.dedekindZeta_eulerProduct
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace NK.HeckeL.Nonvanishing

/-- **The Euler product of the Dedekind zeta function with finitely many factors removed.**

For a number field `K`, a finite set `S` of primes and a real `s > 1`, the Euler product
`∏_{𝔭 ∉ S} (1 - N𝔭^{-s})⁻¹` equals the value `ζ_K(s)` of the Dedekind zeta function times the
finite product `∏_{𝔭 ∈ S} (1 - N𝔭^{-s})` of the removed local factors. -/
theorem zetaUnramifiedK_eq_dedekindZeta_mul {K : Type*} [Field K] [NumberField K]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.zetaUnramifiedK K S s =
      ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) *
        ∏ 𝔭 ∈ S, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) := by
  classical
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
  -- The local factors `(1 - N𝔭^{-s})⁻¹` are positive reals and their logarithms are summable.
  have hpos : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
      0 < Commons.NumberTheory.NumberField.DedekindZeta.localFactor K s 𝔭.asIdeal := by
    intro 𝔭
    rw [Commons.NumberTheory.NumberField.DedekindZeta.localFactor]
    exact inv_pos.mpr (by linarith [Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one (K := K) hs0 𝔭])
  have hsumm : Summable (fun 𝔭 : NK.HeckeL.PrimeIdeal K =>
      Real.log (Commons.NumberTheory.NumberField.DedekindZeta.localFactor K s 𝔭.asIdeal)) :=
    Commons.NumberTheory.NumberField.DedekindZeta.summable_log_localFactor (K := K) hs
  -- Hence the Euler product over the primes outside `S` is multipliable, as a product of
  -- positive reals and therefore as a product of complex numbers.
  have hsumm' : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      Real.log (Commons.NumberTheory.NumberField.DedekindZeta.localFactor K s 𝔭.1.asIdeal)) :=
    hsumm.comp_injective Subtype.coe_injective
  have hmulR : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      Commons.NumberTheory.NumberField.DedekindZeta.localFactor K s 𝔭.1.asIdeal) :=
    Real.multipliable_of_summable_log (fun 𝔭 => hpos 𝔭.1) hsumm'
  have hmulC : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      ((Commons.NumberTheory.NumberField.DedekindZeta.localFactor K s 𝔭.1.asIdeal : ℝ) : ℂ)) :=
    hmulR.map Complex.ofRealHom Complex.continuous_ofReal
  have hcomp : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) := by
    refine hmulC.congr (fun 𝔭 => ?_)
    rw [Commons.NumberTheory.NumberField.DedekindZeta.localFactor]
    push_cast
    ring
  -- Splitting the Euler product over all primes into the primes in `S` and the primes outside.
  have hsplit : (∏ 𝔭 ∈ S, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) *
      (∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) := by
    set F : NK.HeckeL.PrimeIdeal K → ℂ := fun 𝔭 =>
      (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
    have hcompF : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} => F 𝔭.1) :=
      hcomp
    have h1 : (∏' x : ↥(S : Set (NK.HeckeL.PrimeIdeal K)), F x) = ∏ 𝔭 ∈ S, F 𝔭 :=
      Finset.tprod_subtype' S F
    have h2 : (∏' x : ↥((S : Set (NK.HeckeL.PrimeIdeal K))ᶜ), F x)
        = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, F 𝔭.1 := by
      apply tprod_congr_subtype
      intro x
      exact Iff.rfl
    have h3 : (∏' x : NK.HeckeL.PrimeIdeal K, F x)
        = ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) := by
      rw [← NK.HeckeL.Product.dedekindZeta_eulerProduct (K := K) hs]
    have hfin : Multipliable (fun x : ↥(S : Set (NK.HeckeL.PrimeIdeal K)) => F x) :=
      (hasProd_fintype _ _).multipliable
    have hspl := Multipliable.tprod_mul_tprod_compl (f := F)
      (s := (S : Set (NK.HeckeL.PrimeIdeal K))) hfin hcompF
    simpa only [h1, h2, h3] using hspl
  have hA : (∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = NK.HeckeL.zetaUnramifiedK K S s := rfl
  -- The finite product of the removed factors is the inverse of the product of the inverses.
  have hBA : (∏ 𝔭 ∈ S, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) *
      (∏ 𝔭 ∈ S, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro 𝔭 _
    have hx : ((1 : ℝ) - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≠ 0 := by
      have := Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one
        (K := K) hs0 𝔭
      linarith
    have hx' : (1 : ℂ) - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
      exact hx
    rw [inv_mul_cancel₀ hx']
  have hD : (∏ 𝔭 ∈ S, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) *
      NK.HeckeL.zetaUnramifiedK K S s = ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) := by
    rw [← hA]
    exact hsplit
  rw [← hD, mul_comm (∏ 𝔭 ∈ S, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
    (NK.HeckeL.zetaUnramifiedK K S s), mul_assoc, hBA, mul_one]

end NK.HeckeL.Nonvanishing
