/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

The fibre decomposition of the truncated Euler product of `L`, expressed in the vocabulary of
`NK.HeckeL.Nonvanishing.primeFiber` (the prime `underPrime 𝔮` of `K` below a prime `𝔮` of `L`
and the fibre `primesOverPrime K L 𝔭 = {𝔮 // underPrime 𝔮 = 𝔭}`):

`∏_{𝔮 ∉ S} (1 - N𝔮^{-s})⁻¹ = ∏_{𝔭 ∉ S} ∏_{𝔮 | 𝔭} (1 - N𝔮^{-s})⁻¹`.

The proof splits the index set `{𝔮 // underPrime 𝔮 ∉ S}` along the fibres of `underPrime` using
`Equiv.sigmaFiberEquiv` and `HasProd.sigma`, the fibres being finite.  The absolute convergence of
the product over all the places of `L` is obtained from the Dedekind zeta function of `L`, via the
positive real local factors and `Real.multipliable_of_summable_log`.
-/
import Mathlib
import Submission.NK.HeckeL.Nonvanishing.primeFiber
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors

noncomputable section

namespace NK.HeckeL.Nonvanishing

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

open Commons.NumberTheory.NumberField.DedekindZeta in
/-- The Euler factors `(1 - N𝔮^{-s})⁻¹` over the primes of `L` avoiding a modulus `S` form an
absolutely convergent product for `s > 1`: this is the restriction of the Euler product of the
Dedekind zeta function of `L`. -/
theorem multipliable_eulerFactor_subtype (S : Finset (PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    Multipliable (fun 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} =>
      (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) := by
  have hspos : (0 : ℝ) < s := lt_trans zero_lt_one hs
  have hpos : ∀ 𝔮 : PrimeIdeal L, 0 < localFactor L s 𝔮.asIdeal := fun 𝔮 => by
    rw [localFactor]
    exact inv_pos.mpr (by linarith [rpow_neg_absNorm_primeIdeal_lt_one (K := L) hspos 𝔮])
  have hsum : Summable (fun 𝔮 : PrimeIdeal L => Real.log (localFactor L s 𝔮.asIdeal)) :=
    summable_log_localFactor (K := L) hs
  have hU : Summable (fun 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} =>
      Real.log (localFactor L s 𝔮.1.asIdeal)) :=
    hsum.subtype (fun 𝔮 : PrimeIdeal L => underPrime (K := K) 𝔮 ∉ S)
  have hmulR : Multipliable (fun 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} =>
      localFactor L s 𝔮.1.asIdeal) :=
    Real.multipliable_of_summable_log (fun 𝔮 => hpos 𝔮.1) hU
  refine (hmulR.map Complex.ofRealHom Complex.continuous_ofReal).congr (fun 𝔮 => ?_)
  rw [Function.comp_apply, localFactor]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

/-- **The fibre decomposition of the truncated Euler product of `L`**: the product over the places
of `L` outside the modulus `S` is the product, over the places `𝔭` of `K` outside `S`, of the
products over the places of `L` above `𝔭`. -/
theorem zetaUnramified_eq_tprod_primesOver (S : Finset (PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    zetaUnramified K L S s
      = ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          ∏' 𝔮 : primesOverPrime K L 𝔭.1,
            (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
  have hd := multipliable_eulerFactor_subtype (K := K) (L := L) S hs
  have hzeq : zetaUnramified K L S s
      = ∏' 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S},
          (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    rw [zetaUnramified_eq_tprod_primesOutside]
    exact tprod_congr_subtype
      (fun 𝔮 : PrimeIdeal L =>
        (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      (fun 𝔮 => not_liesOver_iff_underPrime_notMem)
  let F : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} → {𝔭 : PrimeIdeal K // 𝔭 ∉ S} :=
    fun 𝔮 => ⟨underPrime 𝔮.1, 𝔮.2⟩
  let G : (Σ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭}) → ℂ :=
    fun x => (1 - (((Ideal.absNorm x.2.1.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
  have hsig : Multipliable G :=
    (Equiv.multipliable_iff
      (f := fun 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} =>
        (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      (Equiv.sigmaFiberEquiv F)).mpr hd
  -- the fibre over `𝔭` is `primesOverPrime K L 𝔭`
  let hfib : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭} ≃
        primesOverPrime K L 𝔭.1 := fun 𝔭 =>
    { toFun := fun a => ⟨a.1.1, by simpa using congrArg Subtype.val a.2⟩
      invFun := fun a => ⟨⟨a.1, by rw [a.2]; exact 𝔭.2⟩, by exact Subtype.ext a.2⟩
      left_inv := fun a => Subtype.ext (Subtype.ext rfl)
      right_inv := fun a => Subtype.ext rfl }
  have hrow : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      HasProd (fun a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭} =>
          G ⟨𝔭, a⟩)
        (∏' a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭},
          G ⟨𝔭, a⟩) := by
    intro 𝔭
    haveI : Fintype {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭} :=
      Fintype.ofEquiv _ (hfib 𝔭).symm
    exact (hasProd_fintype
      (fun a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭} =>
        G ⟨𝔭, a⟩)).multipliable.hasProd
  have h1 : ∏' x : Σ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
        {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭}, G x
      = ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          ∏' a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭},
            G ⟨𝔭, a⟩ :=
    (HasProd.sigma hsig.hasProd hrow).tprod_eq.symm
  have h2 : ∏' 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S},
        (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
      = ∏' x : Σ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭}, G x :=
    ((Equiv.sigmaFiberEquiv F).tprod_eq
      (fun 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} =>
        (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)).symm
  have hinner : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      (∏' a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭}, G ⟨𝔭, a⟩)
      = ∏' 𝔮 : primesOverPrime K L 𝔭.1,
        (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    intro 𝔭
    calc ∏' a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭},
            G ⟨𝔭, a⟩
        = ∏' a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭},
            (1 - (((Ideal.absNorm ((hfib 𝔭) a).1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ :=
          tprod_congr (fun a => rfl)
      _ = ∏' 𝔮 : primesOverPrime K L 𝔭.1,
            (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ :=
          Equiv.tprod_eq (hfib 𝔭)
            (fun 𝔮 : primesOverPrime K L 𝔭.1 =>
              (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
  calc zetaUnramified K L S s
      = ∏' 𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S},
          (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := hzeq
    _ = ∏' x : Σ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭}, G x := h2
    _ = ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          ∏' a : {𝔮 : {𝔮 : PrimeIdeal L // underPrime (K := K) 𝔮 ∉ S} // F 𝔮 = 𝔭},
            G ⟨𝔭, a⟩ := h1
    _ = ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          ∏' 𝔮 : primesOverPrime K L 𝔭.1,
            (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := tprod_congr hinner

end NK.HeckeL.Nonvanishing
