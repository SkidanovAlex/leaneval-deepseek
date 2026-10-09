import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.PrimeIdeles
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle of an exponent function supported on a finite set, as a product of prime idèles

For a number field `K` and a function `f : PrimeIdeal K → ℤ` with finite support contained in a
finite set `s`, the idèle `ideleOfFun K f` (the idèle which is the `f 𝔮`-th power of a local
uniformiser at `𝔮`) is the product `∏_{𝔮 ∈ s} (ideleOfPrime K 𝔮) ^ (f 𝔮)`.

This is the **ideal-idèle computation**'s first half: it turns the idèle attached to a fractional
ideal (`NK.NUV2.RouteB.RayModulus.fracIdele`, which is `ideleOfFun` of the `𝔮`-adic multiplicities)
into a product of prime idèles, so that an idèlic Artin map which is Frobenius-normalised at the
relevant primes computes the Artin symbol of the ideal as `∏ Frob_𝔮 ^ v_𝔮`.

Everything is phrased through `NK.GlobalCFTdeep.SecondInequality.ideleSingle`, whose API
(`ideleOfFun_eq_ideleSingle`, `ideleOfPrime_eq_ideleSingle`, `ideleSingle_mul`, …) already exists.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors IsMulCommutative

namespace Work.SSGRoute.N4Escape

open NK.GlobalCFT

variable {K : Type*} [Field K] [NumberField K]

/-- The single-place idèles as a monoid homomorphism in the local value. -/
noncomputable def ideleSingleHom (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    (𝔭.adicCompletion K)ˣ →* Idele K where
  toFun z := NK.GlobalCFTdeep.SecondInequality.ideleSingle K 𝔭 z
  map_one' := NK.GlobalCFTdeep.SecondInequality.ideleSingle_one 𝔭
  map_mul' z z' := NK.GlobalCFTdeep.SecondInequality.ideleSingle_mul 𝔭 z z'

/-- **The powers of a single-place idèle.**  `(ideleSingle K 𝔭 z)^n = ideleSingle K 𝔭 (z^n)`. -/
theorem ideleSingle_zpow (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (z : (𝔭.adicCompletion K)ˣ) (n : ℤ) :
    (NK.GlobalCFTdeep.SecondInequality.ideleSingle K 𝔭 z) ^ n =
      NK.GlobalCFTdeep.SecondInequality.ideleSingle K 𝔭 (z ^ n) :=
  (map_zpow (ideleSingleHom 𝔭) z n).symm

/-- **The prime idèle as a single-place idèle.** -/
theorem ideleOfPrime_zpow_eq_ideleSingle (𝔭 : NK.Chebotarev.PrimeIdeal K) (n : ℤ) :
    (NK.HeckeL.ideleOfPrime K 𝔭) ^ n =
      NK.GlobalCFTdeep.SecondInequality.ideleSingle K 𝔭
        ((IdeleClassGroup.unifUnit K 𝔭) ^ n) := by
  rw [NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_eq_ideleSingle, ideleSingle_zpow]

/-- **The idèle of an exponent function supported at a single prime.** -/
theorem ideleOfFun_single (𝔭 : NK.Chebotarev.PrimeIdeal K) (f : NK.Chebotarev.PrimeIdeal K → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (hsupp : ∀ q, q ≠ 𝔭 → f q = 0) :
    IdeleClassGroup.ideleOfFun K f hf = (NK.HeckeL.ideleOfPrime K 𝔭) ^ (f 𝔭) := by
  rw [ideleOfPrime_zpow_eq_ideleSingle,
    NK.GlobalCFTdeep.SecondInequality.ideleOfFun_eq_ideleSingle (K := K) (𝔭 := 𝔭) hf hsupp]

/-- **The idèle-factorisation of `ideleOfFun`.**  If the finite support of `f` is contained in the
finite set `s`, then `ideleOfFun K f` is the product of the prime idèles of `s` raised to the
exponents `f 𝔮`. -/
theorem ideleOfFun_eq_prod_ideleOfPrime (s : Finset (NK.Chebotarev.PrimeIdeal K))
    (f : NK.Chebotarev.PrimeIdeal K → ℤ) (hf : ∀ᶠ q in Filter.cofinite, f q = 0)
    (hsupp : ∀ q, q ∉ s → f q = 0) :
    IdeleClassGroup.ideleOfFun K f hf =
      ∏ q ∈ s, (NK.HeckeL.ideleOfPrime K q) ^ (f q) := by
  classical
  revert f
  refine Finset.induction_on s ?base ?step
  case base =>
    intro f hf hsupp
    have hf0 : f = fun _ => 0 := funext fun q => hsupp q (Finset.notMem_empty q)
    subst hf0
    rw [Finset.prod_empty]
    refine Idele.ext fun v => ?_
    rcases v with w | q
    · rfl
    · rfl
  case step =>
    intro 𝔭 s h𝔭 ih f hf hsupp
    -- split off the exponent at `𝔭`
    set g : NK.Chebotarev.PrimeIdeal K → ℤ := fun q => if q = 𝔭 then f q else 0 with hg
    set f' : NK.Chebotarev.PrimeIdeal K → ℤ := fun q => if q = 𝔭 then 0 else f q with hf'
    have hgf : g + f' = f := by
      funext q
      by_cases h : q = 𝔭 <;> simp [hg, hf', h]
    have hgfin : ∀ᶠ q in Filter.cofinite, g q = 0 := by
      rw [Filter.eventually_cofinite]
      refine (Set.finite_singleton 𝔭).subset ?_
      intro q hq
      show q = 𝔭
      by_contra hne
      exact hq (by show (if q = 𝔭 then f q else 0) = 0; rw [if_neg hne])
    have hf'fin : ∀ᶠ q in Filter.cofinite, f' q = 0 := by
      rw [Filter.eventually_cofinite]
      refine ((Filter.eventually_cofinite.mp hf)).subset ?_
      intro q hq hfq
      apply hq
      by_cases h : q = 𝔭
      · show (if q = 𝔭 then 0 else f q) = 0
        rw [if_pos h]
      · show (if q = 𝔭 then 0 else f q) = 0
        rw [if_neg h]
        exact hfq
    have hgf'fin : ∀ᶠ q in Filter.cofinite, (g + f') q = 0 := by
      rw [hgf]; exact hf
    have hgsupp : ∀ q, q ≠ 𝔭 → g q = 0 := by
      intro q hq
      show (if q = 𝔭 then f q else 0) = 0
      rw [if_neg hq]
    have hgsame : g 𝔭 = f 𝔭 := by
      show (if 𝔭 = 𝔭 then f 𝔭 else 0) = f 𝔭
      rw [if_pos rfl]
    have hf'supp : ∀ q, q ∉ s → f' q = 0 := by
      intro q hq
      show (if q = 𝔭 then 0 else f q) = 0
      by_cases h : q = 𝔭
      · rw [if_pos h]
      · rw [if_neg h]
        exact hsupp q (by
          intro hmem
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact h h'
          · exact hq h')
    have hkey : IdeleClassGroup.ideleOfFun K f hf =
        IdeleClassGroup.ideleOfFun K g hgfin * IdeleClassGroup.ideleOfFun K f' hf'fin := by
      rw [NK.HeckeL.Basic.IdeleFun.mul g f' hgfin hf'fin hgf'fin,
        NK.HeckeL.Basic.IdeleFun.congr hgf'fin hf hgf]
    have hsingle : IdeleClassGroup.ideleOfFun K g hgfin = (NK.HeckeL.ideleOfPrime K 𝔭) ^ (f 𝔭) := by
      rw [ideleOfFun_single 𝔭 g hgfin hgsupp, hgsame]
    rw [hkey, hsingle, ih f' hf'fin hf'supp, Finset.prod_insert h𝔭]
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    show (NK.HeckeL.ideleOfPrime K q) ^ (if q = 𝔭 then 0 else f q) =
      (NK.HeckeL.ideleOfPrime K q) ^ (f q)
    rw [if_neg (fun h => h𝔭 (by rw [← h]; exact hq))]

/-- **The ideal-idèle computation for an idèlic Artin map.**  If `f` is supported in the finite set
`s`, every prime of `s` is unramified in `L/K`, `Φ` kills the principal idèles and is
Frobenius-normalised at the primes of `s`, then `Φ` of the idèle `ideleOfFun K f` is
`∏_{𝔮 ∈ s} Frob_𝔮 ^ (f 𝔮)`.

This is the step which turns `χ(Art(𝔡))` into `∑_{𝔮} v_𝔮(𝔡)·χ(Frob_𝔮)` in the orthogonality
computation of the escape-form Grünwald theorem (it applies to the `T'`-free part `𝔡` of the
divisor of the Grünwald element, since `T'` contains all the ramified primes, so that the support
of `𝔡` consists of unramified primes). -/
theorem artinMap_ideleOfFun_eq_prod_frobAtPrime {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (Φ : Idele K →* (L ≃ₐ[K] L))
    (hprin : ∀ a : Kˣ, Φ (Idele.principalIdele K a) = 1)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K, NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮 →
      Φ (NK.HeckeL.ideleOfPrime K 𝔮) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔮)
    (s : Finset (NK.Chebotarev.PrimeIdeal K)) (f : NK.Chebotarev.PrimeIdeal K → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (hsupp : ∀ q, q ∉ s → f q = 0)
    (hunr : ∀ q ∈ s, NK.HeckeL.IsUnramifiedIn (K := K) (L := L) q) :
    Φ (IdeleClassGroup.ideleOfFun K f hf) =
      ∏ q ∈ s, (NK.Chebotarev.frobAtPrime (K := K) (L := L) q) ^ (f q) := by
  rw [ideleOfFun_eq_prod_ideleOfPrime s f hf hsupp, map_prod]
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [map_zpow, hfrob q (hunr q hq)]

end Work.SSGRoute.N4Escape
