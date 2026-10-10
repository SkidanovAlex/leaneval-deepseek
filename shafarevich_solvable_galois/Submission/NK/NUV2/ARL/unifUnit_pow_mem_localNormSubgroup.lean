import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.HR.Basic
import Submission.NK.CFTLib.NormPrincipal.localNormFinite_range_iff_inertiaDeg_dvd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm of a local uniformiser at an unramified place

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` which is
**unramified** in `L`, and `q | Q` a prime of `𝓞 L` above `Q`, with inertia degree
`f = f(q | Q)`.  The main result,

  `NK.NUV2.ARL.zpow_unifUnit_inertiaDeg_mem_localNormSubgroup`,

says that the `f`-th power of a local uniformiser `ϖ_Q` of `K_Q` lies in the local norm subgroup
`N_Q = ⨆_{q | Q} N_{L_q/K_Q}(L_qˣ)`.

This is the classical statement `N_{L_q/K_Q}(ϖ_q) = ϖ_Q^f · (unit)`, together with the fact that at
an **unramified** place every local unit is a local norm
(`NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified`).  Concretely:

* `Place.localNormFinite q Q hq (unifUnit L q)` lies in `localNormSubgroup Q` by definition, and
  `NK.CFTLib.val_localNormFinite` computes its valuation as
  `Valued.v (unifUnit L q) ^ f = WithZero.exp (-1) ^ f = WithZero.exp (-f)`;
* `NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits` writes
  `Place.localNormFinite q Q hq (unifUnit L q) = ϖ_Q ^ n · u` with `u` a local unit; comparing
  valuations gives `n = f`, so `ϖ_Q ^ f = N(ϖ_q) · u⁻¹`;
* `u⁻¹` is a local norm because `Q` is unramified.

This is exactly the arithmetic input isolated as the missing step **L3** in
`Submission/Work/CFTLib/HR/STATUS.md` (there called "`π^f ∈ N_Q`, i.e. the norm of a uniformiser"),
which turns the value `art (onePlace Q b) = Frob_Q ^ (v_Q b)` of the idèlic Artin map of a
cyclotomic extension into the local-norm criterion `b ∈ N_Q ⟺ f ∣ v_Q(b)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ARL

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The `f`-th power of a local uniformiser is a local norm at an unramified place.**

For a finite place `Q` of `K` which is unramified in `L`, a prime `q | Q` of `𝓞 L`, and
`f = f(q|Q)` the inertia degree, the element `ϖ_Q ^ f` of `K_Qˣ` lies in the local norm subgroup
`N_Q = ⨆_{q | Q} N_{L_q/K_Q}(L_qˣ)`. -/
theorem zpow_unifUnit_inertiaDeg_mem_localNormSubgroup (Q : HeightOneSpectrum (𝓞 K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q)
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) :
    (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q) ^ ((q.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℤ)
      ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) := by
  classical
  set z : (Q.adicCompletion K)ˣ :=
    Place.localNormFinite q Q hq (IdeleClassGroup.unifUnit L q) with hz
  -- `z` is a local norm, by definition of the local norm subgroup
  have hzmem : z ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (Place.ofFinite Q) := by
    rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
    exact Subgroup.mem_iSup_of_mem ⟨q, hq⟩ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  -- decompose `z = ϖ_Q ^ n · u` with `u` a local unit
  obtain ⟨n, u, hu, hzu⟩ := NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits (K := K) Q z
  -- compare the valuations: `n = f`
  have hzval : Valued.v (z : Q.adicCompletion K) = WithZero.exp (-n) := by
    rw [hzu, Units.val_mul, map_mul, IdeleClassGroup.valued_unifUnit_zpow,
      (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hu, mul_one]
  have hzval' : Valued.v (z : Q.adicCompletion K)
      = WithZero.exp (-((q.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℤ)) := by
    rw [hz, NK.CFTLib.val_localNormFinite, IdeleClassGroup.valued_unifUnit,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hn : n = ((q.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℤ) := by
    have h := hzval.symm.trans hzval'
    exact neg_injective (WithZero.exp_injective h)
  -- hence `ϖ_Q ^ f = z · u⁻¹` is a local norm
  have hmain : (IdeleClassGroup.unifUnit K Q) ^ ((q.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℤ)
      = z * u⁻¹ := by
    rw [hzu, hn]
    group
  rw [hmain]
  exact Subgroup.mul_mem _ hzmem
    (Subgroup.inv_mem _ (NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
      (K := K) (L := L) Q hunr hu))

/-! ## The local norm group at an unramified place, in divisibility form

`NK.CFTLib.NormPrincipal.localNormFinite_range_iff_inertiaDeg_dvd` identifies the image of the
local norm `N_{L_q/K_Q}` on the completions with the elements of `K_Qˣ` whose `Q`-adic valuation is
divisible by `f = f(q|Q)`, but under the *global* hypothesis that `L/K` is unramified at **every**
finite place.  The two lemmas below remove that hypothesis: only `e(q|Q) = 1` is used, and the
`⨆`-form of the local norm subgroup is reduced to a single one of its factors by the equality of
the ranges of the local norms at the primes above `Q` (`range_localNormFinite_eq_of_liesOver`).
-/

/-- **The range of the local norm at a place with `e = 1`, in divisibility form.**  Same statement
and proof as `NK.CFTLib.NormPrincipal.localNormFinite_range_iff_inertiaDeg_dvd`, with the global
hypothesis `differentIdeal (𝓞 F) (𝓞 K) = ⊤` weakened to the local one
`e(q|Q) = 1` (which is all that its proof uses). -/
theorem localNormFinite_range_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one
    {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (Q : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (he : q.asIdeal.ramificationIdx (𝓞 F) = 1) (z : (Q.adicCompletion F)ˣ) :
    (∃ y : (q.adicCompletion K)ˣ, Place.localNormFinite q Q hq y = z) ↔
      (q.asIdeal.inertiaDeg (𝓞 F) : ℤ) ∣ NK.CFTLib.finVal F Q z := by
  letI : Algebra (Q.adicCompletion F) (q.adicCompletion K) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  have hlf : Place.localNormFinite q Q hq =
      Units.map (Algebra.norm (Q.adicCompletion F)) := rfl
  have hstep : (∃ y : (q.adicCompletion K)ˣ, Place.localNormFinite q Q hq y = z) ↔
      (∃ x : q.adicCompletion K,
        Algebra.norm (Q.adicCompletion F) x = (z : Q.adicCompletion F)) := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(y : q.adicCompletion K), by rw [← hy, hlf, Units.coe_map]⟩
    · rintro ⟨x, hx⟩
      haveI : Module.Finite (Q.adicCompletion F) (q.adicCompletion K) :=
        Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
      haveI : Module.Free (Q.adicCompletion F) (q.adicCompletion K) :=
        Module.Free.of_divisionRing _ _
      have hxne : x ≠ 0 := by
        intro hx0
        rw [hx0, Algebra.norm_zero] at hx
        exact (Units.ne_zero z) hx.symm
      refine ⟨Units.mk0 x hxne, ?_⟩
      rw [hlf]
      exact Units.ext (by rw [Units.coe_map, Units.val_mk0]; exact hx)
  rw [hstep, Commons.NumberTheory.NumberField.Completion.norm_range_of_ramificationIdx_eq_one
      Q q hq he (z : Q.adicCompletion F)]
  exact NK.CFTLib.NormPrincipal.exists_val_eq_pow_iff_dvd_finVal Q z _
    (Ideal.inertiaDeg_pos q.asIdeal (𝓞 F))

/-- **The local norm subgroup at an unramified place, in divisibility form.**

For a finite place `Q` of `K` with `e(q|Q) = 1` for every `q | Q`, a prime `q | Q` and
`z ∈ K_Qˣ`: the element `z` is a local norm from `L` at `Q` if and only if its `Q`-adic valuation
`finVal K Q z` is divisible by the inertia degree `f(q|Q)`.

Equivalently, `N_Q = ⟨ϖ_Q^f⟩ · 𝒪_Qˣ`, the classical description of the norm group of an
unramified local extension. -/
theorem mem_localNormSubgroup_ofFinite_iff_inertiaDeg_dvd (Q : HeightOneSpectrum (𝓞 K))
    (hunr : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal →
      q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (z : (Q.adicCompletion K)ˣ) :
    z ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) ↔
      (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ NK.CFTLib.finVal K Q z := by
  rw [← NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup Q q hq]
  exact localNormFinite_range_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one Q q hq (hunr q hq) z


/-! ## The local kernel of an idèlic Artin map at an unramified place

Let `art : 𝕀 K →* Gal(L/K)` be a homomorphism killing the idèle norms `N_{L/K}𝕀_L` and carrying the
idèle of an **unramified** finite place `Q` to `frobAtPrime Q`.  Then the kernel of
`a ↦ art (onePlace Q a)` on `K_Qˣ` is exactly the local norm group `N_Q`.

This is the "alternative finish" of `Submission/Work/CFTLib/HR/STATUS.md` (step L3), and it turns
the value `art (onePlace Q b) = 1` — the only thing a global reciprocity law at a modulus can give
at `Q` — into the local-norm statement `b ∈ N_Q`, via the description
`N_Q = {b | f(q|Q) ∣ v_Q(b)}` of the local norm group of an unramified local extension.
-/

/-- `onePlace` of the local uniformiser is the idèle of the prime. -/
theorem onePlace_unifUnit_eq_ideleOfPrime (Q : HeightOneSpectrum (𝓞 K)) :
    NK.HassePrinciple.onePlace (Place.ofFinite Q) (IdeleClassGroup.unifUnit K Q) =
      NK.HeckeL.ideleOfPrime K Q := by
  ext v
  rcases v with w | q
  · rw [NK.HassePrinciple.onePlace_apply_ne (by simp),
      NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofInfinite]
  · by_cases h : q = Q
    · subst h
      rw [NK.HassePrinciple.onePlace_apply_self,
        NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_self]
    · rw [NK.HassePrinciple.onePlace_apply_ne (by simpa using h),
        NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_ne_setup h]

/-- **The local kernel of an idèlic Artin map at an unramified finite place.**

Let `art : 𝕀 K →* Gal(L/K)` kill the idèle norms `N_{L/K}𝕀_L` and send the idèle of the unramified
prime `Q` to `frobAtPrime Q`.  Then for `a ∈ K_Qˣ`, `art (onePlace Q a) = 1` forces `a ∈ N_Q`:
the local norm group of an unramified local extension is exactly the subgroup of elements whose
valuation is divisible by the inertia degree. -/
theorem mem_localNormSubgroup_of_onePlace_mem_ker [IsMulCommutative (Gal(L/K))]
    (Q : HeightOneSpectrum (𝓞 K)) (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q)
    (art : Idele K →* Gal(L/K))
    (hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1)
    (hfrob : art (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    {a : (Q.adicCompletion K)ˣ}
    (ha : art (NK.HassePrinciple.onePlace (Place.ofFinite Q) a) = 1) :
    a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) := by
  classical
  -- a prime of `𝓞 L` above `Q`, and the inertia degree
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  -- the one-place Artin map `ψ = art ∘ onePlace Q`
  set ψ : (Q.adicCompletion K)ˣ →* Gal(L/K) := art.comp (NK.CFTLib.IdeleHasse.onePlaceHom (Place.ofFinite Q)) with hψ
  have hψ_apply : ∀ b, ψ b = art (NK.HassePrinciple.onePlace (Place.ofFinite Q) b) :=
    fun b => rfl
  -- `N_Q ⊆ ker ψ`: a local norm is an idèle norm
  have hle : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q)
      ≤ MonoidHom.ker ψ := by
    intro b hb
    rw [MonoidHom.mem_ker, hψ_apply]
    have hmem : NK.HassePrinciple.onePlace (Place.ofFinite Q) b ∈ Idele.normImage K L :=
      (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
        (Place.ofFinite Q) b).mpr hb
    obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hmem
    rw [show NK.HassePrinciple.onePlace (Place.ofFinite Q) b = Idele.normIdeleHom K L y from
      Idele.ext fun v => hy v]
    exact hnorm y
  -- `ψ` of the uniformiser is the Frobenius
  have hψ_unif : ψ (IdeleClassGroup.unifUnit K Q) =
      NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    rw [hψ_apply, onePlace_unifUnit_eq_ideleOfPrime]
    exact hfrob
  -- the order of the Frobenius is the inertia degree
  have hord : orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
      = q.asIdeal.inertiaDeg (𝓞 K) :=
    NK.CFTLib.ArtinReciprocityIdeal.orderOf_frobAtPrime_eq_inertiaDeg Q q hq hunr
  -- decompose `a = ϖ_Q ^ n · u` with `u` a local unit
  obtain ⟨n, u, hu, hzu⟩ := NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits (K := K) Q a
  have hψu : ψ u = 1 := MonoidHom.mem_ker.mp (hle
    (NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L)
      Q hunr hu))
  -- hence `ψ a = Frob ^ n`, and `ψ a = 1` forces the inertia degree to divide `n`
  have hψa : ψ a = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ n := by
    rw [hzu, map_mul, map_zpow, hψ_unif, hψu, mul_one]
  have h1 : (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ n = 1 := by
    rw [← hψa, hψ_apply]
    exact ha
  have hdvd : (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ n := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  -- the valuation of `a` is `n`
  have hfin : NK.CFTLib.finVal K Q a = n := by
    have huval : Valued.v ((u : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = 1 :=
      (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hu
    rw [NK.CFTLib.finVal, hzu, Units.val_mul, map_mul,
      IdeleClassGroup.valued_unifUnit_zpow, huval, mul_one, WithZero.log_exp, neg_neg]
  -- conclude with the divisibility description of `N_Q`
  exact (mem_localNormSubgroup_ofFinite_iff_inertiaDeg_dvd (K := K) (L := L) Q hunr q hq a).mpr
    (by rw [hfin]; exact hdvd)


end NK.NUV2.ARL
