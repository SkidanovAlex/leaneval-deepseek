import Mathlib
import Submission.Work.SSGRoute.ZDataMup.MyImports
import Submission.Work.SSGRoute.ZDataMup.localFactor_productFormula_abelian
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.localFactor_unramified_eq_frob_zpow
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos
import Submission.Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_frobAtPrime_of_mem_span_of_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The product formula at the places of the ramified support

The gluing computation for the idèlic Artin map `Φ : 𝕀_K →* Gal(L/K)` of a congruence datum: for
`x ∈ Kˣ` which is a local unit at every place of a finite set `T` containing the ramified primes
and at every prime `𝔮 | (m)` outside `T`, and which is positive at every real place, one has

  `artinSym (x·𝓞 K) * ∏_{𝔮 ∈ T} Φ (onePlace_𝔮 (x_𝔮)) = 1`.

The proof is the standard one: `Φ` kills the principal idèles, so

  `1 = Φ (principalIdele K x) = ∏_v Φ (onePlace_v (x_v))`

(`cprod_localFactor_eq_one`), and the only places contributing are those where `x_v` is not a local
unit.  Those are exactly the places in the support of the exponent vector `exps (x·𝓞 K)`; they are
all finite, all unramified in `L` and all outside `(m)`, so at each of them the local factor is the
Frobenius raised to the multiplicity (`localFactor_at_prime_eq_frob_pow`), and the product of those
is by definition `artinSym (x·𝓞 K)`.

## Contents

* `cprod_union_of_disjoint`, `cprod_image_ofFinite` — bookkeeping for `cprod`;
* `count_eq_zero_iff_localUnit` — the local unit ↔ zero `𝔮`-adic multiplicity dictionary;
* `localFactor_at_prime_eq_frob_pow` — the local factor at a single unramified prime where
  `Φ (ideleOfPrime Q) = frobAtPrime Q`, isolated from
  `Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow` (which asks for the normalisation at
  *every* unramified prime, more than the conductor-drop setting provides);
* `localFactor_eq_one_of_localUnit`, `localFactor_ofInfinite_eq_one_of_pos` — the trivial local
  factors;
* `productFormula_ramifiedSupport` — the target statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

/-! ## Bookkeeping for `cprod` -/

/-- Splitting a `cprod` over a disjoint union. -/
theorem cprod_union_of_disjoint {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    {ι : Type} [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) (f : ι → G) :
    NK.CFTLib.IdeleHasse.cprod hcomm (s ∪ t) f
      = NK.CFTLib.IdeleHasse.cprod hcomm s f * NK.CFTLib.IdeleHasse.cprod hcomm t f := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold NK.CFTLib.IdeleHasse.cprod
  exact Finset.prod_union h

/-- A `cprod` over the image of a finset of finite places is the product over the source, the
insertion `Place.ofFinite` being injective. -/
theorem cprod_image_ofFinite {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    {K : Type} [Field K] [NumberField K] [DecidableEq (NK.GlobalCFT.Place K)]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (f : NK.GlobalCFT.Place K → G) :
    NK.CFTLib.IdeleHasse.cprod hcomm (T.image (NK.GlobalCFT.Place.ofFinite (K := K))) f
      = NK.CFTLib.IdeleHasse.cprod hcomm T (fun 𝔮 => f (NK.GlobalCFT.Place.ofFinite 𝔮)) := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold NK.CFTLib.IdeleHasse.cprod
  refine Finset.prod_image ?_
  intro a _ b _ hab
  exact Sum.inr.inj hab

/-! ## The local unit ↔ multiplicity dictionary -/

/-- **The `𝔮`-adic multiplicity of a principal ideal vanishes exactly at the local units.**  The
multiplicity of `𝔮` in `(x)` is the `𝔮`-adic valuation of the local image of `x`
(`finVal_localImageAt_eq_count`), and the latter vanishes exactly on the local units
(`finVal_eq_zero_iff_mem_localUnits`). -/
theorem count_eq_zero_iff_localUnit {K : Type} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : Kˣ) :
    FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) ((x : Kˣ) : K)) = 0
      ↔ NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x ∈
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔮) := by
  rw [← finVal_localImageAt_eq_count (K := K) 𝔮 x]
  exact NK.CFTLib.finVal_eq_zero_iff_mem_localUnits K 𝔮 _

/-! ## The local factor at a single unramified prime -/

/-- **The local factor at a single unramified prime where the prime idèle is the Frobenius.**

This is `Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow` with the hypothesis
`Φ (ideleOfPrime Q') = frobAtPrime Q'` required only at the single prime `Q`; the proof is
reproduced. -/
theorem localFactor_at_prime_eq_frob_pow {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)}
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q)
    (hF : Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    (x : Kˣ) :
    Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x))
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q ^
        (FractionalIdeal.count K Q (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (x : K))) := by
  classical
  let ψ : (Q.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    Φ.comp (NK.CFTLib.IdeleHasse.onePlaceHom (NK.GlobalCFT.Place.ofFinite Q))
  have hψ_apply : ∀ a : (Q.adicCompletion K)ˣ,
      ψ a = Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) a) := fun a => rfl
  have hψ_localUnits :
      ∀ u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q), ψ u = 1 := by
    intro u hu
    rw [hψ_apply]
    have hsub := NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
      (K := K) (L := L) Q hunr hu
    have hmem : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u ∈
        NK.GlobalCFT.Idele.normImage K L :=
      (NK.CFTLib.IdeleHasse.onePlace_ofFinite_mem_normImage_iff (K := K) (L := L) Q u).mpr hsub
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hmem
    rw [show NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u
        = NK.GlobalCFT.Idele.normIdeleHom K L y from NK.GlobalCFT.Idele.ext fun v => hy v]
    exact hN y
  have hψ_unif : ψ (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    rw [hψ_apply, NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime]
    exact hF
  obtain ⟨n, u, hu, hdec⟩ := NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits (K := K) Q
    (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x)
  have hψa : ψ (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q ^ n := by
    rw [hdec, map_mul, map_zpow, hψ_unif, hψ_localUnits u hu, mul_one]
  have hn : n = NK.CFTLib.finVal K Q
      (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x) := by
    have hval : Valued.v (((NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x :
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ)) :
          NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))
        = WithZero.exp (-n) := by
      rw [hdec, Units.val_mul, map_mul, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow,
        (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hu, mul_one]
    rw [NK.CFTLib.finVal, hval, WithZero.log_exp]
    ring
  rw [← hψ_apply (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x), hψa, hn,
    finVal_localImageAt_eq_count]

/-! ## The trivial local factors -/

/-- **The local factor at a finite place where `x` is a local unit and which is unramified**: a
local unit is a local norm there, hence an idèle norm, hence killed by `Φ`. -/
theorem localFactor_eq_one_of_localUnit {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)}
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) (x : Kˣ)
    (hu : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
      NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q)) :
    Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x)) = 1 := by
  have hsub := NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
    (K := K) (L := L) Q hunr hu
  have hmem : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
      (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x) ∈
        NK.GlobalCFT.Idele.normImage K L :=
    (NK.CFTLib.IdeleHasse.onePlace_ofFinite_mem_normImage_iff (K := K) (L := L) Q _).mpr hsub
  obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hmem
  rw [show NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x)
      = NK.GlobalCFT.Idele.normIdeleHom K L y from NK.GlobalCFT.Idele.ext fun v => hy v]
  exact hN y

/-- **The archimedean local factor of a totally positive `x` is trivial**: `x` is a local norm at
every real place by its positivity, hence at every place. -/
theorem localFactor_ofInfinite_eq_one_of_pos {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)}
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (x : Kˣ)
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((x : Kˣ) : K)))
    (w : NumberField.InfinitePlace K) :
    Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) x)) = 1 := by
  have hmem : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) :=
    ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos x w hpos
  have hmem' : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w)
      (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) x) ∈
        NK.GlobalCFT.Idele.normImage K L :=
    (NK.CFTLib.IdeleHasse.onePlace_ofInfinite_mem_normImage_iff (K := K) (L := L) w _).mpr hmem
  obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hmem'
  rw [show NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) x)
      = NK.GlobalCFT.Idele.normIdeleHom K L y from NK.GlobalCFT.Idele.ext fun v => hy v]
  exact hN y

/-! ## The product formula at the ramified support -/

theorem productFormula_ramifiedSupport {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (Φ : NK.GlobalCFT.Idele K →* Gal(L/K))
    (hprin : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hnorm : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hfrob : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔮.asIdeal →
      Φ (NK.HeckeL.ideleOfPrime K 𝔮) = NK.Chebotarev.frobAtPrime 𝔮)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hTram : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 → 𝔮 ∈ T)
    (hTunr : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔮 ∉ T → Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) = 1)
    (x : Kˣ)
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((x : Kˣ) : K)))
    (hunitT : ∀ 𝔮 ∈ T,
      NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x ∈
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔮))
    (hunitm : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal → 𝔮 ∉ T →
      NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x ∈
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔮)) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((x : Kˣ) : K))
      * (NK.CFTLib.IdeleHasse.cprod hcomm T (fun 𝔮 =>
          Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮)
            (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x)))) = 1 := by
  classical
  set A : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) ((x : Kˣ) : K)
    with hA
  set F : NK.GlobalCFT.Place K → Gal(L/K) := fun v =>
    Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) with hF
  have hF_apply : ∀ v : NK.GlobalCFT.Place K, F v =
      Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) := fun v => rfl
  set Tp : Finset (NK.GlobalCFT.Place K) := T.image NK.GlobalCFT.Place.ofFinite with hTp
  set Sp : Finset (NK.GlobalCFT.Place K) :=
    (NK.CFTLib.Arl.exps A).support.image NK.GlobalCFT.Place.ofFinite with hSp
  -- the local unit ↔ multiplicity dictionary for `A`
  have hcount_iff : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K 𝔮 A = 0 ↔
        NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x ∈
          NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔮) := by
    intro 𝔮
    rw [hA]
    exact count_eq_zero_iff_localUnit 𝔮 x
  -- the local factor at a place of the support is the corresponding Frobenius power
  have hpoint : ∀ 𝔮 ∈ (NK.CFTLib.Arl.exps A).support,
      F (NK.GlobalCFT.Place.ofFinite 𝔮)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔮 ^ (NK.CFTLib.Arl.exps A 𝔮) := by
    intro 𝔮 h𝔮
    rw [Finsupp.mem_support_iff, NK.CFTLib.Arl.exps_apply] at h𝔮
    have hnu : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x ∉
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔮) :=
      fun hu => h𝔮 ((hcount_iff 𝔮).mpr hu)
    have h𝔮T : 𝔮 ∉ T := fun hmem => hnu (hunitT 𝔮 hmem)
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮 :=
      isUnramifiedIn_of_ramificationIdxIn_eq_one 𝔮 (hTunr 𝔮 h𝔮T)
    have hmq : (m : NumberField.RingOfIntegers K) ∉ 𝔮.asIdeal :=
      fun hmem => hnu (hunitm 𝔮 hmem h𝔮T)
    have h1 := localFactor_at_prime_eq_frob_pow hnorm 𝔮 hunr (hfrob 𝔮 hmq) x
    rw [hF_apply, show NK.CFTLib.Arl.exps A 𝔮 = FractionalIdeal.count K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            ((x : Kˣ) : K)) from by rw [NK.CFTLib.Arl.exps_apply, hA]]
    exact h1
  -- the `cprod` over the support of `exps A` is the Artin symbol
  have hSp_eq : NK.CFTLib.IdeleHasse.cprod hcomm Sp F
      = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A := by
    rw [hSp, cprod_image_ofFinite]
    letI : CommMonoid (Gal(L/K)) := NK.CFTLib.Arl.galCommMonoid hcomm
    unfold NK.CFTLib.Arl.artinSym
    rw [Finsupp.prod_of_support_subset (f := NK.CFTLib.Arl.exps A) (Finset.Subset.refl _)
      (g := fun 𝔭 e => (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e)
      (fun i _ => zpow_zero _)]
    exact Finset.prod_congr rfl (fun 𝔮 h𝔮 => hpoint 𝔮 h𝔮)
  -- the `cprod` over `T` is the one of the statement
  have hTp_eq : NK.CFTLib.IdeleHasse.cprod hcomm Tp F
      = NK.CFTLib.IdeleHasse.cprod hcomm T (fun 𝔮 =>
          Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮)
            (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x))) := by
    rw [hTp, cprod_image_ofFinite]
  -- the two halves are disjoint: at a place of `T` the element `x` is a local unit
  have hdisj : Disjoint Sp Tp := by
    rw [Finset.disjoint_left]
    intro v hvSp hvTp
    rw [hSp] at hvSp
    obtain ⟨𝔮, h𝔮S, h𝔮v⟩ := Finset.mem_image.mp hvSp
    rw [hTp] at hvTp
    obtain ⟨𝔮', h𝔮'T, h𝔮'v⟩ := Finset.mem_image.mp hvTp
    have hqq' : 𝔮 = 𝔮' := Sum.inr.inj (h𝔮v.trans h𝔮'v.symm)
    rw [← hqq'] at h𝔮'T
    rw [Finsupp.mem_support_iff, NK.CFTLib.Arl.exps_apply] at h𝔮S
    exact h𝔮S ((hcount_iff 𝔮).mpr (hunitT 𝔮 h𝔮'T))
  -- every place outside `T` and off the support has trivial local factor
  have hrest : ∀ v : NK.GlobalCFT.Place K, v ∉ Sp ∪ Tp →
      Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1 := by
    intro v hv
    cases v with
    | inl w => exact localFactor_ofInfinite_eq_one_of_pos hnorm x hpos w
    | inr 𝔮 =>
      have hvSp : NK.GlobalCFT.Place.ofFinite 𝔮 ∉ Sp := fun h => hv (Finset.mem_union_left _ h)
      have hvTp : NK.GlobalCFT.Place.ofFinite 𝔮 ∉ Tp := fun h => hv (Finset.mem_union_right _ h)
      have h𝔮T : 𝔮 ∉ T := fun h𝔮T => hvTp (by
        rw [hTp]; exact Finset.mem_image_of_mem _ h𝔮T)
      have h𝔮S : 𝔮 ∉ (NK.CFTLib.Arl.exps A).support := fun h𝔮S => hvSp (by
        rw [hSp]; exact Finset.mem_image_of_mem _ h𝔮S)
      have hcount0 : FractionalIdeal.count K 𝔮 A = 0 := by
        rw [← NK.CFTLib.Arl.exps_apply]
        exact Finsupp.notMem_support_iff.mp h𝔮S
      have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮 :=
        isUnramifiedIn_of_ramificationIdxIn_eq_one 𝔮 (hTunr 𝔮 h𝔮T)
      by_cases hmq : (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal
      · exact localFactor_eq_one_of_localUnit hnorm 𝔮 hunr x ((hcount_iff 𝔮).mp hcount0)
      · rw [localFactor_at_prime_eq_frob_pow hnorm 𝔮 hunr (hfrob 𝔮 hmq) x, ← hA, hcount0,
          zpow_zero]
  -- the product formula on `Sp ∪ Tp`, split over the two halves
  have hmain := cprod_localFactor_eq_one (K := K) (L := L) hcomm Φ hprin hnorm x (Sp ∪ Tp) hrest
  rw [cprod_union_of_disjoint hcomm hdisj F] at hmain
  rw [hSp_eq, hTp_eq] at hmain
  exact hmain

end Work.SSGRoute.ZDataMup
