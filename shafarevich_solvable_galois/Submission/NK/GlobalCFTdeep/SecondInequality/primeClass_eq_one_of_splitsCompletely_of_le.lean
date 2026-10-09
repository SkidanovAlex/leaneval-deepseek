/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A completely split prime is a norm

Let `L / K` be a finite Galois extension of number fields and let `𝔭` be a prime of `K` which
splits completely in `L`.  Then the idèle `ideleOfPrime K 𝔭` (the chosen uniformiser at `𝔭`, and
`1` at every other place) is the idèlic norm of an idèle of `L`: the prime `𝔭` is a norm.

Consequently, in the ray class group `𝕀 K ⧸ (Kˣ · U)` for a subgroup `U ≤ 𝕀 K` containing the norm
subgroup `N_{L/K} 𝕀 L`, the class of `𝔭` is trivial.

The proof is the componentwise computation of the idèlic norm.  Choose `𝔓` above `𝔭`.  Since `𝔭`
splits completely, the local extension `L_𝔓 / K_𝔭` has degree `1`, so every local unit of `K_𝔭` is a
local norm (`norm_units_surjective_of_ramificationIdx_eq_one`); pick a unit `u` of `L_𝔓` with
`N(π_𝔓 · u) = π_𝔭`.  The idèle `y` of `L` which is `π_𝔓 · u` at `𝔓` and `1` elsewhere then has
`N(y) = ideleOfPrime K 𝔭`: at `𝔭` this is the identity `N(π_𝔓 · u) = π_𝔭`, and at every other place
both sides are `1`.

## Main results

* `ideleOfPrime_mem_normImage_of_splitsCompletely`
* `primeClass_eq_one_of_splitsCompletely_of_le`
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped NumberField WithZero BigOperators Classical nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

section Helpers

variable {L : Type*} [Field L] [NumberField L]

/-- The finite component of `ideleOfPrime L 𝔓` at a prime `q`: it is the local uniformiser at
`q = 𝔓` and `1` elsewhere. -/
private theorem ideleOfPrime_apply_ofFinite (𝔓 q : PrimeIdeal L) :
    NK.HeckeL.ideleOfPrime L 𝔓 (NK.GlobalCFT.Place.ofFinite q) =
      NK.GlobalCFT.IdeleClassGroup.unifUnit L q ^ (if q = 𝔓 then (1 : ℤ) else 0) := rfl

/-- The archimedean component of `ideleOfPrime` is trivial. -/
private theorem ideleOfPrime_apply_ofInfinite (𝔓 : PrimeIdeal L) (w : InfinitePlace L) :
    NK.HeckeL.ideleOfPrime L 𝔓 (NK.GlobalCFT.Place.ofInfinite w) = 1 := rfl

variable {K : Type*} [Field K] [NumberField K]

/-- `ideleOfFun` only depends on the function, not on the proof of its finite support. -/
private theorem ideleOfFun_congr {f g : PrimeIdeal K → ℤ}
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (hg : ∀ᶠ q in Filter.cofinite, g q = 0)
    (h : f = g) :
    NK.GlobalCFT.IdeleClassGroup.ideleOfFun K f hf
      = NK.GlobalCFT.IdeleClassGroup.ideleOfFun K g hg := by
  subst h
  exact Subtype.ext rfl

/-- The idèle attached to a prime ideal is the idèle attached to the corresponding ideal. -/
private theorem ideleOfPrime_eq_ideleOfIdeal (𝔭 : PrimeIdeal K) :
    NK.HeckeL.ideleOfPrime K 𝔭 = NK.HeckeL.ideleOfIdeal K 𝔭.asIdeal := by
  refine ideleOfFun_congr _ _ ?_
  funext q
  rw [FractionalIdeal.count_maximal K q 𝔭]
  by_cases h : q = 𝔭
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

end Helpers
section UnitIdèle

variable {L : Type*} [Field L] [NumberField L]

/-- The idèle which is the local unit `u` at the finite place `q` and `1` at every other place. -/
private noncomputable def ideleOfUnitAt (L : Type*) [Field L] [NumberField L]
    (q : PrimeIdeal L) (u : (q.adicCompletion L)ˣ) : NK.GlobalCFT.Idele L :=
  ⟨fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q' => if h : q' = q then h.symm ▸ u else 1, by
      classical
      rw [Filter.eventually_cofinite]
      refine Set.Finite.subset (Set.finite_singleton (NK.GlobalCFT.Place.ofFinite q)) ?_
      intro v hv
      rcases v with w | q'
      · exact absurd (NK.GlobalCFT.Place.mem_localUnits_ofInfinite (w := w) (x := (1 : _))) hv
      · by_cases h : q' = q
        · rw [h]
          exact Set.mem_singleton _
        · exfalso
          refine hv ?_
          simp only [dif_neg h]
          exact Subgroup.one_mem _⟩

@[simp] private theorem ideleOfUnitAt_apply_ofFinite_self (q : PrimeIdeal L)
    (u : (q.adicCompletion L)ˣ) :
    ideleOfUnitAt L q u (NK.GlobalCFT.Place.ofFinite q) = u := by
  show (if h : q = q then h.symm ▸ u else 1) = u
  rw [dif_pos rfl]

@[simp] private theorem ideleOfUnitAt_apply_ofFinite_ne {q q' : PrimeIdeal L} (h : q' ≠ q)
    (u : (q.adicCompletion L)ˣ) :
    ideleOfUnitAt L q u (NK.GlobalCFT.Place.ofFinite q') = 1 := by
  show (if h : q' = q then h.symm ▸ u else 1) = 1
  rw [dif_neg h]

@[simp] private theorem ideleOfUnitAt_apply_ofInfinite (q : PrimeIdeal L) (u : (q.adicCompletion L)ˣ)
    (w : InfinitePlace L) :
    ideleOfUnitAt L q u (NK.GlobalCFT.Place.ofInfinite w) = 1 := rfl

end UnitIdèle
/-! ## The idèle of a single finite place with a prescribed value, and the local computation -/

/-! ## The local computation -/

section Local

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The local norm of a uniformiser is a uniformiser times a norm of a unit.**  If `q | Q` with
`e = f = 1`, then there is a unit `u` of `L_q` such that the norm of the local uniformiser times
`u` is the local uniformiser of `K_Q`. -/
private theorem exists_unit_mul_norm_unifUnit
    (Q : PrimeIdeal K) (q : PrimeIdeal L)
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (he : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (hf : q.asIdeal.inertiaDeg (𝓞 K) = 1) :
    ∃ u : (q.adicCompletion L)ˣ,
      NK.GlobalCFT.Place.localNormFinite q Q hq
          (NK.GlobalCFT.IdeleClassGroup.unifUnit L q * u)
        = NK.GlobalCFT.IdeleClassGroup.unifUnit K Q := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  have halg : ∀ z : Q.adicCompletion K,
      algebraMap (Q.adicCompletion K) (q.adicCompletion L) z
        = Commons.RingTheory.Henselian.adicCompletionMap Q q hq z :=
    fun z => RingHom.congr_fun (RingHom.algebraMap_toAlgebra _) z
  have hfr : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = 1 := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq, he, hf, mul_one]
  have hvalnorm : ∀ z : q.adicCompletion L,
      Valued.v (Algebra.norm (Q.adicCompletion K) z)
        = (Valued.v z : WithZero (Multiplicative ℤ)) := by
    intro z
    have h1 := Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow Q q hq z
    have h2 : Valued.v (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) z))
        = (Valued.v (Algebra.norm (Q.adicCompletion K) z) : WithZero (Multiplicative ℤ))
            ^ q.asIdeal.ramificationIdx (𝓞 K) := by
      rw [halg]
      exact Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
        (Algebra.norm (Q.adicCompletion K) z)
    rw [h2, he, pow_one, hfr, pow_one] at h1
    exact h1
  have hxv : (Valued.v ((NK.GlobalCFT.IdeleClassGroup.unifUnit L q : (q.adicCompletion L)ˣ) :
      q.adicCompletion L) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) :=
    NK.GlobalCFT.IdeleClassGroup.valued_unifUnit (K := L) q
  set c : Q.adicCompletion K := Algebra.norm (Q.adicCompletion K)
      ((NK.GlobalCFT.IdeleClassGroup.unifUnit L q : (q.adicCompletion L)ˣ) : q.adicCompletion L)
    with hcdef
  have hcv : (Valued.v c : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := by
    rw [hcdef, hvalnorm]
    exact hxv
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcv
    exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) hcv.symm
  set C : (Q.adicCompletion K)ˣ := Units.mk0 c hcne with hCdef
  set u₀ : (Q.adicCompletion K)ˣ := NK.GlobalCFT.IdeleClassGroup.unifUnit K Q / C with hu₀def
  have hu₀v : (Valued.v ((u₀ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) :
      WithZero (Multiplicative ℤ)) = 1 := by
    have hcu : ((u₀ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)
        = (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q : Q.adicCompletion K) / c := by
      rw [hu₀def, Units.val_div_eq_div_val, hCdef, Units.val_mk0]
    rw [hcu, map_div₀, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit (K := K) Q, hcv,
      div_self (WithZero.exp_ne_zero (a := (-1 : ℤ)))]
  obtain ⟨y, hy⟩ :=
    Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
      Q q hq he (u₀ : Q.adicCompletion K) hu₀v
  have hyv : (Valued.v y : WithZero (Multiplicative ℤ)) = 1 := by
    rw [← hvalnorm y, hy]
    exact hu₀v
  have hyne : y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hyv
    exact zero_ne_one hyv
  refine ⟨Units.mk0 y hyne, ?_⟩
  have h1 : NK.GlobalCFT.Place.localNormFinite q Q hq
      (NK.GlobalCFT.IdeleClassGroup.unifUnit L q) = C := by
    rw [NK.GlobalCFT.Place.localNormFinite]
    apply Units.ext
    simp only [Units.coe_map, Units.val_mk0, hCdef, hcdef,
      NK.GlobalCFT.IdeleClassGroup.unifUnit, Units.coe_map, Units.val_mk0]
  have h2 : NK.GlobalCFT.Place.localNormFinite q Q hq (Units.mk0 y hyne) = u₀ := by
    rw [NK.GlobalCFT.Place.localNormFinite]
    apply Units.ext
    simp only [Units.coe_map, Units.val_mk0]
    exact hy
  rw [map_mul, h1, h2, hu₀def]
  exact mul_div_cancel C (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)

end Local

/-! ## The main results -/

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **A completely split prime is a norm.**  If `𝔭` splits completely in the finite Galois
extension `L / K`, then the idèle `ideleOfPrime K 𝔭` (the chosen uniformiser at `𝔭`, `1` elsewhere)
lies in the idèlic norm subgroup `N_{L/K} 𝕀 L`.

The witness is `y = ideleOfPrime L 𝔓 * z`, where `𝔓` is a prime of `L` above `𝔭` and `z` is the
idèle which is a suitable unit `u` of `L_𝔓` at `𝔓` and `1` elsewhere; `u` is chosen so that
`N_{L_𝔓/K_𝔭}(π_𝔓 · u) = π_𝔭`, which is possible because `𝔭` splits completely, so that the local
extension has degree `1` and every unit of `K_𝔭` is a local norm.  Then `N(y)` and
`ideleOfPrime K 𝔭` agree at every place, by the componentwise formula for the idèlic norm. -/
theorem ideleOfPrime_mem_normImage_of_splitsCompletely (𝔭 : PrimeIdeal K)
    (h𝔭 : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L) :
    NK.HeckeL.ideleOfPrime K 𝔭 ∈ NK.GlobalCFT.Idele.normImage K L := by
  classical
  -- ### Splitting data: a prime `𝔓 | 𝔭` with `e = f = 1`
  obtain ⟨heIn, hfIn⟩ :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := L) 𝔭).mp h𝔭
  obtain ⟨𝔓, hLies⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
  haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := hLies
  haveI hGal : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  have he : 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    have h1 := Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L)
      𝔭.asIdeal 𝔓.asIdeal (Gal(L/K))
    rw [h1] at heIn
    exact heIn
  have hf : 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    have h1 := Ideal.inertiaDegIn_eq_inertiaDeg (A := 𝓞 K) (B := 𝓞 L)
      𝔭.asIdeal 𝔓.asIdeal (Gal(L/K))
    rw [h1] at hfIn
    exact hfIn
  -- ### The local unit
  obtain ⟨u, hu⟩ := exists_unit_mul_norm_unifUnit (K := K) (L := L) 𝔭 𝔓 hLies he hf
  -- ### The idèle realising the norm
  set z : NK.GlobalCFT.Idele L := ideleOfUnitAt L 𝔓 u with hzdef
  set y : NK.GlobalCFT.Idele L := NK.HeckeL.ideleOfPrime L 𝔓 * z with hydef
  have hz_fin_self : z (NK.GlobalCFT.Place.ofFinite 𝔓) = u := by
    rw [hzdef]
    exact ideleOfUnitAt_apply_ofFinite_self 𝔓 u
  have hz_fin_ne : ∀ q : PrimeIdeal L, q ≠ 𝔓 → z (NK.GlobalCFT.Place.ofFinite q) = 1 := by
    intro q hq
    rw [hzdef]
    exact ideleOfUnitAt_apply_ofFinite_ne hq u
  have hz_inf : ∀ w : InfinitePlace L, z (NK.GlobalCFT.Place.ofInfinite w) = 1 := by
    intro w
    rw [hzdef]
    exact ideleOfUnitAt_apply_ofInfinite 𝔓 u w
  have hy_fin_self : y (NK.GlobalCFT.Place.ofFinite 𝔓)
      = NK.GlobalCFT.IdeleClassGroup.unifUnit L 𝔓 * u := by
    rw [hydef, NK.GlobalCFT.Idele.mul_apply, ideleOfPrime_apply_ofFinite,
      if_pos rfl, zpow_one, hz_fin_self]
  have hy_fin_ne : ∀ q : PrimeIdeal L, q ≠ 𝔓 → y (NK.GlobalCFT.Place.ofFinite q) = 1 := by
    intro q hq
    rw [hydef, NK.GlobalCFT.Idele.mul_apply, ideleOfPrime_apply_ofFinite, if_neg hq,
      zpow_zero, hz_fin_ne q hq, one_mul]
  have hy_inf : ∀ w : InfinitePlace L, y (NK.GlobalCFT.Place.ofInfinite w) = 1 := by
    intro w
    rw [hydef, NK.GlobalCFT.Idele.mul_apply, ideleOfPrime_apply_ofInfinite, hz_inf w, mul_one]
  -- ### The norm of `y`
  have hnorm_lies : ∀ (Q : PrimeIdeal K) (hQ : 𝔓.asIdeal.LiesOver Q.asIdeal),
      NK.GlobalCFT.Idele.normIdeleFun K L y (NK.GlobalCFT.Place.ofFinite Q)
        = NK.GlobalCFT.Place.localNormFinite 𝔓 Q hQ
            (NK.GlobalCFT.IdeleClassGroup.unifUnit L 𝔓 * u) := by
    intro Q hQ
    have hmem : 𝔓 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q :=
      (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := 𝔓)).mpr hQ
    have hsingle : ∀ b ∈ (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).attach,
        b ≠ ⟨𝔓, hmem⟩ →
        (NK.GlobalCFT.Place.localNormFinite b.1 Q
            ((NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := b.1)).mp b.2))
            (y (NK.GlobalCFT.Place.ofFinite b.1)) = 1 := by
      intro b _ hbne
      have hb1 : b.1 ≠ 𝔓 := fun h => hbne (Subtype.ext h)
      rw [hy_fin_ne b.1 hb1, map_one]
    have key : (∏ b ∈ (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).attach,
        (NK.GlobalCFT.Place.localNormFinite b.1 Q
            ((NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := b.1)).mp b.2))
            (y (NK.GlobalCFT.Place.ofFinite b.1)))
        = (NK.GlobalCFT.Place.localNormFinite 𝔓 Q
            ((NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := 𝔓)).mp hmem))
            (y (NK.GlobalCFT.Place.ofFinite 𝔓)) :=
      Finset.prod_eq_single_of_mem _ (Finset.mem_attach _ _) hsingle
    rw [NK.GlobalCFT.Idele.normIdeleFun_ofFinite, key, hy_fin_self]
  have hnorm_not_lies : ∀ (Q : PrimeIdeal K), ¬ 𝔓.asIdeal.LiesOver Q.asIdeal →
      NK.GlobalCFT.Idele.normIdeleFun K L y (NK.GlobalCFT.Place.ofFinite Q) = 1 := by
    intro Q hQ
    rw [NK.GlobalCFT.Idele.normIdeleFun_ofFinite]
    refine Finset.prod_eq_one fun b _ => ?_
    have hb1 : b.1 ≠ 𝔓 := by
      intro h
      exact hQ (h ▸ (NK.GlobalCFT.Place.mem_primesOverFinite
        (K := K) (L := L) (Q := Q) (q := b.1)).mp b.2)
    rw [hy_fin_ne b.1 hb1, map_one]
  have hnorm_inf : ∀ w : InfinitePlace K,
      NK.GlobalCFT.Idele.normIdeleFun K L y (NK.GlobalCFT.Place.ofInfinite w) = 1 := by
    intro w
    rw [NK.GlobalCFT.Idele.normIdeleFun_ofInfinite]
    refine Finset.prod_eq_one fun b _ => ?_
    rw [hy_inf b.1, map_one]
  -- ### The membership in the norm subgroup
  rw [NK.GlobalCFT.Idele.mem_normImage]
  refine ⟨y, fun v => ?_⟩
  rcases v with w | Q
  · rw [ideleOfPrime_apply_ofInfinite, hnorm_inf w]
  · by_cases hQ : Q = 𝔭
    · rw [hQ, hnorm_lies 𝔭 hLies, ideleOfPrime_apply_ofFinite, if_pos rfl, zpow_one, hu]
    · have hnot : ¬ 𝔓.asIdeal.LiesOver Q.asIdeal := by
        intro h
        have h1 : Q.asIdeal = 𝔓.asIdeal.under (𝓞 K) := h.over
        have h2 : 𝔭.asIdeal = 𝔓.asIdeal.under (𝓞 K) := hLies.over
        exact hQ (HeightOneSpectrum.ext (h1.trans h2.symm))
      rw [hnorm_not_lies Q hnot, ideleOfPrime_apply_ofFinite, if_neg hQ, zpow_zero]

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely_of_le`,
-- namespace `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFTdeep.SecondInequality.Defs` (for the `PrimeIdeal` shorthand) and
-- `Submission.NK.GlobalCFT.NormFunctorial` (for `NK.GlobalCFT.Idele.normImage`,
-- `normIdeleHom`, `normIdeleFun`, `principalSubgroup`, `principalIdele`); `Defs` brings in
-- `Submission.NK.HeckeL.All` (for `NK.HeckeL.primeClass`, `ideleOfPrime`, `ideleOfIdeal`).
-- Useful as well:
-- `Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one`.
--
-- MATHEMATICS.  `primeClass K U 𝔭` is the class of the ideal `𝔭` in the ray class group
-- `rayClassGroup K U = 𝕀 K ⧸ (Kˣ ⊔ U)`, i.e. the class of the idèle `ideleOfIdeal K 𝔭.asIdeal`
-- (`ideleOfPrime K 𝔭`: the idèle with the chosen uniformiser at `𝔭` and `1` elsewhere).  Its
-- triviality means `ideleOfPrime K 𝔭 ∈ Kˣ ⊔ U`.
--
-- If `𝔭` splits completely in `L`, take `𝔓 | 𝔭`.  Since `[L_𝔓 : K_𝔭] = 1` the local norm of a
-- uniformiser is again one, so `N_{L/K}(ideleOfPrime L 𝔓) = δ * ideleOfPrime K 𝔭` with `δ` equal
-- to `1` at every place except `𝔭`, where it is the unit `π_𝔓 / π_𝔭 ∈ 𝒪_𝔭ˣ`.  That unit is the
-- norm of some element of `L_𝔓ˣ` by `norm_units_surjective_of_ramificationIdx_eq_one` (`𝔭` is
-- unramified because it splits completely), so `δ ∈ N_{L/K} 𝕀 L ≤ U`, and likewise
-- `N(ideleOfPrime L 𝔓) ∈ U`.  Hence `ideleOfPrime K 𝔭 = δ⁻¹ N(ideleOfPrime L 𝔓) ∈ U ≤ Kˣ ⊔ U`,
-- which is the claim.  Note that no hypothesis `Kˣ ≤ U` is needed: the conclusion is a statement
-- about the subgroup generated by `Kˣ` and `U`.
--
-- The proof below uses the sharper formulation of the same computation
-- (`ideleOfPrime_mem_normImage_of_splitsCompletely`): a completely split prime is a norm, i.e.
-- `ideleOfPrime K 𝔭 ∈ N_{L/K} 𝕀 L`, so it lies in `U` as soon as `N_{L/K} 𝕀 L ≤ U`.
theorem primeClass_eq_one_of_splitsCompletely_of_le {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Subgroup (NK.GlobalCFT.Idele K)} (hU : NK.GlobalCFT.Idele.normImage K L ≤ U)
    (𝔭 : PrimeIdeal K)
    (h𝔭 : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L) :
    NK.HeckeL.primeClass K U 𝔭 = 1 := by
  classical
  have hmem : NK.HeckeL.ideleOfPrime K 𝔭 ∈ NK.GlobalCFT.Idele.normImage K L :=
    ideleOfPrime_mem_normImage_of_splitsCompletely (K := K) (L := L) 𝔭 h𝔭
  have hmemU : NK.HeckeL.ideleOfPrime K 𝔭 ∈ U := hU hmem
  have hEp : NK.HeckeL.ideleOfPrime K 𝔭 = NK.HeckeL.ideleOfIdeal K 𝔭.asIdeal :=
    ideleOfPrime_eq_ideleOfIdeal 𝔭
  rw [NK.HeckeL.primeClass, NK.HeckeL.classOfIdeal, ← hEp]
  rw [NK.GlobalCFT.IdeleClassGroup.rayClassGroupMk, NK.GlobalCFT.IdeleClassGroup.mk,
    QuotientGroup.map_mk']
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_sup.mpr
    ⟨1, Subgroup.one_mem _, NK.HeckeL.ideleOfPrime K 𝔭, hmemU, by rw [MonoidHom.id_apply, one_mul]⟩

end NK.GlobalCFTdeep.SecondInequality
