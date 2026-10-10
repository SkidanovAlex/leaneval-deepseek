import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Submission.Work.SSGRoute.ZDataMup.CycleAux
import Submission.Work.SSGRoute.ZDataMup.CycleIdele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence-`1` criterion for idèlic norms at a cycle (ideal modulus)

The `ℕ`-modulus statement `NK.CFTLib.ArtinReciprocityIdeal.mem_normImage_of_congruence_mul_norm`
(`Submission/NK/CFTLib/ArtinReciprocityIdeal/langCyclicRelIndex_proved.lean`) says: an idèle `z`
of `K` with trivial ideal whose product with an idèlic norm `N_{L/K}(y)` is `≡ 1` modulo an
admissible modulus `m` at the primes dividing `(m)` and positive at the real places is itself an
idèlic norm.

The proof only ever refers to a modulus through the *set of primes* at which the congruence is
imposed.  This module carries the statement over to the *cycles* (ideal moduli)
`Work.SSGRoute.ZDataMup.Cycle` of `CycleDefs.lean`, which is the form needed when the modulus must
be supported exactly on the ramified primes (the support of `(m)` is always saturated above the
rational primes, so no `ℕ`-modulus can have support exactly the ramified primes).

The only changes with respect to the `ℕ`-modulus proof are:

* the congruence branch is taken at the primes `𝔭 ∈ c.supp` instead of the primes `(m) ∈ 𝔭`, and
  the bound `c.level 𝔭 = exp (-(max 1 (c.lev 𝔭)))` of `Cycle.CongrAt` is upgraded to the bound
  `exp (-(c.lev 𝔭))` used by `Cycle.IsAdmissible` (`Cycle.level_le_exp_neg_lev_cmn`);
* the unramified branch is taken at the primes `𝔭 ∉ c.supp`, which are unramified by `hram`.

The local verification is the standard one
(`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`): at `𝔭 ∈ c.supp` the congruence together with
admissibility exhibits the local component as a local norm, at `𝔭 ∉ c.supp` the extension is
unramified and `z` is a local unit (it has trivial ideal), so again the local component is a local
norm, and at the archimedean places positivity supplies a local norm.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT

/-- **The level of a cycle is at most the unfloored exponential level.**  The level of a cycle is
floored at `1` (`Cycle.level`), so `c.level 𝔭 = exp (-(max 1 (c.lev 𝔭)))`; since
`c.lev 𝔭 ≤ max 1 (c.lev 𝔭)` this is at most `exp (-(c.lev 𝔭))`, the bound appearing in
`Cycle.IsAdmissible`. -/
theorem Cycle.level_le_exp_neg_lev_cmn {K : Type} [Field K] [NumberField K] (c : Cycle K)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    c.level 𝔭 ≤ (WithZero.exp (-(((c.lev 𝔭 : ℕ) : ℤ))) : WithZero (Multiplicative ℤ)) := by
  rw [Cycle.level, WithZero.exp_le_exp]
  have h : ((c.lev 𝔭 : ℕ) : ℤ) ≤ (((max 1 (c.lev 𝔭) : ℕ) : ℤ)) := by
    exact_mod_cast le_max_right 1 (c.lev 𝔭)
  omega

/-- `normIdeleFun` is multiplicative in the idèle. -/
lemma normIdeleFun_mul_cmn {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (y₁ y₂ : Idele L) (v : Place K) :
    Idele.normIdeleFun K L (y₁ * y₂) v =
      Idele.normIdeleFun K L y₁ v * Idele.normIdeleFun K L y₂ v := by
  rw [← Idele.normIdeleHom_apply, map_mul, Idele.mul_apply, Idele.normIdeleHom_apply,
    Idele.normIdeleHom_apply]

/-- **The congruence-`1` criterion at a cycle**: an idèle `z` of `K` with trivial ideal whose
product with an idèlic norm `N_{L/K}(y)` is `≡ 1` modulo the cycle `c` at the primes of `c` and
positive at the real places is itself an idèlic norm, provided `c` contains every ramified prime of
`L/K` (in the form `hram`) and is admissible.

For the cycle supported exactly on the ramified primes this is the input of the idèle–ideal
dictionary of the conductor drop, and it is the cycle-analogue of
`NK.CFTLib.ArtinReciprocityIdeal.mem_normImage_of_congruence_mul_norm`. -/
theorem cycleMemNormImageOfCongr
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (c : Work.SSGRoute.ZDataMup.Cycle K)
    (hpos : ∀ 𝔭 ∈ c.supp, 0 < c.lev 𝔭)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p → p ∈ c.supp)
    (hadm : Work.SSGRoute.ZDataMup.Cycle.IsAdmissible K L c)
    (z : NK.GlobalCFT.Idele K) (y : NK.GlobalCFT.Idele L)
    (hz : z.idealOf = 1)
    (hcong : ∀ 𝔭 ∈ c.supp,
      c.CongrAt 𝔭 (z (NK.GlobalCFT.Place.ofFinite 𝔭) *
        NK.GlobalCFT.Idele.normIdeleFun K L y (NK.GlobalCFT.Place.ofFinite 𝔭)))
    (hposarch : ∀ w : NumberField.InfinitePlace K,
      NK.CFTLib.Arl.PosAtReal w (z (NK.GlobalCFT.Place.ofInfinite w) *
        NK.GlobalCFT.Idele.normIdeleFun K L y (NK.GlobalCFT.Place.ofInfinite w))) :
    z ∈ NK.GlobalCFT.Idele.normImage K L := by
  classical
  -- it suffices to be a local norm at every place
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm (K := K) (L := L) z]
  intro v
  rcases v with v | Q
  · -- the archimedean case
    obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace L, w.comap (algebraMap K L) = v :=
      NumberField.InfinitePlace.comap_surjective v
    have hwl : w.LiesOver v := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v).mpr hw
    haveI : w.LiesOver v := hwl
    have hdef : Place.localNormInfinite w v
        = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) := rfl
    have hmem : z (Place.ofInfinite v) * Idele.normIdeleFun K L y (Place.ofInfinite v) ∈
        (Place.localNormInfinite w v).range := by
      rw [hdef]
      rcases v.isReal_or_isComplex with hvR | hvC
      · rcases w.isReal_or_isComplex with hwR | hwC
        · rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hvR hwR]
          exact Subgroup.mem_top _
        · refine NK.GlobalCFTdeep.NormIndex.localNormInfinite_posSubgroup_le_range_of_real_complex
            hvR hwC ?_
          rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
          exact hposarch v hvR
      · have hwC : w.IsComplex :=
          NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
        rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
        exact Subgroup.mem_top _
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
      (Place.ofInfinite w) u * y⁻¹, ?_⟩
    have h1 : Idele.normIdeleFun K L
          (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofInfinite w) u *
            y⁻¹)
          (Place.ofInfinite v)
        = Place.localNormInfinite w v u * (Idele.normIdeleFun K L y (Place.ofInfinite v))⁻¹ := by
      rw [normIdeleFun_mul_cmn, Idele.normIdeleFun_inv_apply,
        NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite v w u]
    rw [h1, hu]
    group
  · -- the nonarchimedean case
    obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    by_cases hQ : Q ∈ c.supp
    · -- `Q` is a prime of the cycle: the congruence and admissibility give the local norm
      obtain ⟨u, hu⟩ := hadm Q hQ q hq
        (z (Place.ofFinite Q) * Idele.normIdeleFun K L y (Place.ofFinite Q))
        (le_trans (hcong Q hQ) (Cycle.level_le_exp_neg_lev_cmn c Q))
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofFinite q) u * y⁻¹, ?_⟩
      have h1 : Idele.normIdeleFun K L
            (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite q) u *
              y⁻¹)
            (Place.ofFinite Q)
          = Place.localNormFinite q Q hq u * (Idele.normIdeleFun K L y (Place.ofFinite Q))⁻¹ := by
        rw [normIdeleFun_mul_cmn, Idele.normIdeleFun_inv_apply,
          NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u]
      rw [h1, hu]
      group
    · -- `Q ∉ c.supp`: the extension is unramified at `Q` and `z` is a local unit there
      have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q := by
        by_contra h
        exact hQ (hram Q h)
      have hzQ : z (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q) :=
        Idele.mem_integralIdeles.mp ((Idele.idealOf_eq_one_iff z).mp hz) (Place.ofFinite Q)
          (Place.isFinite_ofFinite Q)
      obtain ⟨u, -, hu⟩ :=
        NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q q hq (hunr q hq) (z (Place.ofFinite Q)) hzQ
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofFinite q) u, ?_⟩
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u,
        hu]

end Work.SSGRoute.ZDataMup
