import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.CFTLib.integralIdelesLeNormImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Congruence-`1` integral idèles are norms

The target of this file is `NK.CFTLib.ArtinReciprocityIdeal.integral_congr_pos_mem_normImage`:
for a finite cyclic Galois extension `L / K` of number fields, an idèle `u` of `K` which is

* a local unit at every finite place (`u ∈ 𝕀_K^{int}`),
* congruent to `1` modulo a modulus `m` at every finite place dividing `(m)`,
* positive at every real place,

and where `m` is an *admissible* modulus (Lang's condition: the congruence units of level `m` are
local norms) and `m` kills all ramification (every ramified prime divides `(m)`), is a norm of an
idèle of `L`.

The proof is the local–global principle for norms of idèles
(`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`, which supplies the passage from "locally a
norm at every place" to "a norm"), together with the local verification at each place `v` of `K`:

* at a finite place `Q` with `(m) ∉ Q`, the hypothesis `hram` forces `L / K` to be unramified at
  `Q`, so `u Q` is a local unit and hence the norm of a local unit
  (`KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one`);
* at a finite place `Q` with `(m) ∈ Q`, the congruence hypothesis `hcongr` together with
  admissibility `hadm` exhibits `u Q` as a local norm directly;
* at an archimedean place `v`, positivity `hpos` gives a local norm: either the local extension is
  `ℝ ⊆ ℝ` or `ℂ ⊆ ℂ` (where the norm on units is onto), or `v` is real and `w` is complex, where
  the norm is onto the positive units (`localNormInfinite_posSubgroup_le_range_of_real_complex`).

Each local preimage is packaged as a single-place idèle
(`KummerCase.singleIdele`), whose norm is computed by
`KummerCase.normIdeleFun_singleIdele_ofFinite` / `..._ofInfinite`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField.LiesOver
open NK.GlobalCFT

namespace NK.CFTLib.ArtinReciprocityIdeal

theorem integral_congr_pos_mem_normImage (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) (u : NK.GlobalCFT.Idele K)
    (hint : u ∈ NK.GlobalCFT.Idele.integralIdeles K)
    (hcongr : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
      Valued.v ((u (NK.GlobalCFT.Place.ofFinite 𝔭) : 𝔭.adicCompletion K) - 1) ≤
        Valued.v (((m : ℕ) : 𝔭.adicCompletion K)))
    (hpos : ∀ w : NumberField.InfinitePlace K,
      NK.CFTLib.Arl.PosAtReal w (u (NK.GlobalCFT.Place.ofInfinite w))) :
    u ∈ NK.GlobalCFT.Idele.normImage K L := by
  classical
  -- the local–global principle: it suffices to be a local norm at every place
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm (K := K) (L := L) u]
  intro v
  rcases v with v | Q
  · -- the archimedean case
    obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace L, w.comap (algebraMap K L) = v :=
      NumberField.InfinitePlace.comap_surjective v
    have hwl : w.LiesOver v := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v).mpr hw
    haveI : w.LiesOver v := hwl
    have hdef : NK.GlobalCFT.Place.localNormInfinite w v
        = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) := rfl
    have hmem : u (NK.GlobalCFT.Place.ofInfinite v) ∈
        (NK.GlobalCFT.Place.localNormInfinite w v).range := by
      rw [hdef]
      rcases v.isReal_or_isComplex with hvR | hvC
      · rcases w.isReal_or_isComplex with hwR | hwC
        · -- both places real: the local norm is onto
          rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hvR hwR]
          exact Subgroup.mem_top _
        · -- `v` real, `w` complex: the local norm is onto the positive units
          refine NK.GlobalCFTdeep.NormIndex.localNormInfinite_posSubgroup_le_range_of_real_complex
            hvR hwC ?_
          rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
          exact hpos v hvR
      · -- `v` complex: `w` is complex too and the local norm is onto
        have hwC : w.IsComplex :=
          NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
        rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
        exact Subgroup.mem_top _
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
      (NK.GlobalCFT.Place.ofInfinite w) y, ?_⟩
    rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite v w y]
    exact hy.symm
  · -- the nonarchimedean case
    obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    have hmem : u (NK.GlobalCFT.Place.ofFinite Q) ∈
        (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
      by_cases hmQ : (m : NumberField.RingOfIntegers K) ∈ Q.asIdeal
      · -- `Q` divides `(m)`: the congruence condition and admissibility give the local norm
        exact hadm Q hmQ q hq (u (NK.GlobalCFT.Place.ofFinite Q)) (hcongr Q hmQ)
      · -- `Q` does not divide `(m)`: the extension is unramified at `Q`, so units are norms
        have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q := by
          by_contra h
          exact hmQ (hram Q h)
        obtain ⟨y, -, hy⟩ :=
          NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
            Q q hq (hunr q hq) (u (NK.GlobalCFT.Place.ofFinite Q))
            (NK.GlobalCFT.Idele.mem_integralIdeles.mp hint (NK.GlobalCFT.Place.ofFinite Q)
              (NK.GlobalCFT.Place.isFinite_ofFinite Q))
        exact ⟨y, hy⟩
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
      (NK.GlobalCFT.Place.ofFinite q) y, ?_⟩
    rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq y]
    exact hy.symm

end NK.CFTLib.ArtinReciprocityIdeal
