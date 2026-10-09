import Mathlib
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range
import Submission.NeukirchUchida.Local.LocalGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

open NumberField IsDedekindDomain

namespace Work.SSGRoute.ZConstruction

/-- **A local `p`-th power is a local norm.**  For a finite Galois extension `L/K` of number
fields whose Galois group has `p` elements, and any place `v` of `K`, every `p`-th power in the
local field `K_v` lies in the local norm subgroup `N(L_w/K_v)` of the level at `v`.

Mathematical content (this is *not* a rewriting step): `localNormSubgroup` is the `iSup`, over the
places `w | v`, of the images of the norm maps `(localField L w)ˣ →* (localField K v)ˣ`, so one must
exhibit the place `w` and an element mapping to `γ^p`.  The local degree `f = [L_w : K_v]` is the
order of the decomposition group of `w`, hence divides `|Gal(L/K)| = p`, so `f ∈ {1, p}`.  View
`γ ∈ K_v^×` inside `L_w` (which contains `K_v`): if `f = p` then `N_{L_w/K_v}(γ) = γ^p`
(`Algebra.norm_algebraMap`), and if `f = 1` the local extension is trivial, so the norm is the
identity and `γ^p = N(γ^p)`.  Either way `γ^p` is a norm.  Scripts for the two inputs are named in
the reviews of this request: `Algebra.norm_algebraMap` for the norm of a base element, and the
finrank-equals-decomposition-group-order statement in
`Submission/NeukirchUchida/Local/LocalGalois.lean`.

This is the remaining ingredient of step (b) of the wiring plan of
`ZConstruction/auxPairingGate_odd`.  Together with
`Work.SSGRoute.ZConstruction.localImageAt_mem_powRange_of_localPowClass_eq_one`,
`NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff` and the kills-norms clause of
`ZConstruction.exists_abelianArtin_localFactors` it closes the coherence-to-equality step. -/
theorem mem_localNormSubgroup_of_mem_powRange {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (hcard : Nat.card (L ≃ₐ[K] L) = p) (v : NK.GlobalCFT.Place K)
    (a : (NK.GlobalCFT.Place.localField K v)ˣ)
    (ha : a ∈ (powMonoidHom p :
      (NK.GlobalCFT.Place.localField K v)ˣ →* (NK.GlobalCFT.Place.localField K v)ˣ).range) :
    a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
  classical
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp ha
  rw [powMonoidHom_apply] at hγ
  rcases v with w | Q
  · -- ## The archimedean case
    rcases w.isReal_or_isComplex with hwR | hwC
    · -- `w` real
      obtain ⟨w', hw'⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) w
      haveI : w'.LiesOver w := hw'
      rcases w'.isReal_or_isComplex with hw'R | hw'C
      · -- `w'` real: the local norm is surjective
        rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (v := w) (w₀ := w')
          (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real
            (K := K) (L := L) hwR hw'R)]
        exact Subgroup.mem_top a
      · -- `w'` complex over the real place `w`: the extension has even degree, so `p = 2`
        have hram : ¬ NumberField.InfinitePlace.IsUnramified K w' := by
          rw [NumberField.InfinitePlace.isUnramified_iff]
          push_neg
          exact ⟨NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw'C,
            by rw [NumberField.InfinitePlace.LiesOver.comap_eq w' w]
               exact NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr hwR⟩
        have hstab : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w') = 2 :=
          (NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two).mp hram
        have hp2 : p = 2 := by
          have hdvd : 2 ∣ p := by
            rw [← hcard, ← hstab]
            exact Subgroup.card_subgroup_dvd_card _
          exact (Nat.Prime.dvd_iff_eq (Fact.out : p.Prime) (by norm_num)).mp hdvd
        rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap
          (K := K) (L := L) hw' hwR hw'C]
        rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
        set ρ := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hwR with hρdef
        have hne : ρ (γ : w.Completion) ≠ 0 :=
          fun h => Units.ne_zero γ (ρ.injective (by rw [h, map_zero]))
        have hval : (a : w.Completion) = (γ : w.Completion) ^ 2 := by
          rw [← hγ, hp2, Units.val_pow_eq_pow_val]
        show 0 < ρ (a : w.Completion)
        rw [hval, map_pow]
        exact pow_two_pos_of_ne_zero hne
    · -- `w` complex: every place above is complex, so the local norm is surjective
      obtain ⟨w', hw'⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) w
      haveI : w'.LiesOver w := hw'
      have hw'C : w'.IsComplex :=
        NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w' hwC
      rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (v := w) (w₀ := w')
        (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
          (K := K) (L := L) hwC hw'C)]
      exact Subgroup.mem_top a
  · -- ## The nonarchimedean case
    obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    have hmem : a ∈ (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
      rw [MonoidHom.mem_range]
      letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
      haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
        Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
      haveI : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
        Module.Free.of_divisionRing _ _
      -- the local degree `d = [L_q : K_Q]` is the order of the decomposition group,
      -- hence divides `p = |Gal(L/K)|`
      set d : ℕ := Module.finrank (Q.adicCompletion K) (q.adicCompletion L) with hddef
      have hd_eq : d =
          Nat.card (Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) q) := by
        rw [hddef]
        exact (Submission.NeukirchUchida.Local.finrank_adicCompletion_eq_ef' Q q hq).trans
          (Submission.NeukirchUchida.Local.card_decompositionSubgroup Q q hq).symm
      have hdvd : d ∣ p := by
        rw [hd_eq, ← hcard]
        exact Subgroup.card_subgroup_dvd_card _
      have hdiv : p / d * d = p := Nat.div_mul_cancel hdvd
      -- `γ^{p/d}`, viewed in `L_q`, is a preimage of `γ^p`
      set x : (Q.adicCompletion K)ˣ := γ ^ (p / d) with hxdef
      have hxa : x ^ d = a := by rw [hxdef, ← pow_mul, hdiv, hγ]
      refine ⟨Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) x, ?_⟩
      have hlf : NK.GlobalCFT.Place.localNormFinite q Q hq
          = Units.map (Algebra.norm (Q.adicCompletion K)) := rfl
      rw [hlf]
      apply Units.ext
      rw [Units.coe_map, Units.coe_map]
      change (Algebra.norm (Q.adicCompletion K))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (x : Q.adicCompletion K))
        = (a : Q.adicCompletion K)
      rw [Algebra.norm_algebraMap, ← hddef, ← Units.val_pow_eq_pow_val, hxa]
    rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
    exact Subgroup.mem_iSup_of_mem
      (S := fun q : {q : HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver Q.asIdeal} =>
        (NK.GlobalCFT.Place.localNormFinite q.1 Q q.2).range) ⟨q, hq⟩ hmem

end Work.SSGRoute.ZConstruction
