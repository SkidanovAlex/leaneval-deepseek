import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.Existence.hilbertReciprocityInputs
import Submission.NK.KC.localGaloisPackageAux
import Submission.NK.LocalReciprocity.NormLimitationAdic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local base-change input from the local reciprocity law, at an unramified place

Target: `NK.CFTLib.Existence.LocalBaseChangeInput`.

After fixing the place `q | w` of `E`, the statement is the local-field assertion
`K_Qˣ ⊆ N_{E_q/M_w}(E_qˣ)` for `F = K_Q`, `F' = M_w` and `E' = E_q`.  The proof compares
the norm group `N_{E'/F'}` with the preimage `N_{F'/F}⁻¹(N_{E'/F})` (they have the same index
in `F'ˣ`, the first by the index theorem at `E'/F'`, the second by the tower formula and the
index theorems at `F'/F` and `E'/F`), and checks `Fˣ ⊆ N_{F'/F}⁻¹(N_{E'/F})` using that
`Fˣ / N_{E'/F} ≅ Gal(E'/F)` has exponent dividing `[F':F]` (`hloc`, `hunr`, `hcycL`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain

noncomputable section

namespace NK.KC

open NK.LocalReciprocity

theorem localBaseChange_aux
    {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M] [Algebra K E]
    [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1)
    (hloc : ∀ (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
              (hr : r.asIdeal.LiesOver Q.asIdeal),
      Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣
        Module.finrank (Q.adicCompletion K) (w.adicCompletion M)) :
    ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
      (hq : q.asIdeal.LiesOver w.asIdeal),
      ∀ x : Kˣ, Units.map (algebraMap M (w.adicCompletion M)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
        (NK.GlobalCFT.Place.localNormFinite q w hq).range := by
  classical
  haveI hgalME : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  haveI hfdME : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := M) (L := E) w
  haveI hQ : q.asIdeal.LiesOver Q.asIdeal := Ideal.LiesOver.trans q.asIdeal w.asIdeal Q.asIdeal
  refine ⟨q, hq, ?_⟩
  obtain ⟨hcommF, hcommF', hexp⟩ := localGaloisPackage_mine hgen hcycL Q w hw hunr hloc q hq hQ
  -- ### the scalar tower `K_Q → M_w → E_q`
  haveI hST : IsScalarTower (Q.adicCompletion K) (w.adicCompletion M) (q.adicCompletion E) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply,
        Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q w q hw hq hQ])
  -- ### finiteness and Galois-ness of the local extensions
  haveI hfdE : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hQ
  haveI hgalE : IsGalois (Q.adicCompletion K) (q.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hQ
  haveI hfdF : FiniteDimensional (Q.adicCompletion K) (w.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q w hw
  haveI hgalF : IsGalois (Q.adicCompletion K) (w.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q w hw
  haveI hfdE' : FiniteDimensional (w.adicCompletion M) (q.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion w q hq
  haveI hgalE' : IsGalois (w.adicCompletion M) (q.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion w q hq
  -- ### the index theorems
  have hidxE : (normGroup (Q.adicCompletion K) (q.adicCompletion E)).index =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion E) :=
    NK.LocalReciprocity.index_normGroup_eq_finrank Q q (hcomm := hcommF)
  have hunr' : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
    rw [ramificationIdx_eq_ramificationIdxIn Q w hw, hunr]
  have hcyclF : IsCyclic (w.adicCompletion M ≃ₐ[Q.adicCompletion K] w.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
      Q w hw hunr'
  have hidxF : (normGroup (Q.adicCompletion K) (w.adicCompletion M)).index =
      Module.finrank (Q.adicCompletion K) (w.adicCompletion M) :=
    NK.LocalReciprocity.index_normGroup_eq_finrank Q w (hcomm := NK.Summary.NUV2.Tame.mul_comm_of_isCyclic hcyclF)
  have hidxE' : (normGroup (w.adicCompletion M) (q.adicCompletion E)).index =
      Module.finrank (w.adicCompletion M) (q.adicCompletion E) :=
    NK.LocalReciprocity.index_normGroup_eq_finrank w q (hcomm := hcommF')
  -- ### the Artin map at `E_q / K_Q` and the exponent step
  obtain ⟨Φ, hΦsurj, hΦker⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_artinMap_of_abelian_local Q hcommF
  have hpow : ∀ a : (Q.adicCompletion K)ˣ,
      a ^ Module.finrank (Q.adicCompletion K) (w.adicCompletion M) ∈
        normGroup (Q.adicCompletion K) (q.adicCompletion E) := by
    intro a
    have h1 : Φ a ^ Module.finrank (Q.adicCompletion K) (w.adicCompletion M) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact hexp (Φ a)
    have h2 : a ^ Module.finrank (Q.adicCompletion K) (w.adicCompletion M) ∈ MonoidHom.ker Φ := by
      rw [MonoidHom.mem_ker, map_pow, h1]
    rwa [hΦker] at h2
  -- ### the norm limitation identity
  have hleNE : normGroup (Q.adicCompletion K) (q.adicCompletion E) ≤
      normGroup (Q.adicCompletion K) (w.adicCompletion M) :=
    NK.LocalReciprocity.normGroup_le_of_tower
  have hle : normGroup (w.adicCompletion M) (q.adicCompletion E) ≤
      (normGroup (Q.adicCompletion K) (q.adicCompletion E)).comap
        (Units.map (Algebra.norm (Q.adicCompletion K) :
          (w.adicCompletion M) →* (Q.adicCompletion K))) := by
    intro y hy
    rw [Subgroup.mem_comap]
    rw [NK.LocalReciprocity.normGroup_trans (F := Q.adicCompletion K)
      (E := w.adicCompletion M) (M := q.adicCompletion E)]
    exact Subgroup.mem_map_of_mem _ hy
  haveI hfreeF : Module.Free (Q.adicCompletion K) (w.adicCompletion M) :=
    Module.Free.of_divisionRing _ _
  haveI hfreeE' : Module.Free (w.adicCompletion M) (q.adicCompletion E) :=
    Module.Free.of_divisionRing _ _
  have hrel : (normGroup (Q.adicCompletion K) (q.adicCompletion E)).relIndex
      (normGroup (Q.adicCompletion K) (w.adicCompletion M)) =
      (normGroup (w.adicCompletion M) (q.adicCompletion E)).index := by
    have hmul := Subgroup.relIndex_mul_index hleNE
    rw [hidxE, hidxF] at hmul
    have hfr := Module.finrank_mul_finrank (Q.adicCompletion K) (w.adicCompletion M)
      (q.adicCompletion E)
    have hpos : 0 < Module.finrank (Q.adicCompletion K) (w.adicCompletion M) :=
      Module.finrank_pos
    have h2 : (normGroup (Q.adicCompletion K) (q.adicCompletion E)).relIndex
        (normGroup (Q.adicCompletion K) (w.adicCompletion M)) *
        Module.finrank (Q.adicCompletion K) (w.adicCompletion M) =
        Module.finrank (w.adicCompletion M) (q.adicCompletion E) *
        Module.finrank (Q.adicCompletion K) (w.adicCompletion M) := by
      rw [hmul, ← hfr, mul_comm]
    rw [hidxE']
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hidxK' : ((normGroup (Q.adicCompletion K) (q.adicCompletion E)).comap
      (Units.map (Algebra.norm (Q.adicCompletion K) :
        (w.adicCompletion M) →* (Q.adicCompletion K)))).index =
      (normGroup (w.adicCompletion M) (q.adicCompletion E)).index := by
    rw [Subgroup.index_comap]
    have hrange : (Units.map (Algebra.norm (Q.adicCompletion K) :
        (w.adicCompletion M) →* (Q.adicCompletion K))).range =
        normGroup (Q.adicCompletion K) (w.adicCompletion M) := rfl
    rw [hrange, hrel]
  have hne : (normGroup (w.adicCompletion M) (q.adicCompletion E)).index ≠ 0 := by
    rw [hidxE']
    exact (Module.finrank_pos (R := w.adicCompletion M) (M := q.adicCompletion E)).ne'
  have heq : normGroup (w.adicCompletion M) (q.adicCompletion E) =
      (normGroup (Q.adicCompletion K) (q.adicCompletion E)).comap
        (Units.map (Algebra.norm (Q.adicCompletion K) :
          (w.adicCompletion M) →* (Q.adicCompletion K))) :=
    NK.LocalReciprocity.eq_of_le_of_index_eq_of_index_ne_zero hle hne hidxK'
  -- ### conclusion
  haveI hSTKF : IsScalarTower K (Q.adicCompletion K) (w.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion Q w hw
  intro x
  have htri : Units.map (algebraMap M (w.adicCompletion M)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) =
      Units.map (algebraMap (Q.adicCompletion K) (w.adicCompletion M)).toMonoidHom
        (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x) := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.coe_map, Units.coe_map, Units.coe_map]
    have h1 := RingHom.congr_fun (IsScalarTower.algebraMap_eq K M (w.adicCompletion M)) (x : K)
    have h2 := RingHom.congr_fun
      (IsScalarTower.algebraMap_eq K (Q.adicCompletion K) (w.adicCompletion M)) (x : K)
    simp only [RingHom.comp_apply] at h1 h2
    exact h1.symm.trans h2
  rw [htri]
  have hmem : Units.map (algebraMap (Q.adicCompletion K) (w.adicCompletion M)).toMonoidHom
      (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x) ∈
      normGroup (w.adicCompletion M) (q.adicCompletion E) := by
    rw [heq, Subgroup.mem_comap]
    have hnorm : Units.map (Algebra.norm (Q.adicCompletion K))
        (Units.map (algebraMap (Q.adicCompletion K) (w.adicCompletion M)).toMonoidHom
          (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x)) =
        (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x) ^
          Module.finrank (Q.adicCompletion K) (w.adicCompletion M) := by
      refine Units.ext ?_
      rw [Units.coe_map, Units.coe_map, Units.val_pow_eq_pow_val]
      exact Algebra.norm_algebraMap (R := Q.adicCompletion K) (S := w.adicCompletion M) _
    rw [hnorm]
    exact hpow _
  rwa [show (NK.GlobalCFT.Place.localNormFinite q w hq).range =
      normGroup (w.adicCompletion M) (q.adicCompletion E) from rfl]

/-- **The local base-change input** (Milne, *CFT*, III.3.5/III.3.6). -/
theorem localBaseChangeInput_of_kc : NK.CFTLib.Existence.LocalBaseChangeInput :=
  fun {K L M E} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgen hcycL Q w hw hunr hloc =>
    localBaseChange_aux hgen hcycL Q w hw hunr hloc

end NK.KC
