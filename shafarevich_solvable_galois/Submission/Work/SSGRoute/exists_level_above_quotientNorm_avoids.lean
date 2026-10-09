import Mathlib
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.exists_level_normGroup_not_mem_of_not_pthPower
import Submission.Work.SSGRoute.normImage_at_level_proper
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.phi1_level_naturality
import Submission.Work.SSGRoute.exists_level_local_embedding_fix
import Submission.Work.SSGRoute.norm_fail_of_local_embedding
import Submission.Work.SSGRoute.exists_level_above_quotientNorm_avoids_infinite
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localFixed_all
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
import Submission.NK.LocalCFT.Instance.normGroup_real_complex
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_realization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **Local fixed field of the decomposition group, in units.**  A unit `a` of `K_wˣ` fixed by
the whole decomposition group `D_w = decompK w` is the image of a unit of the base local field
`k_vˣ` under the canonical local map. -/
theorem localFixedUnits_eq_localAlgebraMapUnits (w : NK.GlobalCFT.Place K)
    (v : NK.GlobalCFT.Place k) (hv : NK.GlobalCFT.Place.LiesOver w v)
    (a : (NK.GlobalCFT.Place.localField K w)ˣ)
    (hafix : ∀ σ : decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a) :
    ∃ a₀ : (NK.GlobalCFT.Place.localField k v)ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits w v hv a₀ = a :=
  NK.GlobalCFT.Inclusion.globalCFT_localFixed_mem_range (K := k) (L := K) hv a
    ((localUnitsEquiv_fixed_iff_ringEquiv_fixed_general (k := k) (K := K) w a).mp hafix)

/-- The image of `k_vˣ` in `K_wˣ` is fixed by the decomposition group. -/
theorem localUnitsEquiv_localAlgebraMapUnits_eq_self (w : NK.GlobalCFT.Place K)
    (v : NK.GlobalCFT.Place k) (hv : NK.GlobalCFT.Place.LiesOver w v)
    (u : (NK.GlobalCFT.Place.localField k v)ˣ) (σ : decompK (k := k) w) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w σ
        (NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u)
      = NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u := by
  have h := NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower
    (F := k) (L := k) (M := K) hv σ u
  rw [← h]
  congr 1
  have hτ : (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := k) (L := k) (M := K) hv σ) = 1 :=
    Subsingleton.elim _ _
  rw [hτ, NK.HassePrinciple.localUnitsEquiv_one]
  rfl

end

/-- **Z5a (cone form of `Work.SSGRoute.exists_level_quotientNorm_avoids`).**  For
`a ∈ (K_wˣ)^{D_w}` that is not the `p`-th power of a `D_w`-fixed unit, and ANY level `L₀ ⊇ K`
with `w₀ ∣ w`, there are a level `L ⊇ L₀` (Galois over `k`), `w' ∣ w₀`, and `N ⊴ D_{w'}` of index
`p`, `D_{w'}/N` cyclic, such that the image of `a` in `L_{w'}ˣ` is not an `N`-relative norm.
Route (same as the base form, H390's plan): local CFT gives a cyclic degree-`p` `E/k_v` with
`a ∉ N(E)` (`Work.SSGRoute.exists_level_normGroup_not_mem_of_not_pthPower`); realise the compositum
`E·L₀,w₀` as a completion of a level containing `L₀` (Kummer generator + weak approximation +
Galois closure); norms from a bigger field lie in the norms from `E`. -/
theorem exists_level_above_quotientNorm_avoids
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (a : (NK.GlobalCFT.Place.localField K w)ˣ)
    (hafix : ∀ σ : decompK (k := k) w, NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a)
    (ha : ¬ ∃ b : (NK.GlobalCFT.Place.localField K w)ˣ,
      (∀ σ : decompK (k := k) w, NK.HassePrinciple.localUnitsEquiv (K := k) w σ b = b) ∧
        b ^ p = a)
    (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra k L₀] [Algebra K L₀] [IsScalarTower k K L₀]
    [FiniteDimensional k L₀] [IsGalois k L₀]
    (w₀ : NK.GlobalCFT.Place L₀) (hw₀ : NK.GlobalCFT.Place.LiesOver w₀ w) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra L₀ L)
      (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w₀)
      (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
      (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
      IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
          (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
            (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a))) := by
  classical
  rcases w with wK | qw
  · -- archimedean place
    exact exists_level_above_quotientNorm_avoids_infinite p k K (NK.GlobalCFT.Place.ofInfinite wK)
      (NK.GlobalCFT.Place.isInfinite_ofInfinite wK) a hafix ha L₀ w₀ hw₀
  · -- finite place
    rcases w₀ with w₀K | q₀
    · exact absurd ((NK.GlobalCFT.Place.isFinite_of_liesOver hw₀).mpr
        (NK.GlobalCFT.Place.isFinite_ofFinite qw)) (by simp)
    · -- the base place of `k` below `q₀`
      let Qk : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
        ⟨q₀.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
          Ideal.under_ne_bot _ q₀.ne_bot⟩
      have hq₀Q : q₀.asIdeal.LiesOver Qk.asIdeal := Ideal.over_under q₀.asIdeal
      have hq₀qw : q₀.asIdeal.LiesOver qw.asIdeal := by
        rcases (NK.GlobalCFT.Place.liesOver_iff _ _).mp hw₀ with h | ⟨q', Q', e1, e2, hL⟩
        · obtain ⟨w', v', e1, e2, hL⟩ := h
          exact absurd e1 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q₀).symm
        · rw [NK.GlobalCFT.Place.ofFinite_inj] at e1 e2
          rw [← e1, ← e2] at hL; exact hL
      have hqwQ : qw.asIdeal.LiesOver Qk.asIdeal := by
        haveI := hq₀qw
        have hQeq : Qk.asIdeal = qw.asIdeal.under (NumberField.RingOfIntegers k) := by
          change q₀.asIdeal.under (NumberField.RingOfIntegers k) = _
          rw [Ideal.LiesOver.over (A := NumberField.RingOfIntegers K) (P := q₀.asIdeal)
                (p := qw.asIdeal),
            Ideal.under_under (A := NumberField.RingOfIntegers k) q₀.asIdeal]
        rw [hQeq]
        exact Ideal.over_under qw.asIdeal
      obtain ⟨a₀, ha₀⟩ := localFixedUnits_eq_localAlgebraMapUnits k K
        (NK.GlobalCFT.Place.ofFinite qw) (NK.GlobalCFT.Place.ofFinite Qk)
        (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) a hafix
      have hnotpow : ∀ b : (Qk.adicCompletion k)ˣ, b ^ p ≠ a₀ := by
        intro b hb
        apply ha
        refine ⟨NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite qw)
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) b, ?_, ?_⟩
        · intro σ
          exact localUnitsEquiv_localAlgebraMapUnits_eq_self k K (NK.GlobalCFT.Place.ofFinite qw)
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) b σ
        · rw [← map_pow, hb, ha₀]
      obtain ⟨E, hEf, hEA, hEfd, hEgal, hEcard, hEnorm⟩ :=
        exists_level_normGroup_not_mem_of_not_pthPower Qk p a₀ hnotpow
      obtain ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, q', hq', hq'Q, hne⟩ :=
        exists_level_local_embedding_fix k L₀ q₀ Qk hq₀Q E
      letI : Field L := hLf
      letI : NumberField L := hLn
      letI : Algebra k L := hLk
      letI : Algebra L₀ L := hLL₀
      letI : IsScalarTower k L₀ L := hST
      letI : FiniteDimensional k L := hLfd
      letI : IsGalois k L := hLgal
      obtain ⟨N, hNnorm, hNfin, hcyc, hcard, hfail⟩ :=
        norm_fail_of_local_embedding p k L Qk q' hq'Q E hEcard hne a₀ hEnorm
      letI : N.Normal := hNnorm
      letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q') ⧸ N) := hNfin
      have hstep1 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
            (NK.GlobalCFT.Place.ofFinite qw) hw₀)
            (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite qw)
              (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) a₀)
          = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q) a₀ := by
        rw [← MonoidHom.comp_apply, localAlgebraMapUnits_comp (K := k) (L := K) (M := L₀)
            hw₀ (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ)
            (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q)]
      have hstep2 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
            (NK.GlobalCFT.Place.ofFinite q₀) (NK.GlobalCFT.Place.liesOver_ofFinite hq'))
            (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
              (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q) a₀)
          = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q) a₀ := by
        rw [← MonoidHom.comp_apply, localAlgebraMapUnits_comp (K := k) (L := L₀) (M := L)
            (NK.GlobalCFT.Place.liesOver_ofFinite hq')
            (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q)
            (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q)]
      have hkey : NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
            (NK.GlobalCFT.Place.ofFinite q₀) (NK.GlobalCFT.Place.liesOver_ofFinite hq')
            (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
              (NK.GlobalCFT.Place.ofFinite qw) hw₀ a)
          = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q) a₀ := by
        rw [← ha₀, hstep1, hstep2]
      exact ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, NK.GlobalCFT.Place.ofFinite q',
        NK.GlobalCFT.Place.liesOver_ofFinite hq', N, hNnorm, hNfin, hcyc, hcard, by
          rw [hkey]
          exact hfail⟩

end Work.SSGRoute
