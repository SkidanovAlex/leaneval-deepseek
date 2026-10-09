import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.flowKernel_fixedField
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.RamifiedPlacesAux
import Submission.Work.SSGRoute.ramifiedPlaces_finite
import Submission.Work.SSGRoute.exists_T0_split_generating_disj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The data part of the coker side of Step 4, from level-`m` stage-3 data

This module proves `Work.SSGRoute.step4_coker_data_of_level_data`: from a level-`m` proper
stage-3 datum `(φm, ψm)` (`hdata : IsProperStageData p K m i j φm ψm`) together with a surjective
operator map `Φ : F(m) ⇢ F(n)` (to a level `n ≤ m`), one obtains a full
`Work.SSGRoute.Step4CokerData p K n i j` whose level is `m`, whose operator map is `Φ`, and whose
level-`m` maps are `φm`, `ψm`; consequently its level-`n` stage-`τ+1` map `D.psi` is the push-down
`(flowGroupMap p (K ≃ₐ[ℚ] K) τ₁ τ₂ Φ) ∘ ψm`.

Concretely, with `ψn := (flowGroupMap Φ) ∘ ψm` (a level-`n` flow solution, because `ψm` is one)
and `φn := (flowGroupMap Φ) ∘ φm` (its projection):

* `Λ` is the field cut out by `ψn.ker` (`Work.SSGRoute.flowKernel_fixedField`, run at the stage
  `(τ+1) = (tauSucc i j)`), so that `ψn.ker = Λ.fixingSubgroup`;
* `T⁰` is the Chebotarev set of `Work.SSGRoute.exists_T0_split_generating_disj`: its places are
  finite, pairwise non-conjugate, killed on decomposition groups by `φn`, *unramified* for `ψn`
  (`IsInertia ℚ A σ → ψn σ = 1`) and their `ψn`-images generate `flowEKer p (K ≃ₐ[ℚ] K) n i j`
  and are cyclic;
* `S` is the union of `T⁰` with the places over `Ram(Λ) ∪ {p}` that are not conjugate to a
  `T⁰`-place (`Work.SSGRoute.ramifiedPlaces_finite`): `S` covers `Ram(Λ) ∪ {p}`, has no
  superfluous element, contains `T⁰`, and has one place per prime;
* `sec` is a section of `Gal(ℚ̄/ℚ) → Gal(K/ℚ)`.

The bookkeeping is the union `S = T⁰ ∪ …`: conjugation invariance of the predicate "ramified in `Λ`
or over `p`" (`relevant_conj_iff_aux`) keeps the coverage of `S` (`hSram`), while the finiteness,
the pairwise non-conjugacy and the "no superfluous element" clauses are inherited by the two parts
and hold across the union because the elements of `Sram` that are conjugate to a `T⁰`-place are
dropped (their places are already accounted for by `T⁰`).
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-! ## Two auxiliary surjectivity/lifting facts for the rank change

`Work.SSGRoute.step4_coker_data_of_level_data` is stated purely in terms of the level-`m` data and
the operator map `Φ`, so the level-`n` flow solution `ψn = (flowGroupMap Φ) ∘ ψm` and its
projection `φn` are built here; the two facts below (the rank change is surjective, and it carries
lifts to lifts) are the standard ones. -/

private theorem flowQuotMap_surjective_aux (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (i j : ℕ)
    (Φ : OperatorMap G m n) : Function.Surjective (flowQuotMap p G i j Φ) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨z, hz⟩ := Φ.surjective x.1
    refine ⟨QuotientGroup.mk' _ ⟨z, Subgroup.mem_top z⟩, ?_⟩
    rw [flowQuotMap_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hz)

private theorem flowGroupMap_surjective_aux (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (i j : ℕ)
    (Φ : OperatorMap G m n) : Function.Surjective (flowGroupMap p G i j Φ) := by
  intro γ
  obtain ⟨x, hx⟩ := flowQuotMap_surjective_aux p G i j Φ γ.left
  have key : flowGroupMap p G i j Φ (SemidirectProduct.mk x γ.right)
      = SemidirectProduct.mk ((flowQuotMap p G i j Φ) x) γ.right := by
    rw [flowGroupMap]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.map_left]
    · rw [SemidirectProduct.map_right]; rfl
  exact ⟨SemidirectProduct.mk x γ.right, by rw [key, hx]⟩

private theorem flowGroupMap_comp_liftsFlow_aux (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (h : SSGRoute.LiftsFlow ψm φm) :
    SSGRoute.LiftsFlow ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)
      ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm) := by
  intro σ
  obtain ⟨hright, z, hz1, hz2⟩ := h σ
  refine ⟨?_, ⟨Φ.toHom z.1, Subgroup.mem_top _⟩, ?_, ?_⟩
  · show ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) (ψm σ)).right
      = ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φm σ)).right
    rw [flowGroupMap, SemidirectProduct.map_right, flowGroupMap, SemidirectProduct.map_right,
      MonoidHom.id_apply, MonoidHom.id_apply]
    exact hright
  · show ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) (ψm σ)).left
      = (QuotientGroup.mk' _ ⟨Φ.toHom z.1, Subgroup.mem_top _⟩ :
          flowQuotient p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    rw [flowGroupMap, SemidirectProduct.map_left]
    rw [show (ψm σ).left = QuotientGroup.mk' _ z from hz1]
    rw [flowQuotMap_mk]
  · show ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φm σ)).left
      = (QuotientGroup.mk' _ ⟨Φ.toHom z.1, Subgroup.mem_top _⟩ :
          flowQuotient p (K ≃ₐ[ℚ] K) n i j)
    rw [flowGroupMap, SemidirectProduct.map_left]
    rw [show (φm σ).left = QuotientGroup.mk' _ z from hz2]
    rw [flowQuotMap_mk]

private theorem val_p_smul_iff (p : ℕ) (A : ValuationSubring SSGRoute.QBar)
    (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) :
    (g • A).valuation (p : SSGRoute.QBar) < 1 ↔ A.valuation (p : SSGRoute.QBar) < 1 := by
  have hcast : (algebraMap ℚ SSGRoute.QBar p) = (p : SSGRoute.QBar) := by simp
  have h1 := Work.SSGRoute.comap_valuation_lt_one_iff (K := ℚ) (L := SSGRoute.QBar) (g • A) p
  rw [Work.SSGRoute.comap_algebraMap_smul A g] at h1
  rw [hcast] at h1
  have h2 := Work.SSGRoute.comap_valuation_lt_one_iff (K := ℚ) (L := SSGRoute.QBar) A p
  rw [hcast] at h2
  exact h1.symm.trans h2

private theorem relevant_smul_iff (p : ℕ) (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ] [IsGalois ℚ Λ] (A : ValuationSubring SSGRoute.QBar)
    (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) :
    (SSGRoute.IsRamifiedIn ℚ Λ (g • A) ∨ (g • A).valuation (p : SSGRoute.QBar) < 1) ↔
    (SSGRoute.IsRamifiedIn ℚ Λ A ∨ A.valuation (p : SSGRoute.QBar) < 1) := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : IsGalois ℚ SSGRoute.QBar := { to_isSeparable := inferInstance, to_normal := inferInstance }
  exact or_congr
    (Work.SSGRoute.isRamifiedIn_conj Λ (IsGalois.fixingSubgroup_normal_of_isGalois Λ) A g)
    (val_p_smul_iff p A g)

private theorem relevant_conj_iff_aux (p : ℕ) (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ] [IsGalois ℚ Λ] {A B : ValuationSubring SSGRoute.QBar}
    (h : SSGRoute.IsConjPlace ℚ A B) :
    (SSGRoute.IsRamifiedIn ℚ Λ A ∨ A.valuation (p : SSGRoute.QBar) < 1) ↔
    (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) := by
  obtain ⟨g, hg⟩ := h
  rw [← hg]
  exact (relevant_smul_iff p Λ A g).symm

theorem step4_coker_data_of_level_data (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (m : ℕ) (hm : 1 ≤ m) (hnm : n ≤ m)
    (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hdata : Work.SSGRoute.IsProperStageData p K m i j φm ψm) :
    ∃ D : Work.SSGRoute.Step4CokerData p K n i j, D.m = m ∧ HEq D.Φ Φ ∧ HEq D.φm φm ∧ HEq D.ψm ψm ∧
      HEq D.psi ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K)
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2 Φ).comp ψm) := by
  classical
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : IsGalois ℚ SSGRoute.QBar := { to_isSeparable := inferInstance, to_normal := inferInstance }
  let ψn : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
    (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm
  let φn : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm
  have hψm_surj : Function.Surjective ψm := hdata.2.2.1.1
  have hψm_open : IsOpen (ψm.ker : Set SSGRoute.GalQ) := hdata.2.2.1.2.1
  have hψm_quot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 (ψm σ) = Work.SSGRoute.restrict K σ :=
    hdata.2.2.1.2.2
  have hφm_quot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) m i j (φm σ) = Work.SSGRoute.restrict K σ :=
    hdata.1.1.2.2
  have hLift_m : SSGRoute.LiftsFlow ψm φm := hdata.2.1
  have hopen_n : IsOpen (ψn.ker : Set SSGRoute.GalQ) := by
    refine Subgroup.isOpen_mono ?_ hψm_open
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    show (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) (ψm σ) = 1
    rw [hσ, map_one]
  have hsurj_n : Function.Surjective ψn :=
    (flowGroupMap_surjective_aux p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp hψm_surj
  have hquot_n : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψn σ) = Work.SSGRoute.restrict K σ := by
    intro σ
    change flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
      ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) (ψm σ)) = Work.SSGRoute.restrict K σ
    rw [flowQuot_flowGroupMap]
    exact hψm_quot σ
  have hquot_φn : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φn σ) = Work.SSGRoute.restrict K σ := by
    intro σ
    change flowQuot p (K ≃ₐ[ℚ] K) n i j
      ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φm σ)) = Work.SSGRoute.restrict K σ
    rw [flowQuot_flowGroupMap]
    exact hφm_quot σ
  have hLift_n : SSGRoute.LiftsFlow ψn φn :=
    flowGroupMap_comp_liftsFlow_aux p K Φ ψm φm hLift_m
  obtain ⟨Λ, hΛfd, hΛgal, hKΛ, hΛfix, -, -⟩ :=
    Work.SSGRoute.flowKernel_fixedField p K n (tauSucc i j).1 (tauSucc i j).2 ψn hopen_n hsurj_n hquot_n
  have hΛker : ψn.ker = Λ.fixingSubgroup := Subgroup.ext (fun σ => (hΛfix σ).symm)
  haveI : FiniteDimensional ℚ Λ := hΛfd
  haveI : IsGalois ℚ Λ := hΛgal
  obtain ⟨T0, hT0fin, hT0φ1, hT0gen, hT0cyc, hT0inertia, hT0disj⟩ :=
    Work.SSGRoute.exists_T0_split_generating_disj p K n i j φn ψn hLift_n hopen_n hsurj_n
  obtain ⟨Sram, hSramfin, hSramdisj, hSramcov⟩ := Work.SSGRoute.ramifiedPlaces_finite p Λ
  have hsec_exists : ∃ sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ,
      ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s := by
    have hsurj_sec : Function.Surjective (AlgEquiv.restrictNormalHom K) :=
      AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) (E := SSGRoute.QBar)
    exact ⟨fun s => Classical.choose (hsurj_sec s), fun s => Classical.choose_spec (hsurj_sec s)⟩
  obtain ⟨sec, hsec⟩ := hsec_exists
  have hT0split : ∀ A ∈ T0, SSGRoute.IsSplitIn ℚ K A := by
    intro A hA σ hσ
    refine Work.SSGRoute.mem_fixingSubgroup_of_restrict_eq_one K ?_
    rw [← hquot_φn σ, hT0φ1 A hA σ hσ, map_one]
  let S : Finset (ValuationSubring SSGRoute.QBar) :=
    T0 ∪ Sram.filter (fun B => (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1)
      ∧ ∀ A ∈ T0, ¬ SSGRoute.IsConjPlace ℚ A B)
  have hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A := by
    intro A hA
    rw [show S = T0 ∪ Sram.filter _ from rfl, Finset.mem_union] at hA
    rcases hA with hA | hA
    · exact hT0fin A hA
    · exact hSramfin A (Finset.mem_filter.mp hA).1
  have hSmin : ∀ A ∈ S, A ∈ T0 ∨ SSGRoute.IsRamifiedIn ℚ Λ A ∨ A.valuation (p : SSGRoute.QBar) < 1 := by
    intro A hA
    rw [show S = T0 ∪ Sram.filter _ from rfl, Finset.mem_union] at hA
    rcases hA with hA | hA
    · exact Or.inl hA
    · exact Or.inr (Finset.mem_filter.mp hA).2.1
  have hT0S : ∀ A ∈ T0, A ∈ S := by
    intro A hA
    rw [show S = T0 ∪ Sram.filter _ from rfl]
    exact Finset.mem_union_left _ hA
  have hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ℚ A B → A = B := by
    intro A hA B hB hc
    rw [show S = T0 ∪ Sram.filter _ from rfl, Finset.mem_union] at hA hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hT0disj A hA B hB hc
    · exact absurd hc ((Finset.mem_filter.mp hB).2.2 A hA)
    · exact absurd (Work.SSGRoute.isConjPlace_symm hc) ((Finset.mem_filter.mp hA).2.2 B hB)
    · exact hSramdisj A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hc
  have hSram' : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B := by
    intro B hB hrel
    obtain ⟨A₀, hA₀mem, hA₀conj⟩ := hSramcov B hB hrel
    have hrelA₀ : SSGRoute.IsRamifiedIn ℚ Λ A₀ ∨ A₀.valuation (p : SSGRoute.QBar) < 1 :=
      (relevant_conj_iff_aux p Λ hA₀conj).mpr hrel
    by_cases hfree : ∀ A ∈ T0, ¬ SSGRoute.IsConjPlace ℚ A A₀
    · refine ⟨A₀, ?_, hA₀conj⟩
      rw [show S = T0 ∪ Sram.filter _ from rfl]
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA₀mem, hrelA₀, hfree⟩)
    · rw [not_forall] at hfree
      obtain ⟨A, hfree⟩ := hfree
      rw [Classical.not_imp] at hfree
      exact ⟨A, hT0S A hfree.1,
        Work.SSGRoute.isConjPlace_trans (Classical.not_not.mp hfree.2) hA₀conj⟩
  have hT0unram : ∀ A ∈ T0, ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → ψn σ = 1 := hT0inertia
  let D : Work.SSGRoute.Step4CokerData p K n i j :=
    { m := m, hm := hm, hnm := hnm, Φ := Φ, φm := φm, ψm := ψm, data := hdata
      Λ := Λ, fdΛ := hΛfd, galΛ := hΛgal, hKΛ := hKΛ, hΛker := hΛker
      S := S, T0 := T0, sec := sec, hSfin := hSfin, hSdisj := hSdisj, hSram := hSram'
      hSmin := hSmin, hsec := hsec, hT0S := hT0S, hT0split := hT0split, hT0unram := hT0unram
      hT0gen := hT0gen, hT0cyc := hT0cyc }
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl

end Work.SSGRoute
