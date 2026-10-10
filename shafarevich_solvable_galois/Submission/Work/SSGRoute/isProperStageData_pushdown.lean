import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.stage3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pushing Stage-3 data down along a shrinking map

If `(φm, ψm)` is stage-3 data at level `m` and `Φ : F(m) ⇢ F(n)` is a surjective `G`-operator
homomorphism, then the push-forwards `Φ_* φm`, `Φ_* ψm` are stage-3 data at level `n`: every
clause of `IsProperStageData` is inherited by the image.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open _root_.Work.CohomologicalShrinking

set_option maxHeartbeats 800000

/-! ## Elementary helpers (kept private to avoid clashing with sibling modules) -/

/-- The image of a cyclic subgroup under a homomorphism is cyclic. -/
private theorem isCyclic_map_of_isCyclic_aux {N P : Type*} [Group N] [Group P] (f : N →* P)
    (H : Subgroup N) (h : IsCyclic ↥H) : IsCyclic ↥(Subgroup.map f H) := by
  let F : ↥H →* ↥(Subgroup.map f H) :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.1 b.1) }
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective F hsurj

/-- `flowQuotMap` is surjective (it is induced by a surjective operator map). -/
private theorem flowQuotMap_surjective_aux {p : ℕ} {G : Type*} [Group G] {m n : ℕ}
    (i j : ℕ) (Φ : OperatorMap G m n) :
    Function.Surjective (flowQuotMap p G i j Φ) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨z, hz⟩ := Φ.surjective x.1
    refine ⟨(QuotientGroup.mk' _) ⟨z, Subgroup.mem_top z⟩, ?_⟩
    rw [flowQuotMap_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hz)

/-- `flowGroupMap` is surjective. -/
private theorem flowGroupMap_surjective_aux {p : ℕ} {G : Type*} [Group G] {m n : ℕ}
    (i j : ℕ) (Φ : OperatorMap G m n) :
    Function.Surjective (flowGroupMap p G i j Φ) := by
  intro γ
  obtain ⟨x, hx⟩ := flowQuotMap_surjective_aux (p := p) i j Φ γ.left
  have key : flowGroupMap p G i j Φ (SemidirectProduct.mk x γ.right)
      = SemidirectProduct.mk ((flowQuotMap p G i j Φ) x) γ.right := by
    rw [flowGroupMap]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.map_left]
    · rw [SemidirectProduct.map_right]; rfl
  exact ⟨SemidirectProduct.mk x γ.right, by rw [key, hx]⟩

/-- The left component of `flowGroupMap`. -/
private theorem flowGroupMap_left_aux {p : ℕ} {G : Type*} [Group G] {m n : ℕ}
    (i j : ℕ) (Φ : OperatorMap G m n) (γ : flowGroup p G m i j) :
    (flowGroupMap p G i j Φ γ).left = flowQuotMap p G i j Φ γ.left := rfl

/-- The right (`G`-)component of `flowGroupMap`. -/
private theorem flowGroupMap_right_aux {p : ℕ} {G : Type*} [Group G] {m n : ℕ}
    (i j : ℕ) (Φ : OperatorMap G m n) (γ : flowGroup p G m i j) :
    (flowGroupMap p G i j Φ γ).right = γ.right := rfl

/-- `flowQuotMap` on the class of a representative, in the form matching `LiftsFlowAt`. -/
private theorem flowQuotMap_mk_aux {p : ℕ} {G : Type*} [Group G] {m n : ℕ}
    (i j : ℕ) (Φ : OperatorMap G m n)
    (x : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotMap p G i j Φ (QuotientGroup.mk x : flowQuotient p G m i j)
      = (QuotientGroup.mk ⟨Φ.toHom x, Subgroup.mem_top _⟩ : flowQuotient p G n i j) := by
  simpa only [QuotientGroup.coe_mk'] using flowQuotMap_mk p G i j Φ x

/-- **Scholz solutions are stable under the rank change `F(m) ⇢ F(n)`.** -/
private theorem scholz_pushdown_aux (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ) :
    SSGRoute.IsScholzSolution p K n i j ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) := by
  obtain ⟨hflow, hsch⟩ := hφ
  obtain ⟨hsurj, hopen, hres⟩ := hflow
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (flowGroupMap_surjective_aux (p := p) i j Φ).comp hsurj
  · refine Subgroup.isOpen_mono ?_ hopen
    intro σ hσ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ ⊢
    rw [hσ, map_one]
  · intro σ
    rw [MonoidHom.comp_apply, flowQuot_flowGroupMap]
    exact hres σ
  · intro A hA σ hσ hσK
    rw [MonoidHom.comp_apply, hsch.1 A hA σ hσ hσK, map_one]
  · intro c hc hcK
    rw [MonoidHom.comp_apply, hsch.2.1 c hc hcK, map_one]
  · intro A hA h
    obtain ⟨σ, hσ, hσK, hne⟩ := h
    have hne' : φ σ ≠ 1 := fun hc => hne (by rw [MonoidHom.comp_apply, hc, map_one])
    obtain ⟨h1, h2, h3⟩ := hsch.2.2 A hA ⟨σ, hσ, hσK, hne'⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [← Subgroup.map_map (K := SSGRoute.decomp ℚ A) (f := φ)
        (g := flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ)]
      exact isCyclic_map_of_isCyclic_aux _ _ h2
    · intro σ' hσ'
      obtain ⟨τ, hτ, hτφ⟩ := h3 σ' hσ'
      exact ⟨τ, hτ, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hτφ]⟩

theorem isProperStageData_pushdown (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    {m n i j : ℕ} (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (h : IsProperStageData p K m i j φm ψm) :
    IsProperStageData p K n i j
      ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm)
      ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K)
          (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 Φ).comp ψm) := by
  obtain ⟨hSch, hLift, hFlow, hT1, hInv, hRam⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact scholz_pushdown_aux p K Φ φm hSch
  · intro σ
    refine ⟨?_, ?_⟩
    · show (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ (ψm σ)).right
          = (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (φm σ)).right
      rw [flowGroupMap_right_aux, flowGroupMap_right_aux, (hLift σ).1]
    · obtain ⟨z, hz1, hz2⟩ := (hLift σ).2
      refine ⟨⟨Φ.toHom z, Subgroup.mem_top _⟩, ?_, ?_⟩
      · show (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ (ψm σ)).left
            = (QuotientGroup.mk ⟨Φ.toHom z, Subgroup.mem_top _⟩ :
                flowQuotient p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
        rw [flowGroupMap_left_aux, hz1, flowQuotMap_mk_aux]
      · show (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (φm σ)).left
            = (QuotientGroup.mk ⟨Φ.toHom z, Subgroup.mem_top _⟩ :
                flowQuotient p (K ≃ₐ[ℚ] K) n i j)
        rw [flowGroupMap_left_aux, hz2, flowQuotMap_mk_aux]
  · obtain ⟨hsurj, hopen, hres⟩ := hFlow
    refine ⟨?_, ?_, ?_⟩
    · exact (flowGroupMap_surjective_aux (p := p) (tauSucc i j).1 (tauSucc i j).2 Φ).comp hsurj
    · refine Subgroup.isOpen_mono ?_ hopen
      intro σ hσ
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ ⊢
      rw [hσ, map_one]
    · intro σ
      rw [MonoidHom.comp_apply, flowQuot_flowGroupMap]
      exact hres σ
  · intro A hA σ hσ hσK
    rw [MonoidHom.comp_apply, hT1 A hA σ hσ hσK, map_one]
  · intro c hc hcK
    rw [MonoidHom.comp_apply, hInv c hc hcK, map_one]
  · intro A hA h
    obtain ⟨σ, hσ, hσK, hne⟩ := h
    have hne' : ψm σ ≠ 1 := fun hc => hne (by rw [MonoidHom.comp_apply, hc, map_one])
    obtain ⟨h1, h2⟩ := hRam A hA ⟨σ, hσ, hσK, hne'⟩
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | ⟨hcyc, hhit⟩
    · left
      intro σ' hσ'
      rw [MonoidHom.comp_apply, h2 σ' hσ', map_one]
    · right
      refine ⟨?_, ?_⟩
      · rw [← Subgroup.map_map (K := SSGRoute.decomp ℚ A) (f := ψm)
          (g := flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ)]
        exact isCyclic_map_of_isCyclic_aux _ _ hcyc
      · intro σ' hσ'
        obtain ⟨τ, hτ, hτψ⟩ := hhit σ' hσ'
        exact ⟨τ, hτ, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hτψ]⟩

end Work.SSGRoute
