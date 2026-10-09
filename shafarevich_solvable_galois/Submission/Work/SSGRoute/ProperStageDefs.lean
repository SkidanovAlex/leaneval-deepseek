import Mathlib
import Submission.Work.CohomologicalShrinking.Semidirect
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Step 3 of Theorem 15: the level projection and the properness criterion

Schmidt–Wingberg's Step 3 compares solutions of the level-`τ+1` embedding problem with those of
the level-`τ` problem through the natural projection

`flowGroupProj p G m i j : F(m)/F(m)^{(τ+1)} ⋊ G →* F(m)/F(m)^{(τ)} ⋊ G`,  `τ+1 = tauSucc i j`,

whose kernel `flowEKer p G m i j` is the copy of the graded piece `E p G m i j` inside the
level-`τ+1` group.

A lift `ψ` of a solution `φ` of the level-`τ` problem factors through the projection
(`flowGroupProj_comp_of_LiftsFlow`); consequently `ψ` is surjective as soon as its image contains
`flowEKer` (`surjective_of_flowEKer_le_range`): this is the form in which properness is obtained
in Step 3 (the `T⁰` primes of the paper, and the Frattini argument for `τ ≥ (2,1)`).
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking

open scoped TensorProduct

set_option maxHeartbeats 800000

/-- The next term of the refinement is contained in the current one: `P_{(i,j)+1} ≤ P_{(i,j)}`. -/
theorem refinedTerm_tauSucc_le (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 ≤ refinedTerm p P i j := by
  rcases lt_or_ge j i with h | h
  · rw [tauSucc_of_lt h]
    exact refinedTerm_antitone_snd p P i j
  · rw [tauSucc_of_le h, refinedTerm_one]
    intro x hx
    show x ∈ (pSeries p P i ⊓ centralSeries P j) ⊔ pSeries p P (i + 1)
    exact Subgroup.mem_sup_right hx

/-- The projection `F(m)/F(m)^{(τ+1)} →* F(m)/F(m)^{(τ)}` (the identity on `F(m)`). -/
noncomputable def flowQuotientProj (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2 →* flowQuotient p G m i j :=
  QuotientGroup.map ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
    (MonoidHom.id (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
    (fun x hx => refinedTerm_tauSucc_le p (Work.Shrinking.freeOperatorGroup G m) i j hx)

theorem flowQuotientProj_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotientProj p G m i j
        (QuotientGroup.mk' ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y) =
      QuotientGroup.mk' ((flowTerm p G m i j).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        ⟨MonoidHom.id _ y, Subgroup.mem_top _⟩ :=
  QuotientGroup.map_mk' _ _ _ _ y

/-- The level projection fixes the class of a representative. -/
theorem flowQuotientProj_coe (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotientProj p G m i j
        (↑y : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) =
      (↑y : flowQuotient p G m i j) := by
  change flowQuotientProj p G m i j
      (QuotientGroup.mk' ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y) =
    QuotientGroup.mk' ((flowTerm p G m i j).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y
  rw [flowQuotientProj_mk]
  rfl

/-- `G`-equivariance of the level projection of the left factors. -/
theorem flowQuotientProj_smul (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (x : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) :
    flowQuotientProj p G m i j (g • x) = g • flowQuotientProj p G m i j x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) x
  have hP : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hKP : (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g)
      (tauSucc i j).1 (tauSucc i j).2
  have hKQ : (flowTerm p G m i j).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m i j :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g) i j
  have keyP : g • (QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y)
      = QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        (Work.Shrinking.subAut ⊤ g hP y) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2) g hP hKP
      (QuotientGroup.mk' _ y) = _
    rw [Work.Shrinking.quotAut_mk]
  have keyQ : g • (QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        ⟨MonoidHom.id _ y, Subgroup.mem_top _⟩)
      = QuotientGroup.mk' ((flowTerm p G m i j).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        (Work.Shrinking.subAut ⊤ g hP ⟨MonoidHom.id _ y, Subgroup.mem_top _⟩) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G m i j) g hP hKQ
      (QuotientGroup.mk' _ _) = _
    rw [Work.Shrinking.quotAut_mk]
  rw [keyP]
  simp only [flowQuotientProj_mk]
  rw [keyQ]
  congr 1

/-- **The level projection** `F(m)/F(m)^{(τ+1)} ⋊ G →* F(m)/F(m)^{(τ)} ⋊ G` of Step 3. -/
noncomputable def flowGroupProj (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 →* flowGroup p G m i j :=
  SemidirectProduct.map (flowQuotientProj p G m i j) (MonoidHom.id G)
    (fun g => MonoidHom.ext (fun x => flowQuotientProj_smul p G m i j g x))

theorem flowGroupProj_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (a : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) (g : G) :
    flowGroupProj p G m i j (SemidirectProduct.mk a g) =
      SemidirectProduct.mk (flowQuotientProj p G m i j a) g := rfl

/-- The copy of the graded piece `E p G m i j` inside `F(m)/F(m)^{(τ+1)} ⋊ G`: the kernel of the
level projection. -/
noncomputable def flowEKer (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Subgroup (flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) :=
  (flowGroupProj p G m i j).ker

/-- **Properness of a lift from the `T⁰`-generation of the graded piece.**

If `ψ` is a lift of a surjective level-`τ` solution `φ` and the images of the subgroups
`T i ≤ G_ℚ` (with `T i ≤ ker φ`, e.g. decomposition groups of primes split completely in the
level-`τ` field) generate the copy `flowEKer` of `E(m,τ)` inside the level-`τ+1` group, then `ψ`
is surjective.  This is the criterion `Work.Properness.Setup.isProper_of_iSup_map_eq` in the
`T⁰` form used in Step 3 of Theorem 15. -/
theorem surjective_of_iSup_map_eq_flowEKer {p : ℕ}
    {G : Type*} [Group G] {m i j : ℕ} {H0 : Type*} [Group H0]
    {ψ : H0 →* flowGroup p G m (tauSucc i j).1 (tauSucc i j).2}
    {φ : H0 →* flowGroup p G m i j}
    (hLift : ∀ σ : H0, flowGroupProj p G m i j (ψ σ) = φ σ)
    (hφ : Function.Surjective φ) {ι : Type*} (T : ι → Subgroup H0)
    (hgen : (⨆ i, (T i).map ψ) = flowEKer p G m i j) :
    Function.Surjective ψ := by
  have hle : flowEKer p G m i j ≤ (MonoidHom.range ψ) := by
    rw [← hgen]
    refine iSup_le fun i => ?_
    rintro x ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  intro x
  obtain ⟨σ, hσ⟩ := hφ (flowGroupProj p G m i j x)
  have hmem : x * (ψ σ)⁻¹ ∈ flowEKer p G m i j := by
    rw [flowEKer, MonoidHom.mem_ker, map_mul, map_inv, hLift σ, hσ, mul_inv_cancel]
  obtain ⟨σ', hσ'⟩ := hle hmem
  exact ⟨σ' * σ, by rw [map_mul, hσ', mul_assoc, inv_mul_cancel, mul_one]⟩

end Work.SSGRoute
