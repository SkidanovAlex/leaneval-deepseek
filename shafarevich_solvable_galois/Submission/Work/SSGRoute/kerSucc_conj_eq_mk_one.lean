import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel of `flowGroupSucc` is central: conjugation depends only on the `G`-coordinate

The projection `flowGroupSucc p G m i j : Γ(τ+1) →* Γ(τ)` of
`Submission.Work.SSGRoute.FlowGroupSuccDefs` has kernel the graded piece
`E(m,τ) = F(m)_{(i,j)}/F(m)_{(τ+1)}` inside `F(m)/F(m)^{(τ+1)}` (the left factor `N` of the
semidirect product `Γ(τ+1) = F(m)/F(m)^{(τ+1)} ⋊ G`).  By Lemma 4 of Schmidt–Wingberg —
`⁅P_{(i,j)}, P⁆ ≤ P_{(i,j)+1}` — this graded piece is **central** in `F(m)/F(m)^{(τ+1)}`.

Consequently, conjugating an element `x` of the kernel by an element of `Γ(τ+1)` only depends on
the `G`-coordinate of that element: the difference `mk a g · mk 1 g⁻¹` lies in the normal subgroup
`N`, where it acts trivially on the kernel.  This is the statement proved below.

## Main declarations

* `Work.SSGRoute.semidirect_mk_conj` — the conjugation formula in a semidirect product;
* `Work.SSGRoute.commutator_flowTerm_le_top` — Lemma 4 in commutator form for `F(m)`;
* `Work.SSGRoute.flowQuotSucc_ker_central` — the kernel of `flowQuotSucc` is central;
* `Work.SSGRoute.kerSucc_conj_eq_mk_one` — the target lemma.
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking
open scoped commutatorElement

/-! ## Two elementary group-theoretic lemmas -/

/-- Conjugation in a semidirect product, in coordinates: conjugating `mk c 1` by `mk a g` gives
`mk (a * φ g c * a⁻¹) 1`. -/
theorem semidirect_mk_conj {N G : Type*} [Group N] [Group G] (φ : G →* MulAut N)
    (a c : N) (g : G) :
    SemidirectProduct.mk (φ := φ) a g * SemidirectProduct.mk (φ := φ) c 1
        * (SemidirectProduct.mk (φ := φ) a g)⁻¹
      = SemidirectProduct.mk (φ := φ) (a * φ g c * a⁻¹) 1 := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right, mul_assoc]

/-- **Lemma 4 of Schmidt–Wingberg, commutator form with the whole group**: the commutator of a
refined term `P_{(i,j)}` with `P` lies in the next refined term `P_{(i,j)+1}`. -/
theorem commutator_flowTerm_le_top (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    ⁅flowTerm p G m i j, ⊤⁆ ≤ flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 :=
  calc ⁅flowTerm p G m i j, ⊤⁆
      ≤ ⁅pSeries p (Work.Shrinking.freeOperatorGroup G m) i, ⊤⁆ :=
        Subgroup.commutator_mono (refinedTerm_le_pSeries p _ i j) le_rfl
    _ ≤ pSeries p (Work.Shrinking.freeOperatorGroup G m) (i + 1) :=
        commutator_pSeries_le p _ i
    _ ≤ flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 :=
        pSeries_succ_le_refinedTerm_succ p i j

/-- The kernel of `flowQuotSucc` — that is, the graded piece `E(m,τ)` inside
`F(m)/F(m)^{(τ+1)}` — is central in `F(m)/F(m)^{(τ+1)}`. -/
theorem flowQuotSucc_ker_central (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (a c : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2)
    (hc : c ∈ (flowQuotSucc p G m i j).ker) :
    a * c * a⁻¹ = c := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) c
  rw [MonoidHom.mem_ker, flowQuotSucc_mk] at hc
  have hx : ((x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
      Work.Shrinking.freeOperatorGroup G m) ∈ flowTerm p G m i j :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x).mp hc)
  have hle : ⁅(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)), flowTerm p G m i j⁆
      ≤ flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 := by
    rw [Subgroup.commutator_comm]
    exact commutator_flowTerm_le_top p G m i j
  have hmem : ⁅((y : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
      Work.Shrinking.freeOperatorGroup G m), (x : Work.Shrinking.freeOperatorGroup G m)⁆
      ∈ flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 :=
    (Subgroup.commutator_le.mp hle) (y : Work.Shrinking.freeOperatorGroup G m)
      (Subgroup.mem_top _) (x : Work.Shrinking.freeOperatorGroup G m) hx
  rw [← map_mul, ← map_inv, ← map_mul]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
    div_eq_mul_inv]
  exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using hmem)

/-- **The target lemma**: in the semidirect product `Γ(τ+1) = F(m)/F(m)^{(τ+1)} ⋊ G`, conjugation
of an element `x` of the kernel of `flowGroupSucc` by `mk a g` only depends on the `G`-coordinate
`g`, because the graded piece `E(m,τ)` is central in `F(m)/F(m)^{(τ+1)}`. -/
theorem kerSucc_conj_eq_mk_one (p : ℕ) (G : Type*) [Group G] (i j m : ℕ)
    (a : Work.CohomologicalShrinking.flowQuotient p G m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (g : G) (x : ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker) :
    Work.AbsoluteGalois.conjKernelMul (Work.SSGRoute.flowGroupSucc p G m i j)
        ((SemidirectProduct.mk a g : Work.CohomologicalShrinking.flowGroup p G m
          (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2)) x
      = Work.AbsoluteGalois.conjKernelMul (Work.SSGRoute.flowGroupSucc p G m i j)
          ((SemidirectProduct.mk 1 g : Work.CohomologicalShrinking.flowGroup p G m
            (Work.CohomologicalShrinking.tauSucc i j).1
            (Work.CohomologicalShrinking.tauSucc i j).2)) x := by
  apply Subtype.ext
  set xa : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 :=
    (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) with hxa
  -- the kernel consists of elements whose `G`-coordinate is `1` and whose `N`-coordinate dies
  -- in `F(m)/F(m)^{(τ)}`
  have hxr : xa.right = 1 := by
    have h := congrArg SemidirectProduct.right x.2
    simpa [hxa] using h
  have hxl : flowQuotSucc p G m i j xa.left = 1 := by
    have h := congrArg SemidirectProduct.left x.2
    simpa [hxa] using h
  have hx : xa = SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2)
      xa.left 1 :=
    SemidirectProduct.ext rfl hxr
  -- the `G`-action preserves the kernel (naturality of the projection)
  have hc : flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g xa.left
      ∈ (flowQuotSucc p G m i j).ker := by
    have h := flowQuotSucc_smul p G m i j g xa.left
    rw [show g • xa.left
        = flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g xa.left from rfl] at h
    rw [MonoidHom.mem_ker, h, hxl]
    exact smul_one g
  -- centrality of the kernel
  have hcent : a * flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g xa.left * a⁻¹
      = flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g xa.left :=
    flowQuotSucc_ker_central p G m i j a _ hc
  calc SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) a g
          * xa
          * (SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) a g)⁻¹
      = SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) a g
          * SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) xa.left 1
          * (SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) a g)⁻¹ := by
        rw [hx]
    _ = SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2)
          (a * flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g xa.left * a⁻¹) 1 :=
        semidirect_mk_conj (flowAction p G m (tauSucc i j).1 (tauSucc i j).2) a xa.left g
    _ = SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2)
          (flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g xa.left) 1 := by rw [hcent]
    _ = SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2)
          (1 * flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g xa.left * 1⁻¹) 1 := by
        simp
    _ = SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) 1 g
          * SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) xa.left 1
          * (SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) 1 g)⁻¹ :=
        (semidirect_mk_conj (flowAction p G m (tauSucc i j).1 (tauSucc i j).2) 1 xa.left g).symm
    _ = SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) 1 g
          * xa
          * (SemidirectProduct.mk (φ := flowAction p G m (tauSucc i j).1 (tauSucc i j).2) 1 g)⁻¹ := by
        rw [hx]

end Work.SSGRoute
