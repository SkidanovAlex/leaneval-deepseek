import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.CohomologicalShrinking.Prop7iConcrete
import Submission.Work.CohomologicalShrinking.TateShifts
import Submission.Work.CohomologicalShrinking.exists_shrinking_Hm2_tate
import Submission.Work.CohomologicalShrinking.flow.finite_refinedQuotient
import Submission.Work.CohomologicalShrinking.nonempty_prop5Data_one_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-! ## The triviality of the normal factor at `τ = (1,1)`

At `τ = (1,1)` the refined term is the whole group, `F(m)^{(1,1)} = F(m)`, so the normal subgroup
`F(m)/F(m)^{(1,1)} ◁ Γ_m` of the semidirect product `Γ_m = F(m)/F(m)^{(1,1)} ⋊ G` is trivial.
We record this in the form needed below: the quotient `flowQuotient p G m 1 1 = F(m)/F(m)^{(1,1)}`
is a subsingleton. -/

/-- `F(m)^{(1,1)} = F(m)`: the quotient `F(m)/F(m)^{(1,1)}` is trivial. -/
theorem stage3ShrinkingIOne_flowQuotient_subsingleton (p : ℕ) (G : Type*) [Group G] (m : ℕ) :
    Subsingleton (flowQuotient p G m 1 1) := by
  have hq : flowQuotient p G m 1 1 =
      ((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)) ⧸
        ((flowTerm p G m 1 1).subgroupOf ⊤)) := rfl
  have ht : flowTerm p G m 1 1 = ⊤ := by rw [flowTerm, refinedTerm_one, pSeries_one]
  rw [hq, ht]
  exact QuotientGroup.subsingleton_iff.mpr rfl

/-- The normal subgroup `F(m)/F(m)^{(1,1)} ◁ Γ_m` is trivial. -/
theorem stage3ShrinkingIOne_flowNormal_subsingleton (p : ℕ) (G : Type*) [Group G] (m : ℕ) :
    Subsingleton ↥(flowNormal p G m 1 1) := by
  haveI := stage3ShrinkingIOne_flowQuotient_subsingleton p G m
  refine ⟨fun a b => Subtype.ext ?_⟩
  obtain ⟨y, hy⟩ := a.2
  obtain ⟨y', hy'⟩ := b.2
  rw [← hy, ← hy', Subsingleton.elim y y']

/-! ## The corestriction from the trivial normal factor vanishes

The first map `flowHSα` of the homological Hochschild–Serre sequence of
`F(m)/F(m)^{(1,1)} ◁ Γ_m` is the corestriction out of `H₁` of the (trivial) normal subgroup; being
a map out of the zero module it is zero, hence `range (flowHSα p G 1 1 T m) = ⊥`.  This is the
`τ = (1,1)` form of the statement that the recalled `H⁻² = H₁` is an isomorphism here (the
coinflation `flowHSβ` is injective), and it is the input that lets the zero map `α` satisfy
`hαrange` of `exists_shrinking_H1_semidirect_of_alpha`. -/

/-- **The corestriction of the Hochschild–Serre sequence at `τ = (1,1)` is zero.** -/
theorem stage3ShrinkingIOne_flowHSα_range_bot (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    [Fintype G]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (flowHSα p G 1 1 T m).range = ⊥ := by
  -- the normal subgroup is trivial, hence so is `H₁` of it
  haveI hsub := stage3ShrinkingIOne_flowNormal_subsingleton p G m
  haveI : (Rep.res (flowNormal p G m 1 1).subtype (flowRep p G m 1 1 T)).IsTrivial := inferInstance
  haveI hab : Subsingleton (Abelianization ↥(flowNormal p G m 1 1)) := by
    refine QuotientGroup.subsingleton_iff.mpr ?_
    refine le_antisymm le_top (fun x _ => ?_)
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  haveI hH1 : Subsingleton (↑(groupHomology.H1
      (Rep.res (flowNormal p G m 1 1).subtype (flowRep p G m 1 1 T))) : Type) :=
    Subsingleton.intro (fun a b => (groupHomology.H1AddEquivOfIsTrivial
      (Rep.res (flowNormal p G m 1 1).subtype (flowRep p G m 1 1 T))).injective
        (Subsingleton.elim _ _))
  rw [AddMonoidHom.range_eq_bot_iff]
  exact AddMonoidHom.ext (fun x => by rw [Subsingleton.elim x 0]; simp)

/-- **Proposition 7 (i) of Schmidt–Wingberg at the base `τ = (1,1)`.**

This is the `i = 1` instance of `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper`,
which is stated with the hypothesis `hi : 2 ≤ i` because its proof uses the paper's map `α`
together with `Work.CohomologicalShrinking.flowAlpha_range` (whose construction needs
`ν = (i,j) ≥ (2,1)`).  It is needed by the induction of Theorem 15 at the base `τ = (1,1)`, where
`Γ_m(1,1) = G` (`Work.CohomologicalShrinking.refinedTerm_one`: `refinedTerm p P 1 1 = pSeries p P 1
= ⊤`) and `E p G m 1 1 = F(m)/F(m)^{(2,1)} = squareQuotient p G m`; `1 ≤ j ≤ i` forces `j = 1`.

**Proof (much cheaper than the `2 ≤ i` case).**  At `ν = (1,1)` one has `F(m)^{(1,1)} = F(m)`, so
the first Hochschild–Serre term is `H₁(N, E⊗T)` with `N = ⊥`; hence
`range (Work.CohomologicalShrinking.flowHSα p G 1 1 T m) = ⊥` and the **zero** map satisfies both
`hαrange` and `hαnat` of
`Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_of_alpha` (which has no `2 ≤ i`
hypothesis and already discharges the recalled `H^{-2} = H₁` by
`Work.CohomologicalShrinking.exists_bridge`).  Equivalently: the statement is the `i = j = 1` case
of `Work.CohomologicalShrinking.exists_shrinking_Hm2_tate` (the paper's Proposition 6 with
`k = −2`, unconditional given `D`), transported by the isomorphism `γ` and the naturality `hβnat`
of `Work.CohomologicalShrinking.exists_bridge` via `flowHSβ`.  Either way the remaining work is the
`flowRep`-vs-`flowRepG` bookkeeping.  The paper says the same: "If `τ = 1`, then the statement to
prove is just a special case of proposition 6."

`D : Prop5Data p G 1 1` is in fact redundant (`nonempty_prop5Data_one_one`), but keeping it matches
the general signature. -/
theorem stage3Shrinking_i_one (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (D : Work.CohomologicalShrinking.Prop5Data p G 1 1)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → (↑(groupHomology.H1
        (Work.CohomologicalShrinking.flowRep p G m 1 1 T)) : Type),
      ∃ Φ : Work.CohomologicalShrinking.OperatorMap G m n,
        ∀ k : Fin t,
          Work.CohomologicalShrinking.flowZMap (p := p) G 1 1 Φ T (x k) = 0 := by
  refine exists_shrinking_H1_semidirect_of_alpha p G (i := 1) (j := 1) le_rfl D T
    (fun m => 0) (fun m => ?_) (fun m n Φ x => by simp) t hn
  rw [AddMonoidHom.range_zero]
  exact (stage3ShrinkingIOne_flowHSα_range_bot p G T m).symm

end Work.SSGRoute
