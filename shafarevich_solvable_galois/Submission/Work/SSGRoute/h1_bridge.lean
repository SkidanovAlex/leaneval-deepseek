import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Compatibility lemmas: Mathlib's `groupCohomology` (inhomogeneous `1`-cocycles and `1`-coboundaries
of the representation attached to a `DistribMulAction`) agrees with the local vocabulary
`IsCocycleOn`/`IsCoboundaryOn`, and `H1` is the quotient of the `1`-cocycles by the
`1`-coboundaries, so that any linear form on the cocycles killing the coboundaries descends to
`H1`. -/
theorem h1_bridge (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M] :
    (∀ (f : G → M),
        f ∈ groupCohomology.cocycles₁ (Rep.of (Representation.ofDistribMulAction (ZMod p) G M)) ↔
          SSGRoute.IsCocycleOn (MonoidHom.id G) ⊤ f) ∧
    (∀ (f : G → M),
        f ∈ groupCohomology.coboundaries₁ (Rep.of (Representation.ofDistribMulAction (ZMod p) G M)) ↔
          SSGRoute.IsCoboundaryOn (MonoidHom.id G) ⊤ f) ∧
    (∀ (lin : ↥(groupCohomology.cocycles₁ (Rep.of (Representation.ofDistribMulAction (ZMod p) G M))) →ₗ[ZMod p] ZMod p),
        (∀ (x : G → M) (hx : x ∈ groupCohomology.coboundaries₁ (Rep.of (Representation.ofDistribMulAction (ZMod p) G M))),
          lin ⟨x, groupCohomology.coboundaries₁_le_cocycles₁ _ hx⟩ = 0) →
        ∃ Lift : groupCohomology.H1 (Rep.of (Representation.ofDistribMulAction (ZMod p) G M)) →ₗ[ZMod p] ZMod p,
          ∀ x : ↥(groupCohomology.cocycles₁ (Rep.of (Representation.ofDistribMulAction (ZMod p) G M))),
            Lift (groupCohomology.H1π _ x) = lin x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    rw [groupCohomology.mem_cocycles₁_iff]
    constructor
    · intro hc g _ h _
      have hh := hc g h
      simp only [Representation.ofDistribMulAction_apply_apply, MonoidHom.id_apply] at hh ⊢
      rw [hh, add_comm]
    · intro hc g h
      have hh := hc g trivial h trivial
      simp only [Representation.ofDistribMulAction_apply_apply, MonoidHom.id_apply] at hh ⊢
      rw [hh, add_comm]
  · intro f
    constructor
    · intro hf
      obtain ⟨m, hm⟩ :=
        groupCohomology.isCoboundary₁_of_mem_coboundaries₁ (k := ZMod p) (G := G) (A := M) f hf
      refine ⟨m, ?_⟩
      intro g _
      rw [← hm g]
      simp only [MonoidHom.id_apply]
    · rintro ⟨m, hm⟩
      have hf : groupCohomology.IsCoboundary₁ (G := G) (A := M) f :=
        ⟨m, fun g => by
          have hgg := hm g trivial
          simp only [MonoidHom.id_apply] at hgg
          exact hgg.symm⟩
      exact (groupCohomology.coboundariesOfIsCoboundary₁ (k := ZMod p) (G := G) (A := M) hf).2
  · intro lin hlin
    let A := Rep.of (Representation.ofDistribMulAction (ZMod p) G M)
    let f : ↥(groupCohomology.cocycles₁ A) →ₗ[ZMod p] groupCohomology.H1 A :=
      (groupCohomology.H1π A).hom
    have hsurj : Function.Surjective f :=
      (ModuleCat.epi_iff_surjective (groupCohomology.H1π A)).1 inferInstance
    have hker : LinearMap.ker f ≤ LinearMap.ker lin := by
      intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      have hy2 : (y : G → M) ∈ groupCohomology.coboundaries₁ A :=
        (groupCohomology.H1π_eq_zero_iff (A := A) y).1 hy
      have h0 := hlin (y : G → M) hy2
      have hyy : (⟨(y : G → M), groupCohomology.coboundaries₁_le_cocycles₁ A hy2⟩ :
          ↥(groupCohomology.cocycles₁ A)) = y := Subtype.ext rfl
      rwa [← hyy]
    refine ⟨(Submodule.liftQ (LinearMap.ker f) lin hker).comp
      (LinearMap.quotKerEquivOfSurjective f hsurj).symm.toLinearMap, ?_⟩
    intro x
    show (Submodule.liftQ (LinearMap.ker f) lin hker)
      ((LinearMap.quotKerEquivOfSurjective f hsurj).symm (f x)) = lin x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    exact Submodule.liftQ_apply _ _ _

end Work.SSGRoute
