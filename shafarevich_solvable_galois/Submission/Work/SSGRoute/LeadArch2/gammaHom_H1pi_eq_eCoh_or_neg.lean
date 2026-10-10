import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotient
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.augSES_shortExact
import Submission.Work.SSGRoute.eCoh_delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LeadArch2

open CategoryTheory SSGRoute.PTExt

attribute [local instance] Fintype.ofFinite

/-! ## The universal cocycle `g ↦ g - 1` of the augmentation ideal

The two degree-one realisations of `H¹ → Ext¹_G(ℤ, ·)` — the augmentation-sequence one
(`Work.SSGRoute.ExtH1.gammaHom`) and the bar-resolution one (`SSGRoute.PTExt.eCoh 1`) — are compared
by reducing to the single "universal" cocycle `g ↦ augDiff G g` of the augmentation ideal `augI G`,
in which the augmentation sequence `0 → I → k[G] → k → 0` is realised as a class by the connecting
map `δ` (`Work.SSGRoute.eCoh_delta` at `n = 0`).
-/

/-- The universal `1`-cocycle `g ↦ g - 1` of the augmentation ideal. -/
noncomputable def augUniv (G : Type) [Group G] : G → ↥(Work.SSGRoute.ExtH1.augI G) :=
  fun g => Work.SSGRoute.ExtH1.augDiff G g

/-- `g ↦ g - 1` is a `1`-cocycle (Mathlib's cocycle condition, on the representation `augI G`). -/
lemma augUniv_mem_cocycles₁ (G : Type) [Group G] :
    augUniv G ∈ groupCohomology.cocycles₁ (Work.SSGRoute.ExtH1.augI G) := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro g h
  apply Subtype.ext
  dsimp only [augUniv]
  simp only [Submodule.coe_add]
  rw [Work.SSGRoute.ExtH1.regRep_ρ_augDiff]
  change (Work.SSGRoute.ExtH1.ebas G (g * h) - Work.SSGRoute.ExtH1.ebas G 1 :
      Work.SSGRoute.ExtH1.regRep G)
      = (Work.SSGRoute.ExtH1.ebas G (g * h) - Work.SSGRoute.ExtH1.ebas G g)
        + (Work.SSGRoute.ExtH1.ebas G g - Work.SSGRoute.ExtH1.ebas G 1)
  abel

/-- The connecting map of the augmentation sequence sends the canonical generator of
`H⁰(G, Coeff)` to the class of the universal cocycle `g ↦ g - 1` in `H¹(G, augI G)`.  This is
`groupCohomology.δ₀_apply` with `z = 1`, `y = ebas G 1` (whose augmentation is `1`) and
`x = g ↦ g - 1` (whose `augIncl`-image is `d₀₁ (ebas G 1)`). -/
lemma delta_univ (G : Type) [Group G] :
    (groupCohomology.δ (Work.SSGRoute.augSES_shortExact G) 0 1 rfl).hom
        ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff))
      = (groupCohomology.H1π (Work.SSGRoute.ExtH1.augI G)).hom
          ⟨augUniv G, augUniv_mem_cocycles₁ G⟩ := by
  have hz : (1 : Coeff) ∈ (SSGRoute.PTExt.unitRep G).ρ.invariants := by
    rw [Representation.mem_invariants]
    intro g
    rfl
  have hy : (Rep.Hom.hom (Work.SSGRoute.ExtH1.augHom G)) (Work.SSGRoute.ExtH1.ebas G 1)
      = (↑(⟨(1 : Coeff), hz⟩ : ↥(SSGRoute.PTExt.unitRep G).ρ.invariants) :
          ↥(SSGRoute.PTExt.unitRep G)) := by
    rw [Work.SSGRoute.ExtH1.augHom_ebas]
  have hx : ⇑(Rep.Hom.hom (Work.SSGRoute.ExtH1.augIncl G)) ∘ (augUniv G)
      = (ConcreteCategory.hom (groupCohomology.d₀₁ (Work.SSGRoute.ExtH1.regRep G)))
          (Work.SSGRoute.ExtH1.ebas G 1) := by
    funext g
    show (Work.SSGRoute.ExtH1.augIncl G) (Work.SSGRoute.ExtH1.augDiff G g)
        = (ConcreteCategory.hom (groupCohomology.d₀₁ (Work.SSGRoute.ExtH1.regRep G)))
          (Work.SSGRoute.ExtH1.ebas G 1) g
    rw [groupCohomology.d₀₁_hom_apply]
    rw [Work.SSGRoute.ExtH1.regRep_ρ_ebas, mul_one]
    rfl
  have hδ := groupCohomology.δ₀_apply (X := Work.SSGRoute.ExtH1.augSES G)
      (Work.SSGRoute.augSES_shortExact G)
      (⟨(1 : Coeff), hz⟩ : ↥(SSGRoute.PTExt.unitRep G).ρ.invariants)
      (Work.SSGRoute.ExtH1.ebas G 1) hy (augUniv G) hx
  have hz_eq : (groupCohomology.H0Iso (SSGRoute.PTExt.unitRep G)).inv ⟨(1 : Coeff), hz⟩
      = (groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff) := by
    rw [groupCohomology.H0IsoOfIsTrivial_inv_apply]
  rw [hz_eq] at hδ
  rw [hδ]

/-! ## The degree-zero value of `eCoh` at the trivial representation

`eCoh 0 G (unitRep G) : H⁰(G, Coeff) ≃+ Ext⁰_G(Coeff, Coeff)` is an additive isomorphism between
two free `ℤ`-modules of rank one, so it is `±` the canonical generator.  The computation is done
by composing with `Abelian.Ext.addEquiv₀` and evaluating a `Coeff`-linear endomorphism of `Coeff`
at `1`: the composite is an additive (auto)morphism of `Coeff`, and any additive bijection of `ℤ`
sends `1` to `±1`.
-/

/-- **Degree-zero computation.** `addEquiv₀` of `eCoh 0 G (unitRep G)` on the canonical generator
(sent to `1` by `H0IsoOfIsTrivial`) is the identity or its negative. -/
theorem addEquiv0_eCoh_zero_unitRep_inv_one (G : Type) [Group G] :
    Abelian.Ext.addEquiv₀
        (SSGRoute.PTExt.eCoh 0 G (SSGRoute.PTExt.unitRep G)
          ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff)))
      = 𝟙 (SSGRoute.PTExt.unitRep G) ∨
    Abelian.Ext.addEquiv₀
        (SSGRoute.PTExt.eCoh 0 G (SSGRoute.PTExt.unitRep G)
          ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff)))
      = -𝟙 (SSGRoute.PTExt.unitRep G) := by
  let A : Rep Coeff G := SSGRoute.PTExt.unitRep G
  let Θ : Coeff ≃+ SSGRoute.PTExt.extH A 0 :=
    (Iso.toLinearEquiv (groupCohomology.H0IsoOfIsTrivial A).symm).toAddEquiv.trans
      (SSGRoute.PTExt.eCoh 0 G A)
  let g : Coeff →+ Coeff :=
    { toFun := fun z => (Abelian.Ext.addEquiv₀ (Θ z)).hom.toLinearMap 1
      map_zero' := by simp [Θ, map_zero]
      map_add' := by
        intro a b
        simp [Θ, map_add, Abelian.Ext.addEquiv₀.map_add, Rep.add_hom,
          Representation.IntertwiningMap.add_toLinearMap, LinearMap.add_apply] }
  obtain ⟨x, hx⟩ := Θ.surjective (Abelian.Ext.mk₀ (𝟙 A))
  have hmk : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (𝟙 A)) = 𝟙 A :=
    (Abelian.Ext.mk₀_bijective A A).1 (Abelian.Ext.mk₀_addEquiv₀_apply (Abelian.Ext.mk₀ (𝟙 A)))
  have hx1 : g x = 1 := by
    show (Abelian.Ext.addEquiv₀ (Θ x)).hom.toLinearMap 1 = (1 : Coeff)
    rw [hx, hmk]
    rfl
  have hxdec : x = (ULift.down x) • (1 : Coeff) := by
    apply ULift.ext
    simp
  have hgx : g x = (ULift.down x) • g 1 := by
    conv_lhs => rw [hxdec]
    rw [map_zsmul]
  have hgmul : (ULift.down x) * (ULift.down (g 1)) = 1 := by
    have h : (ULift.down x) • g 1 = 1 := by rw [← hgx]; exact hx1
    have h2 : ULift.down ((ULift.down x) • g 1) = ULift.down (1 : Coeff) :=
      congrArg ULift.down h
    simpa using h2
  have hm : ULift.down (g 1) = 1 ∨ ULift.down (g 1) = -1 := by
    rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hgmul) with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inl h2
    · exact Or.inr h2
  have hg1 : g 1 = 1 ∨ g 1 = -1 := by
    rcases hm with h | h
    · left; rw [← ULift.up_down (g 1), h]; rfl
    · right; rw [← ULift.up_down (g 1), h]; rfl
  rcases hg1 with h1 | h1
  · left
    change Abelian.Ext.addEquiv₀ (Θ 1) = 𝟙 A
    have hlin : (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro y
      calc (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap y
          = (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap (y • (1 : ↥A)) := by
            congr 1; simp
        _ = y • (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap (1 : ↥A) :=
              LinearMap.map_smul _ _ _
        _ = y • (1 : Coeff) := by
              rw [show (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap (1 : ↥A) = 1 from h1]
        _ = y := by simp
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rw [hlin]
    rfl
  · right
    change Abelian.Ext.addEquiv₀ (Θ 1) = -𝟙 A
    have hlin : (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap = -LinearMap.id := by
      apply LinearMap.ext
      intro y
      calc (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap y
          = (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap (y • (1 : ↥A)) := by
            congr 1; simp
        _ = y • (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap (1 : ↥A) :=
              LinearMap.map_smul _ _ _
        _ = y • (-1 : Coeff) := by
              rw [show (Abelian.Ext.addEquiv₀ (Θ 1)).hom.toLinearMap (1 : ↥A) = -1 from h1]
        _ = -y := by simp
        _ = (-LinearMap.id) y := rfl
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rw [hlin]
    rfl

/-- **Degree-zero computation, `Ext` form.**  `eCoh 0 G (unitRep G)` on the canonical generator is
`mk₀ 𝟙` or its negative. -/
theorem eCoh_zero_unitRep_inv_one_eq_mk0_or_neg (G : Type) [Group G] :
    SSGRoute.PTExt.eCoh 0 G (SSGRoute.PTExt.unitRep G)
        ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff))
      = Abelian.Ext.mk₀ (𝟙 (SSGRoute.PTExt.unitRep G)) ∨
    SSGRoute.PTExt.eCoh 0 G (SSGRoute.PTExt.unitRep G)
        ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff))
      = -Abelian.Ext.mk₀ (𝟙 (SSGRoute.PTExt.unitRep G)) := by
  let A : Rep Coeff G := SSGRoute.PTExt.unitRep G
  let c : SSGRoute.PTExt.extH A 0 :=
    SSGRoute.PTExt.eCoh 0 G A ((groupCohomology.H0IsoOfIsTrivial A).inv (1 : Coeff))
  have hc : Abelian.Ext.addEquiv₀ c = 𝟙 A ∨ Abelian.Ext.addEquiv₀ c = -𝟙 A :=
    addEquiv0_eCoh_zero_unitRep_inv_one G
  rcases hc with h | h
  · left
    change c = Abelian.Ext.mk₀ (𝟙 A)
    rw [← Abelian.Ext.mk₀_addEquiv₀_apply c, h]
  · right
    change c = -Abelian.Ext.mk₀ (𝟙 A)
    rw [← Abelian.Ext.mk₀_addEquiv₀_apply c, h, Abelian.Ext.mk₀_neg]

/-- (B1; the design's `Work.SSGRoute.LeadArch2.gammaHom_H1π_eq_eCoh_or_neg`, renamed to an ASCII
identifier; also on disk, as a `sorry`, as `Work.SSGRoute.PT.gammaHom_H1pi_eq_eCoh_or_neg`) The two
degree-one realisations `H¹ → Ext¹_G(ℤ, ·)` agree up to sign: the workspace `gammaHom` (augmentation
sequence, used by `levelClassOf`) and `eCoh 1` (bar resolution, used by `zLocal`).  The sign is
irrelevant at `p = 2`, which is the only prime at which the consumer
(`archPairLocalAbs_hpairArch_two`) is used.  Route: reduce to the universal cocycle `g ↦ g - 1` in
`augI G` (`cocycleHom_augDiff` + `eCoh_one_comp_mk0`), then `eCoh_delta` at `n = 0` for `augSES G`
with `δ 1 = [g ↦ g - 1]` and `eCoh 0 1 = mk₀ 𝟙`. -/
theorem gammaHom_H1pi_eq_eCoh_or_neg (G : Type) [Group G] (M : Type) [AddCommGroup M]
    [Module SSGRoute.PTExt.Coeff M] [DistribMulAction G M] [SMulCommClass G SSGRoute.PTExt.Coeff M]
    (ψ : ↥(Work.GroupCohomology.Z1 G M))
    (hψ : (ψ.1 : G → (SSGRoute.PTExt.modRep G M)) ∈
      groupCohomology.cocycles₁ (SSGRoute.PTExt.modRep G M)) :
    Work.SSGRoute.ExtH1.gammaHom G M (Work.SSGRoute.augSES_shortExact G)
        (Work.GroupCohomology.H1π G M ψ) =
      SSGRoute.PTExt.eCoh 1 G (SSGRoute.PTExt.modRep G M)
        ((groupCohomology.H1π (SSGRoute.PTExt.modRep G M)).hom ⟨ψ.1, hψ⟩) ∨
    Work.SSGRoute.ExtH1.gammaHom G M (Work.SSGRoute.augSES_shortExact G)
        (Work.GroupCohomology.H1π G M ψ) =
      -SSGRoute.PTExt.eCoh 1 G (SSGRoute.PTExt.modRep G M)
        ((groupCohomology.H1π (SSGRoute.PTExt.modRep G M)).hom ⟨ψ.1, hψ⟩) := by
  let hS : (Work.SSGRoute.ExtH1.augSES G).ShortExact := Work.SSGRoute.augSES_shortExact G
  let φ : Work.SSGRoute.ExtH1.augI G ⟶ SSGRoute.PTExt.modRep G M :=
    Work.SSGRoute.ExtH1.cocycleHom G ψ.1
      ((Work.SSGRoute.ExtH1.crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2)
  let zu : ↥(groupCohomology.cocycles₁ (Work.SSGRoute.ExtH1.augI G)) :=
    ⟨augUniv G, augUniv_mem_cocycles₁ G⟩
  let E : SSGRoute.PTExt.extH (Work.SSGRoute.ExtH1.augI G) 1 :=
    SSGRoute.PTExt.eCoh 1 G (Work.SSGRoute.ExtH1.augI G)
      ((groupCohomology.H1π (Work.SSGRoute.ExtH1.augI G)).hom zu)
  have hL : Work.SSGRoute.ExtH1.gammaHom G M hS (Work.GroupCohomology.H1π G M ψ)
      = hS.extClass.comp (Abelian.Ext.mk₀ φ) (by norm_num : 1 + 0 = 1) := by
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π, Work.SSGRoute.ExtH1.gammaZ1_apply]
    rfl
  have hE : E = hS.extClass ∨ E = -hS.extClass := by
    have hdelta := Work.SSGRoute.eCoh_delta 0 G (Work.SSGRoute.ExtH1.augSES G) hS
        ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff))
    rw [delta_univ G] at hdelta
    have hc := eCoh_zero_unitRep_inv_one_eq_mk0_or_neg G
    have hk : (SSGRoute.PTExt.eCoh 0 G (SSGRoute.PTExt.unitRep G)
          ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff))).comp
          hS.extClass (by norm_num : 0 + 1 = 1) = hS.extClass ∨
        (SSGRoute.PTExt.eCoh 0 G (SSGRoute.PTExt.unitRep G)
          ((groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff))).comp
          hS.extClass (by norm_num : 0 + 1 = 1) = -hS.extClass := by
      rcases hc with hc | hc
      · left
        rw [hc]
        exact Abelian.Ext.mk₀_id_comp hS.extClass
      · right
        rw [hc, Abelian.Ext.neg_comp]
        exact congrArg Neg.neg (Abelian.Ext.mk₀_id_comp hS.extClass)
    rcases hdelta with h | h
    · rcases hk with hk | hk
      · left; exact h.trans hk
      · right; exact h.trans hk
    · rcases hk with hk | hk
      · right; exact h.trans (by rw [hk])
      · left; exact h.trans (by rw [hk, neg_neg])
  have hz : ∀ g : G,
      (⟨ψ.1, hψ⟩ : ↥(groupCohomology.cocycles₁ (SSGRoute.PTExt.modRep G M))) g = φ.hom (zu g) := by
    intro g
    exact (Work.SSGRoute.ExtH1.cocycleHom_augDiff G ψ.1
      ((Work.SSGRoute.ExtH1.crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2) g).symm
  have hR : SSGRoute.PTExt.eCoh 1 G (SSGRoute.PTExt.modRep G M)
      ((groupCohomology.H1π (SSGRoute.PTExt.modRep G M)).hom ⟨ψ.1, hψ⟩)
      = E.comp (Abelian.Ext.mk₀ φ) (add_zero 1) := by
    rw [← Work.SSGRoute.E7cOmega.eCoh_one_comp_mk0 G (Work.SSGRoute.ExtH1.augI G)
      (SSGRoute.PTExt.modRep G M) φ zu ⟨ψ.1, hψ⟩ hz]
  rcases hE with hE | hE
  · left
    rw [hL, hR, hE]
  · right
    rw [hL, hR, hE, Abelian.Ext.neg_comp]
    simp

end Work.SSGRoute.LeadArch2
