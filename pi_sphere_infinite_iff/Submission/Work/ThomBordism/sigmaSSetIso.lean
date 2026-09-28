import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Bordism.toSSet_coprod_iso
import Submission.Work.Cohomology.Pullback

/-!
# The singular simplicial set of a `σ`-type of spaces is the coproduct of the pieces

For a family of topological spaces `α : ι → TopCat`, the space `TopCat.of (Σ i, α i)` (the
`σ`-type with the sum topology) is the coproduct of the `α i`, with the inclusions
`TopCat.sigmaι α i` (`TopCat.sigmaCofanIsColimit`).  The singular simplicial set of a *coproduct*
is not the coproduct of the singular simplicial sets for a general right adjoint functor, but it is
here: the standard simplex `Δᵏ` is *connected*, so every continuous map `Δᵏ ⟶ Σ i, α i` lands in a
single fibre (`exists_lift_sigma`).  The main results are

* `Work.ThomBordism.sigmaLegs_bijective` — the levelwise statement: the canonical map
  `(Σ i, (toSSet (α i))ₖ) → (toSSet (Σ i, α i))ₖ` is a bijection;
* `Work.ThomBordism.ssetSigmaCofan_isColimit` — the cofan with point `toSSet (Σ i, α i)` and legs
  `toSSet.map (TopCat.sigmaι α i)` is a colimiting cofan;
* `Work.ThomBordism.ssetSigmaIso` — `toSSet (Σ i, α i) ≅ ∐ i, toSSet (α i)`, compatible with the
  inclusions (`ssetSigmaIso_hom_sigmaι`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory Limits Topology

namespace Work.ThomBordism

noncomputable section

/-! ## A continuous map from a connected space into a `σ`-type lands in one fibre -/

/-- **A continuous map from a connected space to a `σ`-type of spaces lands entirely in one
fibre**: it is `t ↦ ⟨i, g t⟩` for some index `i` and continuous `g`.  (The fibres are clopen, and
the image of a connected space in a space whose components are the fibres is connected.) -/
theorem exists_lift_sigma {ι : Type} {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]
    {T : Type} [TopologicalSpace T] [ConnectedSpace T] {f : T → Σ i, Y i} (hf : Continuous f) :
    ∃ (i : ι) (g : T → Y i), Continuous g ∧ ∀ t, f t = ⟨i, g t⟩ := by
  have hs : IsPreconnected (Set.range f) := isPreconnected_range hf
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  have hne : (Set.range f ∩ Set.range (Sigma.mk (f t₀).1)).Nonempty :=
    ⟨f t₀, ⟨t₀, rfl⟩, ⟨(f t₀).2, rfl⟩⟩
  have hsub : Set.range f ⊆ Set.range (Sigma.mk (f t₀).1) :=
    hs.subset_isClopen isClopen_range_sigmaMk hne
  obtain ⟨g, hg⟩ := Set.range_subset_range_iff_exists_comp.1 hsub
  refine ⟨(f t₀).1, g, ?_, fun t => ?_⟩
  · exact (IsEmbedding.continuous_iff (IsEmbedding.sigmaMk (i := (f t₀).1))).mpr (hg ▸ hf)
  · exact congrFun hg t

/-! ## The levelwise splitting -/

variable {ι : Type} (α : ι → TopCat.{0})

/-- The inclusion `α i ⟶ TopCat.of (Σ i, α i)` as a map of underlying types. -/
lemma sigmaι_hom_apply (i : ι) (x : (α i : Type)) :
    (TopCat.sigmaι α i).hom x = (⟨i, x⟩ : Σ i, α i) := rfl

/-- **The levelwise splitting of the simplices of a `σ`-type**: the canonical map from the `σ`-type
of the `k`-simplices of the pieces to the `k`-simplices of the disjoint union is a bijection. -/
theorem sigmaLegs_bijective (k : SimplexCategoryᵒᵖ) :
    Function.Bijective (fun x : (Σ i, (TopCat.toSSet.obj (α i)).obj k) =>
      (TopCat.toSSet.map (TopCat.sigmaι α x.1)).app k x.2) := by
  constructor
  · rintro ⟨i, σ⟩ ⟨j, τ⟩ h
    have h' := congrArg (TopCat.toSSetObjEquivT (TopCat.of (Σ i, α i)) k) h
    rw [Work.Bordism.toSSetObjEquiv_map_apply, Work.Bordism.toSSetObjEquiv_map_apply] at h'
    have hij : i = j := by
      have h2 := DFunLike.congr_fun h' (stdSimplex.vertex (0 : Fin (k.unop.len + 1)))
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, sigmaι_hom_apply,
        sigmaι_hom_apply] at h2
      exact (Sigma.mk.inj h2).1
    subst hij
    congr 1
    apply (TopCat.toSSetObjEquivT (α i) k).injective
    refine DFunLike.ext _ _ fun t => ?_
    have h2 := DFunLike.congr_fun h' t
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, sigmaι_hom_apply,
      sigmaι_hom_apply] at h2
    exact eq_of_heq (Sigma.mk.inj h2).2
  · intro ξ
    obtain ⟨i, g, hg, hfg⟩ := exists_lift_sigma (Y := fun i => (α i : Type))
      (T := ↥(stdSimplex ℝ (Fin (k.unop.len + 1))))
      (f := fun t => (TopCat.toSSetObjEquivT (TopCat.of (Σ i, α i)) k ξ) t)
      (TopCat.toSSetObjEquivT (TopCat.of (Σ i, α i)) k ξ).continuous
    refine ⟨⟨i, (TopCat.toSSetObjEquivT (α i) k).symm ⟨g, hg⟩⟩, ?_⟩
    apply (TopCat.toSSetObjEquivT (TopCat.of (Σ i, α i)) k).injective
    rw [Work.Bordism.toSSetObjEquiv_map_apply, Equiv.apply_symm_apply]
    refine ContinuousMap.ext fun t => ?_
    rw [ContinuousMap.comp_apply, sigmaι_hom_apply]
    exact (hfg t).symm

/-! ## The cofan of the singular simplicial set and its colimit property -/

/-- The cofan expressing that the singular simplicial set of a `σ`-type of spaces is the coproduct
of the singular simplicial sets of the pieces. -/
noncomputable def ssetSigmaCofan : Cofan (fun i => TopCat.toSSet.obj (α i)) :=
  Cofan.mk (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
    (fun i => TopCat.toSSet.map (TopCat.sigmaι α i))

/-- **The cofan `ssetSigmaCofan` is a colimiting cofan.**  The levelwise statement
`sigmaLegs_bijective` says that each evaluation is a coproduct cofan in `Type`, and colimits in a
functor category are computed pointwise (`evaluationJointlyReflectsColimits`). -/
noncomputable def ssetSigmaCofan_isColimit : IsColimit (ssetSigmaCofan α) := by
  refine evaluationJointlyReflectsColimits (K := SimplexCategoryᵒᵖ) (C := Type)
    (c := ssetSigmaCofan α) ?_
  intro k
  let F : ι → Type := fun i => (TopCat.toSSet.obj (α i)).obj k
  let c : Cofan F := Cofan.mk ((TopCat.toSSet.obj (TopCat.of (Σ i, α i))).obj k)
    (fun i => (TopCat.toSSet.map (TopCat.sigmaι α i)).app k)
  have hbij : Function.Bijective (CofanTypes.fromSigma F c.cofanTypes) := by
    rw [show CofanTypes.fromSigma F c.cofanTypes
        = fun x : (Σ i, F i) => (TopCat.toSSet.map (TopCat.sigmaι α x.1)).app k x.2 from rfl]
    exact sigmaLegs_bijective α k
  have hc : IsColimit c := (Cofan.nonempty_isColimit_iff_bijective_fromSigma c).mpr hbij |>.some
  exact (IsColimit.equivOfNatIsoOfIso
    (α := (Discrete.compNatIsoDiscrete (fun i => TopCat.toSSet.obj (α i))
      ((evaluation SimplexCategoryᵒᵖ Type).obj k)).symm)
    c (((evaluation SimplexCategoryᵒᵖ Type).obj k).mapCocone (ssetSigmaCofan α))
    (Cocone.ext (Iso.refl _) (fun j => rfl))).1 hc

/-! ## The isomorphism -/

/-- **The singular simplicial set of a `σ`-type of spaces is the coproduct of the singular
simplicial sets of the pieces.** -/
noncomputable def ssetSigmaIso :
    TopCat.toSSet.obj (TopCat.of (Σ i, α i)) ≅ ∐ (fun i => TopCat.toSSet.obj (α i)) :=
  IsColimit.coconePointUniqueUpToIso (ssetSigmaCofan_isColimit α) (colimit.isColimit _)

/-- **The isomorphism `ssetSigmaIso` is compatible with the inclusions**: it carries the inclusion
of the `i`-th piece to the `i`-th coproduct inclusion. -/
theorem ssetSigmaIso_hom_sigmaι (i : ι) :
    TopCat.toSSet.map (TopCat.sigmaι α i) ≫ (ssetSigmaIso α).hom
      = Sigma.ι (fun i => TopCat.toSSet.obj (α i)) i := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom (ssetSigmaCofan_isColimit α)
    (colimit.isColimit (Discrete.functor (fun i => TopCat.toSSet.obj (α i)))) ⟨i⟩
  simp only [ssetSigmaIso, ssetSigmaCofan, Cofan.mk_ι_app] at h ⊢
  exact h

end

end Work.ThomBordism
