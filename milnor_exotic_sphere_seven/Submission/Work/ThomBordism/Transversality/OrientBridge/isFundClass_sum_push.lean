import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.OrientBridge.isFundClass_map_homeomorph
import Submission.Work.ThomBordism.boundaryLocalGenerator

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sum of the pushed fundamental classes of a finite family is a fundamental class

If `Fam : ι → Man8` is a finite family of closed oriented `8`-manifolds and `φ : Σ i, (Fam i).pt ≃ₜ M`
is a homeomorphism, then the sum `∑ i, (φ ∘ σᵢ)_* (Fam i).c` of the pushed forward fundamental
classes is a fundamental class of `M`
(`Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push`).

The proof is the local analysis of the disjoint union of the pieces, carried out on `M`:

* the local class of a sum is the sum of the local classes (`localClassAt_sum`);
* a piece whose image does not contain the point in question contributes `0`
  (`localClassAt_homologyMap_eq_zero_of_ne`);
* the piece containing the point is the image of its own space under the **open embedding**
  `φ ∘ σᵢ` (`Homeomorph.isOpenEmbedding` composed with `Topology.IsOpenEmbedding.sigmaMk`), so it
  induces an isomorphism on local homology (`isIso_openEmbPairMap_of_isOpenEmbedding`,
  `localClassAt_naturality`), and an isomorphism carries a generator to a generator
  (`span_singleton_of_isIso`), the generator being supplied by the fundamental class field
  `Man8.c_fund`.

This is the generalisation, to an arbitrary finite index family, of the subsingleton case
`OrientBridge.isFundClass_sum_push_of_subsingleton_index`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.Transversality.OrientBridge

noncomputable section

/-- `Work.Orient.locClass` is the local class of `Work.ThomBordism.localClassAt`. -/
theorem locClass_eq_localClassAt (X : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ X).homology n) (x : X) :
    Work.Orient.locClass X n c x = Work.ThomBordism.localClassAt X n c x := rfl

/-- **The local class is additive in the global class.** -/
theorem locClass_sum {X : TopCat} (n : ℕ) (x : X) {κ : Type} [Fintype κ]
    (f : κ → (Work.Cohomology.singularChains ℤ X).homology n) :
    Work.Orient.locClass X n (∑ i, f i) x = ∑ i, Work.Orient.locClass X n (f i) x := by
  rw [locClass_eq_localClassAt]
  exact Work.ThomBordism.localClassAt_sum n x f

/-- **A morphism of `ℤ`-modules which is an isomorphism carries a generator to a generator.** -/
theorem span_singleton_of_isIso {A B : ModuleCat ℤ} (φ : A ⟶ B) [IsIso φ] (a : A)
    (h : Submodule.span ℤ {a} = ⊤) :
    Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} = ⊤ := by
  have hmap : Submodule.map (ModuleCat.Hom.hom φ) (Submodule.span ℤ {a}) =
      Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} := by
    rw [Submodule.map_span]
    simp
  have htop : Submodule.map (ModuleCat.Hom.hom φ) (⊤ : Submodule ℤ A) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr]
    exact (ModuleCat.epi_iff_surjective _).mp (IsIso.epi_of_iso φ)
  rw [← hmap, h, htop]

/-- **The image of a local class under the pair map induced by an injective map.**

This is `Work.ThomBordism.localClassAt_naturality`, written for `Work.Orient.locClass` and for the
concrete pair map `Work.ThomBordism.openEmbPairMap`. -/
theorem locClass_push_eq {X Y : TopCat} (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y)
    (hinj : Function.Injective f) {n : ℕ}
    (c : (Work.Cohomology.singularChains ℤ X).homology n) :
    Work.Orient.locClass Y n
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n c) y
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.ThomBordism.openEmbPairMap f x y hinj hxy) n))
          (Work.Orient.locClass X n c x) := by
  rw [locClass_eq_localClassAt, locClass_eq_localClassAt]
  exact Work.ThomBordism.localClassAt_naturality f x y hxy
    (Work.ThomBordism.openEmbPairMapG f x y hinj hxy)
    (Work.ThomBordism.openEmbPairMapW f x y hinj hxy) n c

/-! ## The pushed pieces -/

variable {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
variable {M : Type} [TopologicalSpace M]

/-- The `i`-th piece pushed into `M` along the homeomorphism `φ : Σ i, (Fam i).pt ≃ₜ M`. -/
abbrev pushPt (φ : (Σ i, (Fam i).pt) ≃ₜ M) (i : ι) : (Fam i).X ⟶ TopCat.of M :=
  TopCat.ofHom ⟨fun y => φ ⟨i, y⟩, φ.continuous_toFun.comp continuous_sigmaMk⟩

/-- The pushforward of the fundamental class of the `i`-th piece. -/
abbrev pushClass (φ : (Σ i, (Fam i).pt) ≃ₜ M) (i : ι) :
    (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology 8 :=
  HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of M)
    (pushPt φ i)) 8 (Fam i).c

theorem isFundClass_sum_push {ι : Type} [Fintype ι] (Fam : ι → Work.ThomBordism.Man8)
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 8)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8)))
      Work.ThomBordism.Transversality.smoothHeight M]
    [CompactSpace M] [T2Space M] (φ : (Σ i : ι, (Fam i).pt) ≃ₜ M) :
    Work.Orient.IsFundClass (TopCat.of M) 8
      (∑ i, HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of M)
        (TopCat.ofHom ⟨fun y => φ ⟨i, y⟩, φ.continuous_toFun.comp continuous_sigmaMk⟩)) 8
        (Fam i).c) := by
  intro y
  rw [locClass_eq_localClassAt]
  -- the point `y` is the image of a point of the `i₀`-th piece
  obtain ⟨w, rfl⟩ : ∃ w : Σ i, (Fam i).pt, φ w = y := ⟨φ.symm y, φ.apply_symm_apply y⟩
  obtain ⟨i₀, y₀⟩ := w
  -- the local class of the sum is the sum of the local classes
  have hsum : Work.ThomBordism.localClassAt (TopCat.of M) 8
        (∑ i, pushClass φ i) (φ ⟨i₀, y₀⟩)
      = ∑ i : ι, Work.ThomBordism.localClassAt (TopCat.of M) 8 (pushClass φ i)
          (φ ⟨i₀, y₀⟩) :=
    Work.ThomBordism.localClassAt_sum 8 _ _
  -- the pieces away from `y` contribute `0`
  have hother : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i₀ →
      Work.ThomBordism.localClassAt (TopCat.of M) 8 (pushClass φ j) (φ ⟨i₀, y₀⟩) = 0 := by
    intro j _ hj
    refine Work.ThomBordism.localClassAt_homologyMap_eq_zero_of_ne (pushPt φ j) _
      (fun z hz => ?_) 8 (Fam j).c
    have h1 : (⟨j, z⟩ : Σ i, (Fam i).pt) = ⟨i₀, y₀⟩ := φ.injective hz
    exact hj ((Sigma.mk.injEq _ _ _ _).mp h1).1
  -- the piece containing `y` contributes a generator
  have hinj : Function.Injective (pushPt φ i₀) := by
    intro a b hab
    have h1 : (⟨i₀, a⟩ : Σ i, (Fam i).pt) = ⟨i₀, b⟩ := φ.injective hab
    exact eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h1).2
  have hemb : Topology.IsOpenEmbedding (fun z : (Fam i₀).pt => pushPt φ i₀ z) :=
    (Homeomorph.isOpenEmbedding φ).comp
      (Topology.IsOpenEmbedding.sigmaMk (σ := fun i => (Fam i).pt) (i := i₀))
  have hgen : Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of M) 8
        (pushClass φ i₀) (φ ⟨i₀, y₀⟩))} = ⊤ := by
    have hfund : Submodule.span ℤ
        {Work.ThomBordism.localClassAt (Fam i₀).X 8 (Fam i₀).c y₀} = ⊤ :=
      (Fam i₀).c_fund y₀
    have hxy : pushPt φ i₀ y₀ = φ ⟨i₀, y₀⟩ := rfl
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.ThomBordism.openEmbPairMap (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy) 8) :=
      Work.ThomBordism.isIso_openEmbPairMap_of_isOpenEmbedding (f := pushPt φ i₀) (x := y₀)
        (y := φ ⟨i₀, y₀⟩) hinj hxy hemb 8
    rw [show pushClass φ i₀ = HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (Fam i₀).X (TopCat.of M) (pushPt φ i₀)) 8 (Fam i₀).c from rfl]
    rw [Work.ThomBordism.localClassAt_naturality (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hxy
      (Work.ThomBordism.openEmbPairMapG (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy)
      (Work.ThomBordism.openEmbPairMapW (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy) 8 (Fam i₀).c]
    exact span_singleton_of_isIso (HomologicalComplex.homologyMap
      (Work.ThomBordism.openEmbPairMap (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy) 8)
      (Work.ThomBordism.localClassAt (Fam i₀).X 8 (Fam i₀).c y₀) hfund
  rw [hsum, Finset.sum_eq_single i₀ hother (fun h => absurd (Finset.mem_univ i₀) h)]
  exact hgen

end

end Work.ThomBordism.Transversality.OrientBridge
