import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.relChains_free
import Submission.Work.Cohomology.cokernel_map_shortExact
import Submission.Work.Cohomology.cokernel_biprod_map_iso
import Submission.Work.Cohomology.relChains_compl_union_free
import Submission.Work.Cohomology.hmv_shortExact
import Submission.Work.Cohomology.smallLift_cov


set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section
/-! ## A vanishing criterion for a cokernel

The auxiliary statement that the middle term of the long exact sequence of a pair vanishes when
both the outer terms do. -/

/-- **If `H_{k+1}(f)` is surjective and `H_k(f)` is injective, then `H_{k+1}(coker f)` vanishes.** -/
theorem isZero_homology_coker_of_epi_mono {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L)
    (k : ℕ) [Mono f] (hepi : Epi (HomologicalComplex.homologyMap f (k+1)))
    (hmono : Mono (HomologicalComplex.homologyMap f k)) :
    IsZero ((cokernel f).homology (k+1)) := by
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) ‹Mono f› inferInstance
  have hij : (ComplexShape.down ℕ).Rel (k+1) k := by simp [ComplexShape.down]
  have hg0 : HomologicalComplex.homologyMap S.g (k+1) = 0 := by
    haveI := hepi
    rw [← cancel_epi (HomologicalComplex.homologyMap S.f (k+1)), comp_zero,
      ← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero]
  haveI hmonoδ : Mono (hS.δ (k+1) k hij) :=
    ShortComplex.Exact.mono_g (hS.homology_exact₃ (k+1) k hij) hg0
  have hδ0 : hS.δ (k+1) k hij = 0 := by
    haveI := hmono
    rw [← cancel_mono (HomologicalComplex.homologyMap S.f k), zero_comp,
      hS.δ_comp (k+1) k hij]
  refine IsZero.iff_id_eq_zero _ |>.mpr ?_
  rw [← cancel_mono (hS.δ (k+1) k hij), Category.id_comp, hδ0, zero_comp]

/-! ## The small chains of a cover of a union

For open `U, V ⊆ X` the small chains of the cover `{U,V}` of `X` are the small chains of the
induced cover `{U', V'}` of the open subspace `U ∪ V`. -/

section CoverUnion

variable {X : TopCat}

/-- `U ∪ V` as a topological space. -/
abbrev coverY (U V : Set X) : TopCat := TopCat.of ↥(U ∪ V)

/-- `U` viewed as a subset of the open subspace `U ∪ V`. -/
def smallCoverU (U V : Set X) : Set ↥(U ∪ V) := {y | (y : X) ∈ U}

/-- `V` viewed as a subset of the open subspace `U ∪ V`. -/
def smallCoverV (U V : Set X) : Set ↥(U ∪ V) := {y | (y : X) ∈ V}

/-- The small chains of the induced cover of `U ∪ V`. -/
abbrev coverChains (U V : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  smallChains (X := coverY U V) (smallCoverU U V) (smallCoverV U V)

/-- The small simplicial set of the induced cover of `U ∪ V`. -/
abbrev coverSSet (U V : Set X) : SSet :=
  smallSSet (X := coverY U V) (smallCoverU U V) (smallCoverV U V)

/-- Smallness for the induced cover of `U ∪ V`. -/
abbrev CoverSmall (U V : Set X) {k : ℕ} (τ : Simplex (coverY U V) k) : Prop :=
  IsSmall (X := coverY U V) (smallCoverU U V) (smallCoverV U V) τ

lemma isOpen_smallCoverU {U V : Set X} (hU : IsOpen U) : IsOpen (smallCoverU U V) :=
  hU.preimage continuous_subtype_val

lemma isOpen_smallCoverV {U V : Set X} (hV : IsOpen V) : IsOpen (smallCoverV U V) :=
  hV.preimage continuous_subtype_val

lemma smallCoverU_union_smallCoverV (U V : Set X) : smallCoverU U V ∪ smallCoverV U V = Set.univ := by
  ext y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  by_cases h : (y : X) ∈ U
  · exact Or.inl h
  · exact Or.inr (y.2.resolve_left h)

/-- The image of a singular simplex which is small for `(U,V)` is contained in `U ∪ V`. -/
lemma range_subset_union_of_isSmall {U V : Set X} {k : ℕ} {σ : Simplex X k}
    (h : IsSmall U V σ) :
    Set.range (fun z => (X.toSSetObjEquivT (Opposite.op ⦋k⦌)) σ z) ⊆ U ∪ V := by
  rcases h with h | h
  · exact fun y hy => Or.inl (h hy)
  · exact fun y hy => Or.inr (h hy)

/-- A small simplex of `X` lifted to a simplex of `U ∪ V`. -/
noncomputable def smallLiftSimplex (U V : Set X) (k : ℕ) (σ : (smallSSet U V) _⦋k⦌) :
    Simplex (coverY U V) k :=
  Classical.choose (exists_map_inclUX_of_range_subset (U ∪ V) (Opposite.op ⦋k⦌) σ.1
    (range_subset_union_of_isSmall σ.2))

lemma smallLiftSimplex_spec (U V : Set X) (k : ℕ) (σ : (smallSSet U V) _⦋k⦌) :
    (TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌)
      (smallLiftSimplex U V k σ) = σ.1 :=
  Classical.choose_spec (exists_map_inclUX_of_range_subset (U ∪ V) (Opposite.op ⦋k⦌) σ.1
    (range_subset_union_of_isSmall σ.2))

/-- The inclusion of `U ∪ V` into `X` is injective on simplices. -/
lemma map_subtypeIncl_injective (U V : Set X) (k : ℕ) :
    Function.Injective ((TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌)) := by
  intro a b hab
  have hfun : (coverY U V).toSSetObjEquivT (Opposite.op ⦋k⦌) a
      = (coverY U V).toSSetObjEquivT (Opposite.op ⦋k⦌) b := by
    ext z
    have h3 := DFunLike.congr_fun (congrArg (fun s => X.toSSetObjEquivT (Opposite.op ⦋k⦌) s) hab) z
    rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_map_apply] at h3
    exact h3
  exact (TopCat.toSSetObjEquivT (coverY U V) (Opposite.op ⦋k⦌)).injective hfun

/-- The lift of a small simplex is small for the induced cover of `U ∪ V`. -/
lemma isSmall_liftSimplex (U V : Set X) (k : ℕ) (σ : (smallSSet U V) _⦋k⦌) :
    CoverSmall U V (smallLiftSimplex U V k σ) := by
  change IsSmall (X := coverY U V) (smallCoverU U V) (smallCoverV U V)
    (smallLiftSimplex U V k σ)
  rw [isSmall_iff]
  rcases (isSmall_iff σ.1).mp σ.2 with h | h
  · left
    rintro y ⟨z, rfl⟩
    have h1 : sdMap k ((TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌)
        (smallLiftSimplex U V k σ)) z = sdMap k σ.1 z := by
      rw [smallLiftSimplex_spec]
    have h2 : sdMap k ((TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌)
        (smallLiftSimplex U V k σ)) z
          = ((sdMap k (smallLiftSimplex U V k σ) z : ↥(U ∪ V)) : X) := by
      rw [sdMap_map]
      rfl
    show ((sdMap k (smallLiftSimplex U V k σ) z : ↥(U ∪ V)) : X) ∈ U
    rw [← h2, h1]
    exact h ⟨z, rfl⟩
  · right
    rintro y ⟨z, rfl⟩
    have h1 : sdMap k ((TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌)
        (smallLiftSimplex U V k σ)) z = sdMap k σ.1 z := by
      rw [smallLiftSimplex_spec]
    have h2 : sdMap k ((TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌)
        (smallLiftSimplex U V k σ)) z
          = ((sdMap k (smallLiftSimplex U V k σ) z : ↥(U ∪ V)) : X) := by
      rw [sdMap_map]
      rfl
    show ((sdMap k (smallLiftSimplex U V k σ) z : ↥(U ∪ V)) : X) ∈ V
    rw [← h2, h1]
    exact h ⟨z, rfl⟩

/-- A simplex of `U ∪ V` which is small for the induced cover is small for `(U,V)` in `X`. -/
lemma isSmall_map_subtypeIncl {U V : Set X} {k : ℕ} {τ : Simplex (coverY U V) k}
    (h : CoverSmall U V τ) :
    IsSmall U V ((TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌) τ) := by
  change IsSmall (X := coverY U V) (smallCoverU U V) (smallCoverV U V) τ at h
  rw [isSmall_iff] at h ⊢
  have hmap : ∀ z : (Delta k : TopCat),
      sdMap k ((TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋k⦌) τ) z
        = ((sdMap k τ z : ↥(U ∪ V)) : X) := by
    intro z
    rw [sdMap_map]
    rfl
  rw [funext hmap]
  rcases h with h | h
  · left
    rintro y ⟨z, rfl⟩
    exact h ⟨z, rfl⟩
  · right
    rintro y ⟨z, rfl⟩
    exact h ⟨z, rfl⟩

/-- A morphism of the chains of a simplicial set is determined by its values on generators. -/
lemma eq_of_gen_SSet {Y : SSet} {n : ℕ} {M : ModuleCat ℤ}
    {f g : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶ M}
    (h : ∀ σ : Y _⦋n⦌, ModuleCat.Hom.hom f (genSSet Y n σ) = ModuleCat.Hom.hom g (genSSet Y n σ)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have htop : LinearMap.ker (ModuleCat.Hom.hom f - ModuleCat.Hom.hom g) = ⊤ := by
    apply Ct.mem_of_gen_SSet (Y := Y) (n := n)
    intro σ
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h σ
  have hc := Submodule.eq_top_iff'.mp htop c
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using hc

/-- The inclusion of the small chains of the induced cover of `U ∪ V` into the chains of
`U ∪ V`. -/
abbrev coverToSing (U V : Set X) : coverChains U V ⟶ singularChains ℤ (coverY U V) :=
  smallToSing (X := coverY U V) (smallCoverU U V) (smallCoverV U V)

/-- The inclusion of the chains of `U ∪ V` into the chains of `X`. -/
abbrev coverIncl (U V : Set X) : singularChains ℤ (coverY U V) ⟶ singularChains ℤ X :=
  inclChains X (U ∪ V)

/-- The map on small chains induced by the inclusion `U ∪ V ⊆ X`, in the forward direction. -/
noncomputable def smallChainsToCoverHom (U V : Set X) (n : ℕ) :
    (smallChains U V).X n ⟶ (coverChains U V).X n :=
  Cofan.IsColimit.desc ((smallSSet U V).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ : (smallSSet U V) _⦋n⦌ =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
        (genSSet (coverSSet U V) n ⟨smallLiftSimplex U V n σ, isSmall_liftSimplex U V n σ⟩)))

lemma smallChainsToCoverHom_gen (U V : Set X) (n : ℕ) (σ : (smallSSet U V) _⦋n⦌) :
    ModuleCat.Hom.hom (smallChainsToCoverHom U V n) (genSSet (smallSSet U V) n σ)
      = genSSet (coverSSet U V) n ⟨smallLiftSimplex U V n σ, isSmall_liftSimplex U V n σ⟩ := by
  have h := Cofan.IsColimit.fac
    ((smallSSet U V).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ : (smallSSet U V) _⦋n⦌ =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
        (genSSet (coverSSet U V) n ⟨smallLiftSimplex U V n σ, isSmall_liftSimplex U V n σ⟩))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (coverChains U V).X n) =>
    ModuleCat.Hom.hom g (1 : ℤ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  rw [smallChainsToCoverHom]
  exact h2

/-- The map on small chains induced by the inclusion `U ∪ V ⊆ X`, in the backward direction. -/
noncomputable def smallChainsOfCoverHom (U V : Set X) (n : ℕ) :
    (coverChains U V).X n ⟶ (smallChains U V).X n :=
  Cofan.IsColimit.desc ((coverSSet U V).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun τ : (coverSSet U V) _⦋n⦌ =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (genSSet (smallSSet U V) n
        ⟨(TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋n⦌) τ.1,
          isSmall_map_subtypeIncl τ.2⟩)))

lemma smallChainsOfCoverHom_gen (U V : Set X) (n : ℕ) (τ : (coverSSet U V) _⦋n⦌) :
    ModuleCat.Hom.hom (smallChainsOfCoverHom U V n) (genSSet (coverSSet U V) n τ)
      = genSSet (smallSSet U V) n
          ⟨(TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋n⦌) τ.1,
            isSmall_map_subtypeIncl τ.2⟩ := by
  have h := Cofan.IsColimit.fac
    ((coverSSet U V).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun τ : (coverSSet U V) _⦋n⦌ =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (genSSet (smallSSet U V) n
        ⟨(TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋n⦌) τ.1,
          isSmall_map_subtypeIncl τ.2⟩))) τ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (smallChains U V).X n) =>
    ModuleCat.Hom.hom g (1 : ℤ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  rw [smallChainsOfCoverHom]
  exact h2

/-- The two comparisons are mutually inverse (forward-backward). -/
lemma smallChainsToCoverHom_comp_ofCoverHom (U V : Set X) (n : ℕ) :
    smallChainsToCoverHom U V n ≫ smallChainsOfCoverHom U V n = 𝟙 ((smallChains U V).X n) := by
  apply eq_of_gen_SSet (Y := smallSSet U V) (n := n)
  intro σ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, smallChainsToCoverHom_gen,
    smallChainsOfCoverHom_gen]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]
  congr 1
  exact Subtype.ext (smallLiftSimplex_spec U V n σ)

/-- The two comparisons are mutually inverse (backward-forward). -/
lemma smallChainsOfCoverHom_comp_toCoverHom (U V : Set X) (n : ℕ) :
    smallChainsOfCoverHom U V n ≫ smallChainsToCoverHom U V n = 𝟙 ((coverChains U V).X n) := by
  apply eq_of_gen_SSet (Y := coverSSet U V) (n := n)
  intro τ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, smallChainsOfCoverHom_gen,
    smallChainsToCoverHom_gen]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]
  congr 1
  apply Subtype.ext
  exact map_subtypeIncl_injective U V n
    (smallLiftSimplex_spec U V n
      ⟨(TopCat.toSSet.map (subtypeIncl X (U ∪ V))).app (Opposite.op ⦋n⦌) τ.1,
        isSmall_map_subtypeIncl τ.2⟩)

/-- The forward comparison is compatible with the inclusions of the small chains. -/
lemma smallChainsToCoverHom_comp_smallToSing (U V : Set X) (n : ℕ) :
    smallChainsToCoverHom U V n ≫ (coverToSing U V).f n ≫ (coverIncl U V).f n
      = (smallToSing U V).f n := by
  apply eq_of_gen_SSet (Y := smallSSet U V) (n := n)
  intro σ
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    smallChainsToCoverHom_gen, smallToSing_gen, inclChains_gen, smallToSing_gen]
  congr 1
  exact smallLiftSimplex_spec U V n σ

/-- The backward comparison is compatible with the inclusions of the small chains. -/
lemma smallChainsOfCoverHom_comp_smallToSing (U V : Set X) (n : ℕ) :
    smallChainsOfCoverHom U V n ≫ (smallToSing U V).f n
      = (coverToSing U V).f n ≫ (coverIncl U V).f n := by
  apply eq_of_gen_SSet (Y := coverSSet U V) (n := n)
  intro τ
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    smallChainsOfCoverHom_gen, smallToSing_gen, smallToSing_gen, inclChains_gen]
  simp only [simplexMap]

/-- The forward comparison is a chain map. -/
lemma smallChainsToCoverHom_comm (U V : Set X) (i j : ℕ) :
    smallChainsToCoverHom U V i ≫ (coverChains U V).d i j
      = (smallChains U V).d i j ≫ smallChainsToCoverHom U V j := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hinj : Function.Injective
      (fun y => ((coverIncl U V).f j).hom (((coverToSing U V).f j).hom y)) := by
    intro a b hab
    exact smallToSing_f_injective (X := coverY U V) (smallCoverU U V) (smallCoverV U V) j
      (injective_chainComplexMap_subtypeIncl X (U ∪ V) j hab)
  apply hinj
  show ((coverIncl U V).f j).hom (((coverToSing U V).f j).hom
        (((coverChains U V).d i j).hom ((smallChainsToCoverHom U V i).hom x)))
    = ((coverIncl U V).f j).hom (((coverToSing U V).f j).hom
        ((smallChainsToCoverHom U V j).hom (((smallChains U V).d i j).hom x)))
  have h1 : ((coverToSing U V).f j).hom
        (((coverChains U V).d i j).hom ((smallChainsToCoverHom U V i).hom x))
      = (((singularChains ℤ (coverY U V)).d i j).hom)
        (((coverToSing U V).f i).hom ((smallChainsToCoverHom U V i).hom x)) := by
    have h := congrArg (fun (φ : (coverChains U V).X i ⟶
        (singularChains ℤ (coverY U V)).X j) => φ.hom ((smallChainsToCoverHom U V i).hom x))
      (HomologicalComplex.Hom.comm (coverToSing U V) i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
  have h2 : ((coverIncl U V).f j).hom
        ((((singularChains ℤ (coverY U V)).d i j).hom)
          (((coverToSing U V).f i).hom ((smallChainsToCoverHom U V i).hom x)))
      = ((singularChains ℤ X).d i j).hom (((coverIncl U V).f i).hom
          (((coverToSing U V).f i).hom ((smallChainsToCoverHom U V i).hom x))) := by
    have h := congrArg (fun (φ : (singularChains ℤ (coverY U V)).X i ⟶
        (singularChains ℤ X).X j) => φ.hom
          (((coverToSing U V).f i).hom ((smallChainsToCoverHom U V i).hom x)))
      (HomologicalComplex.Hom.comm (coverIncl U V) i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
  have h3 : ((coverIncl U V).f i).hom
        (((coverToSing U V).f i).hom ((smallChainsToCoverHom U V i).hom x))
      = ((smallToSing U V).f i).hom x := by
    have h := congrArg (fun (φ : (smallChains U V).X i ⟶ (singularChains ℤ X).X i) =>
      φ.hom x) (smallChainsToCoverHom_comp_smallToSing U V i)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have h4 : ((singularChains ℤ X).d i j).hom (((smallToSing U V).f i).hom x)
      = ((smallToSing U V).f j).hom (((smallChains U V).d i j).hom x) := by
    have h := congrArg (fun (φ : (smallChains U V).X i ⟶ (singularChains ℤ X).X j) =>
      φ.hom x) (HomologicalComplex.Hom.comm (smallToSing U V) i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have h5 : ((smallToSing U V).f j).hom (((smallChains U V).d i j).hom x)
      = ((coverIncl U V).f j).hom (((coverToSing U V).f j).hom
          ((smallChainsToCoverHom U V j).hom (((smallChains U V).d i j).hom x))) := by
    have h := congrArg (fun (φ : (smallChains U V).X j ⟶ (singularChains ℤ X).X j) =>
      φ.hom (((smallChains U V).d i j).hom x))
      (smallChainsToCoverHom_comp_smallToSing U V j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
  rw [h1, h2, h3, h4, h5]

/-- The backward comparison is a chain map. -/
lemma smallChainsOfCoverHom_comm (U V : Set X) (i j : ℕ) :
    smallChainsOfCoverHom U V i ≫ (smallChains U V).d i j
      = (coverChains U V).d i j ≫ smallChainsOfCoverHom U V j := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hinj : Function.Injective (fun y => ((smallToSing U V).f j).hom y) :=
    smallToSing_f_injective U V j
  apply hinj
  show ((smallToSing U V).f j).hom
        (((smallChains U V).d i j).hom ((smallChainsOfCoverHom U V i).hom x))
    = ((smallToSing U V).f j).hom
        ((smallChainsOfCoverHom U V j).hom (((coverChains U V).d i j).hom x))
  have h1 : ((smallToSing U V).f j).hom
        (((smallChains U V).d i j).hom ((smallChainsOfCoverHom U V i).hom x))
      = ((singularChains ℤ X).d i j).hom
        (((smallToSing U V).f i).hom ((smallChainsOfCoverHom U V i).hom x)) := by
    have h := congrArg (fun (φ : (smallChains U V).X i ⟶ (singularChains ℤ X).X j) =>
      φ.hom ((smallChainsOfCoverHom U V i).hom x))
      (HomologicalComplex.Hom.comm (smallToSing U V) i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
  have h2 : ((smallToSing U V).f i).hom ((smallChainsOfCoverHom U V i).hom x)
      = ((coverIncl U V).f i).hom (((coverToSing U V).f i).hom x) := by
    have h := congrArg (fun (φ : (coverChains U V).X i ⟶ (singularChains ℤ X).X i) =>
      φ.hom x) (smallChainsOfCoverHom_comp_smallToSing U V i)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have h3 : ((singularChains ℤ X).d i j).hom
        (((coverIncl U V).f i).hom (((coverToSing U V).f i).hom x))
      = ((coverIncl U V).f j).hom
        ((((singularChains ℤ (coverY U V)).d i j).hom) (((coverToSing U V).f i).hom x)) := by
    have h := congrArg (fun (φ : (singularChains ℤ (coverY U V)).X i ⟶
        (singularChains ℤ X).X j) => φ.hom (((coverToSing U V).f i).hom x))
      (HomologicalComplex.Hom.comm (coverIncl U V) i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have h4 : (((singularChains ℤ (coverY U V)).d i j).hom) (((coverToSing U V).f i).hom x)
      = ((coverToSing U V).f j).hom (((coverChains U V).d i j).hom x) := by
    have h := congrArg (fun (φ : (coverChains U V).X i ⟶
        (singularChains ℤ (coverY U V)).X j) => φ.hom x)
      (HomologicalComplex.Hom.comm (coverToSing U V) i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have h5 : ((coverIncl U V).f j).hom
        (((coverToSing U V).f j).hom (((coverChains U V).d i j).hom x))
      = ((smallToSing U V).f j).hom
        ((smallChainsOfCoverHom U V j).hom (((coverChains U V).d i j).hom x)) := by
    have h := congrArg (fun (φ : (coverChains U V).X j ⟶ (singularChains ℤ X).X j) =>
      φ.hom (((coverChains U V).d i j).hom x))
      (smallChainsOfCoverHom_comp_smallToSing U V j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
  rw [h1, h2, h3, h4, h5]

/-- **The small chains of the cover `{U,V}` of `X` are the small chains of the induced cover of
`U ∪ V`.** -/
noncomputable def smallChainsCoverIso (U V : Set X) : smallChains U V ≅ coverChains U V where
  hom := HomologicalComplex.Hom.mk (smallChainsToCoverHom U V)
    (fun i j _ => smallChainsToCoverHom_comm U V i j)
  inv := HomologicalComplex.Hom.mk (smallChainsOfCoverHom U V)
    (fun i j _ => smallChainsOfCoverHom_comm U V i j)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro i
    exact smallChainsToCoverHom_comp_ofCoverHom U V i
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro i
    exact smallChainsOfCoverHom_comp_toCoverHom U V i


end CoverUnion

/-! ## A subgroup of a free `ℤ`-module is free

The transfer lemma used in the final step: if `f : M →ₗ[ℤ] N` is injective and `N` is a free
`ℤ`-module, then so is `M` (it is a module isomorphic to the submodule `range f ≤ N`).
The statement is stated with the `Submodule.module` instance on the range, which is the one used
by `LinearEquiv.ofInjective`; the two module structures on a submodule over `ℤ` are equal because
a `ℤ`-module structure on an additive group is unique. -/

/-- **A `ℤ`-submodule of a free `ℤ`-module is free**, in the `Submodule.module` flavour of the
range, which is the one produced by `LinearEquiv.ofInjective`. -/
theorem free_range_of_free' {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] [Module.Free ℤ N] (f : M →ₗ[ℤ] N) :
    @Module.Free ℤ ↥(LinearMap.range f) Int.instSemiring (LinearMap.range f).addCommMonoid
      (Submodule.module (LinearMap.range f)) := by
  rw [show Submodule.module (LinearMap.range f) = AddCommGroup.toIntModule ↥(LinearMap.range f)
    from Subsingleton.elim _ _]
  exact free_submodule_of_free_int (LinearMap.range f)

/-- **A subgroup of a free `ℤ`-module is free**: an injective `ℤ`-linear map into a free module has
free domain. -/
theorem free_of_injective_int' {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] [Module.Free ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Injective f) :
    Module.Free ℤ M := by
  letI : Module ℤ ↥(LinearMap.range f) := Submodule.module (LinearMap.range f)
  exact Module.Free.of_equiv' (free_range_of_free' f) (LinearEquiv.ofInjective f hf).symm

/-! ## The quotient by the small chains of a two-element cover -/

/-- **The quotient of the chains of `X` by the small chains of the open cover `{U,V}` computes the
relative homology of the complement of the union.**

Writing `W := U ∪ V`, the small chains of the cover `{U,V}` of `X` are the small chains of the
induced cover of the open subspace `W` (`smallChainsCoverIso`), so the natural comparison map `F`
from the former to the chains of `W` satisfies `F ≫ coverIncl U V = smallToSing U V` and is a
quasi-isomorphism.  The long exact sequences of the pair sequences of `coverIncl U V` and of
`F ≫ coverIncl U V` then show that `H_{k+1}` of `coker (smallToSing U V)` vanishes as soon as
`H_{k+1}(X, W) = H_{k+1}(relChains X (U ∪ V))` does. -/
theorem isZero_coker_smallToSing_of_isZero_relChains {X : TopCat} (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (k : ℕ)
    (h : CategoryTheory.Limits.IsZero ((relChains X (U ∪ V)).homology (k+1))) :
    CategoryTheory.Limits.IsZero
      ((CategoryTheory.Limits.cokernel (smallToSing U V)).homology (k+1)) := by
  let F : smallChains U V ⟶ singularChains ℤ (coverY U V) :=
    (smallChainsCoverIso U V).hom ≫ coverToSing U V
  have hF_eq : F = (smallChainsCoverIso U V).hom ≫ coverToSing U V := rfl
  have hFg : F ≫ coverIncl U V = smallToSing U V := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact smallChainsToCoverHom_comp_smallToSing U V n
  haveI hcts : Mono (coverToSing U V) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr
      (smallToSing_f_injective (X := coverY U V) (smallCoverU U V) (smallCoverV U V) n)
  haveI hcincl : Mono (coverIncl U V) := mono_chainMap_subtypeIncl X (U ∪ V)
  have hmapF : ∀ n, HomologicalComplex.homologyMap F n
      = HomologicalComplex.homologyMap ((smallChainsCoverIso U V).hom) n
        ≫ HomologicalComplex.homologyMap (coverToSing U V) n := by
    intro n
    rw [hF_eq, HomologicalComplex.homologyMap_comp]
  have hisoF : ∀ n, IsIso (HomologicalComplex.homologyMap F n) := by
    intro n
    haveI h1 : IsIso (HomologicalComplex.homologyMap ((smallChainsCoverIso U V).hom) n) :=
      Iso.isIso_hom ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (smallChainsCoverIso U V))
    haveI h2 : IsIso (HomologicalComplex.homologyMap (coverToSing U V) n) :=
      smallChains_homology_iso (X := coverY U V) (smallCoverU U V) (smallCoverV U V)
        (isOpen_smallCoverU hU) (isOpen_smallCoverV hV) (smallCoverU_union_smallCoverV U V) n
    rw [hmapF n]
    infer_instance
  -- `H_{k+1}` and `H_k` of the inclusion `coverIncl U V`
  have hij : (ComplexShape.down ℕ).Rel (k+1) k := by simp [ComplexShape.down]
  have hSg : (ShortComplex.mk (coverIncl U V) (cokernel.π (coverIncl U V))
      (cokernel.condition (coverIncl U V))).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  haveI hepig : Epi (HomologicalComplex.homologyMap (coverIncl U V) (k+1)) :=
    ShortComplex.Exact.epi_f (hSg.homology_exact₂ (k+1)) (IsZero.eq_zero_of_tgt h _)
  haveI hmonog : Mono (HomologicalComplex.homologyMap (coverIncl U V) k) :=
    ShortComplex.Exact.mono_g (hSg.homology_exact₁ (k+1) k hij) (IsZero.eq_zero_of_src h _)
  have hmapFg : ∀ n, HomologicalComplex.homologyMap (F ≫ coverIncl U V) n
      = HomologicalComplex.homologyMap F n ≫ HomologicalComplex.homologyMap (coverIncl U V) n := by
    intro n
    rw [HomologicalComplex.homologyMap_comp]
  haveI hepiFg : Epi (HomologicalComplex.homologyMap (F ≫ coverIncl U V) (k+1)) := by
    rw [hmapFg]
    haveI := hisoF (k+1)
    infer_instance
  haveI hmonoFg : Mono (HomologicalComplex.homologyMap (F ≫ coverIncl U V) k) := by
    rw [hmapFg]
    haveI := hisoF k
    infer_instance
  have hres := isZero_homology_coker_of_epi_mono (F ≫ coverIncl U V) k hepiFg hmonoFg
  rwa [hFg] at hres

/-- **The Mayer–Vietoris injection for the excluded-set functor.**

For any subsets `U, V` of a topological space `X` there is a short exact sequence of chain complexes
`0 ⟶ C_*(X)/(C_*(U) + C_*(V)) → C_*(X)/C_*(U) ⊞ C_*(X)/C_*(V) ⟶ coker (smallToSing U V) ⟶ 0`
(the "A+B" sequence, obtained from the Mayer–Vietoris short exact sequence `mvShort U V` — which
carries no hypotheses — by the snake lemma for the morphism `mvToTrivial U V` into the split
sequence `trivialShort X`).  Its long exact sequence in degree `k` reads
`H_{k+1}(coker (smallToSing U V)) → H_k(C_*(X)/(C_*(U)+C_*(V))) → H_k(C_*(X)/C_*(U)) ⊞ …`, and
`C_*(X)/(C_*(U) + C_*(V))` is `coker (smallToSing U V)` while `C_*(X)/C_*(U)` and `C_*(X)/C_*(V)`
are `relChains X U` and `relChains X V`.  Hence vanishing of `H_{k+1}(coker (smallToSing U V))`
makes the Mayer–Vietoris map
`H_k(relChains X (U ∩ V)) → H_k(relChains X U) ⊞ H_k(relChains X V)` injective. -/
theorem exists_injective_relChains_union {X : TopCat} (U V : Set X) (k : ℕ)
    (h : CategoryTheory.Limits.IsZero
      ((CategoryTheory.Limits.cokernel (smallToSing U V)).homology (k+1))) :
    ∃ f : ↥((relChains X (U ∩ V)).homology k) →ₗ[ℤ]
          ↥(CategoryTheory.Limits.biprod ((relChains X U).homology k)
             ((relChains X V).homology k)),
      Function.Injective f := by
  haveI hmonoU : Mono (inclChains X U) := mono_chainMap_subtypeIncl X U
  haveI hmonoV : Mono (inclChains X V) := mono_chainMap_subtypeIncl X V
  haveI hmono1 : Mono ((mvToTrivial U V).τ₁) := mono_chainMap_subtypeIncl X (U ∩ V)
  haveI hmono2 : Mono ((mvToTrivial U V).τ₂) := biprod.map_mono _ _
  haveI hmono3 : Mono ((mvToTrivial U V).τ₃) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr (smallToSing_f_injective U V n)
  obtain ⟨f, g', hfg, hSE⟩ := cokernel_map_shortExact (mvShort_shortExact U V)
    (trivialShort_shortExact X) (mvToTrivial U V) hmono1 hmono2 hmono3
  let E : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    { X₁ := cokernel ((mvToTrivial U V).τ₁), X₂ := cokernel ((mvToTrivial U V).τ₂),
      X₃ := cokernel ((mvToTrivial U V).τ₃), f := f, g := g', zero := hfg }
  have hE : E.ShortExact := hSE
  have hij : (ComplexShape.down ℕ).Rel (k+1) k := by simp [ComplexShape.down]
  haveI hmono : Mono (HomologicalComplex.homologyMap E.f k) :=
    ShortComplex.Exact.mono_g (hE.homology_exact₁ (k+1) k hij) (IsZero.eq_zero_of_src h _)
  obtain ⟨e₂⟩ := cokernel_biprod_map_iso (inclChains X U) (inclChains X V)
  obtain ⟨e₃⟩ := homology_biprod_iso_chain (cokernel (inclChains X U)) (cokernel (inclChains X V)) k
  have eFull : E.X₂.homology k
      ≅ (cokernel (inclChains X U)).homology k ⊞ (cokernel (inclChains X V)).homology k :=
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso e₂).trans e₃
  refine ⟨eFull.toLinearEquiv.toLinearMap.comp
    (HomologicalComplex.homologyMap E.f k).hom, ?_⟩
  exact eFull.toLinearEquiv.injective.comp
    ((ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap E.f k)).mp hmono)

/-- **Mayer–Vietoris for the top relative homology of the complement of a union.**

Write `F(X) := (relChains M Xᶜ).homology N` for the relative homology `H_N(M, M∖X)` of the
"excluded set" `X` (contravariant in `X`).  For closed `A B ⊆ M` with `A ∩ B` compact, the
Mayer–Vietoris sequence of the excluded-set functor gives an injection
`F(A∪B) ↪ F(A) ⊞ F(B)` (via the connecting map from `F(A∩B)[N+1]`, which vanishes because `A∩B`
is compact), so freeness of `F(A)` and `F(B)` implies that of `F(A∪B)`.

Roadmap.  Put `S := Aᶜ`, `T := Bᶜ` (open, since `A B` are closed), so that `S ∩ T = (A∪B)ᶜ` and
`S ∪ T = (A∩B)ᶜ`, and write `C_S ⊆ C_M` for the subcomplex of chains supported in `S`.

1. **The "A+B" short exact sequence of chain complexes** (purely algebraic, no hypotheses):
   `0 → C_M/C_{S∩T} → C_M/C_S ⊞ C_M/C_T → C_M/(C_S+C_T) → 0`,
   with the diagonal `[x] ↦ ([x],[x])` and the difference `([x],[y]) ↦ [x-y]`.  Monomorphy and
   epimorphy are immediate, and the kernel of the difference map is the image of the diagonal:
   if `x - y ∈ C_S + C_T`, say `x - y = s + t` with `s ∈ C_S`, `t ∈ C_T`, then
   `([x],[y]) = ([x-s],[y+t])` with `x - s = y + t`.  (This is the abelian-category statement
   "cokernels of a monomorphism of short exact sequences", obtainable from
   `Work.Cohomology.shortExact_cokernel_map` (in `pd_triple.lean`, reachable through
   `relChainsPairModel`) applied to `C_S ⊞ C_T --sum--> C_S + C_T --incl--> C_M`, or from
   Mathlib's snake lemma; alternatively prove it directly by hand as in `shortExact_cokernel_map`.)
2. **Acyclicity of the small-chains quotient.**  The natural map
   `C_M/(C_S+C_T) → C_M/C_{S∪T}` is a quasi-isomorphism: its kernel is
   `C_{S∪T}/(C_S+C_T)`, which is the quotient of the chains of the space `X := S ∪ T` by the
   "small chains" of the open cover `{S, T}` of `X`, and that quotient is acyclic by
   `Work.Cohomology.smallChains_homology_iso` (the long exact sequence of
   `0 → C^{S,T} → C_*(X) → C_*(X)/C^{S,T} → 0` shows that all homology of the quotient vanishes,
   since the inclusion of the small chains is a quasi-isomorphism).  Hence for every `n`
   `H_n(C_M/(C_S+C_T)) ≅ H_n(C_M/C_{S∪T}) = F(A∩B)ₙ`.
3. **Vanishing.**  `H_{N+1}(C_M/C_{S∪T}) = F(A∩B)[N+1] = 0` because `A ∩ B` is compact
   (`Work.Cohomology.relChains_vanishing_of_compact`, which gives `H_i(M, Xᶜ) = 0` for `i > N`).
4. **Conclusion.**  The long exact sequence of the short exact sequence of step 1 in degree `N`
   reads `H_{N+1}(C_M/(C_S+C_T)) → F(A∪B) → H_N(C_M/C_S ⊞ C_M/C_T) → H_N(C_M/(C_S+C_T))`; the
   first term is `0` by steps 2 and 3, so `F(A∪B) → F(A) ⊞ F(B)` is injective (identifying
   `H_n(X ⊞ Y) ≅ H_n(X) ⊞ H_n(Y)`, cf. `Work.Cohomology.homology_biprod_iso`).
5. Finally `↥(F(A) ⊞ F(B))` is a free `ℤ`-module (as the biproduct is the product, or via an
   explicit isomorphism to `↥(F(A)) × ↥(F(B))` and `Module.Free.prod`), and a subgroup of a free
   `ℤ`-module is free (`Work.Cohomology.free_submodule_of_free_int`), which gives the claim. -/
theorem relChains_compl_union_free_of_compact_inter {N : ℕ} (hN : 1 ≤ N) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (hABc : IsCompact (A ∩ B))
    (hFA : Module.Free ℤ ↥((Work.Cohomology.relChains M Aᶜ).homology N))
    (hFB : Module.Free ℤ ↥((Work.Cohomology.relChains M Bᶜ).homology N)) :
    Module.Free ℤ ↥((Work.Cohomology.relChains M (A ∪ B)ᶜ).homology N) := by
  have hAopen : IsOpen Aᶜ := hA.isOpen_compl
  have hBopen : IsOpen Bᶜ := hB.isOpen_compl
  have h0 : IsZero ((relChains M (Aᶜ ∪ Bᶜ)).homology (N + 1)) := by
    have hh := relChains_vanishing_of_compact hN (A ∩ B) hABc (N + 1) (by omega)
    rwa [Set.compl_inter] at hh
  have hX3 : IsZero ((cokernel (smallToSing Aᶜ Bᶜ)).homology (N + 1)) :=
    isZero_coker_smallToSing_of_isZero_relChains Aᶜ Bᶜ hAopen hBopen N h0
  obtain ⟨f, hf⟩ := exists_injective_relChains_union (X := M) Aᶜ Bᶜ N hX3
  haveI hP : Module.Free ℤ ↥((relChains M Aᶜ).homology N) := hFA
  haveI hQ : Module.Free ℤ ↥((relChains M Bᶜ).homology N) := hFB
  -- the biproduct of two free `ℤ`-modules is free, via the split short exact sequence
  -- `0 → F(A) → F(A) ⊞ F(B) → F(B) → 0`
  let S' : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (biprod.inl : (relChains M Aᶜ).homology N ⟶
        (relChains M Aᶜ).homology N ⊞ (relChains M Bᶜ).homology N)
      (biprod.snd : (relChains M Aᶜ).homology N ⊞ (relChains M Bᶜ).homology N ⟶
        (relChains M Bᶜ).homology N) biprod.inl_snd
  have hS' : S'.ShortExact :=
    ShortComplex.Splitting.shortExact
      { r := (biprod.fst : (relChains M Aᶜ).homology N ⊞ (relChains M Bᶜ).homology N ⟶
          (relChains M Aᶜ).homology N)
        s := (biprod.inr : (relChains M Bᶜ).homology N ⟶
          (relChains M Aᶜ).homology N ⊞ (relChains M Bᶜ).homology N)
        f_r := biprod.inl_fst
        s_g := biprod.inr_snd
        id := biprod.total }
  haveI hbip : Module.Free ℤ
      ↥((relChains M Aᶜ).homology N ⊞ (relChains M Bᶜ).homology N) :=
    ModuleCat.free_shortExact hS'
  have hfree : Module.Free ℤ ↥((relChains M (Aᶜ ∩ Bᶜ)).homology N) :=
    free_of_injective_int' f hf
  rw [Set.compl_union]
  exact hfree

end

end Work.Cohomology
