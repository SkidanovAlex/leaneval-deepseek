import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs

/-!
# A finite basic-open cover of `D(g)` along which a section of `S.X₃` lifts

Let `X` be an affine scheme and `0 → X₁ →f X₂ →g X₃ → 0` a short exact sequence of sheaves of
`𝒪_X`-modules.  For a section `y` of `X₃` over a basic open `D(g)` we construct a finite family
`f i ∈ Γ(X, ⊤)` with `D(f i) ≤ D(g)`, covering `D(g)`, and such that `y|_D(f i)` lifts to a section
of `X₂` over `D(f i)`.

The mathematical content is the standard fact that an epimorphism of sheaves of modules is
*locally* surjective: a morphism of sheaves of modules is an epimorphism iff it is surjective on
stalks, which admits local lifts on a cover.  The formal argument below is:

* `(cokernel.π S.g)` is the projection to the presheaf cokernel `Qp` of `S.g`; its sheafification is
  `Q := sheafification Qp`, and the unit `η : Qp ⟶ Q` is locally injective because it is the
  sheafification map of the underlying presheaf of abelian groups;
* the composite `πp ≫ η` is a morphism of presheaves of modules out of `S.X₃`, hence (by full
  faithfulness of the forgetful functor) defines a morphism `qq : S.X₃ ⟶ Q` of sheaves of modules;
* since `S.g ≫ qq = 0` and `S.g` is an epimorphism, `qq = 0`.  Consequently for every open `U` and
  every section `z` of `S.X₃` over `U`, `η(πp z) = 0`;
* local injectivity of `η` then produces an open cover of `U` on which `πp z` vanishes, and the
  pointwise description of the presheaf cokernel (the kernel of `(cokernel.π φ).app X` is the range
  of `φ.app X`) turns this into local lifts of `z`;
* finally, affine schemes have a basis of basic opens and `D(g)` is quasi-compact, so the local
  lifts can be refined to a finite basic-open cover.

-/

universe u

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-! ## Auxiliary lemmas -/

/-- **(G1)** Every point of a basic open `D(g)` of an affine scheme has a basic open neighbourhood
`D(f)` contained in a prescribed open `V` containing the point and contained in `D(g)`. -/
lemma exists_basicOpen_le_of_mem {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine X]
    (g : X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
    (V : X.Opens) (x : X) (hxV : x ∈ V) (hx : x ∈ X.basicOpen g) :
    ∃ f : X.presheaf.obj (Opposite.op (⊤ : X.Opens)),
      x ∈ X.basicOpen f ∧ X.basicOpen f ≤ V ∧ X.basicOpen f ≤ X.basicOpen g := by
  have hx' : x ∈ (V ⊓ X.basicOpen g : X.Opens) := ⟨hxV, hx⟩
  obtain ⟨U', hU', hxU', hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen X)) hx'
  obtain ⟨f, rfl⟩ := hU'
  exact ⟨f, hxU', hle.trans inf_le_left, hle.trans inf_le_right⟩

/-- **(G2)** A cover of a quasi-compact open set by opens has a finite subcover, indexed by
`Fin r`. -/
lemma exists_finite_iSup_of_le_iSup {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) {ι : Type u} (F : ι → X.Opens) (h : U ≤ ⨆ i, F i) :
    ∃ (r : ℕ) (a : Fin r → ι), U ≤ ⨆ i, F (a i) := by
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i => (F i : Set X)) (fun i => (F i).isOpen)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h hx)
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨t.card, fun i => ((Finset.equivFin t).symm i).1, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨(Finset.equivFin t) ⟨i, hi⟩, ?_⟩
  show x ∈ F (((Finset.equivFin t).symm ((Finset.equivFin t) ⟨i, hi⟩)).1)
  rw [Equiv.symm_apply_apply]
  exact hxi

/-- **(F1)** The cokernel of a morphism of presheaves of modules is computed pointwise: a section
of the target which is killed by the cokernel projection comes from the source. -/
lemma exists_of_cokernel_π_app_eq_zero {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M₂ M₃ : PresheafOfModules.{u} R} (φ : M₂ ⟶ M₃) (X : Cᵒᵖ) (z : M₃.obj X)
    (h : (cokernel.π φ).app X z = 0) : ∃ s : M₂.obj X, (φ.app X) s = z := by
  let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have hmap : (S.map (PresheafOfModules.evaluation R X)).Exact :=
    (ShortComplex.exact_cokernel φ).map (PresheafOfModules.evaluation R X)
  exact (ShortComplex.moduleCat_exact_iff _).mp hmap z h

/-- **(F2)** Form of local injectivity of a morphism of presheaves of abelian groups on the site of
opens of a scheme: two sections agreeing after applying `φ` agree on a neighbourhood of any point
of their common domain. -/
lemma exists_le_and_map_eq_of_localInjective {X : AlgebraicGeometry.Scheme.{u}}
    {P Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ]
    {U : X.Opens} {s t : P.obj (Opposite.op U)}
    (h : φ.app (Opposite.op U) s = φ.app (Opposite.op U) t) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      P.map (CategoryTheory.homOfLE hVU).op s = P.map (CategoryTheory.homOfLE hVU).op t := by
  have hmem := CategoryTheory.Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) φ s t h
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V, f, hf, hxV⟩ := hmem x hx
  exact ⟨V, leOfHom f, hxV, by
    rw [show CategoryTheory.homOfLE (leOfHom f) = f from rfl]
    exact hf⟩

/-- **(F2')** Module-level form of `exists_le_and_map_eq_of_localInjective`. -/
lemma exists_le_and_map_eq_of_localInjective' {X : AlgebraicGeometry.Scheme.{u}}
    {R₀ : X.Opensᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R₀} (f : M ⟶ N)
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    {U : X.Opens} {s t : M.obj (Opposite.op U)}
    (h : f.app (Opposite.op U) s = f.app (Opposite.op U) t) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      M.map (CategoryTheory.homOfLE hVU).op s = M.map (CategoryTheory.homOfLE hVU).op t :=
  exists_le_and_map_eq_of_localInjective
    ((PresheafOfModules.toPresheaf R₀).map f) h hx

/-! ## The main lemma -/

theorem exists_basicOpen_cover_with_lifts {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine X]
    (S : CategoryTheory.ShortComplex (SheafOfModules X.ringCatSheaf)) (hS : S.ShortExact)
    (g : X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
    (y : Work.DSF1.Sheaf.sectionsAt S.X₃ (X.basicOpen g)) :
    ∃ (r : ℕ) (f : Fin r → X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
      (h : ∀ i, X.basicOpen (f i) ≤ X.basicOpen g),
      (X.basicOpen g ≤ ⨆ i, X.basicOpen (f i)) ∧
      (∀ i, ∃ x : Work.DSF1.Sheaf.sectionsAt S.X₂ (X.basicOpen (f i)),
        Work.DSF1.Sheaf.sectionsMap S.g (X.basicOpen (f i)) x =
          (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).obj.map
            (CategoryTheory.homOfLE (h i)).op) y) := by
  classical
  haveI hEpi : Epi S.g := hS.epi_g
  -- ### Step 0: the presheaf cokernel of `S.g`, its sheafification, and the induced map `qq`
  let φ : (SheafOfModules.forget X.ringCatSheaf).obj S.X₂ ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj S.X₃ :=
    (SheafOfModules.forget X.ringCatSheaf).map S.g
  let πp := cokernel.π φ
  let Q : SheafOfModules X.ringCatSheaf :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj (cokernel φ)
  let η : cokernel φ ⟶ (SheafOfModules.forget X.ringCatSheaf).obj Q :=
    (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (cokernel φ)
  let qq : S.X₃ ⟶ Q := (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimage (πp ≫ η)
  have hqq : (SheafOfModules.forget X.ringCatSheaf).map qq = πp ≫ η :=
    (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage (πp ≫ η)
  have hgq : S.g ≫ qq = 0 := by
    apply (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_injective
    rw [Functor.map_comp, hqq, Functor.map_zero, ← Category.assoc, cokernel.condition φ, zero_comp]
  have hq0 : qq = 0 := (cancel_epi S.g).mp (by rw [hgq, comp_zero])
  have hπη : πp ≫ η = 0 := by rw [← hqq, hq0, Functor.map_zero]
  -- ### Step 1: `η (πp z) = 0` for every section `z` of `S.X₃`
  have hzero : ∀ (U : X.Opens)
      (z : ((SheafOfModules.forget X.ringCatSheaf).obj S.X₃).obj (Opposite.op U)),
      η.app (Opposite.op U) (πp.app (Opposite.op U) z) = 0 := by
    intro U z
    have h := congrArg (fun (f : (SheafOfModules.forget X.ringCatSheaf).obj S.X₃ ⟶
        (SheafOfModules.forget X.ringCatSheaf).obj Q) => f.app (Opposite.op U) z) hπη
    simpa using h
  -- ### Step 2: `η` is locally injective
  haveI : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) η :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (cokernel φ).presheaf))
  -- ### Step 3: for every point of `D(g)` there is a basic open neighbourhood with a lift
  have key : ∀ (x : X) (hx : x ∈ (X.basicOpen g : Set X)),
      ∃ (f : X.presheaf.obj (Opposite.op (⊤ : X.Opens))) (hfg : X.basicOpen f ≤ X.basicOpen g),
        x ∈ X.basicOpen f ∧
        ∃ s : Work.DSF1.Sheaf.sectionsAt S.X₂ (X.basicOpen f),
          Work.DSF1.Sheaf.sectionsMap S.g (X.basicOpen f) s =
            (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).obj.map
              (CategoryTheory.homOfLE hfg).op) y := by
    intro x hx
    -- (i) the image of `y` in the sheafified cokernel vanishes
    have hy : η.app (Opposite.op (X.basicOpen g)) (πp.app (Opposite.op (X.basicOpen g)) y) =
        η.app (Opposite.op (X.basicOpen g))
          (0 : (cokernel φ).obj (Opposite.op (X.basicOpen g))) := by
      rw [hzero (X.basicOpen g) y, map_zero]
    -- (ii) hence `πp y` vanishes on a neighbourhood of `x`
    obtain ⟨V, hVg, hxV, hV0⟩ := exists_le_and_map_eq_of_localInjective' η hy hx
    have hV0' : πp.app (Opposite.op V)
        (((SheafOfModules.forget X.ringCatSheaf).obj S.X₃).map
          (CategoryTheory.homOfLE hVg).op
          (show ((SheafOfModules.forget X.ringCatSheaf).obj S.X₃).obj
            (Opposite.op (X.basicOpen g)) from y)) = 0 := by
      rw [← PresheafOfModules.naturality_apply πp (CategoryTheory.homOfLE hVg).op
        (show ((SheafOfModules.forget X.ringCatSheaf).obj S.X₃).obj
          (Opposite.op (X.basicOpen g)) from y)] at hV0
      simpa using hV0
    -- (iii) lift `y|_V` to `X₂`
    obtain ⟨s, hs⟩ := exists_of_cokernel_π_app_eq_zero φ (Opposite.op V) _ hV0'
    -- (iv) shrink `V` to a basic open neighbourhood of `x`
    obtain ⟨f, hxf, hfV, hfg⟩ := exists_basicOpen_le_of_mem g V x hxV hx
    refine ⟨f, hfg, hxf, ?_⟩
    refine ⟨((SheafOfModules.forget X.ringCatSheaf).obj S.X₂).map
      (CategoryTheory.homOfLE hfV).op s, ?_⟩
    have hlift : φ.app (Opposite.op (X.basicOpen f))
        (((SheafOfModules.forget X.ringCatSheaf).obj S.X₂).map
          (CategoryTheory.homOfLE hfV).op s) =
        ((SheafOfModules.forget X.ringCatSheaf).obj S.X₃).map
          (CategoryTheory.homOfLE hfg).op y := by
      rw [PresheafOfModules.naturality_apply, hs, ← PresheafOfModules.map_comp_apply]
      rw [show (CategoryTheory.homOfLE hVg).op ≫ (CategoryTheory.homOfLE hfV).op =
          (CategoryTheory.homOfLE hfg).op from rfl]
    exact hlift
  -- ### Step 4: extract a finite subcover
  have hcomp : IsCompact ((X.basicOpen g : X.Opens) : Set X) :=
    (AlgebraicGeometry.isAffineOpen_top X).basicOpen g |>.isCompact
  have hcov : X.basicOpen g ≤ ⨆ x : {x : X // x ∈ (X.basicOpen g : Set X)},
      X.basicOpen ((key x.1 x.2).choose) := by
    intro z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨z, hz⟩, (key z hz).choose_spec.choose_spec.1⟩
  obtain ⟨r, a, ha⟩ := exists_finite_iSup_of_le_iSup (X.basicOpen g) hcomp
    (fun x : {x : X // x ∈ (X.basicOpen g : Set X)} => X.basicOpen ((key x.1 x.2).choose)) hcov
  refine ⟨r, fun i => (key (a i).1 (a i).2).choose,
    fun i => (key (a i).1 (a i).2).choose_spec.choose, ha, fun i => ?_⟩
  exact (key (a i).1 (a i).2).choose_spec.choose_spec.2

end Work.DSF1.Sheaf
