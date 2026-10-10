import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

namespace NK.RepresentationTheory.GroupCohomology

open CategoryTheory CategoryTheory.Limits groupCohomology

noncomputable section

variable {k G : Type} [CommRing k] [Group G]

section PiRep

variable {ι : Type}

/-- The pointwise product representation: `G` acts on `∀ i, (M i).V` componentwise. -/
noncomputable def piRep (M : ι → Rep.{0,0,0} k G) : Rep.{0,0,0} k G :=
  Rep.of ({ toFun := fun g => LinearMap.pi (fun i => (M i).ρ g ∘ₗ LinearMap.proj i)
            map_one' := by ext x i; simp
            map_mul' := by intro g h; ext x i; simp [LinearMap.pi_apply] }
          : Representation k G (∀ i, (M i).V))

@[simp] theorem piRep_ρ_apply (M : ι → Rep.{0,0,0} k G) (g : G) (x : ∀ i, (M i).V) (i : ι) :
    (piRep M).ρ g x i = (M i).ρ g (x i) := rfl

/-- Evaluation at `i` as a morphism of representations. -/
noncomputable def piRepEval (M : ι → Rep.{0,0,0} k G) (i : ι) : piRep M ⟶ M i :=
  Rep.ofHom ⟨LinearMap.proj i, fun g => by ext x; simp⟩

@[simp] theorem piRepEval_hom_apply (M : ι → Rep.{0,0,0} k G) (i : ι) (x : (piRep M).V) :
    (piRepEval M i).hom x = x i := rfl

/-- The pointwise product of representations is a categorical product. -/
noncomputable def piRepCone (M : ι → Rep.{0,0,0} k G) : Fan M :=
  Fan.mk (piRep M) (fun i => piRepEval M i)

noncomputable def piRepConeIsLimit (M : ι → Rep.{0,0,0} k G) : IsLimit (piRepCone M) where
  lift s := Rep.ofHom ⟨LinearMap.pi (fun i => (s.π.app ⟨i⟩).hom.toLinearMap), fun g => by
    ext x i
    exact LinearMap.congr_fun ((s.π.app ⟨i⟩).hom.isIntertwining' g) x⟩
  uniq s m w := by
    ext x
    funext i
    exact congrArg (fun f => (f : s.pt ⟶ M i) x) (w ⟨i⟩)

/-- The canonical isomorphism between the categorical product `∏ᶜ M` of representations and
the pointwise product `piRep M`. -/
noncomputable def piRepIso (M : ι → Rep.{0,0,0} k G) : piRep M ≅ ∏ᶜ M :=
  (piRepConeIsLimit M).conePointUniqueUpToIso (limit.isLimit (Discrete.functor M))

theorem piRepIso_hom_π (M : ι → Rep.{0,0,0} k G) (i : ι) :
    (piRepIso M).hom ≫ Pi.π M i = piRepEval M i :=
  (piRepConeIsLimit M).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (Discrete.functor M)) ⟨i⟩

end PiRep

section Extraction

/-- In a short complex of modules, an element of the cycles whose homology class vanishes is in
the image of the differential. -/
lemma exists_toCycles_of_homologyπ_eq_zero {k : Type} [CommRing k]
    (S : ShortComplex (ModuleCat k)) (z : S.cycles) (hz : S.homologyπ z = 0) :
    ∃ w : S.X₁, S.toCycles w = z := by
  have h1 : S.pOpcycles (S.iCycles z) = 0 := by
    have h := congrArg (fun f : S.cycles ⟶ S.opcycles => f z) S.homology_π_ι
    simp only [ModuleCat.comp_apply] at h
    rw [hz] at h
    simpa using h.symm
  obtain ⟨w, hw⟩ :=
    LinearMap.mem_range.mp ((S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles z)).1 h1)
  refine ⟨w, (ModuleCat.mono_iff_injective S.iCycles).1 inferInstance ?_⟩
  rw [← ConcreteCategory.comp_apply S.toCycles S.iCycles w, S.toCycles_i]
  exact hw

end Extraction


section Main

variable {ι : Type}

/-- The key lemma: for the pointwise product representation `piRep M`, a cohomology class all of
whose projections to the factors `M i` vanish is zero. -/
theorem piRep_injective (M : ι → Rep.{0,0,0} k G) (n : ℕ)
    (x : groupCohomology (piRep M) n)
    (h : ∀ i, (groupCohomology.map (MonoidHom.id G) (piRepEval M i) n).hom x = 0) :
    x = 0 := by
  revert h
  refine groupCohomology_induction_on x ?_
  intro y h
  -- the components of `y` vanish in cohomology
  have hyi : ∀ i, (groupCohomology.π (M i) n)
      (HomologicalComplex.cyclesMap
        (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)) n y)
      = 0 := by
    intro i
    have h1 := congrArg (fun f => f y) (π_map (A := piRep M) (B := M i)
      (MonoidHom.id G) (piRepEval M i) n)
    simp only [ModuleCat.comp_apply] at h1
    rw [h i] at h1
    simpa using h1.symm
  -- hence each component is a coboundary
  have hwit : ∀ i, ∃ w : ↑((inhomogeneousCochains (M i)).sc n).X₁,
      (inhomogeneousCochains (M i)).iCycles n
        (HomologicalComplex.cyclesMap
          (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)) n y)
      = (inhomogeneousCochains (M i)).d ((ComplexShape.up ℕ).prev n) n w := by
    intro i
    obtain ⟨w, hw⟩ := exists_toCycles_of_homologyπ_eq_zero ((inhomogeneousCochains (M i)).sc n) _
      (hyi i)
    refine ⟨w, ?_⟩
    have h2 : ((inhomogeneousCochains (M i)).sc n).iCycles
        (((inhomogeneousCochains (M i)).sc n).toCycles w)
        = ((inhomogeneousCochains (M i)).sc n).f w := by
      rw [← ShortComplex.toCycles_i]
      rfl
    rw [hw] at h2
    exact h2
  classical
  choose w hw using hwit
  -- assemble the witnesses into a cochain of the product
  let Z : (Fin ((ComplexShape.up ℕ).prev n) → G) → (∀ i, (M i).V) := fun g i => w i g
  have hZW : ∀ i,
      (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)).f
        ((ComplexShape.up ℕ).prev n) Z = w i := by
    intro i
    ext g
    simp only [cochainsMap_f, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom]
    rfl
  have hZ : (inhomogeneousCochains (piRep M)).d ((ComplexShape.up ℕ).prev n) n Z
      = (inhomogeneousCochains (piRep M)).iCycles n y := by
    apply funext
    intro g
    apply funext
    intro i
    have hcomm : (inhomogeneousCochains (M i)).d ((ComplexShape.up ℕ).prev n) n
          ((cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)).f
            ((ComplexShape.up ℕ).prev n) Z)
        = (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)).f n
          ((inhomogeneousCochains (piRep M)).d ((ComplexShape.up ℕ).prev n) n Z) :=
      congrArg (fun f => f Z) (HomologicalComplex.Hom.comm
        (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i))
        ((ComplexShape.up ℕ).prev n) n)
    rw [hZW i] at hcomm
    have hcyc : (inhomogeneousCochains (M i)).iCycles n
          ((HomologicalComplex.cyclesMap
            (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)) n) y)
        = (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)).f n
          ((inhomogeneousCochains (piRep M)).iCycles n y) :=
      congrArg (fun f : (inhomogeneousCochains (piRep M)).cycles n ⟶
          (inhomogeneousCochains (M i)).X n => f y)
        (HomologicalComplex.cyclesMap_i
          (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)) n)
    have hφ : (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)).f n
          ((inhomogeneousCochains (piRep M)).d ((ComplexShape.up ℕ).prev n) n Z)
        = (cochainsMap (A := piRep M) (B := M i) (MonoidHom.id G) (piRepEval M i)).f n
          ((inhomogeneousCochains (piRep M)).iCycles n y) := by
      rw [← hcomm, ← hw i]
      exact hcyc
    have h := congrFun hφ g
    simpa [piRepEval_hom_apply] using h
  have hy_eq : (inhomogeneousCochains (piRep M)).toCycles ((ComplexShape.up ℕ).prev n) n Z = y := by
    apply (ModuleCat.mono_iff_injective ((inhomogeneousCochains (piRep M)).iCycles n)).1
      inferInstance
    have h2 : (inhomogeneousCochains (piRep M)).iCycles n
        ((inhomogeneousCochains (piRep M)).toCycles ((ComplexShape.up ℕ).prev n) n Z)
        = (inhomogeneousCochains (piRep M)).d ((ComplexShape.up ℕ).prev n) n Z := by
      rw [← HomologicalComplex.toCycles_i]
      rfl
    rw [h2, hZ]
  have hzero : (inhomogeneousCochains (piRep M)).homologyπ n
      ((inhomogeneousCochains (piRep M)).toCycles ((ComplexShape.up ℕ).prev n) n Z) = 0 :=
    congrArg (fun f : (inhomogeneousCochains (piRep M)).X ((ComplexShape.up ℕ).prev n) ⟶
        (inhomogeneousCochains (piRep M)).homology n => f Z)
      (HomologicalComplex.toCycles_comp_homologyπ (inhomogeneousCochains (piRep M)) _ n)
  rw [← hy_eq]
  exact hzero

end Main

section Target

/-- The family of maps on group cohomology induced by the projections of a categorical product
of representations is jointly injective. -/
theorem piCohomology_injective {k G : Type} [CommRing k] [Group G]
    {ι : Type} (M : ι → Rep.{0, 0, 0} k G) (n : ℕ) (x : groupCohomology (∏ᶜ M) n)
    (h : ∀ i, (groupCohomology.map (MonoidHom.id G) (CategoryTheory.Limits.Pi.π M i) n).hom x = 0) :
    x = 0 := by
  -- express the projections of `∏ᶜ M` through the pointwise product
  have hπ : ∀ i, Pi.π M i = (piRepIso M).inv ≫ piRepEval M i := by
    intro i
    rw [← piRepIso_hom_π M i, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hy : ∀ i, (groupCohomology.map (MonoidHom.id G) (piRepEval M i) n).hom
      ((groupCohomology.map (MonoidHom.id G) (piRepIso M).inv n).hom x) = 0 := by
    intro i
    have h1 := h i
    rw [hπ i, groupCohomology.map_id_comp, ModuleCat.comp_apply] at h1
    exact h1
  have h2 : (groupCohomology.map (MonoidHom.id G) (piRepIso M).inv n).hom x = 0 :=
    piRep_injective M n _ hy
  have h4 : (groupCohomology.map (A := piRep M) (B := ∏ᶜ M) (MonoidHom.id G)
        (piRepIso M).hom n).hom
      ((groupCohomology.map (A := ∏ᶜ M) (B := piRep M) (MonoidHom.id G)
        (piRepIso M).inv n).hom x) = x := by
    change (ConcreteCategory.hom
        (((groupCohomology.functor k G n).mapIso (piRepIso M)).hom))
      ((ConcreteCategory.hom
        (((groupCohomology.functor k G n).mapIso (piRepIso M)).inv)) x) = x
    exact Iso.inv_hom_id_apply ((groupCohomology.functor k G n).mapIso (piRepIso M)) x
  rw [← h4, h2]
  simp

end Target


end

end NK.RepresentationTheory.GroupCohomology
