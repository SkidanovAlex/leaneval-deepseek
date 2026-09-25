import Submission.NK.Reconstruct.hausPi

/-!
# The general base change `π_{M/K} : Γ_M → Γ_K` for an arbitrary finite extension `M/K`

Shimizu's `π_{L/K} : Γ_L → Γ_K` (arXiv:2009.10431, §4) is the map induced by the inclusion
`G_L ⊆ G_K` on the torsion-free ℓ-adic abelianisations; it satisfies `π(Frob_𝔭) = Frob_{𝔭|K}`.
`NK.Reconstruct.gammaBaseChangeHom` constructs it for a level `L` that is *normal over the base*
(which is what the projective-system construction of `Γ_K` requires).  For the reconstruction step
one needs it in the two further cases

* `M/K` an arbitrary finite extension of number fields (Shimizu's Lemma 4f.4 and the assembly of
  §4 use base changes for intermediate fields `K₁ ⊆ N ⊆ L` with `N` *not* normal over `K₁`),

and this file constructs it.  The construction replaces the compositum `N ⊔ L` of
`NK.Reconstruct.gammaBaseChangeHom` by the compositum of the level `N` with the **normal closure
`Z` of `M` over `↥K.L`** (`NK.Reconstruct.baseClosure`), which is normal over `↥K.L` *and*, being
stable under `Gal(Ω/↥K.L) ⊇ Gal(Ω/↥M.L)`, normal over `↥M.L` as well
(`NK.Reconstruct.normal_toIntermediateField`); so the same field is a level over both bases, and
the "forget the `M`-structure" map (`NK.Reconstruct.levelInclGenHom`) can be applied to it.

## Contents

* `NK.Reconstruct.algOfLe` — the `Algebra ↥K.L ↥M.L` structure given by the inclusion;
* `NK.Reconstruct.baseClosure`, `le_baseClosure`, `le_baseClosure_set` — the normal closure of
  `M` over `↥K.L`, as a level over `↥K.L`;
* `NK.Reconstruct.normal_toIntermediateField`, `NK.Reconstruct.levelOverM` — a field containing
  `M.L` viewed as a level over `↥M.L` (normality by carrier-stability under `Gal(Ω/↥M.L)`);
* `NK.Reconstruct.supClosure` (+ `le_supClosure`, `baseClosure_le_supClosure`, `supClosure_mono`,
  `set_le_supClosure`), `NK.Reconstruct.supClosureM` (+ `supClosureM_mono`) — the compositum of a
  level over `↥K.L` with the closure, as a level over both bases;
* `NK.Reconstruct.levelInclGenHom` (+`_apply_coe`), `NK.Reconstruct.ellInclGen` (+`_coe`) — the
  "forget the `M`-structure" map, at the group level and on the ℓ-primary parts;
* `NK.Reconstruct.levelInclGenHom_comp`, `NK.Reconstruct.ellInclGen_ellRestrict` — the
  naturality squares;
* **`NK.Reconstruct.generalBaseChange`** — `π_{M/K} : Γ_M → Γ_K`, with
  `generalBaseChange_compatible` (the projections form a compatible family),
  **`generalBaseChange_apply`** (the projection formula) and
  **`generalBaseChange_continuous`**.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace NK.Reconstruct

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

/-- The `Algebra ↥K.L ↥M.L` structure given by the inclusion. -/
noncomputable def algOfLeNumFieldIn (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) : Algebra ↥K.L ↥M.L :=
  RingHom.toAlgebra
    { toFun := fun x => ⟨x.1, h x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }

/-- `M` viewed over `K.L`. -/
noncomputable abbrev baseChangeLevel (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) :
    IntermediateField ↥K.L Ω :=
  IntermediateField.extendScalars (F := K.L) (E := M.L) h

/-- The normal closure of `M` over `K.L`, as a level over `K.L`. -/
noncomputable def baseClosure (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) : FrobLevel ↥K.L Ω where
  L := IntermediateField.normalClosure ↥K.L ↥(baseChangeLevel K M h) Ω
  finite := by
    haveI : FiniteDimensional ↥K.L ↥(baseChangeLevel K M h) := by
      haveI : NumberField ↥(baseChangeLevel K M h) := inferInstanceAs (NumberField ↥M.L)
      infer_instance
    infer_instance
  normal := inferInstance
  numberField := by
    haveI : FiniteDimensional ↥K.L ↥(baseChangeLevel K M h) := by
      haveI : NumberField ↥(baseChangeLevel K M h) := inferInstanceAs (NumberField ↥M.L)
      infer_instance
    haveI : FiniteDimensional ↥K.L
        ↥(IntermediateField.normalClosure ↥K.L ↥(baseChangeLevel K M h) Ω) := inferInstance
    exact NumberField.of_module_finite ↥K.L _

theorem le_baseClosure (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) :
    baseChangeLevel K M h ≤ (baseClosure K M h).L :=
  IntermediateField.le_normalClosure _

theorem le_baseClosure_set (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) :
    M.L ≤ ((baseClosure K M h).L : Set Ω) := by
  intro x hx
  exact le_baseClosure K M h (show x ∈ (baseChangeLevel K M h : Set Ω) from hx)

/-- Normality of a field over a smaller base. -/
theorem normal_toIntermediateField {K M : NumFieldIn ℚ Ω} (h : K.L ≤ M.L)
    (Z : FrobLevel ↥K.L Ω) (hMZ : (M.L : Set Ω) ⊆ (Z.L : Set Ω)) :
    Normal ↥M.L (Subfield.toIntermediateField (Z.L.toSubfield) (fun x : ↥M.L => hMZ x.2)) := by
  letI : Algebra ↥K.L ↥M.L := algOfLeNumFieldIn K M h
  haveI : IsScalarTower ↥K.L ↥M.L Ω := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show (algebraMap ↥K.L Ω x : Ω) = (algebraMap ↥M.L Ω (⟨(x : Ω), h x.2⟩ : ↥M.L) : Ω)
    rfl
  refine (IntermediateField.normal_iff_forall_map_le' (F := ↥M.L) (L := Ω)).mpr ?_
  intro σ
  have hσK : ∀ x : Ω, x ∈ Z.L → σ x ∈ Z.L := by
    have hh := (IntermediateField.normal_iff_forall_map_le' (F := ↥K.L) (L := Ω)).mp Z.normal
      (σ.restrictScalars ↥K.L)
    intro x hx
    exact hh ((IntermediateField.mem_map (S := Z.L)).mpr ⟨x, hx, rfl⟩)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map
    (S := Subfield.toIntermediateField (Z.L.toSubfield) (fun x : ↥M.L => hMZ x.2))).mp hy
  exact hσK z hz

/-- A field `Z ⊇ M.L` viewed as a level over `M.L`. -/
noncomputable def levelOverM {K M : NumFieldIn ℚ Ω} (h : K.L ≤ M.L) (Z : FrobLevel ↥K.L Ω)
    (hMZ : (M.L : Set Ω) ⊆ (Z.L : Set Ω)) : FrobLevel ↥M.L Ω where
  L := Subfield.toIntermediateField (Z.L.toSubfield) (fun x : ↥M.L => hMZ x.2)
  finite := by
    haveI : NumberField ↥(Subfield.toIntermediateField (Z.L.toSubfield) (fun x : ↥M.L => hMZ x.2)) :=
      inferInstanceAs (NumberField ↥Z.L)
    infer_instance
  normal := normal_toIntermediateField h Z hMZ
  numberField := inferInstanceAs (NumberField ↥Z.L)

/-- The compositum of a level over `K.L` with the closure of `M`. -/
noncomputable def supClosure (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω) :
    FrobLevel ↥K.L Ω :=
  N.sup (baseClosure K M h)

theorem le_supClosure (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω) :
    N.L ≤ (supClosure K M h N).L :=
  FrobLevel.le_sup_left N (baseClosure K M h)

theorem baseClosure_le_supClosure (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω) :
    (baseClosure K M h).L ≤ (supClosure K M h N).L :=
  FrobLevel.le_sup_right N (baseClosure K M h)

theorem supClosure_mono (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) {A B : FrobLevel ↥K.L Ω}
    (hAB : A.L ≤ B.L) : (supClosure K M h A).L ≤ (supClosure K M h B).L :=
  FrobLevel.sup_le (hAB.trans (le_supClosure K M h B)) (baseClosure_le_supClosure K M h B)

theorem set_le_supClosure (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω) :
    (M.L : Set Ω) ⊆ ((supClosure K M h N).L : Set Ω) :=
  (le_baseClosure_set K M h).trans (baseClosure_le_supClosure K M h N)

/-- The compositum, viewed as a level over `M.L`. -/
noncomputable def supClosureM (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω) :
    FrobLevel ↥M.L Ω :=
  levelOverM h (supClosure K M h N) (set_le_supClosure K M h N)

/-- The monotonicity of `supClosureM`. -/
theorem supClosureM_mono (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) {A B : FrobLevel ↥K.L Ω}
    (hAB : A.L ≤ B.L) : (supClosureM K M h A).L ≤ (supClosureM K M h B).L :=
  supClosure_mono K M h hAB

/-- The group homomorphism "forget the `M`-structure", at the composita. -/
noncomputable def levelInclGenHom (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω) :
    Gal(↥(supClosureM K M h N).L/↥M.L) →* Gal(↥(supClosure K M h N).L/↥K.L) := by
  letI : Algebra ↥K.L ↥M.L := algOfLeNumFieldIn K M h
  haveI : IsScalarTower ↥K.L ↥M.L Ω := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show (algebraMap ↥K.L Ω x : Ω) = (algebraMap ↥M.L Ω (⟨(x : Ω), h x.2⟩ : ↥M.L) : Ω)
    rfl
  exact AlgEquiv.restrictScalarsHom (R := ↥K.L) (S := ↥M.L)
    (A := ↥(supClosureM K M h N).L)

/-- The ℓ-part of "forget the `M`-structure". -/
noncomputable def ellInclGen (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ)
    (N : FrobLevel ↥K.L Ω) :
    LevelEllPart (K := ↥M.L) (K' := Ω) (supClosureM K M h N).L ℓ →*
      LevelEllPart (K := ↥K.L) (K' := Ω) (supClosure K M h N).L ℓ where
  toFun x := ⟨Abelianization.map (levelInclGenHom K M h N) x.1,
    ellPart_map_le ℓ _ (Subgroup.mem_map_of_mem _ x.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] theorem ellInclGen_coe (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ)
    (N : FrobLevel ↥K.L Ω) (x : LevelEllPart (K := ↥M.L) (K' := Ω) (supClosureM K M h N).L ℓ) :
    ((ellInclGen K M h ℓ N x :
        LevelEllPart (K := ↥K.L) (K' := Ω) (supClosure K M h N).L ℓ) :
      Abelianization Gal(↥(supClosure K M h N).L/↥K.L))
      = Abelianization.map (levelInclGenHom K M h N) x.1 := rfl

/-- The underlying function of "forget the `M`-structure" is unchanged. -/
theorem levelInclGenHom_apply_coe (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω)
    (g : Gal(↥(supClosureM K M h N).L/↥M.L)) (x : ↥(supClosure K M h N).L) :
    (((levelInclGenHom K M h N g : Gal(↥(supClosure K M h N).L/↥K.L)) x :
        ↥(supClosure K M h N).L) : Ω)
      = ((g ⟨(x : Ω), (show (x : Ω) ∈ (supClosureM K M h N).L from x.2)⟩ :
          ↥(supClosureM K M h N).L) : Ω) := rfl

/-- The naturality square at the group level. -/
theorem levelInclGenHom_comp (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (A B : FrobLevel ↥K.L Ω)
    (hAB : A.L ≤ B.L) :
    ((levelRestrictHom (supClosure K M h A) (supClosure K M h B) (supClosure_mono K M h hAB)).comp
        (levelInclGenHom K M h B) :
      Gal(↥(supClosureM K M h B).L/↥M.L) →* Gal(↥(supClosure K M h A).L/↥K.L))
      = ((levelInclGenHom K M h A).comp
        (levelRestrictHom (supClosureM K M h A) (supClosureM K M h B)
          (supClosureM_mono K M h hAB)) :
      Gal(↥(supClosureM K M h B).L/↥M.L) →* Gal(↥(supClosure K M h A).L/↥K.L)) := by
  ext g x
  simp only [MonoidHom.comp_apply, levelRestrictHom_apply_coe, levelInclGenHom_apply_coe]

/-- The naturality square for the ℓ-primary parts. -/
theorem ellInclGen_ellRestrict (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ)
    (A B : FrobLevel ↥K.L Ω) (hAB : A.L ≤ B.L) :
    ((ellRestrict ℓ (supClosure K M h A) (supClosure K M h B) (supClosure_mono K M h hAB)).comp
        (ellInclGen K M h ℓ B) :
      LevelEllPart (K := ↥M.L) (K' := Ω) (supClosureM K M h B).L ℓ →*
        LevelEllPart (K := ↥K.L) (K' := Ω) (supClosure K M h A).L ℓ)
      = ((ellInclGen K M h ℓ A).comp
        (ellRestrict ℓ (supClosureM K M h A) (supClosureM K M h B)
          (supClosureM_mono K M h hAB)) :
      LevelEllPart (K := ↥M.L) (K' := Ω) (supClosureM K M h B).L ℓ →*
        LevelEllPart (K := ↥K.L) (K' := Ω) (supClosure K M h A).L ℓ) := by
  ext x
  simp only [MonoidHom.comp_apply, ellRestrict_coe, ellInclGen_coe, levelRestrict]
  show ((Abelianization.map (levelRestrictHom (supClosure K M h A) (supClosure K M h B)
        (supClosure_mono K M h hAB))).comp (Abelianization.map (levelInclGenHom K M h B))) x.1
      = ((Abelianization.map (levelInclGenHom K M h A)).comp
          (Abelianization.map (levelRestrictHom (supClosureM K M h A) (supClosureM K M h B)
            (supClosureM_mono K M h hAB)))) x.1
  rw [DFunLike.congr_fun (Abelianization.map_comp (levelInclGenHom K M h B)
        (levelRestrictHom (supClosure K M h A) (supClosure K M h B)
          (supClosure_mono K M h hAB))) x.1,
      DFunLike.congr_fun (Abelianization.map_comp
        (levelRestrictHom (supClosureM K M h A) (supClosureM K M h B)
          (supClosureM_mono K M h hAB))
        (levelInclGenHom K M h A)) x.1,
      congrArg Abelianization.map (levelInclGenHom_comp K M h A B hAB)]

/-- The projections of the general base change form a compatible family. -/
theorem generalBaseChange_compatible (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ)
    (f : Gamma ↥M.L Ω ℓ) :
    Compatible ℓ (fun N : FrobLevel ↥K.L Ω =>
      ellRestrict ℓ N (supClosure K M h N) (le_supClosure K M h N)
        (ellInclGen K M h ℓ N (Gamma.proj (supClosureM K M h N) f))) := by
  intro N₁ N₂ h12
  have h12' : (supClosure K M h N₁).L ≤ (supClosure K M h N₂).L := supClosure_mono K M h h12
  have h12M : (supClosureM K M h N₁).L ≤ (supClosureM K M h N₂).L := supClosureM_mono K M h h12
  have e₁ : ellRestrict ℓ N₁ N₂ h12
        (ellRestrict ℓ N₂ (supClosure K M h N₂) (le_supClosure K M h N₂)
          (ellInclGen K M h ℓ N₂ (Gamma.proj (supClosureM K M h N₂) f)))
      = ellRestrict ℓ N₁ (supClosure K M h N₂) (h12.trans (le_supClosure K M h N₂))
          (ellInclGen K M h ℓ N₂ (Gamma.proj (supClosureM K M h N₂) f)) :=
    DFunLike.congr_fun (ellRestrict_comp (K := ↥K.L) (K' := Ω) ℓ (L := N₁) (M := N₂)
      (N := supClosure K M h N₂) h12 (le_supClosure K M h N₂)) _
  have e₂ : ellRestrict ℓ N₁ (supClosure K M h N₂) (h12.trans (le_supClosure K M h N₂))
        (ellInclGen K M h ℓ N₂ (Gamma.proj (supClosureM K M h N₂) f))
      = ellRestrict ℓ N₁ (supClosure K M h N₁) (le_supClosure K M h N₁)
          (ellRestrict ℓ (supClosure K M h N₁) (supClosure K M h N₂) h12'
            (ellInclGen K M h ℓ N₂ (Gamma.proj (supClosureM K M h N₂) f))) :=
    (DFunLike.congr_fun (ellRestrict_comp (K := ↥K.L) (K' := Ω) ℓ (L := N₁)
      (M := supClosure K M h N₁) (N := supClosure K M h N₂) (le_supClosure K M h N₁) h12') _).symm
  have e₃ : ellRestrict ℓ (supClosure K M h N₁) (supClosure K M h N₂) h12'
        (ellInclGen K M h ℓ N₂ (Gamma.proj (supClosureM K M h N₂) f))
      = ellInclGen K M h ℓ N₁
          (ellRestrict ℓ (supClosureM K M h N₁) (supClosureM K M h N₂) h12M
            (Gamma.proj (supClosureM K M h N₂) f)) :=
    DFunLike.congr_fun (ellInclGen_ellRestrict K M h ℓ N₁ N₂ h12) _
  have e₄ : ellRestrict ℓ (supClosureM K M h N₁) (supClosureM K M h N₂) h12M
        (Gamma.proj (supClosureM K M h N₂) f) = Gamma.proj (supClosureM K M h N₁) f :=
    Gamma.proj_compatible _ _ h12M f
  rw [e₁, e₂, e₃, e₄]

/-- **The general base change `π_{M/K} : Γ_M → Γ_K`** for an arbitrary finite extension `M/K` of
number fields, induced by `G_M ⊆ G_K` on the torsion-free ℓ-adic abelianisations. -/
noncomputable def generalBaseChange (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ) :
    Gamma ↥M.L Ω ℓ →* Gamma ↥K.L Ω ℓ where
  toFun f := Gamma.mk (fun N => ellRestrict ℓ N (supClosure K M h N) (le_supClosure K M h N)
      (ellInclGen K M h ℓ N (Gamma.proj (supClosureM K M h N) f)))
    (generalBaseChange_compatible K M h ℓ f)
  map_one' := by
    refine Gamma.ext (fun N => ?_)
    simp only [Gamma.proj_mk, map_one]
  map_mul' f g := by
    refine Gamma.ext (fun N => ?_)
    simp only [Gamma.proj_mk, map_mul]

/-- The projection formula for the general base change. -/
theorem generalBaseChange_apply (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ)
    (f : Gamma ↥M.L Ω ℓ) (N : FrobLevel ↥K.L Ω) :
    Gamma.proj N (generalBaseChange K M h ℓ f)
      = ellRestrict ℓ N (supClosure K M h N) (le_supClosure K M h N)
          (ellInclGen K M h ℓ N (Gamma.proj (supClosureM K M h N) f)) := rfl

/-- Continuity of the general base change. -/
theorem generalBaseChange_continuous (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ) :
    Continuous ⇑(generalBaseChange K M h ℓ) := by
  show Continuous fun f : Gamma ↥M.L Ω ℓ =>
    (⟨fun N => ellRestrict ℓ N (supClosure K M h N) (le_supClosure K M h N)
        (ellInclGen K M h ℓ N (Gamma.proj (supClosureM K M h N) f)),
      generalBaseChange_compatible K M h ℓ f⟩ : Gamma ↥K.L Ω ℓ)
  refine Continuous.subtype_mk ?_ ?_
  · rw [continuous_pi_iff]
    intro N
    exact (continuous_of_discreteTopology.comp (continuous_of_discreteTopology.comp
      (continuous_proj ℓ (supClosureM K M h N))))


