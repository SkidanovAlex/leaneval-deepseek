/-
# The reduced zeroth singular homology of a two-point discrete space

A discrete space `X` with `X ≃ Bool` has exactly two path components, hence
`H₀(X; ℤ) ≅ ℤ ⊕ ℤ`, and the augmentation `ε : H₀(X; ℤ) ⟶ ℤ` is the sum of the two
coefficients `(a, b) ↦ a + b`; its kernel is a copy of `ℤ`.

The proof follows `Submission/Work/Cohomology/reducedH0SphereOne.lean` (the case of the
`0`-sphere, which is the two-point space `{±1}`), but is stated for an arbitrary
`Y : TopCat` equipped with an equivalence `ZerothHomotopy Y ≃ Bool`, so that it applies to
any two-point discrete space.  The generic linear-algebra lemmas of that file are reproduced
here under different names so that the two files can be imported together.

The formal proof goes through `TopCat.singularHomology₀Iso`, which identifies `H₀(X; ℤ)`
with the coproduct of copies of `ℤ` indexed by `ZerothHomotopy X`, together with
`TopCat.singularHomology₀Iso_sigma_desc_id`, which says that the augmentation is the
coproduct `Sigma.desc` of the identities.
-/
import Mathlib
import Submission.Work.Cohomology.SphDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped unitInterval
open CategoryTheory Limits AlgebraicTopology

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Work.Cohomology

noncomputable section

/-! ## The two `ℤ`-module structures on a kernel

The kernel of a linear map `M →ₗ[ℤ] ℤ` carries two module structures: the restriction of the
ambient one (`Submodule.module`, which is what typeclass search finds by default) and the
canonical `AddCommGroup.toIntModule`.  `kerMod` pins the latter.  For `ℤ` the two structures
agree because the module structure of an abelian group over `ℤ` is determined by the group
(`AddCommMonoid.subsingletonIntModule`), so the corresponding objects of `ModuleCat ℤ` are
isomorphic. -/

/-- Two `ModuleCat.of` objects built from the same type with two module structures `a`, `b`
which are equal (automatically, over `ℤ`) are isomorphic. -/
def moduleCatOfIsoOfEq {M : Type} [AddCommGroup M] {a b : Module ℤ M} :
    @ModuleCat.of ℤ _ M _ a ≅ @ModuleCat.of ℤ _ M _ b := by
  have h : a = b := Subsingleton.elim a b
  rw [h]

/-- The `ModuleCat ℤ` object associated with the kernel of `f`, with the module structure
selected by typeclass search, is isomorphic to `kerMod f`, where the module structure is pinned
to `AddCommGroup.toIntModule`. -/
def ofKerIsoKerMod {M : Type} [AddCommGroup M] [Module ℤ M] (f : M →ₗ[ℤ] ℤ) :
    ModuleCat.of ℤ ↥(LinearMap.ker f) ≅ kerMod f :=
  moduleCatOfIsoOfEq

/-! ## `ZerothHomotopy` of a discrete space -/

/-- A path in a discrete space is constant, because a continuous map from a connected space into
a discrete space is constant. -/
lemma joined_eq_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {x y : X}
    (h : Joined x y) : x = y := by
  have hc := PreconnectedSpace.constant (α := unitInterval) (Y := X) (inferInstance)
      h.somePath.continuous (x := (0 : unitInterval)) (y := (1 : unitInterval))
  rw [Path.source h.somePath, Path.target h.somePath] at hc
  exact hc

/-- `ZerothHomotopy.mk` is a bijection for a discrete space. -/
lemma zerothHomotopy_mk_bijective (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    Function.Bijective (ZerothHomotopy.mk (X := X)) :=
  ⟨fun _ _ h => joined_eq_of_discrete (Quotient.exact h), ZerothHomotopy.mk_surjective⟩

/-- For a discrete space, the type of path components is the space itself. -/
noncomputable def zerothHomotopyEquivOfDiscrete (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] : ZerothHomotopy X ≃ X :=
  (Equiv.ofBijective _ (zerothHomotopy_mk_bijective X)).symm

/-- A discrete space with `X ≃ Bool` has exactly two path components. -/
noncomputable def zerothHomotopyEquivBoolOfDiscrete (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] (e : X ≃ Bool) : ZerothHomotopy X ≃ Bool :=
  (zerothHomotopyEquivOfDiscrete X).trans e

/-! ## General linear algebra helpers -/

/-- The coefficient ring, as an object of `ModuleCat ℤ`. -/
abbrev Rz : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- An isomorphism in `ModuleCat ℤ` gives a linear equivalence of the underlying modules. -/
noncomputable def redH0_linEquivOfIso {M N : ModuleCat ℤ} (e : M ≅ N) : M ≃ₗ[ℤ] N :=
  LinearEquiv.ofBijective (ModuleCat.Hom.hom e.hom) (by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨e.inv.hom, fun x => ?_, fun y => ?_⟩
    · have h2 : (e.inv.hom) ∘ₗ (e.hom.hom) = LinearMap.id := by
        rw [← ModuleCat.hom_comp, e.hom_inv_id, ModuleCat.hom_id]
      exact LinearMap.congr_fun h2 x
    · have h2 : (e.hom.hom) ∘ₗ (e.inv.hom) = LinearMap.id := by
        rw [← ModuleCat.hom_comp, e.inv_hom_id, ModuleCat.hom_id]
      exact LinearMap.congr_fun h2 y)

/-- Composing with a linear equivalence does not change the kernel, up to isomorphism. -/
noncomputable def redH0_kerCongr {M N P : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (e : M ≃ₗ[ℤ] N) (f : N →ₗ[ℤ] P) :
    LinearMap.ker (f ∘ₗ (e : M →ₗ[ℤ] N)) ≃ₗ[ℤ] LinearMap.ker f where
  toFun x := ⟨e x, LinearMap.mem_ker.mpr (by
    have h := LinearMap.mem_ker.mp x.2
    simp only [LinearMap.comp_apply] at h
    exact h)⟩
  invFun y := ⟨e.symm y, LinearMap.mem_ker.mpr (by
    have h := LinearMap.mem_ker.mp y.2
    simpa [LinearMap.comp_apply, e.apply_symm_apply] using h)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

/-! ## The map `(a, b) ↦ a + b` on `Bool → ℤ` -/

/-- The map `f ↦ f true + f false` on `Bool → ℤ`. -/
noncomputable def redH0_sig : (Bool → ℤ) →ₗ[ℤ] ℤ where
  toFun f := f true + f false
  map_add' f g := by simp only [Pi.add_apply]; ring
  map_smul' n f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma redH0_sig_single (j : Bool) (x : ℤ) : redH0_sig (Pi.single j x) = x := by
  cases j <;> simp [redH0_sig, Pi.single_eq_same, Pi.single_eq_of_ne]

/-- The kernel of `(a, b) ↦ a + b` is a copy of `ℤ`. -/
noncomputable def redH0_kerSigEquiv : LinearMap.ker redH0_sig ≃ₗ[ℤ] ℤ where
  toFun f := (f : Bool → ℤ) true
  invFun n := ⟨fun b => if b then n else -n, by
    show redH0_sig (fun b => if b then n else -n) = 0
    simp [redH0_sig]⟩
  left_inv f := by
    apply Subtype.ext
    funext b
    have hf : (f : Bool → ℤ) true + (f : Bool → ℤ) false = 0 := by
      have h := f.2
      rw [LinearMap.mem_ker] at h
      -- v4.35: `simpa [redH0_sig] using h` now simplifies `h` to `True`; the goal is `h` by definition
      exact h
    cases b with
    | true => simp
    | false => simp; linarith
  right_inv n := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

/-! ## The coproduct of two copies of `ℤ` -/

noncomputable def redH0_eCoprod : (∐ (fun _ : Bool ↦ Rz)) ≅
    ModuleCat.of ℤ (DirectSum Bool (fun _ ↦ ℤ)) :=
  ModuleCat.coprodIsoDirectSum (fun _ : Bool ↦ Rz)

noncomputable def redH0_eFun : ModuleCat.of ℤ (DirectSum Bool (fun _ ↦ ℤ)) ≅
    ModuleCat.of ℤ (Bool → ℤ) :=
  (DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ ↦ ℤ)).toModuleIso

lemma redH0_iota_eCoprod (j : Bool) :
    Sigma.ι (fun _ : Bool ↦ Rz) j ≫ redH0_eCoprod.hom
      = ModuleCat.ofHom (DirectSum.lof ℤ Bool (fun _ ↦ ℤ) j) :=
  ModuleCat.ι_coprodIsoDirectSum_hom (Z := fun _ : Bool ↦ Rz) j

lemma redH0_ofHom_lof_comp_eFun (j : Bool) :
    ModuleCat.ofHom (DirectSum.lof ℤ Bool (fun _ ↦ ℤ) j) ≫ redH0_eFun.hom
      = ModuleCat.ofHom ((DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ ↦ ℤ) : _ →ₗ[ℤ] _)
          ∘ₗ DirectSum.lof ℤ Bool (fun _ ↦ ℤ) j) := by
  rw [show redH0_eFun.hom = ModuleCat.ofHom
        (DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ ↦ ℤ) : _ →ₗ[ℤ] _) from rfl,
      ← ModuleCat.ofHom_comp]

lemma redH0_sig_comp_lof (j : Bool) :
    (redH0_sig ∘ₗ ((DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ ↦ ℤ) : _ →ₗ[ℤ] _)
      ∘ₗ DirectSum.lof ℤ Bool (fun _ ↦ ℤ) j)) = 1 := by
  apply LinearMap.ext_ring
  simp [LinearMap.comp_apply, DirectSum.linearEquivFunOnFintype_lof, redH0_sig_single]

/-! ## The computation for a space with `ZerothHomotopy Y ≃ Bool` -/

section General

variable (Y : TopCat.{0}) (k : ZerothHomotopy Y ≃ Bool)

noncomputable def redH0_iso : ((singularHomologyFunctor (ModuleCat ℤ) 0).obj Rz).obj Y ≅
    (∐ (fun _ : ZerothHomotopy Y ↦ Rz)) := Y.singularHomology₀Iso Rz

noncomputable def redH0_desc : (∐ (fun _ : ZerothHomotopy Y ↦ Rz)) ⟶ Rz :=
  Sigma.desc (fun _ ↦ 𝟙 Rz)

noncomputable def redH0_eRe : (∐ (fun _ : ZerothHomotopy Y ↦ Rz)) ≅
    (∐ (fun _ : Bool ↦ Rz)) :=
  (sigmaConst.obj Rz).mapIso k.toIso

noncomputable def redH0_eAllIso : (∐ (fun _ : ZerothHomotopy Y ↦ Rz)) ≅
    ModuleCat.of ℤ (Bool → ℤ) :=
  redH0_eRe Y k ≪≫ redH0_eCoprod ≪≫ redH0_eFun

noncomputable def redH0_eAll : ↥(∐ (fun _ : ZerothHomotopy Y ↦ Rz)) ≃ₗ[ℤ] (Bool → ℤ) :=
  redH0_linEquivOfIso (redH0_eAllIso Y k)

lemma redH0_iota_eRe (i : ZerothHomotopy Y) :
    Sigma.ι (fun _ : ZerothHomotopy Y ↦ Rz) i ≫ (redH0_eRe Y k).hom
      = Sigma.ι (fun _ : Bool ↦ Rz) (k i) := by
  rw [show (redH0_eRe Y k).hom = (sigmaConst.obj Rz).map k.toIso.hom
        from Functor.mapIso_hom _ _, sigmaConst_obj_map, Sigma.ι_comp_map']
  simp [Equiv.toIso_hom_hom_apply]

lemma redH0_iota_eAll (i : ZerothHomotopy Y) :
    Sigma.ι (fun _ : ZerothHomotopy Y ↦ Rz) i ≫ (redH0_eAllIso Y k).hom
      = ModuleCat.ofHom ((DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ ↦ ℤ) : _ →ₗ[ℤ] _)
          ∘ₗ DirectSum.lof ℤ Bool (fun _ ↦ ℤ) (k i)) := by
  show (Sigma.ι (fun _ : ZerothHomotopy Y ↦ Rz) i ≫ (redH0_eRe Y k).hom) ≫
      redH0_eCoprod.hom ≫ redH0_eFun.hom = _
  rw [redH0_iota_eRe, ← Category.assoc, redH0_iota_eCoprod, redH0_ofHom_lof_comp_eFun]

/-- The augmentation, transported along `redH0_eAll`, is the map `(a, b) ↦ a + b`. -/
lemma redH0_desc_eq : ModuleCat.Hom.hom (redH0_desc Y)
    = redH0_sig ∘ₗ (redH0_eAll Y k :
        ↥(∐ (fun _ : ZerothHomotopy Y ↦ Rz)) →ₗ[ℤ] (Bool → ℤ)) := by
  have hmor : redH0_desc Y = (redH0_eAllIso Y k).hom ≫ ModuleCat.ofHom redH0_sig := by
    apply Sigma.hom_ext
    intro i
    dsimp only [redH0_desc]
    rw [Sigma.ι_desc, ← Category.assoc, redH0_iota_eAll, ModuleCat.ofHom_comp]
    exact ModuleCat.hom_ext (by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
      exact (redH0_sig_comp_lof (k i)).symm)
  rw [hmor, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  rfl

end General

/-- The reduced zeroth homology of a space with two path components is `ℤ`. -/
theorem redH0_zerothEquivBool (Y : TopCat.{0}) (k : ZerothHomotopy Y ≃ Bool) :
    Nonempty (ModuleCat.of ℤ (LinearMap.ker (ModuleCat.Hom.hom (Y.singularHomology₀ε Rz)))
      ≅ ModuleCat.of ℤ ℤ) := by
  have hε : ModuleCat.Hom.hom (Y.singularHomology₀ε Rz)
      = ModuleCat.Hom.hom (redH0_desc Y)
        ∘ₗ (redH0_linEquivOfIso (redH0_iso Y) : _ →ₗ[ℤ] _) := by
    rw [← Y.singularHomology₀Iso_sigma_desc_id Rz, ModuleCat.hom_comp]
    rfl
  have h1 : LinearMap.ker (ModuleCat.Hom.hom (Y.singularHomology₀ε Rz)) ≃ₗ[ℤ]
      LinearMap.ker (ModuleCat.Hom.hom (redH0_desc Y)) := by
    rw [hε]
    exact redH0_kerCongr (redH0_linEquivOfIso (redH0_iso Y)) (ModuleCat.Hom.hom (redH0_desc Y))
  have h2 : LinearMap.ker (ModuleCat.Hom.hom (redH0_desc Y)) ≃ₗ[ℤ]
      LinearMap.ker redH0_sig := by
    rw [redH0_desc_eq Y k]
    exact redH0_kerCongr (redH0_eAll Y k) redH0_sig
  exact ⟨LinearEquiv.toModuleIso (h1.trans (h2.trans redH0_kerSigEquiv))⟩

/-! ## The main statement -/

theorem reducedH0OfTwoPoints (X : Type) [TopologicalSpace X] [DiscreteTopology X] (e : X ≃ Bool) :
    Nonempty (kerMod (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℤ ℤ))) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨h⟩ := redH0_zerothEquivBool (TopCat.of X) (zerothHomotopyEquivBoolOfDiscrete X e)
  exact ⟨(ofKerIsoKerMod (ModuleCat.Hom.hom
    (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℤ ℤ)))).symm ≪≫ h⟩

end

end Work.Cohomology
