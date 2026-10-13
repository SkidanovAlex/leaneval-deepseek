import Mathlib
import Submission.Work.DSMX0U.ModelF

/-!
# DSMX0U — the coaugmentation `ε : A ⟶ P⁰` of the tower model

This file contains the *coaugmentation* of the finite free model `P = towerModel hstep M s₀` of
`RΓ` (see `Submission/Work/DSMX0U/ModelF.lean`), and its compatibility with a chain map
`φ : P ⟶ C`: given a level `k₀` of the tower whose degree is `0` (i.e. `levelDeg M k₀ - 1 = 0`,
so that `k₀ = M`), the cell `s = tower hstep M s₀ k₀` carries a coaugmentation generator: an
element `g` of its `gen`-part whose image under the cell's map into `C` is the coaugmentation
element `c₀ 1` of `C` in degree `0` (`Cell.hcoaugσ`, the field of the cell construction).

## The argument

The term of the model in degree `0` is the term `G = gen × rel` of the level `k₀`
(`towerModelXIso hstep M s₀ k₀`, transported along `hk : levelDeg M k₀ - 1 = 0`).  The element
`x = (g, 0) ∈ G` is a *cycle* of the level: the differential `Cell.d` of the tower kills the
`gen`-part.  Hence, transported into `P`, it is a cycle of `P` in degree `0`
(`towerModel_d_apply_eq_zero`: the model's differential out of the degree of a level is, under the
canonical isomorphisms, the differential of that level, and all other differentials vanish by the
shape of the complex).  So the linear map `A → P⁰, 1 ↦ x` is a cycle and may serve as `ε`.

Its compatibility with `φ` is `towerModel_coaug_apply`: the naturality of `XIsoOfEq` for the chain
map `φ`, the identity `hφ` for the components of `φ`, the fact that `φ ⟨g, 0⟩ = iCycles (σ g)` and
the defining property `hg` of `g` show that `ε ≫ φ.f 0 = c₀`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

section Aux

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- The coaugmentation element of `C` in degree `d = 0`, expressed through the canonical
isomorphism `C^d ≅ C^0`.  (`coaugElem` is defined through `eqToHom`, and `XIsoOfEq` through
`eqToIso`, so this is a definitional identity.) -/
lemma coaugElem_eq_XIso (d : ℤ) (h : d = 0) :
    coaugElem A c₀ d h = (C.XIsoOfEq h).inv.hom (c₀.hom 1) := by
  rw [coaugElem]
  simp [HomologicalComplex.XIsoOfEq]

/-- **A cycle of a level of the tower is a cycle of the model.**  If `x` is an element of the term
of the level `k` of the tower with `(tower k).d x = 0`, then its image in the model
(under `towerModelXIso`, i.e. in degree `levelDeg M k - 1 = M - k`) is killed by every
differential of the model.

Indeed, the only non-zero differential of the model out of that degree is the one into the degree
`levelDeg M (k-1) - 1` (when `k ≥ 1`), which is `towerModel_d`, i.e. the differential of the cell
at level `k` (up to the canonical isomorphisms); and for `k = 0` the target degree is above `M`,
where the model vanishes. -/
lemma towerModel_d_apply_eq_zero
    (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) (x : ↥((tower hstep M s₀ k).G A))
    (hx : ((tower hstep M s₀ k).d A).hom x = 0) (j : ℤ) :
    ((towerModel hstep M s₀).d (levelDeg M k - 1) j).hom
      ((towerModelXIso hstep M s₀ k).inv.hom x) = 0 := by
  by_cases hj : (ComplexShape.up ℤ).Rel (levelDeg M k - 1) j
  · -- the only relevant degree: `j = levelDeg M k - 1 + 1 = levelDeg M k`
    have hj' : levelDeg M k - 1 + 1 = j := by
      simpa [ComplexShape.up_Rel] using hj
    rw [← hj']
    cases k with
    | zero =>
      -- the target degree `M + 1` is above `M`, where the model vanishes
      have hZ : IsZero ((towerModel hstep M s₀).X (levelDeg M 0 - 1 + 1)) :=
        towerModel_isZero_of_gt hstep M s₀ (by simp)
      have h : (towerModel hstep M s₀).d (levelDeg M 0 - 1) (levelDeg M 0 - 1 + 1) = 0 :=
        IsZero.eq_of_tgt hZ _ 0
      rw [h]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
    | succ k' =>
      -- the target degree is the degree of the level `k'`, so the differential is `towerModel_d`
      rw [show levelDeg M (k' + 1) - 1 + 1 = levelDeg M k' - 1 by
        rw [levelDeg_succ]; omega]
      rw [towerModel_d hstep M s₀ k']
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.inv_hom_id_apply]
      change (towerModelXIso hstep M s₀ k').inv.hom
        (((tower hstep M s₀ (k' + 1)).d A).hom x) = 0
      rw [hx]
      exact map_zero _
  · -- all other differentials vanish by the shape of the complex
    rw [HomologicalComplex.shape (towerModel hstep M s₀) (levelDeg M k - 1) j hj]
    simp

/-- **The coaugmentation element is carried to `c₀` by `φ`.**  For the coaugmentation element
`x = (g, 0)` of the level `k₀` (with `hk : levelDeg M k₀ - 1 = 0`), its image in the model is
carried by the degree-`0` component of `φ` to the coaugmentation `c₀ : A ⟶ C⁰`. -/
lemma towerModel_coaug_apply
    (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s)
    (M : ℤ) (s₀ : Cell A C c₀ (M + 1))
    (φ : towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (levelDeg M k - 1) =
        (towerModelXIso hstep M s₀ k).hom ≫ (tower hstep M s₀ k).φ A)
    (k₀ : ℕ) (hk : levelDeg M k₀ - 1 = 0)
    (g : ↥((tower hstep M s₀ k₀).gen))
    (hg : (C.iCycles (levelDeg M k₀ - 1)).hom ((tower hstep M s₀ k₀).σ.hom g) =
      coaugElem A c₀ (levelDeg M k₀ - 1) hk) :
    (φ.f 0).hom ((HomologicalComplex.XIsoOfEq (towerModel hstep M s₀) hk.symm).inv.hom
      ((towerModelXIso hstep M s₀ k₀).inv.hom
        (⟨g, 0⟩ : ↥((tower hstep M s₀ k₀).G A)))) = c₀.hom 1 := by
  -- naturality of `XIsoOfEq` for the chain map `φ`
  have hnat := congrArg (fun (f : (towerModel hstep M s₀).X (levelDeg M k₀ - 1) ⟶ C.X 0) =>
      f.hom ((towerModelXIso hstep M s₀ k₀).inv.hom
        (⟨g, 0⟩ : ↥((tower hstep M s₀ k₀).G A))))
    (HomologicalComplex.XIsoOfEq_inv_naturality φ hk.symm)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [← hnat]
  -- the component `φ.f (levelDeg M k₀ - 1)` is `(tower k₀).φ` up to the canonical isomorphism
  have hkey : (φ.f (levelDeg M k₀ - 1)).hom
      ((towerModelXIso hstep M s₀ k₀).inv.hom (⟨g, 0⟩ : ↥((tower hstep M s₀ k₀).G A)))
      = coaugElem A c₀ (levelDeg M k₀ - 1) hk := by
    rw [hφ k₀]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [Iso.inv_hom_id_apply]
    simp [Cell.φ, Cell.φHom, LinearMap.coprod_apply, hg]
  rw [hkey]
  -- `coaugElem` is `c₀ 1`, and the two `XIsoOfEq`s cancel
  rw [coaugElem_eq_XIso]
  rw [← ConcreteCategory.comp_apply]
  have hcomp : (C.XIsoOfEq hk).inv ≫ (C.XIsoOfEq hk.symm).inv = 𝟙 (C.X 0) := by
    rw [HomologicalComplex.XIsoOfEq_inv_comp_XIsoOfEq_inv]
    simp
  rw [hcomp]
  simp

end Aux

/-- **The coaugmentation of the tower model.**  Given a level `k₀` of the tower whose degree is
`0` and a chain map `φ : towerModel ⟶ C` whose components are the maps `(tower k).φ` of the cells
(up to the canonical isomorphisms of the model), the coaugmentation generator of the level `k₀`
produces a coaugmentation `ε : A ⟶ P⁰` of the model which is a cocycle and is carried to the
coaugmentation `c₀` of `C` by `φ`. -/
theorem exists_towerCoaug {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1))
    (φ : Work.DSMX0U.towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (Work.DSMX0U.levelDeg M k - 1) = CategoryTheory.CategoryStruct.comp
        (Work.DSMX0U.towerModelXIso hstep M s₀ k).hom (Work.DSMX0U.Cell.φ A (Work.DSMX0U.tower hstep M s₀ k)))
    (k₀ : ℕ) (hk : Work.DSMX0U.levelDeg M k₀ - 1 = 0) :
    ∃ ε : ModuleCat.of A A ⟶ (Work.DSMX0U.towerModel hstep M s₀).X 0,
      (∀ j : ℤ, CategoryTheory.CategoryStruct.comp ε ((Work.DSMX0U.towerModel hstep M s₀).d 0 j) = 0) ∧
      CategoryTheory.CategoryStruct.comp ε (φ.f 0) = c₀ := by
  -- the coaugmentation generator of the level `k₀`
  obtain ⟨g, hg⟩ := (tower hstep M s₀ k₀).hcoaugσ hk
  -- its image `x = (g, 0)` in the term of the level `k₀`
  let x : ↥((tower hstep M s₀ k₀).G A) := ⟨g, 0⟩
  have hxd : ((tower hstep M s₀ k₀).d A).hom x = 0 := by
    simp only [x]
    simp [Cell.d, Cell.dHom, LinearMap.coprod_apply]
  -- the coaugmentation map `A ⟶ G` of the level, and its transport into the model
  let ε₀ : ModuleCat.of A A ⟶ (tower hstep M s₀ k₀).G A :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A ↥((tower hstep M s₀ k₀).G A) x)
  have hε₀ : ε₀.hom (1 : A) = x := by
    simp only [ε₀, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  refine ⟨ε₀ ≫ (towerModelXIso hstep M s₀ k₀).inv ≫
    (HomologicalComplex.XIsoOfEq (towerModel hstep M s₀) hk.symm).inv, ?_, ?_⟩
  · -- `ε` is a cocycle: its value is a cycle of the model (degree `0`)
    intro j
    simp only [Category.assoc]
    rw [HomologicalComplex.XIsoOfEq_inv_comp_d (towerModel hstep M s₀) hk.symm j]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply, hε₀]
    exact towerModel_d_apply_eq_zero hstep M s₀ k₀ x hxd j
  · -- `ε ≫ φ.f 0 = c₀`: the naturality of `XIsoOfEq`, the components of `φ`, and the
    -- defining property of the coaugmentation generator
    simp only [Category.assoc]
    rw [← HomologicalComplex.XIsoOfEq_inv_naturality φ hk.symm]
    rw [hφ k₀]
    have hkey : ((tower hstep M s₀ k₀).φ A).hom x = coaugElem A c₀ (levelDeg M k₀ - 1) hk := by
      simp only [x]
      simp [Cell.φ, Cell.φHom, LinearMap.coprod_apply, hg]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hε₀, Iso.inv_hom_id_apply, hkey]
    rw [coaugElem_eq_XIso]
    rw [← ConcreteCategory.comp_apply]
    have hcomp : (C.XIsoOfEq hk).inv ≫ (C.XIsoOfEq hk.symm).inv = 𝟙 (C.X 0) := by
      rw [HomologicalComplex.XIsoOfEq_inv_comp_XIsoOfEq_inv]
      simp
    rw [hcomp]
    simp

end Work.DSMX0U
