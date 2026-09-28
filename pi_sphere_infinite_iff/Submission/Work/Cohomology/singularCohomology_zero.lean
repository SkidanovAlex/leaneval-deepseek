import Mathlib
import Submission.Work.Cohomology.Singular

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology

noncomputable section

/-
# The zeroth singular cohomology of a path-connected space

We compute `H⁰(X; R) = R` for a path-connected space `X`.

The chain of isomorphisms is the following.

* `(singularCochainComplex R X).homology 0` is the kernel of the zeroth differential `d⁰` (there
  is no term in degree `-1`); this is `cohomology₀IsoKernel` below, via `ShortComplex` machinery
  and the identification of `K.sc 0` with the short complex `K.X 0 → K.X 1 → K.X 2`.
* The zeroth differential is the transpose of `d₁ : X₁ → X₀`; hence its kernel is
  `LinearMap.ker ((d₁).dualMap)` (see `dualDifferential_hom`).
* The augmentation `ε : X₀ → R` (` = π₀.fromChainComplexXZero ≫ Sigma.desc (fun _ => 1)`) is a
  linear functional which is `1` on every `0`-simplex; it is well defined because it factors
  through the cokernel of `d₁`.  Its values on the generators `sgen s` give the isomorphism
  `ker (d₁ᴴ) ≅ R`: surjectivity via `c ↦ c • ε` and injectivity via the fact that any two
  `0`-simplices of the singular simplicial set of a path-connected space are joined by an edge
  (`pi₀_mk_base`), so that `φ (sgen s) = φ (sgen s₀)` for `φ` in the kernel (`eval_constancy'`).

A small amount of "defeq plumbing" is needed because `singularChains R X` is an `abbrev` for
`(TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)` through a `def`
(`TopCat.toSSet`/`singularChainComplexFunctor`), so that the two expressions are only
propositionally (not definitionally, at the transparency used by tactics) equal.  The `set_option`
below makes `isDefEq` ignore the transparency mode, which resolves this.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits Simplicial

/-- A chosen point of a path-connected space. -/
def basePoint (X : TopCat) [PathConnectedSpace X] : X :=
  Classical.choice (PathConnectedSpace.nonempty (X := X))

/-- The `0`-simplex of the singular simplicial set of `X` corresponding to the chosen base
point. -/
def baseSimplex (X : TopCat) [PathConnectedSpace X] :
    (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌) :=
  (TopCat.toSSetObj₀Equiv (X := X)).symm (basePoint X)

/-- The `0`-chain of `X` given by a `0`-simplex. -/
def sgen (R : Type) [CommRing R] (X : TopCat)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)) :
    (Work.Cohomology.singularChains R X).X 0 :=
  ModuleCat.Hom.hom (SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of R R) s) 1

/-- The **augmentation** `X₀ → R`: the linear functional which takes the value `1` on every
`0`-simplex of `X`.  It is defined through the cokernel of `d₁`, which is
`∐ (fun _ : π₀ X ↦ R)`. -/
def aug (R : Type) [CommRing R] (X : TopCat) :
    (Work.Cohomology.singularChains R X).X 0 ⟶ ModuleCat.of R R :=
  SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of R R) ≫
    Sigma.desc (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => 𝟙 (ModuleCat.of R R))

/-- The augmentation takes the value `1` on every `0`-simplex. -/
theorem aug_ι (R : Type) [CommRing R] (X : TopCat)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)) :
    SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of R R) s ≫ aug R X
      = 𝟙 (ModuleCat.of R R) := by
  rw [aug, ← Category.assoc, SSet.π₀.comp_fromChainComplexXZero, Sigma.ι_desc]

/-- The augmentation kills the differential `d₁`. -/
theorem aug_d (R : Type) [CommRing R] (X : TopCat) :
    (Work.Cohomology.singularChains R X).d 1 0 ≫ aug R X = 0 := by
  have hd : (Work.Cohomology.singularChains R X).d 1 0 =
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d 1 0 := rfl
  rw [aug, ← Category.assoc, hd, SSet.π₀.d_fromChainComplexXZero, zero_comp]

/-- The augmentation takes the value `1` on the generators `sgen`. -/
theorem aug_sgen (R : Type) [CommRing R] (X : TopCat)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)) :
    ModuleCat.Hom.hom (aug R X) (sgen R X s) = 1 := by
  have h := congrArg ModuleCat.Hom.hom (aug_ι R X s)
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h 1

/-- The augmentation lies in the kernel of the zeroth differential. -/
theorem dualDifferential_aug (R : Type) [CommRing R] (X : TopCat) :
    ModuleCat.Hom.hom (Work.Cohomology.dualDifferential R X 0)
      (ModuleCat.Hom.hom (aug R X)) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (aug_d R X)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  rw [← h]
  rfl

/-- In a path-connected space, all `0`-simplices of the singular simplicial set represent the
same connected component. -/
theorem pi₀_mk_base (X : TopCat) [PathConnectedSpace X]
    (s : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)) :
    SSet.π₀.mk s = SSet.π₀.mk (baseSimplex X) := by
  have hjoin : Joined (TopCat.toSSetObj₀Equiv (X := X) s)
      (TopCat.toSSetObj₀Equiv (X := X) (baseSimplex X)) := PathConnectedSpace.joined _ _
  obtain ⟨p⟩ := hjoin
  have e : SSet.Edge s (baseSimplex X) := by
    rw [← Equiv.symm_apply_apply (TopCat.toSSetObj₀Equiv (X := X)) s,
      ← Equiv.symm_apply_apply (TopCat.toSSetObj₀Equiv (X := X)) (baseSimplex X)]
    exact (TopCat.toSSetObjEdgeEquiv (X := X)).symm (TopCat.pathEquiv.symm p)
  exact SSet.π₀.sound e

/-- Any linear functional on the `0`-chains which vanishes on the differential `d₁` is constant
on the generators `sgen`, when `X` is path-connected. -/
theorem eval_constancy (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X]
    (f : (Work.Cohomology.singularChains R X).X 0 →ₗ[R] R)
    (hf : f.comp ((Work.Cohomology.singularChains R X).d 1 0).hom = 0)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)) :
    f (sgen R X s) = f (sgen R X (baseSimplex X)) := by
  have hmem : (Work.Cohomology.singularChains R X).d 1 0 ≫ ModuleCat.ofHom f = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
    exact hf
  have hmem' : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d 1 0
      ≫ ModuleCat.ofHom f = 0 := by
    rw [show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d 1 0 =
      (Work.Cohomology.singularChains R X).d 1 0 from rfl]
    exact hmem
  obtain ⟨h, hfac⟩ := CokernelCofork.IsColimit.desc'
    (SSet.isColimitCokernelCoforkChainComplexDOneZero (TopCat.toSSet.obj X) (ModuleCat.of R R))
    (ModuleCat.ofHom f) hmem'
  have key : ∀ s, f (sgen R X s) =
      ModuleCat.Hom.hom h
        (ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => ModuleCat.of R R)
          (SSet.π₀.mk s)) 1) := by
    intro s
    rw [show f (sgen R X s) = ModuleCat.Hom.hom
        (SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of R R) s
          ≫ ModuleCat.ofHom f) 1 from by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      rfl]
    rw [← hfac, CokernelCofork.π_ofπ]
    rw [← Category.assoc, SSet.π₀.comp_fromChainComplexXZero]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  rw [key s, key (baseSimplex X), pi₀_mk_base X s]

/-- The augmentation, as an element of the kernel of the zeroth differential. -/
def augKer (R : Type) [CommRing R] (X : TopCat) :
    LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.dualDifferential R X 0)) :=
  ⟨ModuleCat.Hom.hom (aug R X), by
    rw [LinearMap.mem_ker]
    exact dualDifferential_aug R X⟩

/-- Evaluation of a functional killing `d₁` at the base generator. -/
def ev (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] :
    LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.dualDifferential R X 0)) →ₗ[R] R where
  toFun φ := φ.1 (sgen R X (baseSimplex X))
  map_add' φ ψ := by rw [Submodule.coe_add, LinearMap.add_apply]
  map_smul' c φ := by rw [Submodule.coe_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The inverse of `ev`: a scalar multiple of the augmentation. -/
def mk (R : Type) [CommRing R] (X : TopCat) :
    R →ₗ[R] LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.dualDifferential R X 0)) :=
  LinearMap.toSpanSingleton R _ (augKer R X)

/-- `ev` is a retraction of `mk`. -/
theorem ev_mk (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] (c : R) :
    ev R X (mk R X c) = c := by
  rw [mk, LinearMap.toSpanSingleton_apply]
  change (c • (augKer R X).1) (sgen R X (baseSimplex X)) = c
  rw [LinearMap.smul_apply, show (augKer R X).1 = ModuleCat.Hom.hom (aug R X) from rfl, aug_sgen,
    smul_eq_mul, mul_one]

/-- `ev` is injective. -/
theorem ev_eq_zero (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X]
    (φ : LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.dualDifferential R X 0)))
    (hφ : ev R X φ = 0) : φ = 0 := by
  have hf : φ.1.comp ((Work.Cohomology.singularChains R X).d 1 0).hom = 0 :=
    LinearMap.mem_ker.mp φ.2
  have hmem : (Work.Cohomology.singularChains R X).d 1 0 ≫ ModuleCat.ofHom φ.1 = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
    exact hf
  have hmem' : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d 1 0
      ≫ ModuleCat.ofHom φ.1 = 0 := by
    rw [show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d 1 0 =
      (Work.Cohomology.singularChains R X).d 1 0 from rfl]
    exact hmem
  obtain ⟨h, hfac⟩ := CokernelCofork.IsColimit.desc'
    (SSet.isColimitCokernelCoforkChainComplexDOneZero (TopCat.toSSet.obj X) (ModuleCat.of R R))
    (ModuleCat.ofHom φ.1) hmem'
  have hh : h = 0 := by
    apply Sigma.hom_ext h 0
    intro y
    rw [comp_zero]
    obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective y
    rw [← SSet.π₀.comp_fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of R R) s,
      Category.assoc]
    rw [CokernelCofork.π_ofπ] at hfac
    rw [hfac]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
    apply LinearMap.ext_ring
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    show φ.1 (sgen R X s) = 0
    rw [eval_constancy R X φ.1 hf s]
    exact hφ
  rw [hh, comp_zero] at hfac
  have hof : ModuleCat.ofHom φ.1 = 0 := hfac.symm
  have hfl : φ.1 = 0 := by
    have := congrArg ModuleCat.Hom.hom hof
    simpa [ModuleCat.hom_ofHom, ModuleCat.hom_zero] using this
  exact Subtype.ext hfl

/-- `ev` is a bijection. -/
theorem ev_bijective (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] :
    Function.Bijective (ev R X) :=
  ⟨fun φ ψ h => sub_eq_zero.mp (ev_eq_zero R X (φ - ψ) (by rw [map_sub, h, sub_self])),
   fun c => ⟨mk R X c, ev_mk R X c⟩⟩

/-- The kernel of the zeroth differential of the singular cochain complex is isomorphic to `R`. -/
theorem kerDualDifferential_iso (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] :
    Nonempty (LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.dualDifferential R X 0))
      ≃ₗ[R] R) :=
  ⟨LinearEquiv.ofBijective (ev R X) (ev_bijective R X)⟩

/-- The zeroth singular cohomology of a path-connected space with coefficients in a nontrivial
commutative ring is the coefficient ring itself.  (This is the degree-zero case of the universal
coefficient theorem, combined with Mathlib's computation of `H₀`.) -/
theorem singularCohomology_zero (R : Type) [CommRing R] [Nontrivial R] (X : TopCat)
    [PathConnectedSpace X] :
    Nonempty (Work.Cohomology.singularCohomology R 0 X ≅ ModuleCat.of R R) := by
  let K := Work.Cohomology.singularCochainComplex R X
  have : K.HasHomology 0 := inferInstance
  have hf : (K.sc 0).f = 0 := by rfl
  have c1 : Work.Cohomology.singularCohomology R 0 X ≅ K.cycles 0 :=
    (ShortComplex.asIsoHomologyπ (K.sc 0) hf).symm
  have c2 : K.cycles 0 ≅ (K.sc' 0 0 1).cycles := K.cyclesIsoSc' 0 0 1 (by simp) (by simp)
  have c3 : (K.sc' 0 0 1).cycles ≅ kernel (K.d 0 1) := ShortComplex.cyclesIsoKernel _
  have hd : K.d 0 1 = Work.Cohomology.dualDifferential R X 0 := by
    simp only [K, Work.Cohomology.singularCochainComplex, CochainComplex.of, CochainComplex.of.d]
    rfl
  rw [hd] at c3
  have c4 : kernel (Work.Cohomology.dualDifferential R X 0) ≅
      ModuleCat.of R (LinearMap.ker (ModuleCat.Hom.hom
        (Work.Cohomology.dualDifferential R X 0))) :=
    ModuleCat.kernelIsoKer _
  have e : LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.dualDifferential R X 0)) ≃ₗ[R] R :=
    (kerDualDifferential_iso R X).some
  have c5 : ModuleCat.of R (LinearMap.ker (ModuleCat.Hom.hom
        (Work.Cohomology.dualDifferential R X 0))) ≅ ModuleCat.of R R := e.toModuleIso
  exact ⟨c1 ≪≫ c2 ≪≫ c3 ≪≫ c4 ≪≫ c5⟩

end

end Work.Cohomology
