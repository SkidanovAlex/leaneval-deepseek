import Mathlib
import Submission.Work.Serre.serreC0KillHomologyDefs
import Submission.Work.Serre.serreC0KillHomologySets
import Submission.Work.Serre.serreC0KillUAcyclic
import Submission.Work.Serre.serreC0KillShellHomology
import Submission.Work.Serre.serreC0KillShellImage
import Submission.Work.Serre.serreC0KillZHomeo
import Submission.Work.Serre.serreC0KillRho
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.RatHurewicz.CompressRelToRelPi

/-!
# Auxiliary lemmas for `Work.Serre.serreC0KillHomology`

The main theorem computes `H_{n+1}(attachCells n Y ι f)` as the quotient of `H_{n+1}(Y)` by the
span of the Hurewicz classes of the attaching maps.  This file collects the pieces of the proof:

* generic module-category bookkeeping (quotients along linear equivalences);
* `H_{n+1}(U) ≅ H_{n+1}(Y)` via the retraction `ρ` and the homeomorphism `Y ≅ KillA f`;
* the identification of the image of `H_{n+1}(Z)` with the span of the Hurewicz classes;
* the Mayer–Vietoris cokernel computation.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-! ## Generic module-category bookkeeping -/

/-- Transporting a quotient along a linear equivalence, with the target submodule given
explicitly. -/
def quotCongrIso {M N : ModuleCat ℤ} (e : ↥M ≃ₗ[ℤ] ↥N) (P : Submodule ℤ ↥M)
    (Q : Submodule ℤ ↥N) (h : Submodule.map (e : ↥M →ₗ[ℤ] ↥N) P = Q) :
    (ModuleCat.of ℤ (↥M ⧸ P)) ≅ (ModuleCat.of ℤ (↥N ⧸ Q)) := by
  have hP : (AddCommGroup.toIntModule (↥M ⧸ P)) = Submodule.Quotient.module P :=
    Subsingleton.elim _ _
  have hQ : (AddCommGroup.toIntModule (↥N ⧸ Q)) = Submodule.Quotient.module Q :=
    Subsingleton.elim _ _
  rw [hP, hQ]
  exact LinearEquiv.toModuleIso (Submodule.Quotient.equiv (P := P) (Q := Q) e h)

/-- An isomorphism in `ModuleCat ℤ` gives a linear equivalence of the underlying modules. -/
noncomputable def linEquivOfIso {M N : ModuleCat ℤ} (φ : M ⟶ N) [IsIso φ] : ↥M ≃ₗ[ℤ] ↥N :=
  LinearEquiv.ofBijective (ModuleCat.Hom.hom φ) (ConcreteCategory.bijective_of_isIso φ)

/-- **The first isomorphism theorem, categorically**: if the range of `a` is the kernel of a
surjection `b`, then `b` induces an isomorphism from the quotient of the source of `b` by the
range of `a` to the target of `b`. -/
theorem quotRangeIsoOfSurjKer {M M' N : ModuleCat ℤ} (a : M' ⟶ M) (b : M ⟶ N)
    (hb : Function.Surjective (ModuleCat.Hom.hom b))
    (h : LinearMap.ker (ModuleCat.Hom.hom b) = LinearMap.range (ModuleCat.Hom.hom a)) :
    Nonempty (ModuleCat.of ℤ (↥M ⧸ LinearMap.range (ModuleCat.Hom.hom a)) ≅ N) := by
  refine ⟨?_⟩
  have hP : (AddCommGroup.toIntModule (↥M ⧸ LinearMap.range (ModuleCat.Hom.hom a)))
      = Submodule.Quotient.module (LinearMap.range (ModuleCat.Hom.hom a)) :=
    Subsingleton.elim _ _
  rw [hP]
  exact ((Submodule.quotEquivOfEq (p := LinearMap.range (ModuleCat.Hom.hom a))
    (p' := LinearMap.ker (ModuleCat.Hom.hom b)) h.symm).toModuleIso).trans
      (LinearMap.quotKerEquivOfSurjective (ModuleCat.Hom.hom b) hb).toModuleIso

section Biprod

variable {C D : ChainComplex (ModuleCat ℤ) ℕ}

/-- If the `k`-th homology of `D` vanishes, the homology of the projection `C ⊞ D ⟶ C` is an
isomorphism. -/
theorem homologyMap_biprod_fst_isIso (k : ℕ) (hD : IsZero (D.homology k)) :
    IsIso (HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k) := by
  refine ⟨HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k, ?_, ?_⟩
  · have htot : HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k
          ≫ HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k
        + HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k
          ≫ HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) k
        = 𝟙 ((C ⊞ D).homology k) := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]
    have hB : HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k
        ≫ HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) k = 0 := by
      have h0 : HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k = 0 :=
        IsZero.eq_zero_of_tgt hD _
      rw [h0, zero_comp]
    rw [hB, add_zero] at htot
    exact htot
  · rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst,
      HomologicalComplex.homologyMap_id]

end Biprod

/-! ## The Hurewicz classes of the attaching maps -/

/-- The `i`-th attaching map, composed with the inclusion of the old part: a map
`S^{n+1} → ↥(KillA f)`. -/
abbrev killAIMap (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    C(Work.RatHurewicz.cellSphere n, ↥(KillA f)) :=
  ⟨fun z => ⟨Work.RatHurewicz.attachIncl n Y ι f (f i z), ⟨f i z, rfl⟩⟩, by fun_prop⟩

/-- Two proofs of `1 ≤ m` give the same Hurewicz class. -/
theorem hurewiczClass_proof_irrel {m : ℕ} {X : Type} [TopologicalSpace X] (h₁ h₂ : 1 ≤ m)
    (g : C(Work.Stems.sphere m, X)) :
    Work.Stems.hurewiczClass m h₁ g = Work.Stems.hurewiczClass m h₂ g := by
  have he : h₁ = h₂ := Subsingleton.elim _ _
  rw [he]

/-- The span of the Hurewicz classes of the attaching maps, viewed in `H_{n+1}(KillA f)`. -/
abbrev killHurewiczSpan (hn : 1 ≤ n) (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Submodule ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillA f))).homology (n+1)) :=
  Submodule.span ℤ (Set.range (fun i : ι => Work.Stems.hurewiczClass (n+1) (by omega)
    (⟨fun z => ⟨Work.RatHurewicz.attachIncl n Y ι f (f i z), ⟨f i z, rfl⟩⟩, by fun_prop⟩ :
      C(Work.RatHurewicz.cellSphere n, ↥(KillA f)))))

/-! ## The inclusion of the old part in the outer part -/

/-- A retraction of `KillU f` onto `KillA f` induces an isomorphism in homology. -/
theorem isIso_homologyMap_retractKillU (f : ι → C(Work.RatHurewicz.cellSphere n, Y))
    (ρ : C(↥(KillU f), ↥(KillA f)))
    (hρ : ∀ a : ↥(KillA f),
      ρ ⟨(a : KillX f), KillA_subset_KillU f a.2⟩ = a) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(KillU f)) (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) k) := by
  have hρ' : ∀ (a : ↥(KillA f)) (h : (a : KillX f) ∈ KillU f),
      ρ ⟨(a : KillX f), h⟩ = a := by
    intro a h
    have hEq : (⟨(a : KillX f), h⟩ : ↥(KillU f))
        = ⟨(a : KillX f), KillA_subset_KillU f a.2⟩ := Subtype.ext rfl
    rw [hEq]
    exact hρ a
  let A' : Set ↥(KillU f) := {x | (x : KillX f) ∈ KillA f}
  let incA'U : C(↥A', ↥(KillU f)) := ⟨Subtype.val, continuous_subtype_val⟩
  let incAU : C(↥(KillA f), ↥(KillU f)) :=
    ⟨fun a => ⟨(a : KillX f), KillA_subset_KillU f a.2⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩
  let θh : ↥A' ≃ₜ ↥(KillA f) :=
    { toFun := fun x => ⟨(((x : ↥A') : ↥(KillU f)) : KillX f), x.2⟩
      invFun := fun a => ⟨⟨(a : KillX f), KillA_subset_KillU f a.2⟩, a.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun a => Subtype.ext rfl
      continuous_toFun :=
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk incAU.continuous _ }
  let θc : C(↥A', ↥(KillA f)) := ⟨θh.toFun, θh.continuous_toFun⟩
  let E : TopCat.of ↥A' ≅ TopCat.of ↥(KillA f) := TopCat.isoOfHomeo θh
  have hEh : E.hom = TopCat.ofHom θc :=
    TopCat.isoOfHomeo_hom (X := TopCat.of ↥A') (Y := TopCat.of ↥(KillA f)) θh
  have hρcomp : ρ.comp incA'U = θc := by
    apply ContinuousMap.ext
    intro x
    exact hρ' ⟨(((x : ↥A') : ↥(KillU f)) : KillX f), x.2⟩ (((x : ↥A') : ↥(KillU f))).2
  have hcomp : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥A') (TopCat.of ↥(KillU f)) (TopCat.ofHom incA'U)) k
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(KillU f)) (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) k
      = HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥A') (TopCat.of ↥(KillA f)) E.hom) k := by
    rw [← HomologicalComplex.homologyMap_comp, ← Work.Cohomology.chainMap_comp',
      ← TopCat.ofHom_comp, hρcomp, hEh]
  haveI h1 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥A') (TopCat.of ↥(KillU f)) (TopCat.ofHom incA'U)) k) :=
    isIso_inclChains_KillU f k
  haveI hc : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥A') (TopCat.of ↥(KillA f)) E.hom) := by
    rw [Work.Cohomology.chainMap]
    exact Functor.map_isIso _ _
  haveI h2 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥A') (TopCat.of ↥(KillA f)) E.hom) k) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso
      (asIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥A') (TopCat.of ↥(KillA f)) E.hom)) k)
  haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥A') (TopCat.of ↥(KillU f)) (TopCat.ofHom incA'U)) k
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(KillU f)) (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) k) := by
    rw [hcomp]
    exact h2
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of ↥A')
      (TopCat.of ↥(KillU f)) (TopCat.ofHom incA'U)) k)
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillU f))
      (TopCat.of ↥(KillA f)) (TopCat.ofHom ρ)) k)

/-! ## The shell range -/

/-- For **any** homeomorphism `e : ↥(KillZ f) ≅ Σ i, S`, the image in `H_{n+1}(KillA f)` of the
composite `KillShellToA f ∘ e` is the span of the Hurewicz classes of the attaching maps. -/
theorem range_homologyMap_KillShellToA_comp (hn : 1 ≤ n)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y))
    (e : ↥(KillZ f) ≃ₜ (Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) :
    LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(KillZ f)) (TopCat.of ↥(KillA f))
        (TopCat.ofHom ((KillShellToA f).comp ⟨e, e.continuous_toFun⟩))) (n+1)))
      = killHurewiczSpan (n := n) (Y := Y) (ι := ι) hn f := by
  set S : TopCat := TopCat.of (Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2))) with hS
  have hred : ∀ (e : ↥(KillZ f) ≃ₜ (Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))),
      LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f)) (TopCat.of ↥(KillA f))
          (TopCat.ofHom ((KillShellToA f).comp ⟨e, e.continuous_toFun⟩))) (n+1)))
      = LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ S (TopCat.of ↥(KillA f))
          (TopCat.ofHom (KillShellToA f))) (n+1))) := by
    intro e
    let E : TopCat.of ↥(KillZ f) ≅ S := TopCat.isoOfHomeo e
    have hEh : E.hom = TopCat.ofHom (⟨e, e.continuous_toFun⟩ :
        C(↥(KillZ f), (Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2))))) :=
      TopCat.isoOfHomeo_hom (X := TopCat.of ↥(KillZ f)) (Y := S) e
    have hdec : Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f)) (TopCat.of ↥(KillA f))
        (TopCat.ofHom ((KillShellToA f).comp ⟨e, e.continuous_toFun⟩))
        = Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f)) S E.hom
          ≫ Work.Cohomology.chainMap ℤ S (TopCat.of ↥(KillA f))
            (TopCat.ofHom (KillShellToA f)) := by
      rw [hEh, ← Work.Cohomology.chainMap_comp', ← TopCat.ofHom_comp]
    have hhom : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of ↥(KillZ f)) (TopCat.of ↥(KillA f))
          (TopCat.ofHom ((KillShellToA f).comp ⟨e, e.continuous_toFun⟩))) (n+1)
        = HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of ↥(KillZ f)) S E.hom) (n+1)
          ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ S
            (TopCat.of ↥(KillA f)) (TopCat.ofHom (KillShellToA f))) (n+1) := by
      rw [hdec, HomologicalComplex.homologyMap_comp]
    haveI hc : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f)) S E.hom) := by
      rw [Work.Cohomology.chainMap]
      exact Functor.map_isIso _ _
    haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(KillZ f)) S E.hom) (n+1)) :=
      Iso.isIso_hom (HomologicalComplex.homologyMapIso
        (asIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f)) S E.hom)) (n+1))
    have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of ↥(KillZ f)) S E.hom) (n+1))) :=
      (ConcreteCategory.bijective_of_isIso _).2
    rw [hhom, ModuleCat.hom_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  obtain ⟨e', he'⟩ := serreC0KillShellImage (n := n) hn ι f
  rw [hred e, ← hred e']
  exact he'

/-! ## The Hurewicz classes and the homeomorphism `Y ≅ KillA f` -/

/-- The Hurewicz class of `f i`, pushed forward along the homeomorphism `Y ≅ ↥(KillA f)`, is the
Hurewicz class of the composite `KillA`-valued map. -/
theorem hurewiczClass_rangeHomeo (hn : 1 ≤ n) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of Y)
        (TopCat.of ↥(KillA f)) (TopCat.ofHom ⟨Work.RatHurewicz.rangeHomeo n Y ι f,
          (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩)) (n+1)))
      (Work.Stems.hurewiczClass (n+1) (by omega) (f i))
    = Work.Stems.hurewiczClass (n+1) (by omega) (killAIMap (n := n) (Y := Y) (ι := ι) f i) := by
  have hnat := Work.Stems.hurewiczClass_natural (n+1) (by omega)
    (⟨Work.RatHurewicz.rangeHomeo n Y ι f,
      (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩ : C(Y, ↥(KillA f))) (f i)
  have hcomp : (⟨Work.RatHurewicz.rangeHomeo n Y ι f,
      (Work.RatHurewicz.rangeHomeo n Y ι f).continuous_toFun⟩ : C(Y, ↥(KillA f))).comp (f i)
      = killAIMap (n := n) (Y := Y) (ι := ι) f i :=
    ContinuousMap.ext (fun z => rfl)
  rw [hcomp] at hnat
  exact hnat.symm

/-! ## The Mayer–Vietoris cokernel -/

/-- **The Mayer–Vietoris cokernel.**  If `H_n(U ∩ V) = 0`, the `(n+1)`-st homology of `X` is the
quotient of `H_{n+1}(U) ⊞ H_{n+1}(V)` by the image of `H_{n+1}(U ∩ V)`. -/
theorem mvCoker (f : ι → C(Work.RatHurewicz.cellSphere n, Y))
    (hZ : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(KillZ f))).homology n)) :
    Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of (KillX f))).homology (n+1)) ≅
      ModuleCat.of ℤ (↥(Work.Cohomology.HBiprod (X := TopCat.of (KillX f)) (KillU f) (KillV f) (n+1)) ⧸
        LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.mvLeft (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1))))) := by
  have hU : IsOpen (KillU f) := isOpen_KillU f
  have hV : IsOpen (KillV f) := isOpen_KillV f
  have hcov : KillU f ∪ KillV f = Set.univ := KillU_union_KillV f
  have hZ' : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(KillU f ∩ KillV f))).homology n) := hZ
  haveI hsub : Subsingleton ↥(Work.Cohomology.HInter (X := TopCat.of (KillX f)) (KillU f) (KillV f) n) :=
    ModuleCat.subsingleton_of_isZero hZ'
  have hδ : Work.Cohomology.mvδ (X := TopCat.of (KillX f)) (KillU f) (KillV f) n = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  have hb : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.mvRight (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1))) := by
    intro y
    have hex := Work.Cohomology.mv_H_exact₃ (X := TopCat.of (KillX f)) (KillU f) (KillV f) n
    rw [ShortComplex.moduleCat_exact_iff] at hex
    have hy : (Work.Cohomology.mvδ (X := TopCat.of (KillX f)) (KillU f) (KillV f) n).hom y = 0 := by
      rw [hδ]
      simp
    obtain ⟨x, hx⟩ := hex y hy
    exact ⟨x, hx⟩
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.mvRight (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1)))
      = LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.mvLeft (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1))) := by
    refine le_antisymm ?_ ?_
    · intro y hy
      have hex := Work.Cohomology.mv_H_exact₂ (X := TopCat.of (KillX f)) (KillU f) (KillV f) (n+1)
      rw [ShortComplex.moduleCat_exact_iff] at hex
      exact hex y hy
    · rw [LinearMap.range_le_ker_iff]
      have h0 : HomologicalComplex.homologyMap (Work.Cohomology.mvLeft (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1)
          ≫ HomologicalComplex.homologyMap (Work.Cohomology.mvRight (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1)
          = 0 := by
        rw [← HomologicalComplex.homologyMap_comp, Work.Cohomology.mvComp,
          HomologicalComplex.homologyMap_zero]
      have h1 := congrArg ModuleCat.Hom.hom h0
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h1
      exact h1
  obtain ⟨e⟩ := quotRangeIsoOfSurjKer
    (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1))
    (HomologicalComplex.homologyMap (Work.Cohomology.mvRight (X := TopCat.of (KillX f)) (KillU f) (KillV f)) (n+1)) hb hker
  exact ⟨(Work.Cohomology.smallIso (X := TopCat.of (KillX f)) (KillU f) (KillV f) hU hV hcov (n+1)).symm ≪≫ e.symm⟩

/-! ## The first component of the Mayer–Vietoris map -/

/-- The singular chain complex of a topological space is the chain complex of its singular
simplicial set (definitional). -/
theorem chainMap_eq_chainComplexMap {Y Z : TopCat} (g : Y ⟶ Z) :
    Work.Cohomology.chainMap ℤ Y Z g
      = SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of ℤ ℤ) := rfl

/-- The composite of the first Mayer–Vietoris map with the projection onto the `U`-factor is the
chain map of the inclusion `U ∩ V ↪ U`. -/
theorem mvLeft_comp_fst {X : TopCat} (U V : Set X) :
    Work.Cohomology.mvLeft U V ≫ biprod.fst
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U)
          (TopCat.ofHom (Work.Cohomology.inclUVU U V).hom) := by
  have h1 : Work.Cohomology.mvLeft U V = biprod.lift
      (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.inclUVU U V)) (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.inclUVV U V))
        (ModuleCat.of ℤ ℤ)) := rfl
  have h2 : biprod.lift
      (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.inclUVU U V)) (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.inclUVV U V))
        (ModuleCat.of ℤ ℤ)) ≫ biprod.fst
      = SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.inclUVU U V))
          (ModuleCat.of ℤ ℤ) :=
    biprod.lift_fst _ _
  exact (congrArg (fun k => k ≫ biprod.fst) h1).trans
    (h2.trans (chainMap_eq_chainComplexMap
      (TopCat.ofHom (Work.Cohomology.inclUVU U V).hom)).symm)

end

end Work.Serre
