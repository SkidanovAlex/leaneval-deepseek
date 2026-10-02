import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.Thom.relCohMap_comp
import Submission.Work.Thom.relCohMap_id
import Submission.Work.ThomBordism.tubeLocalDegreeGlobalSign
import Submission.Work.Thom.mixedCupC_pairNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The zero section of the normal total space -/

/-- **The zero section of the normal total space** `ν = NormalTotal E`, i.e. `x ↦ (x, 0)`. -/
def zeroSectionNormal (E : EmbeddingData V (8 + k)) : C(V.pt, NormalTotal E) :=
  ⟨fun x => ⟨(x, 0), zero_mem_normalSpace E x⟩,
    Continuous.subtype_mk (Continuous.prodMk continuous_id continuous_const)
      (fun x => zero_mem_normalSpace E x)⟩

@[simp] theorem zeroSectionNormal_apply (E : EmbeddingData V (8 + k)) (x : V.pt) :
    (zeroSectionNormal E x : NormalTotal E) = ⟨(x, 0), zero_mem_normalSpace E x⟩ := rfl

@[simp] theorem zeroSectionNormal_proj (E : EmbeddingData V (8 + k)) (x : V.pt) :
    NormalTotal.proj (zeroSectionNormal E x) = x := rfl

@[simp] theorem zeroSectionNormal_vec (E : EmbeddingData V (8 + k)) (x : V.pt) :
    NormalTotal.vec (zeroSectionNormal E x) = 0 := rfl


/-! ## Degree bridges for the relative pairing and the relative pullback -/

/-- **The relative Kronecker pairing across a change of degrees.** -/
lemma relKronH_bridgeA {X : TopCat} {A : Set X} {a b : ℕ} (h : a = b)
    (β : (relComplex ℤ X A).homology a) (c : (relChains X A).homology b) :
    relKronH X A a β (h.symm ▸ c) = relKronH X A b (h ▸ β) c := by
  cases h
  rfl

/-- **The relative pullback commutes with a change of degrees.** -/
lemma relCohMap_cast {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y}
    (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B) {a b : ℕ} (h : a = b)
    (y : Work.Thom.RelCoh ℤ a Y B) :
    (Work.Thom.relCohMap f A B hf ℤ b).hom (h ▸ y)
      = h ▸ ((Work.Thom.relCohMap f A B hf ℤ a).hom y) := by
  cases h
  rfl


/-- A change of degrees commutes with scalar multiplication. -/
lemma cast_smul {M : ℕ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, Module ℤ (M n)]
    {a b : ℕ} (h : a = b) (c : ℤ) (y : M a) : h ▸ (c • y) = c • (h ▸ y) := by
  cases h
  rfl

/-- A change of degrees commutes with negation (stated for the relative cohomology itself, so that
the type family is not left as a metavariable). -/
lemma cast_neg_rel {X : TopCat} {A : Set X} {a b : ℕ} (h : a = b)
    (y : Work.Cohomology.relCohomology ℤ X A a) :
    (h ▸ (-y) : Work.Cohomology.relCohomology ℤ X A b) = -(h ▸ y) := by
  cases h
  rfl

/-- `Work.Cohomology.mixedCup` and `Work.Thom.mixedCupC` are the same pairing (the latter is the
former with the space written as `TopCat.of B`). -/
lemma mixedCup_topCatOf_eq_mixedCupC (B : Type) [TopologicalSpace B] (A : Set B) (m n : ℕ) :
    Work.Cohomology.mixedCup (TopCat.of B) A m n = Work.Thom.mixedCupC ℤ A m n := rfl

/-- The relative Kronecker pairing is additive in its first variable. -/
lemma relKronH_neg_left {X : TopCat} {A : Set X} {n : ℕ}
    (β : (relComplex ℤ X A).homology n) (c : (relChains X A).homology n) :
    relKronH X A n (-β) c = - relKronH X A n β c := by
  have h := LinearMap.map_neg (relKronH X A n) β
  rw [h]
  rfl

/-- The relative Kronecker pairing is additive in its second variable. -/
lemma relKronH_neg_right {X : TopCat} {A : Set X} {n : ℕ}
    (β : (relComplex ℤ X A).homology n) (c : (relChains X A).homology n) :
    relKronH X A n β (-c) = - relKronH X A n β c :=
  LinearMap.map_neg (relKronH X A n β) c

/-- The mixed cup product is additive in its second variable. -/
lemma mixedCup_neg_right (X : TopCat) (A : Set X) (m n : ℕ)
    (x : Work.Cohomology.singularCohomology ℤ m X) (u : Work.Cohomology.relCohomology ℤ X A n) :
    mixedCup X A m n x (-u) = - mixedCup X A m n x u :=
  LinearMap.map_neg (mixedCup X A m n x) u


/-- The zero section of the normal total space, as the composition of the zero section of the
gluing-data normal bundle with the identification of the total spaces. -/
theorem comp_zeroSection_eq_zeroSectionNormal {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ι : Type} (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (ψ : Z.TotalSpace ≃ₜ NormalTotal E)
    (hproj : ∀ p : Z.TotalSpace, NormalTotal.proj (ψ p) = p.1)
    (hvec : ∀ x : V.pt, NormalTotal.vec (ψ (Work.Thom.zeroSection Z x)) = 0) :
    (ψ : C(Z.TotalSpace, NormalTotal E)).comp (Work.Thom.zeroSection Z) = zeroSectionNormal E := by
  apply ContinuousMap.ext
  intro x
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact hproj _
  · exact hvec _

/-! ## The general homeomorphism transfer of the relative pairing -/

/-- **Naturality of the relative Kronecker pairing under a homeomorphism of pairs**, in the form
needed for the transport of the local degree along the identification of the normal bundle with its
gluing-data model. -/
theorem relKronH_homeoPair {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B)
    (hw : CategoryTheory.CategoryStruct.comp (subtypeIncl X A) (TopCat.ofHom e)
      = CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.subtype hAB)) (subtypeIncl Y B))
    (n : ℕ) (b : Work.Thom.RelCoh ℤ n Y B)
    (z : (relChains X A).homology n) (z' : (relChains Y B).homology n)
    (hz : (HomologicalComplex.homologyMap (relChainsMapOf X Y A B (TopCat.ofHom e)
        (TopCat.ofHom (e.subtype hAB)) hw) n).hom z = z') :
    relKronH X A n
        ((HomologicalComplex.homologyMap (relComplexMap ℤ A B (TopCat.ofHom e)
          (fun x hx => (hAB x).mp hx)) n).hom b) z
      = relKronH Y B n b z' := by
  have h := relKronH_natural (X := X) (Y := Y) (A := A) (B := B) (TopCat.ofHom e)
    (TopCat.ofHom (e.subtype hAB)) (fun x hx => (hAB x).mp hx) hw n b z
  rw [hz] at h
  exact h


/-! ## The local degree at the collapse class -/

/-- **The local degree of the collapse class, in the world `(ν, ν∖0)`.**  (statement as in the
docstring of the module). -/
theorem exists_localDegree_at_collapseRelK8 {V : Work.ThomBordism.Man8} [PathConnectedSpace V.pt]
    [ConnectedSpace V.pt] {k : ℕ} {E : EmbeddingData V (8 + k)} (hk : 1 ≤ k)
    {ι : Type} (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (ψ : Z.TotalSpace ≃ₜ NormalTotal E)
    (hproj : ∀ p : Z.TotalSpace, NormalTotal.proj (ψ p) = p.1)
    (hlen : ∀ p : Z.TotalSpace, Work.Thom.fibreNorm Z p ≠ 0 ↔ normalNorm E (ψ p) ≠ 0)
    (hvec : ∀ x : V.pt, NormalTotal.vec (ψ (Work.Thom.zeroSection Z x)) = 0)
    (hZ : Nonempty (Work.Thom.ThomClass Z k))
    {ε : ℝ} {C : TubeChart E ε} (q : NormalSphSub E ε) (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y) = OnePoint.some (normalBlowUp E ε (C.inv y))) :
    ∃ U : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E),
      ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal E)),
        relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k x U))
          (collapseRelK8 C g hg hR hbox)
        = kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom x) V.c := by
  classical
  obtain ⟨UZ₀, c₀, s, hs, hUZ₀, hc₀, hpair⟩ :=
    Work.ThomBordism.tubeLocalDegreeGlobalSign (V := V) (k := k) (hk := hk) Z hZ
  have hmemZ : ∀ p : Z.TotalSpace, p ∈ Work.Thom.zeroComplement Z
      ↔ Work.Thom.fibreNorm Z p ≠ 0 := by
    intro p
    rw [Work.Thom.zeroComplement, Set.mem_setOf_eq, Work.Thom.fibreNorm]
    exact norm_ne_zero_iff.symm
  have hAB : ∀ x : NormalTotal E, x ∈ normalNonzero E
      ↔ ψ.symm x ∈ Work.Thom.zeroComplement Z := by
    intro x
    rw [mem_normalNonzero, hmemZ, hlen, ψ.apply_symm_apply]
  have hw : CategoryTheory.CategoryStruct.comp
      (subtypeIncl (TopCat.of (NormalTotal E)) (normalNonzero E)) (TopCat.ofHom (ψ.symm))
      = CategoryTheory.CategoryStruct.comp (TopCat.ofHom ((ψ.symm).subtype hAB))
        (subtypeIncl (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)) := by
    apply TopCat.ext
    intro a
    rfl
  set cZ : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8) :=
    (HomologicalComplex.homologyMap (relChainsMapOf (TopCat.of (NormalTotal E))
      (TopCat.of Z.TotalSpace) (normalNonzero E) (Work.Thom.zeroComplement Z)
      (TopCat.ofHom (ψ.symm)) (TopCat.ofHom ((ψ.symm).subtype hAB)) hw) (k + 8)).hom
      (collapseRelK8 C g hg hR hbox) with hcZ
  haveI hiso := isIso_relChainsMapOf_homeoSub (X := TopCat.of (NormalTotal E))
    (Y := TopCat.of Z.TotalSpace) (ψ.symm) hAB hw (k + 8)
  have hcZgen : Submodule.span ℤ ({cZ} : Set _) = ⊤ := by
    rw [hcZ]
    exact span_singleton_map_eq_top
      (f := ((HomologicalComplex.homologyMap (relChainsMapOf (TopCat.of (NormalTotal E))
        (TopCat.of Z.TotalSpace) (normalNonzero E) (Work.Thom.zeroComplement Z)
        (TopCat.ofHom (ψ.symm)) (TopCat.ofHom ((ψ.symm).subtype hAB)) hw) (k + 8)).hom))
      (x := collapseRelK8 C g hg hR hbox)
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      (collapseRelK8_span_top C q hU hR hbox g hg hg2)
  obtain ⟨eT⟩ := Work.ThomBordism.thomPairTopHomologyIsoV2 (hk := hk) Z hZ
  have hcases : cZ = c₀ ∨ cZ = -c₀ :=
    Work.ThomBordism.eq_pm_of_span_eq_top_of_iso eT.toLinearEquiv hcZgen hc₀
  set UZ : Work.Thom.OpenThom Z k :=
    (if s = 1 then (if cZ = c₀ then UZ₀ else -UZ₀) else (if cZ = c₀ then -UZ₀ else UZ₀))
    with hUZdef
  have hf1 : ∀ x ∈ normalNonzero E,
      (ψ.symm : C(NormalTotal E, Z.TotalSpace)) x ∈ Work.Thom.zeroComplement Z :=
    fun x hx => (hAB x).mp hx
  have hg1 : ∀ y ∈ Work.Thom.zeroComplement Z,
      (ψ : C(Z.TotalSpace, NormalTotal E)) y ∈ normalNonzero E :=
    fun y hy => (hAB (ψ y)).mpr (by simpa using hy)
  set U : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E) :=
    (Work.Thom.relCohMap (ψ.symm) (normalNonzero E) (Work.Thom.zeroComplement Z) hf1 ℤ k).hom UZ
    with hUdef
  refine ⟨U, ?_⟩
  · intro x
    set xZ : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace) :=
      (Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8).hom x with hxZ
    have hcomp1 : Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
          Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8
        = 𝟙 (Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal E))) := by
      have hcomp : (ψ : C(Z.TotalSpace, NormalTotal E)).comp
            (ψ.symm : C(NormalTotal E, Z.TotalSpace)) = ContinuousMap.id (NormalTotal E) := by
        apply ContinuousMap.ext
        intro y
        exact ψ.apply_symm_apply y
      rw [← Work.Thom.CohMap_comp (ψ.symm : C(NormalTotal E, Z.TotalSpace))
        (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8, hcomp, Work.Thom.CohMap_id]
    have hcx : (Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8).hom xZ = x := by
      rw [hxZ]
      have h2 : (Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8).hom
            ((Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8).hom x)
          = (Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
              Work.Thom.CohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) ℤ 8).hom x := by
        rw [ModuleCat.hom_comp]
        rfl
      rw [h2, hcomp1]
      rfl
    have hcomp2 : Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
          Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8
        = Work.Thom.CohMap ((ψ : C(Z.TotalSpace, NormalTotal E)).comp
            (Work.Thom.zeroSection Z)) ℤ 8 := by
      rw [Work.Thom.CohMap_comp (Work.Thom.zeroSection Z)
        (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8]
    have hzz : (Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom xZ
        = (Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom x := by
      have h2 : (Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom
            ((Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8).hom x)
          = (Work.Thom.CohMap (ψ : C(Z.TotalSpace, NormalTotal E)) ℤ 8 ≫
              Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom x := by
        rw [ModuleCat.hom_comp]
        rfl
      rw [hxZ, h2, hcomp2, comp_zeroSection_eq_zeroSectionNormal Z ψ hproj hvec]
    have hZs : relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (k + 8)
        ((Nat.add_comm 8 k) ▸ mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          8 k xZ UZ) cZ
        = kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom xZ) V.c := by
      have base := hpair xZ
      rw [hUZdef]
      by_cases hs1 : s = 1
      · rw [if_pos hs1]
        by_cases hc : cZ = c₀
        · rw [if_pos hc, hc, base, hs1]
          ring
        · rw [if_neg hc]
          rcases hcases with hcZ | hcZ
          · exact absurd hcZ hc
          · rw [hcZ, mixedCup_neg_right, cast_neg_rel, relKronH_neg_left, relKronH_neg_right,
            base, hs1]
            ring
      · have hs' : s = -1 := by
          rcases hs with h | h
          · exact absurd h hs1
          · exact h
        rw [if_neg hs1]
        by_cases hc : cZ = c₀
        · rw [if_pos hc, hc, mixedCup_neg_right, cast_neg_rel, relKronH_neg_left, base, hs']
          ring
        · rw [if_neg hc]
          rcases hcases with hcZ | hcZ
          · exact absurd hcZ hc
          · rw [hcZ, relKronH_neg_right, base, hs']
            ring
    have hpu : (Work.Thom.relCohMap (ψ.symm) (normalNonzero E) (Work.Thom.zeroComplement Z)
          (fun x hx => (hAB x).mp hx) ℤ (k + 8)).hom
        ((Nat.add_comm 8 k) ▸ mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          8 k xZ UZ)
        = (Nat.add_comm 8 k) ▸ mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k x U := by
      rw [relCohMap_cast (A := normalNonzero E) (B := Work.Thom.zeroComplement Z)
        (ψ.symm) hf1 (Nat.add_comm 8 k)]
      simp only [mixedCup_topCatOf_eq_mixedCupC]
      rw [Work.Thom.mixedCupC_pairNatural (ψ.symm) (normalNonzero E)
        (Work.Thom.zeroComplement Z) hf1 8 k xZ UZ]
      rw [hcx, hUdef]
    have hK := relKronH_homeoPair (X := TopCat.of (NormalTotal E))
      (Y := TopCat.of Z.TotalSpace) (ψ.symm) hAB hw (k + 8)
      ((Nat.add_comm 8 k) ▸ mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        8 k xZ UZ)
      (collapseRelK8 C g hg hR hbox) cZ rfl
    rw [hpu, hZs, hzz] at hK
    exact hK

end

end Work.Tubular
