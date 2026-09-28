import Mathlib
import Submission.Work.Serre.ThmCylSigma.Rel
import Submission.Work.Serre.ThmCylSigma.Main
import Submission.Work.StemsB.AToolsR
import Submission.Work.StemsB.MixedCupR

/-!
# The cup-map property of a `σ`-type

For a family of spaces `Y i`, subsets `A i ⊆ Y i`, maps `π i : Y i → B i` and relative classes
`U i ∈ H^n(Y i, A i; ℚ)` whose cup maps `x ↦ π i^*(x) ⌣ U i` are isomorphisms in a range, the
assembled class `Uσ ∈ H^n(Σ i, Y i, Σ i, A i; ℚ)` has the same property for the `σ`-map
`Σ i, π i`.

The mathematical content is that the singular cochain complex of a `σ`-type splits as the product
of the cochain complexes of the pieces (`Work.Serre.Sigma.restr` and `Work.Serre.Sigma.assemble`
are mutually inverse, commute with the differentials, and with the cup product, see
`Submission/Work/Serre/ThmCylSigma/Basic.lean`), so that both the absolute and the relative
cohomology of a `σ`-type are the products of those of the pieces.  This file makes that splitting
explicit at the level of cohomology classes:

* `Coh_sigma_eq_zero_of_restr_eq_zero` -- a class of the `σ`-type whose restrictions to all pieces
  vanish is zero;
* `exists_Coh_sigma_of_restr` -- conversely every family of classes on the pieces is the family of
  restrictions of a class of the `σ`-type;
* `exists_relClass_sigma` -- a family of relative classes is the family of restrictions of a single
  relative class of the `σ`-type;
* `exists_sigmaClass` -- the cup-map property transfers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Serre.Sigma

noncomputable section

variable {ι : Type} {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]

/-! ## The zero class -/

/-- **The cohomology class of the zero cochain is zero.** -/
theorem cohomologyClassOf_zero (X : SSet) (R : Type) [CommRing R] (n : ℕ)
    (h : Work.Cohomology.cochainDiff R X (0 : Work.Cohomology.Cochain R X n) = 0) :
    Work.Cohomology.cohomologyClassOf R X (0 : Work.Cohomology.Cochain R X n) h = 0 := by
  rw [Work.Cohomology.cohomologyClassOf]
  have hz : Work.Cohomology.cocycleOf R X (0 : Work.Cohomology.Cochain R X n) h = 0 := by
    apply Work.Cohomology.iCycles_injective R X n
    rw [Work.Cohomology.iCycles_cocycleOf]
    simp
  rw [hz]
  simp

/-! ## The assembly of the zero family -/

/-- **The assembly of the zero family of cochains is zero.** -/
theorem assemble_zero (R : Type) [CommRing R] (n : ℕ) :
    assemble R n (fun i => (0 : Work.Cohomology.Cochain R (Spiece ι Y i) n)) = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_assemble (ι := ι) (Y := Y)]
  simp only [Work.Cohomology.genEval, LinearMap.zero_apply]

/-- **The assembly of a family of vanishing cochains is zero.** -/
theorem assemble_eq_zero (R : Type) [CommRing R] (n : ℕ)
    (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) (hw : ∀ i, w i = 0) :
    assemble R n w = 0 := by
  rw [show w = (fun i => (0 : Work.Cohomology.Cochain R (Spiece ι Y i) n)) from funext hw,
    assemble_zero]

/-- **The relative assembly of a family of vanishing relative cochains is zero.** -/
theorem assembleRel_eq_zero (R : Type) [CommRing R] (A : ∀ i, Set (Y i)) (n : ℕ)
    (w : ∀ i, Work.Cohomology.relKern R (TopCat.of (Y i)) (A i) n) (hw : ∀ i, w i = 0) :
    assembleRel R A n w = 0 := by
  refine Subtype.ext ?_
  rw [assembleRel_coe, Submodule.coe_zero]
  exact assemble_eq_zero R n (fun i => (w i).1) (fun i => by rw [hw i]; rfl)

/-! ## The restriction of a class to a piece -/

/-- **The restriction of the class of a cocycle.**  The pullback of a cohomology class along the
inclusion of a piece is the class of the restricted cocycle. -/
theorem CohMap_pieceIncl_classOf (i : ι) (k : ℕ)
    (a : Work.Cohomology.Cochain ℚ (Ssig ι Y) k)
    (ha : Work.Cohomology.cochainDiff ℚ (Ssig ι Y) a = 0) :
    (Work.Thom.CohMap (pieceIncl (Y := Y) i).hom ℚ k).hom
        (Work.Cohomology.cohomologyClassOf ℚ (Ssig ι Y) a ha) =
      Work.Cohomology.cohomologyClassOf ℚ (Spiece ι Y i) (restr ℚ i k a)
        (by rw [cochainDiff_restr, ha, map_zero]) := by
  exact Work.Cohomology.singularCohomologyMap_classOf ℚ (X := TopCat.of (Y i))
    (Y := TopCat.of (Σ j, Y j)) (TopCat.ofHom (pieceIncl (Y := Y) i).hom) a ha

/-! ## Degree zero -/

/-- `K.homologyπ 0` is injective: there is no incoming differential in degree `0`. -/
theorem homologyπ_zero_injective (K : CochainComplex (ModuleCat ℚ) ℕ) (z : K.cycles 0)
    (h : K.homologyπ 0 z = 0) : z = 0 := by
  have hT : (ShortComplex.mk (K.toCycles ((ComplexShape.up ℕ).prev 0) 0) (K.homologyπ 0)
      (K.toCycles_comp_homologyπ ((ComplexShape.up ℕ).prev 0) 0)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      (K.homologyIsCokernel ((ComplexShape.up ℕ).prev 0) 0 rfl)
  obtain ⟨y, hy⟩ := (ShortComplex.exact_iff_of_hasForget
    (ShortComplex.mk (K.toCycles ((ComplexShape.up ℕ).prev 0) 0) (K.homologyπ 0)
      (K.toCycles_comp_homologyπ ((ComplexShape.up ℕ).prev 0) 0))).mp hT z (by simpa using h)
  have hy' : (ConcreteCategory.hom (K.toCycles ((ComplexShape.up ℕ).prev 0) 0)) y = z := by
    simpa using hy
  have hz : ((ConcreteCategory.hom (K.toCycles ((ComplexShape.up ℕ).prev 0) 0)) :
      K.X ((ComplexShape.up ℕ).prev 0) → K.cycles 0) = 0 := by
    rw [HomologicalComplex.toCycles_eq_zero K (by simp [ComplexShape.up_Rel])]
    rfl
  calc z = (ConcreteCategory.hom (K.toCycles ((ComplexShape.up ℕ).prev 0) 0)) y := hy'.symm
    _ = 0 := by rw [hz]; simp

/-- **A `0`-cocycle whose class vanishes is zero.** -/
theorem cochain_eq_zero_of_class_eq_zero_deg_zero (X : SSet) (β : Work.Cohomology.Cochain ℚ X 0)
    (hβ : Work.Cohomology.cochainDiff ℚ X β = 0)
    (h : Work.Cohomology.cohomologyClassOf ℚ X β hβ = 0) : β = 0 := by
  have hz : (Work.Cohomology.SSetCochainComplex ℚ X).homologyπ 0
      (Work.Cohomology.cocycleOf ℚ X β hβ) = 0 := h
  have h0 := homologyπ_zero_injective (Work.Cohomology.SSetCochainComplex ℚ X) _ hz
  rw [← Work.Cohomology.iCycles_cocycleOf ℚ X β hβ, h0, map_zero]

/-! ## Detection of absolute cohomology classes of a `σ`-type by the pieces -/

/-- **A cohomology class of a `σ`-type whose restrictions to all pieces vanish is zero.** -/
theorem Coh_sigma_eq_zero_of_restr_eq_zero (k : ℕ) (z : Work.Thom.Coh ℚ k (Σ i, Y i))
    (h : ∀ i, (Work.Thom.CohMap (pieceIncl (Y := Y) i).hom ℚ k).hom z = 0) : z = 0 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ (Ssig ι Y) k z
  have hcl : ∀ i, Work.Cohomology.cohomologyClassOf ℚ (Spiece ι Y i) (restr ℚ i k a)
      (by rw [cochainDiff_restr, ha, map_zero]) = 0 := by
    intro i
    have h2 : (Work.Thom.CohMap (pieceIncl (Y := Y) i).hom ℚ k).hom
        (Work.Cohomology.cohomologyClassOf ℚ (Ssig ι Y) a ha) = 0 := h i
    rwa [CohMap_pieceIncl_classOf (i := i) (k := k) a ha] at h2
  rcases k with _ | k'
  · -- degree zero: every restriction vanishes, hence the cochain is zero
    have hz : ∀ i, restr ℚ i 0 a = 0 := fun i =>
      cochain_eq_zero_of_class_eq_zero_deg_zero (Spiece ι Y i) (restr ℚ i 0 a) _ (hcl i)
    have ha0 : a = 0 := by
      rw [← assemble_restr (R := ℚ) (Y := Y) 0 a]
      exact assemble_eq_zero ℚ 0 (fun i => restr ℚ i 0 a) hz
    have h00 : Work.Cohomology.cochainDiff ℚ (Ssig ι Y)
        (0 : Work.Cohomology.Cochain ℚ (Ssig ι Y) 0) = 0 := by
      simp [Work.Cohomology.cochainDiff]
    exact (Work.Cohomology.cohomologyClassOf_congr ℚ (Ssig ι Y) ha0 ha h00).trans
      (cohomologyClassOf_zero (Ssig ι Y) ℚ 0 h00)
  · -- positive degree: every restriction is a coboundary, hence so is the cochain
    have hex : ∀ i, ∃ w : Work.Cohomology.Cochain ℚ (Spiece ι Y i) k',
        Work.Cohomology.cochainDiff ℚ (Spiece ι Y i) w = restr ℚ i (k' + 1) a := fun i =>
      exists_cochainDiff_of_cohomologyClassOf_eq_zero (Spiece ι Y i)
        (restr ℚ i (k' + 1) a) _ (hcl i)
    choose w hw using hex
    have ha0 : a = Work.Cohomology.cochainDiff ℚ (Ssig ι Y) (assemble ℚ k' w) := by
      rw [← assemble_restr (R := ℚ) (Y := Y) (k' + 1) a]
      rw [show (fun i => restr ℚ i (k' + 1) a)
          = (fun i => Work.Cohomology.cochainDiff ℚ (Spiece ι Y i) (w i)) from
        funext (fun i => (hw i).symm)]
      rw [← cochainDiff_assemble (ι := ι) (Y := Y) (R := ℚ) (n := k') w]
    exact (Work.Cohomology.cohomologyClassOf_congr ℚ (Ssig ι Y) ha0 ha _).trans
      (cohomologyClassOf_cochainDiff_eq_zero' (Ssig ι Y) (assemble ℚ k' w))

/-! ## Surjectivity of the restriction to the pieces -/

/-- **Every family of cohomology classes of the pieces comes from a class of the `σ`-type.** -/
theorem exists_Coh_sigma_of_restr (k : ℕ) (c : ∀ i, Work.Thom.Coh ℚ k (Y i)) :
    ∃ z : Work.Thom.Coh ℚ k (Σ i, Y i),
      ∀ i, (Work.Thom.CohMap (pieceIncl (Y := Y) i).hom ℚ k).hom z = c i := by
  classical
  choose a ha hcls using fun i => Work.Cohomology.exists_cohomologyClassOf ℚ (Spiece ι Y i) k (c i)
  have hcyc : Work.Cohomology.cochainDiff ℚ (Ssig ι Y) (assemble ℚ k a) = 0 := by
    rw [cochainDiff_assemble (ι := ι) (Y := Y) (R := ℚ) (n := k) a]
    exact assemble_eq_zero ℚ (k + 1) (fun i => Work.Cohomology.cochainDiff ℚ (Spiece ι Y i) (a i))
      (fun i => ha i)
  refine ⟨Work.Cohomology.cohomologyClassOf ℚ (Ssig ι Y) (assemble ℚ k a) hcyc, fun i => ?_⟩
  rw [CohMap_pieceIncl_classOf (i := i) (k := k) (assemble ℚ k a) hcyc]
  exact (Work.Cohomology.cohomologyClassOf_congr ℚ (Spiece ι Y i)
    (restr_assemble (R := ℚ) (Y := Y) k a i) _ _).trans (hcls i)

/-! ## A relative class with prescribed restrictions -/

/-- **Every family of relative classes of the pieces comes from a relative class of the
`σ`-type.** -/
theorem exists_relClass_sigma (A : ∀ i, Set (Y i)) (n : ℕ)
    (U : ∀ i, Work.Thom.RelCoh ℚ n (Y i) (A i)) :
    ∃ Uσ : Work.Thom.RelCoh ℚ n (Σ i, Y i) (sigmaSet A),
      ∀ i, (Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
        (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ n).hom Uσ = U i := by
  classical
  choose v hv hcls using fun i =>
    Work.Cohomology.exists_relClassOf ℚ (TopCat.of (Y i)) (A i) n (U i)
  have hcoc : Work.Cohomology.relDiffLM ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) n
      (assembleRel ℚ A n v) = 0 := by
    rw [relDiffLM_assembleRel (A := A) (n := n) (w := v)]
    refine assembleRel_eq_zero ℚ A (n + 1) (fun i =>
      Work.Cohomology.relDiffLM ℚ (TopCat.of (Y i)) (A i) n (v i)) ?_
    intro i
    exact hv i
  refine ⟨Work.Cohomology.relClassOf ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A)
    (assembleRel ℚ A n v) hcoc, fun i => ?_⟩
  exact (relClassOf_assembleRel_restr (A := A) n v hv hcoc i).trans (hcls i)

/-! ## The cup-map property of a `σ`-type -/

/-- **The `σ`-type cup map.**  If the cup maps of the pieces are isomorphisms in a range, so is
the cup map of the assembled class. -/
theorem exists_sigmaClass {B : ι → Type} [∀ i, TopologicalSpace (B i)]
    (A : ∀ i, Set (Y i)) (π : ∀ i, C(Y i, B i)) (r N : ℕ)
    (U : ∀ i, Work.Thom.RelCoh ℚ (r + 1) (Y i) (A i))
    (hU : ∀ i k, k + (r + 1) ≤ N → CategoryTheory.IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (A i) k (r + 1)).flip (U i)) ∘ₗ
        (Work.Thom.CohMap (π i) ℚ k).hom))) :
    ∃ Uσ : Work.Thom.RelCoh ℚ (r + 1) (Σ i, Y i) (sigmaSet A),
      ∀ k, k + (r + 1) ≤ N → CategoryTheory.IsIso (ModuleCat.ofHom
        (((Work.Thom.mixedCupC ℚ (sigmaSet A) k (r + 1)).flip Uσ) ∘ₗ
          (Work.Thom.CohMap (sigmaMap π) ℚ k).hom)) := by
  classical
  choose v hv hcls using fun i =>
    Work.Cohomology.exists_relClassOf ℚ (TopCat.of (Y i)) (A i) (r + 1) (U i)
  have hcoc : Work.Cohomology.relDiffLM ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) (r + 1)
      (assembleRel ℚ A (r + 1) v) = 0 := by
    rw [relDiffLM_assembleRel (A := A) (n := r + 1) (w := v)]
    refine assembleRel_eq_zero ℚ A (r + 2) (fun i =>
      Work.Cohomology.relDiffLM ℚ (TopCat.of (Y i)) (A i) (r + 1) (v i)) ?_
    intro i
    exact hv i
  set Uσ : Work.Thom.RelCoh ℚ (r + 1) (Σ i, Y i) (sigmaSet A) :=
    Work.Cohomology.relClassOf ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A)
      (assembleRel ℚ A (r + 1) v) hcoc with hUσdef
  have hrestr : ∀ i, (Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
      (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ (r + 1)).hom Uσ = U i := fun i =>
    (relClassOf_assembleRel_restr (A := A) (r + 1) v hv hcoc i).trans (hcls i)
  refine ⟨Uσ, fun k hk => ?_⟩
  -- the piecewise cup maps are bijective
  have hΦi : ∀ i, Function.Bijective (fun x : Work.Thom.Coh ℚ k (B i) =>
      (Work.Thom.mixedCupC ℚ (A i) k (r + 1)) ((Work.Thom.CohMap (π i) ℚ k).hom x) (U i)) :=
    fun i => (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp (hU i k hk)
  -- the cup map of the `σ`-type
  set Φσ : Work.Thom.Coh ℚ k (Σ i, B i) →ₗ[ℚ]
      Work.Thom.RelCoh ℚ (k + (r + 1)) (Σ i, Y i) (sigmaSet A) :=
    ((Work.Thom.mixedCupC ℚ (sigmaSet A) k (r + 1)).flip Uσ) ∘ₗ
      (Work.Thom.CohMap (sigmaMap π) ℚ k).hom with hΦσdef
  have hΦσ_apply : ∀ x : Work.Thom.Coh ℚ k (Σ i, B i), Φσ x =
      (Work.Thom.mixedCupC ℚ (sigmaSet A) k (r + 1))
        ((Work.Thom.CohMap (sigmaMap π) ℚ k).hom x) Uσ := fun x => by
    simp only [hΦσdef, LinearMap.comp_apply, LinearMap.flip_apply]
  -- the restriction of the `σ`-type cup map
  have hkey : ∀ (i : ι) (x : Work.Thom.Coh ℚ k (Σ i, B i)),
      (Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
        (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ ((k + r) + 1)).hom (Φσ x) =
      (Work.Thom.mixedCupC ℚ (A i) k (r + 1))
        ((Work.Thom.CohMap (π i) ℚ k).hom
          ((Work.Thom.CohMap (pieceIncl (Y := B) i).hom ℚ k).hom x)) (U i) := by
    intro i x
    have h := relCohMap_mixedCup_sigmaMap (A := A) (π := π) (n := r + 1) (k := k) Uσ x i
    rw [hrestr i] at h
    rw [hΦσ_apply x]
    exact h
  have hbij : Function.Bijective Φσ := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hzero : Φσ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hx0 : ∀ i, (Work.Thom.CohMap (pieceIncl (Y := B) i).hom ℚ k).hom (x - y) = 0 := by
        intro i
        have h1 := hkey i (x - y)
        rw [hzero, map_zero] at h1
        have hf0 : (Work.Thom.mixedCupC ℚ (A i) k (r + 1))
            ((Work.Thom.CohMap (π i) ℚ k).hom (0 : Work.Thom.Coh ℚ k (B i))) (U i) = 0 := by
          simp only [map_zero, LinearMap.zero_apply]
        exact (hΦi i).1 (h1.symm.trans hf0.symm)
      exact sub_eq_zero.mp (Coh_sigma_eq_zero_of_restr_eq_zero k (x - y) hx0)
    · intro y
      have hex : ∀ i, ∃ z : Work.Thom.Coh ℚ k (B i),
          (Work.Thom.mixedCupC ℚ (A i) k (r + 1)) ((Work.Thom.CohMap (π i) ℚ k).hom z) (U i) =
            (Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
              (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ (k + r + 1)).hom y :=
        fun i => (hΦi i).2 _
      choose z hz using hex
      obtain ⟨x, hx⟩ := exists_Coh_sigma_of_restr (Y := B) (k := k) z
      refine ⟨x, ?_⟩
      have hzero : Φσ x - y = 0 := by
        apply relZero_of_restr_zero (A := A) (m := k + r)
        intro i
        rw [map_sub, hkey i x, hx i, hz i, sub_self]
      exact sub_eq_zero.mp hzero
  -- convert the bijectivity into the isomorphism statement
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ?_
  simpa only [ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.flip_apply,
    hΦσdef] using hbij

end

end Work.Serre.Sigma
