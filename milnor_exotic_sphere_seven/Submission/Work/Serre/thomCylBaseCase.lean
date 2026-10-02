import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.Defs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Thom.Cohomology
import Submission.Work.StemsB.ThomRatShim
-- (The declarations this file needs (`Work.Serre.EulerFibreRange`,
-- `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`, `isZero_coh_of_ratAcyclic`, …) were moved
-- to the upstream module `Submission.Work.Serre.EulerFibreRoot`; importing *that* instead of
-- `Submission.Work.Serre.thomIsoCylFibreRange` removes the import edge that made the target of
-- `thomIsoCylFibreRange.lean` unprovable (build cycle).  See
-- `Submission/Work/Serre/TICFR_SESSION_NOTES.md`, FINDING 1.)
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Serre.Basic
import Submission.Work.Cohomology.exists_smul_oneH
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.StemsB.Rat.collarSuspClassAuxRat
import Submission.Work.Serre.exists_ratCup_iso_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

/-!
# The base case of the Thom isomorphism for a rational spherical fibration

This proves `Work.Serre.thomCylBaseCase`: for the mapping cylinder pair `(cyl q, range (cylIncl q))`
of a map `q : X → PUnit` to a point (`X` being the fibre of `q`, a rational homology `r`-sphere
through degree `N` in the sense of the hypotheses), there is a relative class
`U ∈ H^{r+1}(cyl q, range (cylIncl q); ℚ)` whose mixed cup product with the pullback along the
retraction `cylRetract q` is an isomorphism in the range.

The argument is the "suspension" computation: `δ_r : H^r(F;ℚ) ≅ H^{r+1}(cyl q, F;ℚ)` is the
connecting map of the pair `(cyl q, F)` and is an isomorphism because the mapping cylinder is
contracted onto the point `PUnit`, so its cohomology vanishes in positive degrees; the class `U` is
the image of a generator of `H^r(F;ℚ) ≅ ℚ`, and the cup map is an isomorphism in degree `0`
(non-zero linear map between one-dimensional `ℚ`-vector spaces) and between vanishing modules in
degrees `≥ 1`.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Elementary auxiliary lemmas -/

/-- For a map `q : X → PUnit` (a point), the fibre over the unique point is the source. -/
def tcbFibrePUnitHomeo {X : Type} [TopologicalSpace X] (q : C(X, PUnit)) :
    Work.StemsB.fibre q () ≃ₜ X where
  toFun x := x.1
  invFun x := ⟨x, Subsingleton.elim _ _⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by
    refine (continuous_induced_rng (f := (Subtype.val : Work.StemsB.fibre q () → X))).2 ?_
    show Continuous fun x : X => ((⟨x, Subsingleton.elim _ _⟩ : Work.StemsB.fibre q ()) : X)
    exact continuous_id

/-- For a map `q : X → PUnit`, the fibre over the point is the bottom copy of the source in the
mapping cylinder. -/
def tcbFibreRangeHomeo {X : Type} [TopologicalSpace X] (q : C(X, PUnit)) :
    Work.StemsB.fibre q () ≃ₜ ↥(Set.range (cylIncl q)) :=
  (tcbFibrePUnitHomeo q).trans (cylHomeo q).some

/-- The pullback along the retraction of the mapping cylinder is an isomorphism. -/
theorem tcbIsIso_cohMap_cylRetract {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) : IsIso (Work.Thom.CohMap (cylRetract p) ℚ n) := by
  have hleft : ((cylInr p).comp (cylRetract p)).Homotopic (ContinuousMap.id (cyl p)) :=
    ⟨cylMoveHomotopy p⟩
  have hcomp : (cylRetract p).comp (cylInr p) = ContinuousMap.id B :=
    ContinuousMap.ext fun x => rfl
  refine IsIso.mk ⟨Work.Thom.CohMap (cylInr p) ℚ n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp, hcomp]
    exact Work.Thom.CohMap_id (B := B) ℚ n
  · rw [← Work.Thom.CohMap_comp, Work.Thom.CohMap_homotopic hleft ℚ n]
    exact Work.Thom.CohMap_id (B := cyl p) ℚ n

/-- In a concrete category, an isomorphism applied to the inverse-image of a point recovers the
point. -/
theorem tcbModuleIso_hom_inv_apply {M N : ModuleCat ℚ} (e : M ≅ N) (y : ↥N) :
    e.hom.hom (e.inv.hom y) = y := by
  have h := congrArg (fun (φ : N ⟶ N) => φ.hom y) (Iso.inv_hom_id e)
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h


/-- The converse direction of `tcbModuleIso_hom_inv_apply`. -/
theorem tcbModuleIso_inv_hom_apply {M N : ModuleCat ℚ} (e : M ≅ N) (x : ↥M) :
    e.inv.hom (e.hom.hom x) = x := by
  have h := congrArg (fun (φ : M ⟶ M) => φ.hom x) (Iso.hom_inv_id e)
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h

/-- The pullback along a homeomorphism is an isomorphism. -/
theorem tcbIsIso_cohMap_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (n : ℕ) : IsIso (Work.Thom.CohMap (φ : C(X, Y)) ℚ n) := by
  refine IsIso.mk ⟨Work.Thom.CohMap (φ.symm : C(Y, X)) ℚ n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp]
    rw [show (φ : C(X, Y)).comp (φ.symm : C(Y, X)) = ContinuousMap.id Y from
      ContinuousMap.ext fun y => φ.apply_symm_apply y]
    exact Work.Thom.CohMap_id (B := Y) ℚ n
  · rw [← Work.Thom.CohMap_comp]
    rw [show (φ.symm : C(Y, X)).comp (φ : C(X, Y)) = ContinuousMap.id X from
      ContinuousMap.ext fun x => φ.symm_apply_apply x]
    exact Work.Thom.CohMap_id (B := X) ℚ n

/-- The connecting map `H^n(B;R) → H^{n+1}(X,B;R)` of a pair is bijective as soon as the absolute
cohomology of the ambient space vanishes in degrees `n` and `n+1`. -/
theorem tcbPairDelta_bijective {Y : Type} [TopologicalSpace Y] (B : Set Y) (n : ℕ)
    (h1 : Subsingleton ↥(Work.Thom.Coh ℚ n Y)) (h2 : Subsingleton ↥(Work.Thom.Coh ℚ (n + 1) Y)) :
    Function.Bijective (Work.StemsB.pairδCR ℚ B n).hom := by
  haveI := h1
  haveI := h2
  constructor
  · intro x y hxy
    have hker : LinearMap.ker (Work.StemsB.pairδCR ℚ B n).hom = ⊥ := by
      rw [Work.StemsB.pairKer₃R ℚ B n, LinearMap.range_eq_bot]
      exact LinearMap.ext fun z => by simp [Subsingleton.elim z 0]
    have hmem : x - y ∈ LinearMap.ker (Work.StemsB.pairδCR ℚ B n).hom := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [hker] at hmem
    exact sub_eq_zero.mp (by simpa using hmem)
  · intro y
    have hzero : (Work.Thom.relToAbs ℚ B (n + 1)).hom = 0 :=
      LinearMap.ext fun z => Subsingleton.elim _ _
    have hrange : LinearMap.range (Work.StemsB.pairδCR ℚ B n).hom = ⊤ := by
      rw [Work.StemsB.pairKer₁R ℚ B n, hzero, LinearMap.ker_zero]
    exact LinearMap.mem_range.mp (by rw [hrange]; exact Submodule.mem_top)

/-- The inverse of a degree-transport isomorphism of relative cohomology is the corresponding cast
of elements. -/
theorem tcbRelCohEqToIso_inv_apply {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ}
    (h : a = b) (x : Work.Thom.RelCoh ℚ b X A) :
    ((eqToIso (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)).inv).hom x = h.symm ▸ x := by
  cases h
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- A linear map whose conjugate by isomorphisms to `ℚ` is zero is zero. -/
theorem tcbConj_eq_zero {M N : ModuleCat ℚ} (f : ↥M →ₗ[ℚ] ↥N)
    (u : M ≅ ModuleCat.of ℚ ℚ) (v : N ≅ ModuleCat.of ℚ ℚ)
    (h : (u.inv ≫ (ModuleCat.ofHom f ≫ v.hom)).hom = 0) : f = 0 := by
  have hgl : (u.inv ≫ (ModuleCat.ofHom f ≫ v.hom)).hom
      = v.hom.hom.comp (f.comp u.inv.hom) := by
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_assoc]
  rw [hgl] at h
  have hinj : Function.Injective v.hom.hom :=
    ((CategoryTheory.ConcreteCategory.isIso_iff_bijective v.hom).mp inferInstance).1
  apply LinearMap.ext
  intro x
  have h1 : v.hom.hom (f (u.inv.hom (u.hom.hom x))) = 0 := by
    have h2 := congrArg (fun (k : ℚ →ₗ[ℚ] ℚ) => k (u.hom.hom x)) h
    simpa [LinearMap.comp_apply] using h2
  rw [tcbModuleIso_inv_hom_apply u x] at h1
  exact hinj (by simpa using h1)

/-! ## The theorem -/

theorem thomCylBaseCase (r N : ℕ) (hr : 1 ≤ r) (X : Type) [TopologicalSpace X]
    (q : C(X, PUnit)) (hq : Work.StemsB.IsSerreFibration q)
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre q ()))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q ())) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q ())) r ≅ ModuleCat.of ℚ ℚ)) :
    ∃ U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)),
      ∀ m : ℕ, m + r + 1 ≤ N + 1 → CategoryTheory.IsIso (ModuleCat.ofHom
        (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) m (r + 1))).flip U ∘ₗ
          (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ m).hom)) := by
  classical
  set A : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q) with hA
  -- ### 1. The cohomology of the point and of the mapping cylinder
  have hPvan : ∀ n : ℕ, 0 < n → IsZero (Work.Thom.Coh ℚ n PUnit) := by
    intro n hn
    have h1 : IsZero (Work.Serre.ratH (TopCat.of PUnit) n) :=
      Work.Serre.RatAcyclic.isZero_ratH ratAcyclic_punit hn
    exact isZero_ratCoh_of_isZero_ratH h1
  have hMvan : ∀ n : ℕ, 0 < n → IsZero (Work.Thom.Coh ℚ n (Work.Serre.cyl q)) := by
    intro n hn
    haveI := isIso_cohMap_cylInr q n
    exact IsZero.of_iso (hPvan n hn) (asIso (Work.Thom.CohMap (Work.Serre.cylInr q) ℚ n))
  -- ### 2. The connecting map `δ_r` is bijective
  have hδ : Function.Bijective (Work.StemsB.pairδCR ℚ A r).hom :=
    tcbPairDelta_bijective A r
      (ModuleCat.isZero_iff_subsingleton.mp (hMvan r (by omega)))
      (ModuleCat.isZero_iff_subsingleton.mp (hMvan (r + 1) (by omega)))
  -- ### 3. A generator of `H^r` of the bottom copy of the source
  have hAr : Nonempty (Work.Thom.Coh ℚ r ↥A ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨eF⟩ := hgen
    haveI hII := tcbIsIso_cohMap_homeo ((tcbFibreRangeHomeo q).symm) r
    have h1 : Work.Thom.Coh ℚ r ↥A ≅ Work.Thom.Coh ℚ r (Work.StemsB.fibre q ()) :=
      (asIso (Work.Thom.CohMap ((tcbFibreRangeHomeo q).symm : C(↥A, Work.StemsB.fibre q ()))
        ℚ r)).symm
    exact ⟨h1 ≪≫ (Work.StemsB.ratDualUCT
        (Work.Serre.ratChains (TopCat.of (Work.StemsB.fibre q ()))) r).some
      ≪≫ ratCupAux_dualIsoRat eF⟩
  obtain ⟨eA⟩ := hAr
  set gen : Work.Thom.Coh ℚ r ↥A := (eA.inv).hom 1 with hgen_def
  have hgen_ne : gen ≠ 0 := by
    intro h0
    have hinj : Function.Injective (eA.inv).hom :=
      ((CategoryTheory.ConcreteCategory.isIso_iff_bijective eA.inv).mp inferInstance).1
    have h1 : (eA.inv).hom (1 : ℚ) = (eA.inv).hom 0 := by
      rw [hgen_def] at h0
      rw [h0, map_zero]
    exact one_ne_zero (hinj h1)
  -- ### 4. The class `U`
  set U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) A :=
    (Work.StemsB.pairδCR ℚ A r).hom gen with hU_def
  have hUne : U ≠ 0 := by
    intro h0
    rw [hU_def] at h0
    exact hgen_ne (hδ.1 (by rw [h0, map_zero]))
  -- ### 5. Isomorphisms identifying the two sides with `ℚ`
  obtain ⟨e1⟩ := Work.Cohomology.singularCohomology_zero ℚ (TopCat.of PUnit)
  have hδIso : IsIso (Work.StemsB.pairδCR ℚ A r) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr hδ
  let δIso : Work.Thom.Coh ℚ r ↥A ≅ Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) A :=
    asIso (Work.StemsB.pairδCR ℚ A r)
  let e2' : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) A ≅ ModuleCat.of ℚ ℚ :=
    δIso.symm ≪≫ eA
  let e0 : Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl q) A ≅
      Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) A :=
    eqToIso (congrArg (fun t => Work.Thom.RelCoh ℚ t (Work.Serre.cyl q) A) (Nat.zero_add (r + 1)))
  let e2 : Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl q) A ≅ ModuleCat.of ℚ ℚ :=
    e0 ≪≫ e2'
  -- ### 6. Assembly
  refine ⟨U, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- ## The case `m = 0`
    subst hm0
    set φ0 : Work.Thom.Coh ℚ 0 PUnit →ₗ[ℚ]
        Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl q) A :=
      ((Work.Thom.mixedCupC ℚ A 0 (r + 1))).flip U ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom with hφ0_def
    have hαiso : IsIso (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0) :=
      tcbIsIso_cohMap_cylRetract q 0
    let α : Work.Thom.Coh ℚ 0 PUnit ≅ Work.Thom.Coh ℚ 0 (Work.Serre.cyl q) :=
      asIso (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0)
    set u : Work.Thom.Coh ℚ 0 (Work.Serre.cyl q) :=
      Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl q))) with hu_def
    have hxu : (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom (α.inv.hom u) = u := by
      change α.hom.hom (α.inv.hom u) = u
      exact tcbModuleIso_hom_inv_apply α u
    have hunit : (Work.Thom.mixedCupC ℚ A 0 (r + 1)) u U = e0.inv.hom U := by
      rw [Work.StemsB.Rat.mixedCupC_oneH_zeroQ A (r + 1) U]
      exact (tcbRelCohEqToIso_inv_apply A (Nat.zero_add (r + 1)) U).symm
    have hU0ne : e0.inv.hom U ≠ 0 := by
      intro hcon
      have h2 : e0.hom.hom (e0.inv.hom U) = e0.hom.hom 0 :=
        congrArg (fun z => e0.hom.hom z) hcon
      rw [tcbModuleIso_hom_inv_apply e0 U, map_zero] at h2
      exact hUne h2
    have hφ0ne : φ0 ≠ 0 := by
      intro hzero
      have hx : φ0 (α.inv.hom u) = 0 := by
        have hx' := LinearMap.congr_fun hzero (α.inv.hom u)
        simpa using hx'
      have hval : φ0 (α.inv.hom u) = e0.inv.hom U := by
        show (Work.Thom.mixedCupC ℚ A 0 (r + 1))
            ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom (α.inv.hom u)) U
          = e0.inv.hom U
        rw [hxu, hunit]
      rw [hval] at hx
      exact hU0ne hx
    -- the conjugated endomorphism of `ℚ` is non-zero at `1`
    have hg1 : (e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom 1 ≠ 0 := by
      intro h1
      have hg0 : (e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom = 0 := by
        apply LinearMap.ext
        intro x
        have hx : (e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom x
            = x * ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom 1) := by
          simpa using map_smul ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom) x (1 : ℚ)
        rw [hx, h1, mul_zero]
        rfl
      apply hφ0ne
      exact tcbConj_eq_zero φ0 e1 e2 hg0
    have hGeq : e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)
        = ModuleCat.ofHom ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom) :=
      ModuleCat.hom_ext (by rw [ModuleCat.hom_ofHom])
    have hconjIso : IsIso (ModuleCat.ofHom ((e1.inv ≫ (ModuleCat.ofHom φ0 ≫ e2.hom)).hom)) :=
      ratCupAux_isIso_ofHom_rat_ne_zero _
        (ratCupAux_ratEnd_ne_zero_of_apply_one_ne_zero hg1)
    exact ratCupAux_isIso_of_iso_conj_rat (u := e1) (v := e2) (hGeq ▸ hconjIso)
  · -- ## The case `m ≥ 1`
    haveI hdom : Subsingleton ↥(Work.Thom.Coh ℚ m PUnit) :=
      ModuleCat.isZero_iff_subsingleton.mp (hPvan m hmpos)
    haveI hcod : Subsingleton ↥(Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl q) A) := by
      have hk : 0 < m + r := by omega
      have hkn : m + r ≠ r := by omega
      have hkle : m + r ≤ N := by omega
      have h1 : IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q ())) (m + r)) :=
        hvan (m + r) hk hkn hkle
      have h2 : IsZero (Work.Thom.Coh ℚ (m + r) (Work.StemsB.fibre q ())) :=
        isZero_ratCoh_of_isZero_ratH h1
      have h3 : IsZero (Work.Thom.Coh ℚ (m + r) ↥A) :=
        isZero_coh_of_homeo (tcbFibreRangeHomeo q) h2
      have hδk : Function.Bijective (Work.StemsB.pairδCR ℚ A (m + r)).hom :=
        tcbPairDelta_bijective A (m + r)
          (ModuleCat.isZero_iff_subsingleton.mp (hMvan (m + r) (by omega)))
          (ModuleCat.isZero_iff_subsingleton.mp (hMvan (m + r + 1) (by omega)))
      haveI : IsIso (Work.StemsB.pairδCR ℚ A (m + r)) :=
        (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr hδk
      have h4 : IsZero (Work.Thom.RelCoh ℚ (m + r + 1) (Work.Serre.cyl q) A) :=
        IsZero.of_iso h3 (asIso (Work.StemsB.pairδCR ℚ A (m + r))).symm
      have h5 : IsZero (Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl q) A) := by
        rw [← Nat.add_assoc m r 1]
        exact h4
      exact ModuleCat.isZero_iff_subsingleton.mp h5
    refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩

end

end Work.Serre
