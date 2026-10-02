import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.GysinFibreRange
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.StemsB.Periodicity
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.pathConnectedSpace_of_ratAcyclic
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.strictFibre_ratH_homotopyFibre
import Submission.Work.Serre.cylRelPi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The `ℚ`-dual of a zero module is zero. -/
theorem e3bR_isZero_dual_of_isZero {M : ModuleCat ℚ} (hM : IsZero M) :
    IsZero (ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun f g => LinearMap.ext fun x => by
      haveI : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp hM
      rw [Subsingleton.elim x 0]; simp⟩

/-- Vanishing of `ratH` implies vanishing of `ratCoh` (over the field `ℚ`), via the universal
coefficient theorem over a field (`Work.StemsB.ratDualUCT`). -/
theorem e3bR_isZero_ratCoh_of_isZero_ratH {X : TopCat} {n : ℕ}
    (h : IsZero (ratH X n)) : IsZero (ratCoh X n) :=
  IsZero.of_iso (e3bR_isZero_dual_of_isZero h) (Work.StemsB.ratDualUCT (ratChains X) n).some

/-- Vanishing of the rational cohomology of a rationally acyclic space in positive degrees. -/
theorem e3bR_isZero_coh_of_ratAcyclic {E : Type} [TopologicalSpace E] (hE : RatAcyclic E) {n : ℕ}
    (hn : 0 < n) : IsZero (Work.Thom.Coh ℚ n E) :=
  e3bR_isZero_ratCoh_of_isZero_ratH (Work.StemsB.isZero_ratH_of_ratAcyclic hE hn)

/-- **Vanishing of cohomology transports along a homeomorphism.** -/
theorem e3bR_isZero_coh_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) {n : ℕ} (h : IsZero (Work.Thom.Coh ℚ n X)) :
    IsZero (Work.Thom.Coh ℚ n Y) := by
  haveI : IsIso (Work.Thom.CohMap (φ : C(X, Y)) ℚ n) := by
    refine IsIso.mk ⟨Work.Thom.CohMap (φ.symm : C(Y, X)) ℚ n, ?_, ?_⟩
    · rw [← Work.Thom.CohMap_comp]
      rw [show (φ : C(X, Y)).comp (φ.symm : C(Y, X)) = ContinuousMap.id Y from
        ContinuousMap.ext fun y => φ.apply_symm_apply y]
      exact Work.Thom.CohMap_id (B := Y) ℚ n
    · rw [← Work.Thom.CohMap_comp]
      rw [show (φ.symm : C(Y, X)).comp (φ : C(X, Y)) = ContinuousMap.id X from
        ContinuousMap.ext fun x => φ.symm_apply_apply x]
      exact Work.Thom.CohMap_id (B := X) ℚ n
  exact IsZero.of_iso h (asIso (Work.Thom.CohMap (φ : C(X, Y)) ℚ n))

/-- **The forgetful map `H^{k+1}(X,A;ℚ) → H^{k+1}(X;ℚ)` is an isomorphism** when the cohomology of
the subspace vanishes in degrees `k` and `k+1` (with `k ≥ 1`): the long exact sequence of the pair
squeezes it, the connecting map having zero source and the restriction having zero target. -/
theorem e3bR_isIso_relToAbs_succ {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ) (hk : 1 ≤ k)
    (h1 : IsZero (Work.Thom.Coh ℚ k A)) (h2 : IsZero (Work.Thom.Coh ℚ (k + 1) A)) :
    IsIso (Work.Thom.relToAbs ℚ A (k + 1)) := by
  haveI : Subsingleton (Work.Thom.Coh ℚ k A) := ModuleCat.isZero_iff_subsingleton.mp h1
  haveI : Subsingleton (Work.Thom.Coh ℚ (k + 1) A) := ModuleCat.isZero_iff_subsingleton.mp h2
  have hker : LinearMap.ker (Work.Thom.relToAbs ℚ A (k + 1)).hom = ⊥ := by
    rw [← Work.StemsB.pairKer₁R ℚ A k]
    refine LinearMap.range_eq_bot.mpr (LinearMap.ext fun x => ?_)
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact map_zero _
  have hrng : LinearMap.range (Work.Thom.relToAbs ℚ A (k + 1)).hom = ⊤ := by
    rw [Work.StemsB.pairKer₂R ℚ A (k + 1)]
    exact LinearMap.ker_eq_top.mpr (LinearMap.ext fun x => Subsingleton.elim _ _)
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (Work.Thom.relToAbs ℚ A (k + 1))).mpr ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have hxy' : (Work.Thom.relToAbs ℚ A (k + 1)).hom x =
        (Work.Thom.relToAbs ℚ A (k + 1)).hom y := hxy
    have hmem : x - y ∈ LinearMap.ker (Work.Thom.relToAbs ℚ A (k + 1)).hom := by
      rw [LinearMap.mem_ker, map_sub, hxy', sub_self]
    rw [hker] at hmem
    exact sub_eq_zero.mp (by simpa using hmem)
  · have hmem : y ∈ LinearMap.range (Work.Thom.relToAbs ℚ A (k + 1)).hom := by
      rw [hrng]; exact Submodule.mem_top
    exact hmem

/-- **The pullback along `cylInr` is an isomorphism**: `cylRetract` and `cylInr` are homotopy
inverse (`Work.Serre.cylHomotopyEquiv`). -/
theorem e3bR_isIso_cohMap_cylInr {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) : IsIso (Work.Thom.CohMap (cylInr p) ℚ n) := by
  have hleft : ((cylInr p).comp (cylRetract p)).Homotopic (ContinuousMap.id (cyl p)) :=
    ⟨cylMoveHomotopy p⟩
  have hcomp : (cylRetract p).comp (cylInr p) = ContinuousMap.id B :=
    ContinuousMap.ext fun x => rfl
  refine IsIso.mk ⟨Work.Thom.CohMap (cylRetract p) ℚ n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp]
    rw [Work.Thom.CohMap_homotopic hleft ℚ n]
    exact Work.Thom.CohMap_id (B := cyl p) ℚ n
  · rw [← Work.Thom.CohMap_comp, hcomp]
    exact Work.Thom.CohMap_id (B := B) ℚ n

/-- The composite `cylInr^* ∘ cylRetract^*` is the identity on `H^*(B;ℚ)`. -/
theorem e3bR_cohMap_cylInr_cylRetract {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) (x : Work.Thom.Coh ℚ n B) :
    (Work.Thom.CohMap (cylInr p) ℚ n).hom ((Work.Thom.CohMap (cylRetract p) ℚ n).hom x) = x := by
  have hcomp : (cylRetract p).comp (cylInr p) = ContinuousMap.id B :=
    ContinuousMap.ext fun x => rfl
  have h : Work.Thom.CohMap (cylRetract p) ℚ n ≫ Work.Thom.CohMap (cylInr p) ℚ n =
      𝟙 (Work.Thom.Coh ℚ n B) := by
    rw [← Work.Thom.CohMap_comp, hcomp]
    exact Work.Thom.CohMap_id (B := B) ℚ n
  have hx := congrArg (fun (g : Work.Thom.Coh ℚ n B ⟶ Work.Thom.Coh ℚ n B) => g.hom x) h
  simpa using hx

/-- **E3(b) from the global Thom class**: the assembly.  See the module docstring of
`Submission/Work/Serre/GysinFibreRange.lean`: the class `e` is the absolute class induced by the
Thom class `U`, and `x ↦ x ⌣ e` is the composite of the Thom isomorphism with the two
isomorphisms `relToAbs` (degree `≥ 2`) and `cylInr^*`. -/
theorem e3bR_serreE3b_of_thomCyl (hT : ThomIsoCylFibreRange) : SerreE3b := by
  intro E B _ _ p e₀ r N hr hp hB hE hfib hgen m hm
  haveI : PathConnectedSpace B := inferInstance
  haveI hFund : Subsingleton (FundamentalGroup B (p e₀)) :=
    ⟨fun x y => Quotient.inductionOn₂ x y
      (fun u v => Quotient.sound (SimplyConnectedSpace.paths_homotopic u v))⟩
  have hsc : Subsingleton (HomotopyGroup (Fin 1) B (p e₀)) :=
    ⟨fun x y => (HomotopyGroup.pi1EquivFundamentalGroup (x := p e₀)).injective
      (Subsingleton.elim _ _)⟩
  have hEpc : PathConnectedSpace E := pathConnectedSpace_of_ratAcyclic hE
  haveI hpcFib : PathConnectedSpace (Work.StemsB.fibre p (p e₀)) :=
    pathConnectedSpace_fibre_of_isSerreFibration p hp (p e₀) hEpc inferInstance hsc
  have hbridge : ∀ j : ℕ, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p (p e₀))) j ≅
      ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) j) :=
    fun j => strictFibre_ratH_homotopyFibre p hp e₀ (p e₀) inferInstance j
  have hfibS : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p (p e₀))) t) :=
    fun t ht htr htN => IsZero.of_iso (hfib t ht htr htN) (hbridge t).some
  have hgenS : Nonempty (ratH (TopCat.of (Work.StemsB.fibre p (p e₀))) r ≅ ModuleCat.of ℚ ℚ) :=
    ⟨(hbridge r).some ≪≫ hgen.some⟩
  obtain ⟨U, hU⟩ := hT E B p (p e₀) r N hr hp hB hE hpcFib hfibS hgenS
  have hA : ∀ k : ℕ, 0 < k → IsZero (Work.Thom.Coh ℚ k ↥(Set.range (cylIncl p))) := by
    intro k hk
    obtain ⟨φ⟩ := cylHomeo p
    exact e3bR_isZero_coh_of_homeo φ (e3bR_isZero_coh_of_ratAcyclic hE hk)
  refine ⟨(Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U), ?_⟩
  have hrelIso : IsIso (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)) :=
    e3bR_isIso_relToAbs_succ (Set.range (cylIncl p)) (m + r) (by omega)
      (hA (m + r) (by omega)) (hA (m + r + 1) (by omega))
  have hcylIso : IsIso (Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)) := e3bR_isIso_cohMap_cylInr p _
  have hfIso : IsIso (ModuleCat.ofHom (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom))) := hU m hm
  have hfBij : Function.Bijective (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom)) := by
    simpa only [ModuleCat.hom_ofHom] using
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom)))).mp hfIso
  have hhBij : Function.Bijective ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom) := by
    simpa only [ModuleCat.hom_ofHom] using
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1))).mp hrelIso
  have hgBij : Function.Bijective ((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom) := by
    simpa only [ModuleCat.hom_ofHom] using
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (Work.Thom.CohMap (cylInr p) ℚ (m + r + 1))).mp hcylIso
  have hkey : (cupWith (TopCat.of B) (r + 1) ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) m) =
      ((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom).comp (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom).comp (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom))) := by
    ext x
    change Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of B)) m (r + 1) x
        ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) =
      (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom
          ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))
            ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x) U))
    rw [Work.StemsB.mixedCup_relToAbs_R ℚ (Set.range (cylIncl p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x) U]
    rw [Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (cylInr p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x)
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)]
    rw [e3bR_cohMap_cylInr_cylRetract p m x]
  rw [hkey]
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (ModuleCat.ofHom (((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom).comp (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom).comp (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom)))))).mpr ?_
  show Function.Bijective ⇑(((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom).comp (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom).comp (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom))))
  exact hgBij.comp (hhBij.comp hfBij)

end

end Work.Serre

