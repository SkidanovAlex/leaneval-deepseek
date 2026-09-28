import Mathlib
import Submission.Work.Serre.GysinFibreRange
import Submission.Work.Serre.cylRelPi
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.StemsB.Periodicity
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.cupNaturalH

/-!
# The root of the TICFR / E3(b) development

This module holds the declarations that the *whole* TICFR/E3(b) node is built on and that used to
live in `Submission/Work/Serre/thomIsoCylFibreRange.lean`:

* the **definition** `Work.Serre.EulerFibreRange` (the absolute Euler-class form of the Gysin
  theorem, equivalent to `Work.Serre.ThomIsoCylFibreRange`);
* the reduction `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`;
* the elementary helpers `bijective_of_comp_left`, `isZero_dual_of_isZero`,
  `isZero_ratCoh_of_isZero_ratH`, `isZero_coh_of_ratAcyclic`, `isZero_coh_of_homeo`,
  `isIso_relToAbs_succ`, `isIso_cohMap_cylInr`, `cohMap_cylInr_cylRetract`.

They are here (and *not* in `thomIsoCylFibreRange.lean`) so that the downstream modules
`Submission.Work.Serre.thomCylBaseCase` and `Submission.Work.Serre.eulerFibreRange` can import
*this* module instead of `thomIsoCylFibreRange.lean`: those two modules import the latter only for
the declarations above, and that import is what makes it impossible for
`thomIsoCylFibreRange.lean` to import them back and close its target
(Lean reports a build cycle; see `Submission/Work/Serre/TICFR_SESSION_NOTES.md`, FINDING 1).

The names are unchanged (the namespace `Work.Serre` is the same), so every existing consumer keeps
working; the only change needed to *break the cycle* is, in those two modules, replacing
`import Submission.Work.Serre.thomIsoCylFibreRange` by
`import Submission.Work.Serre.EulerFibreRoot` (or by nothing, if the import of this module is
already transitive).

(This file is the `EulerFibreRoot` proposed in `TICFR_SESSION_NOTES.md`, FINDING 1, way out 2.)
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- **Cancellation of a bijective factor on the left.** -/
theorem bijective_of_comp_left {α β γ : Type*} {g : β → γ} {f : α → β}
    (hg : Function.Bijective g) (h : Function.Bijective (g ∘ f)) : Function.Bijective f :=
  ⟨fun x y hxy => h.1 (by simp [Function.comp, hxy]),
   fun z => by
     obtain ⟨y, hy⟩ := h.2 (g z)
     exact ⟨y, hg.1 (by simpa [Function.comp] using hy)⟩⟩


/-! ## The cohomology of a rationally acyclic subspace vanishes -/

/-- The `ℚ`-dual of a zero module is zero. -/
theorem isZero_dual_of_isZero {M : ModuleCat ℚ} (hM : IsZero M) :
    IsZero (ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun f g => LinearMap.ext fun x => by
      haveI : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp hM
      rw [Subsingleton.elim x 0]; simp⟩

/-- Vanishing of `ratH` implies vanishing of `ratCoh` (over the field `ℚ`), via the universal
coefficient theorem over a field (`Work.StemsB.ratDualUCT`). -/
theorem isZero_ratCoh_of_isZero_ratH {X : TopCat} {n : ℕ}
    (h : IsZero (ratH X n)) : IsZero (ratCoh X n) :=
  IsZero.of_iso (isZero_dual_of_isZero h) (Work.StemsB.ratDualUCT (ratChains X) n).some

/-- Vanishing of the rational cohomology of a rationally acyclic space in positive degrees. -/
theorem isZero_coh_of_ratAcyclic {E : Type} [TopologicalSpace E] (hE : RatAcyclic E) {n : ℕ}
    (hn : 0 < n) : IsZero (Work.Thom.Coh ℚ n E) :=
  isZero_ratCoh_of_isZero_ratH (Work.StemsB.isZero_ratH_of_ratAcyclic hE hn)

/-- **Vanishing of cohomology transports along a homeomorphism.** -/
theorem isZero_coh_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
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
theorem isIso_relToAbs_succ {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ) (hk : 1 ≤ k)
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

/-! ## The homotopy equivalence `cyl p ≃ B` -/

/-- **The pullback along `cylInr` is an isomorphism**: `cylRetract` and `cylInr` are homotopy
inverse (`Work.Serre.cylHomotopyEquiv`). -/
theorem isIso_cohMap_cylInr {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
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
theorem cohMap_cylInr_cylRetract {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
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

/-! ## The Euler-class (absolute) form of the statement -/

/-- **The Euler-class form of the Gysin theorem in the range given by the fibre.**  For a Serre
fibration `p : E → B` with rationally acyclic total space, simply connected base and strict fibre a
rational `r`-sphere through degree `N`, there is `e ∈ H^{r+1}(B;ℚ)` whose cup product
`⌣ e : H^m(B;ℚ) → H^{m+r+1}(B;ℚ)` is an isomorphism for `m + r + 1 ≤ N + 1`.

This is the content of `Work.Serre.SerreE3b` / `Work.Stems.Engine.GysinRangeFree`; the target
`ThomIsoCylFibreRange` is *equivalent* to it, see
`Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange` (this direction) and
`Work.Serre.serreE3b_of_thomCyl` (`Submission/Work/Serre/serreE3b.lean`, the converse). -/
def EulerFibreRange : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (r N : ℕ),
    1 ≤ r → Work.StemsB.IsSerreFibration p → SimplyConnectedSpace B → RatAcyclic E →
      PathConnectedSpace (Work.StemsB.fibre p b₀) →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) t)) →
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∃ e : Work.Thom.Coh ℚ (r + 1) B,
        ∀ m : ℕ, m + r + 1 ≤ N + 1 →
          IsIso (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e m))

/-! ## The reduction -/

/-- **The global Thom class statement follows from the Euler-class form of the Gysin theorem.**
The relative Thom class `U` is chosen so that `(cylInr p)^*(relToAbs U) = e`, and the compatibility
of the mixed cup product with `relToAbs` (`Work.StemsB.mixedCup_relToAbs_R`), together with the
naturality `Work.Cohomology.cupNaturalH` and the retraction identity
`(cylInr p)^* ∘ (cylRetract p)^* = id`, identifies the target's map with
`(cylInr p)^* ∘ relToAbs ∘ (⊔ U) = (⊔ e)`.  Since the two outer maps are isomorphisms
(`isIso_cohMap_cylInr`, `isIso_relToAbs_succ`), the target follows. -/
theorem thomIsoCylFibreRange_of_eulerFibreRange (h : EulerFibreRange) :
    Work.Serre.ThomIsoCylFibreRange := by
  intro E B _ _ p b₀ r N hr hp hB hE hfib0 hfib hgen
  -- the bottom copy of the source is rationally acyclic, hence its cohomology vanishes
  have hA : ∀ k : ℕ, 0 < k → IsZero (Work.Thom.Coh ℚ k ↥(Set.range (cylIncl p))) := by
    intro k hk
    obtain ⟨φ⟩ := cylHomeo p
    exact isZero_coh_of_homeo φ (isZero_coh_of_ratAcyclic hE hk)
  -- hence the forgetful map is an isomorphism in the relevant degrees
  have hrelIso : IsIso (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)) :=
    isIso_relToAbs_succ (Set.range (cylIncl p)) r hr
      (hA r (by omega)) (hA (r + 1) (by omega))
  obtain ⟨e, he⟩ := h E B p b₀ r N hr hp hB hE hfib0 hfib hgen
  -- a copy of `e` typed in the cohomology of the simplicial model, for the rewrites below
  set e' : ratCoh (TopCat.of B) (r + 1) := e with he'
  -- the class `U`
  have hbijRel : Function.Bijective (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1))).mp hrelIso
  have hbijInr : Function.Bijective (Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.CohMap (cylInr p) ℚ (r + 1))).mp (isIso_cohMap_cylInr p (r + 1))
  have hbijComp : Function.Bijective
      (fun z : Work.Thom.RelCoh ℚ (r + 1) (cyl p) (Set.range (cylIncl p)) =>
        (Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom z)) := hbijInr.comp hbijRel
  obtain ⟨U, hU⟩ := hbijComp.2 e'
  have hedef : e' = (Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U) := hU.symm
  refine ⟨U, fun m hm => ?_⟩
  set φ : Work.Thom.Coh ℚ m B →ₗ[ℚ] Work.Thom.RelCoh ℚ (m + (r + 1)) (cyl p) (Set.range (cylIncl p)) :=
    (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom with hφ
  change IsIso (ModuleCat.ofHom φ)
  -- the key identity: `(cylInr p)^* ∘ relToAbs ∘ φ = (⊔ e')`
  have hkey : (cupWith (TopCat.of B) (r + 1) e' m) =
      ((Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom).comp
        (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom).comp φ) := by
    ext x
    show Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of B)) m (r + 1) x e' =
      (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom
          (φ x))
    rw [hφ]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [Work.StemsB.mixedCup_relToAbs_R ℚ (Set.range (cylIncl p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x) U]
    rw [Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (cylInr p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x)
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)]
    rw [cohMap_cylInr_cylRetract p m x, ← hedef]
  -- it follows that `φ` is bijective
  have hbijCup : Function.Bijective (cupWith (TopCat.of B) (r + 1) e' m) := by
    rw [he']
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e m))).mp (he m hm)
  have hbijComp2 : Function.Bijective
      (((Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom).comp
        (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom).comp φ)) := by
    rw [← hkey]; exact hbijCup
  have hbijInr2 : Function.Bijective (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1)))).mp (isIso_cohMap_cylInr p (m + (r + 1)))
  have hbijMid : Function.Bijective
      (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom).comp φ) :=
    bijective_of_comp_left hbijInr2 hbijComp2
  have hbijRel2 : Function.Bijective (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1)))).mp
        (isIso_relToAbs_succ (Set.range (cylIncl p)) (m + r) (by omega)
          (hA (m + r) (by omega)) (hA (m + r + 1) (by omega)))
  have hbijf : Function.Bijective φ := bijective_of_comp_left hbijRel2 hbijMid
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom φ)).mpr hbijf


end

end Work.Serre
