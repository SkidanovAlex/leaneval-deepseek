import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.StemsB.PairDeltaNaturalR
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.Basic
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.cohMapIsoOfRatHomologyIso
import Submission.Work.Serre.DiscPair.ratH_of_contractible_base

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibrewise restriction of the relative class: the weakly contractible base

Let `q : C(X,B)` be a Serre fibration over a weakly contractible base `B` (path connected with all
homotopy groups trivial), with path connected fibre `F = q⁻¹{b₀}` whose rational homology is
concentrated in degree `r` (`H_t(F;ℚ) = 0` for `0 < t ≤ N`, `t ≠ r`, and `H_r(F;ℚ) ≅ ℚ`).

`fibreRestrictionContractible` says that in degree `r+1` the restriction of the relative cohomology
of the mapping-cylinder pair along the inclusion of the fibre pair over `b₀` is an isomorphism.  The
proof is the naturality of the connecting map of a pair (`Work.StemsB.pairDeltaNaturalR`) applied to
the ladder of pairs `(π⁻¹{b₀}, F) → (cyl q, range (cylIncl q))`:

```
H^r(range cylIncl)  --δ_A-->  H^{r+1}(cyl q, range cylIncl)
      | β                                | ρ
      v                                  v
H^r(F)              --δ_F-->  H^{r+1}(π⁻¹{b₀}, F)
```

Both `δ`'s are isomorphisms (the cylinder is rationally acyclic — it is homotopy equivalent to the
weakly contractible base `B` — and the fibre of the retraction is contractible, being the cone on
`q⁻¹{b₀}`).  `β` is an isomorphism because `range (cylIncl q) ≅ X` and `F ≅ q⁻¹{b₀}` by explicit
homeomorphisms (`cylHomeoExplicit` and the map `x ↦ (cylIncl q x, ·)`), and because the inclusion of
the fibre is a rational homology isomorphism in degree `r` (`fibreInclRatHomologyIso` below, proved
from Serre's `E₀` in range form, the Serre pair comparison and the pair sequence).
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## The inclusion of the fibre is a rational homology isomorphism in degree `r`

This is the `X`-side counterpart of `Work.Serre.DiscPair.ratH_of_contractible_base`: there the
statement is that `H_r(X;ℚ) ≅ ℚ`, here that the *specific* map induced by the inclusion of the
fibre, `H_r(q⁻¹{b₀};ℚ) → H_r(X;ℚ)`, is an isomorphism.  The proof uses the same three inputs (the
rational acyclicity of `B` below degree `N+1`, the Serre pair comparison, and
`nonempty_ratH_iso_of_isZero_rel`, which produces the isomorphism induced by the inclusion). -/

theorem fibreInclRatHomologyIso {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r) (hrN : r + 1 ≤ N)
    (hq : Work.StemsB.IsSerreFibration q) (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q b₀))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) r ≅ ModuleCat.of ℚ ℚ)) :
    CategoryTheory.IsIso (Work.Serre.ratHomologyMap (Work.StemsB.fibreIncl q b₀) r) := by
  classical
  -- (1) `B` is rationally acyclic in degrees `1, …, N+1`
  have hE0B : ∀ j : ℕ, 0 < j → j < N + 2 → IsZero (Work.Serre.ratH (TopCat.of B) j) :=
    Work.Serre.serreE0Range B b₀ (N + 1) (fun i _ => hBc i)
  -- (2) the relative rational homology of `(B, {b₀})` vanishes in degrees `1, …, N+1`
  have hBrel : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
      IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology k) :=
    fun k hk1 hkN => isZero_relChainsR_point_of_isZero_ratH B b₀ k (by omega)
      (hE0B k (by omega) (by omega))
  -- (3) the Serre pair comparison: `H_i(X, q⁻¹{b₀};ℚ) ≅ H_i(B, {b₀};ℚ)`
  have hcmp := (Work.Serre.ratSerrePairComparison q hq b₀ (N + 1) r (by omega) hr hX hB
    (fun i _ => hBc i) hpc (fun j hj hjr => hvan j hj (by omega) (by omega))).1
  have hXrel : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
      IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))).homology k) :=
    fun k hk1 hkN =>
      IsZero.of_iso (hBrel k hk1 hkN) (Classical.choice (hcmp k (by omega)))
  -- (4) the pair sequence of `(X, q⁻¹{b₀})`: the map induced by the inclusion of the fibre is
  -- both injective and surjective in degree `r`
  have hrel1 : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))).homology
      (r + 1)) := hXrel (r + 1) (by omega) (by omega)
  have hrel0 : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))).homology
      r) := hXrel r (by omega) (by omega)
  have hS1 := Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B)) r
  have hS2 := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B)) r
  haveI hmono : Mono (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))) r) :=
    hS1.mono_g_iff.mpr (IsZero.eq_zero_of_src hrel1 _)
  haveI hepi : Epi (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))) r) :=
    hS2.epi_f_iff.mpr (IsZero.eq_zero_of_tgt hrel0 _)
  have htarget : IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))) r) :=
    isIso_of_mono_of_epi _
  have hmap : HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))) r
      = Work.Serre.ratHomologyMap (Work.StemsB.fibreIncl q b₀) r := rfl
  rw [← hmap]
  exact htarget

/-! ## Auxiliary facts -/

/-- **`CohMap` of a homeomorphism is an isomorphism.** -/
theorem fibreRestrictionCohMapOfHomeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
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

/-- **The connecting map of a pair is an isomorphism when the two outer terms vanish.** -/
theorem fibreRestrictionPairDeltaIsIsoRat (X : TopCat) (A : Set X) (m : ℕ)
    (h1 : IsZero (Work.Cohomology.singularCohomology ℚ (m + 1) X))
    (h2 : IsZero (Work.Cohomology.singularCohomology ℚ m X)) :
    IsIso (Work.Cohomology.pairδ ℚ X A m) := by
  have hmono : Mono (Work.Cohomology.pairδ ℚ X A m) := by
    have hf : (ShortComplex.mk (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ X A) m)
        (Work.Cohomology.pairδ ℚ X A m) (Work.Cohomology.pair_comp_δ ℚ X A m)).f = 0 :=
      h2.eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hf).mp (Work.Cohomology.pair_exact₃ ℚ X A m)
  have hepi : Epi (Work.Cohomology.pairδ ℚ X A m) := by
    have hg : (ShortComplex.mk (Work.Cohomology.pairδ ℚ X A m)
        (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ X A) (m + 1))
        (Work.Cohomology.pairδ_comp ℚ X A m)).g = 0 := h1.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp (Work.Cohomology.pair_exact₁ ℚ X A m)
  exact isIso_of_mono_of_epi _

/-! ## The main theorem -/

theorem fibreRestrictionContractible {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r)
    (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q b₀))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) r ≅ ModuleCat.of ℚ ℚ))
    (hrN : r + 1 ≤ N) :
    CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' ({b₀} : Set B)), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b₀} : Set B)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)) := by
  classical
  -- ## Notation
  let A : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q)
  let M' : Type := ↥((Work.Serre.cylRetract q) ⁻¹' ({b₀} : Set B))
  let F : Set M' := {x | (x : Work.Serre.cyl q) ∈ A}
  let f : C(M', Work.Serre.cyl q) := ⟨Subtype.val, continuous_subtype_val⟩
  -- ## The outer terms of the two connecting maps vanish
  have hE0B : ∀ j : ℕ, 0 < j → j < N + 2 → IsZero (Work.Serre.ratH (TopCat.of B) j) :=
    Work.Serre.serreE0Range B b₀ (N + 1) (fun i _ => hBc i)
  have hCohB : ∀ j : ℕ, 0 < j → j ≤ N + 1 → IsZero (Work.Thom.Coh ℚ j B) :=
    fun j hj hjN => isZero_ratCoh_of_isZero_ratH (hE0B j hj (by omega))
  obtain ⟨E, _hE⟩ := Work.Serre.cylHomotopyEquivExplicit q
  haveI hEiso : ∀ j : ℕ, IsIso (Work.Serre.ratHomologyMap E.toFun j) :=
    fun j => Work.Serre.IsRatHomologyIso.of_homotopyEquiv E j
  have hCohM : ∀ j : ℕ, 0 < j → j ≤ N + 1 →
      IsZero (Work.Thom.Coh ℚ j (Work.Serre.cyl q)) := by
    intro j hj hjN
    haveI : IsIso (Work.Thom.CohMap E.toFun ℚ j) :=
      Work.Serre.cohMapIsoOfRatHomologyIso E.toFun j (hEiso j)
    exact IsZero.of_iso (hCohB j hj hjN) (asIso (Work.Thom.CohMap E.toFun ℚ j)).symm
  haveI hContrM' : ContractibleSpace M' :=
    Work.Serre.DiscPair.cylRetractPreimageContractible q b₀
  have hCohM' : ∀ j : ℕ, 0 < j → IsZero (Work.Thom.Coh ℚ j M') := by
    intro j hj
    exact isZero_ratCoh_of_isZero_ratH
      (Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of M') j hj)
  -- ## The connecting maps are isomorphisms
  haveI hδA : IsIso (Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) A r) :=
    fibreRestrictionPairDeltaIsIsoRat (TopCat.of (Work.Serre.cyl q)) A r
      (hCohM (r + 1) (by omega) (by omega)) (hCohM r (by omega) (by omega))
  haveI hδF : IsIso (Work.Cohomology.pairδ ℚ (TopCat.of M') F r) :=
    fibreRestrictionPairDeltaIsIsoRat (TopCat.of M') F r (hCohM' (r + 1) (by omega)) (hCohM' r (by omega))
  -- ## The pair `(π⁻¹{b₀}, F)` ≅ `(X, fibre q b₀)`
  obtain ⟨eB, heB⟩ := Work.Serre.cylHomeoExplicit q
  have hframe : ∀ z : ↥A, Work.Serre.cylIncl q (eB.symm z) = (z : Work.Serre.cyl q) := by
    intro z
    rw [← heB (eB.symm z)]
    exact congrArg Subtype.val (Homeomorph.apply_symm_apply eB z)
  have happ : ∀ p : X, Work.Serre.cylRetract q (Work.Serre.cylIncl q p) = q p :=
    fun p => DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) p
  have hmemΦ : ∀ x : Work.StemsB.fibre q b₀,
      Work.Serre.cylIncl q x.1 ∈ (Work.Serre.cylRetract q) ⁻¹' ({b₀} : Set B) := by
    intro x
    show Work.Serre.cylRetract q (Work.Serre.cylIncl q x.1) = b₀
    rw [happ x.1]
    exact x.2
  let Φ : Work.StemsB.fibre q b₀ → ↥F := fun x =>
    ⟨⟨Work.Serre.cylIncl q x.1, hmemΦ x⟩, ⟨x.1, rfl⟩⟩
  have hΦcont : Continuous Φ := by
    have h1 : Continuous (fun x : Work.StemsB.fibre q b₀ =>
        (⟨Work.Serre.cylIncl q x.1, hmemΦ x⟩ : M')) :=
      Continuous.subtype_mk ((Work.Serre.cylIncl q).continuous.comp continuous_subtype_val)
        hmemΦ
    exact Continuous.subtype_mk h1 (fun x => ⟨x.1, rfl⟩)
  have hmemΨ : ∀ y : ↥F, q (eB.symm ⟨(y : M'), y.2⟩) = b₀ := by
    intro y
    rw [← happ (eB.symm ⟨(y : M'), y.2⟩), hframe ⟨(y : M'), y.2⟩]
    exact y.1.2
  let Ψ : ↥F → Work.StemsB.fibre q b₀ := fun y =>
    ⟨eB.symm ⟨(y : M'), y.2⟩, hmemΨ y⟩
  have hΨcont : Continuous Ψ := by
    have hbase : Continuous (fun y : ↥F => ((y : M') : Work.Serre.cyl q)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have h1 : Continuous (fun y : ↥F => (⟨(y : M'), y.2⟩ : ↥A)) :=
      Continuous.subtype_mk hbase (fun y => y.2)
    have h2 : Continuous (fun y : ↥F => eB.symm ⟨(y : M'), y.2⟩) :=
      (eB.symm).continuous.comp h1
    exact Continuous.subtype_mk h2 hmemΨ
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    intro x
    refine Subtype.ext ?_
    show eB.symm ⟨(Φ x : M'), (Φ x).2⟩ = x.1
    have hz : (⟨(Φ x : M'), (Φ x).2⟩ : ↥A) = eB x.1 := by
      refine Subtype.ext ?_
      show Work.Serre.cylIncl q x.1 = (eB x.1 : Work.Serre.cyl q)
      rw [heB]
    rw [hz, Homeomorph.symm_apply_apply]
  have hΦΨ : ∀ y, Φ (Ψ y) = y := by
    intro y
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    show Work.Serre.cylIncl q (eB.symm ⟨(y : M'), y.2⟩) = ((y : M') : Work.Serre.cyl q)
    exact hframe ⟨(y : M'), y.2⟩
  let eF : Work.StemsB.fibre q b₀ ≃ₜ ↥F :=
    { toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ,
      continuous_toFun := hΦcont, continuous_invFun := hΨcont }
  -- ## The map of pairs of the fibre, and its two factorisations
  let gLT : C(↥F, ↥A) :=
    ⟨fun a => ⟨f ↑a, (fun x hx => hx) ↑a a.2⟩,
      Continuous.subtype_mk (f.continuous.comp continuous_subtype_val)
        (fun a => (fun x hx => hx) ↑a a.2)⟩
  let j' : C(↥F, X) := (eB.symm : C(↥A, X)).comp gLT
  have hcomp : j'.comp (eF : C(Work.StemsB.fibre q b₀, ↥F)) = Work.StemsB.fibreIncl q b₀ := by
    apply ContinuousMap.ext
    intro x
    show eB.symm (gLT (Φ x)) = (Work.StemsB.fibreIncl q b₀) x
    rw [Work.StemsB.fibreIncl_apply]
    have hz : gLT (Φ x) = eB x.1 := by
      refine Subtype.ext ?_
      show ((Φ x : M') : Work.Serre.cyl q) = (eB x.1 : Work.Serre.cyl q)
      rw [heB]
    rw [hz, Homeomorph.symm_apply_apply]
  have hcomp2 : gLT = (eB : C(X, ↥A)).comp j' := by
    apply ContinuousMap.ext
    intro a
    show gLT a = eB (eB.symm (gLT a))
    rw [Homeomorph.apply_symm_apply]
  haveI hβ : IsIso (Work.Thom.CohMap gLT ℚ r) := by
    haveI heF : IsIso (Work.Thom.CohMap (eF : C(Work.StemsB.fibre q b₀, ↥F)) ℚ r) :=
      fibreRestrictionCohMapOfHomeo eF r
    haveI hfib : IsIso (Work.Thom.CohMap (Work.StemsB.fibreIncl q b₀) ℚ r) :=
      Work.Serre.cohMapIsoOfRatHomologyIso (Work.StemsB.fibreIncl q b₀) r
        (fibreInclRatHomologyIso q b₀ r N hr hrN hq hB hBc hX hpc hvan hgen)
    have hsplit : Work.Thom.CohMap j' ℚ r ≫
        Work.Thom.CohMap (eF : C(Work.StemsB.fibre q b₀, ↥F)) ℚ r =
        Work.Thom.CohMap (Work.StemsB.fibreIncl q b₀) ℚ r := by
      rw [← Work.Thom.CohMap_comp, hcomp]
    haveI : IsIso (Work.Thom.CohMap j' ℚ r ≫
        Work.Thom.CohMap (eF : C(Work.StemsB.fibre q b₀, ↥F)) ℚ r) := by
      rw [hsplit]; exact hfib
    haveI hj' : IsIso (Work.Thom.CohMap j' ℚ r) :=
      IsIso.of_isIso_comp_right (Work.Thom.CohMap j' ℚ r)
        (Work.Thom.CohMap (eF : C(Work.StemsB.fibre q b₀, ↥F)) ℚ r)
    haveI heBiso : IsIso (Work.Thom.CohMap (eB : C(X, ↥A)) ℚ r) := fibreRestrictionCohMapOfHomeo eB r
    have hsplit2 : Work.Thom.CohMap (eB : C(X, ↥A)) ℚ r ≫ Work.Thom.CohMap j' ℚ r =
        Work.Thom.CohMap gLT ℚ r := by
      rw [← Work.Thom.CohMap_comp, hcomp2]
    rw [← hsplit2]
    infer_instance
  -- ## Naturality of the connecting map of a pair
  have hsq_pt : ∀ y : Work.Thom.Coh ℚ r ↥A,
      (Work.Thom.relCohMap f F A (fun x hx => hx) ℚ (r + 1)).hom
          ((Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) A r).hom y)
        = (Work.Cohomology.pairδ ℚ (TopCat.of M') F r).hom
          ((Work.Thom.CohMap gLT ℚ r).hom y) := by
    intro y
    have h := Work.StemsB.pairDeltaNaturalR ℚ f F A (fun x hx => hx) r y
    simpa only [gLT] using h
  -- ## Assembly: `ρ` is injective and surjective
  have hδAb : Function.Bijective
      (Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) A r).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hδA
  have hδFb : Function.Bijective (Work.Cohomology.pairδ ℚ (TopCat.of M') F r).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hδF
  have hβb : Function.Bijective (Work.Thom.CohMap gLT ℚ r).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hβ
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨x', hx'⟩ := hδAb.2 x
    obtain ⟨y', hy'⟩ := hδAb.2 y
    have e1 : (Work.Thom.relCohMap f F A (fun x hx => hx) ℚ (r + 1)).hom x
        = (Work.Cohomology.pairδ ℚ (TopCat.of M') F r).hom
          ((Work.Thom.CohMap gLT ℚ r).hom x') := by
      rw [← hx', hsq_pt x']
    have e2 : (Work.Thom.relCohMap f F A (fun x hx => hx) ℚ (r + 1)).hom y
        = (Work.Cohomology.pairδ ℚ (TopCat.of M') F r).hom
          ((Work.Thom.CohMap gLT ℚ r).hom y') := by
      rw [← hy', hsq_pt y']
    have e3 : (Work.Thom.CohMap gLT ℚ r).hom x' = (Work.Thom.CohMap gLT ℚ r).hom y' :=
      hδFb.1 (by rw [← e1, ← e2, hxy])
    rw [← hx', ← hy', hβb.1 e3]
  · intro w
    obtain ⟨y, hy⟩ := hδFb.2 w
    obtain ⟨z, hz⟩ := hβb.2 y
    exact ⟨(Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) A r).hom z,
      by rw [hsq_pt z, hz, hy]⟩

end

end Work.Serre.DiscPair
