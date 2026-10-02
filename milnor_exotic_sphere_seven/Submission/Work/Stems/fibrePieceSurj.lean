import Mathlib
import Submission.Work.Serre.fibreNonvanishing
import Submission.Work.Serre.fibreExcisionIso
import Submission.Work.Serre.fibrePairMapSurj
import Submission.Work.Serre.ratPairComparisonBOneGeneral
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Cohomology.PairSequence
import Submission.Work.StemsB.RelCohMapPairHomotopyR
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.isIso_relCohMap_excision_of_interior
import Submission.Work.Serre.isZero_homology_relChainsR_cylCMid_of_pairComparison
import Submission.Work.Serre.homologyInjectiveOfRelCohSurjective
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.ratPairComparisonOneBoundary
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Stems.fibrePieceCollapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Surjectivity of the restriction `H^r(cyl q) → H^r(CMid q b)`

Target: `Work.Stems.fibrePieceSurj` (see the statement below).  This is "piece 1" of the Stems
assembly: for a Serre fibration `q : X → B` over a path connected base whose fibres have the
rational homology of `S^r` through degree `N` (`r ≤ N`), the restriction

  `H^r(cyl q; ℚ) ⟶ H^r(CMid q b; ℚ)`,

where `CMid q b = range (cylIncl q) ∪ (cylRetract q)⁻¹{b}` is the union of the bottom copy of `X`
with the cone on the fibre over `b`, is **surjective**.

## The route

`M = cyl q`, `A = range (cylIncl q)` (the bottom copy `≅ X`), `P = (cylRetract q)⁻¹{b}` (the cone
on the fibre `q⁻¹{b}`), `C = CMid q b = A ∪ P`.  The exact sequence of the pair `(M,C)` reads

  `H^r(M) ⟶ H^r(C) ⟶^{δ} H^{r+1}(M,C) ⟶ H^{r+1}(M)`,

so the restriction is onto as soon as the vanishing `H^{r+1}(M,C;ℚ) = 0` is known (then `δ = 0`).
The vanishing is proved from the *homological* statement `H_{r+1}(M,C;ℚ) = 0` (the perfect Kronecker
duality over the field `ℚ`, `Work.Serre.relKronMapRInjective`).  For the homology vanishing we use
the short exact sequence of the triple `P ⊆ C ⊆ M` (`Work.Serre.RatTower.tripleShortR_shortExact`)
together with the two comparison isomorphisms

* `Work.Serre.collapseMap q b`: `C_*(X, q⁻¹b;ℚ) → C_*(C, P;ℚ)` is a homology isomorphism (the cone
  `P` is attached to the bottom copy along the fibre), and
* `Work.Serre.retractMap q b`: `C_*(M, P;ℚ) → C_*(B, {b};ℚ)` is a homology isomorphism (the
  retraction is a homotopy equivalence of pairs, the push-up homotopy `cylMove` preserving `P`),

which identify the map `H_*(C,P) → H_*(M,P)` of the triple with the pair comparison
`Work.Serre.relPairMapRat q b`.  The latter is onto in degree `r+1`
(`Work.Serre.ratPairComparisonOneBoundary`) and invertible in degree `r`
(`Work.Serre.B1Rel.relPairMapRat_isIso`), which is exactly what the algebraic lemma
(`Work.Serre.isZero_homology_third_of_epi_isIso`) needs.
-/

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## The vanishing of `H_{r+1}(cyl q, CMid q b; ℚ)` -/

/-- **The vanishing of the relative rational homology `H_{r+1}(cyl q, CMid q b; ℚ)`** from the two
comparison isomorphisms of the triple `P ⊆ CMid q b ⊆ cyl q` and the pair comparison for `q` in
degrees `r+1` (onto) and `r` (invertible). -/
theorem isZero_relChainsR_cylCMid (q : C(X, B)) (b : B) (r : ℕ)
    (hcol : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) n))
    (hret : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) n))
    (hepi : Epi (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) (r + 1)))
    (hiso : IsIso (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) r)) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.CMid q b)).homology (r + 1)) := by
  classical
  have hS : (Work.Serre.RatTower.tripleShortR (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.fibreSet q b) (Work.Serre.CMid q b) Set.subset_union_right).ShortExact :=
    Work.Serre.RatTower.tripleShortR_shortExact _ _ _ _
  haveI hcol1 : IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) (r + 1)) :=
    hcol (r + 1)
  haveI hcol0 : IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) r) := hcol r
  haveI hret1 : IsIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1)) :=
    hret (r + 1)
  haveI hret0 : IsIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r) := hret r
  -- the commuting square `collapse ≫ incl ≫ retract = relPairMapRat`
  have hsq : HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) (r + 1)
      ≫ HomologicalComplex.homologyMap (Work.Serre.inclMap q b) (r + 1)
      ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1)
      = HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) (r + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      Work.Serre.collapseMap_comp_retractMap]
  have hsq' : HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) r
      ≫ HomologicalComplex.homologyMap (Work.Serre.inclMap q b) r
      ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r
      = HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) r := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      Work.Serre.collapseMap_comp_retractMap]
  -- transfer the hypotheses to the middle map of the triple
  have hSf_epi : Epi (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) (r + 1)) := by
    haveI hcomp : Epi (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) (r + 1)
        ≫ HomologicalComplex.homologyMap (Work.Serre.inclMap q b) (r + 1)
        ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1)) := by
      rw [hsq]; exact hepi
    haveI : Epi (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) (r + 1)
        ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1)) :=
      epi_of_epi (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) (r + 1))
        (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) (r + 1)
          ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1))
    rw [show HomologicalComplex.homologyMap (Work.Serre.inclMap q b) (r + 1)
        = (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) (r + 1)
          ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1))
          ≫ inv (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1)) from by simp]
    exact inferInstance
  have hSf_iso : IsIso (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) r) := by
    haveI hcomp : IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) r
        ≫ HomologicalComplex.homologyMap (Work.Serre.inclMap q b) r
        ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r) := by
      rw [hsq']; exact hiso
    haveI hmid : IsIso (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) r
        ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r) :=
      IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) r)
        (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) r
          ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r)
    exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap (Work.Serre.inclMap q b) r)
      (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r)
  exact Work.Serre.isZero_homology_third_of_epi_isIso hS (r + 1) (by omega) hSf_epi hSf_iso

/-- **The vanishing of the relative rational cohomology `H^{r+1}(cyl q, CMid q b; ℚ)`**, by the
perfect Kronecker duality over the field `ℚ` (`Work.Serre.relKronMapRInjective`). -/
theorem isZero_relCoh_cylCMid (q : C(X, B)) (b : B) (r : ℕ)
    (h : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.CMid q b)).homology (r + 1))) :
    IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Work.Serre.CMid q b)) := by
  classical
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
  haveI : Subsingleton ↥((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.CMid q b)).homology (r + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp h
  have h1 : (Work.Serre.relKronMapR ℚ (TopCat.of (Work.Serre.cyl q))
        (Work.Serre.CMid q b) (r + 1)).hom x
      = (Work.Serre.relKronMapR ℚ (TopCat.of (Work.Serre.cyl q))
        (Work.Serre.CMid q b) (r + 1)).hom y := by
    apply LinearMap.ext
    intro z
    exact congrArg (fun g : (↥((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.CMid q b)).homology (r + 1)) →ₗ[ℚ] ℚ) => g z)
      (Subsingleton.elim (α := ↥((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
        (Work.Serre.CMid q b)).homology (r + 1)) →ₗ[ℚ] ℚ) _ _)
  exact Work.Serre.relKronMapRInjective (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMid q b)
    (r + 1) h1


/-! ## The two comparison isomorphisms (delegated / proved elsewhere)

`collapsePieceIso` is `H_*(X, q⁻¹b;ℚ) ≅ H_*(CMid q b, P;ℚ)` (the cone is attached to the bottom copy
along the fibre) and `retractPieceIso` is `H_*(cyl q, P;ℚ) ≅ H_*(B, {b};ℚ)` (the retraction is a
homotopy equivalence of pairs).  These two are the *only* geometric inputs of the argument. -/

/-- **The collapse `H_*(X, q⁻¹b;ℚ) → H_*(CMid q b, P;ℚ)` is an isomorphism.**

Proof route.  Write `M = cyl q`, `A = range (cylIncl q) ≅ X` (the bottom copy), `P = fibreSet q b`
(the cone on the fibre), `C = CMid q b = A ∪ P`, and let `U = C ∩ cylCollar q` be the collar part
of `C`.  Then

* `H_*(C, P) ≅ H_*(U, U ∩ P)`: excision (`Work.Serre.CylCMidVan.relChainsR_excisionInterior`) for
  the cover of `C` by the open sets `U` and `{λ > 0}` (a point of `C` with `λ = 0` lies in `U`, and
  a point with `λ > 0` lies in `P`, in fact in its interior, by `Work.Serre.CMidPair.cylLam_eq_zero_iff`);
* `H_*(U, U ∩ P) ≅ H_*(A, A ∩ P)`: the collar shrink `Work.Serre.cylShrinkHomotopy` retracts `U`
  onto `A` through maps preserving `P` (`Work.Serre.cylRetract_cylShrink`), giving a homotopy
  equivalence of pairs (see `Work.Serre.DiscPair.relPairHomotopic` and
  `Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso`);
* `H_*(A, A ∩ P) ≅ H_*(X, q⁻¹b)`: the homeomorphism `Work.Serre.cylHomeo`
  (`Work.Serre.isIso_relChainsRPairMap_homeoPair`, or `isIso_relChainsRPairMap_homeo`). -/
theorem collapsePieceIso (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) n) :=
  Work.Stems.collapseMap_isIso q b n

/-- **The retraction `H_*(cyl q, P;ℚ) → H_*(B, {b};ℚ)` is an isomorphism.**

Proof route.  Apply the five lemma for maps of pairs over `ℚ`
(`Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso`) to the map of pairs
`cylRetract q : (cyl q, P) → (B, {b})`:
* `cylRetract q : cyl q → B` is a homotopy equivalence (`Work.Serre.cylHomotopyEquivExplicit`), so
  it is an isomorphism on rational homology;
* its restriction `P → {b}` is a homotopy equivalence as well, since `P` is the cone on the fibre
  (contractible, `Work.Serre.DiscPair.cylRetractPreimageContractible`) and `{b}` is a point; the
  cone contraction `Work.RatHurewicz.cylFibrePush` gives the homotopy
  `const (cylInr q b) ~ id_P` explicitly. -/
theorem retractPieceIso (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) n) :=
  Work.Serre.isIso_retractMap q b n

/-! ## The target -/

theorem fibrePieceSurj {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (hB : PathConnectedSpace B) (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q)
    (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Surjective (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ
      (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMid q b)) r).hom := by
  classical
  haveI := hB
  -- the fibre data, in the sharp form used by the pair comparison
  have hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < r →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q y)) j) :=
    fun y j hj hjr => hvan y j hj (by omega) (le_trans (le_of_lt hjr) hrN)
  have h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q y)) 0
      ≅ ModuleCat.of ℚ ℚ) := fun y => by
    haveI := hpc y
    exact Work.Serre.ratH_zero_of_pathConnected (Work.StemsB.fibre q y)
  -- the pair comparison in degree `r + 1` is onto
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) (r + 1)).hom := by
    rw [show r + 1 = 1 + r from by omega]
    exact Work.Serre.ratPairComparisonOneBoundary q hq b r hr hB (hpc b)
      (fun j hj hjl => hvan b j hj (by omega) (by omega))
  have hepi : Epi (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) (r + 1)) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  -- and invertible in degree `r`
  have hiso : IsIso (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) r) :=
    Work.Serre.B1Rel.relPairMapRat_isIso q hq b (r + 1) r (by omega) hfib h0 r (by omega)
  -- the vanishing of the relative homology, and hence of the relative cohomology
  have hH : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.CMid q b)).homology (r + 1)) :=
    isZero_relChainsR_cylCMid q b r (fun n => collapsePieceIso q b n)
      (fun n => retractPieceIso q b n) hepi hiso
  have hC : IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Work.Serre.CMid q b)) :=
    isZero_relCoh_cylCMid q b r hH
  -- the exact sequence of the pair `(cyl q, CMid q b)`: `δ = 0`, so the restriction is onto
  have hex := Work.Cohomology.pair_exact₃ ℚ (TopCat.of (Work.Serre.cyl q))
    (Work.Serre.CMid q b) r
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  have hδ : Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.CMid q b) r = 0 := IsZero.eq_zero_of_tgt hC _
  have hker : LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ
        (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMid q b) r)) = ⊤ := by
    rw [hδ]; simp
  have hex' : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℚ (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMid q b)) r))
      = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ
        (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMid q b) r)) := hex
  rw [hker] at hex'
  exact LinearMap.range_eq_top.mp hex'

end

end Work.Stems
