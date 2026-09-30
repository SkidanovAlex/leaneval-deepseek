import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.fibrePairMapSurj
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.ratPairComparisonOneBoundary
import Submission.Work.Serre.Basic
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.CMidPairDefs
import Submission.Work.Serre.CMidCollarDefs
import Submission.Work.Serre.CMidCollarShrink
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.CylCMidVan.relChainsR_excisionInterior
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.ratPairComparisonBOneGeneral

/-!
# The "middle" inclusion of the mapping cylinder is injective on rational homology

Target: `Work.Serre.cylMidHomologyInj`.

Write `q : C(X,B)`, `M = cyl q` (the mapping cylinder), `Mid = CMid q b = range (cylIncl q) ∪
(cylRetract q)⁻¹{b}` (the bottom copy together with the cone on the fibre over `b`) and
`P = (cylRetract q)⁻¹{b}` (that cone).  The target is the injectivity of the map
`H_r(Mid;ℚ) → H_r(M;ℚ)` induced by the inclusion, in degree `r`, for a Serre fibration whose fibre
is rationally acyclic in degrees `0 < t < r` (`t ≤ N`) and rationally a line in degree `r`.

## Route

`M ≃ B` and `Mid ≃ X/F_b` (the cofibre of `F_b ↪ X`), so the composite
`H_r(Mid) → H_r(M) → H_r(B)` is `H_r(X,F_b) → H_r(B)`, which is injective because the pair map
`φ_r : H_r(X,F_b) → H_r(B,{b})` is an isomorphism (`Work.Serre.B1Rel.relPairMapRat_isIso`) and
`H_r(B,{b}) → H_r(B)` is an isomorphism for `r ≥ 1`.  Formally we use the pair sequence of
`(M, Mid)`:

`H_{r+1}(M,Mid) → H_r(Mid) → H_r(M)` is exact, so it suffices to know `H_{r+1}(M,Mid;ℚ) = 0`.

For the vanishing, use the triple sequence of `P ⊆ Mid ⊆ M`:
if the map `H_{r+1}(Mid,P) → H_{r+1}(M,P)` is onto and `H_r(Mid,P) → H_r(M,P)` is injective, then
`H_{r+1}(M,Mid) = 0`.  Both statements are transported from the pair map `φ` along

* the isomorphism `H_*(X,F_b) → H_*(Mid,P)` (`π₁` composed with `conePairIso_mid`, i.e. the bottom
  inclusion `X → Mid` after identifying `X` with the bottom copy `cylBot q` by
  `Work.Serre.cylHomeoExplicit`), and
* the isomorphism `H_*(M,P) → H_*(B,{b})` induced by the retraction `cylRetract q` (`μ`), which
  is a homotopy equivalence of pairs because `P` is contractible
  (`Work.Serre.DiscPair.cylRetractPreimageContractible`).
-/

/-!
# The "middle" inclusion of the mapping cylinder is injective on rational homology

(Note on the statement below: as recorded, the type of the intermediate map was written
`C(↥((...) : Set (cyl p), cyl p)) r`, which is missing one closing parenthesis and does not
parse; the statement as formalised here supplies it, i.e. it is
`C(↥((...) : Set (cyl p)), cyl p) r`. No mathematical change is involved.)
-/

/-!
# The "middle" inclusion of the mapping cylinder is injective on rational homology

The statement below is exactly the requested one; as recorded, the type of the intermediate map was
written

  `C(↥((Set.range (Work.Serre.cylIncl p) ∪ (Work.Serre.cylRetract p ⁻¹' {b}) :
      Set (Work.Serre.cyl p)), Work.Serre.cyl p))`

which is missing the closing parenthesis of `↥(` and therefore does not parse
(`unexpected token ')'; expected ','`).  The statement formalised below supplies that parenthesis,
i.e. its intermediate map is `C(↥((...) : Set (Work.Serre.cyl p)), Work.Serre.cyl p)`; no
mathematical change is involved.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Serre
namespace CylMidInj

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- The fibre of `q` over `b`. -/
abbrev Fib (q : C(X, B)) (b : B) : Set X := q ⁻¹' ({b} : Set B)

/-- The middle set `Mid = range (cylIncl q) ∪ (cylRetract q) ⁻¹' {b}`.  (Definitionally equal to
the set appearing in the target statement and to `Work.Serre.CMid q b`.) -/
abbrev Mid (q : C(X, B)) (b : B) : Set (cyl q) :=
  (Set.range (cylIncl q) ∪ (cylRetract q) ⁻¹' ({b} : Set B) : Set (cyl q))

/-- The fibre cone `P = (cylRetract q) ⁻¹' {b}` inside the mapping cylinder. -/
abbrev cone (q : C(X, B)) (b : B) : Set (cyl q) := (cylRetract q) ⁻¹' ({b} : Set B)

lemma cone_subset_mid (q : C(X, B)) (b : B) : cone q b ⊆ Mid q b := Set.subset_union_right

/-- The retraction of the mapping cylinder, restricted to the middle set. -/
def retrMid (q : C(X, B)) (b : B) : C(↥(Mid q b), B) where
  toFun z := cylRetract q z.1
  continuous_toFun := (cylRetract q).continuous.comp continuous_subtype_val

@[simp] lemma retrMid_apply (q : C(X, B)) (b : B) (z : ↥(Mid q b)) :
    retrMid q b z = cylRetract q z.1 := rfl

lemma retrMid_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (retrMid q b) (CMidCollar.M q b) ({b} : Set B) := fun x hx => hx

/-- The bottom copy `cylBot q = range (cylIncl q)` of the mapping cylinder. -/
abbrev bot (q : C(X, B)) : Set (cyl q) := Set.range (cylIncl q)

/-- The homeomorphism of `Work.Serre.cylHomeoExplicit`, chosen once and for all. -/
noncomputable def botHE (q : C(X, B)) : X ≃ₜ ↥(bot q) := Classical.choose (cylHomeoExplicit q)

lemma botHE_spec (q : C(X, B)) (x : X) : (botHE q x : cyl q) = cylIncl q x :=
  Classical.choose_spec (cylHomeoExplicit q) x

/-- The bottom-copy homeomorphism, as a continuous map. -/
def botC (q : C(X, B)) : C(X, ↥(bot q)) := ⟨⇑(botHE q), (botHE q).continuous⟩

@[simp] lemma botC_apply (q : C(X, B)) (x : X) : botC q x = botHE q x := rfl

lemma retr_botHE (q : C(X, B)) (x : X) :
    cylRetract q ((botHE q x : ↥(bot q)) : cyl q) = q x :=
  (congrArg (cylRetract q) (botHE_spec q x)).trans
    (DFunLike.congr_fun (cylRetract_cylIncl q) x)

lemma botHE_symm_coe (q : C(X, B)) (y : ↥(bot q)) :
    (botHE q ((botHE q).symm y) : cyl q) = (y : cyl q) :=
  congrArg Subtype.val (Homeomorph.apply_symm_apply (botHE q) y)

lemma cylIncl_botHE_symm (q : C(X, B)) (y : ↥(bot q)) :
    cylIncl q ((botHE q).symm y) = (y : cyl q) :=
  (botHE_spec q ((botHE q).symm y)).symm.trans (botHE_symm_coe q y)

lemma fibHE_toFun_mem (q : C(X, B)) (b : B) (x : ↥(Fib q b)) :
    cylRetract q ((botHE q x.1 : ↥(bot q)) : cyl q) ∈ ({b} : Set B) :=
  Eq.mpr (congrArg (fun z : B => z ∈ ({b} : Set B)) (retr_botHE q x.1)) x.2

lemma fibHE_invFun_mem (q : C(X, B)) (b : B) (y : ↥(CMidCollar.A q b)) :
    q ((botHE q).symm (y.1 : ↥(bot q))) ∈ ({b} : Set B) := by
  have h1 : q ((botHE q).symm (y.1 : ↥(bot q)))
      = cylRetract q ((y.1 : ↥(bot q)) : cyl q) :=
    ((DFunLike.congr_fun (cylRetract_cylIncl q) _).symm).trans
      (congrArg (cylRetract q) (cylIncl_botHE_symm q (y.1 : ↥(bot q))))
  rw [h1]
  exact y.2

/-- The restriction of the bottom-copy homeomorphism to the fibres: `F_b ≃ A`, where `A` is the
copy of the fibre inside the bottom copy. -/
noncomputable def fibHE (q : C(X, B)) (b : B) : ↥(Fib q b) ≃ₜ ↥(CMidCollar.A q b) where
  toFun x := ⟨botHE q x.1, fibHE_toFun_mem q b x⟩
  invFun y := ⟨(botHE q).symm (y.1 : ↥(bot q)), fibHE_invFun_mem q b y⟩
  left_inv x := Subtype.ext (Homeomorph.symm_apply_apply (botHE q) x.1)
  right_inv y := Subtype.ext (Homeomorph.apply_symm_apply (botHE q) (y.1 : ↥(bot q)))
  continuous_toFun := Continuous.subtype_mk ((botHE q).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((botHE q).symm.continuous.comp continuous_subtype_val) _


/-! ## Auxiliary: a map between acyclic spaces is a rational homology isomorphism -/

lemma ratHomologyMap_comp' {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    ratHomologyMap (g.comp f) n = ratHomologyMap f n ≫ ratHomologyMap g n := by
  show HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Z)
      (TopCat.ofHom (g.comp f))) n
    = HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
        (TopCat.ofHom f)) n
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z)
          (TopCat.ofHom g)) n
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from TopCat.ofHom_comp f g,
    show Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Z)
          (TopCat.ofHom f ≫ TopCat.ofHom g)
        = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)
          ≫ Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g) from by
      simp only [Work.Cohomology.chainMap, Functor.map_comp]]
  exact HomologicalComplex.homologyMap_comp _ _ _

/-- A map between contractible spaces is an isomorphism on rational homology. -/
theorem isRatHomologyIso_of_contractible {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) : IsRatHomologyIso f := by
  have hX : IsRatHomologyIso (toPoint X) := ratAcyclic_of_contractible X
  have hY : IsRatHomologyIso (toPoint Y) := ratAcyclic_of_contractible Y
  intro n
  have hsq : ratHomologyMap (toPoint X) n = ratHomologyMap f n ≫ ratHomologyMap (toPoint Y) n := by
    rw [show toPoint X = (toPoint Y).comp f from
      ContinuousMap.ext (fun x => Subsingleton.elim _ _), ratHomologyMap_comp']
  haveI := hY n
  haveI hcomp : IsIso (ratHomologyMap f n ≫ ratHomologyMap (toPoint Y) n) := by
    rw [← hsq]; exact hX n
  exact IsIso.of_isIso_comp_right (ratHomologyMap f n) (ratHomologyMap (toPoint Y) n)

/-! ## The maps of the comparison -/

/-- The inclusion of the source as the bottom copy of the middle set. -/
def midBottom (q : C(X, B)) (b : B) : C(X, ↥(Mid q b)) where
  toFun x := ⟨cylIncl q x, Or.inl ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk (cylIncl q).continuous (fun x => Or.inl ⟨x, rfl⟩)

@[simp] lemma midBottom_coe (q : C(X, B)) (b : B) (x : X) :
    ((midBottom q b x : ↥(Mid q b)) : cyl q) = cylIncl q x := rfl

lemma midBottom_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (midBottom q b) (Fib q b) (CMidCollar.M q b) := by
  intro x hx
  show (midBottom q b x : cyl q) ∈ (cylRetract q) ⁻¹' ({b} : Set B)
  rw [midBottom_coe]
  exact (DFunLike.congr_fun (cylRetract_cylIncl q) x).trans hx

lemma botHE_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (⇑(botHE q)) (Fib q b) (CMidCollar.A q b) :=
  fun x hx => fibHE_toFun_mem q b ⟨x, hx⟩

/-- The comparison `(X, F_b) → (cylBot q, A)` induced by the bottom-copy homeomorphism. -/
def pi1 (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(bot q)) (CMidCollar.A q b) :=
  relChainsRPairMap (Fib q b) (CMidCollar.A q b) (botC q)
    (botHE_mapsTo q b)

/-- The cone-pair comparison `(cylBot q, A) → (Mid, M)`. -/
def rho (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(bot q)) (CMidCollar.A q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(Mid q b)) (CMidCollar.M q b) :=
  relChainsRPairMap (CMidCollar.A q b) (CMidCollar.M q b) (CMidCollar.inclAC q b)
    (CMidCollar.mapsTo_inclAC q b)

/-- The comparison `(X, F_b) → (Mid, M)`: the bottom inclusion composed with the cone-pair
isomorphism. -/
def rhoX (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(Mid q b)) (CMidCollar.M q b) :=
  pi1 q b ≫ rho q b

/-- The retraction `(Mid, M) → (B, {b})`. -/
def delta (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(Mid q b)) (CMidCollar.M q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of B) ({b} : Set B) :=
  relChainsRPairMap (CMidCollar.M q b) ({b} : Set B) (retrMid q b) (retrMid_mapsTo q b)

/-- The retraction `(cyl q, P) → (B, {b})`. -/
def mu (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of (cyl q)) (cone q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of B) ({b} : Set B) :=
  relChainsRPairMap (cone q b) ({b} : Set B) (cylRetract q) (fun _ hx => hx)

/-- The pair map `(X, F_b) → (B, {b})`. -/
def phi (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of B) ({b} : Set B) :=
  relPairMapRat q b

/-! ## The comparison maps are homology isomorphisms -/

/-- The fibre homeomorphism, as a continuous map. -/
def fibC (q : C(X, B)) (b : B) : C(↥(Fib q b), ↥(CMidCollar.A q b)) :=
  ⟨⇑(fibHE q b), (fibHE q b).continuous⟩

@[simp] lemma fibC_apply (q : C(X, B)) (b : B) (x : ↥(Fib q b)) : fibC q b x = fibHE q b x := rfl

lemma isRatHomologyIso_botHE (q : C(X, B)) : IsRatHomologyIso (botC q) :=
  IsRatHomologyIso.of_homotopyEquiv (botHE q).toHomotopyEquiv

lemma isRatHomologyIso_fibHE (q : C(X, B)) (b : B) : IsRatHomologyIso (fibC q b) :=
  IsRatHomologyIso.of_homotopyEquiv (fibHE q b).toHomotopyEquiv

theorem isIso_restrict_fibHE (q : C(X, B)) (b : B) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ
      (TopCat.of ↥(Fib q b)) (TopCat.of ↥(CMidCollar.A q b))
      (TopCat.ofHom (Work.Serre.DiscPair.restrictPair (Fib q b) (CMidCollar.A q b) (botC q)
        (botHE_mapsTo q b)))) k) := by
  have h : IsRatHomologyIso (fibC q b) := isRatHomologyIso_fibHE q b
  have heq : Work.Serre.DiscPair.restrictPair (Fib q b) (CMidCollar.A q b) (botC q)
      (botHE_mapsTo q b) = fibC q b := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl
  change IsIso (ratHomologyMap (Work.Serre.DiscPair.restrictPair (Fib q b)
    (CMidCollar.A q b) (botC q) (botHE_mapsTo q b)) k)
  rw [heq]
  exact h k

theorem isIso_pi1 (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (pi1 q b) n) := by
  have hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ
      (TopCat.of X) (TopCat.of ↥(bot q)) (TopCat.ofHom (botC q))) k) := by
    intro k
    have h : IsRatHomologyIso (botC q) := isRatHomologyIso_botHE q
    exact h k
  have hA : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ
      (TopCat.of ↥(Fib q b)) (TopCat.of ↥(CMidCollar.A q b))
      (TopCat.ofHom (Work.Serre.DiscPair.restrictPair (Fib q b) (CMidCollar.A q b) (botC q)
        (botHE_mapsTo q b)))) k) := isIso_restrict_fibHE q b
  exact Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso (Fib q b)
    (CMidCollar.A q b) (botC q) (botHE_mapsTo q b) n hf hA

theorem isIso_rho (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (rho q b) n) :=
  Work.Serre.CMidCollar.conePairIso_mid q b n

theorem isIso_rhoX (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (rhoX q b) n) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap (pi1 q b) n) := isIso_pi1 q b n
  haveI h2 : IsIso (HomologicalComplex.homologyMap (rho q b) n) := isIso_rho q b n
  show IsIso (HomologicalComplex.homologyMap (pi1 q b ≫ rho q b) n)
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **The comparison square**: the composite `(X,F_b) → (Mid,M) → (B,{b})` is the pair map. -/
theorem rhoX_comp_delta (q : C(X, B)) (b : B) : rhoX q b ≫ delta q b = phi q b := by
  have hmid : (CMidCollar.inclAC q b).comp (botC q) = midBottom q b := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact botHE_spec q x
  have hmm : (retrMid q b).comp (midBottom q b) = q := by
    apply ContinuousMap.ext
    intro x
    show cylRetract q ((midBottom q b x : ↥(Mid q b)) : cyl q) = q x
    rw [midBottom_coe]
    exact DFunLike.congr_fun (cylRetract_cylIncl q) x
  calc rhoX q b ≫ delta q b
      = (relChainsRPairMap (Fib q b) (CMidCollar.M q b)
            ((CMidCollar.inclAC q b).comp (botC q))
            ((CMidCollar.mapsTo_inclAC q b).comp (botHE_mapsTo q b)))
          ≫ delta q b := by
        rw [rhoX, pi1, rho, CsrSharp.Tools.relChainsRPairMap_comp]
    _ = (relChainsRPairMap (Fib q b) (CMidCollar.M q b) (midBottom q b)
            (midBottom_mapsTo q b)) ≫ delta q b := by
        rw [CsrSharp.Tools.relChainsRPairMap_congr hmid _ _]
    _ = relChainsRPairMap (Fib q b) ({b} : Set B) ((retrMid q b).comp (midBottom q b))
          ((retrMid_mapsTo q b).comp (midBottom_mapsTo q b)) := by
        rw [delta, CsrSharp.Tools.relChainsRPairMap_comp]
    _ = relChainsRPairMap (Fib q b) ({b} : Set B) q (fun _ hx => hx) := by
        rw [CsrSharp.Tools.relChainsRPairMap_congr hmm _ _]
    _ = phi q b := rfl

/-! ## The vanishing of `H_{r+1}(M, Mid)` and the final assembly -/


/-! ## The retraction `(M, P) → (B, {b})` is a homology isomorphism -/

/-- The apex of the cone `cone q b`. -/
def conePt (q : C(X, B)) (b : B) : ↥(cone q b) := ⟨cylInr q b, rfl⟩

/-- The push-up homotopy contracts the cone `cone q b` to its apex. -/
def coneHomotopy (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(cone q b))
      (ContinuousMap.const ↥(cone q b) (conePt q b)) where
  toContinuousMap :=
    ⟨fun z : unitInterval × ↥(cone q b) => ⟨cylMove q (z.2, z.1), by
        show cylRetract q (cylMove q (z.2, z.1)) ∈ ({b} : Set B)
        rw [CMidPair.cylRetract_cylMove]
        exact z.2.2⟩,
      Continuous.subtype_mk (f := fun z : unitInterval × ↥(cone q b) => cylMove q (z.2, z.1))
        ((cylMove q).continuous.comp
          ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))
        (fun z => by
          show cylRetract q (cylMove q (z.2, z.1)) ∈ ({b} : Set B)
          rw [CMidPair.cylRetract_cylMove]
          exact z.2.2)⟩
  map_zero_left := fun y => by
    apply Subtype.ext
    show (cylMove q (y, 0) : cyl q) = (y : cyl q)
    rw [cylMove_zero]
  map_one_left := fun y => by
    apply Subtype.ext
    show (cylMove q (y, 1) : cyl q) = cylInr q b
    rw [cylMove_one]
    exact congrArg (fun z => cylInr q z) y.2

/-- The restriction of the retraction to the cone. -/
def coneToPt (q : C(X, B)) (b : B) : C(↥(cone q b), ↥({b} : Set B)) where
  toFun z := ⟨cylRetract q z.1, z.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (f := fun z : ↥(cone q b) => cylRetract q z.1)
      ((cylRetract q).continuous.comp continuous_subtype_val) (fun z => z.2)

/-- The apex, as a map from the base point. -/
def ptToCone (q : C(X, B)) (b : B) : C(↥({b} : Set B), ↥(cone q b)) where
  toFun _ := conePt q b
  continuous_toFun := continuous_const

lemma ptToCone_comp_coneToPt (q : C(X, B)) (b : B) :
    (ptToCone q b).comp (coneToPt q b) = ContinuousMap.const ↥(cone q b) (conePt q b) :=
  ContinuousMap.ext (fun _ => rfl)

/-- The restriction of the retraction to the cone, as a homotopy equivalence onto the base. -/
def coneHE (q : C(X, B)) (b : B) :
    ContinuousMap.HomotopyEquiv ↥(cone q b) ↥({b} : Set B) :=
  ContinuousMap.HomotopyEquiv.mk (coneToPt q b) (ptToCone q b)
    (by
      show ((ptToCone q b).comp (coneToPt q b)).Homotopic (ContinuousMap.id ↥(cone q b))
      rw [ptToCone_comp_coneToPt]
      exact ⟨(coneHomotopy q b).symm⟩)
    (by
      have hsub : Subsingleton ↥({b} : Set B) := ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
      have hcomp : (coneToPt q b).comp (ptToCone q b) = ContinuousMap.id ↥({b} : Set B) :=
        ContinuousMap.ext (fun x => hsub.elim _ _)
      show ((coneToPt q b).comp (ptToCone q b)).Homotopic (ContinuousMap.id ↥({b} : Set B))
      rw [hcomp])

theorem isIso_mu (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (mu q b) n) := by
  refine Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso (cone q b) ({b} : Set B)
    (cylRetract q) (fun _ hx => hx) n ?_ ?_
  · intro j
    obtain ⟨E, hE⟩ := cylHomotopyEquivExplicit q
    have h : IsRatHomologyIso E.toFun := IsRatHomologyIso.of_homotopyEquiv E
    have hh : IsIso (ratHomologyMap E.toFun j) := h j
    rwa [hE] at hh
  · intro j
    have h : IsRatHomologyIso (coneHE q b).toFun :=
      IsRatHomologyIso.of_homotopyEquiv (coneHE q b)
    have hh : IsIso (ratHomologyMap (coneHE q b).toFun j) := h j
    have hmap : (coneHE q b).toFun = Work.Serre.DiscPair.restrictPair (cone q b)
        ({b} : Set B) (cylRetract q) (fun _ hx => hx) :=
      ContinuousMap.ext (fun x => Subtype.ext rfl)
    rwa [hmap] at hh


/-! ## The triple sequence of `P ⊆ Mid ⊆ M` -/

/-- The triple short exact sequence `0 → C_*(Mid,P;ℚ) → C_*(M,P;ℚ) → C_*(M,Mid;ℚ) → 0`. -/
def trip (q : C(X, B)) (b : B) : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
  Work.Serre.RatTower.tripleShortR (TopCat.of (cyl q)) (cone q b) (Mid q b) (cone_subset_mid q b)

/-- The inclusion `Mid ⊆ cyl q`, as a map of pairs `(Mid, P ∩ Mid) → (M, P)`. -/
def midInclM (q : C(X, B)) (b : B) : C(↥(Mid q b), cyl q) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem midInclM_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (midInclM q b) (CMidCollar.M q b) (cone q b) := fun _ hx => hx

/-- The middle map of the triple is the pair map of the inclusion. -/
theorem trip_f_eq (q : C(X, B)) (b : B) :
    (trip q b).f = relChainsRPairMap (CMidCollar.M q b) (cone q b) (midInclM q b)
      (midInclM_mapsTo q b) := rfl

/-- **The comparison square**: the middle map of the triple followed by the retraction of the
cylinder is the restriction of `cylRetract q` to the middle set. -/
theorem delta_eq_trip_f (q : C(X, B)) (b : B) : delta q b = (trip q b).f ≫ mu q b := by
  have hcomp : (cylRetract q).comp (midInclM q b) = retrMid q b :=
    ContinuousMap.ext (fun _ => rfl)
  calc delta q b
      = relChainsRPairMap (CMidCollar.M q b) ({b} : Set B) (retrMid q b)
          (retrMid_mapsTo q b) := rfl
    _ = relChainsRPairMap (CMidCollar.M q b) ({b} : Set B)
          ((cylRetract q).comp (midInclM q b))
          ((fun _ hx => hx) : Set.MapsTo ((cylRetract q).comp (midInclM q b))
            (CMidCollar.M q b) ({b} : Set B)) :=
        (CsrSharp.Tools.relChainsRPairMap_congr hcomp.symm _ _).symm
    _ = relChainsRPairMap (CMidCollar.M q b) (cone q b) (midInclM q b) (midInclM_mapsTo q b)
          ≫ relChainsRPairMap (cone q b) ({b} : Set B) (cylRetract q) (fun _ hx => hx) :=
        (CsrSharp.Tools.relChainsRPairMap_comp (midInclM q b) (cylRetract q)
          (midInclM_mapsTo q b) (fun _ hx => hx)
          (hg'' := (fun _ hx => hx : Set.MapsTo ((cylRetract q).comp (midInclM q b))
            (CMidCollar.M q b) ({b} : Set B)))).symm
    _ = (trip q b).f ≫ mu q b := rfl

/-! ## Vanishing from the pair comparison -/

/-- **Vanishing of the third term of a short exact sequence of chain complexes over `ℚ`.**  If
`0 → X₁ → X₂ → X₃ → 0` is short exact and the map `H_n(X₁) → H_n(X₂)` is onto while
`H_{n-1}(X₁) → H_{n-1}(X₂)` is an isomorphism, then `H_n(X₃) = 0`. -/
theorem isZero_homology_third_of_epi_isIso {S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)}
    (hS : S.ShortExact) (n : ℕ) (hn : 1 ≤ n)
    (hepi : CategoryTheory.Epi (HomologicalComplex.homologyMap S.f n))
    (hiso : CategoryTheory.IsIso (HomologicalComplex.homologyMap S.f (n - 1))) :
    IsZero (S.X₃.homology n) := by
  have hrel : (ComplexShape.down ℕ).Rel n (n - 1) := by simp [ComplexShape.down]; omega
  have h2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have h3 := (hS.homology_exact₃ n (n - 1) hrel).moduleCat_range_eq_ker
  have h1 := (hS.homology_exact₁ n (n - 1) hrel).moduleCat_range_eq_ker
  have hβker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n)).ker = ⊤ := by
    rw [← h2]
    exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp hepi)
  have hβhom : ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n) = 0 :=
    LinearMap.ker_eq_top.mp hβker
  have hδker : (ModuleCat.Hom.hom (hS.δ n (n - 1) hrel)).ker = ⊥ := by
    rw [← h3, hβhom]
    simp
  have hδinj : Function.Injective (ModuleCat.Hom.hom (hS.δ n (n - 1) hrel)) :=
    LinearMap.ker_eq_bot.mp hδker
  haveI : IsIso (HomologicalComplex.homologyMap S.f (n - 1)) := hiso
  have hγinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f (n - 1))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hδzero : ModuleCat.Hom.hom (hS.δ n (n - 1) hrel) = 0 := by
    have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f (n - 1))).ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr hγinj
    have hrange : (ModuleCat.Hom.hom (hS.δ n (n - 1) hrel)).range = ⊥ := by
      rw [h1, hker]
    exact LinearMap.range_eq_bot.mp hrange
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  have key : ∀ x : ↥(S.X₃.homology n), x = 0 := by
    intro x
    apply hδinj
    rw [hδzero]; rfl
  rw [key a, key b]

/-- **The vanishing of `H_{r+1}(M, Mid;ℚ)`** from the pair comparison: if the pair map
`φ : (X,F_b) → (B,{b})` is onto in degree `r+1` and an isomorphism in degree `r`, then the
relative homology of the mapping cylinder modulo the middle set vanishes in degree `r+1`. -/
theorem isZero_homology_cylMid (q : C(X, B)) (b : B) (r : ℕ)
    (hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (phi q b) (r + 1)).hom)
    (hiso : CategoryTheory.IsIso (HomologicalComplex.homologyMap (phi q b) r)) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (cyl q)) (Mid q b)).homology (r + 1)) := by
  have hsq : rhoX q b ≫ delta q b
      = 𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b)) ≫ phi q b := by
    rw [rhoX_comp_delta, Category.id_comp]
  have hδsurj : Function.Surjective
      (HomologicalComplex.homologyMap (delta q b) (r + 1)).hom := by
    have hc : Function.Surjective (HomologicalComplex.homologyMap
        (𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b))) (r + 1)).hom := by
      rw [HomologicalComplex.homologyMap_id]
      exact fun y => ⟨y, by simp⟩
    exact CsrSharp.Tools.surjective_of_sq_right (rhoX q b) (delta q b)
      (𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b))) (phi q b) hsq (r + 1) hc hsurj
  have hδiso : CategoryTheory.IsIso (HomologicalComplex.homologyMap (delta q b) r) := by
    have hc : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b))) r) := by
      rw [HomologicalComplex.homologyMap_id]; infer_instance
    exact CsrSharp.Tools.isIso_of_sq_right (rhoX q b) (delta q b)
      (𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) (Fib q b))) (phi q b) hsq r
      (isIso_rhoX q b r) hc hiso
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap (mu q b) (r + 1)) :=
    isIso_mu q b (r + 1)
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap (mu q b) r) := isIso_mu q b r
  have htripsurj : CategoryTheory.Epi (HomologicalComplex.homologyMap (trip q b).f (r + 1)) := by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    have hδ : Function.Surjective
        (HomologicalComplex.homologyMap (delta q b) (r + 1)).hom := hδsurj
    rw [delta_eq_trip_f, HomologicalComplex.homologyMap_comp] at hδ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hδ
    obtain ⟨x, hx⟩ := hδ ((HomologicalComplex.homologyMap (mu q b) (r + 1)).hom y)
    exact ⟨x, (ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap (mu q b) (r + 1))).1 hx⟩
  have htripsiso : CategoryTheory.IsIso (HomologicalComplex.homologyMap (trip q b).f r) := by
    refine CsrSharp.Tools.isIso_of_sq_left (trip q b).f (mu q b) (delta q b) (𝟙 _) ?_ r
      (isIso_mu q b r) hδiso ?_
    · rw [delta_eq_trip_f, Category.comp_id]
    · rw [HomologicalComplex.homologyMap_id]; infer_instance
  exact isZero_homology_third_of_epi_isIso
    (Work.Serre.RatTower.tripleShortR_shortExact
      (TopCat.of (cyl q)) (cone q b) (Mid q b) (cone_subset_mid q b))
    (r + 1) (by omega) htripsurj htripsiso

end
end CylMidInj

open CylMidInj in
/-- The inclusion of `C = range (cylIncl p) ∪ (cylRetract p)⁻¹{b}` into the mapping cylinder
`cyl p` is injective on rational homology in degree `r`.  This is the cylinder-vocabulary form of
the homological half of `Work.Serre.fibrePairMapSurj` (dual to `H^r(B,{b};ℚ) ↠ H^r(E,p⁻¹{b};ℚ)`).

WARNING about a bad counterexample raised in review: it is NOT true that `C ≃ E` (equivalently, the
cone `CF_b` does not retract onto its base — `π_1(S¹) → π_1(pt)` forbids it).  The correct
identification is `C = E ∪_{p⁻¹b} C(p⁻¹b) ≃ E/p⁻¹{b}`, so `H_r(C) ≅ H_r(E,p⁻¹{b})` and the map in
the statement is the pair map `H_r(E,p⁻¹{b}) → H_r(B,{b})` modulo `cyl p ≃ B`; that map is injective
in degree `r` because the relative Serre spectral sequence has no other `E₂`-entries in total degree
`r` (rows `0<q<r` vanish by `hvan`, row `q=r` contributes `H⁰(B,{b};H_r(F)) = 0`).  Concretely, for
`T² → S¹` with `r=N=1` one has `H_1(C) ≅ H_1(T²,S¹) ≅ ℚ` and the map to `H_1(S¹) ≅ ℚ` is an
isomorphism, so the statement holds there. -/
theorem cylMidHomologyInj (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Injective (Work.Serre.ratHomologyMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Set.range (Work.Serre.cylIncl p) ∪ (Work.Serre.cylRetract p ⁻¹' {b}) :
            Set (Work.Serre.cyl p))), Work.Serre.cyl p)) r).hom := by
  haveI := hB
  -- the pair comparison `(E, p⁻¹{b}) → (B, {b})` is an isomorphism in degree `r` and onto in `r+1`
  have hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < r →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j) :=
    fun y j hj hjr => hvan y j hj (by omega) (le_trans (le_of_lt hjr) hrN)
  have h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ) := fun y => by
    haveI := hpc y
    exact Work.Serre.ratH_zero_of_pathConnected (Work.StemsB.fibre p y)
  have hiso : CategoryTheory.IsIso (HomologicalComplex.homologyMap (CylMidInj.phi p b) r) :=
    Work.Serre.B1Rel.relPairMapRat_isIso p hp b (r + 1) r (by omega) hfib h0 r (by omega)
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (CylMidInj.phi p b) (r + 1)).hom := by
    rw [show r + 1 = 1 + r from by omega]
    exact Work.Serre.ratPairComparisonOneBoundary p hp b r hr hB (hpc b)
      (fun j hj hjl => hvan b j hj (by omega) (by omega))
  -- the vanishing
  have hzero := CylMidInj.isZero_homology_cylMid p b r hsurj hiso
  -- the pair sequence of `(cyl p, Mid)`
  have hmono : Mono (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.Serre.cyl p))
        (CylMidInj.Mid p b)) r) :=
    (Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of (Work.Serre.cyl p)) (CylMidInj.Mid p b)
      r).mono_g_iff.mpr (IsZero.eq_zero_of_src hzero _)
  exact (ModuleCat.mono_iff_injective _).mp hmono



end Work.Serre
