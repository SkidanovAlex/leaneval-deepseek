import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.fibrePairMapInject
import Submission.Work.Serre.CMidPairDefs
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.csrRelIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology of the "middle" pair of a mapping cylinder surjects onto the homology of the
cylinder

Write `M = cyl q` for the mapping cylinder of `q : C(X,B)`, `A = range (cylIncl q)` for the bottom
copy of the source, `P = (cylRetract q)⁻¹{b}` for the fibre of the retraction over `b` (the cone on
the fibre `q⁻¹b`) and `Cm = A ∪ P` for their union.

The main statement, `Work.Serre.cylMidHomologyOnto`, says that in the transgression degree `r+1` the
map `H_{r+1}(Cm;ℚ) → H_{r+1}(M;ℚ)` is onto, for a Serre fibration whose fibres are rationally
acyclic in degrees `0 < j < r` and rationally a line in degree `r`.

## Route

Enlarging the relative part from `P` to the whole of `M` (both `P` and its copy inside `Cm` are
contractible, via the push-up homotopy `cylMove`), it is enough to show that the map of pairs
`(Cm, P) → (M, P)` is onto in degree `r+1`.  The map of pairs `(X, q⁻¹b) → (B,{b})` factors as

  `(X, q⁻¹b) --cylIncl--> (Cm, P) --incl--> (M, P) --cylRetract--> (B, {b})`,

the first map being the "collapse" of the cone onto the bottom copy, and the last one a rational
homology isomorphism (it is the retraction of the cylinder onto its target, restricted to the pair
`(M,P) → (B,{b})`, which is a homotopy equivalence of pairs).  The composite is the pair map
`relPairMapRat q b` (`midCollapse_comp` below), which is *onto* in degree `r+1` by
`Work.Serre.ratPairComparisonOneBoundary` (the analytic half of `Work.Serre.fibrePairMapInject`).
Since the last map is an isomorphism and the first one is onto, the middle map is onto.

The transfer from the pair `(Cm,P)` to the absolute homology of `Cm` uses the long exact sequence of
the pair: the projection `H_{r+1}(Cm) → H_{r+1}(Cm,P)` is an isomorphism because `P` (and hence its
copy inside `Cm`) is contractible, so it suffices to know that the corresponding projection lands in
the image.

## A note on the statement as requested

The text of the requested statement has an unbalanced parenthesis in the type of the domain of the
map: after `Set (Work.Serre.cyl p)` it closes only the `Set (` and the type ascription, but not the
`↥(` of the coercion, i.e. it reads `Set (Work.Serre.cyl p)), Work.Serre.cyl p))` where the
(subtype) inclusion of `range (cylIncl p) ∪ (cylRetract p)⁻¹{b}` requires
`Set (Work.Serre.cyl p))), Work.Serre.cyl p))`.  As recorded the statement is not well-formed Lean
syntax and cannot be elaborated at all (the parser fails inside the `C(_, _)` notation).  The
declaration below therefore inserts the missing parenthesis — the same form as the on-disk sibling
`Submission/Work/Serre/cylMidHomologyInj.lean` — which is the intended map: the inclusion
`cInclM` of `Work.Serre.CMid p b` into `cyl p`, the very statement consumed by
`Work.Serre.fibreNonvanishing_of_cylMid` in `Submission/Work/Serre/fibreNonvanishing.lean`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## The vocabulary of the middle pair -/

/-- The fibre of the retraction of the mapping cylinder over `b`: the cone on the fibre `q⁻¹{b}`. -/
abbrev midFib (q : C(X, B)) (b : B) : Set (cyl q) := (cylRetract q) ⁻¹' ({b} : Set B)

/-- The "middle" set: the bottom copy of the source together with the fibre cone. -/
abbrev midSet (q : C(X, B)) (b : B) : Set (cyl q) := Set.range (cylIncl q) ∪ midFib q b

/-- The fibre cone, viewed as a subset of the middle set. -/
abbrev midFibSet (q : C(X, B)) (b : B) : Set ↥(midSet q b) := {x | (x : cyl q) ∈ midFib q b}

/-- The apex of the cone `midFib q b`, as a point of the middle set. -/
def midApex (q : C(X, B)) (b : B) : ↥(midFib q b) :=
  ⟨cylInr q b, by show cylRetract q (cylInr q b) ∈ ({b} : Set B); rfl⟩

/-- The inclusion of the middle set into the mapping cylinder. -/
def midIncl (q : C(X, B)) (b : B) : C(↥(midSet q b), cyl q) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

/-- The bottom copy of the source, as a map into the middle set. -/
def midTo (q : C(X, B)) (b : B) : C(X, ↥(midSet q b)) where
  toFun x := ⟨cylIncl q x, Or.inl ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk (cylIncl q).continuous (fun x => Or.inl ⟨x, rfl⟩)

@[simp] theorem midTo_coe (q : C(X, B)) (b : B) (x : X) :
    ((midTo q b x : ↥(midSet q b)) : cyl q) = cylIncl q x := rfl

@[simp] theorem midIncl_coe (q : C(X, B)) (b : B) (x : ↥(midSet q b)) :
    (midIncl q b x : cyl q) = (x : cyl q) := rfl

/-- **The collapse** `C_*(X, q⁻¹b) → C_*(Cm, P)`: the cone is attached along the fibre, so the
relative chains of `(Cm,P)` compute those of `(X,q⁻¹b)` through the bottom inclusion. -/
def midCollapse (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b} : Set B)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(midSet q b)) (midFibSet q b) :=
  relChainsRPairMap (q ⁻¹' ({b} : Set B)) (midFibSet q b) (midTo q b) (by
    intro x hx
    show cylRetract q (cylIncl q x) ∈ ({b} : Set B)
    rw [show cylRetract q (cylIncl q x) = q x from DFunLike.congr_fun (cylRetract_cylIncl q) x]
    exact hx)

/-- The map of pairs `(Cm, P) → (M, P)` induced by the inclusion `Cm ⊆ M`. -/
def midPair (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(midSet q b)) (midFibSet q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (cyl q)) (midFib q b) :=
  relChainsRPairMap (midFibSet q b) (midFib q b) (midIncl q b) (fun x hx => hx)

/-- The map of pairs `(M, P) → (B, {b})` induced by the retraction of the cylinder. -/
def midRetr (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of (cyl q)) (midFib q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of B) ({b} : Set B) :=
  relChainsRPairMap (midFib q b) ({b} : Set B) (cylRetract q) (fun x hx => hx)

/-! ## The push-up homotopy contracts the fibre cone -/

/-- The push-up homotopy of the mapping cylinder stays inside the fibre cone. -/
theorem midFibMove_mem (q : C(X, B)) (b : B) (z : unitInterval × ↥(midFib q b)) :
    cylMove q (z.2, z.1) ∈ midFib q b := by
  show cylRetract q (cylMove q (z.2, z.1)) ∈ ({b} : Set B)
  rw [CMidPair.cylRetract_cylMove]
  exact z.2.2

/-- The push-up homotopy of the mapping cylinder, restricted to the fibre cone. -/
def midFibHom (q : C(X, B)) (b : B) :
    C(unitInterval × ↥(midFib q b), ↥(midFib q b)) where
  toFun z := ⟨cylMove q (z.2, z.1), midFibMove_mem q b z⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylMove q).continuous.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))
    (fun z => midFibMove_mem q b z)

/-- The push-up homotopy contracts the fibre cone onto its apex. -/
def midFibHomotopy (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(midFib q b))
      (ContinuousMap.const ↥(midFib q b) (midApex q b)) where
  toContinuousMap := midFibHom q b
  map_zero_left := fun y => by
    apply Subtype.ext
    show (cylMove q (y, 0) : cyl q) = (y : cyl q)
    rw [cylMove_zero]
  map_one_left := fun y => by
    apply Subtype.ext
    show (cylMove q (y, 1) : cyl q) = cylInr q b
    rw [cylMove_one]
    exact congrArg (fun z => cylInr q z) y.2

/-- The fibre cone is contractible. -/
theorem midFib_contractible (q : C(X, B)) (b : B) : ContractibleSpace ↥(midFib q b) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨midApex q b, ⟨midFibHomotopy q b⟩⟩

/-- The fibre cone is rationally acyclic. -/
theorem midFib_ratAcyclic (q : C(X, B)) (b : B) : RatAcyclic ↥(midFib q b) :=
  @ratAcyclic_of_contractible ↥(midFib q b) _ (midFib_contractible q b)

/-- `H_k` of the fibre cone vanishes for `k > 0`. -/
theorem isZero_ratH_midFib (q : C(X, B)) (b : B) (k : ℕ) (hk : 0 < k) :
    IsZero (ratH (TopCat.of ↥(midFib q b)) k) :=
  RatAcyclic.isZero_ratH (midFib_ratAcyclic q b) hk

/-! ## The fibre cone inside the middle set -/

/-- The fibre cone is contained in the middle set. -/
theorem midFib_subset (q : C(X, B)) (b : B) : midFib q b ⊆ midSet q b :=
  Set.subset_union_right

/-- The fibre cone, included into the middle set. -/
def midFibSetIncl (q : C(X, B)) (b : B) : C(↥(midFib q b), ↥(midSet q b)) where
  toFun y := ⟨(y : cyl q), Or.inr y.2⟩
  continuous_toFun := by
    show Continuous fun y : ↥(midFib q b) => (⟨(y : cyl q), Or.inr y.2⟩ : ↥(midSet q b))
    exact Continuous.subtype_mk continuous_subtype_val (fun y => midFib_subset q b y.2)

/-- The image of the fibre cone lies in the copy of the fibre cone inside the middle set. -/
theorem midFibSetIncl_mem (q : C(X, B)) (b : B) (y : ↥(midFib q b)) :
    midFibSetIncl q b y ∈ midFibSet q b := by
  show (y : cyl q) ∈ midFib q b
  exact y.2

/-- The copy of the fibre cone inside the middle set is homeomorphic to the fibre cone. -/
def midFibSetHomeo (q : C(X, B)) (b : B) : ↥(midFibSet q b) ≃ₜ ↥(midFib q b) where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨midFibSetIncl q b y, midFibSetIncl_mem q b y⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext (by
    show ((midFibSetIncl q b y : ↥(midSet q b)) : cyl q) = (y : cyl q)
    rfl)
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)
  continuous_invFun := Continuous.subtype_mk (midFibSetIncl q b).continuous
    (fun y => midFibSetIncl_mem q b y)

/-- `H_k` of the copy of the fibre cone inside the middle set vanishes for `k > 0`. -/
theorem isZero_ratH_midFibSet (q : C(X, B)) (b : B) (k : ℕ) (hk : 0 < k) :
    IsZero (ratH (TopCat.of ↥(midFibSet q b)) k) := by
  haveI hc : ContractibleSpace ↥(midFib q b) := midFib_contractible q b
  haveI : ContractibleSpace ↥(midFibSet q b) := (midFibSetHomeo q b).contractibleSpace
  exact RatAcyclic.isZero_ratH (ratAcyclic_of_contractible _) hk

/-! ## The pair map `(M,P) → (B,{b})` is a rational homology isomorphism -/

/-- The fibre cone, included into the target copy of the base. -/
def midFibTo (q : C(X, B)) (b : B) : C(↥(midFib q b), ↥({b} : Set B)) where
  toFun y := ⟨cylRetract q y.1, y.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylRetract q).continuous.comp continuous_subtype_val) (fun y => y.2)

/-- The apex, included into the fibre cone. -/
def midFibFrom (q : C(X, B)) (b : B) : C(↥({b} : Set B), ↥(midFib q b)) where
  toFun _ := midApex q b
  continuous_toFun := continuous_const

/-- The restriction of the retraction of the mapping cylinder to the fibre cone is a homotopy
equivalence onto a point. -/
def midFibHE (q : C(X, B)) (b : B) :
    ContinuousMap.HomotopyEquiv ↥(midFib q b) ↥({b} : Set B) :=
  ContinuousMap.HomotopyEquiv.mk (midFibTo q b) (midFibFrom q b)
    (by
      have h : ((midFibFrom q b).comp (midFibTo q b)).Homotopic
          (ContinuousMap.id ↥(midFib q b)) :=
        ⟨(midFibHomotopy q b).symm⟩
      exact h)
    (by
      have h : (midFibTo q b).comp (midFibFrom q b) = ContinuousMap.id ↥({b} : Set B) :=
        ContinuousMap.ext (fun x => Subtype.ext (by
          show (↑(midFibTo q b (midFibFrom q b x)) : B) = ↑x
          rw [Set.mem_singleton_iff.mp (midFibTo q b (midFibFrom q b x)).2,
            Set.mem_singleton_iff.mp x.2]))
      exact Eq.subst (motive := fun t =>
          t.Homotopic (ContinuousMap.id ↥({b} : Set B))) h.symm
        ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id ↥({b} : Set B))⟩)

/-- **The retraction of the mapping cylinder, restricted to the pair `(M,P) → (B,{b})`, is a
rational homology isomorphism.** -/
theorem isIso_midRetr (q : C(X, B)) (b : B) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (midRetr q b) k) := by
  refine DiscPair.relChainsRPairMap_homologyMap_isIso (midFib q b) ({b} : Set B) (cylRetract q)
    (fun x hx => hx) k ?_ ?_
  · intro j
    obtain ⟨e, he⟩ := cylHomotopyEquivExplicit q
    have h : IsRatHomologyIso e.toFun := IsRatHomologyIso.of_homotopyEquiv e
    rw [he] at h
    exact h j
  · intro j
    have h : IsRatHomologyIso (midFibHE q b).toFun :=
      IsRatHomologyIso.of_homotopyEquiv (midFibHE q b)
    have hmap : (midFibHE q b).toFun
        = DiscPair.restrictPair (midFib q b) ({b} : Set B) (cylRetract q) (fun x hx => hx) :=
      ContinuousMap.ext (fun x => Subtype.ext rfl)
    rw [hmap] at h
    exact h j

/-! ## The pair map factors through the middle pair -/

/-- **The composite `(X,q⁻¹b) → (Cm,P) → (M,P) → (B,{b})` is the pair map.** -/
theorem midCollapse_comp (q : C(X, B)) (b : B) :
    midCollapse q b ≫ midPair q b ≫ midRetr q b = relPairMapRat q b := by
  have hmt : Set.MapsTo (midTo q b) (q ⁻¹' ({b} : Set B)) (midFibSet q b) := by
    intro x hx
    show cylRetract q (cylIncl q x) ∈ ({b} : Set B)
    rw [show cylRetract q (cylIncl q x) = q x from DFunLike.congr_fun (cylRetract_cylIncl q) x]
    exact hx
  have hmi : Set.MapsTo (midIncl q b) (midFibSet q b) (midFib q b) := fun x hx => hx
  have hc : Set.MapsTo (cylIncl q) (q ⁻¹' ({b} : Set B)) (midFib q b) :=
    fun x hx => hmi (hmt hx)
  have hr : Set.MapsTo (cylRetract q) (midFib q b) ({b} : Set B) := fun x hx => hx
  have hcomp : (midIncl q b).comp (midTo q b) = cylIncl q := ContinuousMap.ext (fun _ => rfl)
  have hmt' : Set.MapsTo ((midIncl q b).comp (midTo q b)) (q ⁻¹' ({b} : Set B)) (midFib q b) :=
    fun x hx => hmi (hmt hx)
  have hr' : Set.MapsTo ((cylRetract q).comp (cylIncl q)) (q ⁻¹' ({b} : Set B))
      ({b} : Set B) := fun x hx => hr (hc hx)
  have step1 : midCollapse q b ≫ midPair q b
      = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (midFib q b) (cylIncl q) hc := by
    rw [show midCollapse q b
        = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (midFibSet q b) (midTo q b)
            hmt from rfl]
    rw [show midPair q b
        = Work.Serre.relChainsRPairMap (midFibSet q b) (midFib q b) (midIncl q b)
            hmi from rfl]
    rw [CsrSharp.Tools.relChainsRPairMap_comp (midTo q b) (midIncl q b) hmt hmi
      (hg'' := hmt')]
    exact CsrSharp.Tools.relChainsRPairMap_congr hcomp hmt' hc
  have step2 : Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (midFib q b) (cylIncl q) hc
        ≫ midRetr q b
      = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) ({b} : Set B) q
          (fun _ hx => hx) := by
    rw [show midRetr q b
        = Work.Serre.relChainsRPairMap (midFib q b) ({b} : Set B) (cylRetract q) hr from rfl]
    rw [CsrSharp.Tools.relChainsRPairMap_comp (cylIncl q) (cylRetract q) hc hr (hg'' := hr')]
    exact CsrSharp.Tools.relChainsRPairMap_congr (cylRetract_cylIncl q) hr' (fun _ hx => hx)
  rw [← Category.assoc, step1, step2]
  rfl

/-! ## The pair long exact sequence: the projection to the relative homology -/

/-- **The projection `H_{n+1}(X;ℚ) → H_{n+1}(X,A;ℚ)` is an isomorphism as soon as `H_{n+1}(A)` and
`H_n(A)` vanish.**  This is the exactness chase in the long exact sequence of the pair `(X,A)`. -/
theorem isIso_homologyMap_cokernelπ (X : TopCat) (A : Set X) (n : ℕ)
    (h1 : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of A)).homology (n + 1)))
    (h2 : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of A)).homology n)) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (n + 1)) := by
  haveI hmono : Mono (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (n + 1)) :=
    ShortComplex.Exact.mono_g (Work.StemsB.relChainsR_exact₂ ℚ X A (n + 1))
      (IsZero.eq_zero_of_src h1 _)
  haveI hepi : Epi (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (n + 1)) :=
    ShortComplex.Exact.epi_f (Work.StemsB.relChainsR_exact₃ ℚ X A n)
      (IsZero.eq_zero_of_tgt h2 _)
  exact isIso_of_mono_of_epi _

/-! ## The main theorem -/

/-- The homology of `C = range (cylIncl p) ∪ (cylRetract p)⁻¹{b}` surjects onto the homology of
the mapping cylinder `cyl p` in degree `r+1`.  This is the cylinder-vocabulary form of the
homological half of `Work.Serre.fibrePairMapInject` (obtained there from
`Work.Serre.ratPairComparisonOneBoundary`, the Serre pair comparison with base connectivity `1`):
`C ≃ E/p⁻¹{b}` and `cyl p ≃ B` via `cylRetract`, and the map is the pair map modulo those weak
equivalences. -/
theorem cylMidHomologyOnto (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Surjective (Work.Serre.ratHomologyMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Set.range (Work.Serre.cylIncl p) ∪ (Work.Serre.cylRetract p ⁻¹' {b}) :
            Set (Work.Serre.cyl p))), Work.Serre.cyl p)) (r + 1)).hom := by
  -- the pair map is onto in degree `r+1`
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relPairMapRat p b) (r + 1)).hom := by
    rw [show r + 1 = 1 + r from by omega]
    exact Work.Serre.ratPairComparisonOneBoundary p hp b r hr hB (hpc b)
      (fun j hj hjr => hvan b j hj (by omega) (by omega))
  haveI hepi : CategoryTheory.Epi (HomologicalComplex.homologyMap
      (Work.Serre.relPairMapRat p b) (r + 1)) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  -- the chain level factorisation of the pair map
  have hsq : HomologicalComplex.homologyMap (midCollapse p b) (r + 1)
      ≫ HomologicalComplex.homologyMap (midPair p b) (r + 1)
      ≫ HomologicalComplex.homologyMap (midRetr p b) (r + 1)
      = HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) (r + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun φ => HomologicalComplex.homologyMap φ (r + 1)) (midCollapse_comp p b)
  haveI hcomp : CategoryTheory.Epi (HomologicalComplex.homologyMap (midCollapse p b) (r + 1)
      ≫ HomologicalComplex.homologyMap (midPair p b) (r + 1)
      ≫ HomologicalComplex.homologyMap (midRetr p b) (r + 1)) := by
    rw [hsq]; exact hepi
  haveI : CategoryTheory.Epi (HomologicalComplex.homologyMap (midPair p b) (r + 1)
      ≫ HomologicalComplex.homologyMap (midRetr p b) (r + 1)) :=
    epi_of_epi (HomologicalComplex.homologyMap (midCollapse p b) (r + 1))
      (HomologicalComplex.homologyMap (midPair p b) (r + 1)
        ≫ HomologicalComplex.homologyMap (midRetr p b) (r + 1))
  haveI hisoRetr : IsIso (HomologicalComplex.homologyMap (midRetr p b) (r + 1)) :=
    isIso_midRetr p b (r + 1)
  haveI hepiPair : CategoryTheory.Epi (HomologicalComplex.homologyMap (midPair p b) (r + 1)) := by
    rw [show HomologicalComplex.homologyMap (midPair p b) (r + 1)
        = (HomologicalComplex.homologyMap (midPair p b) (r + 1)
          ≫ HomologicalComplex.homologyMap (midRetr p b) (r + 1))
          ≫ inv (HomologicalComplex.homologyMap (midRetr p b) (r + 1)) from by simp]
    exact inferInstance
  -- the naturality square of the pair projections
  have hnat : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(midSet p b))
          (midFibSet p b))
        ≫ midPair p b
      = Work.Cohomology.chainMap ℚ (TopCat.of ↥(midSet p b)) (TopCat.of (cyl p))
          (TopCat.ofHom (midIncl p b))
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl p)) (midFib p b)) :=
    Work.Serre.cokernel_π_relChainsRPairMap (midFibSet p b) (midFib p b) (midIncl p b)
      (fun x hx => hx)
  have hnatH : HomologicalComplex.homologyMap
        (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(midSet p b))
          (midFibSet p b))) (r + 1)
        ≫ HomologicalComplex.homologyMap (midPair p b) (r + 1)
      = HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ (TopCat.of ↥(midSet p b))
          (TopCat.of (cyl p)) (TopCat.ofHom (midIncl p b))) (r + 1)
        ≫ HomologicalComplex.homologyMap
          (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl p)) (midFib p b))) (r + 1) := by
    simpa only [HomologicalComplex.homologyMap_comp]
      using congrArg (fun φ => HomologicalComplex.homologyMap φ (r + 1)) hnat
  -- the two pair projections are isomorphisms in degree `r+1`
  haveI hisoπ : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(midSet p b))
        (midFibSet p b))) (r + 1)) :=
    isIso_homologyMap_cokernelπ _ _ r (isZero_ratH_midFibSet p b (r + 1) (by omega))
      (isZero_ratH_midFibSet p b r (by omega))
  haveI hisoπ' : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl p)) (midFib p b))) (r + 1)) :=
    isIso_homologyMap_cokernelπ _ _ r (isZero_ratH_midFib p b (r + 1) (by omega))
      (isZero_ratH_midFib p b r (by omega))
  -- the absolute map is onto
  haveI hepiAbs : CategoryTheory.Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of ↥(midSet p b)) (TopCat.of (cyl p))
        (TopCat.ofHom (midIncl p b))) (r + 1)) := by
    rw [show HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ
          (TopCat.of ↥(midSet p b)) (TopCat.of (cyl p)) (TopCat.ofHom (midIncl p b))) (r + 1)
        = (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl ℚ
              (TopCat.of ↥(midSet p b)) (midFibSet p b))) (r + 1)
            ≫ HomologicalComplex.homologyMap (midPair p b) (r + 1))
          ≫ inv (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl ℚ
              (TopCat.of (cyl p)) (midFib p b))) (r + 1)) from by
      rw [hnatH, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    exact inferInstance
  have hres := (ModuleCat.epi_iff_surjective _).mp hepiAbs
  have hgoal : Function.Surjective (Work.Serre.ratHomologyMap (midIncl p b) (r + 1)).hom := by
    simpa [Work.Serre.ratHomologyMap, Work.Serre.ratChains, Work.Serre.ratH] using hres
  simpa [midIncl, midSet, midFib] using hgoal

end

end Work.Serre
