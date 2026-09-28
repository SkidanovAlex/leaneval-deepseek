import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.DiscPair.cylPairDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.DiscPair.cylPair_concentrated
import Submission.Work.Serre.DiscPair.ratH_of_contractible_base
import Submission.Work.Serre.DiscPair.thomCylAt_of_contractible
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.CsrSharp.relChainsRHomeomorphCompat
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Thom.relCohMap_comp
import Submission.Work.Serre.DiscPair.relCoh_cylW_line
import Submission.Work.Serre.DiscPair.isZero_relR_fibre_of_weakContractible
import Submission.Work.Serre.DiscPair.isZero_relCoh_fibreBottom

/-!
# The fibrewise restriction of the relative Thom class, over a weakly contractible base

Let `q : C(X,B)` be a Serre fibration whose base `B` is path connected and *weakly* contractible
all of whose fibres are path connected and rationally `S^r` (concentrated in degree `r`, `≅ ℚ`,
through degree `N`).  Then the restriction map on relative cohomology

`H^{r+1}(cyl q, range (cylIncl q); ℚ) ⟶ H^{r+1}((cylRetract q)⁻¹{w}, · ∩ range (cylIncl q); ℚ)`

is an isomorphism for every point `w : B` — the relative Thom class of the mapping cylinder is
detected on every fibre.

## Strategy

Write `A = range (cylIncl q) ⊆ cyl q` (the bottom copy), `P = (cylRetract q)⁻¹{w} ⊆ cyl q` (the
cone on the fibre over `w`) and `W = A ∩ P` (as a subset of `P`).  The target map `φ` factors as

* `s : H^{r+1}(cyl q, A) → H^{r+1}(cyl q, A∩P)` — shrink the second member of the pair, the first
  map of the triple sequence for `A∩P ⊆ A ⊆ cyl q`. It is injective because the third term of that
  triple is `H^r(A, A∩P) ≅ H^r(X, q⁻¹{w}) = 0` (the Serre comparison), and hence an isomorphism
  because both sides are `ℚ`-lines;
* `ψ : H^{r+1}(cyl q, A∩P) → H^{r+1}(P, A∩P)` — the extension lemma
  `isIso_relCohMap_incl_of_isZero`, whose hypothesis is the vanishing of `H^*(cyl q, P)` in degrees
  `r+1` and `r+2`, available because both `cyl q` (homotopy equivalent to the weakly contractible
  `B`) and `P` (the cone on the fibre) are rationally acyclic.

The two relative sets `A∩P` and `A` inside `P` differ only by the (automatic) conjunct
`x ∈ P`, so at the level of the pair `(P, ·)` the maps are related by the `eqToIso` transport of
that set equality.  Hence `φ` is a composite of isomorphisms.
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- The fibre cone of the mapping cylinder over `w`, as a subspace of `cyl q`. -/
abbrev cylP {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) : Set (Work.Serre.cyl q) :=
  (Work.Serre.cylRetract q) ⁻¹' ({w} : Set B)

/-- The bottom copy `X` inside the mapping cylinder. -/
abbrev cylA {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) : Set (Work.Serre.cyl q) :=
  Set.range (Work.Serre.cylIncl q)

/-- The bottom copy of the fibre over `w`, inside the fibre cone. -/
abbrev cylW {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) : Set ↥(cylP q w) :=
  {x | (x : Work.Serre.cyl q) ∈ cylA q}

/-- The same set, written as `A ∩ P` (the form the extension lemma produces). -/
abbrev cylW' {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) : Set ↥(cylP q w) :=
  {x | (x : Work.Serre.cyl q) ∈ cylA q ∩ cylP q w}

/-! ## Two congruence lemmas for the pullback of relative cohomology -/

/-- **Set-congruence for the pullback of relative cohomology**: replacing the source relative set
by an equal set changes the pullback only by the transport isomorphism of the set equality. -/
theorem relCohMap_set_eq {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X] (f : C(Y, X))
    {B₁ B₂ : Set Y} (hB : B₁ = B₂) (A : Set X)
    (hf₁ : ∀ y ∈ B₁, f y ∈ A) (hf₂ : ∀ y ∈ B₂, f y ∈ A) (R : Type) [CommRing R] (n : ℕ) :
    Work.Thom.relCohMap f B₁ A hf₁ R n
      ≫ (eqToIso (congrArg (fun S => Work.Thom.RelCoh R n Y S) hB)).hom
      = Work.Thom.relCohMap f B₂ A hf₂ R n := by
  subst hB
  rw [CategoryTheory.eqToIso_refl, CategoryTheory.Iso.refl_hom, Category.comp_id]

/-- **The pullback of relative cohomology only depends on the underlying continuous map.** -/
theorem relCohMap_congr_map {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X]
    {f f' : C(Y, X)} (h : f = f') (A : Set Y) (B : Set X)
    (hf : ∀ y ∈ A, f y ∈ B) (hf' : ∀ y ∈ A, f' y ∈ B) (R : Type) [CommRing R] (n : ℕ) :
    Work.Thom.relCohMap f A B hf R n = Work.Thom.relCohMap f' A B hf' R n := by
  subst h
  exact Work.Thom.relCohMap_hcongrA f A B hf hf' R n

/-! ## The vanishing of the relative cohomology of `(cyl q, P)` -/

/-- **The pair `(cyl q, P)` has vanishing relative cohomology in degrees `r+1` and `r+2`** when
`cyl q` is rationally acyclic: the connecting map `H^m(P) → H^{m+1}(cyl q, P)` is an isomorphism
for `m = r, r+1` (the absolute cohomology of `cyl q` vanishes in positive degrees), and `P` is
rationally acyclic, being the cone on a fibre. -/
theorem isZero_relCoh_cylP {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) (r : ℕ) (hr : 1 ≤ r)
    (hAcyc : Work.Serre.RatAcyclic (Work.Serre.cyl q)) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (cylP q w)) ∧
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 2) (Work.Serre.cyl q) (cylP q w)) := by
  haveI hP : ContractibleSpace ↥(cylP q w) := Work.Serre.DiscPair.cylRetractPreimageContractible q w
  have hPacyc : Work.Serre.RatAcyclic ↥(cylP q w) := Work.Serre.ratAcyclic_of_contractible _
  have hQ : ∀ n : ℕ, 0 < n → IsZero (Work.Thom.Coh ℚ n (Work.Serre.cyl q)) :=
    fun n hn => Work.Serre.isZero_coh_of_ratAcyclic hAcyc hn
  have hP0 : ∀ n : ℕ, 0 < n → IsZero (Work.Thom.Coh ℚ n ↥(cylP q w)) :=
    fun n hn => Work.Serre.isZero_coh_of_ratAcyclic hPacyc hn
  constructor
  · haveI : IsIso (Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) (cylP q w) r) :=
      Work.Serre.pairδ_isIso_rat _ _ r (hQ (r + 1) (by omega)) (hQ r (by omega))
    exact IsZero.of_iso (hP0 r (by omega))
      (asIso (Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) (cylP q w) r)).symm
  · haveI : IsIso (Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) (cylP q w) (r + 1)) :=
      Work.Serre.pairδ_isIso_rat _ _ (r + 1) (hQ (r + 2) (by omega)) (hQ (r + 1) (by omega))
    exact IsZero.of_iso (hP0 (r + 1) (by omega))
      (asIso (Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q)) (cylP q w) (r + 1))).symm

/-! ## The extension isomorphism `ψ` -/

/-- **The restriction of relative cohomology to the fibre cone**, in the form produced by the
extension lemma `isIso_relCohMap_incl_of_isZero` (the relative set inside `P` is written as
`A ∩ P`). -/
theorem isIso_relCohMap_cylP {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) (r : ℕ) (hr : 1 ≤ r)
    (hAcyc : Work.Serre.RatAcyclic (Work.Serre.cyl q)) :
    IsIso (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(cylP q w), Work.Serre.cyl q))
      (cylW' q w) (cylA q ∩ cylP q w) (fun x hx => hx) ℚ (r + 1)) := by
  obtain ⟨h1, h2⟩ := isZero_relCoh_cylP q w r hr hAcyc
  exact Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero (TopCat.of (Work.Serre.cyl q))
    (cylA q ∩ cylP q w) (cylP q w) Set.inter_subset_right (r + 1) h1 h2

/-! ## The shrink map `s` -/

/-- **The shrink map `H^{r+1}(cyl q, A) → H^{r+1}(cyl q, A ∩ P)` is an isomorphism.**

It is the first map of the triple sequence of `A ∩ P ⊆ A ⊆ cyl q`; it is injective because the
third term of that sequence, `H^r(A, A ∩ P)`, vanishes (`isZero_relCoh_fibreBottom` and the
Serre comparison at `w`), and both of its ends are `ℚ`-lines. -/
theorem isIso_relCohMap_shrink {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) (r : ℕ) (hr : 1 ≤ r)
    (hsrc : Nonempty (Work.Thom.RelCoh ℚ (r+1) (Work.Serre.cyl q) (cylA q) ≅ ModuleCat.of ℚ ℚ))
    (hψ : IsIso (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(cylP q w), Work.Serre.cyl q))
      (cylW' q w) (cylA q ∩ cylP q w) (fun x hx => hx) ℚ (r + 1)))
    (htgt : Nonempty (Work.Thom.RelCoh ℚ (r+1) ↥(cylP q w) (cylW q w) ≅ ModuleCat.of ℚ ℚ))
    (ht3 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ r ↥(cylA q)
      {x : ↥(cylA q) | (x : Work.Serre.cyl q) ∈ cylA q ∩ cylP q w})) :
    IsIso (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
      (cylA q ∩ cylP q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)) := by
  classical
  obtain ⟨e₁⟩ := hsrc
  haveI hmono : Mono (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
      (cylA q ∩ cylP q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)) := by
    have hS := Work.Serre.DiscPair.qTripleShort_shortExact (TopCat.of (Work.Serre.cyl q))
      (cylA q ∩ cylP q w) (cylA q) Set.inter_subset_left
    have hex := hS.homology_exact₁ r (r + 1) (by simp [ComplexShape.up])
    exact (ShortComplex.exact_iff_mono _ (CategoryTheory.Limits.IsZero.eq_zero_of_src ht3 _)).mp hex
  have hinj : Function.Injective (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
      (cylA q ∩ cylP q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hmid : Nonempty (Work.Thom.RelCoh ℚ (r+1) (Work.Serre.cyl q) (cylA q ∩ cylP q w)
      ≅ ModuleCat.of ℚ ℚ) := by
    have hW : cylW' q w = cylW q w := by
      ext x
      constructor
      · intro hx
        exact Set.mem_of_mem_inter_left hx
      · intro hx
        exact Set.mem_inter hx x.2
    haveI := hψ
    exact ⟨(asIso (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cylP q w), Work.Serre.cyl q))
        (cylW' q w) (cylA q ∩ cylP q w) (fun x hx => hx) ℚ (r + 1)))
      ≪≫ eqToIso (congrArg (fun S => Work.Thom.RelCoh ℚ (r+1) ↥(cylP q w) S) hW)
      ≪≫ (Classical.choice htgt)⟩
  obtain ⟨e₂⟩ := hmid
  refine isIso_ofHom_of_linearEquiv_rat e₁.toLinearEquiv e₂.toLinearEquiv
    (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
      (cylA q ∩ cylP q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)).hom ?_
  intro h0
  have h1 : ∀ x, (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
      (cylA q ∩ cylP q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)).hom x = 0 := by
    intro x
    rw [h0]
    rfl
  have hv : e₁.toLinearEquiv.symm (1 : ℚ) ≠ 0 := by
    intro h
    have h2 := e₁.toLinearEquiv.apply_symm_apply (1 : ℚ)
    rw [h, map_zero] at h2
    exact one_ne_zero h2.symm
  exact hv (hinj (by rw [h1 (e₁.toLinearEquiv.symm 1), map_zero]))

/-! ## The factorization of the target map -/

/-- **The shrink map followed by the extension map is the restriction to the pair `(P, W')`.** -/
theorem shrink_comp_eq {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) (r : ℕ) :
    (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q)) (cylA q ∩ cylP q w) (cylA q)
        (fun x hx => hx.1) ℚ (r + 1))
      ≫ (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(cylP q w), Work.Serre.cyl q))
          (cylW' q w) (cylA q ∩ cylP q w) (fun x hx => hx) ℚ (r + 1))
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(cylP q w), Work.Serre.cyl q))
          (cylW' q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1) := by
  rw [Work.Thom.relCohMap_compA (cylW' q w) (cylA q ∩ cylP q w) (cylA q)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(cylP q w), Work.Serre.cyl q))
    (ContinuousMap.id (Work.Serre.cyl q)) (fun x hx => hx) (fun x hx => hx.1) (fun x hx => hx.1)]
  exact relCohMap_congr_map (by ext x; rfl) (cylW' q w) (cylA q) _ _ ℚ (r + 1)

/-! ## The two endpoint lines -/

/-- **The source of the target map is a `ℚ`-line**: the relative cohomology of the pair
`(cyl q, A)` in degree `r+1` is `ℚ`, by `cylPair_concentrated`. -/
theorem relCoh_cylA_line {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hq : Work.StemsB.IsSerreFibration q) (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Thom.RelCoh ℚ (r+1) (Work.Serre.cyl q) (cylA q) ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨hXvan, hXgen⟩ := Work.Serre.DiscPair.ratH_of_contractible_base q b₀ r N hr hrN hq hB hBc
    hX (hpc b₀) (fun t ht htr htN => hvan b₀ t ht htr htN) (hgen b₀)
  exact (Work.Serre.DiscPair.cylPair_concentrated q r N hr
    (ratAcyclic_of_weaklyContractible_base b₀ hB hBc) hX hXvan hXgen).2

/-! ## The main theorem -/

theorem fibreRestriction_of_contractible {B : Type} [TopologicalSpace B] {X : Type}
    [TopologicalSpace X] (q : C(X, B)) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hq : Work.StemsB.IsSerreFibration q) (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (w : B) :
    CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' {w}), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {w}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)) := by
  classical
  -- acyclicity of the mapping cylinder
  have hAcyc : Work.Serre.RatAcyclic (Work.Serre.cyl q) := by
    obtain ⟨he⟩ := Work.Serre.cylHomotopyEquiv q
    exact Work.Serre.ratAcyclic_of_homotopyEquiv he (ratAcyclic_of_weaklyContractible_base b₀ hB hBc)
  -- the source line
  have hsrc := relCoh_cylA_line q b₀ r N hr hrN hq hB hBc hX hpc hvan hgen
  -- the target line (delegated)
  have htgt : Nonempty (Work.Thom.RelCoh ℚ (r+1) ↥(cylP q w) (cylW q w)
      ≅ ModuleCat.of ℚ ℚ) := by
    exact relCoh_cylW_line q w r hr hpc hgen
  -- the vanishing at degree `r` (delegated, two steps)
  have ht3 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ r ↥(cylA q)
      {x : ↥(cylA q) | (x : Work.Serre.cyl q) ∈ cylA q ∩ cylP q w}) := by
    refine isZero_relCoh_fibreBottom q w r ?_
    exact isZero_relR_fibre_of_weakContractible q b₀ r N hr hrN hq hB hBc hX hpc hvan hgen w r
      (by omega) (by omega)
  -- the two isomorphisms
  have hψ : IsIso (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(cylP q w), Work.Serre.cyl q))
      (cylW' q w) (cylA q ∩ cylP q w) (fun x hx => hx) ℚ (r + 1)) :=
    isIso_relCohMap_cylP q w r hr hAcyc
  have hs : IsIso (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
      (cylA q ∩ cylP q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)) :=
    isIso_relCohMap_shrink q w r hr hsrc hψ htgt ht3
  -- the set equality and the transport isomorphism
  have hW : cylW' q w = cylW q w := by
    ext x
    constructor
    · intro hx
      exact Set.mem_of_mem_inter_left hx
    · intro hx
      exact Set.mem_inter hx x.2
  let e : Work.Thom.RelCoh ℚ (r+1) ↥(cylP q w) (cylW' q w)
      ≅ Work.Thom.RelCoh ℚ (r+1) ↥(cylP q w) (cylW q w) :=
    eqToIso (congrArg (fun S => Work.Thom.RelCoh ℚ (r+1) ↥(cylP q w) S) hW)
  have hset : Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(cylP q w), Work.Serre.cyl q)) (cylW' q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)
      ≫ e.hom
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(cylP q w), Work.Serre.cyl q)) (cylW q w) (cylA q) (fun x hx => hx) ℚ (r + 1) :=
    relCohMap_set_eq _ hW (cylA q) (fun x hx => hx.1) (fun x hx => hx) ℚ (r + 1)
  have hEq : (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
        (cylA q ∩ cylP q w) (cylA q) (fun x hx => hx.1) ℚ (r + 1)
      ≫ Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cylP q w), Work.Serre.cyl q)) (cylW' q w) (cylA q ∩ cylP q w)
          (fun x hx => hx) ℚ (r + 1)) ≫ e.hom
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cylP q w), Work.Serre.cyl q)) (cylW q w) (cylA q) (fun x hx => hx) ℚ (r + 1) := by
    rw [shrink_comp_eq q w r, hset]
  rw [← hEq]
  infer_instance

end

end Work.Serre.DiscPair
