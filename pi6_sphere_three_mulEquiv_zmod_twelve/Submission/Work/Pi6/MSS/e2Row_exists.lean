import Mathlib
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.convPage
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.homotopyEquivDual
import Submission.Work.Cohomology.cupUnit
import Submission.Work.Cohomology.cupLeibniz
import Submission.Work.Cohomology.cupAssoc
import Submission.Work.Pi6.MSS.normalizedRepresentative
import Submission.Work.Pi6.MSS.normalizedCoboundary
import Submission.Work.Pi6.MSS.pageUnitSpec
import Submission.Work.Pi6.MSS.mssBotIter_mkQ
import Submission.Work.Pi6.MSS.mssMulCompat
import Submission.Work.Pi6.MSS.mssMulLeib
import Submission.Work.Pi6.MSS.mssProjMul
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The base edge (row) map of the Serre spectral sequence of a fibration

For a Serre fibration `p : E → B` with simply connected base `B`, the bottom row of the second page
of the Serre spectral sequence over a field `𝕜` is the cohomology of the base, and the corresponding
map `H^s(B;𝕜) → E_2^{s,0}` is a unital ring homomorphism whose composite with the edge map
`E_2^{s,0} → H^s(E;𝕜)` is `p^*`; moreover a class dies at the row's edge `E_{s+2}^{s,0}` exactly
when its pullback vanishes.

The concrete model of the spectral sequence used here is
`Work.Pi6.MSS.mssE 𝕜 (serreCF 𝕜 E B p)` together with the product `mssMul`, the bottom-row
projections `mssBotIter` and the unit predicate `mssPageUnit` of `Submission/Work/Pi6/MSS/AssembleCore.lean`
(see also `Submission/Work/Pi6/MSS/NOTES_MSS.md`).

The construction is the standard one: the class of a *skeletal* cocycle `α` of `B` (one vanishing
on simplices of essential dimension `< s`) is mapped to the class of its pullback `p^*α` in
`E_2^{s,0}`.  The two inputs needed for the well-definedness and the multiplicativity of this
assignment are the usual normalization facts for the cochains of a simplicial set, isolated in this
file as the child lemmas `Work.Pi6.MSS.normalizedRepresentative` and
`Work.Pi6.MSS.normalizedCoboundary`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-! ## 1. The skeletal filtration of a simplicial set -/

/-- The skeletal filtration: the cochains of degree `n` vanishing on the `n`-simplices of essential
dimension `< s`.  It is the Serre filtration of the identity map, so that the whole API of
`Work.Pi6.MSS.serreCohFilt` (stability under `δ` and closure under the cup product) applies. -/
abbrev skel (B : Type) [TopologicalSpace B] (s n : ℕ) :
    Submodule 𝕜 (Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n) :=
  coFilt 𝕜 (Work.SSS.sSingP (ContinuousMap.id B)) s n

/-- Membership in the skeletal filtration, in terms of evaluation on simplices. -/
lemma mem_skel {B : Type} [TopologicalSpace B] {s n : ℕ}
    {c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n} :
    c ∈ skel 𝕜 B s n ↔ ∀ σ : (Work.SSS.sSing B) _⦋n⦌, ess σ < s →
      Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) c σ = 0 :=
  Iff.rfl

/-- The skeletal filtration is closed under the cup product. -/
lemma cup_mem_skel {B : Type} [TopologicalSpace B] {s s' n n' : ℕ}
    {α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n}
    {β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n'}
    (hα : α ∈ skel 𝕜 B s n) (hβ : β ∈ skel 𝕜 B s' n') :
    Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α β ∈ skel 𝕜 B (s + s') (n + n') :=
  (serreCohFilt 𝕜 B B (ContinuousMap.id B)).2.2.2.2.1 s s' n n' α β hα hβ

/-- Cochains vanishing on degenerate simplices lie in the skeletal filtration: a simplex of
essential dimension `< n` is degenerate. -/
lemma mem_degenerate_of_ess_lt {X : SSet.{0}} {n : ℕ} {σ : X _⦋n⦌} (h : ess σ < n) :
    σ ∈ X.degenerate n := by
  refine (SSet.mem_degenerate_iff X σ).mpr
    ⟨(SSet.S.mk σ).toN.dim, h, (SSet.S.mk σ).toNπ, inferInstance, ?_⟩
  exact ⟨(SSet.S.mk σ).toN.simplex, SSet.S.map_toNπ_op_apply (SSet.S.mk σ)⟩

/-- A cochain vanishing on degenerate `n`-simplices lies in the `n`-th step of the skeletal
filtration. -/
lemma mem_skel_of_degenerate {B : Type} [TopologicalSpace B] {n : ℕ}
    {c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n}
    (hv : ∀ σ : (Work.SSS.sSing B) _⦋n⦌, σ ∈ SSet.degenerate (Work.SSS.sSing B) n →
      Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) c σ = 0) :
    c ∈ skel 𝕜 B n n := by
  rw [mem_skel]
  intro σ hσ
  exact hv σ (mem_degenerate_of_ess_lt hσ)

/-! ## 2. The pullback of cochains along `p` -/

/-- The pullback of a cochain of `B` along `p`, i.e. the transpose of the chain map of singular
chains.  This is the cochain-level version of `Work.Pi6.cmap 𝕜 p n`. -/
def pbC {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (n : ℕ) :
    Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n →ₗ[𝕜]
      Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n :=
  ((SSet.chainComplexMap (Work.SSS.sSingP p) (ModuleCat.of 𝕜 𝕜)).f n).hom.dualMap

/-- Evaluation of a pulled back cochain: `(p^*c)(τ) = c(p∘τ)`. -/
lemma genEval_pbC {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {n : ℕ}
    (c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n)
    (τ : (Work.SSS.sSing E) _⦋n⦌) :
    Work.Cohomology.genEval 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p n c) τ =
      Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) c ((Work.SSS.sSingP p).app (op ⦋n⦌) τ) :=
  Work.Cohomology.genEval_dualMap 𝕜 (Work.SSS.sSingP p) c τ

/-- The pullback of a cocycle is a cocycle. -/
lemma cochainDiff_pbC {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {n : ℕ}
    {c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n}
    (h : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) c = 0) :
    Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p n c) = 0 :=
  Work.Cohomology.cochainDiff_dualMap_chainComplexMap 𝕜 (Work.SSS.sSingP p) c h

/-- The pullback is compatible with the cup product. -/
lemma pbC_cup {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {n m : ℕ}
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n)
    (β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) m) :
    pbC 𝕜 p (n + m) (Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α β) =
      Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p n α) (pbC 𝕜 p m β) :=
  (Work.Cohomology.cupNatural 𝕜 (Work.SSS.sSingP p) α β).symm

/-- The pullback of a skeletal cochain is skeletal. -/
lemma pbC_mem_skel {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    {c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s} (h : c ∈ skel 𝕜 B s s) :
    pbC 𝕜 p s c ∈ coFilt 𝕜 (Work.SSS.sSingP p) s s := by
  intro τ hτ
  rw [genEval_pbC]
  exact h ((Work.SSS.sSingP p).app (op ⦋s⦌) τ) hτ

/-! ## 3. The skeletal cocycles of the base and their classes -/

/-- The skeletal cocycles of `B` in degree `s`: the `s`-cocycles vanishing on the `s`-simplices of
essential dimension `< s`. -/
def ZB (B : Type) [TopologicalSpace B] (s : ℕ) :
    Submodule 𝕜 (Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s) :=
  (Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing B) s).ker ⊓ skel 𝕜 B s s

lemma mem_ZB {B : Type} [TopologicalSpace B] {s : ℕ}
    {c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s} :
    c ∈ ZB 𝕜 B s ↔ Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) c = 0 ∧
      ∀ σ : (Work.SSS.sSing B) _⦋s⦌, ess σ < s →
        Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) c σ = 0 :=
  Iff.rfl

/-- The complex of cochains of `B` is the singular cochain complex of `B`. -/
lemma cohB_eq (B : Type) [TopologicalSpace B] (s : ℕ) :
    Work.Pi6.Coh 𝕜 B s =
      (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homology s := rfl

/-- The cohomology class of a sum of cocycles is the sum of the classes. -/
lemma cohomologyClassOf_add {B : Type} [TopologicalSpace B] {s : ℕ}
    (α β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s)
    (h : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) (α + β) = 0)
    (hα : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) α = 0)
    (hβ : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) β = 0) :
    Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) (α + β) h =
      Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) α hα +
        Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) β hβ := by
  show (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ s
      (Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B) (α + β) h) =
    (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ s
        (Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B) α hα) +
      (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ s
        (Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B) β hβ)
  rw [Work.Cohomology.cocycleOf_add 𝕜 (Work.SSS.sSing B) α β h hα hβ]
  rw [Work.Cohomology.homologyπ_add]

/-- The cohomology class of a scalar multiple of a cocycle is the scalar multiple of the class. -/
lemma cohomologyClassOf_smul {B : Type} [TopologicalSpace B] {s : ℕ} (a : 𝕜)
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s)
    (h : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) (a • α) = 0)
    (hα : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) α = 0) :
    Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) (a • α) h =
      a • Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) α hα := by
  show (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ s
      (Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B) (a • α) h) =
    a • (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ s
        (Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B) α hα)
  rw [Work.Cohomology.cocycleOf_smul 𝕜 (Work.SSS.sSing B) a α h hα]
  rw [Work.Cohomology.homologyπ_smul]

/-- The class map on the cycles of the singular cochain complex of `B`, as a linear map. -/
def cls (B : Type) [TopologicalSpace B] (s : ℕ) :
    ↥((Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing B) s).ker) →ₗ[𝕜] Work.Pi6.Coh 𝕜 B s where
  toFun c := Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) c.1 c.2
  map_add' x y :=
    cohomologyClassOf_add 𝕜 (x.1) (y.1) (x + y).2 x.2 y.2
  map_smul' a x :=
    cohomologyClassOf_smul 𝕜 a (x.1) (a • x).2 x.2

/-- The class map is the cohomology class of the underlying cocycle. -/
lemma cls_apply {B : Type} [TopologicalSpace B] (s : ℕ)
    (c : ↥((Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing B) s).ker)) :
    cls 𝕜 B s c = Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) c.1 c.2 := rfl

/-- The class map commutes with the cup product. -/
lemma cls_cup {B : Type} [TopologicalSpace B] {s s' : ℕ}
    (x : ↥((Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing B) s).ker))
    (y : ↥((Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing B) s').ker)) :
    cls 𝕜 B (s + s')
        ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) x.1 y.1,
          Work.Cohomology.cochainDiff_cup_of_cocycles 𝕜 (Work.SSS.sSing B) x.1 y.1 x.2 y.2⟩ =
      Work.Pi6.cup 𝕜 B s s' (cls 𝕜 B s x) (cls 𝕜 B s' y) := by
  rw [cls_apply, cls_apply, cls_apply]
  exact (Work.Cohomology.cupH'_apply' 𝕜 (Work.SSS.sSing B) x.1 y.1 x.2 y.2).symm

/-- The class map is compatible with the pullback along `p`. -/
lemma cls_pbC {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (c : ↥((Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing B) s).ker)) :
    (Work.Pi6.cmap 𝕜 p s).hom (cls 𝕜 B s c) =
      Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p s c.1)
        (cochainDiff_pbC 𝕜 p c.2) := by
  rw [cls_apply]
  exact Work.Cohomology.singularCohomologyMap_classOf 𝕜 (TopCat.ofHom p) c.1 c.2

/-! ## 4. The class of the pullback of a skeletal cocycle -/

/-- The pullback along `p` commutes with the coboundary. -/
lemma cochainDiff_pbC_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    {n : ℕ} (c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) n) :
    Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p n c) =
      pbC 𝕜 p (n + 1) (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B) c) := by
  have hcomm := congrArg ModuleCat.Hom.hom (HomologicalComplex.Hom.comm
    (SSet.chainComplexMap (Work.SSS.sSingP p) (ModuleCat.of 𝕜 𝕜)) (n + 1) n)
  simp only [ModuleCat.hom_comp] at hcomm
  apply LinearMap.ext
  intro x
  exact (congrArg c (LinearMap.congr_fun hcomm x)).symm

/-- A degenerate simplex has essential dimension strictly smaller than its dimension.  (The
converse is `mem_degenerate_of_ess_lt`.) -/
lemma ess_lt_of_mem_degenerate {X : SSet.{0}} {n : ℕ} {σ : X _⦋n⦌}
    (h : σ ∈ X.degenerate n) : ess σ < n := by
  obtain ⟨m, hm, f, hf, y, hy⟩ := (SSet.mem_degenerate_iff X σ).mp h
  subst hy
  have hle : SSet.S.mk (X.map f.op y) ≤ SSet.S.mk y := SSet.S.mk_map_le y f
  have hN : (SSet.S.mk (X.map f.op y)).toN ≤ (SSet.S.mk y).toN := by
    rw [SSet.N.le_iff, SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
    exact hle
  have h1 : ess (X.map f.op y) ≤ ess y := SSet.N.dim_le_of_le hN
  have h2 : ess y ≤ m := SSet.S.dim_toN_le (SSet.S.mk y)
  omega

/-- The incoming differential of the Serre filtration is the coboundary of the cochain complex. -/
lemma dPrev_eq_cochainDiff {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (k : ℕ) :
    (serreCF 𝕜 E B p).dPrev (k + 1) = Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing E) k := by
  show ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).d k (k + 1)).hom = _
  rw [Work.Cohomology.SSetCochainComplex_d]
  rfl

/-- The class of the pullback of a skeletal cocycle, in `E_2^{s,0} = pEraw 2 s s`. -/
def Rb {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (s : ℕ) :
    ↥(ZB 𝕜 B s) →ₗ[𝕜] pEraw 𝕜 (serreCF 𝕜 E B p) 2 s s :=
  (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s s).comap
      (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s).subtype)).comp
    (LinearMap.codRestrict (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s)
      ((pbC 𝕜 p s).comp (ZB 𝕜 B s).subtype)
      (fun x => by
        have hzero : (serreCF 𝕜 E B p).d s (pbC 𝕜 p s x.1) = 0 := by
          simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
            CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
          exact cochainDiff_pbC 𝕜 p x.2.1
        refine ⟨pbC_mem_skel 𝕜 p x.2.2, ?_⟩
        show (serreCF 𝕜 E B p).d s (pbC 𝕜 p s x.1) ∈ (serreCF 𝕜 E B p).F (s + 2) (s + 1)
        rw [hzero, show s + 2 = (s + 1) + 1 from rfl, (serreCF 𝕜 E B p).F_top (s + 1)]
        exact Submodule.zero_mem _))

/-- The value of `Rb` on a skeletal cocycle whose pullback lies in the denominator vanishes. -/
lemma Rb_eq_zero_of_mem {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s : ℕ) (x : ↥(ZB 𝕜 B s))
    (h : pbC 𝕜 p s x.1 ∈ pDen 𝕜 (serreCF 𝕜 E B p) 2 s s) : Rb 𝕜 p s x = 0 := by
  rw [Rb]
  exact (pd_mkQ_eq_zero_iff 𝕜 (serreCF 𝕜 E B p) 2 s s _).mpr h

/-- The class map restricted to the skeletal cocycles of `B`. -/
def clsB (B : Type) [TopologicalSpace B] (s : ℕ) :
    ↥(ZB 𝕜 B s) →ₗ[𝕜] Work.Pi6.Coh 𝕜 B s :=
  (cls 𝕜 B s).comp (Submodule.inclusion
    (inf_le_left : ZB 𝕜 B s ≤ (Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing B) s).ker))

lemma clsB_apply {B : Type} [TopologicalSpace B] (s : ℕ) (x : ↥(ZB 𝕜 B s)) :
    clsB 𝕜 B s x = Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) x.1 x.2.1 := rfl

/-- Every cohomology class of `B` has a skeletal cocycle representative, hence the restricted class
map is surjective. -/
lemma clsB_range_top (B : Type) [TopologicalSpace B] (s : ℕ) :
    (clsB 𝕜 B s).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  obtain ⟨α, hα, hv, hcl⟩ := normalizedRepresentative 𝕜 (Work.SSS.sSing B) s y
  refine ⟨⟨α, ⟨hα, fun σ hσ => hv σ (mem_degenerate_of_ess_lt hσ)⟩⟩, ?_⟩
  rw [clsB_apply]
  exact hcl

/-- A skeletal cocycle of vanishing class is the coboundary of a skeletal cochain, hence `Rb`
kills the kernel of the restricted class map. -/
lemma ker_clsB_le_ker_Rb {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s : ℕ) :
    LinearMap.ker (clsB 𝕜 B s) ≤ LinearMap.ker (Rb 𝕜 p s) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    haveI := CochainComplex.isIso_homologyπ₀
      (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B))
    have hinj : Function.Injective
        (((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ 0)).hom :=
      (ConcreteCategory.bijective_of_isIso
        ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ 0)).1
    have hz : Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B) x.1 x.2.1 = 0 := by
      apply hinj
      rw [map_zero]
      exact hx
    have hx0 : x.1 = 0 := by
      have h := Work.Cohomology.iCycles_cocycleOf 𝕜 (Work.SSS.sSing B) x.1 x.2.1
      rw [hz, map_zero] at h
      exact h.symm
    refine Rb_eq_zero_of_mem 𝕜 p 0 x ?_
    rw [hx0, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    obtain ⟨hmemd, hmemv⟩ := x.2
    have hdeg : Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B) x.1 hmemd = 0 := hx
    obtain ⟨β, hβd, hβv⟩ := normalizedCoboundary 𝕜 (Work.SSS.sSing B) k x.1 hmemd
      (fun σ hσ => hmemv σ (ess_lt_of_mem_degenerate hσ)) hdeg
    have hβsk : β ∈ skel 𝕜 B k k := mem_skel_of_degenerate 𝕜 hβv
    have hβE : pbC 𝕜 p k β ∈ coFilt 𝕜 (Work.SSS.sSingP p) k k := pbC_mem_skel 𝕜 p hβsk
    have hdx : pbC 𝕜 p (k + 1) x.1 =
        Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p k β) := by
      rw [← hβd]
      exact (cochainDiff_pbC_eq 𝕜 p β).symm
    have hxF : pbC 𝕜 p (k + 1) x.1 ∈ (serreCF 𝕜 E B p).F (k + 1) (k + 1) :=
      pbC_mem_skel 𝕜 p x.2.2
    have hd : (serreCF 𝕜 E B p).d k (pbC 𝕜 p k β) = pbC 𝕜 p (k + 1) x.1 := by
      simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
        CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
      exact hdx.symm
    refine Rb_eq_zero_of_mem 𝕜 p (k + 1) x ?_
    unfold pDen
    refine Submodule.mem_sup_right (S := pZ 𝕜 (serreCF 𝕜 E B p) 1 (k + 1 + 1) (k + 1))
      (T := pB 𝕜 (serreCF 𝕜 E B p) 2 (k + 1) (k + 1)) ?_
    exact (pd_mem_pB_succ_iff (𝕜 := 𝕜) (W := serreCF 𝕜 E B p) (r := 1) (s' := k)
      (n' := k)).mpr ⟨hxF, pbC 𝕜 p k β, hβE, hd⟩

/-! ## 5. The base row map `H^s(B;𝕜) → E_2^{s,0}` -/

/-! ## 5. The base row map `H^s(B;𝕜) → E_2^{s,0}` -/

/-- A linear section of the restricted class map `ZB_s → H^s(B;𝕜)` (which is surjective by the
normalization theorem). -/
noncomputable def rowSec (B : Type) [TopologicalSpace B] (s : ℕ)
    (hrange : (clsB 𝕜 B s).range = ⊤) : Work.Pi6.Coh 𝕜 B s →ₗ[𝕜] ↥(ZB 𝕜 B s) :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (clsB 𝕜 B s) hrange)

/-- The defining property of the section. -/
lemma rowSec_spec (B : Type) [TopologicalSpace B] (s : ℕ)
    (hrange : (clsB 𝕜 B s).range = ⊤) :
    (clsB 𝕜 B s).comp (rowSec 𝕜 B s hrange) = LinearMap.id :=
  Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective (clsB 𝕜 B s) hrange)

/-- The section is a section. -/
lemma clsB_rowSec (B : Type) [TopologicalSpace B] (s : ℕ)
    (hrange : (clsB 𝕜 B s).range = ⊤) (b : Work.Pi6.Coh 𝕜 B s) :
    clsB 𝕜 B s (rowSec 𝕜 B s hrange b) = b := by
  have h := LinearMap.congr_fun (rowSec_spec 𝕜 B s hrange) b
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- **The base row map** `H^s(B;𝕜) → E_2^{s,0}`, on the concrete page `pEraw`. -/
noncomputable def rowCore {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (s : ℕ) (hker : LinearMap.ker (clsB 𝕜 B s) ≤ LinearMap.ker (Rb 𝕜 p s))
    (hrange : (clsB 𝕜 B s).range = ⊤) :
    Work.Pi6.Coh 𝕜 B s →ₗ[𝕜] pEraw 𝕜 (serreCF 𝕜 E B p) 2 s s :=
  (Rb 𝕜 p s).comp (rowSec 𝕜 B s hrange)

/-- The computation rule for the base row map on skeletal cocycles. -/
lemma rowCore_clsB {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (s : ℕ)
    (hker : LinearMap.ker (clsB 𝕜 B s) ≤ LinearMap.ker (Rb 𝕜 p s))
    (hrange : (clsB 𝕜 B s).range = ⊤) (x : ↥(ZB 𝕜 B s)) :
    rowCore 𝕜 p s hker hrange (clsB 𝕜 B s x) = Rb 𝕜 p s x := by
  show Rb 𝕜 p s (rowSec 𝕜 B s hrange (clsB 𝕜 B s x)) = Rb 𝕜 p s x
  have hmem : rowSec 𝕜 B s hrange (clsB 𝕜 B s x) - x ∈ LinearMap.ker (clsB 𝕜 B s) := by
    rw [LinearMap.mem_ker]
    have h1 : clsB 𝕜 B s (rowSec 𝕜 B s hrange (clsB 𝕜 B s x)) = clsB 𝕜 B s x :=
      clsB_rowSec 𝕜 B s hrange (clsB 𝕜 B s x)
    have h2 : clsB 𝕜 B s (rowSec 𝕜 B s hrange (clsB 𝕜 B s x)) - clsB 𝕜 B s x = 0 :=
      sub_eq_zero.mpr h1
    rw [← map_sub] at h2
    exact h2
  rw [← sub_eq_zero, ← map_sub]
  exact hker hmem

/-- **The base row map**, with values in the bidegree-indexed page `mssE 𝕜 (serreCF 𝕜 E B p) 2 (s,0)`
(which is `pEraw 𝕜 (serreCF 𝕜 E B p) 2 s s` by definition). -/
noncomputable def rowMap {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (s : ℕ) (hker : LinearMap.ker (clsB 𝕜 B s) ≤ LinearMap.ker (Rb 𝕜 p s))
    (hrange : (clsB 𝕜 B s).range = ⊤) :
    Work.Pi6.Coh 𝕜 B s →ₗ[𝕜] mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) :=
  rowCore 𝕜 p s hker hrange

/-- The computation rule for the base row map on skeletal cocycles. -/
lemma rowMap_clsB {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (s : ℕ)
    (hker : LinearMap.ker (clsB 𝕜 B s) ≤ LinearMap.ker (Rb 𝕜 p s))
    (hrange : (clsB 𝕜 B s).range = ⊤) (x : ↥(ZB 𝕜 B s)) :
    rowMap 𝕜 p s hker hrange (clsB 𝕜 B s x) = Rb 𝕜 p s x :=
  rowCore_clsB 𝕜 p s hker hrange x

/-- The class of the unit cochain of `B`, as a skeletal cocycle in degree `0`. -/
lemma clsB_unit (B : Type) [TopologicalSpace B] :
    clsB 𝕜 B 0 ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing B),
      ⟨Work.Cohomology.cochainDiff_unitCochain 𝕜 (Work.SSS.sSing B),
        fun σ hσ => absurd hσ (by omega)⟩⟩ = Work.Pi6.one 𝕜 B := rfl

/-- The pullback of the unit cochain is the unit cochain. -/
lemma pbC_unit {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    pbC 𝕜 p 0 (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing B)) =
      Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E) := by
  apply Work.Cohomology.genEval_ext (R := 𝕜) (X := Work.SSS.sSing E)
  intro σ
  rw [genEval_pbC, Work.Cohomology.genEval_unitCochain, Work.Cohomology.genEval_unitCochain]

/-! ## 6. The unit of the page -/

/-- The unit cochain of `E` lies in `Z_2^{0,0}`. -/
lemma unitCochain_mem_pZ0 {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E) ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [(serreCF 𝕜 E B p).F_zero 0]
    exact Submodule.mem_top
  · have hzero : (serreCF 𝕜 E B p).d 0 (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E)) = 0 := by
      simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
        CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
      exact Work.Cohomology.cochainDiff_unitCochain 𝕜 (Work.SSS.sSing E)
    show (serreCF 𝕜 E B p).d 0 (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E)) ∈
      (serreCF 𝕜 E B p).F (0 + 2) (0 + 1)
    rw [hzero]
    rw [show (0 : ℕ) + 2 = (0 + 1) + 1 from rfl, (serreCF 𝕜 E B p).F_top (0 + 1)]
    exact Submodule.zero_mem _

/-- The image of the class of the unit cochain of `B` under `Rb` is the class of the unit cochain
of `E`. -/
lemma Rb_unit {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (h : Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing B) ∈ ZB 𝕜 B 0) :
    Rb 𝕜 p 0 ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing B), h⟩ =
      Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 0).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 0).subtype)
        ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E), unitCochain_mem_pZ0 𝕜 p⟩ := by
  rw [Rb]
  apply congrArg (fun t => Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 0).comap
    (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 0).subtype) t)
  exact Subtype.ext (pbC_unit 𝕜 p)

/-- **The row map is unital**: the class of the unit of `H^*(B;𝕜)` is the unit of the page. -/
theorem rowMap_pageUnit {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    mssPageUnit 𝕜 E B p
      (rowMap 𝕜 p 0 (ker_clsB_le_ker_Rb 𝕜 p 0) (clsB_range_top 𝕜 B 0) (Work.Pi6.one 𝕜 B)) := by
  have hB : Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing B) ∈ ZB 𝕜 B 0 :=
    ⟨Work.Cohomology.cochainDiff_unitCochain 𝕜 (Work.SSS.sSing B),
      fun σ hσ => absurd hσ (by omega)⟩
  have hrow : rowMap 𝕜 p 0 (ker_clsB_le_ker_Rb 𝕜 p 0) (clsB_range_top 𝕜 B 0)
      (Work.Pi6.one 𝕜 B) =
      Rb 𝕜 p 0 ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing B), hB⟩ := by
    rw [← clsB_unit 𝕜 B]
    exact rowMap_clsB 𝕜 p 0 _ _ _
  rw [hrow, Rb_unit 𝕜 p hB]
  exact pageUnitSpec 𝕜 E B p (unitCochain_mem_pZ0 𝕜 p)

/-! ## 7. The cycles of the last page of the bottom row -/

/-- For `r ≥ 2` and total degree `s`, the cycles `Z_r^s` of the bottom row are the `s`-cycles lying
in `F^s`: the condition `dx ∈ F^{s+r}C^{s+1} = 0` is automatic. -/
lemma pZ_eq_ker (W : CohFilt 𝕜) (r s : ℕ) (hr : 2 ≤ r) :
    pZ 𝕜 W r s s = W.F s s ⊓ (W.d s).ker := by
  rw [pZ]
  have h : W.F (s + r) (s + 1) = ⊥ := conv_F_eq_bot W (by omega)
  rw [h, Submodule.comap_bot]

/-- The denominator of `E_{s+2}^{s,0}`: the `s`-cycles in `F^s` which are coboundaries. -/
lemma pDen_last (W : CohFilt 𝕜) (s : ℕ) :
    pDen 𝕜 W (s + 2) s s = W.F s s ⊓ (W.dPrev s).range := by
  rw [pDen, show s + 2 - 1 = s + 1 from by omega]
  have hZ : pZ 𝕜 W (s + 1) (s + 1) s = ⊥ := by
    rw [pZ, W.F_top s, bot_inf_eq]
  have hB : pB 𝕜 W (s + 2) s s = W.F s s ⊓ (W.dPrev s).range := by
    rw [pB, show s + 1 - (s + 2) = 0 from by omega, W.F_zero (s - 1), Submodule.map_top]
  rw [hZ, hB, bot_sup_eq]

/-- The value of `Rb` through an explicit representative of the cycle `p^*x`. -/
lemma Rb_eq_mkQ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (s : ℕ)
    (x : ↥(ZB 𝕜 B s)) (h : pbC 𝕜 p s x.1 ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 s s) :
    Rb 𝕜 p s x = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s s).comap
      (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s).subtype) ⟨pbC 𝕜 p s x.1, h⟩ := by
  rw [Rb]
  exact congrArg (fun t => Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s s).comap
    (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s).subtype) t) (Subtype.ext rfl)

/-! ## 8. The bottom row of the second page -/

/-- In positive degrees, a cocycle of the total space has vanishing class iff it is a coboundary
(in the Serre filtration's terms). -/
lemma class_zero_iff_mem_dPrev {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (k : ℕ) (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (k + 1))
    (hx : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x = 0) :
    Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) x hx = 0 ↔
      x ∈ ((serreCF 𝕜 E B p).dPrev (k + 1)).range := by
  have hd : (serreCF 𝕜 E B p).dPrev (k + 1) =
      Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing E) k := by
    show ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).d k (k + 1)).hom = _
    rw [Work.Cohomology.SSetCochainComplex_d]
    rfl
  constructor
  · intro h0
    obtain ⟨β, hβ⟩ := Work.Pi6.SQM.SIG.classZeroCoboundary_R 𝕜 (Work.SSS.sSing E) k x hx h0
    exact ⟨β, by rw [hd]; exact hβ⟩
  · rintro ⟨β, hβ⟩
    have hβ' : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) β = x := by
      have h := hβ
      rw [hd] at h
      exact h
    refine Work.Cohomology.homologyπ_eq_zero_of_d 𝕜 (Work.SSS.sSing E) (k + 1) k _ β ?_
    rw [Work.Cohomology.iCycles_cocycleOf]
    show x = ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).d k (k + 1)).hom β
    rw [Work.Cohomology.SSetCochainComplex_d]
    exact hβ'.symm

/-- The class of the zero cocycle vanishes. -/
lemma cohomologyClassOf_zero {B : Type} [TopologicalSpace B] {s : ℕ}
    (h : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing B)
      (0 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s) = 0) :
    Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing B)
      (0 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s) h = 0 := by
  show (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing B)).homologyπ s
    (Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B) 0 h) = 0
  have h' : Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing B)
      (0 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s) h = 0 := by
    have hsm := Work.Cohomology.cocycleOf_smul 𝕜 (Work.SSS.sSing B) (0 : 𝕜)
      (0 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s) (by simpa using h) h
    simpa using hsm
  rw [h', map_zero]

/-- In degree `0` the class of a cocycle of the total space vanishes iff the cocycle is zero. -/
lemma class_zero_iff_eq_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) 0)
    (hx : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x = 0) :
    Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) x hx = 0 ↔ x = 0 := by
  constructor
  · intro h0
    haveI := CochainComplex.isIso_homologyπ₀
      (Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E))
    have hinj : Function.Injective
        (((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).homologyπ 0)).hom :=
      (ConcreteCategory.bijective_of_isIso
        ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).homologyπ 0)).1
    have hz : Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing E) x hx = 0 := by
      apply hinj
      rw [map_zero]
      exact h0
    have h := Work.Cohomology.iCycles_cocycleOf 𝕜 (Work.SSS.sSing E) x hx
    rw [hz, map_zero] at h
    exact h.symm
  · intro h0
    subst h0
    exact cohomologyClassOf_zero 𝕜 hx

/-- **The bottom row disappears exactly when the pullback does.** -/
theorem rowMap_botIter {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hbot : ∀ (s : ℕ) (x : (serreCF 𝕜 E B p).C.X s)
      (hx : ∀ r : ℕ, 2 ≤ r → x ∈ pZ 𝕜 (serreCF 𝕜 E B p) r s s),
      mssBotIter 𝕜 E B p s s
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s s).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s).subtype) ⟨x, hx 2 (by norm_num)⟩) =
        Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (s + 2) s s).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) (s + 2) s s).subtype) ⟨x, hx (s + 2) (by omega)⟩)
    (s : ℕ) (b : Work.Pi6.Coh 𝕜 B s) :
    mssBotIter 𝕜 E B p s s
        (rowMap 𝕜 p s (ker_clsB_le_ker_Rb 𝕜 p s) (clsB_range_top 𝕜 B s) b) = 0 ↔
      (Work.Pi6.cmap 𝕜 p s).hom b = 0 := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    set α := rowSec 𝕜 B 0 (clsB_range_top 𝕜 B 0) b with hα
    have hcls : clsB 𝕜 B 0 α = b := clsB_rowSec 𝕜 B 0 (clsB_range_top 𝕜 B 0) b
    have hrow : rowMap 𝕜 p 0 (ker_clsB_le_ker_Rb 𝕜 p 0) (clsB_range_top 𝕜 B 0) b =
        Rb 𝕜 p 0 α := by
      rw [← hcls]
      exact rowMap_clsB 𝕜 p 0 _ _ α
    set x : (serreCF 𝕜 E B p).C.X 0 := pbC 𝕜 p 0 α.1 with hxdef
    have hxF : x ∈ (serreCF 𝕜 E B p).F 0 0 := pbC_mem_skel 𝕜 p α.2.2
    have hxcyc : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x = 0 :=
      cochainDiff_pbC 𝕜 p α.2.1
    have hxd : (serreCF 𝕜 E B p).d 0 x = 0 := by
      simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
        CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
      exact hxcyc
    have hxZ : ∀ r : ℕ, 2 ≤ r → x ∈ pZ 𝕜 (serreCF 𝕜 E B p) r 0 0 := by
      intro r hr
      rw [pZ_eq_ker 𝕜 (serreCF 𝕜 E B p) r 0 hr]
      exact ⟨hxF, hxd⟩
    have hp : pDen 𝕜 (serreCF 𝕜 E B p) 2 0 0 = ⊥ := by
      rw [pDen_last 𝕜 (serreCF 𝕜 E B p) 0, (serreCF 𝕜 E B p).F_zero 0,
        pd_dPrev_zero (𝕜 := 𝕜) (W := serreCF 𝕜 E B p), LinearMap.range_zero, top_inf_eq]
    have hstep : (mssBotIter 𝕜 E B p 0 0)
        (rowMap 𝕜 p 0 (ker_clsB_le_ker_Rb 𝕜 p 0) (clsB_range_top 𝕜 B 0) b) =
        Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 0).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 0).subtype)
          ⟨x, hxZ 2 (by norm_num)⟩ := by
      rw [hrow]
      exact Rb_eq_mkQ 𝕜 p 0 α (hxZ 2 (by norm_num))
    have hL : (mssBotIter 𝕜 E B p 0 0)
        (rowMap 𝕜 p 0 (ker_clsB_le_ker_Rb 𝕜 p 0) (clsB_range_top 𝕜 B 0) b) = 0 ↔
        x = 0 := by
      rw [hstep]
      change ((Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 0).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 0).subtype)
          ⟨x, hxZ 2 (by norm_num)⟩ :
          ↥(pEraw 𝕜 (serreCF 𝕜 E B p) (0 + 2) 0 0)) = 0) ↔ x = 0
      rw [(pd_mkQ_eq_zero_iff 𝕜 (serreCF 𝕜 E B p) 2 0 0 ⟨x, hxZ 2 (by norm_num)⟩), hp]
      exact Submodule.mem_bot 𝕜
    have hR : (Work.Pi6.cmap 𝕜 p 0).hom b = 0 ↔ x = 0 := by
      have h1 : cls 𝕜 B 0 ⟨α.1, α.2.1⟩ = b := hcls
      have h2 : (Work.Pi6.cmap 𝕜 p 0).hom b =
          Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p 0 α.1)
            (cochainDiff_pbC 𝕜 p α.2.1) := by
        rw [← h1]
        exact cls_pbC 𝕜 p ⟨α.1, α.2.1⟩
      rw [h2]
      exact class_zero_iff_eq_zero 𝕜 p x hxcyc
    exact hL.trans hR.symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    set α := rowSec 𝕜 B (k + 1) (clsB_range_top 𝕜 B (k + 1)) b with hα
    have hcls : clsB 𝕜 B (k + 1) α = b :=
      clsB_rowSec 𝕜 B (k + 1) (clsB_range_top 𝕜 B (k + 1)) b
    have hrow : rowMap 𝕜 p (k + 1) (ker_clsB_le_ker_Rb 𝕜 p (k + 1))
        (clsB_range_top 𝕜 B (k + 1)) b = Rb 𝕜 p (k + 1) α := by
      rw [← hcls]
      exact rowMap_clsB 𝕜 p (k + 1) _ _ α
    set x : (serreCF 𝕜 E B p).C.X (k + 1) := pbC 𝕜 p (k + 1) α.1 with hxdef
    have hxF : x ∈ (serreCF 𝕜 E B p).F (k + 1) (k + 1) := pbC_mem_skel 𝕜 p α.2.2
    have hxcyc : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x = 0 :=
      cochainDiff_pbC 𝕜 p α.2.1
    have hxd : (serreCF 𝕜 E B p).d (k + 1) x = 0 := by
      simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
        CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
      exact hxcyc
    have hxZ : ∀ r : ℕ, 2 ≤ r → x ∈ pZ 𝕜 (serreCF 𝕜 E B p) r (k + 1) (k + 1) := by
      intro r hr
      rw [pZ_eq_ker 𝕜 (serreCF 𝕜 E B p) r (k + 1) hr]
      exact ⟨hxF, hxd⟩
    have hstep : (mssBotIter 𝕜 E B p (k + 1) (k + 1))
        (rowMap 𝕜 p (k + 1) (ker_clsB_le_ker_Rb 𝕜 p (k + 1))
          (clsB_range_top 𝕜 B (k + 1)) b) =
        Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) ((k + 1) + 2) (k + 1) (k + 1)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) ((k + 1) + 2) (k + 1) (k + 1)).subtype)
          ⟨x, hxZ ((k + 1) + 2) (by omega)⟩ := by
      rw [hrow]
      exact hbot (k + 1) x hxZ
    have hL : (mssBotIter 𝕜 E B p (k + 1) (k + 1))
        (rowMap 𝕜 p (k + 1) (ker_clsB_le_ker_Rb 𝕜 p (k + 1))
          (clsB_range_top 𝕜 B (k + 1)) b) = 0 ↔
        x ∈ ((serreCF 𝕜 E B p).dPrev (k + 1)).range := by
      rw [hstep]
      change ((Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) ((k + 1) + 2) (k + 1) (k + 1)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) ((k + 1) + 2) (k + 1) (k + 1)).subtype)
          ⟨x, hxZ ((k + 1) + 2) (by omega)⟩ :
          ↥(pEraw 𝕜 (serreCF 𝕜 E B p) (((k + 1) + 2)) (k + 1) (k + 1))) = 0) ↔
        x ∈ ((serreCF 𝕜 E B p).dPrev (k + 1)).range
      rw [(pd_mkQ_eq_zero_iff 𝕜 (serreCF 𝕜 E B p) ((k + 1) + 2) (k + 1) (k + 1)
          ⟨x, hxZ ((k + 1) + 2) (by omega)⟩), pDen_last]
      exact ⟨fun h => h.2, fun h => ⟨hxF, h⟩⟩
    have hR : (Work.Pi6.cmap 𝕜 p (k + 1)).hom b = 0 ↔
        x ∈ ((serreCF 𝕜 E B p).dPrev (k + 1)).range := by
      have h1 : cls 𝕜 B (k + 1) ⟨α.1, α.2.1⟩ = b := hcls
      have h2 : (Work.Pi6.cmap 𝕜 p (k + 1)).hom b =
          Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p (k + 1) α.1)
            (cochainDiff_pbC 𝕜 p α.2.1) := by
        rw [← h1]
        exact cls_pbC 𝕜 p ⟨α.1, α.2.1⟩
      rw [h2]
      exact class_zero_iff_mem_dPrev 𝕜 p k x hxcyc
    exact hL.trans hR.symm

/-- **Multiplicativity of `Rb` on skeletal cocycles.** -/
lemma Rb_cup {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (s s' : ℕ) (α : ↥(ZB 𝕜 B s)) (β : ↥(ZB 𝕜 B s'))
    (hZB : Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1 ∈ ZB 𝕜 B (s + s')) :
    Rb 𝕜 p (s + s') ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1, hZB⟩ =
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((s' : ℤ), (0 : ℤ))
        (((s + s' : ℕ) : ℤ), (0 : ℤ)) (by ext <;> simp)
        (Rb 𝕜 p s α) (Rb 𝕜 p s' β) := by
  set x : (serreCF 𝕜 E B p).C.X s := pbC 𝕜 p s α.1 with hxdef
  set y : (serreCF 𝕜 E B p).C.X s' := pbC 𝕜 p s' β.1 with hydef
  have hxF : x ∈ (serreCF 𝕜 E B p).F s s := pbC_mem_skel 𝕜 p α.2.2
  have hyF : y ∈ (serreCF 𝕜 E B p).F s' s' := pbC_mem_skel 𝕜 p β.2.2
  have hxd : (serreCF 𝕜 E B p).d s x = 0 := by
    simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
    exact cochainDiff_pbC 𝕜 p α.2.1
  have hyd : (serreCF 𝕜 E B p).d s' y = 0 := by
    simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
    exact cochainDiff_pbC 𝕜 p β.2.1
  have hxZ : x ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 s s := by
    rw [pZ_eq_ker 𝕜 (serreCF 𝕜 E B p) 2 s le_rfl]
    exact ⟨hxF, hxd⟩
  have hyZ : y ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 s' s' := by
    rw [pZ_eq_ker 𝕜 (serreCF 𝕜 E B p) 2 s' le_rfl]
    exact ⟨hyF, hyd⟩
  have hxyF : Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
      ∈ (serreCF 𝕜 E B p).F (s + s') (s + s') :=
    (serreCohFilt 𝕜 E B p).2.2.2.2.1 s s' s s' x y hxF hyF
  have hxyd : (serreCF 𝕜 E B p).d (s + s') (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y)
      = 0 := by
    simp only [CohFilt.d, serreCF_C, Work.Cohomology.SSetCochainComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply]
    exact Work.Cohomology.cochainDiff_cup_of_cocycles 𝕜 (Work.SSS.sSing E) x y
      (by simpa only [hxdef] using cochainDiff_pbC 𝕜 p α.2.1)
      (by simpa only [hydef] using cochainDiff_pbC 𝕜 p β.2.1)
  have hxyZ : Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
      ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s') := by
    rw [pZ_eq_ker 𝕜 (serreCF 𝕜 E B p) 2 (s + s') le_rfl]
    exact ⟨hxyF, hxyd⟩
  -- the left hand side
  have hL : Rb 𝕜 p (s + s') ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1, hZB⟩ =
      Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s')).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s')).subtype)
        ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y, hxyZ⟩ := by
    have hmem : pbC 𝕜 p (s + s') (Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1)
        ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s') := by
      rw [pbC_cup 𝕜 p α.1 β.1]
      exact hxyZ
    rw [Rb_eq_mkQ 𝕜 p (s + s') _ hmem]
    apply congrArg (fun t => Submodule.mkQ _ t)
    apply Subtype.ext
    show pbC 𝕜 p (s + s') (Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1)
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
    rw [pbC_cup 𝕜 p α.1 β.1]
  -- the right hand side
  have ha : Enn ((s : ℤ), (0 : ℤ)) := Enn_pair s 0
  have hb : Enn ((s' : ℤ), (0 : ℤ)) := Enn_pair s' 0
  have hc : ((s : ℤ), (0 : ℤ)) + ((s' : ℤ), (0 : ℤ)) = (((s + s' : ℕ) : ℤ), (0 : ℤ)) := by
    ext <;> simp
  have hR : mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((s' : ℤ), (0 : ℤ))
        (((s + s' : ℕ) : ℤ), (0 : ℤ)) hc
        (Rb 𝕜 p s α) (Rb 𝕜 p s' β) =
      Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s')).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s')).subtype)
        ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y, hxyZ⟩ := by
    have e1 : Rb 𝕜 p s α = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s s).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s).subtype) ⟨x, hxZ⟩ := Rb_eq_mkQ 𝕜 p s α hxZ
    have e2 : Rb 𝕜 p s' β = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s' s').comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 2 s' s').subtype) ⟨y, hyZ⟩ := Rb_eq_mkQ 𝕜 p s' β hyZ
    rw [e1, e2]
    rw [mssMul_apply_enn (a := ((s : ℤ), (0 : ℤ))) (b := ((s' : ℤ), (0 : ℤ)))
      (c := (((s + s' : ℕ) : ℤ), (0 : ℤ))) (ha := ha) (hb := hb) (h := hc)]
    rw [pEcast_hom_apply_comp]
    set HE := (EI_add ha hb).trans (congrArg EI hc) with hHE
    set KE := (EN_add ha hb).trans (congrArg EN hc) with hKE
    have hxZ' : x ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ))) :=
      hxZ
    have hyZ' : y ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 (EI ((s' : ℤ), (0 : ℤ))) (EN ((s' : ℤ), (0 : ℤ))) :=
      hyZ
    change (ConcreteCategory.hom (pEcast 𝕜 (serreCF 𝕜 E B p) 2 HE KE).hom)
        (pd_mul 2 (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ)))
          (EI ((s' : ℤ), (0 : ℤ))) (EN ((s' : ℤ), (0 : ℤ)))
          (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 (EI ((s : ℤ), (0 : ℤ)))
            (EN ((s : ℤ), (0 : ℤ)))).comap (pZ 𝕜 (serreCF 𝕜 E B p) 2 (EI ((s : ℤ), (0 : ℤ)))
            (EN ((s : ℤ), (0 : ℤ)))).subtype) ⟨x, hxZ'⟩)
          (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 (EI ((s' : ℤ), (0 : ℤ)))
            (EN ((s' : ℤ), (0 : ℤ)))).comap (pZ 𝕜 (serreCF 𝕜 E B p) 2 (EI ((s' : ℤ), (0 : ℤ)))
            (EN ((s' : ℤ), (0 : ℤ)))).subtype) ⟨y, hyZ'⟩)) =
      Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s')).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (s + s')).subtype)
        ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y, hxyZ⟩
    rw [pd_mul_nat 2 (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ)))
      (EI ((s' : ℤ), (0 : ℤ))) (EN ((s' : ℤ), (0 : ℤ))) ⟨x, hxZ'⟩ ⟨y, hyZ'⟩]
    rw [pd_pEcast_mkQ' (h := HE) (h' := KE)]
    apply pd_mkQ_congr
    show (serreCF 𝕜 E B p).xcast KE (pd_mulZ 2 (EI ((s : ℤ), (0 : ℤ)))
        (EN ((s : ℤ), (0 : ℤ))) (EI ((s' : ℤ), (0 : ℤ))) (EN ((s' : ℤ), (0 : ℤ)))
        ⟨x, hxZ'⟩ ⟨y, hyZ'⟩).1 = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
    rw [pd_mulZ_val]
    rw [show (serreCF 𝕜 E B p).mul (EN ((s : ℤ), (0 : ℤ))) (EN ((s' : ℤ), (0 : ℤ))) x y
        = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y from serreCup_apply 𝕜 p _ _ _ _]
    rw [pageUnit_xcast_congr (h := KE)
      (h' := (rfl : EN ((s : ℤ), (0 : ℤ)) + EN ((s' : ℤ), (0 : ℤ))
        = EN ((s : ℤ), (0 : ℤ)) + EN ((s' : ℤ), (0 : ℤ)))), CohFilt.xcast_rfl]
    rfl
  rw [hL, hR]

/-- **Multiplicativity of the base row map.** -/
theorem rowMap_mul_aux (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B))
    (hker : ∀ s : ℕ, LinearMap.ker (clsB 𝕜 B s) ≤ LinearMap.ker (Rb 𝕜 p s))
    (hrange : ∀ s : ℕ, (clsB 𝕜 B s).range = ⊤)
    (s s' : ℕ) (b : Work.Pi6.Coh 𝕜 B s) (b' : Work.Pi6.Coh 𝕜 B s') :
    rowMap 𝕜 p (s + s') (hker (s + s')) (hrange (s + s')) (Work.Pi6.cup 𝕜 B s s' b b') =
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((s' : ℤ), (0 : ℤ))
        (((s + s' : ℕ) : ℤ), (0 : ℤ)) (by ext <;> simp)
        (rowMap 𝕜 p s (hker s) (hrange s) b)
        (rowMap 𝕜 p s' (hker s') (hrange s') b') := by
  -- the chosen skeletal representatives
  set α := rowSec 𝕜 B s (hrange s) b with hα
  set β := rowSec 𝕜 B s' (hrange s') b' with hβ
  have hclsα : clsB 𝕜 B s α = b := clsB_rowSec 𝕜 B s (hrange s) b
  have hclsβ : clsB 𝕜 B s' β = b' := clsB_rowSec 𝕜 B s' (hrange s') b'
  have hrowα : rowMap 𝕜 p s (hker s) (hrange s) b = Rb 𝕜 p s α := by
    rw [← hclsα]
    exact rowMap_clsB 𝕜 p s _ _ α
  have hrowβ : rowMap 𝕜 p s' (hker s') (hrange s') b' = Rb 𝕜 p s' β := by
    rw [← hclsβ]
    exact rowMap_clsB 𝕜 p s' _ _ β
  -- the cup of two skeletal cocycles is a skeletal cocycle
  have hZB : Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1 ∈ ZB 𝕜 B (s + s') :=
    ⟨Work.Cohomology.cochainDiff_cup_of_cocycles 𝕜 (Work.SSS.sSing B) α.1 β.1
        α.2.1 β.2.1,
      cup_mem_skel 𝕜 α.2.2 β.2.2⟩
  -- the class of that cup is the cup of the classes
  have hclscup : clsB 𝕜 B (s + s') ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1, hZB⟩
      = Work.Pi6.cup 𝕜 B s s' b b' := by
    have h1 := cls_cup 𝕜 (B := B) (s := s) (s' := s') ⟨α.1, α.2.1⟩ ⟨β.1, β.2.1⟩
    have h2 : cls 𝕜 B (s + s') ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1,
        hZB.1⟩ = clsB 𝕜 B (s + s') ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1,
        hZB⟩ := rfl
    have h3 : cls 𝕜 B s ⟨α.1, α.2.1⟩ = b := hclsα
    have h4 : cls 𝕜 B s' ⟨β.1, β.2.1⟩ = b' := hclsβ
    rw [← h2, h1, h3, h4]
  rw [hrowα, hrowβ, ← hclscup,
    rowMap_clsB 𝕜 p (s + s') (hker (s + s')) (hrange (s + s'))
      ⟨Work.Cohomology.cup 𝕜 (Work.SSS.sSing B) α.1 β.1, hZB⟩]
  exact Rb_cup 𝕜 p s s' α β hZB

/-- **The base-edge (row) map of the Serre spectral sequence of a Serre fibration.**

For a Serre fibration `p : E → B` over a simply connected base and any field `𝕜`, the bottom row of
the second page `E_2^{s,0}` of the Serre spectral sequence receives a unital ring map from the
cohomology of the base, whose composite with the edge map `E_2^{s,0} → H^s(E;𝕜)` is `p^*`; a class
dies at the row's edge `E_{s+2}^{s,0}` exactly when its pullback vanishes. -/
theorem e2Row_exists (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    ∃ row : ∀ s : ℕ, s ≤ N → Work.Pi6.Coh 𝕜 B s →ₗ[𝕜]
        Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)),
      Work.Pi6.MSS.mssPageUnit 𝕜 E B p (row 0 (Nat.zero_le N) (Work.Pi6.one 𝕜 B)) ∧
      (∀ (s s' : ℕ) (hs : s ≤ N) (hs' : s' ≤ N) (hss : s + s' ≤ N)
        (b : Work.Pi6.Coh 𝕜 B s) (b' : Work.Pi6.Coh 𝕜 B s'),
        row (s + s') hss (Work.Pi6.cup 𝕜 B s s' b b') =
          Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((s' : ℤ), (0 : ℤ))
            (((s + s' : ℕ) : ℤ), (0 : ℤ)) (by ext <;> simp)
            (row s hs b) (row s' hs' b')) ∧
      (∀ (s : ℕ) (hs : s ≤ N) (b : Work.Pi6.Coh 𝕜 B s),
        Work.Pi6.MSS.mssBotIter 𝕜 E B p s s (row s hs b) = 0 ↔ (Work.Pi6.cmap 𝕜 p s).hom b = 0) := by
  refine ⟨fun s _ => Work.Pi6.MSS.rowMap 𝕜 p s
    (Work.Pi6.MSS.ker_clsB_le_ker_Rb 𝕜 p s) (Work.Pi6.MSS.clsB_range_top 𝕜 B s), ?_, ?_, ?_⟩
  · exact Work.Pi6.MSS.rowMap_pageUnit 𝕜 p
  · intro s s' hs hs' hss b b'
    exact Work.Pi6.MSS.rowMap_mul_aux 𝕜 p (fun t => Work.Pi6.MSS.ker_clsB_le_ker_Rb 𝕜 p t)
      (fun t => Work.Pi6.MSS.clsB_range_top 𝕜 B t) s s' b b'
  · intro s hs b
    exact Work.Pi6.MSS.rowMap_botIter 𝕜 p
      (fun t x hx => Work.Pi6.MSS.mssBotIter_mkQ 𝕜 p t x hx) s b

end

end Work.Pi6.MSS
