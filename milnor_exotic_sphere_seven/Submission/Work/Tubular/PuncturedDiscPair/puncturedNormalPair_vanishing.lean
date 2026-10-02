import Mathlib
import Submission.Work.Tubular.TubeClass.ComplPointMan8All
import Submission.Work.Tubular.subsingleton_homology_normalTotal_compl_zero
import Submission.Work.Tubular.TubeClass.Core
import Submission.Work.Tubular.onePoint_compl_zero
import Submission.Work.Tubular.OnePointCompl
import Submission.Work.Tubular.onePoint_homology_relChains
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.onePoint_cokernel_pi_compl_point_bijective
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.PuncturedDiscPair.sphOver_punctured_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The punctured normal pair has vanishing `H_{8+k}`

For a closed oriented `8`-manifold `V` embedded in `ℝ^{8+k}` (`E : EmbeddingData V (8+k)`), the
normal total space `ν = NormalTotal E` carries the subspaces

* `P = ν ∖ {x₀}` — the total space with the point `x₀ = 0_{v₀}` of the zero section removed, and
* `Q = {p ∈ P | ‖p‖ ≠ 0}` — the further removal of the zero section (`‖·‖` the fibrewise norm),

and `Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing` states `H_{8+k}(P, Q) = 0`.

## The proof

* `awayPt = {q : P | q.proj = v₀}` is the fibre over `v₀` with `x₀` removed; it is closed in `P`,
  and each of its points has non-zero norm, so `closure awayPt ⊆ interior Q`.  Hence the pair
  `(P, Q)` is excised to the pair `(awaySet, awayRel)` over the complement `awaySet = awayPtᶜ`
  (`Work.Cohomology.excision`, `closure_awayPt_subset_interior_punctRel`);
* the long exact sequence of `(awaySet, awayRel)` (`relChains`,
  `homologyMap_cokernel_pi_bijective_of_isZero`) reduces `H_{8+k}(awaySet, awayRel)` to the
  vanishing of `H_{8+k}(awaySet)` together with that of `H_{8+k}` and `H_{7+k}` of `awayRel`
  (`isZero_relChains_of_isZero`);
* `awaySet` (the open disc bundle over `V ∖ {v₀}`) deformation retracts onto `V ∖ {v₀}`
  (`awayHomotopyEquiv`), so `H_{8+k}(awaySet) = 0`
  (`Work.Tubular.TubeClass.isZero_homology_compl_point_man8_all`);
* `awayRel` (the punctured disc bundle over `V ∖ {v₀}`) is homotopy equivalent to the unit sphere
  bundle over `V ∖ {v₀}` by the radial projection (`awayRelSphHomotopyEquiv`); that sphere bundle
  is identified with the gluing-data sphere bundle `Work.SphHomology.sphOver ν ({v₀}ᶜ)`
  (`sphNormalHomeo`, built from `exists_eucNormalBundle`), whose homology in degrees `≥ 7+k`
  vanishes by `sphOver_punctured_vanishing`.

Nothing here needs the local-degree/Thom-class input: the vanishing of the homology of the
*punctured* (`V ∖ {v₀}`-based) sphere bundle in degrees `≥ 7+k` is precisely what the
"clopen-meets-every-component" argument of `isZero_homology_compl_of_clopen_meets` gives, and the
`{v₀}`-fibre that the radial projection discards is where the top class of the *full* sphere bundle
lives.

## The `k = 0` case

For `k = 0` the normal bundle has rank `0`, so `Q = ∅` and `ν ∖ {x₀} ≅ V ∖ {v₀}`, and the
statement reduces to `H_8(V ∖ {v₀}) = 0`
(`Work.Tubular.TubeClass.isZero_homology_compl_point_man8_all`).

## The companion pair `(ν⁺∖{x₀}, A)`

The pair `(ν⁺∖{x₀}, A)`, `A = onePointNonzero E ∩ (ν⁺∖{x₀})`, is also treated here: `A` is
homeomorphic to `onePointNonzero E` (hence contractible), so `H_n(A)` vanishes in positive degrees
(`isZero_homology_punctComplRel`), and consequently the relative group of `(ν⁺∖{x₀}, A)` vanishes
as soon as `H_{8+k}(ν⁺∖{x₀})` does (`isZero_relChains_punctComplRel`) — the `A`-half of
`Work.Tubular.TubeClass.punctComplTopHomologyVanishing_of_isZero_pair`.
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular.PuncturedDiscPair

noncomputable section

/-- The point of the zero section at which the pair is punctured. -/
abbrev basePt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Work.Tubular.NormalTotal E :=
  ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩

/-- The **punctured normal total space** `ν ∖ {x₀}`. -/
abbrev Punct {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) : Type _ :=
  {p : Work.Tubular.NormalTotal E // p ≠ basePt E v₀}

/-- The **punctured normal pair**: the complement of the zero section inside `ν ∖ {x₀}`. -/
def PunctRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Set (Punct E v₀) :=
  {q | Work.Tubular.normalNorm E q.1 ≠ 0}

/-- The relative set `A` of the pair `(ν⁺∖{x₀}, A)`. -/
def punctComplRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Set (Work.Tubular.PunctCompl E v₀) :=
  {q | (q : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E}

/-- `x₀` does not lie in `A = onePointNonzero E`. -/
theorem zeroSectionPunctPt_notMem_onePointNonzero {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Work.Tubular.zeroSectionPunctPt E v₀ ∉ Work.Tubular.onePointNonzero E := by
  intro h
  rcases (Work.Tubular.mem_onePointNonzero.mp h) with h' | ⟨q, hq, hqeq⟩
  · exact OnePoint.coe_ne_infty _ h'
  · have hq' : q = ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩ := by
      have := OnePoint.coe_injective hqeq
      simpa [Work.Tubular.zeroSectionPunctPt, Work.Tubular.zeroSectionOnePoint] using this
    rw [hq'] at hq
    simp at hq

/-- `A`, viewed as a subspace of `ν⁺∖{x₀}`, is `A` itself. -/
def punctComplRelHomeo {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    ↥(punctComplRel E v₀) ≃ₜ ↥(Work.Tubular.onePointNonzero E) where
  toFun q := ⟨q.1.1, q.2⟩
  invFun p := ⟨⟨p.1, fun h => zeroSectionPunctPt_notMem_onePointNonzero E v₀ (h ▸ p.2)⟩, p.2⟩
  left_inv q := Subtype.ext (Subtype.ext rfl)
  right_inv p := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- `A` is contractible, so its positive-degree homology vanishes. -/
theorem isZero_homology_punctComplRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) (n : ℕ)
    (hn : 0 < n) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(punctComplRel E v₀))).homology n) :=
  Work.Cohomology.isZero_homology_of_homotopyEquiv
    (punctComplRelHomeo E v₀).toHomotopyEquiv n
    (Work.Tubular.isZero_homology_onePointNonzero E n hn)

/-- **The relative group of the pair `(ν⁺∖{x₀}, A)` vanishes in degree `8+k` as soon as
`H_{8+k}(ν⁺∖{x₀})` does** (`A` is contractible, so `H_{8+k}(ν⁺∖{x₀}) ≅ H_{8+k}(ν⁺∖{x₀}, A)`). -/
theorem isZero_relChains_punctComplRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (hA : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Tubular.PunctCompl E v₀))).homology (8 + k))) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.PunctCompl E v₀))
      (punctComplRel E v₀)).homology (8 + k)) := by
  have h1 := isZero_homology_punctComplRel E v₀ (8 + k) (by omega)
  have h2 := isZero_homology_punctComplRel E v₀ ((8 + k) - 1) (by omega)
  have hbij := Work.Cohomology.homologyMap_cokernel_pi_bijective_of_isZero
    (TopCat.of (Work.Tubular.PunctCompl E v₀)) (punctComplRel E v₀) (8 + k) (by omega) h1 h2
  haveI : IsIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains (TopCat.of (Work.Tubular.PunctCompl E v₀))
        (punctComplRel E v₀))) (8 + k)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsZero.of_iso hA (asIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of (Work.Tubular.PunctCompl E v₀))
      (punctComplRel E v₀))) (8 + k))).symm

/-! ## The Euclidean normal bundle with its projection -/

/-- **The normal bundle of `E` as a Euclidean gluing-data bundle, with the identification preserving
both the fibrewise norm and the projection.**  This is
`Work.Tubular.exists_euclidean_normalBundle` with the (definitional, but otherwise unavailable)
statement that the homeomorphism to `NormalTotal E` is fibrewise. -/
theorem exists_euclidean_normalBundle_proj {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∃ (ι : Type) (nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι)
      (_ : Work.Thom.IsEuclidean nu)
      (phi : VectorBundleCore.TotalSpace nu ≃ₜ Work.Tubular.NormalTotal E),
      (∀ p, Work.Thom.fibreNorm nu p = Work.Tubular.normalNorm E (phi p)) ∧
      (∀ p, (phi p).proj = VectorBundleCore.proj nu p) := by
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  refine ⟨Work.ThomBordism.PontryaginThom.CoverIdx V k, Work.Tubular.normalBundle E ND,
    Work.Tubular.isEuclidean_normalBundle E ND, Work.Tubular.eucNormalHomeomorph E ND, ?_, ?_⟩
  · intro p
    rw [Work.Tubular.eucNormalHomeomorph_apply]
    exact Work.Tubular.fibreNorm_eq_normalNorm E ND p
  · intro p
    rfl

/-! ## The pair `(ν ∖ {x₀}, ν ∖ 0)` reduced to a neighbourhood of `V ∖ {v₀}`

Write `P = Punct E v₀ = ν ∖ {x₀}` and `Q = PunctRel E v₀ = ν ∖ 0`.  The excision set is
`awayPt = {q : P | q.proj = v₀}` (the fibre over `v₀` with `x₀` removed, closed in `P` and
contained in `Q`), whose complement is the open set `awaySet = {q : P | q.proj ≠ v₀}`.  The pair
`(awaySet, awayRel)`, `awayRel = awaySet ∩ Q`, is the "punctured disc bundle over `V ∖ {v₀}`"
appearing in `puncturedNormalPair_vanishing`; both its homology in degrees `≥ 7 + k` and the
homology of `awaySet` in degree `8 + k` vanish (see `isZero_homology_awayRel` and
`isZero_homology_awaySet`). -/

/-- The points of `Punct E v₀` lying over `v₀`. -/
abbrev awayPt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Set (Punct E v₀) :=
  {q | q.1.proj = v₀}

/-- The points of `Punct E v₀` lying away from `v₀`. -/
abbrev awaySet {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Set (Punct E v₀) :=
  {q | q.1.proj ≠ v₀}

/-- The relative set of the pair `(awaySet, awaySet ∩ PunctRel)`. -/
abbrev awayRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Set ↥(awaySet E v₀) :=
  {q | (q : Punct E v₀) ∈ PunctRel E v₀}

theorem awaySet_eq_compl {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    awaySet E v₀ = (awayPt E v₀)ᶜ := rfl

theorem isClosed_awayPt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    IsClosed (awayPt E v₀) := by
  refine isClosed_singleton.preimage ?_
  have h1 : Continuous (fun q : Punct E v₀ => (q.1 : Work.Tubular.NormalTotal E)) :=
    continuous_subtype_val
  exact (Work.Tubular.NormalTotal.continuous_proj E).comp h1

theorem isOpen_punctRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    IsOpen (PunctRel E v₀) := by
  have h : PunctRel E v₀ = (fun q : Punct E v₀ => Work.Tubular.normalNorm E q.1) ⁻¹'
      {x : ℝ | x ≠ 0} := rfl
  rw [h]
  exact isOpen_ne.preimage ((Work.Tubular.continuous_normalNorm E).comp continuous_subtype_val)

theorem basePt_eq_of_proj_eq_of_norm_eq_zero {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {v₀ : V.pt}
    {p : Work.Tubular.NormalTotal E} (hp : p.proj = v₀) (h : Work.Tubular.normalNorm E p = 0) :
    p = basePt E v₀ := by
  have hv : p.1.2 = 0 := norm_eq_zero.mp (by simpa [Work.Tubular.normalNorm] using h)
  refine Subtype.ext (Prod.ext ?_ hv)
  simpa [Work.Tubular.NormalTotal.proj] using hp

theorem awayPt_subset_punctRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    awayPt E v₀ ⊆ PunctRel E v₀ := by
  intro q hq
  rw [PunctRel, Set.mem_setOf_eq]
  intro h0
  exact q.2 (basePt_eq_of_proj_eq_of_norm_eq_zero hq h0)

/-- **The excision hypothesis for the pair `(P, Q)`.** -/
theorem closure_awayPt_subset_interior_punctRel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    closure (awayPt E v₀) ⊆ interior (PunctRel E v₀) := by
  rw [(isClosed_awayPt E v₀).closure_eq, (isOpen_punctRel E v₀).interior_eq]
  exact awayPt_subset_punctRel E v₀

/-! ## The long exact sequence of a pair, in the form used here -/

/-- **The relative group of a pair vanishes as soon as the absolute group of the ambient space and
the two neighbouring groups of the subspace do.**  This is the long exact sequence of the pair:
`H_n(X, A) ≅ H_n(X)` because `H_n(A) = H_{n-1}(A) = 0`. -/
theorem isZero_relChains_of_isZero (X : TopCat) (A : Set X) (n : ℕ) (hn : 1 ≤ n)
    (hA : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥A)).homology n))
    (hA' : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥A)).homology (n - 1)))
    (hX : IsZero ((Work.Cohomology.singularChains ℤ X).homology n)) :
    IsZero ((Work.Cohomology.relChains X A).homology n) := by
  have hbij := Work.Cohomology.homologyMap_cokernel_pi_bijective_of_isZero X A n hn hA hA'
  haveI : IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsZero.of_iso hX (asIso (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) n)).symm

/-! ## The open disc bundle over `V ∖ {v₀}` is homotopy equivalent to `V ∖ {v₀}` -/

section AwaySet

attribute [local fun_prop] Work.Tubular.NormalTotal.continuous_proj
  Work.Tubular.NormalTotal.continuous_vec

/-- The zero vector over the base point of a point of `awaySet`. -/
def zeroVec {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (q : ↥(awaySet E v₀)) : Work.Tubular.NormalTotal E :=
  ⟨(q.1.1.proj, 0), Work.Tubular.zero_mem_normalSpace E q.1.1.proj⟩

theorem zeroVec_ne_basePt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (q : ↥(awaySet E v₀)) : zeroVec E v₀ q ≠ basePt E v₀ := by
  intro h
  exact q.2 (by
    have h2 := congrArg (fun p : Work.Tubular.NormalTotal E => p.proj) h
    simpa [Work.Tubular.NormalTotal.proj, zeroVec] using h2)

theorem continuous_zeroVec {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Continuous (zeroVec E v₀) := by
  have hp : Continuous (fun q : ↥(awaySet E v₀) =>
      ((q.1.1.proj, (0 : Work.Tubular.Euc (8 + k))) : V.pt × Work.Tubular.Euc (8 + k))) := by
    fun_prop
  exact Continuous.subtype_mk hp (fun q => Work.Tubular.zero_mem_normalSpace E q.1.1.proj)

/-- The retraction `p ↦ 0_{proj p}` of `awaySet` onto the zero section. -/
def awayZeroFun {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (q : ↥(awaySet E v₀)) : ↥(awaySet E v₀) :=
  ⟨⟨zeroVec E v₀ q, zeroVec_ne_basePt E v₀ q⟩, q.2⟩

theorem continuous_awayZeroFun {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Continuous (awayZeroFun E v₀) :=
  Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_zeroVec E v₀) (zeroVec_ne_basePt E v₀)) (fun q => q.2)

def awayZeroCM {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    C(↥(awaySet E v₀), ↥(awaySet E v₀)) :=
  ⟨awayZeroFun E v₀, continuous_awayZeroFun E v₀⟩

def homNormal {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (z : ↑unitInterval × ↥(awaySet E v₀)) : Work.Tubular.NormalTotal E :=
  ⟨(z.2.1.1.proj, (z.1 : ℝ) • z.2.1.1.vec),
    Submodule.smul_mem _ (z.1 : ℝ) (Work.Tubular.NormalTotal.vec_mem z.2.1.1)⟩

theorem homNormal_ne_basePt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (z : ↑unitInterval × ↥(awaySet E v₀)) : homNormal E v₀ z ≠ basePt E v₀ := by
  intro h
  exact z.2.2 (by
    have h2 := congrArg (fun p : Work.Tubular.NormalTotal E => p.proj) h
    simpa [Work.Tubular.NormalTotal.proj, homNormal] using h2)

theorem continuous_homNormal {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Continuous (homNormal E v₀) := by
  have hp : Continuous (fun z : ↑unitInterval × ↥(awaySet E v₀) =>
      ((z.2.1.1.proj, (z.1 : ℝ) • z.2.1.1.vec) : V.pt × Work.Tubular.Euc (8 + k))) := by
    fun_prop
  exact Continuous.subtype_mk hp
    (fun z => Submodule.smul_mem _ (z.1 : ℝ) (Work.Tubular.NormalTotal.vec_mem z.2.1.1))

/-- The radial homotopy from the retraction to the identity. -/
def awayHomFun {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (z : ↑unitInterval × ↥(awaySet E v₀)) : ↥(awaySet E v₀) :=
  ⟨⟨homNormal E v₀ z, homNormal_ne_basePt E v₀ z⟩, z.2.2⟩

theorem continuous_awayHomFun {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Continuous (awayHomFun E v₀) :=
  Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_homNormal E v₀) (homNormal_ne_basePt E v₀))
    (fun z => z.2.2)

def awayHomotopy {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    (awayZeroCM E v₀).Homotopy (ContinuousMap.id ↥(awaySet E v₀)) where
  toContinuousMap := ⟨awayHomFun E v₀, continuous_awayHomFun E v₀⟩
  map_zero_left q := by
    refine Subtype.ext (Subtype.ext (Work.Tubular.NormalTotal.ext (Prod.ext rfl ?_)))
    simp [awayHomFun, awayZeroCM, awayZeroFun, zeroVec, homNormal]
  map_one_left q := by
    refine Subtype.ext (Subtype.ext (Work.Tubular.NormalTotal.ext (Prod.ext rfl ?_)))
    simp [awayHomFun, homNormal]

def awayToFun {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    C(↥(awaySet E v₀), {y : V.pt // y ≠ v₀}) where
  toFun q := ⟨q.1.1.proj, q.2⟩
  continuous_toFun := by fun_prop

theorem awayToFun_apply {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (q : ↥(awaySet E v₀)) : awayToFun E v₀ q = ⟨q.1.1.proj, q.2⟩ := rfl

def invPt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (y : {y : V.pt // y ≠ v₀}) : Work.Tubular.NormalTotal E :=
  ⟨(y.1, 0), Work.Tubular.zero_mem_normalSpace E y.1⟩

theorem invPt_ne_basePt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (y : {y : V.pt // y ≠ v₀}) : invPt E v₀ y ≠ basePt E v₀ := by
  intro h
  exact y.2 (by
    have h2 := congrArg (fun p : Work.Tubular.NormalTotal E => p.proj) h
    simpa [Work.Tubular.NormalTotal.proj, invPt] using h2)

theorem continuous_invPt {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Continuous (invPt E v₀) := by
  have hp : Continuous (fun y : {y : V.pt // y ≠ v₀} =>
      ((y.1, (0 : Work.Tubular.Euc (8 + k))) : V.pt × Work.Tubular.Euc (8 + k))) := by
    fun_prop
  exact Continuous.subtype_mk hp (fun y => Work.Tubular.zero_mem_normalSpace E y.1)

def awayInvFun {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    C({y : V.pt // y ≠ v₀}, ↥(awaySet E v₀)) where
  toFun y := ⟨⟨invPt E v₀ y, invPt_ne_basePt E v₀ y⟩, y.2⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_invPt E v₀) (invPt_ne_basePt E v₀)) (fun y => y.2)

theorem awayInvFun_apply {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (q : ↥(awaySet E v₀)) :
    (awayInvFun E v₀) (awayToFun E v₀ q) = awayZeroCM E v₀ q := by
  refine Subtype.ext (Subtype.ext (Work.Tubular.NormalTotal.ext ?_))
  rfl

theorem awayToFun_invFun_apply {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (y : {y : V.pt // y ≠ v₀}) : awayToFun E v₀ ((awayInvFun E v₀) y) = y := by
  refine Subtype.ext ?_
  rfl

/-- **`awaySet` (the open disc bundle over `V ∖ {v₀}`) is homotopy equivalent to `V ∖ {v₀}`.** -/
def awayHomotopyEquiv {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    ContinuousMap.HomotopyEquiv ↥(awaySet E v₀) {y : V.pt // y ≠ v₀} where
  toFun := awayToFun E v₀
  invFun := awayInvFun E v₀
  left_inv := by
    have hcomp : (awayInvFun E v₀).comp (awayToFun E v₀) = awayZeroCM E v₀ := by
      apply ContinuousMap.ext
      intro q
      exact awayInvFun_apply E v₀ q
    rw [hcomp]
    exact ⟨awayHomotopy E v₀⟩
  right_inv := by
    have h : (awayToFun E v₀).comp (awayInvFun E v₀) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro y
      exact awayToFun_invFun_apply E v₀ y
    rw [h]

/-- **`H_{8+k}` of the open disc bundle over `V ∖ {v₀}` vanishes.** -/
theorem isZero_homology_awaySet {V : Work.ThomBordism.Man8} {k : ℕ} [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(awaySet E v₀))).homology (8 + k)) :=
  Work.Cohomology.isZero_homology_of_homotopyEquiv (awayHomotopyEquiv E v₀) (8 + k)
    (Work.Tubular.TubeClass.isZero_homology_compl_point_man8_all V v₀ (8 + k) (by omega))

end AwaySet

variable {V : Work.ThomBordism.Man8} {k : ℕ}

structure EucNormalBundle (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) where
  ι : Type
  nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι
  isEucl : Work.Thom.IsEuclidean nu
  phi : VectorBundleCore.TotalSpace nu ≃ₜ Work.Tubular.NormalTotal E
  norm_eq : ∀ p, Work.Thom.fibreNorm nu p = Work.Tubular.normalNorm E (phi p)
  proj_eq : ∀ p, (phi p).proj = VectorBundleCore.proj nu p

theorem exists_eucNormalBundle (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    Nonempty (EucNormalBundle E) := by
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  refine ⟨⟨Work.ThomBordism.PontryaginThom.CoverIdx V k, Work.Tubular.normalBundle E ND,
    Work.Tubular.isEuclidean_normalBundle E ND, Work.Tubular.eucNormalHomeomorph E ND, ?_, ?_⟩⟩
  · intro p
    rw [Work.Tubular.eucNormalHomeomorph_apply]
    exact Work.Tubular.fibreNorm_eq_normalNorm E ND p
  · intro p
    rfl

theorem normalNorm_basePt (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt) : Work.Tubular.normalNorm E (basePt E v₀) = 0 :=
  (Work.Tubular.normalNorm_mk E v₀ 0 (Work.Tubular.zero_mem_normalSpace E v₀)).trans norm_zero

abbrev sphNormal (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Set (Work.Tubular.NormalTotal E) :=
  {p | Work.Tubular.normalNorm E p = 1 ∧ p.proj ≠ v₀}

section Sph

variable (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)

attribute [local fun_prop] Work.Tubular.NormalTotal.continuous_proj
  Work.Tubular.NormalTotal.continuous_vec Work.Tubular.continuous_normalNorm

theorem mem_sphNormal {p : Work.Tubular.NormalTotal E} :
    p ∈ sphNormal E v₀ ↔ Work.Tubular.normalNorm E p = 1 ∧ p.proj ≠ v₀ := Iff.rfl

theorem normalNorm_ne_zero (q : ↥(awayRel E v₀)) : Work.Tubular.normalNorm E q.1.1.1 ≠ 0 :=
  q.2

theorem normalNorm_pos (q : ↥(awayRel E v₀)) : 0 < Work.Tubular.normalNorm E q.1.1.1 :=
  lt_of_le_of_ne (Work.Tubular.normalNorm_nonneg E _) (Ne.symm (normalNorm_ne_zero E v₀ q))

/-! ## The radial projection onto the unit sphere bundle and back -/

/-- The point of the normal total space with the same direction as `q` and norm `1`. -/
def scalePt (q : ↥(awayRel E v₀)) : Work.Tubular.NormalTotal E :=
  ⟨(q.1.1.1.proj, (Work.Tubular.normalNorm E q.1.1.1)⁻¹ • q.1.1.1.vec),
    Submodule.smul_mem _ _ (Work.Tubular.NormalTotal.vec_mem q.1.1.1)⟩

theorem scalePt_norm (q : ↥(awayRel E v₀)) : Work.Tubular.normalNorm E (scalePt E v₀ q) = 1 := by
  rw [scalePt, Work.Tubular.normalNorm_mk, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (normalNorm_pos E v₀ q))]
  exact inv_mul_cancel₀ (normalNorm_ne_zero E v₀ q)

theorem scalePt_proj (q : ↥(awayRel E v₀)) : (scalePt E v₀ q).proj ≠ v₀ := q.1.2

/-- The radial projection of the punctured bundle onto the unit sphere bundle over `{v₀}ᶜ`. -/
def sphScale (q : ↥(awayRel E v₀)) : ↥(sphNormal E v₀) :=
  ⟨scalePt E v₀ q, scalePt_norm E v₀ q, scalePt_proj E v₀ q⟩

theorem continuous_scalePt : Continuous (scalePt E v₀) := by
  have h : ∀ q : ↥(awayRel E v₀), Work.Tubular.normalNorm E q.1.1.1 ≠ 0 :=
    fun q => normalNorm_ne_zero E v₀ q
  unfold scalePt
  fun_prop

theorem continuous_sphScale : Continuous (sphScale E v₀) :=
  Continuous.subtype_mk (continuous_scalePt E v₀)
    (fun q => ⟨scalePt_norm E v₀ q, scalePt_proj E v₀ q⟩)

/-- The inclusion of the unit sphere bundle over `{v₀}ᶜ` into the punctured bundle. -/
def sphToRel (p : ↥(sphNormal E v₀)) : ↥(awayRel E v₀) :=
  ⟨⟨⟨p.1, by
      intro h
      have h1 : Work.Tubular.normalNorm E p.1 = 1 := (mem_sphNormal E v₀).mp p.2 |>.1
      rw [h, normalNorm_basePt] at h1
      exact one_ne_zero h1.symm⟩, (mem_sphNormal E v₀).mp p.2 |>.2⟩, by
      change Work.Tubular.normalNorm E p.1 ≠ 0
      have h1 : Work.Tubular.normalNorm E p.1 = 1 := (mem_sphNormal E v₀).mp p.2 |>.1
      rw [h1]
      exact one_ne_zero⟩

theorem continuous_sphToRel : Continuous (sphToRel E v₀) := by
  unfold sphToRel
  fun_prop

theorem sphScale_sphToRel (p : ↥(sphNormal E v₀)) : sphScale E v₀ (sphToRel E v₀ p) = p := by
  have h1 : Work.Tubular.normalNorm E p.1 = 1 := (mem_sphNormal E v₀).mp p.2 |>.1
  refine Subtype.ext (Work.Tubular.NormalTotal.ext (Prod.ext ?_ ?_))
  · rfl
  · simp [sphScale, scalePt, sphToRel, Work.Tubular.NormalTotal.vec, h1]

/-! ## The radial homotopy -/

theorem homCoeff_pos (t : ↑unitInterval) (r : ℝ) (hr : 0 < r) :
    0 < (1 - (t : ℝ)) * r⁻¹ + (t : ℝ) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]
    simpa using inv_pos.mpr hr
  · have h2 : 0 ≤ (1 - (t : ℝ)) * r⁻¹ := mul_nonneg (by linarith) (inv_pos.mpr hr).le
    linarith

def homCoeff (z : ↑unitInterval × ↥(awayRel E v₀)) : ℝ :=
  (1 - (z.1 : ℝ)) * (Work.Tubular.normalNorm E z.2.1.1.1)⁻¹ + (z.1 : ℝ)

theorem continuous_homCoeff : Continuous (homCoeff E v₀) := by
  have h : ∀ z : ↑unitInterval × ↥(awayRel E v₀), Work.Tubular.normalNorm E z.2.1.1.1 ≠ 0 :=
    fun z => normalNorm_ne_zero E v₀ z.2
  unfold homCoeff
  fun_prop

theorem homCoeff_pos' (z : ↑unitInterval × ↥(awayRel E v₀)) : 0 < homCoeff E v₀ z :=
  homCoeff_pos z.1 _ (normalNorm_pos E v₀ z.2)

theorem homCoeff_zero (q : ↥(awayRel E v₀)) :
    homCoeff E v₀ ((0 : ↑unitInterval), q) = (Work.Tubular.normalNorm E q.1.1.1)⁻¹ := by
  simp [homCoeff]

theorem homCoeff_one (q : ↥(awayRel E v₀)) : homCoeff E v₀ ((1 : ↑unitInterval), q) = 1 := by
  simp [homCoeff]

/-- The point of the normal total space at the intermediate radius. -/
def homPt (z : ↑unitInterval × ↥(awayRel E v₀)) : Work.Tubular.NormalTotal E :=
  ⟨(z.2.1.1.1.proj, homCoeff E v₀ z • z.2.1.1.1.vec),
    Submodule.smul_mem _ _ (Work.Tubular.NormalTotal.vec_mem z.2.1.1.1)⟩

theorem homPt_ne (z : ↑unitInterval × ↥(awayRel E v₀)) : homPt E v₀ z ≠ basePt E v₀ := by
  intro h
  have h1 : Work.Tubular.normalNorm E (homPt E v₀ z) = 0 := by rw [h, normalNorm_basePt]
  rw [homPt, Work.Tubular.normalNorm_mk, norm_smul, Real.norm_eq_abs,
    abs_of_pos (homCoeff_pos' E v₀ z)] at h1
  exact (mul_ne_zero (ne_of_gt (homCoeff_pos' E v₀ z))
    (normalNorm_ne_zero E v₀ z.2)) h1

theorem homPt_proj (z : ↑unitInterval × ↥(awayRel E v₀)) : (homPt E v₀ z).proj ≠ v₀ := z.2.1.2

theorem homPt_norm (z : ↑unitInterval × ↥(awayRel E v₀)) :
    Work.Tubular.normalNorm E (homPt E v₀ z) ≠ 0 := by
  rw [homPt, Work.Tubular.normalNorm_mk, norm_smul, Real.norm_eq_abs,
    abs_of_pos (homCoeff_pos' E v₀ z)]
  exact mul_ne_zero (ne_of_gt (homCoeff_pos' E v₀ z)) (normalNorm_ne_zero E v₀ z.2)

/-- The radial homotopy from the projection to the identity on the punctured bundle. -/
def sphHomFun (z : ↑unitInterval × ↥(awayRel E v₀)) : ↥(awayRel E v₀) :=
  ⟨⟨⟨homPt E v₀ z, homPt_ne E v₀ z⟩, homPt_proj E v₀ z⟩, homPt_norm E v₀ z⟩

theorem continuous_homPt : Continuous (homPt E v₀) := by
  have hc : Continuous (homCoeff E v₀) := continuous_homCoeff E v₀
  unfold homPt
  fun_prop

theorem continuous_sphHomFun : Continuous (sphHomFun E v₀) :=
  Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_homPt E v₀) (fun z => homPt_ne E v₀ z)) (fun z => homPt_proj E v₀ z))
    (fun z => homPt_norm E v₀ z)

theorem sphHomFun_zero (q : ↥(awayRel E v₀)) :
    sphHomFun E v₀ ((0 : ↑unitInterval), q) = sphToRel E v₀ (sphScale E v₀ q) := by
  refine Subtype.ext (Subtype.ext (Subtype.ext (Work.Tubular.NormalTotal.ext (Prod.ext ?_ ?_))))
  · rfl
  · simp [sphHomFun, sphHomFun, homPt, sphToRel, sphScale, scalePt, homCoeff,
      Work.Tubular.NormalTotal.vec]

theorem sphHomFun_one (q : ↥(awayRel E v₀)) : sphHomFun E v₀ ((1 : ↑unitInterval), q) = q := by
  refine Subtype.ext (Subtype.ext (Subtype.ext (Work.Tubular.NormalTotal.ext (Prod.ext ?_ ?_))))
  · rfl
  · simp [sphHomFun, homPt, homCoeff, Work.Tubular.NormalTotal.vec]

def sphScaleCM : C(↥(awayRel E v₀), ↥(sphNormal E v₀)) :=
  ⟨sphScale E v₀, continuous_sphScale E v₀⟩

def sphToRelCM : C(↥(sphNormal E v₀), ↥(awayRel E v₀)) :=
  ⟨sphToRel E v₀, continuous_sphToRel E v₀⟩

def sphHomotopy : ((sphToRelCM E v₀).comp (sphScaleCM E v₀)).Homotopy
    (ContinuousMap.id ↥(awayRel E v₀)) where
  toContinuousMap := ⟨sphHomFun E v₀, continuous_sphHomFun E v₀⟩
  map_zero_left q := sphHomFun_zero E v₀ q
  map_one_left q := sphHomFun_one E v₀ q

def awayRelSphHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥(awayRel E v₀) ↥(sphNormal E v₀) where
  toFun := sphScaleCM E v₀
  invFun := sphToRelCM E v₀
  left_inv := ⟨sphHomotopy E v₀⟩
  right_inv := by
    have h : (sphScaleCM E v₀).comp (sphToRelCM E v₀) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro p
      exact sphScale_sphToRel E v₀ p
    rw [h]

def sphToSphOver (B : EucNormalBundle E) (p : ↥(sphNormal E v₀)) :
    ↥(Work.SphHomology.sphOver B.nu ({v₀}ᶜ)) :=
  ⟨⟨B.phi.symm p.1, (Work.Thom.mem_sphereSet _).mpr (by
      rw [B.norm_eq, B.phi.apply_symm_apply]
      exact (mem_sphNormal E v₀).mp p.2 |>.1)⟩, by
      intro h
      have key : p.1.proj = VectorBundleCore.proj B.nu (B.phi.symm p.1) := by
        rw [← B.proj_eq (B.phi.symm p.1), B.phi.apply_symm_apply]
      exact (mem_sphNormal E v₀).mp p.2 |>.2 (key.trans h)⟩

def sphOverToSph (B : EucNormalBundle E) (q : ↥(Work.SphHomology.sphOver B.nu ({v₀}ᶜ))) :
    ↥(sphNormal E v₀) :=
  ⟨B.phi q.1.1, by
    refine ⟨?_, ?_⟩
    · rw [← B.norm_eq q.1.1]
      exact (Work.Thom.mem_sphereSet q.1.1).mp q.1.2
    · rw [B.proj_eq q.1.1]
      exact q.2⟩

def sphNormalHomeo (B : EucNormalBundle E) :
    ↥(sphNormal E v₀) ≃ₜ ↥(Work.SphHomology.sphOver B.nu ({v₀}ᶜ)) where
  toFun := sphToSphOver E v₀ B
  invFun := sphOverToSph E v₀ B
  left_inv p := by
    refine Subtype.ext ?_
    rw [sphOverToSph, sphToSphOver]
    exact B.phi.apply_symm_apply p.1
  right_inv q := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [sphToSphOver, sphOverToSph]
    exact B.phi.symm_apply_apply q.1.1
  continuous_toFun := by
    unfold sphToSphOver
    fun_prop
  continuous_invFun := by
    unfold sphOverToSph
    fun_prop

theorem isZero_homology_sphNormal [ConnectedSpace V.pt] (B : EucNormalBundle E) (hk : 1 ≤ k)
    (n : ℕ) (hn : 7 + k ≤ n) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(sphNormal E v₀))).homology n) :=
  Work.Cohomology.isZero_homology_of_homotopyEquiv (sphNormalHomeo E v₀ B).toHomotopyEquiv n
    (sphOver_punctured_vanishing hk B.nu B.isEucl v₀ n (by omega))

end Sph

theorem isZero_homology_awayRel [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) (hk : 1 ≤ k)
    (n : ℕ) (hn : 7 + k ≤ n) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(awayRel E v₀))).homology n) := by
  obtain ⟨B⟩ := exists_eucNormalBundle E
  exact Work.Cohomology.isZero_homology_of_homotopyEquiv (awayRelSphHomotopyEquiv E v₀) n
    (isZero_homology_sphNormal E v₀ B hk n hn)

theorem puncturedNormalPair_vanishing {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {p : Work.Tubular.NormalTotal E //
        p ≠ ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩})
      {q | Work.Tubular.normalNorm E q.1 ≠ 0}).homology (8 + k)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- the rank-`0` case: `Q = ∅` and `ν ∖ {x₀} ≅ V ∖ {v₀}`
    subst hk0
    have hzero : ∀ p : Work.Tubular.NormalTotal E, Work.Tubular.normalNorm E p = 0 := by
      intro p
      rw [show Work.Tubular.normalNorm E p = ‖p.1.2‖ from rfl,
        Work.Tubular.TubeClass.vec_eq_zero_of_embeddingData_eight E p]
      simp
    have hQ : {q : {p : Work.Tubular.NormalTotal E //
        p ≠ ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩} |
        Work.Tubular.normalNorm E q.1 ≠ 0} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => h (hzero q.1)
    rw [hQ]
    set φ := Work.Tubular.TubeClass.normalTotalHomeoOfEight E with hφ
    have hb : φ ⟨(v₀, 0), Work.Tubular.TubeClass.zero_mem_normalSpace_eight E v₀⟩ =
        v₀ := rfl
    have hiff : ∀ x : Work.Tubular.NormalTotal E,
        (x ≠ ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩) ↔ φ x ≠ v₀ := by
      intro x
      constructor
      · intro hx hc
        exact hx (φ.injective (by rw [hc, hb]))
      · intro hx hc
        exact hx (by rw [hc, hb])
    let e := φ.subtype (p := fun x : Work.Tubular.NormalTotal E =>
        x ≠ ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩)
      (q := fun y : V.pt => y ≠ v₀) hiff
    have hY : IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of {y : V.pt | y ≠ v₀})).homology 8) :=
      Work.Tubular.TubeClass.isZero_homology_compl_point_man8_all V v₀ 8 (le_refl 8)
    have hX : IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of {p : Work.Tubular.NormalTotal E //
          p ≠ ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩})).homology 8) :=
      Work.Cohomology.isZero_homology_of_homotopyEquiv e.toHomotopyEquiv 8 hY
    haveI := Work.Cohomology.relChains_empty_homology_iso
      (TopCat.of {p : Work.Tubular.NormalTotal E //
        p ≠ ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩}) 8
    exact IsZero.of_iso hX
      (asIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of {p : Work.Tubular.NormalTotal E //
          p ≠ ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩}) ∅)) 8)).symm
  · -- `k ≥ 1`: excise the fibre over `v₀` and use the long exact sequence of the pair
    change CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of (Punct E v₀)) (PunctRel E v₀)).homology (8 + k))
    obtain ⟨e⟩ := Work.Cohomology.excision (TopCat.of (Punct E v₀)) (PunctRel E v₀)
      (awayPt E v₀) (closure_awayPt_subset_interior_punctRel E v₀) (8 + k)
    refine IsZero.of_iso ?_ e
    refine isZero_relChains_of_isZero (TopCat.of ↥{x : Punct E v₀ | x ∉ awayPt E v₀})
      {x : ↥{x : Punct E v₀ | x ∉ awayPt E v₀} | (x : Punct E v₀) ∈ PunctRel E v₀}
      (8 + k) (by omega) ?_ ?_ ?_
    · exact isZero_homology_awayRel E v₀ (by omega) (8 + k) (by omega)
    · exact isZero_homology_awayRel E v₀ (by omega) ((8 + k) - 1) (by omega)
    · exact isZero_homology_awaySet E v₀

end

end Work.Tubular.PuncturedDiscPair
