import Mathlib
import Submission.Work.ThomBordism.stdHalfBallModel
import Submission.Work.ThomBordism.ModelBall.stdHalfBallHomeoBall
import Submission.Work.ThomBordism.ModelBall.Transport
import Submission.Work.SignatureBordism.BallBoundary
import Submission.Work.ThomBordism.modelHalfOrientation
import Submission.Work.Surgery.CollarBall
import Submission.Work.ThomBordism.collarTransport
import Submission.Work.Orient.Boundary
import Submission.Work.ThomBordism.orientOfCollar
import Submission.Work.Orient.Boundary.HalfRestrictIsoAtPoint
import Submission.Work.Orient.Boundary.ExistsInteriorHalfBall
import Submission.Work.Orient.Boundary.LocalClassConstantOnBall
import Submission.Work.Orient.Boundary.CoreClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the prescribed interior local classes of the standard half-ball are realized

`Work.ThomBordism.stdHalfBallOrientExists`: the family of prescribed local classes
`Work.ThomBordism.stdIntOrient` of the standard half-ball `W = {0 ≤ u 0, ‖u‖ ≤ 1}` is the family of
local classes of an actual relative fundamental class `w ∈ H_{m+1}(W, ∂W)`.  Without this the model
lemma `Work.ThomBordism.stdHalfBallBoundarySign` would be vacuous.

## The route

* `stdHalfBallCharted` equips `↥(stdHalfBall (m+1))` with the charted space structure pushed from
  the closed ball along `Work.ThomBordism.ModelBall.stdHalfBallHomeoBall`, making it a compact
  `T2` `(m+1)`-manifold with boundary whose boundary is `stdHalfBallBdry (m+1)`.
* The family `γ x hx := stdIntOrient m x _` — the transfer of the Euclidean generator along the
  *identity* chart `stdIntChart (m+1)` — is an orientation family
  (`Work.Orient.IsHalfOrientationFamily`): it consists of generators by
  `Work.ThomBordism.span_chartTr_eucFam`, and it is coherent over coordinate half-balls by
  `Work.ThomBordism.pieceClassChartTr` (applied to the single chart `stdIntChart (m+1)`, whose
  source is the whole interior).
* `Work.Surgery.hasCollar_ball` gives a collar of the closed ball, transported to `W` by
  `Work.ThomBordism.collarTransport`; the strengthened existence theorem
  `Work.ThomBordism.relFundClass_loc_of_collar` (the strengthened form of
  `Work.ThomBordism.exists_relFundClass_of_collar`, proved in this file) then produces a relative
  fundamental class whose local classes are *exactly* `γ x hx`, i.e. `stdIntOrient m x hx`.
* Finally `relFundClass_congr_set` converts the conclusion, which is stated for the boundary of the
  charted structure, to the statement for the set `stdHalfBallBdry (m+1)` of the target.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology Manifold ContDiff
open Work.PTGeometric

namespace Work.ThomBordism

noncomputable section

/-! ## The charted structure of the standard half-ball -/

/-- **The standard half-ball is a compact manifold with boundary**, with the charted space structure
obtained by pushing forward the structure of the closed ball along the explicit homeomorphism
`ModelBall.stdHalfBallHomeoBall`; its boundary is `stdHalfBallBdry (m+1)`, it is compact, and it
carries a collar (transported from the explicit collar of the closed ball). -/
theorem stdHalfBallCharted (m : ℕ) :
    ∃ (_ : ChartedSpace (EuclideanHalfSpace (m + 1)) ↥(stdHalfBall (m + 1))),
      (∃ (_ : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ ↥(stdHalfBall (m + 1))),
        (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))
            = stdHalfBallBdry (m + 1) ∧
        Work.Surgery.HasCollar m ↥(stdHalfBall (m + 1)) ∧
        CompactSpace ↥(stdHalfBall (m + 1))) := by
  classical
  obtain ⟨e1, h1⟩ := ModelBall.stdHalfBallHomeoBall (m + 1)
  letI cs : ChartedSpace (EuclideanHalfSpace (m + 1)) ↥(stdHalfBall (m + 1)) :=
    Work.PTGeometric.pushedChartedSpace e1.symm
  haveI im : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ ↥(stdHalfBall (m + 1)) :=
    Work.ThomBordism.isManifold_pushedChartedSpace (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
      e1.symm
  have hbiff : ∀ y : ↥(stdHalfBall (m + 1)),
      y ∈ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1)) ↔
        (e1.symm).symm y ∈ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary
          (Work.Surgery.Disk m) :=
    fun y => Work.ThomBordism.mem_boundary_pushedChartedSpace
      (I := modelWithCornersEuclideanHalfSpace (m + 1)) (X := Work.Surgery.Disk m)
      (Y := ↥(stdHalfBall (m + 1))) e1.symm y
  refine ⟨cs, im, ?_, ?_, e1.symm.compactSpace⟩
  · ext y
    have hb := hbiff y
    show (y ∈ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))) ↔
      ((y : Euc (m + 1)) 0 = 0 ∨ ‖(y : Euc (m + 1))‖ = 1)
    rw [show (y ∈ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))) ↔
        (e1 y ∈ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary (Work.Surgery.Disk m)) from hb]
    rw [Work.SignatureBordism.ball_boundary m]
    exact (h1 y).symm
  · exact collarTransport (n := m) (X := Work.Surgery.Disk m) (Y := ↥(stdHalfBall (m + 1)))
      e1.symm hbiff (Work.Surgery.hasCollar_ball m)

/-! ## Transport of the conclusion across an equality of the excluded sets -/

/-- **The existence statement is invariant under replacing the excluded set by an equal set.**
`relPunct` is indexed by the (excluded) boundary set, so the statement has to be transported rather
than rewritten; the transport is along the equation itself (`subst`). -/
theorem relFundClass_congr_set {W : TopCat} {k : ℕ} {B B' : Set W} (h : B = B')
    (γ : ∀ x : W, x ∉ B → Work.Orient.LocH W k x)
    (hex : ∃ w : (Work.Cohomology.relChains W B).homology k,
      (∀ x (hx : x ∉ B),
        (HomologicalComplex.homologyMap (Work.Orient.relPunct W B x hx) k).hom w = γ x hx) ∧
      Work.Orient.IsRelFundClass W k B w) :
    ∃ w : (Work.Cohomology.relChains W B').homology k,
      (∀ x (hx : x ∉ B'),
        (HomologicalComplex.homologyMap (Work.Orient.relPunct W B' x hx) k).hom w
          = γ x (h.symm ▸ hx)) ∧
      Work.Orient.IsRelFundClass W k B' w := by
  subst h
  exact hex

/-- **The truth value of `loc_x u = γ x` is constant on a coordinate half-ball of the interior.** -/
theorem loc_eq_iff_of_mem_halfBall (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (z : W) (r : ℝ) (hr : 0 < r)
    (hball : Work.Orient.halfBallGood (n + 1) W z r)
    (hint : ∀ y ∈ Work.Orient.halfBallPiece (n + 1) W z r,
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      Work.Orient.LocH W (n + 1) x)
    (u : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (a : Work.ThomBordism.RelH W (n + 1) (Work.Orient.halfBallPiece (n + 1) W z r))
    (ha : ∀ (y : W) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      (hyK : y ∈ Work.Orient.halfBallPiece (n + 1) W z r),
      Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hyK) a = γ y hy)
    (x y : W) (hx : x ∈ Work.Orient.halfBallPiece (n + 1) W z r)
    (hy : y ∈ Work.Orient.halfBallPiece (n + 1) W z r) :
    ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x
          (hint x hx)) (n + 1)).hom u = γ x (hint x hx))
      ↔ ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) y
          (hint y hy)) (n + 1)).hom u = γ y (hint y hy)) := by
  classical
  let K : Set W := Work.Orient.halfBallPiece (n + 1) W z r
  let B : Set W := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W
  have hKsub : B ⊆ Kᶜ := fun t ht hKt => hint t hKt ht
  have hsubx : Kᶜ ⊆ ({x} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
  have hsuby : Kᶜ ⊆ ({y} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)
  let v : (Work.Cohomology.relChains W Kᶜ).homology (n + 1) :=
    (HomologicalComplex.homologyMap
      (Work.Orient.relChainsIncl W (A := B) (B := Kᶜ) hKsub) (n + 1)).hom u
  have hfac : ∀ (t : W) (ht : t ∈ K) (hsub : Kᶜ ⊆ ({t} : Set W)ᶜ),
      Work.Orient.relPunct W B t (hint t ht)
        = Work.Orient.relChainsIncl W (A := B) (B := Kᶜ) hKsub
          ≫ Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ hsub := by
    intro t ht hsub
    rw [Work.Orient.relPunct_eq_relChainsIncl]
    rw [← Work.Orient.relChainsIncl_eq_relCokerMap W hsub]
    rw [Work.Orient.relChainsIncl_trans W hKsub hsub]
  have hbr : ∀ (t : W) (ht : t ∈ K),
      Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr ht)
        = (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ht))) (n + 1)).hom := by
    intro t ht
    rw [Work.Orient.resRelH_eq_homologyMap_relChainsIncl W (n + 1)
      (Set.singleton_subset_iff.mpr ht)]
    rw [Work.Orient.relChainsIncl_eq_relCokerMap]
  have key : ∀ (t : W) (ht : t ∈ K),
      (HomologicalComplex.homologyMap (Work.Orient.relPunct W B t (hint t ht)) (n + 1)).hom u
        - γ t (hint t ht)
      = (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ht))) (n + 1)).hom (v - a) := by
    intro t ht
    have h1 := hfac t ht (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ht))
    have h2 : γ t (hint t ht)
        = (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ
            (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ht))) (n + 1)).hom a := by
      rw [← hbr t ht]
      exact (ha t (hint t ht) ht).symm
    rw [h1, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply, map_sub, h2]
    rfl
  have hinj : ∀ (t : W) (ht : t ∈ K), Function.Injective
      ((HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ht))) (n + 1)).hom) :=
    fun t ht => (ConcreteCategory.isIso_iff_bijective _).mp
      (Work.Orient.Boundary.HalfRestrictIsoAtPoint n W z r hr hball hint t ht) |>.1
  constructor
  · intro hh
    have h0 : (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({x} : Set W)ᶜ
        hsubx) (n + 1)).hom (v - a) = 0 := by
      rw [← key x hx, hh, sub_self]
    have hz : v - a = 0 := hinj x hx (by rw [h0, map_zero])
    have h0' : (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({y} : Set W)ᶜ
        hsuby) (n + 1)).hom (v - a) = 0 := by rw [hz, map_zero]
    have hky := key y hy
    rw [h0'] at hky
    exact sub_eq_zero.mp hky
  · intro hh
    have h0 : (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({y} : Set W)ᶜ
        hsuby) (n + 1)).hom (v - a) = 0 := by
      rw [← key y hy, hh, sub_self]
    have hz : v - a = 0 := hinj y hy (by rw [h0, map_zero])
    have h0' : (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kᶜ ({x} : Set W)ᶜ
        hsubx) (n + 1)).hom (v - a) = 0 := by rw [hz, map_zero]
    have hkx := key x hx
    rw [h0'] at hkx
    exact sub_eq_zero.mp hkx


/-- **The relative fundamental class realizing a prescribed orientation family, exactly.**
This is `Work.ThomBordism.exists_relFundClass_of_collar` with the last step of its proof exposed:
the class it produces has *exactly* the prescribed local classes `γ`, not merely generators differing
by a sign, because the local comparison with `γ` is locally constant on the interior and the core
meets every component. -/
theorem relFundClass_loc_of_collar {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (c : Work.Surgery.Collar n M)
    (γ : ∀ x : M, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
      Work.Orient.LocH (TopCat.of M) (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n (TopCat.of M) γ) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)).homology (n + 1),
      Work.Orient.IsRelFundClass (TopCat.of M) (n + 1)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) w ∧
      (∀ (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
        (HomologicalComplex.homologyMap
          (Work.Orient.relPunct (TopCat.of M)
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x hx) (n + 1)).hom w
          = γ x hx) := by
  classical
  obtain ⟨C₀, hCp, hint, hconn, hiso⟩ := coreIso_of_collar (n := n) c
  obtain ⟨u₀, hu₀⟩ := Work.Orient.Boundary.exists_coreClass n (TopCat.of M) hCp hint γ hγ
  let φ := HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of M)
    (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ)
    (fun y hy hyc => hint y hyc hy)) (n + 1)
  haveI : IsIso φ := hiso
  obtain ⟨w, hw⟩ := ((ConcreteCategory.isIso_iff_bijective φ).mp inferInstance).2 u₀
  let B : Set M := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M
  -- the local classes on the core
  have hloc_core : ∀ (x : M) (hx : x ∈ C₀),
      (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M) B x (hint x hx))
        (n + 1)).hom w = γ x (hint x hx) := by
    intro x hx
    have h1 : B ⊆ C₀ᶜ := fun t ht htC => hint t htC ht
    have hsubx : C₀ᶜ ⊆ ({x} : Set M)ᶜ :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
    have hfac : Work.Orient.relPunct (TopCat.of M) B x (hint x hx)
        = Work.Orient.relChainsIncl (TopCat.of M) (A := B) (B := C₀ᶜ) h1
          ≫ Work.Cohomology.relCokerMap (TopCat.of M) C₀ᶜ ({x} : Set M)ᶜ hsubx := by
      rw [Work.Orient.relPunct_eq_relChainsIncl]
      rw [← Work.Orient.relChainsIncl_eq_relCokerMap (TopCat.of M) hsubx]
      rw [Work.Orient.relChainsIncl_trans (TopCat.of M) h1 hsubx]
    have hcomp := HomologicalComplex.homologyMap_comp
      (Work.Orient.relChainsIncl (TopCat.of M) (A := B) (B := C₀ᶜ) h1)
      (Work.Cohomology.relCokerMap (TopCat.of M) C₀ᶜ ({x} : Set M)ᶜ hsubx) (n + 1)
    have hloc : (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M) B x
        (hint x hx)) (n + 1)).hom w
        = Work.Orient.resRelH (TopCat.of M) (n + 1) (Set.singleton_subset_iff.mpr hx) u₀ := by
      rw [hfac, hcomp, ModuleCat.comp_apply, show
        (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of M)
          (A := B) (B := C₀ᶜ) h1) (n + 1)).hom w = u₀ from hw]
      rfl
    rw [hloc, hu₀ x hx]
  -- the relative fundamental class property
  have hwf : Work.Orient.IsRelFundClass (TopCat.of M) (n + 1) B w := by
    refine Work.Orient.Boundary.IsRelFundClassOfCore n (TopCat.of M) C₀ hCp hint hconn w ?_
    intro x hx
    rw [hloc_core x hx]
    exact hγ.1 x (hint x hx)
  -- the comparison with `γ` is locally constant on the interior
  let P : {z : M // z ∉ B} → Prop := fun p =>
    (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M) B p.1 p.2) (n + 1)).hom w
      = γ p.1 p.2
  have key : ∀ p : {z : M // z ∉ B}, ∃ V ∈ 𝓝 p, ∀ q ∈ V, (P q ↔ P p) := by
    intro p
    have hBclosed : IsClosed B := Work.Orient.Boundary.isClosed_boundary_halfSpace n (TopCat.of M)
    obtain ⟨r, hr, hgood, hsub⟩ := Work.Orient.Boundary.exists_halfBall_subset (n := n)
      (W := TopCat.of M) (U := Bᶜ) hBclosed.isOpen_compl p.2
    refine ⟨Subtype.val ⁻¹' (Work.Orient.halfBallPiece (n + 1) (TopCat.of M) p.1 r), ?_, ?_⟩
    · exact (continuous_subtype_val.continuousAt).preimage_mem_nhds
        (Work.Orient.Boundary.halfBallPiece_mem_nhds (n := n) (W := TopCat.of M) hr)
    · intro q hq
      obtain ⟨a, ha⟩ := hγ.2 (Work.Orient.halfBallPiece (n + 1) (TopCat.of M) p.1 r)
        ⟨p.1, r, hr, hgood, rfl⟩ (fun z hz => hsub hz)
      exact loc_eq_iff_of_mem_halfBall n (TopCat.of M) p.1 r hr hgood (fun z hz => hsub hz)
        γ w a ha q.1 p.1 hq
        (Work.Orient.mem_halfBallPiece_center (n := n + 1) (W := TopCat.of M) (z := p.1) hr)
  have hopen : IsOpen {p : {z : M // z ∉ B} | P p} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨V, hV, hVP⟩ := key p
    exact Filter.mem_of_superset hV (fun q hq => (hVP q hq).mpr hp)
  have hclosed : IsClosed {p : {z : M // z ∉ B} | P p} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨V, hV, hVP⟩ := key p
    exact Filter.mem_of_superset hV (fun q hq hqP => hp ((hVP q hq).mp hqP))
  -- every component of the interior meets the core
  have hcore' : ∀ (q : M) (hq : q ∈ C₀), P ⟨q, hint q hq⟩ := fun q hq => hloc_core q hq
  have hloc_all : ∀ (x : M) (hx : x ∉ B),
      (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M) B x hx)
        (n + 1)).hom w = γ x hx := by
    intro x hx
    obtain ⟨y, hyC₀, hy', ⟨pp⟩⟩ := hconn x hx
    haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hcl : IsClopen {s : Set.Icc (0 : ℝ) 1 | P (pp s)} :=
      ⟨hclosed.preimage pp.continuous, hopen.preimage pp.continuous⟩
    have hne : ({s : Set.Icc (0 : ℝ) 1 | P (pp s)}).Nonempty :=
      ⟨1, by show P (pp 1); rw [Path.target pp]; exact hcore' y hyC₀⟩
    have huniv := hcl.eq_univ hne
    have hpath : ∀ s : Set.Icc (0 : ℝ) 1, P (pp s) := by
      intro s
      have hs : s ∈ {s : Set.Icc (0 : ℝ) 1 | P (pp s)} := by rw [huniv]; trivial
      exact hs
    have h0 : P (pp 0) := hpath 0
    have h0' : P (Subtype.mk x hx) := by rw [← Path.source pp]; exact h0
    exact h0'
  exact ⟨w, hwf, hloc_all⟩

/-! ## The main theorem -/

theorem stdHalfBallOrientExists (m : ℕ) (hm : 1 ≤ m) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
        (Work.ThomBordism.stdHalfBallBdry (m + 1))).homology (m + 1),
      (∀ (x : ↥(Work.ThomBordism.stdHalfBall (m + 1)))
          (hx : x ∈ (Work.ThomBordism.stdIntChart (m + 1)).source),
          (HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
              (Work.ThomBordism.stdHalfBallBdry (m + 1)) x
              (Work.ThomBordism.stdIntChart_source_notMem (m + 1) hx)) (m + 1)).hom w
            = Work.ThomBordism.stdIntOrient m x hx) ∧
      Work.Orient.IsRelFundClass (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1))) (m + 1)
        (Work.ThomBordism.stdHalfBallBdry (m + 1)) w := by
  classical
  obtain ⟨cs, him, hbdry, hcollar, hcpt⟩ := stdHalfBallCharted m
  letI := cs
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ ↥(stdHalfBall (m + 1)) := him
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 ↥(stdHalfBall (m + 1)) :=
    inferInstance
  haveI : Nonempty ↥(stdHalfBall (m + 1)) := ⟨⟨0, zero_mem_stdHalfBall (m + 1)⟩⟩
  haveI : CompactSpace ↥(stdHalfBall (m + 1)) := hcpt
  -- the interior of the half-ball in the charted structure is the source of the identity chart
  have hsrc : ∀ (x : ↥(stdHalfBall (m + 1))),
      x ∉ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1)) →
      x ∈ (stdIntChart (m + 1)).source := by
    intro x hx
    rw [hbdry] at hx
    show (x : Euc (m + 1)) ∈ stdIntTarget (m + 1)
    exact (mem_stdHalfBallInterior_iff (m + 1) x).mpr hx
  -- the prescribed family of local classes
  let γ : ∀ x : TopCat.of ↥(stdHalfBall (m + 1)),
      x ∉ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary
        (TopCat.of ↥(stdHalfBall (m + 1))) →
      Work.Orient.LocH (TopCat.of ↥(stdHalfBall (m + 1))) (m + 1) x :=
    fun x hx => stdIntOrient m x (hsrc x hx)
  -- it is an orientation family
  have hγ : Work.Orient.IsHalfOrientationFamily m (TopCat.of ↥(stdHalfBall (m + 1))) γ := by
    refine ⟨?_, ?_⟩
    · intro x hx
      show Submodule.span ℤ
        ({(Work.PTGeometric.HOF.chartTr (e := stdIntChart (m + 1)) x (hsrc x hx)
          (Work.PTGeometric.HOF.eucFam (m + 1) (by omega) ((stdIntChart (m + 1)) x)))} :
          Set (Work.Orient.LocH (TopCat.of ↥(stdHalfBall (m + 1))) (m + 1) x)) = ⊤
      exact span_chartTr_eucFam (by omega) (stdIntChart (m + 1)) x (hsrc x hx)
    · intro K hK hKint
      obtain ⟨z, r, hr, hgood, rfl⟩ := hK
      have hKcpt : IsCompact (Work.Orient.halfBallPiece (m + 1)
          (TopCat.of ↥(stdHalfBall (m + 1))) z r) :=
        Work.Orient.halfBallPiece_isCompact z r hr hgood
      have hKsrc : ∀ x ∈ Work.Orient.halfBallPiece (m + 1)
          (TopCat.of ↥(stdHalfBall (m + 1))) z r, x ∈ (stdIntChart (m + 1)).source :=
        fun x hx => hsrc x (hKint x hx)
      obtain ⟨a, ha⟩ := pieceClassChartTr (by omega) (stdIntChart (m + 1)) _ hKcpt hKsrc
      refine ⟨a, ?_⟩
      intro x hx hxK
      rw [ha x hxK]
      show Work.PTGeometric.HOF.chartTr (e := stdIntChart (m + 1)) x (hKsrc x hxK)
          (Work.PTGeometric.HOF.eucFam (m + 1) (by omega) ((stdIntChart (m + 1)) x))
        = Work.PTGeometric.HOF.chartTr (e := stdIntChart (m + 1)) x (hsrc x hx)
          (Work.PTGeometric.HOF.eucFam (m + 1) (by omega) ((stdIntChart (m + 1)) x))
      exact congrArg (fun h => Work.PTGeometric.HOF.chartTr (e := stdIntChart (m + 1)) x h
        (Work.PTGeometric.HOF.eucFam (m + 1) (by omega) ((stdIntChart (m + 1)) x)))
        (Subsingleton.elim (hKsrc x hxK) (hsrc x hx))
  -- the collar of the half-ball
  -- the class realizing `γ`
  obtain ⟨w, hwf, hwl⟩ := relFundClass_loc_of_collar (n := m) (Classical.choice hcollar) γ hγ
  have hex : ∃ w' : (Work.Cohomology.relChains (TopCat.of ↥(stdHalfBall (m + 1)))
      ((modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1)))).homology (m + 1),
      (∀ (x : ↥(stdHalfBall (m + 1)))
        (hx : x ∉ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))),
        (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of ↥(stdHalfBall (m + 1)))
          ((modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))) x hx)
          (m + 1)).hom w' = γ x hx) ∧
      Work.Orient.IsRelFundClass (TopCat.of ↥(stdHalfBall (m + 1))) (m + 1)
        ((modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))) w' :=
    ⟨w, hwl, hwf⟩
  obtain ⟨w', hwl', hwf'⟩ := relFundClass_congr_set (W := TopCat.of ↥(stdHalfBall (m + 1)))
    (k := m + 1) hbdry γ hex
  refine ⟨w', ?_, hwf'⟩
  intro x hx
  have hx' : x ∉ stdHalfBallBdry (m + 1) := stdIntChart_source_notMem (m + 1) hx
  rw [hwl' x hx']

end

end Work.ThomBordism
