import Mathlib
import Submission.Work.Tubular.Global
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Tubular.exists_halfOrientationFamily_normalDiscSub
import Submission.Work.Tubular.mem_boundary_normalDiscSub_add
import Submission.Work.Tubular.tubeHalfOrientation
import Submission.Work.Orient.Boundary.HalfCoverGlue
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.radialRescale_homologyMap_id
import Submission.Work.ThomBordism.localisation_injective_zeroSection
import Submission.Work.ThomBordism.localGenDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.ThomBordism

noncomputable section

/-! ## The core-class lemma without the smoothness hypothesis

`Work.Orient.Boundary.exists_coreClass` produces, from an orientation family on a compact manifold
with boundary, a class over any compact set of the interior with prescribed local classes.  Its
statement carries an `IsManifold` hypothesis which its proof uses only once, through
`ModelWithCorners.isClosed_boundary`; the version below replaces that input by
`Work.Orient.Boundary.isClosed_boundary_halfSpace` (which needs only a charted space), so that it
can be applied to the normal disc bundle at the `n + 1` model convention, where the smooth structure
is not available. -/

theorem exists_coreClass_charted (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {C : Set W} (hC : IsCompact C)
    (hCint : ∀ x ∈ C, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      Work.Orient.LocH W (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n W γ) :
    ∃ u : Work.Orient.RelH W (n + 1) C,
      ∀ (x : W) (hx : x ∈ C),
        Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) u = γ x (hCint x hx) := by
  classical
  have hbclosed : IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    Work.Orient.Boundary.isClosed_boundary_halfSpace n W
  have hdisj : Disjoint C ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => hCint x hx1 hx2)
  obtain ⟨m, z, r, hr, hgood, hzC, hcov, hdisjt⟩ :=
    Work.Orient.Boundary.HalfCover n W hC hdisj hbclosed
  let K : Fin m → Set W := fun i => Work.Orient.halfBallPiece (n + 1) W (z i) (r i)
  have hK : ∀ i, Work.Orient.IsCoordHalfBall (n + 1) W (K i) :=
    fun i => ⟨z i, r i, hr i, hgood i, rfl⟩
  have hint : ∀ (i : Fin m) (x : W), x ∈ K i →
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W := by
    intro i x hx hxb
    exact Set.disjoint_left.mp hdisjt hxb (Set.mem_iUnion.mpr ⟨i, hx⟩)
  have hζ_exists : ∀ i, ∃ a : Work.Orient.RelH W (n + 1) (K i), ∀ (x : W)
      (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (hxK : x ∈ K i),
      Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxK) a = γ x hx :=
    fun i => hγ.2 (K i) (hK i) (fun x hx => hint i x hx)
  choose hζ hζspec using hζ_exists
  have hglue : ∀ (i j : Fin m) (x : W) (hx : x ∈ K i ∩ K j),
      Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.1) (hζ i)
        = Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.2) (hζ j) := by
    intro i j x hx
    rw [hζspec i x (hint i x hx.1) hx.1, hζspec j x (hint j x hx.2) hx.2]
  obtain ⟨γ₀, hγ₀⟩ := Work.Orient.Boundary.HalfCoverGlue n W K hK hint hζ hglue
  refine ⟨Work.Orient.resRelH W (n + 1) hcov γ₀, ?_⟩
  intro x hx
  have h1 : Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)
        (Work.Orient.resRelH W (n + 1) hcov γ₀)
      = Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hcov hx)) γ₀ := by
    rw [show Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)
          (Work.Orient.resRelH W (n + 1) hcov γ₀)
        = ((Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)).comp
            (Work.Orient.resRelH W (n + 1) hcov)) γ₀ from rfl]
    rw [RelHmap_comp' W (n + 1) (Set.singleton_subset_iff.mpr hx) hcov
      (Set.singleton_subset_iff.mpr (hcov hx))]
  rw [h1]
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
  have h2 : Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hcov hx)) γ₀
      = Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxi) (hζ i) := by
    rw [← hγ₀ i, ← LinearMap.comp_apply,
      ← RelHmap_point_fac W (n + 1) (Set.subset_iUnion K i) hxi]
  rw [h2, hζspec i x (hint i x hxi) hxi]


/-! ## The zero section of the disc bundle -/

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The zero-section point of the disc bundle over `x`. -/
abbrev zeroSecDisc {E : PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) (x : V.pt) :
    Work.Tubular.NormalDiscSub E ε :=
  ⟨Work.Tubular.zeroSectionNormal E x, by
    rw [Work.Tubular.mem_normalClosedDiscSet]
    simpa [Work.Tubular.normalNorm] using hε.le⟩

theorem continuous_zeroSecDisc {E : PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (hε : 0 < ε) : Continuous (zeroSecDisc (E := E) hε) :=
  Continuous.subtype_mk (Work.Tubular.zeroSectionNormal E).continuous _

/-- The zero section of the disc bundle, as a subset. -/
abbrev zeroSecSet {E : PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) :
    Set (Work.Tubular.NormalDiscSub E ε) :=
  Set.range (zeroSecDisc (E := E) hε)

theorem isCompact_zeroSecSet {E : PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) :
    IsCompact (zeroSecSet (E := E) hε) :=
  isCompact_range (continuous_zeroSecDisc (E := E) hε)

/-- **The disc-level localisation is surjective.**  For the disc bundle `D_ε(ν)` of the normal
bundle of `E`, with `Z ⊆ D_ε(ν)` the zero section, the restriction
`H_n(D, D∖Z) → H_n(D, D∖{0_x})` (at the degree `n = 7 + k + 1` of the half-space model) is onto.
It is onto because the half-orientation family of the disc bundle glues to a class over the whole
zero section whose local class at `0_x` generates. -/
theorem disc_locH_surjective [NeZero k] (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (R : Work.Tubular.DiscManifold.HalfModelReindex k) (x : V.pt)
    (hsub : ({zeroSecDisc (E := E) C.eps_pos x} : Set (Work.Tubular.NormalDiscSub E ε))
      ⊆ zeroSecSet (E := E) C.eps_pos) :
    Function.Surjective (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalDiscSub E ε))
      (7 + k + 1) hsub) := by
  letI : ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.chartedSpace_normalDisc_add C R
  obtain ⟨γ, hγ⟩ := Work.Tubular.exists_halfOrientationFamily_normalDiscSub C R
  have hnormZero : ∀ x' : V.pt, Work.Tubular.normalNorm E
      (zeroSecDisc (E := E) C.eps_pos x' : Work.Tubular.NormalTotal E) = 0 := by
    intro x'
    simp [Work.Tubular.normalNorm]
  have hCint : ∀ y ∈ zeroSecSet (E := E) C.eps_pos,
      y ∉ (modelWithCornersEuclideanHalfSpace (7 + k + 1)).boundary
        (Work.Tubular.NormalDiscSub E ε) := by
    intro y hy hb
    obtain ⟨x', rfl⟩ := hy
    rw [Work.Tubular.mem_boundary_normalDiscSub_add C R] at hb
    rw [hnormZero x'] at hb
    exact (ne_of_gt C.eps_pos) hb.symm
  haveI : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.compactSpace_normalDiscSub E ε
  obtain ⟨u, hu⟩ := exists_coreClass_charted (7 + k) (TopCat.of (Work.Tubular.NormalDiscSub E ε))
    (isCompact_zeroSecSet (E := E) C.eps_pos) hCint γ hγ
  have hxl : zeroSecDisc (E := E) C.eps_pos x ∈ zeroSecSet (E := E) C.eps_pos :=
    Set.mem_range_self (f := zeroSecDisc (E := E) C.eps_pos) x
  -- the local class of `u` at `0_x` generates
  have hspan : Submodule.span ℤ ({(Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalDiscSub E ε))
      (7 + k + 1) hsub u)} : Set ((Work.Cohomology.relChains
        (TopCat.of (Work.Tubular.NormalDiscSub E ε))
        ({zeroSecDisc (E := E) C.eps_pos x} : Set (Work.Tubular.NormalDiscSub E ε))ᶜ).homology
          (7 + k + 1))) = ⊤ := by
    rw [show Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalDiscSub E ε)) (7 + k + 1) hsub
        = Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalDiscSub E ε)) (7 + k + 1)
            (Set.singleton_subset_iff.mpr hxl) from rfl]
    rw [hu (zeroSecDisc (E := E) C.eps_pos x) hxl]
    exact hγ.1 (zeroSecDisc (E := E) C.eps_pos x) (hCint _ hxl)
  have hrange : LinearMap.range (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalDiscSub E ε))
      (7 + k + 1) hsub) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hspan]
    exact Submodule.span_le.mpr (fun v hv => by
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨u, rfl⟩)
  exact LinearMap.range_eq_top.mp hrange

/-! ## Part II: the transfer from the disc bundle to the normal total space -/

section Transfer

variable {E : PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}

/-- Continuity of the radial capping. -/
theorem continuous_capEnd (hε : 0 < ε) : Continuous (cap E ε) := by
  refine Continuous.subtype_mk ?_ _
  exact Continuous.prodMk continuous_subtype_val.fst
    (((Work.ThomBordism.continuous_capCoeff hε).comp (Work.Tubular.continuous_normalNorm E)).smul
      continuous_subtype_val.snd)

/-- The radial capping as an endomorphism of the normal total space. -/
noncomputable def capEnd (hε : 0 < ε) :
    C(Work.Tubular.NormalTotal E, Work.Tubular.NormalTotal E) :=
  ⟨cap E ε, continuous_capEnd hε⟩

/-- The radial capping as a map into the disc bundle. -/
noncomputable def capToDisc (hε : 0 < ε) :
    C(Work.Tubular.NormalTotal E, Work.Tubular.NormalDiscSub E ε) :=
  ⟨fun p => ⟨cap E ε p, cap_mem_disc E hε.le p⟩,
    Continuous.subtype_mk (continuous_capEnd hε) _⟩

@[simp] theorem capToDisc_apply (hε : 0 < ε) (p : Work.Tubular.NormalTotal E) :
    ((capToDisc (E := E) hε p : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E)
      = cap E ε p := rfl

@[simp] theorem capEnd_apply (hε : 0 < ε) (p : Work.Tubular.NormalTotal E) :
    capEnd (E := E) hε p = cap E ε p := rfl

/-- The capping fixes the disc bundle pointwise. -/
theorem capToDisc_eq_self (hε : 0 < ε) (p : Work.Tubular.NormalDiscSub E ε) :
    capToDisc (E := E) hε p = p := by
  apply Subtype.ext
  exact Work.ThomBordism.cap_eq_self_of_le E hε.le p.2

/-- The homotopy from the capping to the identity, through positive radial rescalings. -/
noncomputable def capEndHomotopy (hε : 0 < ε) :
    TopCat.Homotopy (TopCat.ofHom (capEnd (E := E) hε))
      (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) :=
  Work.ThomBordism.radialRescaleHomotopyTop E (Work.ThomBordism.capCoeff ε)
    (Work.ThomBordism.continuous_capCoeff hε) (continuous_capEnd hε)

/-- The basic characterisation of the zero section of the normal bundle. -/
theorem mem_range_zeroSectionNormal_iff (E : PontryaginThom.EmbeddingData V (8 + k))
    (p : Work.Tubular.NormalTotal E) :
    p ∈ Set.range (Work.Tubular.zeroSectionNormal E) ↔
      ((p : V.pt × Work.Tubular.Euc (8 + k)).2) = 0 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    rw [← hy, Work.Tubular.zeroSectionNormal_apply]
  · intro h
    exact mem_range_zeroSectionNormal_of_vec_eq_zero E h

/-- The capping preserves the zero section. -/
theorem cap_mem_range_iff (hε : 0 < ε) (p : Work.Tubular.NormalTotal E) :
    cap E ε p ∈ Set.range (Work.Tubular.zeroSectionNormal E) ↔
      p ∈ Set.range (Work.Tubular.zeroSectionNormal E) := by
  have hne : Work.ThomBordism.capCoeff ε (Work.Tubular.normalNorm E p) ≠ 0 :=
    ne_of_gt (Work.ThomBordism.capCoeff_pos hε _ (Work.Tubular.normalNorm_nonneg E p))
  rw [mem_range_zeroSectionNormal_iff, mem_range_zeroSectionNormal_iff]
  change (Work.ThomBordism.capCoeff ε (Work.Tubular.normalNorm E p) •
      ((p : V.pt × Work.Tubular.Euc (8 + k)).2)) = 0 ↔
    ((p : V.pt × Work.Tubular.Euc (8 + k)).2) = 0
  rw [smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hne
    · exact h
  · exact Or.inr

/-- The radial homotopy preserves the complement of the zero section. -/
theorem capEndHomotopy_mem_range_ne (hε : 0 < ε) {t : unitInterval}
    {p : Work.Tubular.NormalTotal E}
    (hp : p ∉ Set.range (Work.Tubular.zeroSectionNormal E)) :
    (capEndHomotopy (E := E) hε) (t, p) ∉
      Set.range (Work.Tubular.zeroSectionNormal E) := by
  have hp' : p ∈ Work.Tubular.normalNonzero E := by
    rw [← Work.ThomBordism.compl_range_zeroSectionNormal E]
    simpa using hp
  have h := Work.ThomBordism.radialRescaleHomotopyFun_mem_normalNonzero E
    (Work.ThomBordism.capCoeff ε) (Work.ThomBordism.capCoeff_pos hε) (t := t) hp'
  show Work.ThomBordism.radialRescaleHomotopyFun E (Work.ThomBordism.capCoeff ε) (t, p)
    ∉ Set.range (Work.Tubular.zeroSectionNormal E)
  rw [← Set.mem_compl_iff, Work.ThomBordism.compl_range_zeroSectionNormal E]
  exact h

/-- The radial homotopy preserves the complement of the zero-section point over `x`. -/
theorem capEndHomotopy_ne_zeroSection (hε : 0 < ε) (x : V.pt) {t : unitInterval}
    {p : Work.Tubular.NormalTotal E} (hp : p ≠ Work.Tubular.zeroSectionNormal E x) :
    (capEndHomotopy (E := E) hε) (t, p) ≠ Work.Tubular.zeroSectionNormal E x := by
  intro hcon
  apply hp
  have hbase : ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1 = x := by
    have hh := congrArg (fun q : Work.Tubular.NormalTotal E =>
      ((q : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1) hcon
    change ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1 = x at hh
    exact hh
  have hmem : p ∈ Set.range (Work.Tubular.zeroSectionNormal E) := by
    by_contra hnot
    exact capEndHomotopy_mem_range_ne (E := E) hε hnot
      (hcon.symm ▸ Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x)
  have hvec : ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).2 = 0 :=
    (mem_range_zeroSectionNormal_iff (E := E) p).mp hmem
  apply Work.Tubular.NormalTotal.ext
  exact Prod.ext hbase hvec

end Transfer


/-- **The capping fixes exactly the fibre of the zero section over a given base point.** -/
theorem cap_eq_zeroSection_iff {E : PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (hε : 0 < ε) (x : V.pt) (p : Work.Tubular.NormalTotal E) :
    cap E ε p = Work.Tubular.zeroSectionNormal E x ↔
      p = Work.Tubular.zeroSectionNormal E x := by
  constructor
  · intro h
    have hmem : p ∈ Set.range (Work.Tubular.zeroSectionNormal E) := by
      rw [← cap_mem_range_iff (E := E) hε p]
      exact ⟨x, h.symm⟩
    have hvec : ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).2 = 0 :=
      (mem_range_zeroSectionNormal_iff (E := E) p).mp hmem
    have hbase : ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1 = x := by
      have hh := congrArg (fun q : Work.Tubular.NormalTotal E =>
        ((q : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1) h
      change ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1
        = x at hh
      exact hh
    apply Work.Tubular.NormalTotal.ext
    exact Prod.ext hbase hvec
  · intro h
    rw [h]
    exact Work.ThomBordism.cap_eq_self_of_le E hε.le (by
      simp [Work.Tubular.normalNorm, hε.le])



/-! ## Part III: the transfer and the main theorem -/

/-- **A map of pairs which is a homotopy retraction induces a surjection on relative homology.**
If `g` is a right homotopy inverse of `f` through maps of the pair `(Y, Y∖K')`, then `f` is
surjective on the relative homology of the pairs `(X, X∖K) → (Y, Y∖K')`. -/
theorem surjective_relHmapOf_of_homotopy_retract {X Y : TopCat} {n : ℕ} (f : X ⟶ Y) (g : Y ⟶ X)
    {K : Set X} {K' : Set Y} (hf : ∀ x, x ∉ K → f x ∉ K') (hg : ∀ y, y ∉ K' → g y ∉ K)
    (Hf : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (hHf : ∀ t y, y ∉ K' → Hf (t, y) ∉ K') :
    Function.Surjective (Work.PTGeometric.HOF.RelHmapOf n f K K' hf) := by
  have hgf : ∀ y : Y, y ∉ K' → (g ≫ f) y ∉ K' := fun y hy => hf (g y) (hg y hy)
  have hcomp : (Work.PTGeometric.HOF.RelHmapOf n f K K' hf).comp
      (Work.PTGeometric.HOF.RelHmapOf n g K' K hg) = LinearMap.id := by
    rw [Work.PTGeometric.HOF.RelHmapOf_comp (n := n) g f hg hf hgf]
    have hbridge : Work.PTGeometric.HOF.RelHmapOf n (g ≫ f) K' K' hgf
        = Work.PTGeometric.HOF.RelHmapOf n (𝟙 Y) K' K' (fun y hy => hy) :=
      Work.PTGeometric.HOF.RelHmapOf_homotopic (n := n) hgf (fun y hy => hy) Hf hHf
    rw [hbridge, Work.PTGeometric.HOF.RelHmapOf_id (n := n) K']
  intro y
  refine ⟨Work.PTGeometric.HOF.RelHmapOf n g K' K hg y, ?_⟩
  have h := LinearMap.congr_fun hcomp y
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  exact h

/-- **The assembly of the surjectivity transfer.**  If the localisation in `X` is surjective, and
the two maps of pairs `(X,X∖K₂) → (Y,Y∖K'₂)` and `(X,X∖K₁) → (Y,Y∖K'₁)` are surjective and
compatible with the localisations, then the localisation in `Y` is surjective. -/
theorem surjective_resRelH_of_surjective {X Y : TopCat} {n : ℕ} (f : X ⟶ Y)
    {K₁ K₂ : Set X} {K'₁ K'₂ : Set Y} (hX : K₁ ⊆ K₂) (hY : K'₁ ⊆ K'₂)
    (hf₁ : ∀ x, x ∉ K₁ → f x ∉ K'₁) (hf₂ : ∀ x, x ∉ K₂ → f x ∉ K'₂)
    (hsurj₂ : Function.Surjective (Work.PTGeometric.HOF.RelHmapOf n f K₂ K'₂ hf₂))
    (hsurj₁ : Function.Surjective (Work.PTGeometric.HOF.RelHmapOf n f K₁ K'₁ hf₁))
    (hD : Function.Surjective (Work.Orient.resRelH X n hX)) :
    Function.Surjective (Work.Orient.resRelH Y n hY) := by
  have hnat := Work.PTGeometric.HOF.RelHmapOf_resRelH (n := n) f hX hY hf₂ hf₁
  intro y
  obtain ⟨y', hy'⟩ := hsurj₁ y
  obtain ⟨z, hz⟩ := hD y'
  refine ⟨Work.PTGeometric.HOF.RelHmapOf n f K₂ K'₂ hf₂ z, ?_⟩
  have hsq : (Work.PTGeometric.HOF.RelHmapOf n f K₁ K'₁ hf₁)
      ((Work.Orient.resRelH X n hX) z) = (Work.Orient.resRelH Y n hY)
        ((Work.PTGeometric.HOF.RelHmapOf n f K₂ K'₂ hf₂) z) := by
    have hh := LinearMap.congr_fun hnat z
    simpa only [LinearMap.comp_apply] using hh
  rw [← hsq, hz, hy']

/-- **The localisation at a point of the zero section of the normal bundle is surjective**, in the
degree `7 + k + 1` of the half-space model.

The capping `p ↦ (proj p, min(1, ε/‖p‖) • vec p)` maps the normal total space into the disc bundle
`D_ε(ν)` and is the identity on it; it is homotopic to the identity through positive radial
rescalings, which preserve both `ν∖0` and `ν∖{0_x}`.  Hence the inclusion of the disc bundle induces
surjections on the relative homology of the pairs `(·, ·∖0(V))` and `(·, ·∖{0_x})`, and it is
compatible with the localisation; the surjectivity of the latter on `D_ε(ν)` (proved from the
half-orientation family of the disc bundle) transfers. -/
theorem normalTotal_locH_surjective_deg7 [NeZero k] [Nonempty V.pt]
    (E : PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (hsub : ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))
      ⊆ Set.range (Work.Tubular.zeroSectionNormal E)) :
    Function.Surjective (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalTotal E))
      (7 + k + 1) hsub) := by
  classical
  obtain ⟨ε, hε, ⟨C⟩⟩ := Work.Tubular.hasTubularNeighbourhood E
  obtain ⟨R⟩ := Work.Tubular.DiscManifold.exists_halfModelReindex k
  -- the inclusion of the disc bundle and the capping
  let ι : TopCat.of (Work.Tubular.NormalDiscSub E ε) ⟶ TopCat.of (Work.Tubular.NormalTotal E) :=
    Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalClosedDiscSet E ε)
  let cT : TopCat.of (Work.Tubular.NormalTotal E) ⟶ TopCat.of (Work.Tubular.NormalDiscSub E ε) :=
    TopCat.ofHom (capToDisc (E := E) hε)
  have hxD : zeroSecDisc (E := E) hε x ∈ zeroSecSet (E := E) hε :=
    Set.mem_range_self (f := zeroSecDisc (E := E) hε) x
  have hDsub : ({zeroSecDisc (E := E) hε x} : Set (Work.Tubular.NormalDiscSub E ε))
      ⊆ zeroSecSet (E := E) hε := Set.singleton_subset_iff.mpr hxD
  -- the preservation conditions
  have hfZ : ∀ q : Work.Tubular.NormalDiscSub E ε, q ∉ zeroSecSet (E := E) hε →
      ι q ∉ Set.range (Work.Tubular.zeroSectionNormal E) := by
    intro q hq hcon
    apply hq
    have hq' : ((q : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).2 = 0 :=
      (mem_range_zeroSectionNormal_iff (E := E) (q : Work.Tubular.NormalTotal E)).mp hcon
    refine ⟨((q : Work.Tubular.NormalTotal E)).proj, ?_⟩
    apply Subtype.ext
    apply Work.Tubular.NormalTotal.ext
    exact Prod.ext rfl (by simpa using hq'.symm)
  have hfx : ∀ q : Work.Tubular.NormalDiscSub E ε,
      q ∉ ({zeroSecDisc (E := E) hε x} : Set (Work.Tubular.NormalDiscSub E ε)) →
      ι q ∉ ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E)) := by
    intro q hq hcon
    apply hq
    apply Subtype.ext
    exact hcon
  have hfc : ∀ p : Work.Tubular.NormalTotal E,
      p ∉ Set.range (Work.Tubular.zeroSectionNormal E) → cT p ∉ zeroSecSet (E := E) hε := by
    intro p hp hcon
    apply hp
    have hmem : ((cT p : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E)
        ∈ Set.range (Work.Tubular.zeroSectionNormal E) := by
      obtain ⟨x', hx'⟩ := hcon
      rw [← hx']
      exact Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x'
    rw [← cap_mem_range_iff (E := E) hε p]
    exact hmem
  have hfcx : ∀ p : Work.Tubular.NormalTotal E,
      p ∉ ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E)) →
      cT p ∉ ({zeroSecDisc (E := E) hε x} : Set (Work.Tubular.NormalDiscSub E ε)) := by
    intro p hp hcon
    apply hp
    have h1 : ((cT p : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E)
        = Work.Tubular.zeroSectionNormal E x := by
      rw [hcon]
    exact (cap_eq_zeroSection_iff (E := E) hε x p).mp h1
  -- the capping composed with the inclusion is homotopic to the identity on both pairs
  let Hf : TopCat.Homotopy (cT ≫ ι) (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) :=
    { toContinuousMap := Work.ThomBordism.radialRescaleHomotopy E (Work.ThomBordism.capCoeff ε)
        (Work.ThomBordism.continuous_capCoeff hε)
      map_zero_left := fun p => by
        show Work.ThomBordism.radialRescaleHomotopyFun E (Work.ThomBordism.capCoeff ε)
          ((0 : unitInterval), p) = (cT ≫ ι) p
        rw [Work.ThomBordism.radialRescaleHomotopyFun_zero]
        rfl
      map_one_left := fun p => by
        show Work.ThomBordism.radialRescaleHomotopyFun E (Work.ThomBordism.capCoeff ε)
          ((1 : unitInterval), p) = (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) p
        rw [Work.ThomBordism.radialRescaleHomotopyFun_one]
        rfl }
  have hHf : ∀ t y, y ∉ Set.range (Work.Tubular.zeroSectionNormal E) →
      Hf (t, y) ∉ Set.range (Work.Tubular.zeroSectionNormal E) :=
    fun t y hy => capEndHomotopy_mem_range_ne (E := E) hε hy
  have hHfx : ∀ t y, y ∉ ({Work.Tubular.zeroSectionNormal E x} :
      Set (Work.Tubular.NormalTotal E)) →
      Hf (t, y) ∉ ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E)) :=
    fun t y hy => capEndHomotopy_ne_zeroSection (E := E) hε x hy
  -- the two surjectivities of the inclusion
  have hsurjZ := surjective_relHmapOf_of_homotopy_retract (n := 7 + k + 1) ι cT hfZ hfc Hf hHf
  have hsurjx := surjective_relHmapOf_of_homotopy_retract (n := 7 + k + 1) ι cT hfx hfcx Hf hHfx
  -- the disc-level statement
  have hD := disc_locH_surjective (k := k) (V := V) E C R x hDsub
  exact surjective_resRelH_of_surjective (n := 7 + k + 1) ι hDsub hsub hfx hfZ hsurjZ hsurjx hD

/-- **The localisation of the top relative homology of the normal bundle at a point of the zero
section is surjective.**

For the normal bundle `ν = NormalTotal E` of the embedding `E : V ↪ ℝ^{8+k}` of a connected closed
oriented smooth `8`-manifold and a point `x : V.pt`, the restriction

  `H_{8+k}(ν, ν∖0(V)) ⟶ H_{8+k}(ν, ν∖{0_x})`

is onto.  The proof is `normalTotal_locH_surjective_deg7`, transported across the numerically equal
degrees `7 + k + 1` and `8 + k`. -/
theorem normalTotal_locH_surjective {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
          (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x)))) (8 + k)).hom := by
  haveI : NeZero k := ⟨by omega⟩
  haveI : Nonempty V.pt := ConnectedSpace.toNonempty
  have h7 := normalTotal_locH_surjective_deg7 (V := V) (k := k) E x
    (Set.singleton_subset_iff.mpr (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x))
  show Function.Surjective (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalTotal E))
    (8 + k) (Set.singleton_subset_iff.mpr
      (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x)))
  suffices ∀ (N : ℕ), N = 7 + k + 1 →
      Function.Surjective (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalTotal E)) N
        (Set.singleton_subset_iff.mpr
          (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x))) by
    exact this (8 + k) (by omega)
  intro N hN
  subst hN
  exact h7


end

end Work.ThomBordism
