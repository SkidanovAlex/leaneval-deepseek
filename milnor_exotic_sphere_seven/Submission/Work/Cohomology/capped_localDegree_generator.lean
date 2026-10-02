import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.localHomology
import Submission.Work.Milnor.homology_capped_compact
import Submission.Work.Cohomology.Duality.convex_compl_sphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local degree of a generator of `H₈(X)` is a generator

Let `X = cappedSpace (cappedDatum F hF)` be the closed `8`-manifold `D(ξ) ∪_F D⁸` obtained by
gluing the disc bundle `ξ = Vk (-2)` to a disc along the capping diffeomorphism `F`, and let
`c ∈ H₈(X; ℤ)` be a generator (so `X` is orientable and `c = ±[X]`).  The file proves that the
image of `c` in the local homology `H₈(X, X ∖ {x}; ℤ) ≅ ℤ` is a generator for *every* `x ∈ X`,
i.e. that every generator of the top homology of `X` is a fundamental class.

The route: the connecting map of the pair `(X, X∖{x})` identifies `H₈(X, X∖{x}) → H₇(X∖{x})` with
the cokernel of `H₈(X) → H₈(X, X∖{x})`; since `H₇(X) = 0`, the image of a generator is a generator
as soon as `H₇(X ∖ {x}) = 0`, which is what is proved:

* `isZero_relChains_punctured_euclid` — the Euclidean input: for compact convex `K ∋ z`, the pair
  `(ℝᴺ∖{z}, ℝᴺ∖K)` has vanishing relative homology (a compatible copy of
  `Work.Cohomology.isZero_relChains_punctured`, needed here because that module clashes with
  `localCohomology`'s `chainMap_comp'`);
* `chartPunctCoverHomeo`, `isZero_relChains_punctured_chart` — the same for a chart-convex compact
  set `K'` inside a coordinate ball of an `N`-manifold (excision, the chart homeomorphism, and
  excision in `ℝᴺ`);
* `isZero_homology_compl_iff_of_mem_chartBall` — **local constancy**: `H₇(M ∖ {z}) = 0` is
  equivalent for points `z` of a common chart-convex compact set (both are isomorphic to
  `H₇(M ∖ K)`);
* `glueU_eq_compl_ιY_zero`, `isZero_homology_compl_capCentre` — the base case: the complement of
  the cap centre is the disc-bundle piece, whose `H₇` vanishes;
* the set of points where `H₇(X ∖ {z}) = 0` is clopen, so it is all of the connected `X`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section


/-- The radial scaling factor of the retraction of `ℝᴺ ∖ {z}` onto the complement of a compact
convex set contained in the ball of radius `R` about `z`: it is `max 1 (R / ‖x - z‖)`, so that the
image of `x` lies at distance at least `R` from `z` (and equals `x` when `‖x - z‖ ≥ R`). -/
noncomputable def euclidRadialScale (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ := max 1 (R / ‖x - z‖)

/-- The scaling factor is at least `1`. -/
theorem euclidRadialScale_one_le (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : 1 ≤ euclidRadialScale N z R x := le_max_left _ _

/-- **The image of `x ≠ z` under the radial retraction lies at distance at least `R` from `z`.** -/
theorem euclidRadialScale_mul_norm_ge (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ≠ z) :
    R ≤ euclidRadialScale N z R x * ‖x - z‖ := by
  have hd : ‖x - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  unfold euclidRadialScale
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), div_mul_cancel₀ _ hd]
  exact le_max_right _ _

/-- The scaling factor along the straight-line homotopy from the identity to the radial
retraction: `(1 - t) + t · max 1 (R / ‖x - z‖)`. -/
noncomputable def euclidHomScale (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ := (1 - t) + t * euclidRadialScale N z R x

/-- The homotopy scaling factor is at least `1` for `t ≥ 0`. -/
theorem euclidHomScale_one_le (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ) (t : ℝ)
    (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin N)) : 1 ≤ euclidHomScale N z R t x := by
  have hc : 1 ≤ euclidRadialScale N z R x := euclidRadialScale_one_le N z R x
  have := mul_le_mul_of_nonneg_left hc ht
  simp only [euclidHomScale]; linarith

/-- **The relative homology of the punctured space vanishes.**

For `K ⊆ ℝᴺ` a nonempty compact convex set (`N ≥ 1`) and `z ∈ K`, the pair
`(ℝᴺ ∖ {z}, ℝᴺ ∖ K)` has trivial relative singular homology in every degree. -/
theorem isZero_relChains_punctured_euclid (N : ℕ) (hN : 1 ≤ N)
    (z : EuclideanSpace ℝ (Fin N)) (K : Set (EuclideanSpace ℝ (Fin N)))
    (hKc : IsCompact K) (hconv : Convex ℝ K) (hz : z ∈ K) :
    ∀ i : ℕ, CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ≠ z})
      {y : {y : EuclideanSpace ℝ (Fin N) | y ≠ z} | (y : EuclideanSpace ℝ (Fin N)) ∉ K}).homology i) := by
  obtain ⟨R, hR, hsub⟩ := hKc.isBounded.subset_ball_lt 0 z
  let X : TopCat := TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ≠ z}
  let A : Set X := {y | (y : EuclideanSpace ℝ (Fin N)) ∉ K}
  have hxn : Continuous fun x : ↥X => (x : EuclideanSpace ℝ (Fin N)) := continuous_subtype_val
  have hnorm : Continuous fun x : ↥X => ‖(x : EuclideanSpace ℝ (Fin N)) - z‖ :=
    (hxn.sub continuous_const).norm
  have hne : ∀ x : ↥X, ‖(x : EuclideanSpace ℝ (Fin N)) - z‖ ≠ 0 :=
    fun x => norm_ne_zero_iff.mpr (sub_ne_zero.mpr x.2)
  have hdiv : Continuous fun x : ↥X => R / ‖(x : EuclideanSpace ℝ (Fin N)) - z‖ :=
    continuous_const.div hnorm hne
  have hscale : Continuous fun x : ↥X => euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) := by
    unfold euclidRadialScale; exact continuous_const.max hdiv
  have hGcont : Continuous fun x : ↥X =>
      z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) • ((x : EuclideanSpace ℝ (Fin N)) - z) :=
    continuous_const.add (hscale.smul (hxn.sub continuous_const))
  have hGne : ∀ x : ↥X, z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
      ((x : EuclideanSpace ℝ (Fin N)) - z) ≠ z := by
    intro x h
    have hc : euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
      have h1 := euclidRadialScale_one_le N z R (x : EuclideanSpace ℝ (Fin N))
      intro h0; rw [h0] at h1; norm_num at h1
    have hv : (x : EuclideanSpace ℝ (Fin N)) - z ≠ 0 := sub_ne_zero.mpr x.2
    have h4 : z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z) - z = 0 := by rw [h, sub_self]
    rw [add_sub_cancel_left] at h4
    exact smul_ne_zero hc hv h4
  have hGnotK : ∀ x : ↥X, z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
      ((x : EuclideanSpace ℝ (Fin N)) - z) ∉ K := by
    intro x hmem
    have hb : dist (z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z)) z < R := by
      have := hsub hmem; rwa [Metric.mem_ball] at this
    have hc0 : 0 ≤ euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) :=
      le_trans zero_le_one (euclidRadialScale_one_le N z R (x : EuclideanSpace ℝ (Fin N)))
    have hge : R ≤ dist (z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z)) z := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      exact euclidRadialScale_mul_norm_ge N z R (x : EuclideanSpace ℝ (Fin N)) x.2
    linarith
  -- the radial retraction `ℝᴺ ∖ {z} ⟶ ℝᴺ ∖ K`
  let g : X ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun x => ⟨⟨z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z), hGne x⟩, hGnotK x⟩,
      hGcont.subtype_mk hGne |>.subtype_mk hGnotK⟩
  let f : TopCat.of A ⟶ X := subtypeIncl X A
  -- the straight-line homotopy on `ℝᴺ ∖ {z}`
  have hXs : Continuous fun q : ↑unitInterval × ↥X =>
      euclidHomScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) := by
    unfold euclidHomScale
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul (hscale.comp continuous_snd))
  have hX1 : ∀ q : ↑unitInterval × ↥X,
      1 ≤ euclidHomScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) :=
    fun q => euclidHomScale_one_le N z R (q.1:ℝ) q.1.2.1 (q.2 : EuclideanSpace ℝ (Fin N))
  have hXmem : ∀ q : ↑unitInterval × ↥X,
      z + euclidHomScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
        ((q.2 : EuclideanSpace ℝ (Fin N)) - z) ≠ z := by
    intro q h
    have hs0 : euclidHomScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
      have h1 := hX1 q; linarith
    have hv : (q.2 : EuclideanSpace ℝ (Fin N)) - z ≠ 0 := sub_ne_zero.mpr q.2.2
    have h4 : z + euclidHomScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
        ((q.2 : EuclideanSpace ℝ (Fin N)) - z) - z = 0 := by rw [h, sub_self]
    rw [add_sub_cancel_left] at h4
    exact smul_ne_zero hs0 hv h4
  have hXbase : Continuous fun q : ↑unitInterval × ↥X =>
      z + euclidHomScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
        ((q.2 : EuclideanSpace ℝ (Fin N)) - z) :=
    continuous_const.add (hXs.smul
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const))
  let HXF : C(↑unitInterval × ↥X, ↥X) :=
    ⟨fun q => ⟨z + euclidHomScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
      ((q.2 : EuclideanSpace ℝ (Fin N)) - z), hXmem q⟩, hXbase.subtype_mk hXmem⟩
  have H0X : TopCat.Homotopy (𝟙 X) (g ≫ f) :=
    ContinuousMap.Homotopy.mk HXF
      (fun x => by
        change HXF (0, x) = x
        apply Subtype.ext
        show z + euclidHomScale N z R (((0:↑unitInterval):ℝ)) (x : EuclideanSpace ℝ (Fin N)) •
          ((x : EuclideanSpace ℝ (Fin N)) - z) = (x : EuclideanSpace ℝ (Fin N))
        simp only [euclidHomScale]; norm_num)
      (fun x => by
        have hgf : (g ≫ f).hom x = (⟨z + euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
            ((x : EuclideanSpace ℝ (Fin N)) - z), hGne x⟩ : ↥X) := rfl
        rw [hgf]
        apply Subtype.ext
        show z + euclidHomScale N z R (((1:↑unitInterval):ℝ)) (x : EuclideanSpace ℝ (Fin N)) •
          ((x : EuclideanSpace ℝ (Fin N)) - z) = z +
          euclidRadialScale N z R (x : EuclideanSpace ℝ (Fin N)) • ((x : EuclideanSpace ℝ (Fin N)) - z)
        simp only [euclidHomScale]; norm_num)
  -- the same homotopy, restricted to `ℝᴺ ∖ K`
  have htA : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hAxn : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) => (q.2 : ↥X) :=
    continuous_subtype_val.comp continuous_snd
  have hAxn2 : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) =>
      ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) := continuous_subtype_val.comp hAxn
  have hAne0 : ∀ q : ↑unitInterval × ↥(TopCat.of A),
      ‖((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z‖ ≠ 0 :=
    fun q => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (q.2 : ↥X).2)
  have hAscale : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) =>
      euclidRadialScale N z R ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) := by
    unfold euclidRadialScale
    exact continuous_const.max (continuous_const.div (hAxn2.sub continuous_const).norm hAne0)
  have hAs : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) =>
      euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) := by
    unfold euclidHomScale
    exact (continuous_const.sub htA).add (htA.mul hAscale)
  have hAs1 : ∀ q : ↑unitInterval × ↥(TopCat.of A),
      1 ≤ euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) :=
    fun q => euclidHomScale_one_le N z R (q.1:ℝ) q.1.2.1 _
  have hAne : ∀ q : ↑unitInterval × ↥(TopCat.of A),
      z + euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) ≠ z := by
    intro q h
    have hs0 : euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
      have h1 := hAs1 q; linarith
    have hv : (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N))) - z ≠ 0 := sub_ne_zero.mpr (q.2 : ↥X).2
    have h4 : z + euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) - z = 0 := by rw [h, sub_self]
    rw [add_sub_cancel_left] at h4
    exact smul_ne_zero hs0 hv h4
  have hAnotK : ∀ q : ↑unitInterval × ↥(TopCat.of A),
      z + euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) ∉ K :=
    fun q => Duality.convex_ray_notMem K hconv z hz
      ⟨((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)), q.2.2⟩ _ (hAs1 q)
  have hAbase : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) =>
      z + euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) :=
    continuous_const.add (hAs.smul (hAxn2.sub continuous_const))
  let HAF : C(↑unitInterval × ↥(TopCat.of A), ↥(TopCat.of A)) :=
    ⟨fun q => ⟨⟨z + euclidHomScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z), hAne q⟩, hAnotK q⟩,
      (hAbase.subtype_mk hAne).subtype_mk hAnotK⟩
  have H0A : TopCat.Homotopy (𝟙 (TopCat.of A)) (f ≫ g) :=
    ContinuousMap.Homotopy.mk HAF
      (fun a => by
        change HAF (0, a) = a
        apply Subtype.ext; apply Subtype.ext
        show z + euclidHomScale N z R (((0:↑unitInterval):ℝ)) (((a : ↥X) : EuclideanSpace ℝ (Fin N))) •
          (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z) = ((a : ↥X) : EuclideanSpace ℝ (Fin N))
        simp only [euclidHomScale]; norm_num)
      (fun a => by
        have hfg : (f ≫ g).hom a = (⟨⟨z + euclidRadialScale N z R (((a : ↥X) : EuclideanSpace ℝ (Fin N))) •
            (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z), hGne (a : ↥X)⟩,
            hGnotK (a : ↥X)⟩ : ↥(TopCat.of A)) := rfl
        rw [hfg]
        apply Subtype.ext; apply Subtype.ext
        show z + euclidHomScale N z R (((1:↑unitInterval):ℝ)) (((a : ↥X) : EuclideanSpace ℝ (Fin N))) •
          (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z) = z + euclidRadialScale N z R
          (((a : ↥X) : EuclideanSpace ℝ (Fin N))) • (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z)
        simp only [euclidHomScale]; norm_num)
  -- the inclusion `ℝᴺ ∖ K ⟶ ℝᴺ ∖ {z}` is a homotopy equivalence, hence a quasi-isomorphism
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of A)) := H0A.symm
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 X) := H0X.symm
  have hq : QuasiIso (inclChains X A) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact homologyEquiv ℤ (TopCat.of A) X f g h1 h2 i
  -- hence the cokernel (the relative chain complex) is acyclic
  intro i
  exact (HomologicalComplex.exactAt_iff_isZero_homology (relChains X A) i).mp
    ((hPairShort_shortExact X A).acyclic_X₃ hq i)

/-- The chart homeomorphism between the punctured pieces of the two covers. -/
def chartPunctCoverHomeo (N : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (c : M) (r : ℝ) (hr : 0 < r) (z : M) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ c
    Metric.ball (e c) r ⊆ e.target →
    z ∈ e.source →
    ({w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r} ≃ₜ
      {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
        (v : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball (e c) r}) := by
  intro e hball hzsrc
  exact {
    toFun := fun w => ⟨⟨e (w.1.1), by
        intro h
        exact w.1.2 (e.toPartialEquiv.injOn w.2.1 hzsrc h)⟩, w.2.2⟩
    invFun := fun v => ⟨⟨e.symm (v.1.1), by
        intro h
        apply v.1.2
        calc v.1.1 = e (e.symm (v.1.1)) := (e.right_inv (hball v.2)).symm
          _ = e z := congrArg e h⟩, by
        have h1 : e (e.symm (v.1.1)) = v.1.1 := e.right_inv (hball v.2)
        have h2 : e (e.symm (v.1.1)) ∈ Metric.ball (e c) r := by rw [h1]; exact v.2
        exact ⟨e.map_target (hball v.2), h2⟩⟩
    left_inv := by
      intro w
      apply Subtype.ext
      apply Subtype.ext
      exact e.left_inv w.2.1
    right_inv := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      exact e.right_inv (hball v.2)
    continuous_toFun :=
      Continuous.subtype_mk
        (Continuous.subtype_mk
          (e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
            (fun w => w.2.1))
          (fun w => by
            intro h
            exact w.1.2 (e.toPartialEquiv.injOn w.2.1 hzsrc h)))
        (fun w => w.2.2)
    continuous_invFun :=
      Continuous.subtype_mk
        (Continuous.subtype_mk
          (e.symm.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
            (fun v => hball v.2))
          (fun v => by
            intro h
            apply v.1.2
            calc v.1.1 = e (e.symm (v.1.1)) := (e.right_inv (hball v.2)).symm
              _ = e z := congrArg e h))
        (fun v => by
          have h1 : e (e.symm (v.1.1)) = v.1.1 := e.right_inv (hball v.2)
          have h2 : e (e.symm (v.1.1)) ∈ Metric.ball (e c) r := by rw [h1]; exact v.2
          exact ⟨e.map_target (hball v.2), h2⟩) }


/-- **The vanishing of the relative homology of the punctured chart-ball pair.**

Let `M` be charted over `ℝ^N`, `c : M`, `e := chartAt _ c`, `r > 0` with `Metric.ball (e c) r ⊆ e.target`,
`K' ⊆ ℝ^N` compact convex with `K' ⊆ Metric.ball (e c) r`, and `z ∈ e ⁻¹' K' ∩ e.source`.
Then `H_i(M ∖ {z}, M ∖ K) = 0` for all `i`, where `K := e ⁻¹' K' ∩ e.source`. -/
theorem isZero_relChains_punctured_chart (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (c : M) (r : ℝ) (hr : 0 < r)
    (K' : Set (EuclideanSpace ℝ (Fin N))) (hKc : IsCompact K') (hconv : Convex ℝ K') :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ c
    Metric.ball (e c) r ⊆ e.target →
    K' ⊆ Metric.ball (e c) r →
    ∀ z : M, z ∈ e ⁻¹' K' ∩ e.source →
      ∀ i : ℕ, CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
        (TopCat.of {y : M | y ≠ z})
        {y : {y : M | y ≠ z} | (y : M) ∉ e ⁻¹' K' ∩ e.source}).homology i) := by
  intro e hball hKsub z hz i
  have hzsrc : z ∈ e.source := hz.2
  have hzK' : e z ∈ K' := hz.1
  have hzball : e z ∈ Metric.ball (e c) r := hKsub hzK'
  have hK'tgt : K' ⊆ e.target := fun v hv => hball (hKsub hv)
  -- the erased set is the image of the compact convex set, hence closed
  have hKeq : e ⁻¹' K' ∩ e.source = e.symm '' K' := by
    ext y; constructor
    · rintro ⟨h1, h2⟩; exact ⟨e y, h1, e.left_inv h2⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, e.map_target (hK'tgt hv)⟩
      show e (e.symm v) ∈ K'
      rw [e.right_inv (hK'tgt hv)]
      exact hv
  have hKclosed : IsClosed (e ⁻¹' K' ∩ e.source) := by
    rw [hKeq]
    exact (hKc.image_of_continuousOn (e.continuousOn_symm.mono hK'tgt)).isClosed
  -- the first two-cover, in `M ∖ {z}`
  let X : TopCat := TopCat.of {y : M | y ≠ z}
  have hUopen : IsOpen {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e ⁻¹' Metric.ball (e c) r} :=
    (e.isOpen_inter_preimage Metric.isOpen_ball).preimage continuous_subtype_val
  have hVopen : IsOpen {w : {y : M | y ≠ z} | (w : M) ∉ e ⁻¹' K' ∩ e.source} :=
    hKclosed.isOpen_compl.preimage continuous_subtype_val
  have hcov : {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r} ∪
      {w : {y : M | y ≠ z} | (w : M) ∉ e ⁻¹' K' ∩ e.source} = Set.univ := by
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : (w : M) ∈ e ⁻¹' K' ∩ e.source
    · left
      refine ⟨h.2, hKsub ?_⟩
      exact h.1
    · right; exact h
  obtain ⟨E1⟩ := homologyTwoCover X {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r}
    {w : {y : M | y ≠ z} | (w : M) ∉ e ⁻¹' K' ∩ e.source} hUopen hVopen hcov i
  refine CategoryTheory.Limits.IsZero.of_iso ?_ E1
  -- the chart identifies the punctured pieces of the two covers
  let Ψ := chartPunctCoverHomeo N (↥M) c r hr z hball hzsrc
  have hΨ : ∀ w : {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r},
      (Ψ w : EuclideanSpace ℝ (Fin N)) = e (w.1.1 : M) := fun w => rfl
  have hcorr : ∀ w : {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r},
      (w ∈ {y : {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r} |
          (y : {y : M | y ≠ z}) ∈ {w : {y : M | y ≠ z} | (w : M) ∉ e ⁻¹' K' ∩ e.source}} ↔
        Ψ w ∈ {v : {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
            (v : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball (e c) r} |
          ((v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z}) : EuclideanSpace ℝ (Fin N)) ∉ K'}) := by
    intro w
    show (w.1.1 : M) ∉ e ⁻¹' K' ∩ e.source ↔ (Ψ w : EuclideanSpace ℝ (Fin N)) ∉ K'
    rw [hΨ w]
    constructor
    · intro h hK'
      exact h ⟨hK', w.2.1⟩
    · intro h hcon
      exact h hcon.1
  obtain ⟨E2⟩ := relChains_homeomorph
    {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r}
    {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
      (v : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball (e c) r}
    {y : {w : {y : M | y ≠ z} | (w : M) ∈ e.source ∩ e⁻¹' Metric.ball (e c) r} |
      (y : {y : M | y ≠ z}) ∈ {w : {y : M | y ≠ z} | (w : M) ∉ e ⁻¹' K' ∩ e.source}}
    {v : {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
        (v : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball (e c) r} |
      (v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z}) ∈
        {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} | (v : EuclideanSpace ℝ (Fin N)) ∉ K'}}
    Ψ hcorr i
  refine CategoryTheory.Limits.IsZero.of_iso ?_ E2
  -- the second two-cover, in `ℝ^N ∖ {e z}`
  let X' : TopCat := TopCat.of {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z}
  have hU'open : IsOpen {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
      (v : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball (e c) r} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hK'closed : IsClosed K' := hKc.isClosed
  have hV'open : IsOpen {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
      (v : EuclideanSpace ℝ (Fin N)) ∉ K'} :=
    hK'closed.isOpen_compl.preimage continuous_subtype_val
  have hcov' : {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
      (v : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball (e c) r} ∪
      {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
        (v : EuclideanSpace ℝ (Fin N)) ∉ K'} = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : (v : EuclideanSpace ℝ (Fin N)) ∈ K'
    · left; exact hKsub h
    · right; exact h
  obtain ⟨E3⟩ := homologyTwoCover X'
    {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
      (v : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball (e c) r}
    {v : {ζ : EuclideanSpace ℝ (Fin N) | ζ ≠ e z} |
      (v : EuclideanSpace ℝ (Fin N)) ∉ K'} hU'open hV'open hcov' i
  refine CategoryTheory.Limits.IsZero.of_iso ?_ E3.symm
  exact isZero_relChains_punctured_euclid N hN (e z) K' hKc hconv hzK' i

/-! ## Local constancy of the vanishing of `H_7` of the complement of a point -/

/-- **Local constancy.**  If `z` and `w` both lie in the chart-convex compact set
`K = e ⁻¹' K' ∩ e.source`, then `H_7(M ∖ {z}) = 0` iff `H_7(M ∖ {w}) = 0`. -/
theorem isZero_homology_compl_iff_of_mem_chartBall (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (c : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ c
    Metric.ball (e c) r ⊆ e.target →
    ∀ (K' : Set (EuclideanSpace ℝ (Fin N))) (hKc : IsCompact K') (hconv : Convex ℝ K'),
      K' ⊆ Metric.ball (e c) r →
      ∀ z : M, z ∈ e ⁻¹' K' ∩ e.source → ∀ w : M, w ∈ e ⁻¹' K' ∩ e.source →
        (CategoryTheory.Limits.IsZero
            ((Work.Cohomology.singularChains ℤ (TopCat.of {y : M | y ≠ z})).homology 7) ↔
          CategoryTheory.Limits.IsZero
            ((Work.Cohomology.singularChains ℤ (TopCat.of {y : M | y ≠ w})).homology 7)) := by
  intro e hball K' hKc hconv hKsub z hz w hw
  have key : ∀ u : M, u ∈ e ⁻¹' K' ∩ e.source →
      (CategoryTheory.Limits.IsZero
          ((Work.Cohomology.singularChains ℤ (TopCat.of {y : M | y ≠ u})).homology 7) ↔
        CategoryTheory.Limits.IsZero
          ((Work.Cohomology.singularChains ℤ (TopCat.of {y : M | y ∉ e ⁻¹' K' ∩ e.source})).homology 7)) := by
    intro u hu
    let Y : TopCat := TopCat.of {y : M | y ≠ u}
    let A : Set Y := {y | (y : M) ∉ e ⁻¹' K' ∩ e.source}
    have hL7 : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains Y A).homology 7) :=
      isZero_relChains_punctured_chart N hN M c r hr K' hKc hconv hball hKsub u hu 7
    have hL8 : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains Y A).homology 8) :=
      isZero_relChains_punctured_chart N hN M c r hr K' hKc hconv hball hKsub u hu 8
    -- the connecting map `H_8(Y,A) → H_7(A)` and the projection `H_7(Y) → H_7(Y,A)` vanish
    have hδ0 : Work.Cohomology.hPairδ Y A 7 = 0 :=
      CategoryTheory.Limits.IsZero.eq_zero_of_src hL8 (Work.Cohomology.hPairδ Y A 7)
    have hg0 : HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y A)) 7 = 0 :=
      CategoryTheory.Limits.IsZero.eq_zero_of_tgt hL7 _
    -- hence `H_7(A) → H_7(Y)` is invertible
    have hf : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y A) 7) := by
      have hEx1 := Work.Cohomology.hPair_exact₁ Y A 7
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx1
      have hker' : (ModuleCat.Hom.hom (Work.Cohomology.hPairδ Y A 7)).range = ⊥ := by
        rw [hδ0]; simp
      have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains Y A) 7)).ker = ⊥ := hEx1.symm.trans hker'
      haveI hmono : Mono (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y A) 7) :=
        (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hker)
      have hEx2 := Work.Cohomology.hPair_exact₂ Y A 7
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx2
      have hrange' : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y A)) 7)).ker = ⊤ := by
        rw [hg0]; simp
      have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains Y A) 7)).range = ⊤ := hEx2.trans hrange'
      haveI hepi : Epi (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y A) 7) :=
        (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range_eq_top.mp hrange)
      exact CategoryTheory.isIso_of_mono_of_epi _
    -- the subspace `A` is the complement of `K`
    let Φ : {y : Y // (y : M) ∉ e ⁻¹' K' ∩ e.source} ≃ₜ {y : M // y ∉ e ⁻¹' K' ∩ e.source} :=
      { toFun := fun y => ⟨y.1.1, y.2⟩
        invFun := fun y => ⟨⟨y.1, fun hh => y.2 (hh ▸ hu)⟩, y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl
        continuous_toFun := Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)
        continuous_invFun := Continuous.subtype_mk
          (Continuous.subtype_mk
            (f := fun y : {y : M // y ∉ e ⁻¹' K' ∩ e.source} => (y : M))
            continuous_subtype_val
            (fun y => by
              intro hh
              exact y.2 (hh ▸ hu)))
          (fun y => y.2) }
    obtain ⟨E4⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv Φ.toHomotopyEquiv 7
    constructor
    · intro h
      have hA : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↑A)).homology 7) :=
        CategoryTheory.Limits.IsZero.of_iso h (asIso (HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains Y A) 7))
      exact CategoryTheory.Limits.IsZero.of_iso hA E4.symm
    · intro h
      have hA : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↑A)).homology 7) :=
        CategoryTheory.Limits.IsZero.of_iso h E4
      exact CategoryTheory.Limits.IsZero.of_iso hA (asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains Y A) 7)).symm
  exact ⟨fun h => (key w hw).mpr ((key z hz).mp h), fun h => (key z hz).mpr ((key w hw).mp h)⟩

/-! ## The cap centre: the complement of `ιY 0` is the `Vk`-piece -/

/-- **The complement of the cap centre is the `Vk (-2)`-piece.** -/
private lemma glueU_eq_compl_ιY_zero (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2))
    (hV : D.V = Work.Milnor.capPunct) :
    Work.Milnor.glueU D = {y : Work.Milnor.cappedSpace D | y ≠ D.ιY 0} := by
  ext y; constructor
  · rintro ⟨x, rfl⟩ h
    obtain ⟨hxU, hφ⟩ := D.ιX_eq_ιY_iff.mp h
    have hmem : (D.φ x : EuclideanSpace ℝ (Fin 8)) ∈ D.V := by
      have hx : x ∈ D.φ.source := by rw [D.source_φ]; exact hxU
      have h1 := D.φ.map_source hx
      rwa [D.target_φ] at h1
    rw [hV] at hmem
    exact (Work.Milnor.mem_capPunct_iff.mp hmem) hφ
  · intro hy
    have hmem : y ∈ Work.Milnor.glueU D ∪ Work.Milnor.glueV D := by
      rw [Work.Milnor.glueU_union_glueV]; trivial
    rcases hmem with h | h
    · exact h
    · obtain ⟨z, rfl⟩ := h
      by_cases hz : z = 0
      · exact absurd (by rw [hz]) hy
      · have hzV : z ∈ D.V := by rw [hV]; exact Work.Milnor.mem_capPunct_iff.mpr hz
        refine ⟨D.φ.symm z, ?_⟩
        rw [D.ιX_eq_ιY_iff]
        refine ⟨?_, ?_⟩
        · rw [← D.source_φ, ← D.φ.symm_target]
          exact D.φ.symm.map_source (by rw [D.φ.symm_source, D.target_φ]; exact hzV)
        · exact D.φ.right_inv (by rw [D.target_φ]; exact hzV)

/-- **The base case: the complement of the cap centre has vanishing `H₇`.** -/
theorem isZero_homology_compl_capCentre (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of
      {y : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF) |
        y ≠ (Work.Milnor.cappedDatum F hF).ιY 0})).homology 7) := by
  obtain ⟨E⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (glueU_eq_compl_ιY_zero (Work.Milnor.cappedDatum F hF)
      (Work.Milnor.cappedDatum_U F hF) (Work.Milnor.cappedDatum_V F hF))).toHomotopyEquiv 7
  exact CategoryTheory.Limits.IsZero.of_iso
    (Work.Milnor.isZero_homology_glueU (Work.Milnor.cappedDatum F hF) 7
      (by norm_num) (by norm_num)) E.symm


/-! ## The main statement -/

theorem capped_localDegree_generator (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    ∀ c : (Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology 8,
      Submodule.span ℤ {c} = ⊤ →
      ∀ x : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF),
        Submodule.span ℤ
          {((HomologicalComplex.homologyMap
            (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
              (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
              {y | y ≠ x})) 8) c)} = ⊤ := by
  intro c hc x
  haveI hT2 : T2Space (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.isT2_capped F hF
  letI hCh : ChartedSpace (EuclideanSpace ℝ (Fin 8))
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.cappedChartedSpace (Work.Milnor.cappedDatum F hF)
  haveI hPC : PathConnectedSpace (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.capped_pathConnected (Work.Milnor.cappedDatum F hF) (Work.Milnor.cappedDatum_U F hF)
  let X : TopCat := TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
  -- the local constancy property at each point
  have hlocal : ∀ z : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF),
      ∃ U : Set (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)),
        IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U,
          (CategoryTheory.Limits.IsZero
              ((Work.Cohomology.singularChains ℤ (TopCat.of
                {y : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF) | y ≠ w})).homology 7) ↔
            CategoryTheory.Limits.IsZero
              ((Work.Cohomology.singularChains ℤ (TopCat.of
                {y : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF) | y ≠ z})).homology 7)) := by
    intro z
    let e : OpenPartialHomeomorph (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
        (EuclideanSpace ℝ (Fin 8)) := chartAt _ z
    have hzt : e z ∈ e.target := e.map_source (mem_chart_source _ z)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e z) hzt
    refine ⟨e.source ∩ e ⁻¹' Metric.ball (e z) (r / 2), ?_, ?_, ?_⟩
    · exact e.isOpen_inter_preimage Metric.isOpen_ball
    · refine ⟨mem_chart_source _ z, ?_⟩
      show e z ∈ Metric.ball (e z) (r / 2)
      exact Metric.mem_ball_self (by linarith)
    · intro w hw
      have hw' : w ∈ e ⁻¹' Metric.closedBall (e z) (r / 2) ∩ e.source :=
        ⟨Metric.ball_subset_closedBall hw.2, hw.1⟩
      exact isZero_homology_compl_iff_of_mem_chartBall 8 (by norm_num) X z r hr hball
        (Metric.closedBall (e z) (r / 2)) (isCompact_closedBall _ _) (convex_closedBall _ _)
        (fun v hv => by
          rw [Metric.mem_ball]
          have hv' : dist v (e z) ≤ r / 2 := Metric.mem_closedBall.mp hv
          linarith)
        w hw' z ⟨by
          show e z ∈ Metric.closedBall (e z) (r / 2)
          exact Metric.mem_closedBall_self (by linarith), mem_chart_source _ z⟩
  -- the base case
  have hbase : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of
      {y : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF) |
        y ≠ (Work.Milnor.cappedDatum F hF).ιY 0})).homology 7) :=
    isZero_homology_compl_capCentre F hF
  -- the set where the vanishing holds is clopen, hence everything
  let S : Set (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    {z | CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of
      {y : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF) | y ≠ z})).homology 7)}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hUopen, hzU, hU⟩ := hlocal z
    exact Filter.mem_of_superset (hUopen.mem_nhds hzU) (fun w hw => (hU w hw).mpr hz)
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hUopen, hzU, hU⟩ := hlocal z
    refine Filter.mem_of_superset (hUopen.mem_nhds hzU) (fun w hw hwS => ?_)
    exact hz ((hU w hw).mp hwS)
  have hSuniv : S = Set.univ := by
    rcases isClopen_iff.mp ⟨hSclosed, hSopen⟩ with h | h
    · exfalso
      have hSne : S.Nonempty := ⟨(Work.Milnor.cappedDatum F hF).ιY 0, hbase⟩
      rw [h] at hSne
      exact Set.not_nonempty_empty hSne
    · exact h
  have hzer : ∀ z : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF),
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of
        {y : Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF) | y ≠ z})).homology 7) := by
    intro z
    have hz : z ∈ S := by rw [hSuniv]; trivial
    exact hz
  -- the connecting map vanishes, so the map to the local homology is onto
  have hδ0 : Work.Cohomology.hPairδ X {y : X | y ≠ x} 7 = 0 :=
    CategoryTheory.Limits.IsZero.eq_zero_of_tgt (hzer x) _
  have hEx := Work.Cohomology.hPair_exact₃ X {y : X | y ≠ x} 7
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
  have hker : (ModuleCat.Hom.hom (Work.Cohomology.hPairδ X {y : X | y ≠ x} 7)).ker = ⊤ := by
    rw [hδ0]; simp
  have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X {y : X | y ≠ x})) 8)).range
      = ⊤ := hEx.trans hker
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X {y : X | y ≠ x})) 8).hom :=
    LinearMap.range_eq_top.mp hrange
  -- linear algebra
  have hmap : Submodule.map (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X {y : X | y ≠ x})) 8).hom
      (Submodule.span ℤ {c}) = Submodule.span ℤ
      {((HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X {y : X | y ≠ x})) 8) c)} := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [hc, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at hmap
  exact hmap.symm

end

end Work.Cohomology
