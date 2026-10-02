import Mathlib
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.Duality.convex_compl_sphere
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.pd_plumbing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the relative homology of the punctured space

Let `K ⊆ ℝᴺ` (`N ≥ 1`) be a nonempty compact convex set and `z ∈ K`.  Then the inclusion
`ℝᴺ ∖ K ⟶ ℝᴺ ∖ {z}` is a homotopy equivalence (radial projection away from `z`, which pushes
everything outside the ball of radius `R ⊇ K` containing `K`): witness the explicit deformation
retraction

`x ↦ z + max 1 (R / ‖x - z‖) • (x - z)`  (`x ≠ z`),

with straight-line homotopy `x ↦ z + ((1 - t) + t max 1 (R / ‖x - z‖)) • (x - z)`.

Consequently the map induced on singular chains is a quasi-isomorphism, and the long exact
sequence of the pair (equivalently, the acyclicity of the cokernel of a quasi-isomorphism of an
exact short complex of chain complexes, `ShortComplex.ShortExact.acyclic_X₃`) shows that the
relative chain complex `C_*(ℝᴺ∖{z}, ℝᴺ∖K)` is acyclic:

`Hᵢ(ℝᴺ∖{z}, ℝᴺ∖K; ℤ) = 0` for every `i`.

This is the base case of the "propagation of a local fundamental class from a point to a compact
convex set" needed for Poincaré duality (see `Submission/Work/Cohomology/PD_PLAN.md`).
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## The radial scaling functions -/

/-- The radial scaling factor of the retraction of `ℝᴺ ∖ {z}` onto the complement of a compact
convex set contained in the ball of radius `R` about `z`: it is `max 1 (R / ‖x - z‖)`, so that the
image of `x` lies at distance at least `R` from `z` (and equals `x` when `‖x - z‖ ≥ R`). -/
def radialScale (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ := max 1 (R / ‖x - z‖)

/-- The scaling factor is at least `1`. -/
theorem radialScale_one_le (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : 1 ≤ radialScale N z R x := le_max_left _ _

/-- **The image of `x ≠ z` under the radial retraction lies at distance at least `R` from `z`.** -/
theorem radialScale_mul_norm_ge (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ≠ z) :
    R ≤ radialScale N z R x * ‖x - z‖ := by
  have hd : ‖x - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  unfold radialScale
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), div_mul_cancel₀ _ hd]
  exact le_max_right _ _

/-- The scaling factor along the straight-line homotopy from the identity to the radial
retraction: `(1 - t) + t · max 1 (R / ‖x - z‖)`. -/
def homScale (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ := (1 - t) + t * radialScale N z R x

/-- The homotopy scaling factor is at least `1` for `t ≥ 0`. -/
theorem homScale_one_le (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) (R : ℝ) (t : ℝ)
    (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin N)) : 1 ≤ homScale N z R t x := by
  have hc : 1 ≤ radialScale N z R x := radialScale_one_le N z R x
  have := mul_le_mul_of_nonneg_left hc ht
  simp only [homScale]; linarith

/-- **The relative homology of the punctured space vanishes.**

For `K ⊆ ℝᴺ` a nonempty compact convex set (`N ≥ 1`) and `z ∈ K`, the pair
`(ℝᴺ ∖ {z}, ℝᴺ ∖ K)` has trivial relative singular homology in every degree. -/
theorem isZero_relChains_punctured (N : ℕ) (hN : 1 ≤ N)
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
  have hscale : Continuous fun x : ↥X => radialScale N z R (x : EuclideanSpace ℝ (Fin N)) := by
    unfold radialScale; exact continuous_const.max hdiv
  have hGcont : Continuous fun x : ↥X =>
      z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) • ((x : EuclideanSpace ℝ (Fin N)) - z) :=
    continuous_const.add (hscale.smul (hxn.sub continuous_const))
  have hGne : ∀ x : ↥X, z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
      ((x : EuclideanSpace ℝ (Fin N)) - z) ≠ z := by
    intro x h
    have hc : radialScale N z R (x : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
      have h1 := radialScale_one_le N z R (x : EuclideanSpace ℝ (Fin N))
      intro h0; rw [h0] at h1; norm_num at h1
    have hv : (x : EuclideanSpace ℝ (Fin N)) - z ≠ 0 := sub_ne_zero.mpr x.2
    have h4 : z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z) - z = 0 := by rw [h, sub_self]
    rw [add_sub_cancel_left] at h4
    exact smul_ne_zero hc hv h4
  have hGnotK : ∀ x : ↥X, z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
      ((x : EuclideanSpace ℝ (Fin N)) - z) ∉ K := by
    intro x hmem
    have hb : dist (z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z)) z < R := by
      have := hsub hmem; rwa [Metric.mem_ball] at this
    have hc0 : 0 ≤ radialScale N z R (x : EuclideanSpace ℝ (Fin N)) :=
      le_trans zero_le_one (radialScale_one_le N z R (x : EuclideanSpace ℝ (Fin N)))
    have hge : R ≤ dist (z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z)) z := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      exact radialScale_mul_norm_ge N z R (x : EuclideanSpace ℝ (Fin N)) x.2
    linarith
  -- the radial retraction `ℝᴺ ∖ {z} ⟶ ℝᴺ ∖ K`
  let g : X ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun x => ⟨⟨z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
        ((x : EuclideanSpace ℝ (Fin N)) - z), hGne x⟩, hGnotK x⟩,
      hGcont.subtype_mk hGne |>.subtype_mk hGnotK⟩
  let f : TopCat.of A ⟶ X := subtypeIncl X A
  -- the straight-line homotopy on `ℝᴺ ∖ {z}`
  have hXs : Continuous fun q : ↑unitInterval × ↥X =>
      homScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) := by
    unfold homScale
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul (hscale.comp continuous_snd))
  have hX1 : ∀ q : ↑unitInterval × ↥X,
      1 ≤ homScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) :=
    fun q => homScale_one_le N z R (q.1:ℝ) q.1.2.1 (q.2 : EuclideanSpace ℝ (Fin N))
  have hXmem : ∀ q : ↑unitInterval × ↥X,
      z + homScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
        ((q.2 : EuclideanSpace ℝ (Fin N)) - z) ≠ z := by
    intro q h
    have hs0 : homScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
      have h1 := hX1 q; linarith
    have hv : (q.2 : EuclideanSpace ℝ (Fin N)) - z ≠ 0 := sub_ne_zero.mpr q.2.2
    have h4 : z + homScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
        ((q.2 : EuclideanSpace ℝ (Fin N)) - z) - z = 0 := by rw [h, sub_self]
    rw [add_sub_cancel_left] at h4
    exact smul_ne_zero hs0 hv h4
  have hXbase : Continuous fun q : ↑unitInterval × ↥X =>
      z + homScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
        ((q.2 : EuclideanSpace ℝ (Fin N)) - z) :=
    continuous_const.add (hXs.smul
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const))
  let HXF : C(↑unitInterval × ↥X, ↥X) :=
    ⟨fun q => ⟨z + homScale N z R (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin N)) •
      ((q.2 : EuclideanSpace ℝ (Fin N)) - z), hXmem q⟩, hXbase.subtype_mk hXmem⟩
  have H0X : TopCat.Homotopy (𝟙 X) (g ≫ f) :=
    ContinuousMap.Homotopy.mk HXF
      (fun x => by
        change HXF (0, x) = x
        apply Subtype.ext
        show z + homScale N z R (((0:↑unitInterval):ℝ)) (x : EuclideanSpace ℝ (Fin N)) •
          ((x : EuclideanSpace ℝ (Fin N)) - z) = (x : EuclideanSpace ℝ (Fin N))
        simp only [homScale]; norm_num)
      (fun x => by
        have hgf : (g ≫ f).hom x = (⟨z + radialScale N z R (x : EuclideanSpace ℝ (Fin N)) •
            ((x : EuclideanSpace ℝ (Fin N)) - z), hGne x⟩ : ↥X) := rfl
        rw [hgf]
        apply Subtype.ext
        show z + homScale N z R (((1:↑unitInterval):ℝ)) (x : EuclideanSpace ℝ (Fin N)) •
          ((x : EuclideanSpace ℝ (Fin N)) - z) = z +
          radialScale N z R (x : EuclideanSpace ℝ (Fin N)) • ((x : EuclideanSpace ℝ (Fin N)) - z)
        simp only [homScale]; norm_num)
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
      radialScale N z R ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) := by
    unfold radialScale
    exact continuous_const.max (continuous_const.div (hAxn2.sub continuous_const).norm hAne0)
  have hAs : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) =>
      homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) := by
    unfold homScale
    exact (continuous_const.sub htA).add (htA.mul hAscale)
  have hAs1 : ∀ q : ↑unitInterval × ↥(TopCat.of A),
      1 ≤ homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) :=
    fun q => homScale_one_le N z R (q.1:ℝ) q.1.2.1 _
  have hAne : ∀ q : ↑unitInterval × ↥(TopCat.of A),
      z + homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) ≠ z := by
    intro q h
    have hs0 : homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
      have h1 := hAs1 q; linarith
    have hv : (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N))) - z ≠ 0 := sub_ne_zero.mpr (q.2 : ↥X).2
    have h4 : z + homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) - z = 0 := by rw [h, sub_self]
    rw [add_sub_cancel_left] at h4
    exact smul_ne_zero hs0 hv h4
  have hAnotK : ∀ q : ↑unitInterval × ↥(TopCat.of A),
      z + homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) ∉ K :=
    fun q => Duality.convex_ray_notMem K hconv z hz
      ⟨((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)), q.2.2⟩ _ (hAs1 q)
  have hAbase : Continuous fun q : ↑unitInterval × ↥(TopCat.of A) =>
      z + homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z) :=
    continuous_const.add (hAs.smul (hAxn2.sub continuous_const))
  let HAF : C(↑unitInterval × ↥(TopCat.of A), ↥(TopCat.of A)) :=
    ⟨fun q => ⟨⟨z + homScale N z R (q.1 : ℝ) ((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) •
        (((q.2 : ↥X) : EuclideanSpace ℝ (Fin N)) - z), hAne q⟩, hAnotK q⟩,
      (hAbase.subtype_mk hAne).subtype_mk hAnotK⟩
  have H0A : TopCat.Homotopy (𝟙 (TopCat.of A)) (f ≫ g) :=
    ContinuousMap.Homotopy.mk HAF
      (fun a => by
        change HAF (0, a) = a
        apply Subtype.ext; apply Subtype.ext
        show z + homScale N z R (((0:↑unitInterval):ℝ)) (((a : ↥X) : EuclideanSpace ℝ (Fin N))) •
          (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z) = ((a : ↥X) : EuclideanSpace ℝ (Fin N))
        simp only [homScale]; norm_num)
      (fun a => by
        have hfg : (f ≫ g).hom a = (⟨⟨z + radialScale N z R (((a : ↥X) : EuclideanSpace ℝ (Fin N))) •
            (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z), hGne (a : ↥X)⟩,
            hGnotK (a : ↥X)⟩ : ↥(TopCat.of A)) := rfl
        rw [hfg]
        apply Subtype.ext; apply Subtype.ext
        show z + homScale N z R (((1:↑unitInterval):ℝ)) (((a : ↥X) : EuclideanSpace ℝ (Fin N))) •
          (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z) = z + radialScale N z R
          (((a : ↥X) : EuclideanSpace ℝ (Fin N))) • (((a : ↥X) : EuclideanSpace ℝ (Fin N)) - z)
        simp only [homScale]; norm_num)
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

end

end Work.Cohomology
