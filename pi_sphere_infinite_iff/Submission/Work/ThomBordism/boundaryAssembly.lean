import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.sigmaBoundarySum
import Submission.Work.ThomBordism.boundarySigmaReduction
import Submission.Work.Bordism.interForm_pullback
import Submission.Work.SignatureBordism.signature_of_isLagrangian
import Submission.Work.SignatureBordism.tensor_bilin_ext

/-!
# `BoundarySigma` from the Lagrangian property of the restriction to the boundary

`Work.ThomBordism.BoundarySigma` asks that `∑ i, (F i).sigma = 0` for the pieces of the boundary of
a `W : NullBordismFamily ι F`.  This file reduces it to **one** geometric statement about the pair
`(W, ∂W)` — the *maximality* half of middle-dimensional Lefschetz duality — plus the two
Poincaré-duality inputs for the closed manifold `∂W` (finite dimensionality and non-degeneracy of
its middle intersection form).

## The reduction, and why it is the crux

Write `M = ∂W` and

* `K = image(H⁴(W;ℚ) → H⁴(M;ℚ))` (`Work.ThomBordism.bdryK`) — the image of the restriction,
* `B` (`Work.ThomBordism.bdryFormBilin`) — the middle intersection form `⟨y ⌣ z, [M]⟩` of `M`,
  whose quadratic form is `Work.Bordism.midForm (bdryClosed W)`.

Two halves of the Lagrangian property of `K` are needed.

* **Isotropy** `K ⊆ Kᗮ`: for `x = i*u`, `y = i*u'` the naturality of the intersection form
  (`Work.Bordism.interForm_pullback`) computes `B x y = ⟨u ⌣ u', i_*[M]⟩_W`, and `i_*[M] = 0`
  because `[M] = ∂w` is a boundary in `W` (`Work.Cohomology.hPairδ_comp`).  This half needs *no*
  duality; it is proved here as `Work.ThomBordism.bdryK_isotropic`.
* **Maximality** `Kᗮ ⊆ K`: this is the content of middle-dimensional Lefschetz duality for the pair
  `(W, ∂W)` (`H⁴(M)/K ≅ H⁵(W,M) ≅ H₄(W)`).  It is *not* proved here; it is stated as the named
  `Prop` `Work.ThomBordism.BoundaryMaximalIsotropic`.  The classical proof uses the double
  `D = W ∪_M W̄`, its Poincaré duality (`H⁴(D) ≅ H₅(D)`, `H⁵(D) ≅ H₄(D)`), the Mayer–Vietoris
  connecting map `∂_D : H₅(D;ℚ) → H₄(M;ℚ)` (whose image is `ker(H₄(M) → H₄(W))`) and the
  transgression identity `⟨∂_D x, z⟩_M = ⟨x, i_* z⟩_D`, which gives `⟨∂_D x, ∂_D x'⟩_M = 0`.

Given both halves, `K` is a *Lagrangian* of `B`, so the signature of `B` vanishes
(`Work.SignatureBordism.signature_of_isLagrangian`) — this is exactly `σ(∂W) = 0` — and
`Work.ThomBordism.sigmaBoundarySum` (proved) converts `σ(∂W) = 0` into `∑ i, (F i).sigma = 0`.

## Main results

* `Work.ThomBordism.bdryIncl`, `bdryK`, `bdryFormBilin` — the restriction, its image and the middle
  intersection form of the boundary;
* `Work.ThomBordism.boundaryClass_incl_eq_zero` — `i_*[∂W] = 0` in `H₈(W;ℤ)`;
* **`Work.ThomBordism.bdryK_isotropic`** — `K ⊆ Kᗮ` (no duality);
* **`Work.ThomBordism.BoundaryMaximalIsotropic`** — `Kᗮ ⊆ K` (the named Lefschetz-duality input);
* **`Work.ThomBordism.boundarySigma_of_isLagrangian`** — `BoundarySigma` from
  `BoundaryMaximalIsotropic` and the two Poincaré-duality inputs for `∂W`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism

noncomputable section

/-- **The inclusion of the boundary** `∂W ⟶ W` of a `NullBordismFamily`. -/
def bdryIncl {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    TopCat.of (bdrySet W.W) ⟶ TopCat.of W.W :=
  Work.Cohomology.subtypeIncl (TopCat.of W.W) (bdrySet W.W)

/-- **The image `K` of the restriction** `H⁴(W;ℚ) → H⁴(∂W;ℚ)`, inside the rationalised middle
cohomology of the boundary. -/
abbrev bdryK {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    Submodule ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))) :=
  LinearMap.range (Work.Bordism.pullbackRat 4 (bdryIncl W))

/-- **The middle intersection form of the boundary**, `⟨y ⌣ z, [∂W]⟩` with `[∂W] = ∂w`. -/
abbrev bdryFormBilin {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) →ₗ[ℚ]
      Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) →ₗ[ℚ]
        ℚ :=
  Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))
    (Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w)

/-- **The boundary class is null-homologous in `W`**: `i_*[∂W] = 0 ∈ H₈(W;ℤ)`.  This is the
long exact sequence of the pair `(W, ∂W)` (`Work.Cohomology.hPairδ_comp`) applied to the relative
fundamental class `w`. -/
theorem boundaryClass_incl_eq_zero {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) :
    (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (bdrySet W.W)) (TopCat.of W.W)
          (bdryIncl W)) 8)
        (Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w) = 0 := by
  have hz : (Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 ≫
      HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of W.W) (bdrySet W.W)) 8) W.w = 0 := by
    rw [Work.Cohomology.hPairδ_comp]
    simp
  have h3 : (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of W.W) (bdrySet W.W)) 8)
        ((Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8) W.w) = 0 := by
    simpa using hz
  simpa only [Work.Cohomology.inclChains, bdryIncl] using h3

/-- **Isotropy on pure tensors**: the middle form of the boundary vanishes on two classes pulled
back from `W`.  By `Work.Bordism.interForm_pullback` the value is
`⟨u ⌣ u', i_*[∂W]⟩`, and `i_*[∂W] = 0` (`boundaryClass_incl_eq_zero`). -/
theorem bdryFormBilin_pullback_tmul {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) (a b : ℚ)
    (m n : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology 4) :
    bdryFormBilin W (Work.Bordism.pullbackRat 4 (bdryIncl W) (a ⊗ₜ[ℤ] m))
      (Work.Bordism.pullbackRat 4 (bdryIncl W) (b ⊗ₜ[ℤ] n)) = 0 := by
  change Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))
      (Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w)
      (Work.Bordism.pullbackRat 4 (bdryIncl W) (a ⊗ₜ[ℤ] m))
      (Work.Bordism.pullbackRat 4 (bdryIncl W) (b ⊗ₜ[ℤ] n)) = 0
  rw [Work.Bordism.pullbackRat_tmul, Work.Bordism.pullbackRat_tmul,
    Work.SignatureBordism.ratInterForm_tmul]
  rw [Work.Bordism.interForm_pullback (bdryIncl W) 4
    (Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w) m n]
  rw [boundaryClass_incl_eq_zero W,
    Work.ThomBordism.interForm_zero_fundamental]
  simp

/-- **The middle form of the boundary vanishes on the image of the restriction** (the isotropy half
of the Lagrangian property): for `u, u' ∈ H⁴(W;ℚ)`,
`⟨i*u ⌣ i*u', [∂W]⟩ = 0`. -/
theorem bdryFormBilin_pullback_eq_zero {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F)
    (u v : Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of W.W))) :
    bdryFormBilin W (Work.Bordism.pullbackRat 4 (bdryIncl W) u)
      (Work.Bordism.pullbackRat 4 (bdryIncl W) v) = 0 := by
  let Φ : Work.SignatureBordism.ratCohomology 4
        (TopCat.toSSet.obj (TopCat.of W.W)) →ₗ[ℚ]
      Work.SignatureBordism.ratCohomology 4
        (TopCat.toSSet.obj (TopCat.of W.W)) →ₗ[ℚ] ℚ :=
    (bdryFormBilin W).compl₁₂ (Work.Bordism.pullbackRat 4 (bdryIncl W))
      (Work.Bordism.pullbackRat 4 (bdryIncl W))
  have hΦ : Φ = 0 := by
    refine Work.SignatureBordism.tensor_bilin_ext (fun a b m n => ?_)
    exact bdryFormBilin_pullback_tmul W a b m n
  have h := LinearMap.congr_fun (LinearMap.congr_fun hΦ u) v
  simpa [Φ, LinearMap.compl₁₂_apply] using h

/-- **The isotropy of the image of the restriction** `K ⊆ Kᗮ`: any two elements of `K` are
orthogonal for the middle intersection form of the boundary.  No duality is used. -/
theorem bdryK_isotropic {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) :
    ∀ x ∈ bdryK W, ∀ y ∈ bdryK W, bdryFormBilin W x y = 0 := by
  intro x hx y hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact bdryFormBilin_pullback_eq_zero W u v

/-- **The middle form of the boundary vanishes on `K`**: an element of the image of the restriction
is isotropic for the middle intersection form of `∂W`. -/
theorem bdryMidForm_eq_zero_of_mem_K {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F)
    {z : Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))} (hz : z ∈ bdryK W) :
    Work.Bordism.midForm (k := 4) (bdryClosed W) z = 0 := by
  show Work.SignatureBordism.quadOfBilin (bdryFormBilin W) z = 0
  rw [Work.SignatureBordism.quadOfBilin_apply]
  exact bdryK_isotropic W z hz z hz

/-- **The associated bilinear form of the boundary vanishes on two elements of `K`.** -/
theorem bdryAssoc_eq_zero_of_mem_K {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F)
    {x y : Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))}
    (hx : x ∈ bdryK W) (hy : y ∈ bdryK W) :
    QuadraticMap.associated (Work.Bordism.midForm (k := 4) (bdryClosed W)) x y = 0 := by
  rw [QuadraticMap.associated_apply,
    bdryMidForm_eq_zero_of_mem_K W (add_mem hx hy),
    bdryMidForm_eq_zero_of_mem_K W hx, bdryMidForm_eq_zero_of_mem_K W hy]
  simp

/-- **The named geometric input: the restriction image is *maximal* isotropic.**

For every `W : NullBordismFamily ι F`, every class `y ∈ H⁴(∂W;ℚ)` orthogonal to the image `K` of
the restriction `H⁴(W;ℚ) → H⁴(∂W;ℚ)` lies in `K`.  Together with the *proved* isotropy
(`Work.ThomBordism.bdryK_isotropic`) this says `K = Kᗮ`: `K` is a **Lagrangian** of the middle
intersection form of `∂W`.

This is the *only* geometric statement missing from `Work.ThomBordism.BoundarySigma`: it is the
maximality half of middle-dimensional Poincaré–Lefschetz duality for the pair `(W, ∂W)`, which is
equivalent (by the long exact sequence of the pair) to the isotropy of the subspace
`im(H₅(W,∂W;ℚ) → H₄(∂W;ℚ)) = ker(H₄(∂W;ℚ) → H₄(W;ℚ))`.  The classical proof doubles `W` along
`∂W` and uses the Poincaré duality of the closed `9`-manifold `D = W ∪_M W̄` together with the
Mayer–Vietoris transgression identity `⟨∂_D x, z⟩_M = ⟨x, i_* z⟩_D`. -/
def BoundaryMaximalIsotropic : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
    ∀ y : Work.SignatureBordism.ratCohomology 4
        (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))),
      (∀ x ∈ bdryK W,
        QuadraticMap.associated (Work.Bordism.midForm (k := 4) (bdryClosed W)) x y = 0)
      → y ∈ bdryK W

/-- **`BoundarySigma` from the Lagrangian property of the restriction to the boundary.**

Given

* `BoundaryMaximalIsotropic` — the maximality half of Lefschetz duality for `(W, ∂W)` (the crux),
* non-degeneracy of the middle intersection form of `∂W` (Poincaré duality for the closed oriented
  `8`-manifold `∂W`),
* finite dimensionality of `H⁴(∂W;ℚ)`,

the sum of the signatures of the pieces of the boundary vanishes.

Proof: the isotropy is `bdryK_isotropic` (proved), the maximality is the hypothesis, so `K = Kᗮ` is
a Lagrangian of the middle form of `∂W`; hence that form has signature `0`
(`Work.SignatureBordism.signature_of_isLagrangian`), i.e. `σ(∂W) = 0`; and
`Work.ThomBordism.sigmaBoundarySum` identifies `σ(∂W)` with `∑ i, (F i).sigma`. -/
theorem boundarySigma_of_isLagrangian
    (hmax : BoundaryMaximalIsotropic)
    (hnd : ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
      Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) (bdryClosed W)))
    (hfin : ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
      FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
        (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))))) :
    BoundarySigma := by
  intro ι _ F W
  rw [← sigmaBoundarySum W]
  haveI := hfin ι F W
  rw [Work.Bordism.sigma_eq_signature_midForm (k := 4) (bdryClosed W)]
  refine Work.SignatureBordism.signature_of_isLagrangian
    (Work.Bordism.midForm (k := 4) (bdryClosed W)) (bdryK W) ?_ ?_ (hnd ι F W)
  · -- the quadratic form of the boundary vanishes on `K`
    intro x hx
    exact bdryMidForm_eq_zero_of_mem_K W hx
  · -- `K` is its own orthogonal complement: isotropy (proved) and maximality (hypothesis)
    intro x
    constructor
    · intro h
      refine hmax ι F W x (fun y hy => ?_)
      rw [QuadraticMap.associated_isSymm (S := ℚ)]
      exact h y hy
    · intro hx y hy
      exact bdryAssoc_eq_zero_of_mem_K W hx hy

end

end Work.ThomBordism
