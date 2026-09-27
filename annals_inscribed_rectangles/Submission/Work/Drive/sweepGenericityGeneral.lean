import Mathlib
import Submission.Work.Drive.exists_meet3Hyp_opens_near_zero
import Submission.Work.Drive.endTripleRegUnrestricted

/-!
# The **general** sweep genericity: `Meet3Hyp` for an arbitrary triple of plane presentations

`Work.Drive.exists_meet3Hyp_opens_near_zero` produces a small parameter at which the *reference* triple
`![rotPresentation Q u, rotPresentation Q v, R]` has `Meet3Hyp`.  Its proof, however, only ever uses

* the smoothness `hP` and the seam invariance `hPseam` of the three plane presentations,
* the two `GoodAt` clauses (which are specific to the reference triple's pair of angles), and
* the **richness** hypothesis `hrich` of the family `sweepChartFam P Ξ c`,
  which is available for *every* triple `P` by the proved
  `Work.Drive.richness_sweepChartFam` (`Drive/hsurjCentred.lean`).

This file extracts the *general* statement, dropping the two `GoodAt` clauses: for an arbitrary triple of
plane presentations `P : Fin 3 → 𝔼² → CappingSpace` (smooth and seam invariant), any `ChartPert` `Ξ`, any
distinct positive levels `c`, and any open set `A` accumulating at `0`, there is a parameter `t ∈ A` of
arbitrary small norm with `Meet3Hyp CappingSpace (sweepChartFam P Ξ c t)`.

The use case is the **`hendL012` row** of the ends-clause design (`NOTES_LEAD_hodd_blockT6.md` §3): the
`EndTripleReg` of a triple of *plane class maps* one of whose blocks is a perturbed **rotated chart of
the curve's chart** `Q` (not a linear plane), where no linear/incidence criterion is available.  The
second theorem here delivers exactly that row, at a parameter of the same Sard call (the same open set
`A`), from the general genericity plus the already-proved bridge
`Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted` (`Drive/endTripleRegUnrestricted.lean`).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The general sweep genericity, for a finite family of triples of plane presentations.**  Given
finitely many triples `P j` of smooth, seam-invariant plane presentations (all sharing the chart
perturbation `Ξ` and the levels `c`), the design's families `sweepChartFam (P j) Ξ c` are *simultaneously*
transverse at some parameter `t ∈ A` of arbitrary small norm.  This is the form in which the ends-clause
design needs it: two `Meet3Hyp` families — the design's own triple and the *mixed* one whose first block
is a linear model — have to be transverse at the **same** parameter `t` (one localized Sard with the
product index `ι`), because the seven class-level rows of `hasClassLinearization_of_endData` are all
evaluated at that single `t`. -/
theorem exists_meet3Hyp_sweepChartFam_family {ι : Type*} [Fintype ι] {Q : ℂ → CappingSpace}
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (P : ι → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ (j : ι) (k : Fin 3), ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P j k))
    (hPseam : ∀ (j : ι) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P j k y = P j k (seamInv2 y))
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧
      ∀ j : ι, Meet3Hyp CappingSpace (sweepChartFam (P j) Ξ c t) := by
  classical
  let G : ι → EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun j t k x => sweepChartFam (P j) Ξ c t k x
  have hslice : ∀ (j : ι) (k' : Fin 3), ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice (P j) Ξ c k' q.1 q.2) :=
    fun j k' => contMDiff_sweepChartSlice_of_family hΞ (hP j) c k'
  have hG : ∀ (j : ι) (k : Fin 3), ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => G j q.1 k q.2) := by
    intro j k
    simpa only [G] using contMDiff_sweepChartFam (P j) Ξ c (hslice j) k
  have hsmooth : ∀ (j : ι) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (G j t k) := by
    intro j t k
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((t, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := (hG j k).comp (contMDiff_iff_contDiff.mpr hφ)
    simpa only [Function.comp_def, G] using hcomp
  have hseam : ∀ (j : ι) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x → G j t k x = G j t k (seamInv x) := by
    intro j t k x hx
    have hinst : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
        (fun z => Ξ (blk k t) (P j k z)) y = (fun z => Ξ (blk k t) (P j k z)) (seamInv2 y) :=
      fun y hy => congrArg (Ξ (blk k t)) (hPseam j k y hy)
    have h := clampedSweep_seamInv (c k) (fun r => 1 - r)
      (fun z => Ξ (blk k t) (P j k z)) hinst x hx
    simpa only [G, sweepChartFam_apply, Function.comp_def] using h
  have hrichG : ∀ (j : ι) (p : CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9)))
      (t₀ : EuclideanSpace ℝ (Fin 12)) (δ : ℝ), IsCompact K → 0 < δ →
      (∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K → ∀ k : Fin 3,
          G j t k (TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K →
        TParity.chartDiff3 p (G j t) y = 0 →
        Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G j t') y) t) := by
    intro j p K t₀ δ hK hδ hcont t y ht hy hz
    refine richness_sweepChartFam (P j) Ξ c hΞ hc hcdist (hP j) p K t₀ δ hK hδ ?_ t y ht hy ?_
    · intro t' y' ht' hy' k
      have h := hcont t' y' ht' hy' k
      simpa only [G] using h
    · have h := hz
      simpa only [G] using h
  obtain ⟨t, htA, htε, hmeet⟩ :=
    localSard_family_in_open (fun _ : ι => CappingSpace) G hG hsmooth hseam hrichG
      A hAopen hA0 ε' hε'
  exact ⟨t, htε, htA, fun j => by simpa only [G] using hmeet j⟩

/-- **The general sweep genericity.**  For an arbitrary triple `P` of smooth, seam-invariant plane
presentations, a chart perturbation `Ξ`, distinct positive levels `c` and an open set `A` accumulating
at the origin, the design's family `sweepChartFam P Ξ c` is transverse at some parameter `t ∈ A` of
arbitrary small norm.

This is `exists_meet3Hyp_opens_near_zero` with the two `GoodAt` clauses removed and the reference triple
replaced by an abstract `P`: the proof is the same localized parametric Sard
(`Work.Drive.localSard_family_in_open`), whose richness hypothesis is
`Work.Drive.richness_sweepChartFam P Ξ c hΞ hc hcdist hP` — which holds for every `P`. -/
theorem exists_meet3Hyp_sweepChartFam_general {Q : ℂ → CappingSpace}
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k y = P k (seamInv2 y))
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧
      Meet3Hyp CappingSpace (sweepChartFam P Ξ c t) := by
  classical
  let G : Unit → EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun _ t k x => sweepChartFam P Ξ c t k x
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  have hG : ∀ (j : Unit) (k : Fin 3), ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => G j q.1 k q.2) := by
    intro j k
    simpa only [G] using contMDiff_sweepChartFam P Ξ c hslice k
  have hsmooth : ∀ (j : Unit) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (G j t k) := by
    intro j t k
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((t, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := (hG j k).comp (contMDiff_iff_contDiff.mpr hφ)
    simpa only [Function.comp_def, G] using hcomp
  have hseam : ∀ (j : Unit) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x → G j t k x = G j t k (seamInv x) := by
    intro j t k x hx
    have hinst : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
        (fun z => Ξ (blk k t) (P k z)) y = (fun z => Ξ (blk k t) (P k z)) (seamInv2 y) :=
      fun y hy => congrArg (Ξ (blk k t)) (hPseam k y hy)
    have h := clampedSweep_seamInv (c k) (fun r => 1 - r)
      (fun z => Ξ (blk k t) (P k z)) hinst x hx
    simpa only [G, sweepChartFam_apply, Function.comp_def] using h
  have hrichG : ∀ (j : Unit) (p : CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9)))
      (t₀ : EuclideanSpace ℝ (Fin 12)) (δ : ℝ), IsCompact K → 0 < δ →
      (∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K → ∀ k : Fin 3,
          G j t k (TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K →
        TParity.chartDiff3 p (G j t) y = 0 →
        Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G j t') y) t) := by
    intro j p K t₀ δ hK hδ hcont t y ht hy hz
    refine richness_sweepChartFam P Ξ c hΞ hc hcdist hP p K t₀ δ hK hδ ?_ t y ht hy ?_
    · intro t' y' ht' hy' k
      have h := hcont t' y' ht' hy' k
      simpa only [G] using h
    · have h := hz
      simpa only [G] using h
  obtain ⟨t, htA, htε, hmeet⟩ :=
    localSard_family_in_open (fun _ : Unit => CappingSpace) G hG hsmooth hseam hrichG
      A hAopen hA0 ε' hε'
  exact ⟨t, htε, htA, by simpa only [G] using hmeet ()⟩

/-- **The `hendL012`-type row for an arbitrary triple of plane presentations.**  Under the same
hypotheses as `exists_meet3Hyp_sweepChartFam_general`, together with the affine invariance of the three
presentations (`diskPlane`-presented planes have it: `Work.Drive.diskPlane_affRep`) and the *perturbed*
level bound below the smallest level, there is a parameter `t ∈ A` of norm `< ε'` at which the three
perturbed class maps satisfy `EndTripleReg`.

Specialising `P` to `![linPlaneChart-model, P₁, P₂]` (with the model at a level `> c 0`) this is the
missing row `hendL012` of `hasClassLinearization_of_endData`, because
`planeClassMap` of a linear plane chart does not depend on its level
(`Work.Drive.planeClassMap_diskPlane_linPlaneChart_eq_of_level`) — so the first argument may be taken to
be any linear plane chart, in particular the *transported* one
`chartPert (blk 0 t) ∘ diskPlane (linPlaneChart (φ 0) c hc)`. -/
theorem exists_endTripleReg_sweepGeneral {Q : ℂ → CappingSpace}
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k y = P k (seamInv2 y))
    (hinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), P k (affRep e mm y) = P k y)
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ)
    (ε' : ℝ) (hε' : 0 < ε')
    (hlevel : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < ε' →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (Ξ (blk k t) (P k y))) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧
      EndTripleReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 0 t) (P 0 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) := by
  obtain ⟨t, htε, htA, hmeet⟩ :=
    exists_meet3Hyp_sweepChartFam_general (Q := Q) Ξ hΞ c hc hcdist P hP hPseam A hAopen hA0 ε' hε'
  refine ⟨t, htε, htA, ?_⟩
  have hPhat : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y)) :=
    fun k => hΞ.2.1.comp (contMDiff_const.prodMk (hP k))
  have hinv' : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        (fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y')) (affRep e mm y)
          = (fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y')) y :=
    fun e mm he k y => congrArg (Ξ (blk k t)) (hinv e mm he k y)
  have hlev' : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      c 0 < levelOf ((fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y')) y) :=
    fun k y => hlevel t htε k y
  have hmeet' : Meet3Hyp CappingSpace
      (fun k : Fin 3 => clampedSweep (c k) (fun r => 1 - r)
        (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y))) := by
    have hfun : (fun k : Fin 3 => clampedSweep (c k) (fun r => 1 - r)
        (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y))) = sweepChartFam P Ξ c t := by
      funext k x
      rfl
    rw [hfun]
    exact hmeet
  exact endTripleReg_of_meet3Hyp_sweeps_unrestricted c (fun r => 1 - r)
    (fun k y => Ξ (blk k t) (P k y)) (by fun_prop) hPhat hc hc10 hc20 (by norm_num) (by norm_num)
    (fun _ _ => by fun_prop) (fun _ _ => by intro a b hab; linarith [hab]) hinv' hlev' hmeet'

end

end Work.Drive
