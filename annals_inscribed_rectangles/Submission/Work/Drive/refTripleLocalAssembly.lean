import Mathlib
import Submission.Work.Drive.refTripleLocal
import Submission.Work.Drive.refTripleEndpoint
import Submission.Work.Drive.hsurjCentred

/-!
# The `hn2` assembly consuming the *localized* reference-triple genericity

`HN2_REFERENCE_ENDPOINT_STATUS.md` §2 records the endpoint
`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine`: `sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1`
from the reference-triple data.  Its genericity input was `Meet3Hyp` of the perturbed reference triple
*and* the two `GoodAt` clauses at one parameter `t`, which the Sard route produces — but the original
producer `Work.Drive.exists_meet3Hyp_and_goodAt_refTriple` demanded a **single chart containing the
whole base triple locus**, an unusable hypothesis for the capping space
(`Submission/Work/Drive/CHART_SOURCE_OPACITY.md`).

`Work.Drive.refTripleLocal` replaces that hypothesis by the *richness* of the localized Sard, and
`Work.Drive.richness_sweepChartFam` (`hsurjCentred.lean`) proves the richness for the design's family
of chart-perturbed clamped sweeps in the required centred shape.  This file performs the resulting
assembly:

* `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleLocal` — the `hn2` identity at the angle `u - v`
  (i.e. at `a = v - u`) for the reference triple `![P_u, P_v, R]`, from

  * the chart data `Ξ`, `Q` (`IsChartData`), the reference plane `R` (smooth + seam-invariant),
  * the `t`-*uniform* engine data: the level data `hlev`, the class-triple parity `hodd`, and the six
    block factor data `hblock`/`hg01`/`hg10`/`h20`/`h21`/`h02`/`h12` (with the block-factor function
    `g t` allowed to depend on the parameter),
  * the germ locale data (`hUa`, `hUa'`, `hparA`, `hUn`, `hUn'`, `hparN`).

  The point of the statement is that **the genericity (`Meet3Hyp` and the two `GoodAt` clauses) is not
  a hypothesis any more**: it is produced internally by `refTripleLocal` from the richness, which is
  proved.  The residual inputs are exactly the transport/linearization data of the other lanes.

* `Work.Drive.norm_pair_blk_le` — the small norm bookkeeping
  (`‖(blk i t, blk j t)‖ ≤ ‖t‖`, from the existing `Work.Drive.norm_blk_le`) that lets the parameter produced by `refTripleLocal` (of norm `< ε`) also serve
  the locality balls of the germ lane.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The reference triple**: the two rotated copies of the chart at the angles `u`, `v`, and the
reference plane `R` (the design's `![P_u, P_v, R]`). -/
def refTriple (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  ![rotPresentation Q u, rotPresentation Q v, R]

/-! ## The norm bookkeeping of the block projections -/

/-- A pair of block projections does not increase the norm (the product carries the max norm). -/
lemma norm_pair_blk_le (i j : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    ‖(blk i t, blk j t)‖ ≤ ‖t‖ := by
  rw [Prod.norm_def]
  exact max_le (norm_blk_le i t) (norm_blk_le j t)

/-! ## The assembly -/

/-- **`hn2` at the angle `u - v` for the reference triple, with the genericity produced internally.**

The hypotheses are the *t-uniform* engine data (see the module docstring); the conclusion is the
antisymmetry of the germ side value at the two opposite angles. -/
theorem sideGerm_add_neg_eq_one_of_refTripleLocal
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    {Q : ℂ → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (hQ : IsChartData Q) (c : ℝ) (hc : 0 < c)
    (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hR : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) R)
    (hRseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → R y = R (seamInv2 y))
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ)
    (g : EuclideanSpace ℝ (Fin 12) → Fin 3 → Fin 3 → ℕ)
    (hcdist : ∀ k k' : Fin 3, cblk k = cblk k' → k = k')
    (hcpos : ∀ k : Fin 3, 0 < cblk k) (hc1 : cblk 1 < cblk 0) (hc2 : cblk 2 < cblk 0)
    {ε : ℝ} (hε : 0 < ε)
    (hlev : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε → ∀ (k : Fin 3)
      (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < levelOf ((fun z => Ξ (blk k t) (refTriple Q R u v k z)) y))
    (hodd : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε →
      Odd (classTripleSet (fun k => fun z => Ξ (blk k t) (refTriple Q R u v k z))).ncard)
    (hblock : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε → ∀ k : Fin 3,
      Odd ((topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) k).ncard) ↔
        (Odd (g t k (k + 1)) ∧ Odd (g t k (k + 2))))
    (hg01 : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε →
      g t 0 1 = CntAt Ξ Q (cblk 1) (v - u) (blk 0 t, blk 1 t))
    (hg10 : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε →
      g t 1 0 = CntAt Ξ Q (cblk 0) (u - v) (blk 1 t, blk 0 t))
    (h20 : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε → Even (g t 2 0))
    (h21 : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε → Even (g t 2 1))
    (h02 : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε → Odd (g t 0 2))
    (h12 : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε → Odd (g t 1 2))
    (hUa : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c (v - u) s → GoodAt Ξ Q c (v - u) s' →
        Odd (CntAt Ξ Q c (v - u) s) = Odd (CntAt Ξ Q c (v - u) s'))
    (hUa' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 1) (v - u) s → GoodAt Ξ Q (cblk 1) (v - u) s' →
        Odd (CntAt Ξ Q (cblk 1) (v - u) s) = Odd (CntAt Ξ Q (cblk 1) (v - u) s'))
    (hparA : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      GoodAt Ξ Q c (v - u) s → GoodAt Ξ Q (cblk 1) (v - u) s →
        Odd (CntAt Ξ Q c (v - u) s) = Odd (CntAt Ξ Q (cblk 1) (v - u) s))
    (hUn : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c (-(v - u)) s → GoodAt Ξ Q c (-(v - u)) s' →
        Odd (CntAt Ξ Q c (-(v - u)) s) = Odd (CntAt Ξ Q c (-(v - u)) s'))
    (hUn' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 0) (-(v - u)) s →
        GoodAt Ξ Q (cblk 0) (-(v - u)) s' →
        Odd (CntAt Ξ Q (cblk 0) (-(v - u)) s) = Odd (CntAt Ξ Q (cblk 0) (-(v - u)) s'))
    (hparN : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      GoodAt Ξ Q c (-(v - u)) s → GoodAt Ξ Q (cblk 0) (-(v - u)) s →
        Odd (CntAt Ξ Q c (-(v - u)) s) = Odd (CntAt Ξ Q (cblk 0) (-(v - u)) s)) :
    sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1 := by
  classical
  -- ## the smoothness of the reference triple and the richness (the localized Sard's hypothesis)
  have hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (refTriple Q R u v k) := by
    intro k
    fin_cases k
    · exact contMDiff_rotPresentation Q u (contMDiff_diskPlane (Q := Q) hQ.1)
    · exact contMDiff_rotPresentation Q v (contMDiff_diskPlane (Q := Q) hQ.1)
    · simpa [refTriple] using hR
  have hrich := richness_sweepChartFam (refTriple Q R u v) Ξ cblk hΞ hcpos hcdist hP
  -- ## the genericity, at a parameter of norm `< ε`
  obtain ⟨t, ht, hmeet, hgood01, hgood10⟩ :=
    refTripleLocal hQ Ξ hΞ cblk hcpos hcdist u v R hR hRseam hrich ε hε
  have ht1 : ‖(blk 0 t, blk 1 t)‖ < ε := lt_of_le_of_lt (norm_pair_blk_le 0 1 t) ht
  have ht2 : ‖(blk 1 t, blk 0 t)‖ < ε := lt_of_le_of_lt (norm_pair_blk_le 1 0 t) ht
  have hgood10' : GoodAt Ξ Q (cblk 0) (-(v - u)) (blk 1 t, blk 0 t) := by
    rw [neg_sub]
    exact hgood10
  have hmain := sideGerm_add_neg_eq_one_of_refTripleEngine Ξ Q hΞ hQ.isSmoothChart c hc
    (refTriple Q R u v) (v - u) t cblk (g t) (hg01 t ht) (by rw [neg_sub]; exact hg10 t ht) hcpos hc1 hc2
    (hlev t ht) hmeet (hodd t ht) (hblock t ht) (h20 t ht) (h21 t ht) (h02 t ht) (h12 t ht)
    hε hUa hUa' hparA hUn hUn' hparN ht1 ht2 hgood01 hgood10'
  rwa [neg_sub] at hmain

end

end Work.Drive
