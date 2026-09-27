import Mathlib
import Submission.Work.Drive.refTripleEndpoint
import Submission.Work.Drive.refTripleLocalAssembly
import Submission.Work.Drive.chartIsSmooth

/-!
# The `hn2` endpoint at **one** parameter (the lead's `NOTES_LEAD_hblock_uniformity.md` §3)

`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine` (`refTripleEndpoint.lean`) is the `hn2`
endpoint; its hypotheses `hlev`, `hmeet`, `hodd`, `hblock`, `h20`…`h12` and the two `GoodAt` facts are
all taken at **one** parameter `t : ℝ¹²`.  The assembly
`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleLocal` (`refTripleLocalAssembly.lean`) instead carries
nine *uniform-in-`t`* binders, which is strictly stronger than what the endpoint needs — and, as the
lead records (`NOTES_LEAD_hblock_uniformity.md` §1), an unwanted uniformity: `hodd` and T6's inputs are
genericity conditions that can *fail* at some small `t` (at a non-transverse `t` the class-triple set
can be infinite, so its `ncard` is `0`).

This file records the lead's fix: the bundle

> `RefTripleAt Ξ Q R u v cblk t`

of everything the endpoint needs at the single parameter `t` (the level bound, `Meet3Hyp`, the
class-triple parity, the two `GoodAt` facts, and the block-factor data for *some* `g`), and the wrapper

> **`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleOneT`** — `sideGerm Ξ Q c (v - u) +
> sideGerm Ξ Q c (u - v) = 1` from the *existence* of a small `t` with `RefTripleAt`.

The `∀ a` packaging to the statement `Work.Drive.hn2_sideGerm_reference` is then trivial (instantiate
`u := 0`, `v := a`).  Everything here is sorry-free and axiom-clean; the content is the *bundling*.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The reference-triple data at one parameter** (the lead's `NOTES_LEAD_hblock_uniformity.md` §3):
the level bound for the three perturbed planes, `Meet3Hyp` of the perturbed triple, the parity of its
class-triple set, the two pair-goodness facts, and the block-factor data (with the reference block's
factors even and the two mixed factors odd) — everything the `hn2` endpoint consumes, at one `t`. -/
def RefTripleAt {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < levelOf (Ξ (blk k t) (refTriple Q R u v k y))) ∧
    Meet3Hyp CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) ∧
    Odd (classTripleSet (fun k => fun z => Ξ (blk k t) (refTriple Q R u v k z))).ncard ∧
    GoodAt Ξ Q (cblk 1) (v - u) (blk 0 t, blk 1 t) ∧
    GoodAt Ξ Q (cblk 0) (u - v) (blk 1 t, blk 0 t) ∧
    ∃ g : Fin 3 → Fin 3 → ℕ,
      g 0 1 = CntAt Ξ Q (cblk 1) (v - u) (blk 0 t, blk 1 t) ∧
      g 1 0 = CntAt Ξ Q (cblk 0) (u - v) (blk 1 t, blk 0 t) ∧
      (∀ k : Fin 3,
        Odd (topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) k).ncard ↔
          (Odd (g k (k + 1)) ∧ Odd (g k (k + 2)))) ∧
      Even (g 2 0) ∧ Even (g 2 1) ∧ Odd (g 0 2) ∧ Odd (g 1 2)

/-- **`hn2` at one angle, from the reference-triple data at *one* parameter.**  The wrapper of
`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine` promised by
`NOTES_LEAD_hblock_uniformity.md` §3: the only genericity input is the *existence* of a small `t` with
`RefTripleAt`. -/
theorem sideGerm_add_neg_eq_one_of_refTripleOneT
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    {Q : ℂ → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (hQ : IsChartData Q) (c : ℝ) (hc : 0 < c)
    (R : EuclideanSpace ℝ (Fin 2) → CappingSpace) (u v : UnitAddCircle) (cblk : Fin 3 → ℝ)
    (hcpos : ∀ k : Fin 3, 0 < cblk k) (hc1 : cblk 1 < cblk 0) (hc2 : cblk 2 < cblk 0)
    {ε : ℝ} (hε : 0 < ε)
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
        Odd (CntAt Ξ Q c (-(v - u)) s) = Odd (CntAt Ξ Q (cblk 0) (-(v - u)) s))
    (hgen : ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ RefTripleAt (Ξ := Ξ) Q R u v cblk t) :
    sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1 := by
  classical
  obtain ⟨t, ht, hlev, hmeet, hodd, hgood01, hgood10, g, hg01, hg10, hblock, h20, h21, h02, h12⟩ := hgen
  have ht1 : ‖(blk 0 t, blk 1 t)‖ < ε := lt_of_le_of_lt (norm_pair_blk_le 0 1 t) ht
  have ht2 : ‖(blk 1 t, blk 0 t)‖ < ε := lt_of_le_of_lt (norm_pair_blk_le 1 0 t) ht
  have hgood10' : GoodAt Ξ Q (cblk 0) (-(v - u)) (blk 1 t, blk 0 t) := by
    rw [neg_sub]
    exact hgood10
  have hmain := sideGerm_add_neg_eq_one_of_refTripleEngine Ξ Q hΞ hQ.isSmoothChart c hc
    (refTriple Q R u v) (v - u) t cblk g hg01 (by rw [neg_sub]; exact hg10) hcpos hc1 hc2
    hlev hmeet hodd hblock h20 h21 h02 h12
    hε hUa hUa' hparA hUn hUn' hparN ht1 ht2 hgood01 hgood10'
  rwa [neg_sub] at hmain

end

end Work.Drive
