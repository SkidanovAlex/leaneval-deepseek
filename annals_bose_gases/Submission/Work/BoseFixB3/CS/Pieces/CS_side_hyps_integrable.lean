import ChallengeDeps
import Submission.Work.BoseFixB3.CS.Pieces.CS_box_hyps_of_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.CS_side_hyps_of_integrable`

**The repair of `Pieces.CS_side_hyps`**: the same seven-conjunct statement, with the missing
standing hypothesis of the paper's Theorem 1.2 — `v ∈ L¹(ℝ³)` — added.  See
`Submission/Work/BoseFixB3/CS/Pieces/FINDING_CS_side_hyps_missing_Integrable_v.md` for the proof
that the un-repaired statement is *false* (its first conjunct is equivalent to `v · w₀² ∈ L¹`,
which the listed hypotheses do not imply).

The two halves are proved separately and independently:

* `Pieces.CS_pair_hyps_of_integrable` — the two `volume.prod volume` conjuncts
  (via `integrable_prod_wPair_mul_bounded` and the a.e. bounds on `w₀`);
* `Pieces.CS_box_hyps_of_integrable` — the five box conjuncts
  (via `ae_bounded_q4B_abox` + `integrableOn_bounded_mul_wPair_sub_abox`).

`CS_side_hyps_of_integrable` is their conjunction, stated exactly in the shape of the original
target, so that it can replace `CS_side_hyps` verbatim in the `CS` chain (where `v ∈ L¹` is
available: `Work.BoseFixB3.CS.b3CSRoot_holds` carries `hv1 : MeasureTheory.MemLp v 1`).
The `MemLp v 1` form is `CS_side_hyps_of_memLp` below.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`CS_side_hyps` with the missing hypothesis `Integrable v`** (all seven conjuncts, verbatim
in the shape of the target). -/
theorem CS_side_hyps_of_integrable {v : E3 → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv_int : MeasureTheory.Integrable v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.Integrable (fun z : E3 × E3 =>
        (Classical.choose h (z.1 - z.2)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 z.1 z.2) ∧
    MeasureTheory.Integrable (fun z : E3 × E3 =>
        Work.BoseFixB3.CS.leakFn fc κ ℓ z.2 * (Classical.choose h (z.1 - z.2))
          * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 z.1 z.2) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
          * (Classical.choose h (x p.1 - x p.2)) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
            - Classical.choose h (x p.1 - x p.2)
              * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) := by
  obtain ⟨h1, h2⟩ :=
    CS_pair_hyps_of_integrable hv hvrad hv_int R hR hv_supp hav h hκ hℓ hRℓ
  obtain ⟨h3, h4, h5, h6, h7⟩ :=
    CS_box_hyps_of_integrable (fc := fc) hv hvrad hv_int R hR hv_supp hav h hκ hℓ hRℓ hΦc
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The `MemLp` form of `CS_side_hyps_of_integrable` (the corpus's standing hypothesis
`MeasureTheory.MemLp v 1`). -/
theorem CS_side_hyps_of_memLp {v : E3 → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.Integrable (fun z : E3 × E3 =>
        (Classical.choose h (z.1 - z.2)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 z.1 z.2) ∧
    MeasureTheory.Integrable (fun z : E3 × E3 =>
        Work.BoseFixB3.CS.leakFn fc κ ℓ z.2 * (Classical.choose h (z.1 - z.2))
          * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 z.1 z.2) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
          * (Classical.choose h (x p.1 - x p.2)) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
            - Classical.choose h (x p.1 - x p.2)
              * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) :=
  CS_side_hyps_of_integrable hv hvrad (MeasureTheory.memLp_one_iff_integrable.mp hv1) R hR
    hv_supp hav h hκ hℓ hRℓ hΦc

end

end Work.BoseFixB3.CS.Pieces
