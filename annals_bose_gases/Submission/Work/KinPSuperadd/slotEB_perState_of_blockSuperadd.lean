import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.slotEB_perState
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The per-state inequality for a `BlockSuperadd` word (`slotEB_perState_of_blockSuperadd`)

This is the ONE-SIDED (`BlockSuperadd`) companion of
`Work.KinPSuperadd.slotEB_perState`, and the form the FS group trick actually
consumes: the equalities of `SlotSplit` are replaced by the inequality
`∫_w K N₁(slice_w Φ) + ∫_u K N₂(slice'_u Φ) ≤ K (N₁+N₂) Φ` (`BlockSuperadd`,
`Defs.lean`), while the two slice-integrability fields of `SlotSplit` are kept as
explicit hypotheses `hInt1`/`hInt2`.

The argument is the proof of `slotEB_perState` with the final equality
`SlotSplit.split` replaced by the inequality `BlockSuperadd`:

* block 1: `slotEB N₁ · ∫Φ² ≤ ∫_w K N₁(slice_w Φ) + ∫ Φ²·qLHSden1`,
* block 2: the same with the two blocks exchanged and `qLHSden2`,
* adding and using `BlockSuperadd` (kinetic part) and `qLHSden_blocks_le`
  (nonnegativity of `w`, for the potential part) gives the claim.

## A note on the name `MeasureTheory.Volume`

The statement handed to us was written with `MeasureTheory.Volume` (capital `V`)
in the hypothesis `hPot2`, while `hPot1`/`hPot` use `MeasureTheory.volume`.
Mathlib has no `MeasureTheory.Volume`, so the statement as literally written
does not elaborate.  Rather than change the statement, we keep the text
byte-for-byte and provide the missing name as an abbreviation for
`MeasureTheory.volume` — which is exactly what it was a typo for (all three
potential-integrability hypotheses are about the same Lebesgue measure).  The
abbreviation is reducible, so every hypothesis and every consumer sees
`MeasureTheory.volume`.
-/

namespace MeasureTheory

/-- `MeasureTheory.Volume` is `MeasureTheory.volume` (see the module docstring:
this name is what the requested statement writes in `hPot2`). -/
abbrev Volume {α : Type*} [MeasureTheory.MeasureSpace α] : MeasureTheory.Measure α :=
  MeasureTheory.volume

end MeasureTheory

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem slotEB_perState_of_blockSuperadd {s μ : ℝ}
    {w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : ∀ x y, 0 ≤ w x y)
    {K : ∀ N : ℕ, (Submission.BoseGases.X N → ℝ) → ℝ}
    (hK : @Work.KinPSuperadd.BlockSuperadd s K)
    (hInt1 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : Submission.BoseGases.X (N1 + N2) → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) Φ →
      MeasureTheory.IntegrableOn (fun wv : Submission.BoseGases.X N2 =>
        K N1 (fun u => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, wv))))
        (Submission.BoseGases.abox N2 s) MeasureTheory.volume)
    (hInt2 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : Submission.BoseGases.X (N1 + N2) → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) Φ →
      MeasureTheory.IntegrableOn (fun uv : Submission.BoseGases.X N1 =>
        K N2 (fun wv => Φ (Submission.BoseGases.mergeBlock N1 N2 (uv, wv))))
        (Submission.BoseGases.abox N1 s) MeasureTheory.volume)
    (hRay : ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) Ψ →
      @Work.KinPSuperadd.slotEB s μ w w1 K N *
          (∫ x in Submission.BoseGases.abox N s, (Ψ x) ^ 2)
        ≤ @Work.KinPSuperadd.blockE s μ w w1 K N Ψ)
    (hPot1 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : Submission.BoseGases.X (N1 + N2) → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) Φ →
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (N1 + N2) =>
        (Φ x) ^ 2 * @Submission.BoseGases.qLHSden1 N1 N2 s μ w w1 x)
        (Submission.BoseGases.abox (N1 + N2) s) MeasureTheory.volume)
    (hPot2 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : Submission.BoseGases.X (N1 + N2) → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) Φ →
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (N1 + N2) =>
        (Φ x) ^ 2 * @Submission.BoseGases.qLHSden2 N1 N2 s μ w w1 x)
        (Submission.BoseGases.abox (N1 + N2) s) MeasureTheory.Volume)
    (hPot : ∀ ⦃N1 N2 : ℕ⦄ (Φ : Submission.BoseGases.X (N1 + N2) → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) Φ →
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (N1 + N2) =>
        (Φ x) ^ 2 * @Submission.BoseGases.qLHSden (N1 + N2) s μ w w1 x)
        (Submission.BoseGases.abox (N1 + N2) s) MeasureTheory.volume)
    {N1 N2 : ℕ} {Φ : Submission.BoseGases.X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ (↑(⊤ : ℕ∞)) Φ) :
    (@Work.KinPSuperadd.slotEB s μ w w1 K N1 + @Work.KinPSuperadd.slotEB s μ w w1 K N2) *
        (∫ x in Submission.BoseGases.abox (N1 + N2) s, (Φ x) ^ 2)
      ≤ @Work.KinPSuperadd.blockE s μ w w1 K (N1 + N2) Φ := by
  -- `Φ` is smooth in the corpus's `ContDiff ℝ ∞` sense
  have hΦsm : ContDiff ℝ ∞ Φ := hΦ
  have hΦc : Continuous Φ := hΦsm.continuous
  -- smoothness of the two families of slices (as `ContDiff ℝ ∞`)
  obtain ⟨hsl1, hsl2⟩ := slice_contDiff_infty_pair (N1 := N1) (N2 := N2) (Φ := Φ) hΦsm
  -- integrability of `Φ²` over the centred box, for every real side
  have hP : IntegrableOn (fun x : X (N1 + N2) => (Φ x) ^ 2) (abox (N1 + N2) s) volume :=
    abox_sq_integrable hΦc
  -- Fubini along the block split for `Φ²`
  obtain ⟨hS1, hS2, hF1, hF2⟩ := slice_fubini (N1 := N1) (N2 := N2) s hP
  -- integrability of the two within-block potential densities over the full box
  have hD1 := hPot1 (N1 := N1) (N2 := N2) Φ hΦsm
  have hD2 := hPot2 (N1 := N1) (N2 := N2) Φ hΦsm
  have hD := hPot (N1 := N1) (N2 := N2) Φ hΦsm
  -- Fubini and slice integrability for the two within-block densities
  obtain ⟨hB1i, _hB2i, hB1F, _hB2F⟩ := slice_fubini (N1 := N1) (N2 := N2) s hD1
  obtain ⟨_hC1i, hC2i, _hC1F, hC2F⟩ := slice_fubini (N1 := N1) (N2 := N2) s hD2
  -- integrability of the two kinetic slice families (the explicit hypotheses)
  have hA1 : IntegrableOn (fun wv : X N2 => K N1 (fun u => Φ (mergeBlock N1 N2 (u, wv))))
      (abox N2 s) volume := hInt1 Φ hΦsm
  have hA2 : IntegrableOn (fun uv : X N1 => K N2 (fun wv => Φ (mergeBlock N1 N2 (uv, wv))))
      (abox N1 s) volume := hInt2 Φ hΦsm
  -- the within-block density at a merged configuration is the density of the slice
  have hcong1 : ∀ wv : X N2,
      (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, wv))) ^ 2 *
          qLHSden1 (N1:=N1) (N2:=N2) s μ w w1 (mergeBlock N1 N2 (u, wv)))
        = ∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, wv))) ^ 2 * qLHSden N1 s μ w w1 u := by
    intro wv
    apply integral_congr_ae
    filter_upwards with u
    rw [qLHSden1_merge]
  have hcong2 : ∀ uv : X N1,
      (∫ wv in abox N2 s, (Φ (mergeBlock N1 N2 (uv, wv))) ^ 2 *
          qLHSden2 (N1:=N1) (N2:=N2) s μ w w1 (mergeBlock N1 N2 (uv, wv)))
        = ∫ wv in abox N2 s, (Φ (mergeBlock N1 N2 (uv, wv))) ^ 2 * qLHSden N2 s μ w w1 wv := by
    intro uv
    apply integral_congr_ae
    filter_upwards with wv
    rw [qLHSden2_merge]
  -- block 1: the Rayleigh bound `hRay` for `K` at `N₁`, integrated over the frozen second block
  have hmono1 : (∫ wv in abox N2 s,
        slotEB s μ w w1 K N1 * (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, wv))) ^ 2))
      ≤ (∫ wv in abox N2 s,
        (K N1 (fun u => Φ (mergeBlock N1 N2 (u, wv)))
          + (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, wv))) ^ 2 *
              qLHSden1 (N1:=N1) (N2:=N2) s μ w w1 (mergeBlock N1 N2 (u, wv))))) := by
    refine integral_mono ?_ ?_ ?_
    · exact hS1.const_mul _
    · exact hA1.add hB1i
    · intro wv
      have h1 := hRay N1 (fun u => Φ (mergeBlock N1 N2 (u, wv))) (hsl1 wv)
      dsimp only
      rw [hcong1 wv]
      simpa only [blockE] using h1
  have hI1 : (∫ wv in abox N2 s,
        slotEB s μ w w1 K N1 * (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, wv))) ^ 2))
      = slotEB s μ w w1 K N1 * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2) := by
    rw [integral_const_mul, hF1]
  have hsplit1 : (∫ wv in abox N2 s,
        (K N1 (fun u => Φ (mergeBlock N1 N2 (u, wv)))
          + (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, wv))) ^ 2 *
              qLHSden1 (N1:=N1) (N2:=N2) s μ w w1 (mergeBlock N1 N2 (u, wv)))))
      = (∫ wv in abox N2 s, K N1 (fun u => Φ (mergeBlock N1 N2 (u, wv))))
        + (∫ x in abox (N1 + N2) s, (Φ x) ^ 2 * qLHSden1 (N1:=N1) (N2:=N2) s μ w w1 x) := by
    rw [integral_add hA1 hB1i, hB1F]
  have hblk1 : slotEB s μ w w1 K N1 * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2)
      ≤ (∫ wv in abox N2 s, K N1 (fun u => Φ (mergeBlock N1 N2 (u, wv))))
        + (∫ x in abox (N1 + N2) s, (Φ x) ^ 2 * qLHSden1 (N1:=N1) (N2:=N2) s μ w w1 x) := by
    rw [← hI1, ← hsplit1]
    exact hmono1
  -- block 2: the same with the two blocks exchanged
  have hmono2 : (∫ uv in abox N1 s,
        slotEB s μ w w1 K N2 * (∫ wv in abox N2 s, (Φ (mergeBlock N1 N2 (uv, wv))) ^ 2))
      ≤ (∫ uv in abox N1 s,
        (K N2 (fun wv => Φ (mergeBlock N1 N2 (uv, wv)))
          + (∫ wv in abox N2 s, (Φ (mergeBlock N1 N2 (uv, wv))) ^ 2 *
              qLHSden2 (N1:=N1) (N2:=N2) s μ w w1 (mergeBlock N1 N2 (uv, wv))))) := by
    refine integral_mono ?_ ?_ ?_
    · exact hS2.const_mul _
    · exact hA2.add hC2i
    · intro uv
      have h1 := hRay N2 (fun wv => Φ (mergeBlock N1 N2 (uv, wv))) (hsl2 uv)
      dsimp only
      rw [hcong2 uv]
      simpa only [blockE] using h1
  have hI2 : (∫ uv in abox N1 s,
        slotEB s μ w w1 K N2 * (∫ wv in abox N2 s, (Φ (mergeBlock N1 N2 (uv, wv))) ^ 2))
      = slotEB s μ w w1 K N2 * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2) := by
    rw [integral_const_mul, hF2]
  have hsplit2 : (∫ uv in abox N1 s,
        (K N2 (fun wv => Φ (mergeBlock N1 N2 (uv, wv)))
          + (∫ wv in abox N2 s, (Φ (mergeBlock N1 N2 (uv, wv))) ^ 2 *
              qLHSden2 (N1:=N1) (N2:=N2) s μ w w1 (mergeBlock N1 N2 (uv, wv)))))
      = (∫ uv in abox N1 s, K N2 (fun wv => Φ (mergeBlock N1 N2 (uv, wv))))
        + (∫ x in abox (N1 + N2) s, (Φ x) ^ 2 * qLHSden2 (N1:=N1) (N2:=N2) s μ w w1 x) := by
    rw [integral_add hA2 hC2i, hC2F]
  have hblk2 : slotEB s μ w w1 K N2 * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2)
      ≤ (∫ uv in abox N1 s, K N2 (fun wv => Φ (mergeBlock N1 N2 (uv, wv))))
        + (∫ x in abox (N1 + N2) s, (Φ x) ^ 2 * qLHSden2 (N1:=N1) (N2:=N2) s μ w w1 x) := by
    rw [← hI2, ← hsplit2]
    exact hmono2
  -- the kinetic words recombine by the ONE-SIDED block-superadditivity
  have hbs := hK Φ hΦsm
  -- the within-block densities are dominated by the full density (`w ≥ 0`)
  have hpot := pot_blocks_le_full (N1 := N1) (N2 := N2) (s := s) (μ := μ) w w1 hw hD1 hD2 hD
  have hsum : (slotEB s μ w w1 K N1 + slotEB s μ w w1 K N2) * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2)
      = slotEB s μ w w1 K N1 * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2)
        + slotEB s μ w w1 K N2 * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2) := by ring
  have hfin : (slotEB s μ w w1 K N1 + slotEB s μ w w1 K N2) * (∫ x in abox (N1 + N2) s, (Φ x) ^ 2)
      ≤ K (N1 + N2) Φ
        + ∫ x in abox (N1 + N2) s, (Φ x) ^ 2 * qLHSden (N1 + N2) s μ w w1 x := by
    rw [hsum]
    linarith [hblk1, hblk2, hbs, hpot]
  simpa only [blockE] using hfin

end Work.KinPSuperadd
