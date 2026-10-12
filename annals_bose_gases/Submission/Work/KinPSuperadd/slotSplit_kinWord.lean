import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SlotSplit` for the corpus kinetic word `kinWord`

This file proves the one obligation named in `KinPSuperadd/Defs.lean` for the
word actually delivered by the corpus:

    `SlotSplit s (fun N Φ => kinWord N s Φ)`.

The proof is a case distinction on the sign of the box side `s`.

* For `0 < s` the block decomposition

      kinWord (N₁+N₂) s Φ
        = ∫_{w ∈ abox N₂ s} kinWord N₁ s (fun u ↦ Φ (mergeBlock (u,w)))
        + ∫_{u ∈ abox N₁ s} kinWord N₂ s (fun w ↦ Φ (mergeBlock (u,w)))

  is the combination of the pure index splitting `kinWord_block_split`
  (`SmallBoxSuperadd`) with the two slice/kinetic identities
  `kin_slice1_integral` / `kin_slice2_integral` (`SboxESlice`), which are
  `aboxFubini` plus the domain-free derivative identities of `EneuSuperadd`.
  The two slice-integrability fields are the Fubini marginal of the block
  kinetic densities `es_kinB1`/`es_kinB2` (continuous on the compact box).

* For `s ≤ 0` the centred cube is contained in `{0}` (empty when `s < 0`), so
  every centred box `abox N s` is a null set and `kinWord N s Φ = 0`
  identically; both sides of the decomposition vanish.

The helper lemma `kinWord_eq_zero_of_nonpos` records the degenerate case.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.KinPSuperadd

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- For a nonpositive side length `s` the centred cube `acube s` is contained
in `{0}` (and is empty when `s < 0`); consequently every centred box
`abox N s` is a null set and the kinetic word `kinWord N s Φ` vanishes. -/
lemma kinWord_eq_zero_of_nonpos {N : ℕ} {s : ℝ} (hs : s ≤ 0) (Φ : X N → ℝ) :
    kinWord N s Φ = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [kinWord]
  · have hvol : (volume : Measure (X N)) (abox N s) = 0 := by
      rcases lt_or_eq_of_le hs with hlt | heq
      · -- `s < 0`: the centred cube, hence the box, is empty
        have hInt : Set.Icc (-s / 2) (s / 2) = (∅ : Set ℝ) :=
          Set.Icc_eq_empty (by linarith)
        have hacube : acube s = (∅ : Set ℝ³) := by
          ext y
          rw [mem_acube_iff, Set.mem_empty_iff_false]
          exact ⟨fun h => by
            have h0 := h 0
            rw [hInt] at h0
            exact h0, fun h => absurd h (Set.notMem_empty y)⟩
        have habox : abox N s = (∅ : Set (X N)) := by
          ext x
          rw [mem_abox_iff, Set.mem_empty_iff_false]
          exact ⟨fun h => by
            have h0 := h ⟨0, hN⟩
            rw [hacube] at h0
            exact h0, fun h => absurd h (Set.notMem_empty x)⟩
        rw [habox, measure_empty]
      · -- `s = 0`: the box is a single point, of volume `(0³)^N = 0` (as `N ≥ 1`)
        rw [heq, abox_volume N 0 le_rfl]
        have hpow : ((0 : ℝ) ^ 3) ^ N = 0 := by
          rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0),
            zero_pow (Nat.pos_iff_ne_zero.mp hN)]
        rw [hpow, ENNReal.ofReal_zero]
    have hz : (volume : Measure (X N)).restrict (abox N s) = 0 :=
      Measure.restrict_eq_zero.mpr hvol
    unfold kinWord
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun k _ => ?_))
    rw [hz]
    exact integral_zero_measure _

theorem slotSplit_kinWord (s : ℝ) :
    @Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
        => @Submission.BoseGases.kinWord N s Φ) := by
  by_cases hs : 0 < s
  · refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      rw [kinWord_block_split s Φ, kin_slice1_integral hs hΦ, kin_slice2_integral hs hΦ]
      rfl
    · intro N1 N2 Φ hΦ
      have hFint := abox_prod_integrable (N1 := N1) (N2 := N2) s (es_kinB1 N1 N2 Φ)
        (es_kinB1_integrableOn_abox hs hΦ)
      have hmarg := hFint.integral_prod_right
      refine hmarg.congr ?_
      filter_upwards with w
      change ∫ (x : X N1) in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (x, w))
          = kinWord N1 s (es_slice1 N1 N2 Φ w)
      rw [kinWord_eq_integral_es_kinAll hs (es_slice1_contDiff hΦ w)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact (slice1_kinAll_eq hΦ x w).symm
    · intro N1 N2 Φ hΦ
      have hFint := abox_prod_integrable (N1 := N1) (N2 := N2) s (es_kinB2 N1 N2 Φ)
        (es_kinB2_integrableOn_abox hs hΦ)
      have hmarg := hFint.integral_prod_left
      refine hmarg.congr ?_
      filter_upwards with u
      change ∫ (y : X N2) in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, y))
          = kinWord N2 s (es_slice2 N1 N2 Φ u)
      rw [kinWord_eq_integral_es_kinAll hs (es_slice2_contDiff hΦ u)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact (slice2_kinAll_eq hΦ u x).symm
  · have hsle : s ≤ 0 := le_of_not_gt hs
    refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      simp [kinWord_eq_zero_of_nonpos hsle]
    · intro N1 N2 Φ hΦ
      simp [kinWord_eq_zero_of_nonpos hsle]
    · intro N1 N2 Φ hΦ
      simp [kinWord_eq_zero_of_nonpos hsle]

end Work.KinPSuperadd
