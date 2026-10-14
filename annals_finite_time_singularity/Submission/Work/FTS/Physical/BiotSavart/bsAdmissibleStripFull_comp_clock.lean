import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
-- ===== merged: Submission.Work.FTS.LocData6.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **THE ORDER-`6` LOCALISED DATUM** (without the `GalClass` conjunct).  For every `0 < α ≤ 1`
and every `K > 0` there is `L₀ > 0` such that for every `L ≥ L₀` there is `β` with

* `|β| ≤ K·α²`;
* `DataAdm α (locG α L β (hLoc α))` (N9's datum class);
* `RegQ α 6 (locG α L β (hLoc α))` (the interior regularity class of `LWPStrong`);
* `L₁₂(locG α L β (hLoc α))(0) = 0` (the orthogonality of N9);
* `Xn α (locG α L β (hLoc α)) ≤ α²` (the order-`4` smallness);
* `Xn₆(locG α L β (hLoc α)) ≤ K·α²` (the order-`6` smallness). -/
theorem locG6_data_min (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K : ℝ) (hK : 0 < K) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ K * α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (locG6 α L β) ∧
      Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) ∧
      Work.Construction.L12 (locG6 α L β) 0 = 0 ∧
      Work.FTS.Nonlin.Xn α (locG6 α L β) ≤ α ^ 2 ∧
      Xn6 α (locG6 α L β) ≤ K * α ^ 2 := by
  have hα2 : 0 < α ^ 2 := by positivity
  obtain ⟨L4, h4⟩ := Work.FTS.LocData.locData_small α hα hα1 (α ^ 2) hα2
  obtain ⟨L6, h6⟩ := locG6_small α hα hα1 (K * α ^ 2) (by positivity)
  refine ⟨max 1 (max L4 L6), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL4 : L4 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL6 : L6 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨b4, _hb4, h12a, hnorm4, hadm⟩ := h4 L hL4
  obtain ⟨b6, hb6, h12b, hnorm6⟩ := h6 L hL6
  -- the two scalars coincide: `L₁₂(locG α L · (hLoc α))(0) = 0` determines `β`
  have hDpos : 0 < Work.Construction.L12 (Work.FTS.LocData.hLoc α) 0 :=
    (Work.FTS.LocData.L12_hLoc α hα hα1).2
  have hkey4 := Work.FTS.LocData.L12_locG α L b4 hα hα1 hL1
  have hkey6 := Work.FTS.LocData.L12_locG α L b6 hα hα1 hL1
  have hbeq : b4 = b6 := by
    have h : b4 * Work.Construction.L12 (Work.FTS.LocData.hLoc α) 0
        = b6 * Work.Construction.L12 (Work.FTS.LocData.hLoc α) 0 := by linarith
    exact mul_right_cancel₀ (ne_of_gt hDpos) h
  rw [← hbeq] at hb6 hnorm6
  exact ⟨b4, hb6, hadm, regQ_locG6_uncond α L b4 hα hα1 hL1, h12a, hnorm4, hnorm6⟩

/-- **THE ORDER-`6` LOCALISED DATUM**: `locG6_data_min` together with the class `GalClass α`
(assembled by `LocData6.galClass_locG6_of` from the decay clause `LocData6.decayAll_locG6`). -/
theorem locG6_data (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K : ℝ) (hK : 0 < K) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ K * α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (locG6 α L β) ∧
      Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) ∧
      Work.FTS.Nonlin.GalClass α (locG6 α L β) ∧
      Work.Construction.L12 (locG6 α L β) 0 = 0 ∧
      Work.FTS.Nonlin.Xn α (locG6 α L β) ≤ α ^ 2 ∧
      Xn6 α (locG6 α L β) ≤ K * α ^ 2 := by
  obtain ⟨L₀, hL₀, h⟩ := locG6_data_min α hα hα1 K hK
  refine ⟨max L₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun L hL => ?_⟩
  obtain ⟨β, hβ, hadm, hreg, h12, hX4, hX6⟩ := h L (le_trans (le_max_left _ _) hL)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  exact ⟨β, hβ, hadm, hreg,
    galClass_locG6_of α L β hα hα1 hL1 hreg (decayAll_locG6 α L β hL1) h12,
    h12, hX4, hX6⟩



end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical.BiotSavart

open Work.CoreResiduals (BSAdmissibleStrip BSAdmissibleStripFull TimeDerivStrip
  TimeDerivStripHolder)

/-- **The reparametrisation of an admissible strip bundle by a clock.**  See the module docstring
for the statement and the transport of each clause. -/
theorem bsAdmissibleStripFull_comp_clock {α : NNReal}
    {ω : Work.CoreResiduals.R3 → ℝ → Work.CoreResiduals.R3} {R S T : ℝ}
    (hS : 0 < S) (hT : 0 < T) (hbun : BSAdmissibleStripFull α ω R S)
    {tau d : ℝ → ℝ}
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, tau t ∈ Set.Icc (0 : ℝ) S)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt tau (d t) t)
    (hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ L * |t - t'|)
    (hdbdd : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ L)
    (hdholder : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |d t - d t'| ≤ L * |t - t'| ^ ((α : NNReal) : ℝ)) :
    BSAdmissibleStripFull α (fun x t => ω x (tau t)) R T := by
  obtain ⟨hstrip, htder, htholder⟩ := hbun
  obtain ⟨hRpos, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩ := hstrip
  obtain ⟨hdiff, ⟨M₁, hM₁⟩, hmeasDt⟩ := htder
  obtain ⟨N₁, hN₁⟩ := htholder
  obtain ⟨L, hL⟩ := hlip
  obtain ⟨Ld, hLd⟩ := hdbdd
  obtain ⟨Ld', hLd'⟩ := hdholder
  have hα0 : 0 ≤ ((α : NNReal) : ℝ) := by positivity
  -- nonnegative versions of the constants
  set L₀ : ℝ := max L 0 with hL₀def
  set L₁ : ℝ := max Ld 0 with hL₁def
  set L₂ : ℝ := max Ld' 0 with hL₂def
  have hL₀nn : 0 ≤ L₀ := le_max_right _ _
  have hL₁nn : 0 ≤ L₁ := le_max_right _ _
  have hL₂nn : 0 ≤ L₂ := le_max_right _ _
  have hL₀ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ L₀ * |t - t'| := fun t ht t' ht' =>
    le_trans (hL t ht t' ht') (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hL₁ : ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ L₁ := fun t ht =>
    le_trans (hLd t ht) (le_max_left _ _)
  have hL₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |d t - d t'| ≤ L₂ * |t - t'| ^ ((α : NNReal) : ℝ) := fun t ht t' ht' =>
    le_trans (hLd' t ht t' ht') (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (abs_nonneg _) _))
  -- nonnegative versions of the bundle constants
  have hM₀ : ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ y, ‖ω y t‖ ≤ max M 0 := fun t ht y =>
    le_trans (hM t ht y) (le_max_left M 0)
  have hM₁₀ : ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ y, ‖timeDeriv ω y t‖ ≤ max M₁ 0 := fun t ht y =>
    le_trans (hM₁ t ht y) (le_max_left M₁ 0)
  have hN₀ : ∀ y, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S,
      ‖ω y t - ω y t'‖ ≤ max N 0 * |t - t'| ^ ((α : NNReal) : ℝ) := by
    intro y t ht t' ht'
    rcases le_total 0 N with h | h
    · rw [max_eq_left h]
      exact hN y t ht t' ht'
    · rw [max_eq_right h, zero_mul]
      refine le_trans (hN y t ht t' ht') ?_
      have h0 : 0 ≤ |t - t'| ^ ((α : NNReal) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
      nlinarith
  have hN₁₀ : ∀ y, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S,
      ‖timeDeriv ω y t - timeDeriv ω y t'‖ ≤ max N₁ 0 * |t - t'| ^ ((α : NNReal) : ℝ) := by
    intro y t ht t' ht'
    rcases le_total 0 N₁ with h | h
    · rw [max_eq_left h]
      exact hN₁ y t ht t' ht'
    · rw [max_eq_right h, zero_mul]
      refine le_trans (hN₁ y t ht t' ht') ?_
      have h0 : 0 ≤ |t - t'| ^ ((α : NNReal) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
      nlinarith
  -- the chain rule along the clock
  have hchain : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y,
      timeDeriv (fun x s => ω x (tau s)) y t = (d t) • timeDeriv ω y (tau t) := by
    intro t ht y
    exact ((hdiff (tau t) (hmem t ht) y).scomp t (hderiv t ht)).deriv
  refine ⟨?_, ?_, ?_⟩
  · -- `BSAdmissibleStrip`
    refine ⟨hRpos, ?_, ⟨max M 0, fun t ht y => hM₀ (tau t) (hmem t ht) y⟩,
      ⟨H, fun t ht => hH (tau t) (hmem t ht)⟩, ?_, ?_⟩
    · intro t ht y hy
      exact hsupp (tau t) (hmem t ht) y hy
    · -- time-Hölder of the reparametrised field
      refine ⟨max N 0 * L₀ ^ ((α : NNReal) : ℝ), fun y t ht t' ht' => ?_⟩
      have h1 := hN₀ y (tau t) (hmem t ht) (tau t') (hmem t' ht')
      have h2 : max N 0 * |tau t - tau t'| ^ ((α : NNReal) : ℝ)
          ≤ max N 0 * (L₀ * |t - t'|) ^ ((α : NNReal) : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hL₀ t ht t' ht') hα0)
          (le_max_right N 0)
      have h3 : max N 0 * (L₀ * |t - t'|) ^ ((α : NNReal) : ℝ)
          = (max N 0 * L₀ ^ ((α : NNReal) : ℝ)) * |t - t'| ^ ((α : NNReal) : ℝ) := by
        rw [Real.mul_rpow hL₀nn (abs_nonneg _)]
        ring
      calc ‖ω y (tau t) - ω y (tau t')‖
            ≤ max N 0 * |tau t - tau t'| ^ ((α : NNReal) : ℝ) := h1
        _ ≤ max N 0 * (L₀ * |t - t'|) ^ ((α : NNReal) : ℝ) := h2
        _ = (max N 0 * L₀ ^ ((α : NNReal) : ℝ)) * |t - t'| ^ ((α : NNReal) : ℝ) := h3
    · intro t ht
      exact hmeas (tau t) (hmem t ht)
  · -- `TimeDerivStrip`
    refine ⟨?_, ?_, ?_⟩
    · intro t ht y
      have h := (hdiff (tau t) (hmem t ht) y).scomp t (hderiv t ht)
      rw [hchain t ht y]
      exact h
    · refine ⟨max M₁ 0 * L₁, fun t ht y => ?_⟩
      rw [hchain t ht y, norm_smul, Real.norm_eq_abs]
      calc |d t| * ‖timeDeriv ω y (tau t)‖ ≤ L₁ * max M₁ 0 :=
            mul_le_mul (hL₁ t ht) (hM₁₀ (tau t) (hmem t ht) y) (norm_nonneg _) hL₁nn
        _ = max M₁ 0 * L₁ := by ring
    · intro t ht
      rw [show (fun y => timeDeriv (fun x s => ω x (tau s)) y t)
          = fun y => (d t) • timeDeriv ω y (tau t) from funext (hchain t ht)]
      exact (hmeasDt (tau t) (hmem t ht)).const_smul (d t)
  · -- `TimeDerivStripHolder`
    refine ⟨max (max N₁ 0 * L₀ ^ ((α : NNReal) : ℝ) * L₁ + max M₁ 0 * L₂)
      (4 * (max M₁ 0 * L₁)), fun y t ht t' ht' => ?_⟩
    rw [hchain t ht y, hchain t' ht' y]
    have hsplit : (d t) • timeDeriv ω y (tau t) - (d t') • timeDeriv ω y (tau t')
        = (d t) • (timeDeriv ω y (tau t) - timeDeriv ω y (tau t'))
          + (d t - d t') • timeDeriv ω y (tau t') := by
      module
    rw [hsplit]
    have htri : ‖(d t) • (timeDeriv ω y (tau t) - timeDeriv ω y (tau t'))
          + (d t - d t') • timeDeriv ω y (tau t')‖
        ≤ |d t| * ‖timeDeriv ω y (tau t) - timeDeriv ω y (tau t')‖
          + |d t - d t'| * ‖timeDeriv ω y (tau t')‖ := by
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
      · rw [norm_smul, Real.norm_eq_abs]
    rcases le_total |t - t'| 1 with hsmall | hbig
    · -- the small step
      have h1 : ‖timeDeriv ω y (tau t) - timeDeriv ω y (tau t')‖
          ≤ (max N₁ 0 * L₀ ^ ((α : NNReal) : ℝ)) * |t - t'| ^ ((α : NNReal) : ℝ) := by
        refine le_trans (hN₁₀ y (tau t) (hmem t ht) (tau t') (hmem t' ht')) ?_
        have hpow : (L₀ * |t - t'|) ^ ((α : NNReal) : ℝ)
            = L₀ ^ ((α : NNReal) : ℝ) * |t - t'| ^ ((α : NNReal) : ℝ) :=
          Real.mul_rpow hL₀nn (abs_nonneg _)
        calc max N₁ 0 * |tau t - tau t'| ^ ((α : NNReal) : ℝ)
            ≤ max N₁ 0 * (L₀ * |t - t'|) ^ ((α : NNReal) : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hL₀ t ht t' ht') hα0)
                (le_max_right N₁ 0)
          _ = (max N₁ 0 * L₀ ^ ((α : NNReal) : ℝ)) * |t - t'| ^ ((α : NNReal) : ℝ) := by
              rw [hpow]; ring
      calc ‖(d t) • (timeDeriv ω y (tau t) - timeDeriv ω y (tau t'))
            + (d t - d t') • timeDeriv ω y (tau t')‖
          ≤ |d t| * ‖timeDeriv ω y (tau t) - timeDeriv ω y (tau t')‖
            + |d t - d t'| * ‖timeDeriv ω y (tau t')‖ := htri
        _ ≤ L₁ * ((max N₁ 0 * L₀ ^ ((α : NNReal) : ℝ)) * |t - t'| ^ ((α : NNReal) : ℝ))
            + (L₂ * |t - t'| ^ ((α : NNReal) : ℝ)) * (max M₁ 0) := by
            refine add_le_add (mul_le_mul (hL₁ t ht) h1 (norm_nonneg _) hL₁nn)
              (mul_le_mul (hL₂ t ht t' ht') (hM₁₀ (tau t') (hmem t' ht') y) (norm_nonneg _)
                (mul_nonneg hL₂nn (Real.rpow_nonneg (abs_nonneg _) _)))
        _ = (max N₁ 0 * L₀ ^ ((α : NNReal) : ℝ) * L₁ + max M₁ 0 * L₂)
              * |t - t'| ^ ((α : NNReal) : ℝ) := by ring
        _ ≤ max (max N₁ 0 * L₀ ^ ((α : NNReal) : ℝ) * L₁ + max M₁ 0 * L₂)
              (4 * (max M₁ 0 * L₁)) * |t - t'| ^ ((α : NNReal) : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
    · -- the large step: the crude bound suffices since `|t - t'|^α ≥ 1`
      have hone : (1 : ℝ) ≤ |t - t'| ^ ((α : NNReal) : ℝ) := Real.one_le_rpow hbig hα0
      have hcrude : ‖timeDeriv ω y (tau t) - timeDeriv ω y (tau t')‖ ≤ 2 * max M₁ 0 := by
        refine le_trans (norm_sub_le _ _) ?_
        have h1 := hM₁₀ (tau t) (hmem t ht) y
        have h2 := hM₁₀ (tau t') (hmem t' ht') y
        linarith
      have hd2 : |d t - d t'| ≤ 2 * L₁ := by
        have h1 := (abs_le.mp (hL₁ t ht)).1
        have h2 := (abs_le.mp (hL₁ t ht)).2
        have h3 := (abs_le.mp (hL₁ t' ht')).1
        have h4 := (abs_le.mp (hL₁ t' ht')).2
        rw [abs_le]
        constructor <;> linarith
      calc ‖(d t) • (timeDeriv ω y (tau t) - timeDeriv ω y (tau t'))
            + (d t - d t') • timeDeriv ω y (tau t')‖
          ≤ |d t| * ‖timeDeriv ω y (tau t) - timeDeriv ω y (tau t')‖
            + |d t - d t'| * ‖timeDeriv ω y (tau t')‖ := htri
        _ ≤ L₁ * (2 * max M₁ 0) + (2 * L₁) * (max M₁ 0) := by
            refine add_le_add (mul_le_mul (hL₁ t ht) hcrude (norm_nonneg _) hL₁nn)
              (mul_le_mul hd2 (hM₁₀ (tau t') (hmem t' ht') y) (norm_nonneg _)
                (by linarith [hL₁nn]))
        _ = (4 * (max M₁ 0 * L₁)) * 1 := by ring
        _ ≤ (4 * (max M₁ 0 * L₁)) * |t - t'| ^ ((α : NNReal) : ℝ) :=
            mul_le_mul_of_nonneg_left hone (by nlinarith [le_max_right M₁ 0, hL₁nn])
        _ ≤ max (max N₁ 0 * L₀ ^ ((α : NNReal) : ℝ) * L₁ + max M₁ 0 * L₂)
              (4 * (max M₁ 0 * L₁)) * |t - t'| ^ ((α : NNReal) : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)

end Work.FTS.Physical.BiotSavart
end
