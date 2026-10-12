import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseFixB1S.PiAnova.fibreCS_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.fibre_update_sq_le`

The **squared fibre mean of a state on the `m`-particle centred box**:

    ∫_{r ∈ abox m ℓ} (∫_{u ∈ acube ℓ} |F (r[j' ↦ u])|)²  ≤  ℓ³ · (ℓ³ · ∫_{r ∈ abox m ℓ} F r²) .

This is the *unreduced* version of `Work.BoseBoxFock.PCFU.fibreMean_sq_integral_le`: the
replacement map `r ↦ Function.update r j' u` keeps the particle number (it overwrites the `j'`-th
slot) whereas `kcInsN` inserts a new one, so the constant acquires a second factor `ℓ³`.

Proof.  Write `m = k + 1` (for `j' : Fin m`).  With `ν = volume ↾ acube ℓ` and
`π = Measure.pi (fun _ : Fin (k+1) => ν)` (so that `π = volume ↾ abox (k+1) ℓ` by
`Submission.BoseGases.restrict_abox_eq_pi`):

* the fibre Cauchy–Schwarz `Work.BoseFixB1S.PiAnova.fibreCS_prod` on the product measure
  `ν ⊗ π` gives `∫_r (∫_u |F (r[j' ↦ u])|)² ≤ (ν univ).toReal · ∫_p |F (p.2[j' ↦ p.1])|²`;
* `integral_prod_symm` identifies the product integral with the iterated one, and the one
  coordinate peel `Work.BoseFixB1S.pi_peel` (which is exactly `∫_p (… p.2 j' p.1)²
  = (ν univ).toReal · ∫_y (… y)²`, i.e. the `ℓ³` of the *overwritten* slot) evaluates it;
* `(ν univ).toReal = ℓ³` (`acube_volume`).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem fibre_update_sq_le {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j' : Fin m)
    {F : Submission.BoseGases.X m → ℝ} (hFm : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hFb : ∀ x, |F x| ≤ C) :
    (∫ r in Submission.BoseGases.abox m ℓ,
        (∫ u in Submission.BoseGases.acube ℓ, |F (Function.update r j' u)|) ^ 2)
      ≤ ℓ ^ 3 * (ℓ ^ 3 * ∫ r in Submission.BoseGases.abox m ℓ, (F r) ^ 2) := by
  classical
  have hm : 0 < m := j'.pos
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- the one-particle measure `ν` (restricted centred cube) and the product measure `π`
  set νc : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hνc
  set πc : Measure (Submission.BoseGases.X (k + 1)) :=
    Measure.pi (fun x : Fin (k + 1) => νc) with hπc
  have hνuniv : νc Set.univ = ENNReal.ofReal (ℓ ^ 3) := by
    rw [hνc, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
  haveI : IsFiniteMeasure νc := ⟨by rw [hνuniv]; exact ENNReal.ofReal_lt_top⟩
  have hνto : (νc Set.univ).toReal = ℓ ^ 3 := by
    rw [hνuniv, ENNReal.toReal_ofReal (by positivity)]
  have hπfin : πc Set.univ < ∞ := by
    rw [hπc, Measure.pi_univ]
    exact ENNReal.prod_lt_top (fun i _ => by rw [hνuniv]; exact ENNReal.ofReal_lt_top)
  haveI : IsFiniteMeasure πc := ⟨hπfin⟩
  -- `π` is the restricted `m`-particle box measure
  have hMc : (volume : Measure (Submission.BoseGases.X (k + 1))).restrict
      (Submission.BoseGases.abox (k + 1) ℓ) = πc := by
    rw [hπc, hνc, ← Submission.BoseGases.restrict_abox_eq_pi]
  -- the joint replacement map is measurable
  have hupd : Measurable (fun p : E3 × Submission.BoseGases.X (k + 1) =>
      Function.update p.2 j' p.1) := by
    refine Measurable.of_eval (fun i => ?_)
    by_cases hi : i = j'
    · subst hi
      have h : (fun p : E3 × Submission.BoseGases.X (k + 1) =>
          Function.update p.2 i p.1 i) = fun p => p.1 := by
        funext p; rw [Function.update_apply, if_pos rfl]
      rw [h]; exact measurable_fst
    · have h : (fun p : E3 × Submission.BoseGases.X (k + 1) =>
          Function.update p.2 j' p.1 i) = fun p => p.2 i := by
        funext p; rw [Function.update_apply, if_neg hi]
      rw [h]; exact (measurable_pi_apply i).comp measurable_snd
  have hGabs : AEStronglyMeasurable
      (fun p : E3 × Submission.BoseGases.X (k + 1) => |F (Function.update p.2 j' p.1)|)
      (νc.prod πc) :=
    (continuous_abs.measurable.comp (hFm.comp hupd)).aestronglyMeasurable
  -- square integrability, from the uniform bound
  have hsqabs : Integrable
      (fun p : E3 × Submission.BoseGases.X (k + 1) => |F (Function.update p.2 j' p.1)| ^ 2)
      (νc.prod πc) := by
    refine Integrable.mono' (integrable_const (C ^ 2)) (hGabs.pow 2) ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hFb _) 2
  have hsq : Integrable
      (fun p : E3 × Submission.BoseGases.X (k + 1) => (F (Function.update p.2 j' p.1)) ^ 2)
      (νc.prod πc) := by
    simpa only [sq_abs] using hsqabs
  have hGsq : Integrable (fun y : Submission.BoseGases.X (k + 1) => (F y) ^ 2) πc := by
    refine Integrable.mono' (integrable_const (C ^ 2)) ((hFm.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hFb y) 2
  -- the fibre Cauchy–Schwarz on the product measure
  have hcs := Work.BoseFixB1S.PiAnova.fibreCS_prod (ν := νc)
      (Ψ := fun p : E3 × Submission.BoseGases.X (k + 1) => |F (Function.update p.2 j' p.1)|)
      hGabs hsqabs
  -- evaluating the product integral: Fubini plus the one-coordinate peel
  have hval : ∫ p : E3 × Submission.BoseGases.X (k + 1),
        |F (Function.update p.2 j' p.1)| ^ 2 ∂(νc.prod πc)
      = ℓ ^ 3 * ∫ r, (F r) ^ 2 ∂πc := by
    calc ∫ p : E3 × Submission.BoseGases.X (k + 1),
          |F (Function.update p.2 j' p.1)| ^ 2 ∂(νc.prod πc)
        = ∫ p : E3 × Submission.BoseGases.X (k + 1),
            (F (Function.update p.2 j' p.1)) ^ 2 ∂(νc.prod πc) := by
          apply integral_congr_ae
          filter_upwards with p
          rw [sq_abs]
      _ = ∫ r : Submission.BoseGases.X (k + 1),
            ∫ z : E3, (F (Function.update r j' z)) ^ 2 ∂νc ∂πc :=
          integral_prod_symm (fun p : E3 × Submission.BoseGases.X (k + 1) =>
            (F (Function.update p.2 j' p.1)) ^ 2) hsq
      _ = (νc Set.univ).toReal * ∫ r, (F r) ^ 2 ∂πc :=
          Work.BoseFixB1S.pi_peel νc j'
            (G := fun y : Submission.BoseGases.X (k + 1) => (F y) ^ 2) hGsq
      _ = ℓ ^ 3 * ∫ r, (F r) ^ 2 ∂πc := by rw [hνto]
  calc (∫ r in Submission.BoseGases.abox (k + 1) ℓ,
        (∫ u in Submission.BoseGases.acube ℓ, |F (Function.update r j' u)|) ^ 2)
      = ∫ r, (∫ u in Submission.BoseGases.acube ℓ, |F (Function.update r j' u)|) ^ 2 ∂πc := by
        rw [hMc]
    _ ≤ (νc Set.univ).toReal * ∫ p, |F (Function.update p.2 j' p.1)| ^ 2 ∂(νc.prod πc) := hcs
    _ = (νc Set.univ).toReal * (ℓ ^ 3 * ∫ r, (F r) ^ 2 ∂πc) := by rw [hval]
    _ = ℓ ^ 3 * (ℓ ^ 3 * ∫ r, (F r) ^ 2 ∂πc) := by rw [hνto]
    _ = ℓ ^ 3 * (ℓ ^ 3 * ∫ r in Submission.BoseGases.abox (k + 1) ℓ, (F r) ^ 2) := by
        rw [← hMc]

end Work.BoseBoxFock.PCFU
