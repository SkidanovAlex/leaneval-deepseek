/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.FQC.Petal
import Submission.Work.FQC.Flower
import Submission.Work.FatouCoordFix.All
import Submission.Work.FatouCoordFix.IntegrationCheck

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.PetalInput` — the petal input of the deformation, from the repaired flower

`Work.FQC.PetalInput d fl` is the structure the deformation of the Écalle cylinder consumes
(`Work.FQC.Height.heightShift`): a `g`-invariant open fundamental domain `Pg ⊆ fl.Pa`, the
no-early-return condition, the measurability of `Pg.indicator φa`, the Abel equation for the
second return map and the entry property.

The area `Work.FatouCoordFix` proves every one of those ingredients for **its own** repaired
flower `ParabolicFlowerFix` (`exists_parabolicFlowerFix`, `mapsTo_g_Pg`, `φa_shift`,
`toHalfPetalFlower.φa_measurable`), but no theorem built `Work.FQC.PetalInput` from it.  This
file supplies the missing glue:

* `Work.FlowerGlue.exists_separating_ball` — for every root-parabolic parameter there is `δ > 0`
  such that no point of `ball z₁ δ` is carried into `ball z₁ δ` by `(T_c)^r`, `1 ≤ r < 5`
  (continuity at `z₁` plus the exactness of the period, `d.ne_per`);
* `Work.FlowerGlue.no_early_of_ball` — hence the no-early-return condition for any `Pg ⊆ ball z₁ δ`;
* `Work.FlowerGlue.petalInput_of_fix` — the petal input of the repaired flower, from
  `Pg ⊆ ball z₁ δ` with `δ` as above;
* `Work.FlowerGlue.exists_petalInput` / `exists_petalInput_small` — the unconditional existence
  at a root-parabolic parameter (using `exists_parabolicFlowerFix_small`), with the petal and the
  half-petal as small as we like.
-/

open scoped Topology ComplexConjugate
open Filter Set Metric Function
open Classical

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FlowerGlue

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F)

noncomputable section

/-! ## 1. The separating ball at the parabolic point -/

/-- **The separating ball.**  For every root-parabolic parameter there is `δ > 0` such that
every point of `ball z₁ δ` is carried by `(T_c)^r` (`1 ≤ r < 5`) to distance at least `δ` from
`z₁`.

The proof: `(T_c)^r` is continuous at `z₁` and `(T_c)^r z₁ ≠ z₁` (`d.ne_per`), so `ball z₁ ε_r`
is mapped into the ball of radius `dist ((T_c)^r z₁) z₁ / 2` around `(T_c)^r z₁`, which is
disjoint from `ball z₁ dist ((T_c)^r z₁) z₁ / 2`; taking `δ ≤ min ε_r, dist(…)/2` gives the
claim. -/
theorem exists_separating_ball {c : ℂ} (d : RootParabolic c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → r < 5 → ∀ z : ℂ,
      dist z d.z₁ < δ → δ ≤ dist ((Tantibar c)^[r] z) d.z₁ := by
  have hsep : ∀ r : ℕ, 1 ≤ r → r < 5 → ∃ ε : ℝ, 0 < ε ∧
      ε ≤ dist ((Tantibar c)^[r] d.z₁) d.z₁ / 2 ∧
      ∀ z : ℂ, dist z d.z₁ < ε → ε ≤ dist ((Tantibar c)^[r] z) d.z₁ := by
    intro r hr1 hr5
    have hne : (Tantibar c)^[r] d.z₁ ≠ d.z₁ :=
      d.ne_per r (Finset.mem_Ioo.mpr ⟨by omega, hr5⟩)
    have hD : 0 < dist ((Tantibar c)^[r] d.z₁) d.z₁ := dist_pos.mpr hne
    have hc : ContinuousAt ((Tantibar c)^[r]) d.z₁ :=
      ((Work.FQC.continuous_of_Tantibar c).iterate r).continuousAt
    have hpre : {u : ℂ | dist ((Tantibar c)^[r] u) ((Tantibar c)^[r] d.z₁)
        < dist ((Tantibar c)^[r] d.z₁) d.z₁ / 2} ∈ 𝓝 d.z₁ :=
      hc (Metric.ball_mem_nhds _ (half_pos hD))
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨min ε (dist ((Tantibar c)^[r] d.z₁) d.z₁ / 2),
      lt_min hεpos (half_pos hD), min_le_right _ _, ?_⟩
    intro z hz
    have hz' : dist z d.z₁ < ε := lt_of_lt_of_le hz (min_le_left _ _)
    have h1 : dist ((Tantibar c)^[r] z) ((Tantibar c)^[r] d.z₁)
        < dist ((Tantibar c)^[r] d.z₁) d.z₁ / 2 := hε (by simpa [Metric.mem_ball] using hz')
    have h2 : dist ((Tantibar c)^[r] d.z₁) d.z₁
        ≤ dist ((Tantibar c)^[r] z) d.z₁ + dist ((Tantibar c)^[r] z) ((Tantibar c)^[r] d.z₁) := by
      have htri := dist_triangle_left ((Tantibar c)^[r] d.z₁) d.z₁ ((Tantibar c)^[r] z)
      linarith
    have h3 := min_le_right ε (dist ((Tantibar c)^[r] d.z₁) d.z₁ / 2)
    linarith
  obtain ⟨ε₁, h1pos, h1le, h1⟩ := hsep 1 (by norm_num) (by norm_num)
  obtain ⟨ε₂, h2pos, h2le, h2⟩ := hsep 2 (by norm_num) (by norm_num)
  obtain ⟨ε₃, h3pos, h3le, h3⟩ := hsep 3 (by norm_num) (by norm_num)
  obtain ⟨ε₄, h4pos, h4le, h4⟩ := hsep 4 (by norm_num) (by norm_num)
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄),
    lt_min (lt_min h1pos h2pos) (lt_min h3pos h4pos), ?_⟩
  intro r hr1 hr5 z hz
  have hδ1 : min (min ε₁ ε₂) (min ε₃ ε₄) ≤ ε₁ :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : min (min ε₁ ε₂) (min ε₃ ε₄) ≤ ε₂ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ3 : min (min ε₁ ε₂) (min ε₃ ε₄) ≤ ε₃ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ4 : min (min ε₁ ε₂) (min ε₃ ε₄) ≤ ε₄ :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  interval_cases r
  · exact le_trans hδ1 (h1 z (lt_of_lt_of_le hz hδ1))
  · exact le_trans hδ2 (h2 z (lt_of_lt_of_le hz hδ2))
  · exact le_trans hδ3 (h3 z (lt_of_lt_of_le hz hδ3))
  · exact le_trans hδ4 (h4 z (lt_of_lt_of_le hz hδ4))

/-- **The no-early-return condition** for a set contained in a separating ball: no `(T_c)^r`,
`1 ≤ r < 5`, maps a point of `Pg` into `Pg`. -/
theorem no_early_of_ball {c : ℂ} (d : RootParabolic c) {δ : ℝ}
    (hsep : ∀ r : ℕ, 1 ≤ r → r < 5 → ∀ z : ℂ,
      dist z d.z₁ < δ → δ ≤ dist ((Tantibar c)^[r] z) d.z₁)
    {Pg : Set ℂ} (hPg : Pg ⊆ Metric.ball d.z₁ δ) :
    ∀ z ∈ Pg, ∀ r : ℕ, 1 ≤ r → r < 5 → (Tantibar c)^[r] z ∉ Pg := by
  intro z hz r hr1 hr5 hzr
  have h1 : dist z d.z₁ < δ := by
    have := hPg hz
    rwa [Metric.mem_ball] at this
  have h2 : dist ((Tantibar c)^[r] z) d.z₁ < δ := by
    have := hPg hzr
    rwa [Metric.mem_ball] at this
  have h3 := hsep r hr1 hr5 z h1
  linarith

/-! ## 2. The petal input of the repaired flower -/

/-- **The petal input of the repaired flower** (`Work.FQC.PetalInput`) at a root-parabolic
parameter, from a size bound on the half-petal: every field is that of
`Work.FatouCoordFix.ParabolicFlowerFix`, except `no_early`, which is
`Work.FlowerGlue.no_early_of_ball` applied to `Pg ⊆ ball z₁ δ`. -/
def petalInput_of_fix {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁) {δ : ℝ}
    (hsep : ∀ r : ℕ, 1 ≤ r → r < 5 → ∀ z : ℂ,
      dist z d.z₁ < δ → δ ≤ dist ((Tantibar c)^[r] z) d.z₁)
    (hPg : fl.Pg ⊆ Metric.ball d.z₁ δ) :
    Work.FQC.PetalInput d fl.toParabolicFlower where
  Pg := fl.Pg
  Pg_sub := fl.Pg_sub
  Pg_open := fl.isOpen_Pg
  Pg_preconnected := fl.isPreconnected_Pg
  mapsTo_g_Pg := fun z hz => fl.mapsTo_g_Pg hz
  no_early := no_early_of_ball d hsep hPg
  indicator_measurable := fl.toHalfPetalFlower.φa_measurable
  φa_shift := fl.φa_shift
  enters_Pg := fl.enters_Pg

/-- **The petal input exists at every root-parabolic parameter**, with the petal and the
half-petal inside any prescribed ball around `z₁`: the separating ball of
`exists_separating_ball` and the small-flower theorem
`Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix_small` give a flower whose half-petal is
contained in the separating ball. -/
theorem exists_petalInput_small {c : ℂ} (d : RootParabolic c) {ε : ℝ} (hε : 0 < ε) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁,
      Nonempty (Work.FQC.PetalInput d fl.toParabolicFlower) ∧
        fl.Pa ⊆ Metric.ball d.z₁ ε ∧ fl.Pg ⊆ Metric.ball d.z₁ ε := by
  obtain ⟨δ, hδpos, hδsep⟩ := exists_separating_ball d
  obtain ⟨fl, hPa, hPg⟩ :=
    Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix_small (F c) ((Tantibar c)^[5]) d.z₁
      (Work.FQC.differentiable_F c) (Work.FQC.differentiableAt_star_comp_g c)
      (Work.FQC.g_comp_g c) (Work.FQC.F_fix c d) (Work.FQC.deriv_F_eq_one c d) d.simple
      d.per_half (lt_min hε hδpos)
  have hPgδ : fl.Pg ⊆ Metric.ball d.z₁ δ :=
    hPg.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hPaε : fl.Pa ⊆ Metric.ball d.z₁ ε :=
    hPa.trans (Metric.ball_subset_ball (min_le_left _ _))
  exact ⟨fl, ⟨petalInput_of_fix d fl hδsep hPgδ⟩, hPaε,
    hPg.trans (Metric.ball_subset_ball (min_le_left _ _))⟩

/-- **The petal input exists at every root-parabolic parameter** (unconditional form). -/
theorem exists_petalInput {c : ℂ} (d : RootParabolic c) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁,
      Nonempty (Work.FQC.PetalInput d fl.toParabolicFlower) := by
  obtain ⟨fl, h, -, -⟩ := exists_petalInput_small d (ε := 1) one_pos
  exact ⟨fl, h⟩

end

end Work.FlowerGlue
