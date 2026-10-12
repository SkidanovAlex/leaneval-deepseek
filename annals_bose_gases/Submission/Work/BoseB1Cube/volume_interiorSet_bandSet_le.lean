import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Geom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `u`-volumes of the sliding interior and of the bad band

`Work.BoseB1Cube.volume_interiorSet_bandSet_le`: both `u`-sets of the sliding
localisation,

    interiorSet ℓ d μ = {u : ‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − 2μ^{-1/3}}  (the m = 1 region),
    bandSet ℓ d μ     = {u : ∃j, ½ℓ(1+d) − 2μ^{-1/3} ≤ |((ℓd)•u)_j| ≤ ½ℓ(1+d)},

satisfy `|·| ≤ ((1+d)/d)³`.  The point is that *both* are contained in the
coordinate cube

    K := acube ((1+d)/d) = {u : ∀j, |u_j| ≤ (1+d)/(2d)},

which is exactly `{u : ∀j, |((ℓd)•u)_j| ≤ ½ℓ(1+d)}`; and the `u`-volume of `K`
is `((1+d)/d)³` (`BoseGases.acube_volume`).  Indeed, for `u ∈ K` we have
`|((ℓd)•u)_j| = ℓd·|u_j| ≤ ℓ(1+d)/2`, so in particular `u` is in the outer cube
`{∀j, |((ℓd)•u)_j| ≤ ½ℓ(1+d)}` — which contains `bandSet` by definition, and
contains `interiorSet` because the inner half-side
`½ℓ(1+d) − 2μ^{-1/3}` is at most the outer one.

The bound is deliberately loose in two ways (it uses neither `d ≤ 1` nor the
positivity of the inner half-side `½ℓ(1+d) − 2μ^{-1/3}`); this is exactly the
`((1+d)/d)³`-error term of FS `eq:appsliding`.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory

namespace Work.BoseB1Cube

open Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **A scalar bound on one coordinate of `u` from one of `(ℓd)•u`**: for
`ℓ, d > 0`, `|((ℓd)•u)_j| ≤ C` gives `|u_j| ≤ C/(ℓd)`. -/
private lemma abs_coord_le_of_smul_le {ℓ d C : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³}
    {j : Fin 3} (h : |((ℓ * d) • u).ofLp j| ≤ C) : |u.ofLp j| ≤ C / (ℓ * d) := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have h1 := h
  rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hℓd] at h1
  exact (le_div_iff₀ hℓd).2 (by linarith [h1])

/-- The cube `acube L` alone recognizes membership through the coordinate
bounds `|u_j| ≤ L/2`. -/
private lemma mem_acube_of_coord_le {L : ℝ} {u : ℝ³} (h : ∀ j : Fin 3, |u.ofLp j| ≤ L / 2) :
    u ∈ Submission.BoseGases.acube L := by
  rw [Submission.BoseGases.mem_acube_iff]
  intro j
  have h2 := abs_le.mp (h j)
  rw [Set.mem_Icc]
  constructor <;> linarith [h2.1, h2.2]

/-- The outer half-side `½ℓ(1+d)` in `(ℓd)•u` coordinates corresponds to the
half-side `((1+d)/d)/2` in `u` coordinates. -/
private lemma halfSide_div {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ((1 / 2) * ℓ * (1 + d)) / (ℓ * d) = ((1 + d) / d) / 2 := by
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  have hd' : d ≠ 0 := ne_of_gt hd
  field_simp

theorem volume_interiorSet_bandSet_le {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet ℓ d μ)).toReal ≤ ((1 + d) / d) ^ 3
      ∧ (MeasureTheory.volume (Work.SmallBoxSliding.bandSet ℓ d μ)).toReal ≤ ((1 + d) / d) ^ 3 := by
  have hA : (0 : ℝ) < (1 + d) / d := by positivity
  have hvol : volume (Submission.BoseGases.acube ((1 + d) / d))
      = ENNReal.ofReal (((1 + d) / d) ^ 3) :=
    Submission.BoseGases.acube_volume _ hA.le
  -- the `interiorSet` is contained in the outer cube
  have hsubI : interiorSet ℓ d μ ⊆ Submission.BoseGases.acube ((1 + d) / d) := by
    intro u hu
    rw [mem_interiorSet_iff] at hu
    refine mem_acube_of_coord_le (fun j => ?_)
    have hδ : 0 ≤ 2 * μ ^ (-(1 / 3) : ℝ) :=
      (mul_pos two_pos (Real.rpow_pos_of_pos hμ _)).le
    have hb : |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) := by linarith [hu j, hδ]
    have h2 := abs_coord_le_of_smul_le hℓ hd0 hb
    rwa [halfSide_div hℓ hd0] at h2
  -- and so is the bad band (its second defining conjunct is that cube)
  have hsubB : bandSet ℓ d μ ⊆ Submission.BoseGases.acube ((1 + d) / d) := by
    intro u hu
    rw [mem_bandSet_iff] at hu
    refine mem_acube_of_coord_le (fun j => ?_)
    have h2 := abs_coord_le_of_smul_le hℓ hd0 (hu.2 j)
    rwa [halfSide_div hℓ hd0] at h2
  have hmain : ∀ {S : Set ℝ³}, S ⊆ Submission.BoseGases.acube ((1 + d) / d) →
      (volume S).toReal ≤ ((1 + d) / d) ^ 3 := by
    intro S hS
    calc (volume S).toReal
        ≤ (volume (Submission.BoseGases.acube ((1 + d) / d))).toReal :=
          ENNReal.toReal_mono (by rw [hvol]; exact ENNReal.ofReal_ne_top) (measure_mono hS)
      _ = ((1 + d) / d) ^ 3 := by rw [hvol, ENNReal.toReal_ofReal (by positivity)]
  exact ⟨hmain hsubI, hmain hsubB⟩

end Work.BoseB1Cube
