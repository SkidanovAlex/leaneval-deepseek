import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB1B.chiCubeBump
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.chiCubeB_hasCompactSupport`

The smooth cube bump `chiCubeB M ℓ d u` (`chiCubeBump.lean`) has compact support for `0 < ℓ`.

`chiCubeB M ℓ d u` is the product of the two scaled bumps `chiCubeScale ℓ` and
`chiCubeScale (ℓ*d)`, but only the **first** factor is needed here, and no hypothesis on `d` is
required: `chiCubeScale ℓ z ≠ 0` already forces every coordinate of `z` to satisfy
`|z_j| < ℓ / 2`, so

    Function.support (chiCubeB M ℓ d u) ⊆ {z | ∀ j, |z.ofLp j| ≤ ℓ / 2},

a closed coordinate box.  That box is shown compact by pushing it through the homeomorphism
`PiLp.homeomorph 2`, where it becomes the product of intervals
`Set.univ.pi (Set.Icc (-r) r)`, compact by `isCompact_univ_pi`.

(`ℓ > 0` is sharp: at `ℓ = 0` the scaling `chiCubeScale 0` is identically `1`, so `chiCubeB`
would be the constant function `1` with non-compact support.)

Helper lemmas, reusable elsewhere:

* `isCompact_ofLp_abs_le` — a closed coordinate box in `EuclideanSpace ℝ (Fin 3)` is compact;
* `chiCubeBase_ofLp_abs_lt_half` — `chiCubeBase` vanishes once one coordinate reaches `1/2`;
* `chiCubeB_support_subset_ofLp_abs_le` — the support inclusion above.
-/

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **A closed coordinate box in `ℝ³` is compact.**  The set `{z | ∀ j, |z_j| ≤ r}` is the
preimage, under the homeomorphism `PiLp.homeomorph 2`, of the product of intervals
`[-r, r]`, which is compact by `isCompact_univ_pi`.  No sign hypothesis on `r` is needed (for
`r < 0` both sides are empty). -/
lemma isCompact_ofLp_abs_le (r : ℝ) :
    IsCompact {z : E3 | ∀ j : Fin 3, |z.ofLp j| ≤ r} := by
  have hS : IsCompact (Set.univ.pi fun _ : Fin 3 => Set.Icc (-r) r) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hK : {z : E3 | ∀ j : Fin 3, |z.ofLp j| ≤ r}
      = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
          (Set.univ.pi fun _ : Fin 3 => Set.Icc (-r) r) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hz j
      exact abs_le.mp (hz j)
    · intro hz j
      exact abs_le.mpr (hz j)
  rw [hK]
  exact (Homeomorph.isCompact_preimage _).mpr hS

/-- **Coordinatewise vanishing of the cube bump**, the complement of the plateau statement
`chiCubeBase_eq_one_of_abs_le`: if some coordinate of `z` has modulus at least `1/2`, then
`chiCubeBase z = 0`. -/
lemma chiCubeBase_ofLp_abs_lt_half {z : E3} (hz : chiCubeBase z ≠ 0) (j : Fin 3) :
    |z.ofLp j| < 1 / 2 := by
  by_contra hc
  rw [not_lt] at hc
  refine hz ?_
  fin_cases j
  · exact chiCubeBase_eq_zero_of_half_le z (Or.inl hc)
  · exact chiCubeBase_eq_zero_of_half_le z (Or.inr (Or.inl hc))
  · exact chiCubeBase_eq_zero_of_half_le z (Or.inr (Or.inr hc))

/-- **The support of the cube window is a coordinate box.**  Only the first factor
`chiCubeScale ℓ = chiCubeBase (ℓ⁻¹ • ·)` of `chiCubeB M ℓ d u` is used; consequently no
hypothesis on `d` is needed (`d ≤ 0` would make the *second* factor the constant `1`). -/
lemma chiCubeB_support_subset_ofLp_abs_le {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    Function.support (chiCubeB M ℓ d u) ⊆ {z : E3 | ∀ j : Fin 3, |z.ofLp j| ≤ ℓ / 2} := by
  intro z hz j
  have hz1 : chiCubeScale ℓ z ≠ 0 := fun h => hz (by rw [chiCubeB, h, zero_mul])
  have hz2 : chiCubeBase ((ℓ⁻¹ : ℝ) • z) ≠ 0 := hz1
  have hj := chiCubeBase_ofLp_abs_lt_half hz2 j
  have hsm : ((ℓ⁻¹ : ℝ) • z).ofLp j = ℓ⁻¹ * z.ofLp j := by simp
  rw [hsm, abs_mul, abs_of_pos (inv_pos.mpr hℓ)] at hj
  have hmul := mul_lt_mul_of_pos_left hj hℓ
  have hsplit : ℓ * ((ℓ⁻¹ : ℝ) * |z.ofLp j|) = |z.ofLp j| := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ), one_mul]
  have hhalf : ℓ * (1 / 2) = ℓ / 2 := by ring
  rw [hsplit, hhalf] at hmul
  exact le_of_lt hmul

/-- **The smooth cube window `chiCubeB M ℓ d u` has compact support for `0 < ℓ`** — the
requirement that the `chiCubeBump` repair kit be usable wherever `chiSmallB` was (an
integrable / `L²` window, an autocorrelation supported in a compact box, …). -/
theorem chiCubeB_hasCompactSupport {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    HasCompactSupport (Work.BoseFixB1B.chiCubeB M ℓ d u) := by
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_ofLp_abs_le (ℓ / 2))
    (chiCubeB_support_subset_ofLp_abs_le hℓ u)

end Work.BoseFixB1B
