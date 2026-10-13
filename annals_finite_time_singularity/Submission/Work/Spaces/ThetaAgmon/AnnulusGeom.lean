/-
Copyright: work module for the Elgindi finite-time singularity project.

# Angular dyadic annuli: the geometry of `sin(2θ)` at a fixed scale

This is the first piece of the "two-scale angular chapter" needed for the crux term
`Work.FTS.H2.EasyU_crux_term` (see `Submission/Work/FTS/H2/NOTES_EasyU_crux_term.md`).

The angular variable `θ ∈ Iθ = [0,π/2]` is decomposed into dyadic annuli
`annulus a = [a,2a]` near the two endpoints, together with a central piece.  On a single
annulus, `sin(2θ)` is *comparable to the scale* `a` (Lemma `sin_two_annulus_equiv`), which
is what makes the angular weights `sin(2θ)^{-η}` and `sin(2θ)^{-γ}` constant at the scale.

Consequently the target integrand of `EasyU_crux_term`,

  `(D_z^4 g)^2 · (D_θ f)^2 · w^2 · sin(2θ)^{-γ}`,   `D_θ f = sin(2θ)·∂_θ f`,

is, on a single annulus `[a,2a]`, dominated by a *constant* multiple of
`(D_z^4 g)^2 w^2 (∂_θ f)^2 · a^{2-γ}` (the exact vanishing `D_θ f = sin(2θ)·∂_θ f` supplies the
two powers of `sin` that make the exponent `2 - γ ≥ 0`), so that the angular weight is
replaced by the *measure* of the annulus at that scale.  This is the mechanism exploited by
the local Hardy inequality `hardy_localized_theta` (delegated) and the
interval Agmon bound (delegated).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces.ThetaAgmon

set_option autoImplicit false

/-- The angular dyadic annulus at scale `a`: the interval `[a, 2a]`.

For `2a ≤ π/2` the annulus is contained in `Iθ = [0,π/2]` (`annulus_subset_Iθ`), and for
`4a ≤ π/2` the function `sin(2θ)` is comparable to `a` on it (`sin_two_annulus_equiv`).
The dyadic decomposition of the angular variable consists of the annuli
`annulus (2^{-(k+1)})` for `k ≥ 0` and the central piece `[1/4, π/2]` (near the upper
endpoint one uses the reflected annuli `π/2 - annulus a`). -/
def annulus (a : ℝ) : Set ℝ := Set.Icc a (2 * a)

theorem annulus_measurableSet (a : ℝ) : MeasurableSet (annulus a) :=
  measurableSet_Icc

theorem annulus_subset_Iθ {a : ℝ} (ha : 0 < a) (ha2 : 2 * a ≤ Real.pi / 2) :
    annulus a ⊆ Work.Spaces.Iθ := by
  intro θ hθ
  simp only [annulus, Set.mem_Icc] at hθ
  exact ⟨le_trans ha.le hθ.1, le_trans hθ.2 ha2⟩

theorem annulus_nonempty {a : ℝ} (ha : 0 < a) : (annulus a).Nonempty :=
  ⟨a, le_refl a, by linarith⟩

/-- **`sin(2θ)` is comparable to the annulus scale.**

For `0 < a` with `4a ≤ π/2` and `θ ∈ [a,2a]` one has `(4/π)·a ≤ sin(2θ) ≤ 4·a`.

The lower bound is the standard `sin x ≥ (2/π)x` on `[0,π/2]` (`Real.mul_le_sin`) and the
upper bound is `sin x ≤ x` (`Real.sin_le`); both are evaluated at `x = 2θ ∈ [2a, 4a]`. -/
theorem sin_two_annulus_equiv {a θ : ℝ} (ha : 0 < a) (ha8 : 4 * a ≤ Real.pi / 2)
    (hθ : θ ∈ annulus a) :
    (4 / Real.pi) * a ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 4 * a := by
  simp only [annulus, Set.mem_Icc] at hθ
  have ha0 : 0 ≤ a := ha.le
  have h2θ0 : 0 ≤ 2 * θ := by linarith [hθ.1, ha0]
  have h2θπ : 2 * θ ≤ Real.pi / 2 := by linarith [hθ.2]
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · have h1 : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) := Real.mul_le_sin h2θ0 h2θπ
    have h2 : (4 / Real.pi) * a ≤ 2 / Real.pi * (2 * θ) := by
      have : (4 / Real.pi) * a = 2 / Real.pi * (2 * a) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith [hθ.1]) (by positivity)
    linarith
  · have h1 : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le h2θ0
    linarith [hθ.2]

/-- **Weight bound on an annulus, nonnegative exponent.**

For `0 < a`, `4a ≤ π/2`, `t ≥ 0` and `θ ∈ [a,2a]`: `sin(2θ)^t ≤ (4a)^t`. -/
theorem rpow_sin_le_annulus_of_nonneg {a θ t : ℝ} (ha : 0 < a)
    (ha8 : 4 * a ≤ Real.pi / 2) (ht : 0 ≤ t) (hθ : θ ∈ annulus a) :
    (Real.sin (2 * θ)) ^ t ≤ (4 * a) ^ t := by
  obtain ⟨-, hub⟩ := sin_two_annulus_equiv ha ha8 hθ
  simp only [annulus, Set.mem_Icc] at hθ
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1, ha.le], by linarith [hθ.2]⟩
  exact Real.rpow_le_rpow hsin0 hub ht

/-- **Weight bound on an annulus, nonpositive exponent.**

For `0 < a`, `4a ≤ π/2`, `t ≤ 0` and `θ ∈ [a,2a]`: `sin(2θ)^t ≤ ((4/π)·a)^t`. -/
theorem rpow_sin_le_annulus_of_nonpos {a θ t : ℝ} (ha : 0 < a)
    (ha8 : 4 * a ≤ Real.pi / 2) (ht : t ≤ 0) (hθ : θ ∈ annulus a) :
    (Real.sin (2 * θ)) ^ t ≤ ((4 / Real.pi) * a) ^ t := by
  obtain ⟨hlb, -⟩ := sin_two_annulus_equiv ha ha8 hθ
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hlb ht

/-- The target weight on an annulus: for `1 ≤ γ` and `θ ∈ [a,2a]` with `4a ≤ π/2`,
`sin(2θ)^{-γ} ≤ ((4/π)·a)^{-γ} = (π/(4a))^γ`. -/
theorem rpow_sin_neg_le_annulus {a θ γ : ℝ} (ha : 0 < a) (ha8 : 4 * a ≤ Real.pi / 2)
    (hγ : 0 ≤ γ) (hθ : θ ∈ annulus a) :
    (Real.sin (2 * θ)) ^ (-γ) ≤ ((4 / Real.pi) * a) ^ (-γ) :=
  rpow_sin_le_annulus_of_nonpos ha ha8 (by linarith) hθ

/-- The `2 - γ` weight on an annulus: for `γ ≤ 2` and `θ ∈ [a,2a]` with `4a ≤ π/2`,
`sin(2θ)^{2-γ} ≤ (4a)^{2-γ}`.

This is the weight produced by the exact vanishing `D_θ f = sin(2θ)·∂_θ f`; on an annulus it
is a *constant* `(4a)^{2-γ}`, i.e. the angular weight is traded for the annulus scale. -/
theorem rpow_sin_two_sub_le_annulus {a θ γ : ℝ} (ha : 0 < a)
    (ha8 : 4 * a ≤ Real.pi / 2) (hγ : γ ≤ 2) (hθ : θ ∈ annulus a) :
    (Real.sin (2 * θ)) ^ (2 - γ) ≤ (4 * a) ^ (2 - γ) :=
  rpow_sin_le_annulus_of_nonneg ha ha8 (by linarith) hθ

end Work.Spaces.ThetaAgmon
