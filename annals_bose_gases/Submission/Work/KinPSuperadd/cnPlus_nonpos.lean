import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `cnPlus_nonpos` — the excited-particle count vanishes on a non-positive box

`cnPlus ℓ N Φ = Σ_i ∫_{abox N ℓ} (QᵢΦ)²` is the excited-particle count on the
centred box `abox N ℓ = (acube ℓ)^N`, `acube ℓ = [−ℓ/2, ℓ/2]³`.

For `ℓ ≤ 0` the box is trivial — `acube ℓ ⊆ acube 0 = {0}` — and `abox N 0`
is a null set as soon as `N ≥ 1` (`volume (abox N 0) = (0³)^N = 0`), while for
`N = 0` the count is an empty sum.  Hence every summand `∫_{abox N ℓ} (QᵢΦ)²`
vanishes, and so does the count.  No regularity of `Φ` is needed: the integral
is over a null set (or an empty sum).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Work.KinPSuperadd

open Submission BoseGases

set_option autoImplicit false

theorem cnPlus_nonpos {s : ℝ} (hs : s ≤ 0) {N : ℕ}
    (Φ : Submission.BoseGases.X N → ℝ) :
    @Submission.BoseGases.cnPlus s N Φ = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- `N = 0`: the count is an empty sum.
    subst hN
    simp [Submission.BoseGases.cnPlus]
  · -- `N ≥ 1`: `abox N s ⊆ abox N 0` and the latter is null.
    unfold Submission.BoseGases.cnPlus
    have h0 : (volume : Measure (Submission.BoseGases.X N))
        (Submission.BoseGases.abox N 0) = 0 := by
      rw [Submission.BoseGases.abox_volume N 0 le_rfl,
        show ((0 : ℝ) ^ 3) ^ N = 0 by
          rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow hN.ne']]
      exact ENNReal.ofReal_zero
    have hsub : Submission.BoseGases.abox N s ⊆ Submission.BoseGases.abox N 0 := by
      intro x hx
      simp only [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.mem_acube_iff]
        at hx ⊢
      intro i m
      have hm := hx i m
      constructor <;> linarith [hm.1, hm.2]
    have hvol : (volume : Measure (Submission.BoseGases.X N))
        (Submission.BoseGases.abox N s) = 0 :=
      measure_mono_null hsub h0
    apply Finset.sum_eq_zero
    intro i _
    exact setIntegral_measure_zero _ hvol

end Work.KinPSuperadd
