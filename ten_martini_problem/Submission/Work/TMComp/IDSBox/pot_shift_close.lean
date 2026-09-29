import Mathlib
import Submission.Work.TMComp.IDSDefs

/-!
# C6 (`P_IDSSpectrum`), box counting: the potential is close under a phase shift

`Work.TMComp.IDSBox.pot_shift_close` compares the two potentials

* `amoPot α lam θ k = 2λ cos 2π(θ + kα)`  (potential at site `k`, phase `θ`), and
* `amoPot α lam 0 (k - j) = 2λ cos 2π((k - j)α)`  (potential at site `k - j`, phase `0`),

under the hypothesis that `θ + jα` is within `δ` of an integer, i.e.
`fracDist (θ + jα) < δ`.

Both cosines are of angles whose *difference* is `2π(θ + jα)`.  Since `cos` is `2π`-periodic
and `1`-Lipschitz on the circle, shifting the argument by `2π` times the nearest integer to
`θ + jα` moves the angle by at most `2π δ`; hence the two potentials differ by at most
`2|λ| · 2π δ = 4π|λ| δ`.

This is the estimate that lets the eigenvalues of the `n`-site Dirichlet box at phase `θ`
be compared with those of the box at phase `0` (after the site shift `k ↦ k - j`), which is
the input to the `δ`-counting of `shiftCount`.
-/

noncomputable section

-- `hδ : 0 ≤ δ` is part of the interface, but the estimate itself does not need it.
set_option linter.unusedVariables false

namespace Work.TMComp.IDSBox

open Work.TMContract

/-- **Reduction of a phase shift to the circle.** If `θ + mα` is within `δ` of an integer,
then the cosines of the two angles `2π(θ + nα)` and `2π((n - m)α)` differ by at most
`2π δ`.  (The intermediate integer part of `θ + mα` is absorbed by the `2π`-periodicity
of `cos`.) -/
lemma cos_shift_close (α θ δ : ℝ) (m n : ℤ)
    (hphase : fracDist (θ + (m : ℝ) * α) < δ) :
    |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
        - Real.cos (2 * Real.pi * (((n : ℝ) - (m : ℝ)) * α))| ≤ 2 * Real.pi * δ := by
  -- `R` is the nearest integer to `θ + mα`, and `r` the (small) remainder.
  set R : ℤ := round (θ + (m : ℝ) * α) with hR
  set r : ℝ := θ + (m : ℝ) * α - R with hr
  have hrbound : |r| ≤ δ := by
    have h1 : |r| = fracDist (θ + (m : ℝ) * α) := rfl
    rw [h1]
    exact le_of_lt hphase
  -- Absorb `2π R` into the periodicity of `cos`.
  have hper : Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
      = Real.cos (2 * Real.pi * (((n : ℝ) - (m : ℝ)) * α) + 2 * Real.pi * r) := by
    have harg : (2 : ℝ) * Real.pi * (θ + (n : ℝ) * α)
        = (2 * Real.pi * (((n : ℝ) - (m : ℝ)) * α) + 2 * Real.pi * r)
          + (R : ℝ) * (2 * Real.pi) := by
      rw [hr]
      ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  rw [hper]
  -- The remaining displacement `2π r` has modulus `≤ 2π δ`, and `cos` is `1`-Lipschitz.
  refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
  rw [add_sub_cancel_left, abs_mul]
  have hpi : |(2 : ℝ) * Real.pi| = 2 * Real.pi := by
    rw [abs_of_pos]; positivity
  rw [hpi]
  calc (2 * Real.pi) * |r| ≤ (2 * Real.pi) * δ :=
        mul_le_mul_of_nonneg_left hrbound (by positivity)
    _ = 2 * Real.pi * δ := by ring

theorem pot_shift_close (α lam θ δ : ℝ) (hδ : 0 ≤ δ) (j : ℤ) (k : ℕ)
    (hphase : Work.TMContract.fracDist (θ + (j : ℝ) * α) < δ) :
    |Work.TMContract.amoPot α lam θ (k : ℤ) - Work.TMContract.amoPot α lam 0 ((k : ℤ) - j)|
      ≤ 4 * Real.pi * |lam| * δ := by
  have hkey := cos_shift_close α θ δ j ((k : ℤ)) hphase
  -- Peel off the common factor `2λ` from both potentials.
  have hmain : |amoPot α lam θ (k : ℤ) - amoPot α lam 0 ((k : ℤ) - j)|
      = 2 * |lam| * |Real.cos (2 * Real.pi * (θ + (((k : ℤ)) : ℝ) * α))
          - Real.cos (2 * Real.pi * (((((k : ℤ)) : ℝ) - (j : ℝ)) * α))| := by
    simp only [amoPot, Int.cast_sub]
    rw [show (2 * lam * Real.cos (2 * Real.pi * (θ + (((k : ℤ)) : ℝ) * α))
            - 2 * lam * Real.cos (2 * Real.pi * (0 + ((((k : ℤ)) : ℝ) - (j : ℝ)) * α)))
          = 2 * lam * (Real.cos (2 * Real.pi * (θ + (((k : ℤ)) : ℝ) * α))
            - Real.cos (2 * Real.pi * (((((k : ℤ)) : ℝ) - (j : ℝ)) * α))) by ring_nf]
    rw [abs_mul]
    have h2 : |(2 : ℝ) * lam| = 2 * |lam| := by rw [abs_mul]; norm_num
    rw [h2]
  calc |amoPot α lam θ (k : ℤ) - amoPot α lam 0 ((k : ℤ) - j)|
      = 2 * |lam| * |Real.cos (2 * Real.pi * (θ + (((k : ℤ)) : ℝ) * α))
          - Real.cos (2 * Real.pi * (((((k : ℤ)) : ℝ) - (j : ℝ)) * α))| := hmain
    _ ≤ 2 * |lam| * (2 * Real.pi * δ) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 * Real.pi * |lam| * δ := by ring

end Work.TMComp.IDSBox
