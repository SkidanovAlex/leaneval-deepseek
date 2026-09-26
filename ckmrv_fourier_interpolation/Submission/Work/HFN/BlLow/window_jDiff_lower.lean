import Mathlib
import Submission.Work.HFN.BlLow.WinDefs
import Submission.Work.Asymptotics.Tile.tile_jDiff_linear_compact
import Submission.Work.HFN.BlLow.jprime_ne_zero_blWinBox
import Submission.Work.HFN.BlLow.blWinBox_far_lower

/-!
# The two-branch lower bound for the `j`-difference on the low bad-line window

This file proves `Work.Asymptotics.BlLow.window_jDiff_lower`: on the low bad-line region
`blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}` and inside the spike window
`|t - Im τ| ≤ 1/8`, the difference of the `j`-invariant at the contour point `i t` and at the
translate pole `zpole τ = τ - tsign τ` dominates the product of the distances to the two points
of the `SL(2,ℤ)`-orbit of `τ` that the contour can meet, `zpole τ` and
`crossedPt τ = tsign τ + S·τ`:

`c ‖i t - zpole τ‖ ‖i t - crossedPt τ‖ ≤ ‖j (i t) - j (zpole τ)‖`.

This is the low-height companion of `Work.Asymptotics.HalfFunnel.jBranch_lower` (the analogue of
which is *false* here, cf. the discussion in `Work.Asymptotics.BlLow.window_bound`): the second
branch is the *crossed* orbit point `crossedPt τ`, not the `S`-translate of the pole.

## Proof

Both `zpole τ` and `crossedPt τ` lie in the closed box
`blWinBox = {|Re| ≤ 1/4, 1/3 ≤ Im ≤ 2/3}` (`zpole_mem_blWinBox`, `crossedPt_mem_blWinBox`), on
which `j'` does not vanish (`Work.Asymptotics.BlLow.jprime_ne_zero_blWinBox`), so
`Work.Asymptotics.Tile.tile_jDiff_linear_compact` gives a uniform local lower bound
`c₀ ‖z - ρ‖ ≤ ‖j z - j ρ‖` for `ρ ∈ blWinBox`, `‖z - ρ‖ ≤ δ₀`.  Since
`j (crossedPt τ) = j (zpole τ)`, it suffices to be close to *either* orbit point:

* if `‖i t - zpole τ‖ ≤ δ₀` (resp. `‖i t - crossedPt τ‖ ≤ δ₀`) use the local bound at
  `zpole τ` (resp. at `crossedPt τ`) and `‖i t - crossedPt τ‖ ≤ 1` (resp.
  `‖i t - zpole τ‖ ≤ 1`), which holds because both points of
  `blWinBox` are at distance at most `1` from the window `ctWin` (`dist_le_one`);

* otherwise both distances exceed `δ₀`, and the two-branch *far* bound
  `Work.Asymptotics.BlLow.blWinBox_far_lower` (a compactness statement whose content is the
  coincidence classification `Work.Asymptotics.BlLow.coincidence_classification`) bounds
  `‖j (i t) - j (zpole τ)‖` from below by a positive constant, while the product of the
  distances is at most `1`.
-/

noncomputable section

open UpperHalfPlane

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel

/-- **The local lower bound on the orbit-point box.**  `j` expands distances uniformly on
`blWinBox`, where `j'` does not vanish. -/
theorem blWinBox_local_lower :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ ρ ∈ blWinBox, ∀ z : ℍ,
      ‖(z : ℂ) - (ρ : ℂ)‖ ≤ δ →
        c * ‖(z : ℂ) - (ρ : ℂ)‖ ≤
          ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun ρ‖ :=
  Work.Asymptotics.Tile.tile_jDiff_linear_compact isCompact_blWinBox
    (fun ρ hρ => jprime_ne_zero_blWinBox hρ)

theorem window_jDiff_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      blLowSet τ → |t - τ.im| ≤ 1 / 8 →
      c * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            - (((Work.Asymptotics.HalfFunnel.zpole τ) : ℍ) : ℂ)‖
        * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            - ((crossedPt τ : ℍ) : ℂ)‖
        ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
            - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)‖ := by
  obtain ⟨c0, δ0, hc0, hδ0, hloc⟩ := blWinBox_local_lower
  obtain ⟨δ, hδpos, hfar⟩ := blWinBox_far_lower δ0 hδ0
  refine ⟨min c0 δ, lt_min hc0 hδpos, ?_⟩
  intro τ t ht hτ hw
  set z0 : ℍ := Work.Asymptotics.HalfFunnel.zpole τ with hz0def
  set z1 : ℍ := crossedPt τ with hz1def
  set out : ℍ := Work.Kernels.imagAxis t ht with houtdef
  have hτbox : τ ∈ clBox := blLowSet_subset_clBox hτ
  have hwin := blLow_window_bounds hτ ht hw
  have hz0 : z0 ∈ blWinBox := zpole_mem_blWinBox hτbox
  have hz1 : z1 ∈ blWinBox := crossedPt_mem_blWinBox hτbox
  have hout : out ∈ ctWin := imagAxis_mem_ctWin t ht hwin.1 hwin.2
  have hd0 : ‖(out : ℂ) - (z0 : ℂ)‖ ≤ 1 := dist_le_one hz0 hout
  have hd1 : ‖(out : ℂ) - (z1 : ℂ)‖ ≤ 1 := dist_le_one hz1 hout
  have hj1 : Work.Kernels.jInvariantFun z1 = Work.Kernels.jInvariantFun z0 := by
    rw [hz1def, hz0def, crossedPt_jInvariantFun, zpole_jInvariantFun]
  have hminc : min c0 δ ≤ c0 := min_le_left _ _
  have hminδ : min c0 δ ≤ δ := min_le_right _ _
  have hm0 : 0 ≤ min c0 δ := le_of_lt (lt_min hc0 hδpos)
  have hgoal : min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ * ‖(out : ℂ) - (z1 : ℂ)‖
      ≤ ‖Work.Kernels.jInvariantFun out - Work.Kernels.jInvariantFun z0‖ := by
    rcases le_or_gt ‖(out : ℂ) - (z0 : ℂ)‖ δ0 with hcase | hcase
    · have hloc0 := hloc z0 hz0 out hcase
      have hA : min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ * ‖(out : ℂ) - (z1 : ℂ)‖
          ≤ min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ := by
        calc min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ * ‖(out : ℂ) - (z1 : ℂ)‖
            ≤ min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ * 1 :=
              mul_le_mul_of_nonneg_left hd1 (mul_nonneg hm0 (norm_nonneg _))
          _ = min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ := by ring
      have hB : min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ ≤ c0 * ‖(out : ℂ) - (z0 : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hminc (norm_nonneg _)
      linarith
    · rcases le_or_gt ‖(out : ℂ) - (z1 : ℂ)‖ δ0 with hcase1 | hcase1
      · have hloc1 := hloc z1 hz1 out hcase1
        rw [hj1] at hloc1
        have h1 : min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ ≤ min c0 δ * 1 :=
          mul_le_mul_of_nonneg_left hd0 hm0
        have hA : min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ * ‖(out : ℂ) - (z1 : ℂ)‖
            ≤ min c0 δ * ‖(out : ℂ) - (z1 : ℂ)‖ := by
          calc min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ * ‖(out : ℂ) - (z1 : ℂ)‖
              ≤ (min c0 δ * 1) * ‖(out : ℂ) - (z1 : ℂ)‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ = min c0 δ * ‖(out : ℂ) - (z1 : ℂ)‖ := by ring
        have hB : min c0 δ * ‖(out : ℂ) - (z1 : ℂ)‖ ≤ c0 * ‖(out : ℂ) - (z1 : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hminc (norm_nonneg _)
        linarith
      · have hfar' := hfar τ t ht hτbox hwin.1 hwin.2 (le_of_lt hcase) (le_of_lt hcase1)
        have hfar'' : δ ≤ ‖Work.Kernels.jInvariantFun out - Work.Kernels.jInvariantFun z0‖ := by
          simpa [hz0def, houtdef] using hfar'
        have h1 : min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ ≤ min c0 δ * 1 :=
          mul_le_mul_of_nonneg_left hd0 hm0
        have h2 : min c0 δ * ‖(out : ℂ) - (z0 : ℂ)‖ * ‖(out : ℂ) - (z1 : ℂ)‖
            ≤ (min c0 δ * 1) * 1 :=
          mul_le_mul h1 hd1 (norm_nonneg _) (mul_nonneg hm0 (by norm_num))
        have hB : (min c0 δ * 1) * 1 ≤ δ := by rw [mul_one, mul_one]; exact hminδ
        linarith
  have hz0coe : ((z0 : ℍ) : ℂ) = ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ) := by rw [hz0def]
  have hz1coe : ((z1 : ℍ) : ℂ) = ((crossedPt τ : ℍ) : ℂ) := by rw [hz1def]
  have houtcoe : out = Work.Kernels.imagAxis t ht := houtdef
  simpa [hz0coe, hz1coe, hz0def, houtcoe] using hgoal

end Work.HFN.BlLow
