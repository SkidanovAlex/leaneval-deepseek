import Mathlib
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep8.periodization_compact_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The partial derivative commutes with the periodization

For a smooth compactly supported `c : (ι → ℝ) → ℂ` the periodization
`P z = ∑' m : ι → ℤ, c (z + m)` satisfies `∂ᵢ P = ∑' m : ι → ℤ, (∂ᵢ c) (· + m)`.

Both sides are locally finite sums.  Fix `z`; the support of `c` lies in a coordinate box
`|y j| ≤ R`, so only the lattice points `m` with `|z j + m j| ≤ R` can contribute either to
`P z` or to `∂ᵢ c (z + m)`, and these are contained in the finite box
`S = {m | m j ∈ [-N j, N j]}` with `N j = ⌊|z j| + R⌋ + 2`.  On the ball of radius `1/2` around
`z` all terms with `m ∉ S` vanish identically (their argument is at distance `> R` from the
support in some coordinate), so there the periodization is the finite sum `∑_{m ∈ S} c (· + m)`.
Differentiating that finite sum with the chain rule for translations and using `tsum_eq_sum` for
the series of derivatives (whose terms with `m ∉ S` vanish, because `c` is identically zero on a
neighbourhood of `z + m`) gives the claim.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep8

open Work.Diff.STE

theorem pd_periodization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : HasCompactSupport c) (i : ι) :
    Work.Diff.STE.pd i (fun z : ι → ℝ => ∑' m : ι → ℤ, c (z + Work.Diff.STE.iVec m))
      = fun z : ι → ℝ => ∑' m : ι → ℤ, Work.Diff.STE.pd i c (z + Work.Diff.STE.iVec m) := by
  classical
  funext z
  -- the support of `c` is contained in the box `|y j| ≤ R`
  obtain ⟨R, _hR0, hR⟩ := exists_bound_tsupport hcs
  -- the finite box of lattice points that can contribute at `z`
  set N : ι → ℤ := fun j => ⌊|z j| + R⌋ + 2 with hN
  set S : Finset (ι → ℤ) := Fintype.piFinset (fun j => Finset.Icc (-(N j)) (N j)) with hS
  -- `N` is comfortably larger than `|z j| + R`
  have hNgt : ∀ j : ι, |z j| + R + 1 < ((N j : ℤ) : ℝ) := by
    intro j
    rw [hN]
    have := Int.lt_floor_add_one (|z j| + R)
    push_cast
    linarith
  -- every lattice point whose translate meets the box of the support lies in `S`
  have hSmem : ∀ m : ι → ℤ, (∀ j, |z j + (m j : ℝ)| ≤ R) → m ∈ S := by
    intro m hm
    rw [hS, Fintype.mem_piFinset]
    intro j
    have h1 : |((m j : ℤ) : ℝ)| ≤ R + |z j| := by
      have h3 : ((m j : ℤ) : ℝ) = (z j + ((m j : ℤ) : ℝ)) - z j := by ring
      rw [h3, sub_eq_add_neg]
      calc |(z j + ((m j : ℤ) : ℝ)) + (-z j)|
          ≤ |z j + ((m j : ℤ) : ℝ)| + |-z j| := abs_add_le _ _
        _ = |z j + ((m j : ℤ) : ℝ)| + |z j| := by rw [abs_neg]
        _ ≤ R + |z j| := by linarith [hm j]
    rw [Finset.mem_Icc]
    have h3 : |(m j : ℤ)| < N j := by
      have h4 : ((|(m j : ℤ)| : ℤ) : ℝ) < ((N j : ℤ) : ℝ) := by
        rw [Int.cast_abs]
        linarith [h1, hNgt j]
      exact_mod_cast h4
    have := abs_lt.mp h3
    exact ⟨by omega, by omega⟩
  -- outside `S` some coordinate of the lattice point is far beyond the box already at `z`
  have hSnot : ∀ m : ι → ℤ, m ∉ S → ∃ j : ι, |z j| + R + 1 < |((m j : ℤ) : ℝ)| := by
    intro m hm
    have hex : ∃ j : ι, ¬ (-(N j) ≤ m j ∧ m j ≤ N j) := by
      by_contra hcon
      exact hm (by
        rw [hS, Fintype.mem_piFinset]
        intro j
        exact Finset.mem_Icc.mpr (by
          by_contra hjb
          exact hcon ⟨j, hjb⟩))
    obtain ⟨j, hj⟩ := hex
    have hj' : m j < -(N j) ∨ N j < m j := by
      by_cases h : -(N j) ≤ m j
      · exact Or.inr (not_le.mp fun h2 => hj ⟨h, h2⟩)
      · exact Or.inl (not_le.mp h)
    refine ⟨j, ?_⟩
    have h3 : N j < |m j| := by
      rcases hj' with h | h
      · exact lt_of_lt_of_le (by omega) (neg_le_abs (m j))
      · exact lt_of_lt_of_le h (le_abs_self (m j))
    have h4 : ((N j : ℤ) : ℝ) < |((m j : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast h3
    linarith [hNgt j]
  -- `c` vanishes far away from the support, uniformly on a neighbourhood of `z`
  have hc_zero : ∀ (m : ι → ℤ) (y : ι → ℝ), m ∉ S → (∀ j, |y j - z j| < 1 / 2) →
      c (y + Work.Diff.STE.iVec m) = 0 := by
    intro m y hm hy
    obtain ⟨j, hj⟩ := hSnot m hm
    have hyj : |y j| < |z j| + 1 / 2 := by
      calc |y j| = |(y j - z j) + z j| := by ring_nf
        _ ≤ |y j - z j| + |z j| := abs_add_le _ _
        _ < 1 / 2 + |z j| := by linarith [hy j]
        _ = |z j| + 1 / 2 := by ring
    have hfar : R < |y j + ((m j : ℤ) : ℝ)| := by
      have h1 : |((m j : ℤ) : ℝ)| ≤ |y j + ((m j : ℤ) : ℝ)| + |y j| := by
        have key : y j + ((m j : ℤ) : ℝ) + -y j = ((m j : ℤ) : ℝ) := by ring
        have hab := abs_add_le (y j + ((m j : ℤ) : ℝ)) (-y j)
        rw [key, abs_neg] at hab
        exact hab
      linarith
    by_contra hcnz
    have hmem : y + Work.Diff.STE.iVec m ∈ tsupport c :=
      subset_tsupport c (Function.mem_support.mpr hcnz)
    have h5 := hR (y + Work.Diff.STE.iVec m) hmem j
    simp only [Pi.add_apply, Work.Diff.STE.iVec_apply] at h5
    linarith
  -- the partial derivative of `c` vanishes off the support of `c`
  have hpd_zero : ∀ p : ι → ℝ, p ∉ tsupport c → Work.Diff.STE.pd i c p = 0 := by
    intro p hp
    have hnhds : (tsupport c)ᶜ ∈ nhds p := (isClosed_tsupport c).isOpen_compl.mem_nhds hp
    have hev : c =ᶠ[nhds p] (fun _ : ι → ℝ => (0 : ℂ)) :=
      Filter.eventually_of_mem hnhds (fun y hy => by
        by_contra hcy
        exact hy (subset_tsupport c (Function.mem_support.mpr hcy)))
    simp only [Work.Diff.STE.pd]
    rw [hev.fderiv_eq]
    simp
  -- near `z` the periodization is the finite sum over the box `S`
  have hevF : (fun y : ι → ℝ => ∑ m ∈ S, c (y + Work.Diff.STE.iVec m)) =ᶠ[nhds z]
      (fun y : ι → ℝ => ∑' m : ι → ℤ, c (y + Work.Diff.STE.iVec m)) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 2)) ?_
    intro y hy
    refine (tsum_eq_sum (s := S) (fun m hm => ?_)).symm
    exact hc_zero m y hm (fun j => by
      have h1 : |y j - z j| ≤ ‖y - z‖ := by
        rw [← Real.norm_eq_abs (y j - z j), ← Pi.sub_apply]
        exact norm_le_pi_norm _ j
      have h2 : ‖y - z‖ < 1 / 2 := by
        have h := hy
        rw [Metric.mem_ball, dist_eq_norm] at h
        exact h
      linarith)
  -- the series of derivatives is the same finite sum: the remaining terms vanish
  have hRHS : (∑' m : ι → ℤ, Work.Diff.STE.pd i c (z + Work.Diff.STE.iVec m))
      = ∑ m ∈ S, Work.Diff.STE.pd i c (z + Work.Diff.STE.iVec m) := by
    refine tsum_eq_sum (s := S) (fun m hm => ?_)
    by_contra hcnz
    have hmem : z + Work.Diff.STE.iVec m ∈ tsupport c := by
      by_contra hnot
      exact hcnz (hpd_zero _ hnot)
    exact hm (hSmem m (fun j => by
      have h5 := hR (z + Work.Diff.STE.iVec m) hmem j
      simpa only [Pi.add_apply, Work.Diff.STE.iVec_apply] using h5))
  -- the finite sum is a sum of translates of `c`, so it differentiates termwise
  have h1 : (fun y : ι → ℝ => ∑ m ∈ S, c (y + Work.Diff.STE.iVec m))
      = (∑ m ∈ S, fun y : ι → ℝ => c (y + Work.Diff.STE.iVec m)) := by
    funext y
    exact (Finset.sum_apply y S
      (fun m : ι → ℤ => fun y : ι → ℝ => c (y + Work.Diff.STE.iVec m))).symm
  have hstep : fderiv ℝ (fun y : ι → ℝ => ∑ m ∈ S, c (y + Work.Diff.STE.iVec m)) z
      = ∑ m ∈ S, fderiv ℝ c (z + Work.Diff.STE.iVec m) := by
    rw [h1, fderiv_sum]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      exact fderiv_comp_add_right (Work.Diff.STE.iVec m)
    · intro m _
      exact (hc.differentiable (by simp)).differentiableAt.comp z
        (differentiableAt_id.add_const (Work.Diff.STE.iVec m))
  have hstepApp : fderiv ℝ (fun y : ι → ℝ => ∑ m ∈ S, c (y + Work.Diff.STE.iVec m)) z
      (Pi.single i 1) = ∑ m ∈ S, Work.Diff.STE.pd i c (z + Work.Diff.STE.iVec m) := by
    rw [hstep, sum_apply]
    rfl
  have hmain : fderiv ℝ (fun y : ι → ℝ => ∑' m : ι → ℤ, c (y + Work.Diff.STE.iVec m)) z
      (Pi.single i 1) = ∑' m : ι → ℤ, Work.Diff.STE.pd i c (z + Work.Diff.STE.iVec m) := by
    rw [← hevF.fderiv_eq, hstepApp, hRHS]
  change fderiv ℝ (fun y : ι → ℝ => ∑' m : ι → ℤ, c (y + Work.Diff.STE.iVec m)) z
      (Pi.single i 1) = ∑' m : ι → ℤ, Work.Diff.STE.pd i c (z + Work.Diff.STE.iVec m)
  exact hmain

end Work.Diff.STE.B3.SymCalcStep8
