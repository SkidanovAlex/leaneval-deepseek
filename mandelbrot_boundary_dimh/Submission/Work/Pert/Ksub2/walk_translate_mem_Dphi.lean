import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk_bdd

namespace Work.Pert.Ksub2

theorem walk_translate_mem_Dphi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} {ρe Tb R : ℝ} {w : ℂ} (hw : w ∈ K')
    (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hZsub : ∀ k ∈ Finset.range (⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊ + 1),
        ∀ u ∈ (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K'), u ∈ d.Dφ)
    {m : ℕ} {z : ℂ} (hz : ‖z - (w - (m : ℂ))‖ ≤ ρe) : z ∈ d.Dφ := by
  -- Two regimes for the depth `m`:
  -- * `m` below the threshold where the hypothesis `hZsub` is stated: `z` lies in the relevant
  --   translate of `cthickening ρe K'`;
  -- * `m` above it: then `Re z < -ξ₀` and `z` is a point of the sector `QLeft ξ₀ ⊆ Dφ`.
  by_cases hm : m ≤ ⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊
  · have hmem : z + (m : ℂ) ∈ Metric.cthickening ρe K' := by
      refine mem_cthickening_of_dist_le hw ?_
      rw [dist_eq_norm]
      have h : (z + (m : ℂ)) - w = z - (w - (m : ℂ)) := by ring
      rw [h]; exact hz
    have him : z ∈ (fun u : ℂ => u - (m : ℂ)) '' (Metric.cthickening ρe K') :=
      ⟨z + (m : ℂ), hmem, by ring⟩
    exact hZsub m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)) z him
  · have hmlt : (⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊ : ℝ) < (m : ℝ) := by
      have h := Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_le hm)
      have h' : ((⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊ + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    have hxlt : Tb + max R (d.ξ₀ + 1) + ρe < (m : ℝ) :=
      lt_of_le_of_lt (Nat.le_ceil _) hmlt
    have hzre : z.re < -d.ξ₀ := by
      have h1 : (z - (w - (m : ℂ))).re ≤ ρe := le_trans (Complex.re_le_norm _) hz
      have h2 : (z - (w - (m : ℂ))).re = z.re - w.re + (m : ℝ) := by
        simp only [Complex.sub_re, Complex.natCast_re]; ring
      have hwr : w.re ≤ Tb := le_trans (Complex.re_le_norm w) (hTb w hw)
      have hmax : d.ξ₀ + 1 ≤ max R (d.ξ₀ + 1) := le_max_right _ _
      linarith
    exact d.Q_sub (Work.Parab.halfplane_subset_QLeft d.ξ₀ hzre)

end Work.Pert.Ksub2
