import Mathlib
import Submission.Work.Pert.Ksub2.tau0_phi_band_norm_le

namespace Work.Pert.Ksub2

/-!
# `Work.Pert.Ksub2.tau0_phi_band_norm_le_nh`

The band bound `tau0_phi_band_norm_le` **without** the hypothesis `0 < y₁`: for every real
`y₁ > η₀` (in particular for `y₁ ≤ 0`, where the band `{|Im w| ≥ y₁}` contains an unbounded
horizontal strip) the Fatou coordinate `φ` of a §4.1-datum is bounded on
`{|Im w| ≥ y₁, Re w ≤ 1}` and every backward translate `w - m` (`m ≥ 1`) lies in the maximal
domain `Dφ`.

The proof is the one of `tau0_phi_band_norm_le`, which never used `0 < y₁`:

* `B \ QLeft ξ₀` is **bounded**: off the sector `2 Re (w + ξ₀) ≥ ‖w + ξ₀‖`
  (`Work.Parab.QLeft_iff`), which with `Re (w + ξ₀) ≤ 1 + ξ₀` gives
  `‖w‖ ≤ max ξ₀ 1 + 2 (1 + ξ₀)` (`norm_le_max_of_not_mem_QLeft`);
* on `B ∩ {‖w‖ ≥ R₁}` inside the sector, `‖φ w‖ ≤ 1` (`Work.PertCrux.phi_norm_le_of_far`);
* on the bounded rest `B ∩ {‖w‖ ≤ R}`, compactness of `φ`
  (`norm_phi_le_of_mem_band_ball`).
-/

theorem tau0_phi_band_norm_le_nh {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y₁ : ℝ} (hy : d.η₀ < y₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, y₁ ≤ |w.im| → w.re ≤ 1 → ∀ m : ℕ, 1 ≤ m →
      w - (m : ℂ) ∈ d.Dφ ∧ ‖d.φ (w - (m : ℂ))‖ ≤ C := by
  -- far out inside the sector the coordinate is small
  obtain ⟨R₁, hR₁pos, hfar⟩ := Work.PertCrux.phi_norm_le_of_far d (c := 1) one_pos
  -- the bounded piece of the band
  obtain ⟨Cfix, hCfix⟩ :=
    norm_phi_le_of_mem_band_ball d hy (y₁ := y₁) (R := max (max d.ξ₀ 1 + 2 * (1 + d.ξ₀)) R₁)
  refine ⟨max 1 Cfix, lt_max_of_lt_left one_pos, ?_⟩
  intro w hwim hwre m hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have him : (w - (m : ℂ)).im = w.im := by simp
  have hre : (w - (m : ℂ)).re = w.re - (m : ℝ) := by simp
  have hre1 : (w - (m : ℂ)).re ≤ 1 := by rw [hre]; linarith
  have hmwim : y₁ ≤ |(w - (m : ℂ)).im| := by rw [him]; exact hwim
  refine ⟨(d.ends_sub _ (lt_of_lt_of_le hy hmwim)).1, ?_⟩
  by_cases hQ : (w - (m : ℂ)) ∈ MandelDim.QLeft d.ξ₀
  · by_cases hR₁ : ‖w - (m : ℂ)‖ ≤ R₁
    · refine le_trans (hCfix _ hmwim hre1 ?_) (le_max_right _ _)
      exact le_trans hR₁ (le_max_right _ _)
    · exact le_trans (hfar _ hQ (le_of_lt (not_le.mp hR₁))) (le_max_left _ _)
  · refine le_trans (hCfix _ hmwim hre1 ?_) (le_max_right _ _)
    exact le_trans (norm_le_max_of_not_mem_QLeft hre1 hQ) (le_max_left _ _)

end Work.Pert.Ksub2
