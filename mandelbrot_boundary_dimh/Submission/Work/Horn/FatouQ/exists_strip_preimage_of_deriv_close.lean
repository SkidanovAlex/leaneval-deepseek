import Mathlib
import Submission.Work.FatouCoord.Exist.exists_eq_of_deriv_close
import Submission.Work.Horn.FatouQ.exists_threshold_rpow_interval

namespace Work.Horn.FatouQ

/-- Near-identity surjectivity onto a right half-strip.

If `φ` is complex-differentiable on the open half-plane `{w | R < w.re}`, has derivative
`1 + O(1)` there (indeed within distance `1/2` of `1`), and is `O(‖w‖^θ)`-close to the
identity with `θ < 1`, then for every half-strip `{|im| ≤ b, re > C}` there is `C` large
enough that `φ` maps the half-plane `{re > R}` onto that half-strip.

The derivative hypothesis makes `w ↦ w - φ w + τ` a `1/2`-contraction near each target
`τ`; the sublinear bound `‖φ w - w‖ ≤ C0 ‖w‖^θ + C1` supplies a disk around `τ`, of
radius comparable to `‖τ‖^θ`, that the contraction maps into itself. -/
theorem exists_strip_preimage_of_deriv_close
    {φ : ℂ → ℂ} {R θ C0 C1 : ℝ} (hR : 0 < R) (hθ : θ < 1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hφdiff : DifferentiableOn ℂ φ {w : ℂ | R < w.re})
    (hderiv : ∀ w : ℂ, R < w.re → ‖deriv φ w - 1‖ ≤ 1 / 2)
    (hclose : ∀ w : ℂ, R < w.re → ‖φ w - w‖ ≤ C0 * ‖w‖ ^ θ + C1) :
    ∀ b : ℝ, ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ b →
      ∃ w : ℂ, R < w.re ∧ φ w = τ := by
  have hopen : IsOpen {w : ℂ | R < w.re} := isOpen_lt continuous_const Complex.continuous_re
  intro b
  by_cases hb : 0 ≤ b
  · -- nontrivial case: the strip is nonempty, pick the threshold radius
    obtain ⟨A, hA⟩ := exists_threshold_rpow_interval (θ := θ) (K := 4 * C0)
      (L := 4 * C1 + R) hθ (by linarith) (by linarith) hb
    refine ⟨max A (max b (max 1 (2 * R))), ?_⟩
    intro τ hτ hτim
    have hτle : max A (max b (max 1 (2 * R))) ≤ τ.re := le_of_lt hτ
    have hτA : A ≤ τ.re := le_trans (le_max_left _ _) hτle
    have hτb : b ≤ τ.re :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hτle)
    have hτ1 : 1 ≤ τ.re :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτle))
    have hτ2R : 2 * R ≤ τ.re :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτle))
    have hτR : R < τ.re := by linarith
    have habs : |τ.re| = τ.re := abs_of_nonneg (by linarith)
    set ρ : ℝ := (τ.re - R) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    -- `‖τ‖` lies between `τ.re` and `τ.re + b`
    have hnorm_le : ‖τ‖ ≤ τ.re + b := by
      calc ‖τ‖ ≤ |τ.re| + |τ.im| := Complex.norm_le_abs_re_add_abs_im τ
        _ = τ.re + |τ.im| := by rw [habs]
        _ ≤ τ.re + b := by linarith
    have hnorm_ge : τ.re ≤ ‖τ‖ := Complex.re_le_norm τ
    have hgrowth : 4 * C0 * ‖τ‖ ^ θ + (4 * C1 + R) ≤ τ.re :=
      hA τ.re ‖τ‖ hτA hnorm_ge hnorm_le
    have hcloseτ : C0 * ‖τ‖ ^ θ + C1 ≤ ρ / 2 := by rw [hρdef]; linarith
    -- the closed disk of radius `ρ` around `τ` lies in the half-plane
    have hre_mem : ∀ w : ℂ, dist w τ ≤ ρ → R < w.re := by
      intro w hw
      have h2 : ‖w - τ‖ ≤ ρ := by rwa [dist_eq_norm] at hw
      have h4 : -(ρ) ≤ (w - τ).re := by
        have h : |(w - τ).re| ≤ ρ := le_trans (Complex.abs_re_le_norm (w - τ)) h2
        linarith [neg_abs_le (w - τ).re]
      have h3 : w.re = τ.re + (w - τ).re := by rw [Complex.sub_re]; ring
      rw [h3]
      rw [hρdef] at h4
      linarith
    have hp : dist (φ τ) τ ≤ (1 - 1 / 2) * ρ := by
      rw [dist_eq_norm]
      have h1 : ‖φ τ - τ‖ ≤ C0 * ‖τ‖ ^ θ + C1 := hclose τ hτR
      have h2 : (1 - 1 / 2) * ρ = ρ / 2 := by ring
      rw [h2]
      linarith
    obtain ⟨w, hw, hwφ⟩ := Work.FatouCoord.Exist.exists_eq_of_deriv_close
      (ψ := φ) (τ := τ) (ρ := ρ) (q := 1 / 2) hρpos (by norm_num) (by norm_num)
      (fun w hw => hφdiff.differentiableAt (hopen.mem_nhds (hre_mem w hw)))
      (fun w hw => hderiv w (hre_mem w hw)) hp
    exact ⟨w, hre_mem w hw, hwφ⟩
  · -- empty strip: any `C` works
    have hblt : b < 0 := not_le.mp hb
    refine ⟨0, ?_⟩
    intro τ _ hτim
    exfalso
    linarith [abs_nonneg τ.im]

end Work.Horn.FatouQ
