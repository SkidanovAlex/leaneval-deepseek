import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.Psi0Aux.GamBar_dthU_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Uniform bounds for the first seven iterates of `Lop` on `Γ̄` and on `6 sin² − 4 cos²`

`Work.Spaces.Lop u θ = sin (2θ) · u'(θ)` is the one-dimensional operator induced by
`D_θ = sin(2θ) ∂_θ`; it is *definitionally* the same function as `Work.Spaces.dthU`.  The
lemma proved here produces a single nonnegative sequence `K` bounding, on the open quadrant
`(0, π/2)` and for all `j ≤ 6`,

* the iterates `Lop^[j] Γ̄_α` of the angular source `Γ̄_α = Γ_α/c_α − (5/4) sin 2θ`,
  *uniformly in `α ∈ (0, 1/4]`*, and
* the iterates `Lop^[j] (6 sin² − 4 cos²)` of a fixed smooth test function
  (the angular part of the `Φ_*`-profile).

## Route

* **The fixed function.**  `h(θ) = 6 sin²θ − 4 cos²θ` is `C^∞`, and `Lop` preserves
  `C^∞`, so every iterate is continuous on the compact interval `[0, π/2]`; compactness
  (`IsCompact.exists_bound_of_continuousOn`) produces a bound, chosen with `Classical.choose`.
* **The `α`-family.**  For `j ≤ 5` the already-proved `Psi0Aux.GamBar_dthU_le` gives
  `|D_θ^j Γ̄| ≤ cc j · α · Γ + dd j · sin 2θ`, and `α ≤ 1/4`, `Γ ≤ 1`, `sin 2θ ≤ 1` turn
  this into `cc j/4 + dd j`; for `j = 0` it gives the constant `K` of that lemma; the
  remaining value `j = 6` is handled by the exact decomposition `D_θ^6 Γ̄ = (1/c) dGam 6 −
  (5/4) Giter 6` on the open quadrant (`Psi0Aux.GamBar_iter_EqOn`), together with
  `|dGam α 6| ≤ α · tBound 5 0 · Γ` and `|Giter 6| ≤ 1095801216 · sin 2θ`
  (`dthU_iter_Tfun_le`, `dthUiter_sin2_iter`).
-/

namespace Work.FTS.PhiStar

theorem LopAuxBounds : ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[j]) (Work.FTS.VocabO.GamBar α) θ| ≤ K j) ∧
    (∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[j]) (fun θ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ| ≤ K j) := by
  -- `Lop` and `dthU` have the same body; we work throughout with `dthU` (the vocabulary in
  -- which the auxiliary estimates are stated) and convert back at the very end.
  have hmain : ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.dthU^[j]) (Work.FTS.VocabO.GamBar α) θ| ≤ K j) ∧
      (∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.dthU^[j]) (fun θ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ| ≤ K j) := by
    -- ## The fixed test function `h = 6 sin² − 4 cos²`, by compactness
    have hsm2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) := by fun_prop
    have key2 : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |(Work.Spaces.dthU^[j]) (fun θ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ| ≤ C := by
      intro j
      have hcont : ContinuousOn
          ((Work.Spaces.dthU^[j]) (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2))
          (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
        ((Work.Spaces.dthU_iter_smooth hsm2 j).continuous).continuousOn
      obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
      refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
      have h := hC θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    choose B2 hB2_0 hB2 using key2
    -- ## The family `Γ̄_α`
    obtain ⟨⟨KG, hKGpos, hKG⟩, cc, dd, hcc0, hdd0, hccdd⟩ :=
      Work.FTS.PhiStar.Psi0Aux.GamBar_dthU_le
    -- the constant for the sixth iterate
    set C6 : ℝ := 10 * (1 / 4 * Work.Spaces.tBound 5 0) + 5 / 4 * 1095801216 with hC6def
    -- ### the range `1 ≤ j ≤ 5`
    have hstep : ∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(Work.Spaces.dthU^[j]) (Work.FTS.VocabO.GamBar α) θ| ≤ cc j / 4 + dd j := by
      intro j hj1 hj5 α hα hα1 θ hθ
      have h := hccdd α hα hα1 j hj1 hj5 θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hG := Work.Spaces.Gam_bounds α θ hα hθI
      have hsin2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have h1 : cc j * α * Work.Spaces.Gam α θ ≤ cc j / 4 := by
        have hαG : α * Work.Spaces.Gam α θ ≤ 1 / 4 := by
          have h' := mul_le_mul hα1 hG.2 hG.1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
          linarith [h']
        have h'' := mul_le_mul_of_nonneg_left hαG (hcc0 j)
        nlinarith [h'']
      have h2 : dd j * Real.sin (2 * θ) ≤ dd j := by
        have h'' := mul_le_mul_of_nonneg_left hsin2le (hdd0 j)
        nlinarith [h'']
      linarith [h, h1, h2]
    -- ### the sixth iterate
    have hstep6 : ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(Work.Spaces.dthU^[6]) (Work.FTS.VocabO.GamBar α) θ| ≤ C6 := by
      intro α hα hα1 θ hθ
      have heq := Work.FTS.PhiStar.Psi0Aux.GamBar_iter_EqOn α hα 6 hθ
      rw [heq, Work.FTS.PhiStar.Psi0Aux.Fbar_apply]
      have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
      have hcpos : 0 < Work.Spaces.c α := by linarith
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hG := Work.Spaces.Gam_bounds α θ hα hθI
      have ht0 : 0 ≤ Work.Spaces.tBound 5 0 := Work.Spaces.tBound_nonneg 5 0
      have hT : |Work.Spaces.Tfun 5 α θ| ≤ Work.Spaces.tBound 5 0 := by
        simpa using Work.Spaces.dthU_iter_Tfun_le 5 α hα (by linarith) θ hθI 0
      have hdG : |Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ| ≤ 1 / 4 * Work.Spaces.tBound 5 0 := by
        have hd : Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ
            = α * Work.Spaces.Tfun 5 α θ * Work.Spaces.Gam α θ := rfl
        rw [hd, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hG.1]
        calc α * |Work.Spaces.Tfun 5 α θ| * Work.Spaces.Gam α θ
            = α * (|Work.Spaces.Tfun 5 α θ| * Work.Spaces.Gam α θ) := by ring
          _ ≤ (1 / 4) * (Work.Spaces.tBound 5 0 * 1) :=
              mul_le_mul hα1 (mul_le_mul hT hG.2 hG.1 ht0)
                (mul_nonneg (abs_nonneg _) hG.1) (by norm_num)
          _ = 1 / 4 * Work.Spaces.tBound 5 0 := by ring
      have hcle : 1 / Work.Spaces.c α ≤ 10 := by
        rw [div_le_iff₀ hcpos]; linarith
      have hA : |(1 / Work.Spaces.c α) * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
          ≤ 10 * (1 / 4 * Work.Spaces.tBound 5 0) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Work.Spaces.c α)]
        calc (1 / Work.Spaces.c α) * |Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
            ≤ 10 * |Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ| :=
              mul_le_mul_of_nonneg_right hcle (abs_nonneg _)
          _ ≤ 10 * (1 / 4 * Work.Spaces.tBound 5 0) := mul_le_mul_of_nonneg_left hdG (by norm_num)
      have hG6 : |Work.FTS.PhiStar.Psi0Aux.Giter 6 θ| ≤ 1095801216 := by
        have hP : |(Work.FTS.PhiStar.Psi0Aux.dthUiterPW 6).eval (Real.cos θ ^ 2)|
            ≤ 1095801216 := by
          rw [Work.FTS.PhiStar.Psi0Aux.dthUiterPW_eval]
          exact le_trans (Work.FTS.PhiStar.Psi0Aux.dthUiter_abs_sum_pow_le _ _ _
            (sq_nonneg _) (Real.cos_sq_le_one θ))
            (Work.FTS.PhiStar.Psi0Aux.dthUiterPWcoef_sum_le 6 (by norm_num))
        have hiter := Work.FTS.PhiStar.Psi0Aux.dthUiter_sin2_iter 6 (by norm_num) θ
        show |Work.Spaces.dthU^[6] (fun t : ℝ => Real.sin (2 * t)) θ| ≤ 1095801216
        rw [hiter, abs_mul]
        calc |Real.sin (2 * θ)|
              * |(Work.FTS.PhiStar.Psi0Aux.dthUiterPW 6).eval (Real.cos θ ^ 2)|
            ≤ 1 * 1095801216 :=
              mul_le_mul (Real.abs_sin_le_one _) hP (abs_nonneg _) (by norm_num)
          _ = 1095801216 := by norm_num
      have hB : |(5 / 4) * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ| ≤ (5 / 4) * 1095801216 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4)]
        exact mul_le_mul_of_nonneg_left hG6 (by norm_num)
      calc |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ
              - 5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ|
          = |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ
              + -(5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ)| := by ring_nf
        _ ≤ |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
              + |-(5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ)| := abs_add_le _ _
        _ = |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
              + |5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ| := by rw [abs_neg]
        _ ≤ C6 := by rw [hC6def]; linarith [hA, hB]
    -- ## assembling the sequence
    let K : ℕ → ℝ := fun j => max (max (max KG C6) (cc j / 4 + dd j)) (B2 j)
    have hK0 : ∀ j, 0 ≤ K j := by
      intro j
      simp only [K]
      exact le_trans (le_trans (le_trans (le_of_lt hKGpos) (le_max_left _ _)) (le_max_left _ _))
        (le_max_left _ _)
    have hKGle : ∀ j, KG ≤ K j := by
      intro j; simp only [K]
      exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    have hC6le : ∀ j, C6 ≤ K j := by
      intro j; simp only [K]
      exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    have hccddle : ∀ j, cc j / 4 + dd j ≤ K j := by
      intro j; simp only [K]
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hB2le : ∀ j, B2 j ≤ K j := by
      intro j; simp only [K]; exact le_max_right _ _
    refine ⟨K, hK0, ?_, ?_⟩
    · intro α hα hα1 j hj θ hθ
      by_cases h0 : j = 0
      · subst h0
        exact le_trans (hKG α hα hα1 θ hθ) (hKGle 0)
      · by_cases h6 : j = 6
        · subst h6
          exact le_trans (hstep6 α hα hα1 θ hθ) (hC6le 6)
        · have hj1 : 1 ≤ j := by omega
          have hj5 : j ≤ 5 := by omega
          exact le_trans (hstep j hj1 hj5 α hα hα1 θ hθ) (hccddle j)
    · intro j hj θ hθ
      exact le_trans (hB2 j θ hθ) (hB2le j)
  exact hmain

end Work.FTS.PhiStar
