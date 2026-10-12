import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.KernelIds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniform scaling bounds on the iterated derivatives of the rescaled bump `χ_ℓ`

`Submission.BoseGases.chiScale ℓ` is the rescaled localization function
`χ_ℓ(x) = χ(x/ℓ)` used throughout the Fournais--Solovej box analysis.  It is
smooth with compact support, and its `j`-th iterated derivative is bounded by
`C_j / ℓ^j`, uniformly in the point and in a translation of the argument.

This file records the estimate in the form required by the kinetic-crux
assembly: a single constant `C` (depending only on the truncation order `N`)
such that

  `‖D^j (χ_ℓ(· − x₀) − c) x‖ ≤ C (1 + C₀) / A^j`     for `j ≤ N`, `|c| ≤ C₀`,

whenever `0 < A ≤ ℓ`.  The subtraction of the constant `c` is harmless for
`j ≥ 1` (derivatives kill constants); for `j = 0` it costs the factor
`(1 + C₀)` on the right-hand side.
-/

noncomputable section

namespace Work.BoseFixB1S.kineticCrux

open scoped ContDiff

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Uniform bounds on the iterated derivatives of the bump `χ`: for every `j`
there is a constant `M j ≥ 0` bounding `‖D^j χ‖` everywhere.  This is
continuity plus compact support. -/
lemma exists_chi_iteratedFDeriv_bound :
    ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧
      ∀ j (y : ℝ³), ‖iteratedFDeriv ℝ j Submission.BoseGases.chi y‖ ≤ M j := by
  have h : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ³, ‖iteratedFDeriv ℝ j Submission.BoseGases.chi y‖ ≤ C := by
    intro j
    have hcs : HasCompactSupport (iteratedFDeriv ℝ j Submission.BoseGases.chi) :=
      Submission.BoseGases.chi_hasCompactSupport.iteratedFDeriv j
    have hcont : Continuous (iteratedFDeriv ℝ j Submission.BoseGases.chi) :=
      Submission.BoseGases.chi_contDiff.continuous_iteratedFDeriv (mod_cast le_top)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    exact ⟨max C 0, le_max_right C 0, fun y => (hC y).trans (le_max_left C 0)⟩
  choose M hM0 hMbd using h
  exact ⟨M, hM0, hMbd⟩

/-- Derivative of a dilated function: rescaling the argument by the scalar `c`
costs a factor `‖c‖^j` in the `j`-th iterated derivative. -/
lemma norm_iteratedFDeriv_comp_smul_le {f : ℝ³ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ)
    (j : ℕ) (x : ℝ³) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ³ => f (c • z)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (c • x)‖ * ‖c‖ ^ j := by
  let S : ℝ³ →L[ℝ] ℝ³ := c • ContinuousLinearMap.id ℝ ℝ³
  have hSx : S x = c • x := by simp [S]
  have hcomp : (fun z : ℝ³ => f (c • z)) = f ∘ S := by funext z; simp [S]
  have hnorm : ‖S‖ ≤ ‖c‖ :=
    calc ‖S‖ ≤ ‖c‖ * ‖ContinuousLinearMap.id ℝ ℝ³‖ := by
            simpa [S] using norm_smul_le c (ContinuousLinearMap.id ℝ ℝ³)
      _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg c)
      _ = ‖c‖ := mul_one ‖c‖
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right S hf x (mod_cast le_top)]
  calc ‖(iteratedFDeriv ℝ j f (S x)).compContinuousLinearMap (fun _ : Fin j => S)‖
      ≤ ‖iteratedFDeriv ℝ j f (S x)‖ * ∏ _ : Fin j, ‖S‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j f (S x)‖ * ‖S‖ ^ j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ‖iteratedFDeriv ℝ j f (c • x)‖ * ‖c‖ ^ j := by
        rw [hSx]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm j) (norm_nonneg _)

/-- The translated and rescaled bump has small iterated derivatives:
`‖D^j (χ(ℓ⁻¹ • (· − x₀))) x‖ ≤ M j / ℓ^j` for every `ℓ > 0`. -/
lemma norm_iteratedFDeriv_chiScale_sub_le {ℓ : ℝ} (hℓ : 0 < ℓ) {M : ℕ → ℝ}
    (hM : ∀ j (y : ℝ³), ‖iteratedFDeriv ℝ j Submission.BoseGases.chi y‖ ≤ M j)
    (j : ℕ) (x₀ x : ℝ³) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀)) x‖
      ≤ M j / ℓ ^ j := by
  have hfun : (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀))
      = fun z : ℝ³ => Submission.BoseGases.chi (ℓ⁻¹ • (z - x₀)) := by
    funext z; simp [Submission.BoseGases.chiScale]
  rw [hfun]
  rw [iteratedFDeriv_comp_sub (f := fun w : ℝ³ => Submission.BoseGases.chi (ℓ⁻¹ • w)) j x₀ x]
  calc ‖iteratedFDeriv ℝ j (fun w : ℝ³ => Submission.BoseGases.chi (ℓ⁻¹ • w)) (x - x₀)‖
      ≤ ‖iteratedFDeriv ℝ j Submission.BoseGases.chi (ℓ⁻¹ • (x - x₀))‖ * ‖ℓ⁻¹‖ ^ j :=
        norm_iteratedFDeriv_comp_smul_le Submission.BoseGases.chi_contDiff (ℓ⁻¹) j (x - x₀)
    _ = ‖iteratedFDeriv ℝ j Submission.BoseGases.chi (ℓ⁻¹ • (x - x₀))‖ * (ℓ⁻¹) ^ j := by
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
    _ ≤ M j * (ℓ⁻¹) ^ j :=
        mul_le_mul_of_nonneg_right (hM j _) (pow_nonneg (inv_nonneg.mpr (le_of_lt hℓ)) j)
    _ = M j / ℓ ^ j := by rw [inv_pow, div_eq_mul_inv]

theorem chiScale_iteratedFDeriv_le {ℓ A C₀ : ℝ} (hA : 0 < A) (hℓA : A ≤ ℓ) (hC₀ : 0 ≤ C₀)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x₀ : EuclideanSpace ℝ (Fin 3)} {c : ℝ}, |c| ≤ C₀ →
      ∀ (j : ℕ), j ≤ N → ∀ x : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ j
          (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiScale ℓ (z - x₀) - c) x‖
          ≤ C * (1 + C₀) / A ^ j := by
  obtain ⟨M, hM0, hMbd⟩ := exists_chi_iteratedFDeriv_bound
  set C : ℝ := (∑ k ∈ Finset.range (N + 1), M k) + 1 with hCdef
  have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), M k := Finset.sum_nonneg (fun k _ => hM0 k)
  have hC1 : 1 ≤ C := by rw [hCdef]; linarith
  have hCnonneg : 0 ≤ C := le_trans zero_le_one hC1
  have hMC : ∀ j, j ≤ N → M j ≤ C := by
    intro j hj
    have hmem : j ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have h1 : M j ≤ ∑ k ∈ Finset.range (N + 1), M k :=
      Finset.single_le_sum (f := M) (fun k _ => hM0 k) hmem
    rw [hCdef]; linarith
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hA hℓA
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
  refine ⟨C, hCnonneg, ?_⟩
  intro x₀ c hc j hj x
  have key : ‖iteratedFDeriv ℝ j (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀)) x‖
      ≤ M j / A ^ j := by
    refine (norm_iteratedFDeriv_chiScale_sub_le hℓpos hMbd j x₀ x).trans ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hℓpos)) ((inv_le_inv₀ hℓpos hA).mpr hℓA) j)
      (hM0 j)
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have h1 : ‖Submission.BoseGases.chiScale ℓ (x - x₀)‖ ≤ M 0 := by
      have hb := hMbd 0 (ℓ⁻¹ • (x - x₀))
      rw [norm_iteratedFDeriv_zero] at hb
      simpa [Submission.BoseGases.chiScale] using hb
    have h2 : ‖c‖ ≤ C₀ := by rwa [Real.norm_eq_abs]
    have h3 : M 0 ≤ C := hMC 0 (Nat.zero_le N)
    calc ‖iteratedFDeriv ℝ 0
            (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀) - c) x‖
        = ‖Submission.BoseGases.chiScale ℓ (x - x₀) - c‖ := by
          rw [norm_iteratedFDeriv_zero]
      _ ≤ ‖Submission.BoseGases.chiScale ℓ (x - x₀)‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ M 0 + C₀ := add_le_add h1 h2
      _ ≤ C * (1 + C₀) := by nlinarith [hC1, hC₀, h3, hM0 0]
      _ = C * (1 + C₀) / A ^ 0 := by rw [pow_zero, div_one]
  · have hcd : ContDiff ℝ ∞ (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀)) :=
      (Submission.BoseGases.chiScale_contDiff hℓne).comp (contDiff_id.sub contDiff_const)
    have hgoal : ‖iteratedFDeriv ℝ j
          (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀) - c) x‖
        = ‖iteratedFDeriv ℝ j (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀)) x‖ := by
      have hfs : (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀) - c)
          = (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀)) - (fun _ : ℝ³ => c) := rfl
      have hcdj : ContDiff ℝ (j : ℕ∞ω)
          (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀)) := hcd.of_le (mod_cast le_top)
      rw [hfs, iteratedFDeriv_sub hcdj contDiff_const]
      have hzero : iteratedFDeriv ℝ j (fun _ : ℝ³ => c) x = 0 := by
        have hh := congr_fun
          (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := ℝ³) (F := ℝ) (ne_of_gt hjpos) c) x
        simpa using hh
      rw [Pi.sub_apply, hzero, sub_zero]
    rw [hgoal]
    calc ‖iteratedFDeriv ℝ j (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - x₀)) x‖
        ≤ M j / A ^ j := key
      _ ≤ C / A ^ j :=
          div_le_div_of_nonneg_right (hMC j hj) (pow_nonneg (le_of_lt hA) j)
      _ ≤ C * (1 + C₀) / A ^ j :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_right hCnonneg (by linarith))
            (pow_nonneg (le_of_lt hA) j)

end Work.BoseFixB1S.kineticCrux
