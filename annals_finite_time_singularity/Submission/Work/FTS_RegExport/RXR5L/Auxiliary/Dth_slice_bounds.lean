import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR5L.Auxiliary.Dth_slice_bounds`

The angular derivative `D_θ = sin(2θ)·∂_θ` of the slices `slice g τ` of a `LimApprox` family `g`
is uniformly bounded, and is Lipschitz in the fake time `τ`, with the radial weight
`Rwt z = z^{3/2}/(1+z)²`:

  `|D_θ (slice g τ) z θ| ≤ C₁ · Rwt z`
  `|D_θ (slice g τ) z θ − D_θ (slice g τ') z θ| ≤ C₁ · Rwt z · |τ − τ'|`

for `τ, τ' ∈ [0,S]`, `z > 0`, `θ ∈ Iθ = [0,π/2]`.

Both clauses are immediate from the two standing estimates for `LimApprox` families, on the
*open* angle range `0 < θ < π/2`:

* `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` — the weighted slotwise bound
  `|mixed b a (slice g τ) z θ| ≤ C·Rwt z` for `a + b ≤ 2`, obtained from the uniform `ℋ⁴`-bound of
  the class-`C` approximants (the constant `C₀·α²` of the `LimApprox` clause) and the interior
  `L^∞`–`ℋ⁴` trade-off `abs_mixed_le_HkNorm_C4_w_proved`;
* `Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus` — the same slots differ between two
  times by `L·Rwt z·|τ − τ'|`, obtained by applying the trade-off to the class-`C` difference
  `slice (gn n) τ - slice (gn n) τ'` and passing to the limit along the `C⁴`-jet convergence.

`D_θ f` is definitionally `mixed 0 1 f`, so these are exactly the required estimates on the open
range.  The two boundary angles `θ = 0` and `θ = π/2` are handled separately: there `sin(2θ) = 0`,
so `D_θ` vanishes identically *whatever* the (possibly junk) value of `∂_θ f`, and both clauses
are trivial.  This is why the statement needs no restriction to the open angular interval.
-/

namespace Work.FTS_RegExport.RXR5L.Auxiliary

theorem Dth_slice_bounds {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hLim : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ C1 * Work.FTS_RegExport.RXT.L12Iter.Rwt z) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z →
        θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ') z θ|
          ≤ C1 * Work.FTS_RegExport.RXT.L12Iter.Rwt z * |τ - τ'|) := by
  have hαG0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the two standing estimates for the limit family, on the open angular range
  obtain ⟨C, hC0, hC⟩ :=
    Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved (αG := Work.FTS.Regularity.pExp α)
      (C₀ := C₀) hαG0 hαG1 hLim S hS
  obtain ⟨L, hL0, hL⟩ :=
    Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus (αG := Work.FTS.Regularity.pExp α)
      (C₀ := C₀) hLim hαG0 hαG1 S hS
  -- `D_θ` vanishes at both boundary angles, whatever the angular slice does there
  have key0 : ∀ (F : ℝ → ℝ → ℝ) (z θ : ℝ), (θ = 0 ∨ θ = Real.pi / 2) →
      Work.Spaces.Dth F z θ = 0 := by
    rintro F z θ (rfl | rfl)
    · simp [Work.Spaces.Dth]
    · simp only [Work.Spaces.Dth]
      rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
  have hC1 : 0 ≤ max C L := le_trans hC0 (le_max_left _ _)
  refine ⟨max C L, hC1, ?_, ?_⟩
  · intro τ hτ z θ hz hθ
    have hR : 0 ≤ Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
      (Work.FTS_RegExport.RXT.L12Iter.Rwt_pos hz).le
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    by_cases hdeg : θ = 0 ∨ θ = Real.pi / 2
    · rw [key0 (Work.FTS.Galerkin.slice g τ) z θ hdeg, abs_zero]
      exact mul_nonneg hC1 hR
    · rw [not_or] at hdeg
      have hθ0' : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hdeg.1)
      have hθ1' : θ < Real.pi / 2 := lt_of_le_of_ne hθ1 hdeg.2
      have h := hC τ hτ 0 1 (by norm_num) z θ hz hθ0' hθ1'
      calc |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ|
          = |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ| := rfl
        _ ≤ C * Work.FTS_RegExport.RXT.L12Iter.Rwt z := h
        _ ≤ max C L * Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hR
  · intro τ hτ τ' hτ' z θ hz hθ
    have hR : 0 ≤ Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
      (Work.FTS_RegExport.RXT.L12Iter.Rwt_pos hz).le
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    by_cases hdeg : θ = 0 ∨ θ = Real.pi / 2
    · rw [key0 (Work.FTS.Galerkin.slice g τ) z θ hdeg,
        key0 (Work.FTS.Galerkin.slice g τ') z θ hdeg, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hC1 hR) (abs_nonneg _)
    · rw [not_or] at hdeg
      have hθ0' : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hdeg.1)
      have hθ1' : θ < Real.pi / 2 := lt_of_le_of_ne hθ1 hdeg.2
      have h := hL τ hτ τ' hτ' 0 1 (by norm_num) z θ hz hθ0' hθ1'
      calc |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ') z θ|
          = |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ| := rfl
        _ ≤ L * Work.FTS_RegExport.RXT.L12Iter.Rwt z * |τ - τ'| := h
        _ ≤ max C L * Work.FTS_RegExport.RXT.L12Iter.Rwt z * |τ - τ'| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)
              (abs_nonneg _)

end Work.FTS_RegExport.RXR5L.Auxiliary
