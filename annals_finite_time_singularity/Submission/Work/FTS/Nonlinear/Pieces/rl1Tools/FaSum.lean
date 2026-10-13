import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-!
## `FaSum` — the triangle inequality for the `L¹(ℝ⁺, r⁻¹dr)`-norm

The weight `K θ * ·` and the `r`-weight `r⁻¹` are nonnegative, so the ~"norm" carried by the
double `lintegral`
`‖f‖ := ∫⁻ r in (0,∞), r⁻¹ * ∫⁻ θ in Iθ, |K θ * f r θ|`
is subadditive: if `N` splits on the open quadrant `Qd` as a *finite* sum `∑ k, p k` (the
twenty summands of the nonlinearity `N`), then `‖N‖ ≤ ∑ k ‖p k‖`.

The only point of care is that the split `hsplit` is assumed on the **open** quadrant, whereas
the inner integral runs over the **closed** interval `Iθ = [0, π/2]`.  On the two endpoints the
weight `K` vanishes (`K 0 = K (π/2) = 0`), so the identity propagates for every `r > 0`.

### A parser fix required by the statement as requested

The third hypothesis of the requested statement writes the integrand of the `AEMeasurable`
hypothesis *without the closing bar* of the absolute value,
`ENNReal.ofReal |Work.Spaces.K θ * p k r θ`.  With Mathlib's global absolute-value notation
(`macro:max atomic("|" noWs) a:term noWs "|"`) that is a *parse error*, so the requested
statement cannot be elaborated as it stands (the same integrand is written correctly, with both
bars, in the fourth hypothesis `hout`).

We do not touch the statement: instead we register, **locally to this file**, the missing
`|·|`-without-closing-bar notation (a prefix `|` whose argument is a full term *not* followed by
`|`), which expands to exactly the same `abs` as the standard notation.  Every other occurrence
of `|·|` in the file -- and of the standard `|·|` in files that import this one -- is unaffected,
because the auxiliary parser requires that no `|` follows the argument (so the standard notation
is selected whenever both bars are present) and because the declaration is `local`, hence not
exported.

This is the only way the *requested text* can be elaborated: with the text as requested plus
this notation the third hypothesis means the same thing as the fourth. -/

open Lean Parser in
/-- `notFollowedBy`-guard for the local absolute-value notation without the closing bar. -/
private def noClosingBar : Parser :=
  notFollowedBy (symbol "|") "the closing `|` of the absolute value notation is omitted here"

open Lean Parser in
local macro:max atomic("|" noWs) a:term noClosingBar : term => `(abs $a)

theorem FaSum {N : Work.FTS.Galerkin.Fn} (p : Fin 20 → Work.FTS.Galerkin.Fn)
    (hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd → N r θ = ∑ k, p k r θ)
    (hin : ∀ k : Fin 20, ∀ r : ℝ, AEMeasurable
      (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ * p k r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hout : ∀ k : Fin 20, AEMeasurable
      (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∑ k : Fin 20, (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)) := by
  classical
  -- ### Step 0: the split holds on all of `Iθ`, the endpoints being killed by `K`
  have hkey : ∀ (r θ : ℝ), 0 < r → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.K θ * N r θ = Work.Spaces.K θ * ∑ k : Fin 20, p k r θ := by
    intro r θ hr hθ
    by_cases h0 : θ = 0
    · subst h0
      simp [Work.Spaces.K]
    by_cases h1 : θ = π / 2
    · subst h1
      simp [Work.Spaces.K]
    · have hq : (r, θ) ∈ Work.Construction.Qd := by
        rw [Work.Construction.Qd]
        simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨hr, lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 h1⟩
      rw [hsplit r θ hq]
  -- ### Step 1: the inner (`θ`-)integral of `N` is that of the sum, for every `r > 0`
  have hinnerEq : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ| := by
    intro r hr
    apply MeasureTheory.setLIntegral_congr_fun
    · exact measurableSet_Icc
    · intro θ hθ
      show ENNReal.ofReal |Work.Spaces.K θ * N r θ|
        = ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|
      rw [hkey r θ hr hθ]
  -- ### Step 2: the `θ`-integral of the sum is at most the sum of the `θ`-integrals
  have hinnerSum : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
        ≤ ∑ k : Fin 20, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.K θ * p k r θ| := by
    intro r hr
    have hstep : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ∑ k : Fin 20,
            ENNReal.ofReal |Work.Spaces.K θ * p k r θ| := by
      apply MeasureTheory.lintegral_mono
      intro θ
      have h1 : ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|
          ≤ ENNReal.ofReal (∑ k : Fin 20, |Work.Spaces.K θ * p k r θ|) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.mul_sum]
        exact Finset.abs_sum_le_sum_abs _ _
      have h2 : ENNReal.ofReal (∑ k : Fin 20, |Work.Spaces.K θ * p k r θ|)
          = ∑ k : Fin 20, ENNReal.ofReal |Work.Spaces.K θ * p k r θ| :=
        ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg _)
      exact h1.trans_eq h2
    rw [MeasureTheory.lintegral_finsetSum' Finset.univ (fun k _ => hin k r)] at hstep
    exact hstep
  -- ### Step 3: replace `N` by the sum in the outer (`r`-)integral
  have hEq : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|) := by
    apply MeasureTheory.lintegral_congr_ae
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro r hr
    show ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
      = ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
    rw [hinnerEq r hr]
  rw [hEq]
  -- ### Step 4: pull `r⁻¹` and the outer integral through the finite sum
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ∑ k : Fin 20, ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) := by
        apply MeasureTheory.lintegral_mono_ae
        apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        intro r hr
        show ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
          ≤ ∑ k : Fin 20, ENNReal.ofReal r⁻¹ *
            (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)
        rw [← Finset.mul_sum]
        exact mul_le_mul_right (hinnerSum r hr) _
    _ = ∑ k : Fin 20, ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) :=
        MeasureTheory.lintegral_finsetSum' Finset.univ (fun k _ =>
          ((ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable).mul (hout k))

end Work.FTS.Nonlinear.Pieces.rl1Tools
