import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FaSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

theorem FaSumAE {N : Work.FTS.Galerkin.Fn} (p : Fin 20 → Work.FTS.Galerkin.Fn)
    (hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd → N r θ = ∑ k, p k r θ)
    (hin : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20, AEMeasurable
      (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)
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
    by_cases h1 : θ = Real.pi / 2
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
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    show ENNReal.ofReal |Work.Spaces.K θ * N r θ|
      = ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|
    rw [hkey r θ hr hθ]
  -- ### Step 2: the `θ`-integral of the sum is at most the sum of the `θ`-integrals
  -- (this only uses the triangle inequality in `θ` and hence holds for *every* `r`
  -- for which the summands are `θ`-a.e.-measurable, in particular a.e. `r`)
  have hinnerSum : ∀ r : ℝ, (∀ k : Fin 20, AEMeasurable
        (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) →
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
        ≤ ∑ k : Fin 20, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.K θ * p k r θ| := by
    intro r hk
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
    rw [MeasureTheory.lintegral_finsetSum' Finset.univ (fun k _ => hk k)] at hstep
    exact hstep
  -- ### Step 3: replace `N` by the sum in the outer (`r`-)integral (pointwise, `r > 0`)
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
  have hae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
        ≤ ∑ k : Fin 20, ENNReal.ofReal r⁻¹ *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) := by
    filter_upwards [hin] with r hrin
    rw [← Finset.mul_sum]
    exact mul_le_mul_right (hinnerSum r hrin) _
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ∑ k : Fin 20, ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) :=
        MeasureTheory.lintegral_mono_ae hae
    _ = ∑ k : Fin 20, ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) :=
        MeasureTheory.lintegral_finsetSum' Finset.univ (fun k _ =>
          ((ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable).mul (hout k))

end Work.FTS.Nonlinear.Pieces.rl1Tools
