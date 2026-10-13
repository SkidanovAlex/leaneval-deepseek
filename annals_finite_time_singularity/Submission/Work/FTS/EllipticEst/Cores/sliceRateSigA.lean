/-
Copyright: work module for the Elgindi finite-time singularity project.

# The endpoint rate of a slice, in the light weight `σ_a = sin(2θ)^{2-γ}`

The target `sliceRateSigA` is the endpoint rate used by the `Step 5` / interpolation chain:
for a `C¹` slice `Φ` on `(0,π/2)` whose weighted derivative square is `σ_a`-integrable,

* `Φ` has a limit `c` at `0⁺` (and `c'` at `(π/2)⁻`), and
* `(Φ θ - c)² ≤ K θ^{γ-1} ∫_0^θ (Φ')² σ_a`,   `(Φ θ - c')² ≤ K (π/2-θ)^{γ-1} ∫_θ^{π/2} (Φ')² σ_a`

with a constant `K = K(α)` uniform in `Φ`.

The ingredients — the Cauchy–Schwarz step, the weight bound `∫_0^θ σ_a^{-1} ≤ K θ^{γ-1}` and
its mirror at `π/2`, the interior FTC and the squeeze for the endpoint limit — are proved in
`Submission.Work.FTS.EllipticEst.Cores.SigABasic`.

The exact statement of `sliceRateSigA` is the one requested; nothing here changes it.

Everything in this file is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.SigABasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

theorem sliceRateSigA :
    ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∃ K : ℝ, 0 < K ∧ ∀ (Φ : ℝ → ℝ),
        ContDiffOn ℝ 1 Φ (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (deriv Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        (∃ c : ℝ, Filter.Tendsto Φ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
            ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
              (Φ θ - c) ^ 2 ≤ K * θ ^ (Work.Spaces.gam α - 1) *
                ∫ θ' in Set.Ioo 0 θ,
                  (deriv Φ θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α))
        ∧ (∃ c : ℝ,
            Filter.Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
            ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
              (Φ θ - c) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) *
                ∫ θ' in Set.Ioo θ (Real.pi / 2),
                  (deriv Φ θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) := by
  intro α hα hα1
  obtain ⟨KW, hKW, hKWb⟩ := integral_sigA_inv_le α hα hα1
  obtain ⟨KWr, hKWr, hKWrb⟩ := integral_sigA_inv_le_right α hα hα1
  have he : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hKpos : (0 : ℝ) < max KW KWr := lt_of_lt_of_le hKW (le_max_left _ _)
  have hKnn : (0 : ℝ) ≤ max KW KWr := hKpos.le
  refine ⟨max KW KWr, hKpos, fun Φ hΦ hInt => ⟨?_, ?_⟩⟩
  · -- ===================== left endpoint =====================
    have hA : IntegrableOn (fun t : ℝ => (deriv Φ t) ^ 2 * sigA α t)
        (Set.Ioo 0 (Real.pi / 2)) := hInt
    have hB : IntegrableOn (fun t : ℝ => (sigA α t)⁻¹) (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_sigA_inv hα hα1).mono_set Set.Ioo_subset_Icc_self
    have hderiv : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2)) :=
      integrableOn_deriv measurableSet_Ioo (fun t ht => ht) hA hB
    set c : ℝ := Φ (Real.pi / 4) - ∫ t in Set.Ioo 0 (Real.pi / 4), deriv Φ t with hc
    have hid : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Φ θ - c = ∫ t in Set.Ioo 0 θ, deriv Φ t := by
      intro θ hθ
      rw [hc]
      exact ftc_at_quarter hΦ hderiv θ hθ
    have hMnn : (0 : ℝ) ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
      setIntegral_nonneg measurableSet_Ioo (fun t ht => sq_mul_sigA_nonneg ht (deriv Φ t))
    have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
          * ∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t := by
      intro θ hθ
      have hs : Set.Ioo (0 : ℝ) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
        fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
      have hAθ : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t) (Set.Ioo 0 θ) :=
        hA.mono_set hs
      have hBθ : IntegrableOn (fun t => (sigA α t)⁻¹) (Set.Ioo 0 θ) := hB.mono_set hs
      have hcs := cs_step hα1 measurableSet_Ioo hs hAθ hBθ
      rw [hid θ hθ]
      have h2 : ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹ ≤ KW * θ ^ (Work.Spaces.gam α - 1) :=
        hKWb θ hθ
      have h5 : KW ≤ max KW KWr := le_max_left _ _
      have h6 : (0 : ℝ) ≤ θ ^ (Work.Spaces.gam α - 1) := Real.rpow_nonneg hθ.1.le _
      have h7 : (0 : ℝ) ≤ ∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_nonneg measurableSet_Ioo (fun x hx => sq_mul_sigA_nonneg (hs hx) (deriv Φ x))
      calc (∫ t in Set.Ioo 0 θ, deriv Φ t) ^ 2
          ≤ (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
              * (∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
              * (KW * θ ^ (Work.Spaces.gam α - 1)) := mul_le_mul_of_nonneg_left h2 h7
        _ ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
              * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t) := by
            rw [show (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                  * (KW * θ ^ (Work.Spaces.gam α - 1))
                = KW * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                  * θ ^ (Work.Spaces.gam α - 1) from by ring,
              show (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
                  * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                = (max KW KWr) * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                  * θ ^ (Work.Spaces.gam α - 1) from by ring]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 h7) h6
    have hfull : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * θ ^ (Work.Spaces.gam α - 1) := by
      intro θ hθ
      have h1 : ∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t
          ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_mono_Ioo hθ.2.le hA (fun x hx => sq_mul_sigA_nonneg hx (deriv Φ x))
      have h2 : (0 : ℝ) ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1) :=
        mul_nonneg hKnn (Real.rpow_nonneg hθ.1.le _)
      calc (Φ θ - c) ^ 2
          ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t) := hbound θ hθ
        _ ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (max KW KWr * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
            * θ ^ (Work.Spaces.gam α - 1) := by ring
    have habs : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |Φ θ - c| ≤ Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * θ ^ ((Work.Spaces.gam α - 1) / 2) := by
      intro θ hθ
      exact abs_le_sqrt_mul_rpow hKnn hMnn hθ.1.le (hfull θ hθ)
    have hlim : Tendsto Φ (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
      have h0 : Tendsto (fun θ => Φ θ - c) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_zero_of_abs_le (A := Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)))
          (by linarith : 0 < (Work.Spaces.gam α - 1) / 2) habs
      have h1 := Tendsto.add_const c h0
      simpa using h1
    exact ⟨c, hlim, hbound⟩
  · -- ===================== right endpoint =====================
    have hA : IntegrableOn (fun t : ℝ => (deriv Φ t) ^ 2 * sigA α t)
        (Set.Ioo 0 (Real.pi / 2)) := hInt
    have hB : IntegrableOn (fun t : ℝ => (sigA α t)⁻¹) (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_sigA_inv hα hα1).mono_set Set.Ioo_subset_Icc_self
    have hderiv : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2)) :=
      integrableOn_deriv measurableSet_Ioo (fun t ht => ht) hA hB
    set c : ℝ := Φ (Real.pi / 4) + ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), deriv Φ t with hc
    have hid : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Φ θ - c = -(∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) := by
      intro θ hθ
      rw [hc]
      exact ftc_at_quarter_right hΦ hderiv θ hθ
    have hMnn : (0 : ℝ) ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
      setIntegral_nonneg measurableSet_Ioo (fun t ht => sq_mul_sigA_nonneg ht (deriv Φ t))
    have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
          * ∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t := by
      intro θ hθ
      have hs : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
        fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
      have hAθ : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t)
          (Set.Ioo θ (Real.pi / 2)) := hA.mono_set hs
      have hBθ : IntegrableOn (fun t => (sigA α t)⁻¹) (Set.Ioo θ (Real.pi / 2)) :=
        hB.mono_set hs
      have hcs := cs_step hα1 measurableSet_Ioo hs hAθ hBθ
      rw [hid θ hθ]
      rw [show (-(∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t)) ^ 2
          = (∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) ^ 2 from by ring]
      have h2 : ∫ t in Set.Ioo θ (Real.pi / 2), (sigA α t)⁻¹
          ≤ KWr * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := hKWrb θ hθ
      have h5 : KWr ≤ max KW KWr := le_max_right _ _
      have h6 : (0 : ℝ) ≤ (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) :=
        Real.rpow_nonneg (by linarith [hθ.2]) _
      have h7 : (0 : ℝ) ≤ ∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_nonneg measurableSet_Ioo (fun x hx => sq_mul_sigA_nonneg (hs hx) (deriv Φ x))
      calc (∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) ^ 2
          ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
              * (∫ t in Set.Ioo θ (Real.pi / 2), (sigA α t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
              * (KWr * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)) :=
            mul_le_mul_of_nonneg_left h2 h7
        _ ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
              * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) := by
            rw [show (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                  * (KWr * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1))
                = KWr * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                  * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) from by ring,
              show (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
                  * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                = (max KW KWr) * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                  * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) from by ring]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 h7) h6
    have hfull : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := by
      intro θ hθ
      have h1 : ∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t
          ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_mono_Ioo_left hθ.1.le hA (fun x hx => sq_mul_sigA_nonneg hx (deriv Φ x))
      have h2 : (0 : ℝ) ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) :=
        mul_nonneg hKnn (Real.rpow_nonneg (by linarith [hθ.2]) _)
      calc (Φ θ - c) ^ 2
          ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) := hbound θ hθ
        _ ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (max KW KWr * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
            * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := by ring
    have habs : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Φ (Real.pi / 2 - y) - c| ≤ Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * y ^ ((Work.Spaces.gam α - 1) / 2) := by
      intro y hy
      have hθ : Real.pi / 2 - y ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have hfy : (Φ (Real.pi / 2 - y) - c) ^ 2
          ≤ (max KW KWr * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
            * y ^ (Work.Spaces.gam α - 1) := by
        have hf := hfull (Real.pi / 2 - y) hθ
        simpa [show Real.pi / 2 - (Real.pi / 2 - y) = y from by ring] using hf
      exact abs_le_sqrt_mul_rpow hKnn hMnn hy.1.le hfy
    have hlim : Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
      have h0 : Tendsto (fun θ => Φ θ - c) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds 0) :=
        tendsto_zero_of_abs_le_reflect (A := Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)))
          (by linarith : 0 < (Work.Spaces.gam α - 1) / 2) habs
      have h1 := Tendsto.add_const c h0
      simpa using h1
    exact ⟨c, hlim, hbound⟩

end Work.FTS.EllipticEst.Cores
