import Mathlib
import Submission.Work.LayerCont.Defs
import Submission.Work.LayerCont.TruncDefs
import Submission.Work.LayerCont.TailIntegrable
import Submission.Work.Asymptotics.detourLeftC_eq_interval_sub_residue
import Submission.Work.Asymptotics.Kaxis_local_tail
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- **The trunc mirror of `LowAgreement`.**  With the pole `τ-1` at height `t₀ > 1` inside the
swept interval `I = (t₀-A, t₀+A) ⊆ [1,∞)`, the deformed trunc layer

`sinSqC r · (∫_{[1,∞)∖I} (K - Aexp)·g + detourLeftC - ∫_I Aexp·g) + sinSqC r · resCorr`

equals the paper's trunc layer `layerTrunc = sinSq r · ∫_{[1,∞)} (K - Aexp)·g` on `{Re τ < 1}`.

Three facts assemble it:

* `Work.Asymptotics.detourLeftC_eq_interval_sub_residue`:
  `detourLeftC = ∫_I K·g - resCorr` (Cauchy–Goursat across the simple pole `τ-1`, which lies inside
  the rectangle because `Re τ < 1`);
* the `Aexp` part is *entire* in the second variable, so its detour contributes exactly
  `∫_I Aexp·g` — so the deformed object is
  `sinSqC r · (∫_{[1,∞)∖I}(K-Aexp)·g + ∫_I K·g - ∫_I Aexp·g)` with the two residue terms cancelling;
* reassembling gives exactly `sinSq r · ∫_{[1,∞)}(K-Aexp)·g = layerTrunc`.

The hypothesis `τ ∈ 𝒟` is what makes the trunc integral *integrable*: the cusp expansion
`Work.Asymptotics.cusp_expansion_of_kernel` (uniform on a compact `K ⊆ 𝒟`, applied to `K = {τ}`)
gives `‖K - Aexp‖ ≤ C(1+t)^M e^{-π(t-T₀)}` on `[1,∞)`, and `Work.LayerCont.TailIntegrable` accepts
the dominator.  (For `τ ∉ 𝒟` the expansion is still expected to hold above the pole heights, but
that statement is not in the library; and `𝒟` is all the continuation argument needs.) -/
theorem TruncAgreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {t₀ A ξ ε : ℝ} (ht₀ : 0 < t₀) (hA : 0 < A) (hξ : 0 < ξ) (hε : 0 < ε)
    (hhi : 1 < t₀ - A)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀ A ξ z → (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ))
    (hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      -ξ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        t₀ - A < (Work.Asymptotics.tauSubOne τ).im ∧ (Work.Asymptotics.tauSubOne τ).im < t₀ + A)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0)
    (hcleanAxis : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      τ ∈ Work.Asymptotics.DomainD →
      Work.Asymptotics.sinSqC r
          * ((∫ t in Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A),
                (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
                    - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
                  * Work.Asymptotics.gaussWeight r t)
              + Work.Asymptotics.detourLeftC ℓ d r t₀ A ξ τ
              - ∫ t in Set.Ioo (t₀ - A) (t₀ + A),
                  Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
                    * Work.Asymptotics.gaussWeight r t)
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ
        = Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r := by
  intro τ r hτ hτre hD
  -- ### local abbreviations
  set I : Set ℝ := Set.Ioo (t₀ - A) (t₀ + A) with hI
  set Kf : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Work.Asymptotics.gaussWeight r t with hKf
  set Af : ℝ → ℂ := fun t => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
      * Work.Asymptotics.gaussWeight r t with hAf
  set Gf : ℝ → ℂ := fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
      * Work.Asymptotics.gaussWeight r t with hGf
  set E : Set ℝ := Set.Ici (1 : ℝ) \ I with hE
  show Work.Asymptotics.sinSqC r * ((∫ t in E, Gf t)
        + Work.Asymptotics.detourLeftC ℓ d r t₀ A ξ τ - ∫ t in I, Af t)
      + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ
      = Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
  have hImeas : MeasurableSet I := measurableSet_Ioo
  have hIci : I ⊆ Set.Ici (1 : ℝ) := fun x hx => le_of_lt (lt_trans hhi hx.1)
  have hEsub : E ⊆ Set.Ici (1 : ℝ) := fun x hx => hx.1
  -- ### the Cauchy–Goursat identity for the detour
  have hres : Work.Asymptotics.detourLeftC ℓ d r t₀ A ξ τ
      = (∫ v in I, Work.Asymptotics.edgeV ℓ d r τ 0 v) - Work.Asymptotics.resCorr r τ :=
    Work.Asymptotics.detourLeftC_eq_interval_sub_residue ℓ d hd ht₀ hε hA hξ
      (by linarith : 0 < t₀ - A) hcl hpole hdeg τ hτ hτre
  -- ### the edge integral on the axis is the contour integral
  have hedge : (∫ v in I, Work.Asymptotics.edgeV ℓ d r τ 0 v) = ∫ v in I, Kf v :=
    MeasureTheory.setIntegral_congr_fun hImeas
      (fun v hv => by
        rw [hKf]
        exact edgeV_zero_eq ℓ d r τ (by linarith [hv.1, hhi]))
  -- ### the `Aexp` factor is continuous, hence integrable on the compact interval
  have hAcont : Continuous Af := by
    rw [hAf]
    unfold Work.Asymptotics.Aexp Work.Asymptotics.gaussWeight
    fun_prop
  have hIntA : IntegrableOn Af I :=
    (hAcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  -- ### the difference is integrable on the tail (cusp expansion on `𝒟`)
  obtain ⟨C₂, M, T₀, hC₂pos, hMnn, hT₀nn, hbnd⟩ :=
    Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd (K := {τ}) isCompact_singleton
      (by rintro x rfl; exact hD)
  have hdom : ∀ t : ℝ, 1 ≤ t →
      ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Work.Asymptotics.gaussWeight r t‖
      ≤ (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
    intro t ht
    have hb := hbnd τ t (Set.mem_singleton τ) ht
    have hexp : Real.exp (-(Real.pi * (t - T₀)))
        = Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * T₀) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [norm_mul, Work.Asymptotics.norm_gaussWeight]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ (C₂ * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
            * Real.exp (-(Real.pi * r ^ 2 * t)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
            * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
          rw [hexp]; ring
  have hdomint : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
      * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))))
      (Set.Ici (1 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => (1 + t) ^ M
        * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) (Set.Ici (1 : ℝ)) :=
      TailIntegrable hMnn (by positivity)
    have h1 : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
        * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) (Set.Ici (1 : ℝ)) :=
      hbase.const_mul (C₂ * Real.exp (Real.pi * T₀))
    refine h1.congr_fun ?_ measurableSet_Ici
    intro t _
    simp only
    rw [show Real.exp (-((Real.pi * (1 + r ^ 2)) * t))
        = Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) by
      rw [← Real.exp_add]; congr 1; ring]
  have hIntG : IntegrableOn Gf (Set.Ici (1 : ℝ)) := by
    rw [hGf]
    show Integrable _ (volume.restrict (Set.Ici (1 : ℝ)))
    refine Integrable.mono' (g := fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
        * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t))))) ?_ ?_ ?_
    · rw [← IntegrableOn]; exact hdomint
    · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
        (by unfold Work.Asymptotics.Aexp; fun_prop)).mul
        (by unfold Work.Asymptotics.gaussWeight; fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht
      exact hdom t ht1
  have hIntGE : IntegrableOn Gf E := hIntG.mono_set hEsub
  have hIntGI : IntegrableOn Gf I := hIntG.mono_set hIci
  -- ### `K = G + A` on `I`, so `K` is integrable there too
  have hIntK : IntegrableOn Kf I :=
    (hIntGI.add hIntA).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring) hImeas
  -- ### the two splits
  have hIntGsub : (∫ t in I, Gf t) = (∫ t in I, Kf t) - (∫ t in I, Af t) := by
    have hsplit : (∫ t in I, Gf t) = ∫ t in I, (Kf t - Af t) := by
      refine MeasureTheory.setIntegral_congr_fun hImeas (fun t _ => ?_)
      simp only [hGf, hKf, hAf]; ring
    rw [hsplit]
    exact MeasureTheory.integral_sub hIntK hIntA
  have hIunion : Set.Ici (1 : ℝ) = E ∪ I := by
    rw [hE]
    exact ((Set.sdiff_union_self (s := Set.Ici (1 : ℝ)) (t := I)).trans
      (Set.union_eq_left.mpr hIci)).symm
  have hsplit : (∫ t in Set.Ici (1 : ℝ), Gf t) = (∫ t in E, Gf t) + (∫ t in I, Gf t) := by
    rw [hIunion, MeasureTheory.setIntegral_union (s := E) (t := I)
      (Set.disjoint_left.mpr (fun x hx hx' => hx.2 hx')) hImeas hIntGE hIntGI]
  -- ### `layerTrunc` unfolded
  have hlayer : Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.Asymptotics.sinSqC r * (∫ t in Set.Ici (1 : ℝ), Gf t) := by
    rw [Work.Asymptotics.layerTrunc, sinSqC_eq_sinSq, hGf]
    simp only [Work.Asymptotics.gaussWeight]
  -- ### the algebra
  rw [hres, hedge, hlayer, hsplit, hIntGsub]
  ring

/-- **`TruncAgreement` in terms of the definitions** `layerTruncCont` / `layerTruncPiece`
(`Submission/Work/LayerCont/TruncDefs.lean`). -/
theorem layerTruncCont_eq_layerTrunc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    {t₀ A ξ ε : ℝ} (ht₀ : 0 < t₀) (hA : 0 < A) (hξ : 0 < ξ) (hε : 0 < ε)
    (hhi : 1 < t₀ - A)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀ A ξ z → (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ))
    (hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      -ξ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        t₀ - A < (Work.Asymptotics.tauSubOne τ).im ∧ (Work.Asymptotics.tauSubOne τ).im < t₀ + A)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0)
    (hcleanAxis : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      τ ∈ Work.Asymptotics.DomainD →
      layerTruncCont ℓ d t₀ A ξ r τ
        = Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r := by
  intro τ r hτ hτre hD
  rw [layerTruncCont, layerTruncPiece]
  exact TruncAgreement ℓ d hd ht₀ hA hξ hε hhi hcl hpole hdeg hcleanAxis τ r hτ hτre hD

end Work.LayerCont
