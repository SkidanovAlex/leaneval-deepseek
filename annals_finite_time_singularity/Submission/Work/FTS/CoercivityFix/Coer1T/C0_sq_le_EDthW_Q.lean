/-
# `(C₀ f)² ≤ EDthW f` in the interior class `SmoothQuad` (`Coer1T`)

This is the **interior-class port** of `Work.Coercivity.C0_sq_le_EDthW`: the same bound

  `(C₀ f)² = (L₁₂(Transport f)(0))² ≤ EDthW f = ∫∫ (D_θ f)² w² dz dθ`

but with the analytic-class hypothesis `Work.Spaces.SmoothNbhd f` — which in this Mathlib is
`ContDiffOn ℝ ⊤`, i.e. *analyticity* on a neighbourhood of the closed quadrant, and is therefore
destroyed by every cut-off — replaced by the genuine `C^∞`-on-the-open-quadrant class
`Work.FTS.LocData.SmoothQuad` of the localisation chapter.

The proof is the one of `Work.Coercivity.C0_sq_le_EDthW`:

* `C₀ f` is the `L²`-pairing of the vector `u = D_θ f · w` with the fixed kernel
  `v = 3 K(θ) z/(1+z)³`, whose `L²`-norm is at most `1`;
* Cauchy–Schwarz gives `(C₀ f)² ≤ (∫ u²)(∫ v²) ≤ EDthW f · 1`.

The *only* place where the smoothness hypothesis enters that proof is the almost-everywhere
strong measurability of `u` over the product of the two restricted measures; `SmoothNbhd` gave it
through a continuous-on-a-neighbourhood argument, whereas `SmoothQuad` gives it through
continuity on the *open* quadrant alone (`continuousOn_dth_mul_w_Q`, `aesm_dth_mul_w_Q` below),
which is all `Spaces.aesm_of_continuousOn_Qd` needs.  Everything else is hypothesis-free.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.zAux
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Measurability of `D_θ f · w` for `SmoothQuad` data

`D_θ` preserves genuine `C^∞`-smoothness on the open quadrant
(`Work.FTS.LocData.contDiffOn_Dth`), and on the open quadrant the weight `w` is continuous with
no singularity, so `D_θ f · w` is continuous there; the quadrant is a.e. all of `Iz ×ˢ Iθ`. -/

/-- `(z,θ) ↦ D_θ f z θ · w(z)` is continuous on the open quadrant for `SmoothQuad` data. -/
theorem continuousOn_dth_mul_w_Q {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hD : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_Dth (isOpen_Ioi.prod isOpen_Ioo) hsm
  have hmono : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hD.continuousOn.mono
      (fun p hp => ⟨Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0) hp.1, hp.2⟩)
  exact hmono.mul Work.Coercivity.continuousOn_w_quad

/-- A.e. strong measurability of `D_θ f · w` with respect to the product of the restrictions of
Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`, for `SmoothQuad` data. -/
theorem aesm_dth_mul_w_Q {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_dth_mul_w_Q hsm)

/-! ## The bound -/

/-- `L₁₂(Transport f)(0)` is a linear functional of `D_θ f · w` whose kernel
`3 K(θ) z/(1+z)³` has `L²`-norm at most `1`; hence `(C₀ f)² ≤ EDthW f`, in the interior class
`SmoothQuad`. -/
theorem C0_sq_le_EDthW_Q {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set u : ℝ × ℝ → ℝ := fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hu
  set v : ℝ × ℝ → ℝ := fun p => 3 * Work.Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 with hv
  have hu2 : Integrable (fun p : ℝ × ℝ => u p ^ 2) P := by
    have h := Work.Coercivity.integrableOn_prod
      (g := fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
      * Work.Spaces.w z ^ 2) hint
    exact h.congr (Eventually.of_forall fun p => by simp only [hu]; ring)
  have hv2 : Integrable (fun p : ℝ × ℝ => v p ^ 2) P := by
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    have hmul : Integrable (fun p : ℝ × ℝ =>
        (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Work.Spaces.K p.2) ^ 2)) P :=
      hran.mul_prod Work.Coercivity.integrableOn_Kθ_sq
    refine hmul.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
    simp only [hv]
    field_simp
    ring
  have huA : MemLp u 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hu2
    rw [hu, hP]
    exact aesm_dth_mul_w_Q hsq
  have hvA : MemLp v 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hv2
    rw [hv]
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.K]
    fun_prop
  have hC0id : Work.Coercivity.C0 f = ∫ p, u p * v p ∂P := by
    have hdef : Work.Coercivity.C0 f = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s := by
      simp only [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
        Work.Spaces.Iθ]
    rw [hdef]
    have h1 : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, u (s, θ) * v (s, θ) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hu, hv, Work.Coercivity.Transport, Work.Spaces.w]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hs1 : 1 + s ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < s from hs])
      field_simp
    rw [h1]
    rw [MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * v p)
      (huA.integrable_mul hvA)).symm
  have hunorm : ∫ p, u p ^ 2 ∂P = Work.Coercivity.EDthW f := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p ^ 2) hu2]
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hu]; ring
  have hsep : ∫ p, v p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6))
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := by
    have hcongr : (fun p : ℝ × ℝ => v p ^ 2)
        =ᵐ[P] fun p : ℝ × ℝ => (9 * (p.1 ^ 2 / (1 + p.1) ^ 6))
          * ((Work.Spaces.K p.2) ^ 2) := by
      filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
      have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
      simp only [hv]; field_simp; ring
    rw [MeasureTheory.integral_congr_ae hcongr]
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    exact Work.Coercivity.integral_prod_sep _ _
      hran Work.Coercivity.integrableOn_Kθ_sq
  have hvnorm : ∫ p, v p ^ 2 ∂P ≤ 1 := by
    rw [hsep]
    have h1 : (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6)) = 3 / 10 := by
      rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Iz_zsq_div_six]
      norm_num
    have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) ≤ 9 / 4 :=
      Work.Coercivity.integral_Iθ_Ksq_le
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    rw [h1]
    nlinarith [h2, hnn]
  calc (Work.Coercivity.C0 f) ^ 2 = (∫ p, u p * v p ∂P) ^ 2 := by rw [hC0id]
    _ ≤ (∫ p, u p ^ 2 ∂P) * (∫ p, v p ^ 2 ∂P) :=
        Work.Coercivity.cs_integral_mul huA hvA
    _ ≤ Work.Coercivity.EDthW f * 1 := by
        rw [hunorm]
        exact mul_le_mul_of_nonneg_left hvnorm
          (by rw [← hunorm]; exact integral_nonneg fun p => sq_nonneg _)
    _ = Work.Coercivity.EDthW f := mul_one _

end Work.FTS.CoercivityFix.Coer1T
