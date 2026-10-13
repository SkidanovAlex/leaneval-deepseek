import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.pth_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` identities -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

/-- `x ^ ((2 - γ)/2) * x ^ ((γ - 2)/2) = 1` for `x > 0`. -/
private lemma rpow_half_mul_half (x γ : ℝ) (hx : 0 < x) :
    x ^ ((2 - γ) / 2) * x ^ ((γ - 2) / 2) = 1 := by
  rw [← Real.rpow_add hx, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero]

/-! ## The core Hardy inequality on the angular interval -/

/-- If `h` is continuous on `[0,θ] ⊆ [0,π/2]` and `h(s)² sin(2s)^{2-γ}` is integrable on
`[0,π/2]`, then `(∫₀^θ h)² ≤ (∫_Iθ h² sin(2s)^{2-γ}) · 100/(γ-1)`.

This is the Cauchy–Schwarz / Hardy step: split `h = (h sin^{(2-γ)/2}) · sin^{(γ-2)/2}`,
square the Hölder inequality and control the singular weight by `sin_two_rpow`. -/
private theorem core (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ π / 2)
    (hcont : ContinuousOn h (Set.Icc 0 θ))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) Iθ) :
    (∫ s in (0 : ℝ)..θ, h s) ^ 2 ≤
      (∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) * (100 / (gam α - 1)) := by
  have hγ1 : 1 < gam α := one_lt_gam hα
  have hγ2 : gam α ≤ 11 / 10 := by rw [gam]; linarith
  have hp1 : -1 < gam α - 2 := by linarith
  have hp0 : gam α - 2 ≤ 0 := by linarith
  -- positivity of sin(2·) on (0,θ), nonnegativity on Iθ
  have hsinpos : ∀ s ∈ Set.Ioo (0 : ℝ) θ, 0 < Real.sin (2 * s) := by
    intro s hs
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) ?_
    linarith [hs.2, hθ1, Real.pi_pos]
  have hsinIθ : ∀ x ∈ Iθ, 0 ≤ Real.sin (2 * x) := by
    intro x hx
    have h1 : 0 ≤ 2 * x := by linarith [hx.1]
    have h2 : 2 * x ≤ Real.pi := by linarith [hx.2, Real.pi_pos]
    exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  have hsub : Set.Ioo (0 : ℝ) θ ⊆ Iθ := by
    intro x hx
    simp only [Iθ, Set.mem_Icc]
    exact ⟨le_of_lt hx.1, le_trans hx.2.le hθ1⟩
  have hae_sub : Set.Ioo (0 : ℝ) θ ≤ᵐ[volume] Iθ :=
    Filter.Eventually.of_forall (fun x hx => hsub hx)
  have hmIθ : MeasurableSet Iθ := by
    simp only [Iθ]
    exact measurableSet_Icc
  have hFnn : 0 ≤ᵐ[volume.restrict Iθ]
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hSnn : 0 ≤ᵐ[volume.restrict Iθ] (fun s => (Real.sin (2 * s)) ^ (gam α - 2)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (hsinIθ x hx) _)
  -- integrability of the integrand over (0,θ)
  have hIntF : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) (Set.Ioo (0 : ℝ) θ) :=
    hint.mono_set hsub
  -- measurability of the two Cauchy–Schwarz factors
  have hcont_sin : ContinuousOn (fun s : ℝ => Real.sin (2 * s)) (Set.Ioo (0 : ℝ) θ) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hsm_h : AEMeasurable h (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (hcont.mono Set.Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo
  have hsm_s : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  have hsm_s2 : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((gam α - 2) / 2))
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  -- the integrability of the two squares
  have eq_v2 : Set.EqOn
      (fun x => ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2)
      (fun x => (Real.sin (2 * x)) ^ (gam α - 2)) (Set.Ioo (0 : ℝ) θ) := by
    intro x hx
    dsimp only
    rw [rpow_sq _ _ (hsinpos x hx), show 2 * ((gam α - 2) / 2) = gam α - 2 by ring]
  have eq_u2 : Set.EqOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2)
      (fun x => (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α)) (Set.Ioo (0 : ℝ) θ) := by
    intro x hx
    dsimp only
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx), show 2 * ((2 - gam α) / 2) = 2 - gam α by ring]
  have hInt_v2 : MeasureTheory.IntegrableOn
      (fun x => ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2) (Set.Ioo (0 : ℝ) θ) :=
    ((sin_two_rpow (gam α - 2) hp1 hp0).1.mono_set hsub).congr_fun eq_v2.symm
      measurableSet_Ioo
  have hInt_u2 : MeasureTheory.IntegrableOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2) (Set.Ioo (0 : ℝ) θ) :=
    hIntF.congr_fun eq_u2.symm measurableSet_Ioo
  have hu_mem : MeasureTheory.MemLp
      (fun x => h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) 2
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hsm_h.mul hsm_s).aestronglyMeasurable).2 hInt_u2
  have hv_mem : MeasureTheory.MemLp (fun x => (Real.sin (2 * x)) ^ ((gam α - 2) / 2)) 2
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hsm_s2.aestronglyMeasurable).2 hInt_v2
  have hcs := cs_integral hu_mem hv_mem
  -- identify the three integrals
  have e1 : (∫ x in Set.Ioo (0 : ℝ) θ,
        (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) * (Real.sin (2 * x)) ^ ((gam α - 2) / 2))
      = ∫ x in Set.Ioo (0 : ℝ) θ, h x := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_assoc, rpow_half_mul_half _ _ (hsinpos x hx), mul_one]
  have e2 : (∫ x in Set.Ioo (0 : ℝ) θ,
        (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx), show 2 * ((2 - gam α) / 2) = 2 - gam α by ring]
  have e3 : (∫ x in Set.Ioo (0 : ℝ) θ, ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [rpow_sq _ _ (hsinpos x hx), show 2 * ((gam α - 2) / 2) = gam α - 2 by ring]
  have key : (∫ x in Set.Ioo (0 : ℝ) θ, h x) ^ 2 ≤
      (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
        * (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2)) := by
    calc (∫ x in Set.Ioo (0 : ℝ) θ, h x) ^ 2
        = (∫ x in Set.Ioo (0 : ℝ) θ,
            (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2))
              * (Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2 := by rw [e1]
      _ ≤ (∫ x in Set.Ioo (0 : ℝ) θ, (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2)
            * (∫ x in Set.Ioo (0 : ℝ) θ,
                ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2) := hcs
      _ = (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
            * (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2)) := by rw [e2, e3]
  -- the monotonicity and the explicit bound for the weight
  have hA : (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
      ≤ ∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) :=
    MeasureTheory.setIntegral_mono_set hint hFnn hae_sub
  have hB : (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2))
      ≤ 100 / (gam α - 1) := by
    have h1 : (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2))
        ≤ ∫ s in Iθ, (Real.sin (2 * s)) ^ (gam α - 2) :=
      MeasureTheory.setIntegral_mono_set (sin_two_rpow (gam α - 2) hp1 hp0).1 hSnn hae_sub
    have h2 : (∫ s in Iθ, (Real.sin (2 * s)) ^ (gam α - 2))
        ≤ 100 / ((gam α - 2) + 1) := (sin_two_rpow (gam α - 2) hp1 hp0).2
    have h3 : 100 / ((gam α - 2) + 1) = 100 / (gam α - 1) := by ring_nf
    exact h1.trans (h2.trans (le_of_eq h3))
  have hA0 : 0 ≤ ∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) :=
    MeasureTheory.setIntegral_nonneg hmIθ
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hB0 : 0 ≤ ∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => Real.rpow_nonneg (hsinIθ x (hsub hx)) _)
  have hIoo : (∫ x in Set.Ioo (0 : ℝ) θ, h x) = ∫ s in (0 : ℝ)..θ, h s := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθ0]
  calc (∫ s in (0 : ℝ)..θ, h s) ^ 2
      = (∫ x in Set.Ioo (0 : ℝ) θ, h x) ^ 2 := by rw [hIoo]
    _ ≤ (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
          * (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2)) := key
    _ ≤ (∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) * (100 / (gam α - 1)) :=
        mul_le_mul hA hB hB0 hA0


theorem HardyTheta (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hz : 0 ≤ z) (h0 : g z 0 = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (g z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ s in Work.Spaces.Iθ,
        (Work.Spaces.pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
  intro θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hpth := pth_integral g z hsm hz θ ⟨hθ0, hθ1⟩
  have hFTC : (∫ s in (0 : ℝ)..θ, pth g z s) = g z θ := by
    rw [hpth.1, h0, sub_zero]
  have hmain := core α hα hα1 (fun s => pth g z s) θ hθ0 hθ1 hpth.2 hint
  rw [hFTC] at hmain
  calc (g z θ) ^ 2
      ≤ (∫ s in Iθ, (pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α))
          * (100 / (gam α - 1)) := hmain
    _ = (100 / (gam α - 1)) * ∫ s in Iθ,
          (pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) := by ring

end Work.Spaces
