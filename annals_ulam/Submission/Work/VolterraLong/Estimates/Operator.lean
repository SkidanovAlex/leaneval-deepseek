import Submission.Work.VolterraLong.Op
import Submission.Work.VolterraLong.Estimates.Basic
import Submission.Work.VolterraLong.Estimates.Gain

/-!
# The weighted estimates for the long-interval Volterra operator
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuity/integrability hypotheses are the same throughout; package
them so the statements below stay readable. -/
structure Data {a b : ℝ} (hab : a ≤ b) where
  A : ℝ → E ≃L[ℝ] E
  G : ℝ → E → E
  Θ : ℝ → ℝ → E → E
  Ξ : ℝ → E
  Z₀ : ℝ → E
  hA : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b)
  hG : Continuous (fun p : ℝ × E => G p.1 p.2)
  hΘ : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2)
  hΞ : Continuous Ξ
  hZ₀ : ContinuousOn Z₀ (Set.Icc a b)

variable {a b : ℝ} {hab : a ≤ b}

/-- The operator `longOp` applied to the data of a `Data` structure. -/
def Data.op (D : Data (E := E) hab) :
    BoundedContinuousFunction (Set.Icc a b) E → BoundedContinuousFunction (Set.Icc a b) E :=
  longOp hab D.A D.G D.Θ D.Ξ D.Z₀ D.hA D.hG D.hΘ D.hΞ D.hZ₀

lemma Data.op_apply_fun (D : Data (E := E) hab) (W : BoundedContinuousFunction (Set.Icc a b) E)
    (s : Set.Icc a b) :
    D.op W s = bcfExt hab W (s : ℝ) - (D.A (s:ℝ)).symm
      (D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab W (s:ℝ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) - D.Ξ (s:ℝ)) := by
  show longOp hab D.A D.G D.Θ D.Ξ D.Z₀ D.hA D.hG D.hΘ D.hΞ D.hZ₀ W s = _
  rw [longOp_apply]
  rfl

/-- The two integrands are interval integrable. -/
lemma tan_integrable (D : Data (E := E) hab) (W : BoundedContinuousFunction (Set.Icc a b) E)
    (s : Set.Icc a b) :
    IntervalIntegrable (fun σ : ℝ => D.Θ (s : ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ))
      volume (s : ℝ) b := by
  have hcont : Continuous (fun σ : ℝ => D.Θ (s : ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) :=
    D.hΘ.comp (continuous_const.prodMk (continuous_id.prodMk
      ((zExt_continuous hab D.hZ₀).add (bcfExt_continuous hab W))))
  exact hcont.intervalIntegrable _ _

/-- **Algebraic identity.** The difference of the two operator values is
`A(s)⁻¹` applied to `∫(Θ W - Θ V) - (Q̃ W - Q̃ V)`. -/
lemma Data.op_sub (D : Data (E := E) hab)
    (W V : BoundedContinuousFunction (Set.Icc a b) E) (s : Set.Icc a b) :
    D.op W s - D.op V s =
      (D.A (s : ℝ)).symm
        ((∫ σ in (s : ℝ)..b, (D.Θ (s : ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ) -
              D.Θ (s : ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ))) -
          (qrem D.G (D.A (s : ℝ)) (zExt hab D.Z₀) (s : ℝ) (bcfExt hab W (s : ℝ)) -
            qrem D.G (D.A (s : ℝ)) (zExt hab D.Z₀) (s : ℝ) (bcfExt hab V (s : ℝ)))) := by
  have h1 : D.op W s = bcfExt hab W (s : ℝ) - (D.A (s:ℝ)).symm
      (D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab W (s:ℝ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) - D.Ξ (s:ℝ)) :=
    D.op_apply_fun W s
  have h2 : D.op V s = bcfExt hab V (s : ℝ) - (D.A (s:ℝ)).symm
      (D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab V (s:ℝ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ)) - D.Ξ (s:ℝ)) :=
    D.op_apply_fun V s
  rw [h1, h2, intervalIntegral.integral_sub (tan_integrable D W s) (tan_integrable D V s)]
  have halg : ∀ u w X Y : E,
      (X - (D.A (s:ℝ)).symm u) - (Y - (D.A (s:ℝ)).symm w) =
        (D.A (s:ℝ)).symm ((D.A (s:ℝ)) (X - Y) - (u - w)) := by
    intro u w X Y
    simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply]
    abel
  rw [halg]
  have huw : (D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab W (s:ℝ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) - D.Ξ (s:ℝ)) -
      (D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab V (s:ℝ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ)) - D.Ξ (s:ℝ)) =
      (D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab W (s:ℝ)) -
        D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab V (s:ℝ))) -
      ((∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ))) := by
    abel
  rw [huw]
  have hinner : (D.A (s:ℝ)) (bcfExt hab W (s:ℝ) - bcfExt hab V (s:ℝ)) -
      ((D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab W (s:ℝ)) -
        D.G (s:ℝ) (zExt hab D.Z₀ (s:ℝ) + bcfExt hab V (s:ℝ))) -
       ((∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ)))) =
      ((∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) -
        (∫ σ in (s:ℝ)..b, D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ))) -
      (qrem D.G (D.A (s:ℝ)) (zExt hab D.Z₀) (s:ℝ) (bcfExt hab W (s:ℝ)) -
        qrem D.G (D.A (s:ℝ)) (zExt hab D.Z₀) (s:ℝ) (bcfExt hab V (s:ℝ))) := by
    simp only [map_sub, qrem]
    abel
  rw [hinner]

/-- `zExt` may be replaced by the original function inside `defect`. -/
lemma defect_zExt_eq {a b : ℝ} (hab : a ≤ b) (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E)
    (Ξ : ℝ → E) (Z₀ : ℝ → E) {s : ℝ} (hs : s ∈ Set.Icc a b) :
    defect G Θ Ξ (zExt hab Z₀) b s = defect G Θ Ξ Z₀ b s := by
  rw [defect, defect, zExt_of_mem hab hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [Set.uIcc_of_le hs.2] at hσ
  show Θ s σ (zExt hab Z₀ σ) = Θ s σ (Z₀ σ)
  rw [zExt_of_mem hab (Z := Z₀) ⟨le_trans hs.1 hσ.1, hσ.2⟩]

/-- The extension of the zero function is zero. -/
lemma bcfExt_zero {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    bcfExt hab (0 : BoundedContinuousFunction (Set.Icc a b) E) x = 0 := by
  rw [bcfExt, Set.IccExtend_apply]
  rfl

/-- At `W = 0` the operator value is `A(s)⁻¹` applied to the defect. -/
lemma Data.op_zero_apply (D : Data (E := E) hab) (s : Set.Icc a b) :
    D.op 0 s = (D.A (s:ℝ)).symm (defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ)) := by
  rw [D.op_apply_fun 0 s]
  simp only [bcfExt_zero, zero_add]
  rw [defect]
  simp only [map_sub, map_add, map_neg, map_zero, zero_sub]
  abel

/-- The weighted Lipschitz estimate for the long-interval Volterra operator. -/
theorem wdist_longOp_le (D : Data (E := E) hab) {lam L Cg B ε R : ℝ}
    (hlam : 0 < lam) (hL : 0 ≤ L) (hCg : 0 ≤ Cg) (hε : 0 ≤ ε) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hAb : ∀ s ∈ Set.Icc a b, ‖((D.A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (D.Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (D.Z₀ σ) 1, ‖D.Θ s σ z - D.Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (D.Z₀ s) 1,
      DifferentiableAt ℝ (fun w => D.G s w) z)
    (hderiv : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (D.Z₀ s) 1,
      ‖fderiv ℝ (fun w => D.G s w) z - (D.A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - D.Z₀ s‖ + ε)
    {W V : BoundedContinuousFunction (Set.Icc a b) E}
    (hW : ∀ s : Set.Icc a b, ‖W s‖ ≤ R) (hV : ∀ s : Set.Icc a b, ‖V s‖ ≤ R) :
    wdist lam (D.op W) (D.op V) ≤ B * (L / lam + (Cg * R + ε)) * wdist lam W V := by
  refine (wdist_le_iff hab (le_of_lt hlam) _ _).mpr (fun s => ?_)
  -- the integrand and its bound
  have hmemW : ∀ σ : Set.Icc a b, zExt hab D.Z₀ (σ:ℝ) + bcfExt hab W (σ:ℝ) ∈
      Metric.closedBall (D.Z₀ σ) 1 := by
    intro σ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : zExt hab D.Z₀ (σ:ℝ) + bcfExt hab W (σ:ℝ) - D.Z₀ σ = bcfExt hab W (σ:ℝ) := by
      rw [zExt_of_mem hab (Z := D.Z₀) σ.2]; abel
    rw [h1, bcfExt_apply]
    linarith [hW σ]
  have hmemV : ∀ σ : Set.Icc a b, zExt hab D.Z₀ (σ:ℝ) + bcfExt hab V (σ:ℝ) ∈
      Metric.closedBall (D.Z₀ σ) 1 := by
    intro σ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : zExt hab D.Z₀ (σ:ℝ) + bcfExt hab V (σ:ℝ) - D.Z₀ σ = bcfExt hab V (σ:ℝ) := by
      rw [zExt_of_mem hab (Z := D.Z₀) σ.2]; abel
    rw [h1, bcfExt_apply]
    linarith [hV σ]
  have hGlip : ∀ σ : Set.Icc a b,
      ‖D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ) -
        D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ)‖ ≤ L * ‖W σ - V σ‖ := by
    intro σ
    have h := hΘ_lip (s:ℝ) s.2 (σ:ℝ) σ.2 _ (hmemW σ) _ (hmemV σ)
    have hsub : (zExt hab D.Z₀ (σ:ℝ) + bcfExt hab W (σ:ℝ)) -
        (zExt hab D.Z₀ (σ:ℝ) + bcfExt hab V (σ:ℝ)) = W σ - V σ := by
      rw [bcfExt_apply, bcfExt_apply]
      abel
    rwa [hsub] at h
  have hGint : IntervalIntegrable (fun σ : ℝ => D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ) -
      D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ)) volume a b := by
    apply Continuous.intervalIntegrable
    have h1 : Continuous (fun σ : ℝ => D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ)) :=
      D.hΘ.comp (continuous_const.prodMk (continuous_id.prodMk
        ((zExt_continuous hab D.hZ₀).add (bcfExt_continuous hab W))))
    have h2 : Continuous (fun σ : ℝ => D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ)) :=
      D.hΘ.comp (continuous_const.prodMk (continuous_id.prodMk
        ((zExt_continuous hab D.hZ₀).add (bcfExt_continuous hab V))))
    exact h1.sub h2
  have hgain := weighted_integral_le hab hlam hL W V (G := fun σ : ℝ =>
      D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ) -
        D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ)) hGlip hGint s
  -- the Taylor remainder bound
  have hqball : Metric.closedBall (zExt hab D.Z₀ (s:ℝ)) 1 = Metric.closedBall (D.Z₀ s) 1 := by
    rw [zExt_of_mem hab (Z := D.Z₀) s.2]
  have hq := qrem_lipschitz (D.A (s:ℝ)) (zExt hab D.Z₀) (s:ℝ) hCg hε hR hR1
    (fun z hz => hdiff (s:ℝ) s.2 z (by rwa [hqball] at hz))
    (fun z hz => by
      have h := hderiv (s:ℝ) s.2 z (by rwa [hqball] at hz)
      simpa [zExt_of_mem hab (Z := D.Z₀) s.2] using h)
    (bcfExt hab W (s:ℝ)) (bcfExt hab V (s:ℝ))
    (by rw [bcfExt_apply]; exact hW s) (by rw [bcfExt_apply]; exact hV s)
  have hq' : ‖qrem D.G (D.A (s:ℝ)) (zExt hab D.Z₀) (s:ℝ) (bcfExt hab W (s:ℝ)) -
      qrem D.G (D.A (s:ℝ)) (zExt hab D.Z₀) (s:ℝ) (bcfExt hab V (s:ℝ))‖ ≤
      (Cg * R + ε) * ‖W s - V s‖ := by
    have hsub : bcfExt hab W (s:ℝ) - bcfExt hab V (s:ℝ) = W s - V s := by
      rw [bcfExt_apply, bcfExt_apply]
    rwa [hsub] at hq
  -- assemble
  rw [Data.op_sub D W V s]
  set X : E := (∫ σ in (s:ℝ)..b, (D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab W σ) -
        D.Θ (s:ℝ) σ (zExt hab D.Z₀ σ + bcfExt hab V σ))) -
      (qrem D.G (D.A (s:ℝ)) (zExt hab D.Z₀) (s:ℝ) (bcfExt hab W (s:ℝ)) -
        qrem D.G (D.A (s:ℝ)) (zExt hab D.Z₀) (s:ℝ) (bcfExt hab V (s:ℝ))) with hX
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hAb (s:ℝ) s.2)
  have h2 : ‖X‖ ≤ (L / lam) * wdist lam W V * Real.exp (lam * (b - (s:ℝ))) +
      (Cg * R + ε) * ‖W s - V s‖ := by
    rw [hX]
    exact le_trans (norm_sub_le _ _) (add_le_add hgain hq')
  have hfinal : ‖(D.A (s:ℝ)).symm X‖ * Real.exp (-(lam * (b - (s:ℝ)))) ≤
      B * (L / lam + (Cg * R + ε)) * wdist lam W V := by
    have h1 : ‖(D.A (s:ℝ)).symm X‖ ≤ B * ‖X‖ :=
      le_trans (ContinuousLinearMap.le_opNorm ((D.A (s:ℝ)).symm : E →L[ℝ] E) X)
        (mul_le_mul_of_nonneg_right (hAb (s:ℝ) s.2) (norm_nonneg X))
    have hexp : Real.exp (-(lam * (b - (s:ℝ)))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg hlam.le (sub_nonneg.mpr s.2.2))
    have hws : ‖W s - V s‖ * Real.exp (-(lam * (b - (s:ℝ)))) ≤ wdist lam W V :=
      le_wdist (le_of_lt hlam) W V s
    have h1e : Real.exp (lam * (b - (s:ℝ))) * Real.exp (-(lam * (b - (s:ℝ)))) = 1 := by
      rw [← Real.exp_add]; simp
    have hLnn : 0 ≤ L / lam := div_nonneg hL hlam.le
    have hCGnn : 0 ≤ Cg * R + ε := by nlinarith
    have hwnn : 0 ≤ wdist lam W V := wdist_nonneg W V
    have hkey : ((L / lam) * wdist lam W V * Real.exp (lam * (b - (s:ℝ))) +
        (Cg * R + ε) * ‖W s - V s‖) * Real.exp (-(lam * (b - (s:ℝ)))) ≤
        (L / lam + (Cg * R + ε)) * wdist lam W V := by
      have h3 : (L / lam) * wdist lam W V * Real.exp (lam * (b - (s:ℝ))) *
          Real.exp (-(lam * (b - (s:ℝ)))) = (L / lam) * wdist lam W V := by
        rw [mul_assoc, h1e, mul_one]
      have h4 : (Cg * R + ε) * ‖W s - V s‖ * Real.exp (-(lam * (b - (s:ℝ)))) ≤
          (Cg * R + ε) * wdist lam W V := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hws hCGnn
      have hexpand : ((L / lam) * wdist lam W V * Real.exp (lam * (b - (s:ℝ))) +
          (Cg * R + ε) * ‖W s - V s‖) * Real.exp (-(lam * (b - (s:ℝ)))) =
          (L / lam) * wdist lam W V * Real.exp (lam * (b - (s:ℝ))) *
            Real.exp (-(lam * (b - (s:ℝ)))) +
          (Cg * R + ε) * ‖W s - V s‖ * Real.exp (-(lam * (b - (s:ℝ)))) := by
        ring
      rw [hexpand, h3]
      linarith [h4]
    calc ‖(D.A (s:ℝ)).symm X‖ * Real.exp (-(lam * (b - (s:ℝ))))
        ≤ (B * ((L / lam) * wdist lam W V * Real.exp (lam * (b - (s:ℝ))) +
            (Cg * R + ε) * ‖W s - V s‖)) * Real.exp (-(lam * (b - (s:ℝ)))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hBnn)
      _ = B * (((L / lam) * wdist lam W V * Real.exp (lam * (b - (s:ℝ))) +
            (Cg * R + ε) * ‖W s - V s‖) * Real.exp (-(lam * (b - (s:ℝ))))) := by ring
      _ ≤ B * ((L / lam + (Cg * R + ε)) * wdist lam W V) :=
          mul_le_mul_of_nonneg_left hkey hBnn
      _ = B * (L / lam + (Cg * R + ε)) * wdist lam W V := by ring
  exact hfinal

/-- The weighted norm of the operator at `W = 0` is bounded by the defect
estimate `B (2 + (b-a)) ε`. -/
theorem wdist_longOp_zero_le (D : Data (E := E) hab)
    {G0 : ℝ → E → E} {Θ0 : ℝ → ℝ → E → E} {Ξ0 : ℝ → E} {lam B ε : ℝ}
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (hAb : ∀ s ∈ Set.Icc a b, ‖((D.A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (D.Z₀ s) = (∫ σ in s..b, Θ0 s σ (D.Z₀ σ)) + Ξ0 s)
    (hG_close : ∀ s ∈ Set.Icc a b, dist (D.G s (D.Z₀ s)) (G0 s (D.Z₀ s)) < ε)
    (hΘ_close : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
      dist (D.Θ s σ (D.Z₀ σ)) (Θ0 s σ (D.Z₀ σ)) < ε)
    (hΞ_close : ∀ s ∈ Set.Icc a b, dist (D.Ξ s) (Ξ0 s) < ε) :
    wdist lam (D.op 0) 0 ≤ B * (2 + (b - a)) * ε := by
  have h0 : ∀ s : Set.Icc a b,
      (0 : BoundedContinuousFunction (Set.Icc a b) E) s = 0 := fun _ => rfl
  refine (wdist_le_iff hab hlam _ _).mpr (fun s => ?_)
  rw [Data.op_zero_apply D s, h0 s, sub_zero]
  have hdef : ‖defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ)‖ ≤ (2 + (b - a)) * ε := by
    rw [defect_zExt_eq hab D.G D.Θ D.Ξ D.Z₀ s.2]
    exact norm_defect_le hab hε D.hZ₀ D.hΘ hΘ0_cont hbase hG_close hΘ_close hΞ_close (s:ℝ) s.2
  have hBnn : 0 ≤ B := le_trans (norm_nonneg ((D.A (s:ℝ)).symm : E →L[ℝ] E)) (hAb (s:ℝ) s.2)
  have hCGnn : 0 ≤ (2 + (b - a)) * ε := by
    have h1 : 0 ≤ b - (s:ℝ) := sub_nonneg.mpr s.2.2
    nlinarith
  have hexp : Real.exp (-(lam * (b - (s:ℝ)))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hlam (sub_nonneg.mpr s.2.2))
  have h1 : ‖((D.A (s:ℝ)).symm : E →L[ℝ] E) (defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ))‖ ≤
      B * ‖defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ)‖ :=
    le_trans (ContinuousLinearMap.le_opNorm ((D.A (s:ℝ)).symm : E →L[ℝ] E) _)
      (mul_le_mul_of_nonneg_right (hAb (s:ℝ) s.2) (norm_nonneg _))
  calc ‖((D.A (s:ℝ)).symm : E →L[ℝ] E) (defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ))‖ *
        Real.exp (-(lam * (b - (s:ℝ))))
      ≤ (B * ‖defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ)‖) *
          Real.exp (-(lam * (b - (s:ℝ)))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = B * (‖defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ)‖ *
          Real.exp (-(lam * (b - (s:ℝ))))) := by ring
    _ ≤ B * ((2 + (b - a)) * ε) := by
        apply mul_le_mul_of_nonneg_left _ hBnn
        calc ‖defect D.G D.Θ D.Ξ (zExt hab D.Z₀) b (s:ℝ)‖ * Real.exp (-(lam * (b - (s:ℝ))))
            ≤ ((2 + (b - a)) * ε) * Real.exp (-(lam * (b - (s:ℝ)))) :=
              mul_le_mul_of_nonneg_right hdef (Real.exp_pos _).le
          _ ≤ ((2 + (b - a)) * ε) * 1 := mul_le_mul_of_nonneg_left hexp hCGnn
          _ = (2 + (b - a)) * ε := mul_one _
    _ = B * (2 + (b - a)) * ε := by ring

end Work.VolterraLong
