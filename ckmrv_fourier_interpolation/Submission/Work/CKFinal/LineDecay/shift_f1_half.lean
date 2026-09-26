import Mathlib
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.CKFinal.LineDecay.F1Half.Basic
import Submission.Work.CKFinal.LineDecay.Kfun_bound_shift

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

set_option maxHeartbeats 1600000

/-- `‖e^{iπr²x}‖ = 1` for real `x`. -/
theorem norm_kerExp_ofReal (r x : ℝ) : ‖Work.Asymptotics.kerExp r (x : ℂ)‖ = 1 := by
  rw [Work.Asymptotics.kerExp,
    show (Real.pi : ℂ) * Complex.I * (r : ℂ) ^ 2 * (x : ℂ)
      = (((Real.pi * r ^ 2 * x : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The pointwise bound on the shifted integrand along a horizontal line in the half-strip. -/
theorem norm_f1fun_horizontal_le (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) {C N : ℝ}
    (hbound : ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R)) :
    ∀ x R : ℝ, 0 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      ‖f1fun ℓ d τ r ((x : ℂ) + (R : ℂ) * Complex.I)‖
        ≤ C * (1 + R) ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * R) := by
  intro x R hx0 hx1 hR
  have hK := hbound (x - 1) R (by linarith) (by linarith) hR
  have harg : ((x - 1 : ℝ) : ℂ) + (R : ℂ) * Complex.I
      = ((x : ℂ) + (R : ℂ) * Complex.I) - 1 := by push_cast; ring
  rw [harg] at hK
  have hker : ‖Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)‖
      = Real.exp (-(Real.pi * r ^ 2 * R)) := by
    rw [kerExp_decomp r x R, norm_mul, norm_kerExp_ofReal, one_mul,
      Work.Asymptotics.norm_gaussWeight]
  rw [f1fun, norm_mul, hker]
  calc ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (((x : ℂ) + (R : ℂ) * Complex.I) - 1))‖
        * Real.exp (-(Real.pi * r ^ 2 * R))
      ≤ (C * (1 + R) ^ N * Real.exp (2 * Real.pi * R)) * Real.exp (-(Real.pi * r ^ 2 * R)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ = C * (1 + R) ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * R) := by
        rw [mul_assoc (C * (1 + R) ^ N) (Real.exp (2 * Real.pi * R))
              (Real.exp (-(Real.pi * r ^ 2 * R))), ← Real.exp_add]
        congr 1
        ring

/-- The top edge `∫_0^1 f₁(x + iR) dx` of the shift rectangle tends to `0`. -/
theorem tendsto_topEdge_f1fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) {C N : ℝ}
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hr : 2 < r ^ 2)
    (hbound : ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R)) :
    Filter.Tendsto
      (fun R : ℝ => ∫ x in (0 : ℝ)..1, f1fun ℓ d τ r ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  set c : ℝ := Real.pi * (r ^ 2 - 2) with hc
  have hcpos : 0 < c := by rw [hc]; nlinarith [Real.pi_pos]
  have hpt := norm_f1fun_horizontal_le ℓ d hd τ r him hbound
  have hbase : Filter.Tendsto
      (fun R : ℝ => (1 + R) ^ N * Real.exp (-c * (1 + R))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero N c hcpos).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have hB : Filter.Tendsto (fun R : ℝ => C * (1 + R) ^ N * Real.exp (-c * R))
      Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto
        (fun R : ℝ => (C * Real.exp c) * ((1 + R) ^ N * Real.exp (-c * (1 + R))))
        Filter.atTop (nhds 0) := by
      simpa using hbase.const_mul (C * Real.exp c)
    refine h2.congr' ?_
    filter_upwards with R
    rw [show C * Real.exp c * ((1 + R) ^ N * Real.exp (-c * (1 + R)))
        = C * (1 + R) ^ N * (Real.exp c * Real.exp (-c * (1 + R))) by ring,
      ← Real.exp_add]
    congr 2
    ring
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (g := fun R : ℝ => C * (1 + R) ^ N * Real.exp (-c * R)) ?_ ?_ hB
  · filter_upwards with R
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (τ.im + 1)] with R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C * (1 + R) ^ N * Real.exp (-c * R))
      (f := fun x : ℝ => f1fun ℓ d τ r ((x : ℂ) + (R : ℂ) * Complex.I))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        have hh := hpt x R (le_of_lt hx.1) hx.2 hR
        rw [hc]
        exact hh)
    simpa using h

/-- Integrability of the ray integrands `y ↦ f₁(a + iy)`, `a ∈ {0,1}`, on `(1,∞)`. -/
theorem integrableOn_f1fun_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) {C N : ℝ}
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hr : 2 < r ^ 2)
    (hbound : ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R))
    (a : ℝ) (ha : a = 0 ∨ a = 1) :
    IntegrableOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi 1) := by
  set M : ℝ := τ.im + 1 with hM
  have hM13 : 13 ≤ M := by rw [hM]; linarith
  have hM1 : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hc : 0 < Real.pi * (r ^ 2 - 2) := by nlinarith [Real.pi_pos]
  -- the ray avoids the pole
  have hmem : ∀ y : ℝ, 1 ≤ y →
      ((a : ℂ) + (y : ℂ) * Complex.I)
        ∈ ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im} \ {(τ : ℂ)}) := by
    intro y hy
    have h1 : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by simp
    have h2 : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [h1]; rcases ha with h | h <;> rw [h] <;> norm_num
    · rw [h1]; rcases ha with h | h <;> rw [h] <;> norm_num
    · rw [h2]; exact hy
    · intro hτ
      have h' := congrArg Complex.re hτ
      rw [h1, UpperHalfPlane.coe_re, hre] at h'
      rcases ha with h | h <;> rw [h] at h' <;> norm_num at h'
  have hcontIcc : ContinuousOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc 1 M) :=
    (continuousOn_f1fun ℓ d hd τ r hre him).comp
      (by fun_prop : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) (Set.Icc 1 M))
      (fun y hy => hmem y hy.1)
  have hInt_Icc := hcontIcc.integrableOn_compact (μ := volume) isCompact_Icc
  have hInt_Ioc : IntegrableOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioc 1 M) := hInt_Icc.mono_set Set.Ioc_subset_Icc_self
  -- the tail
  have hcontIoi : ContinuousOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi M) :=
    (continuousOn_f1fun ℓ d hd τ r hre him).comp
      (by fun_prop : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) (Set.Ioi M))
      (fun y hy => hmem y (le_trans hM1 (le_of_lt hy)))
  have hmeas : AEStronglyMeasurable (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (volume.restrict (Set.Ioi M)) :=
    hcontIoi.aestronglyMeasurable measurableSet_Ioi
  have hgi0 : IntegrableOn (fun y : ℝ => y ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y))
      (Set.Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := N) (by linarith)
      (by norm_num) hc
  have hgi : Integrable (fun y : ℝ => (C * 2 ^ N) * y ^ N
      * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y)) (volume.restrict (Set.Ioi M)) := by
    have h := hgi0.mono_set (Set.Ioi_subset_Ioi (le_of_lt hMpos))
    simpa [mul_assoc] using h.const_mul (C * 2 ^ N)
  have htail : IntegrableOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi M) := by
    refine Integrable.mono' hgi hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy1 : 1 ≤ y := le_trans hM1 (le_of_lt hy)
    have hK := hbound (a - 1) y (by rcases ha with h | h <;> rw [h] <;> norm_num)
      (by rcases ha with h | h <;> rw [h] <;> norm_num) (le_of_lt hy)
    have harg : ((a - 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I
        = ((a : ℂ) + (y : ℂ) * Complex.I) - 1 := by push_cast; ring
    rw [harg] at hK
    have hker : ‖Work.Asymptotics.kerExp r ((a : ℂ) + (y : ℂ) * Complex.I)‖
        = Real.exp (-(Real.pi * r ^ 2 * y)) := by
      rw [kerExp_decomp r a y, norm_mul, norm_kerExp_ofReal, one_mul,
        Work.Asymptotics.norm_gaussWeight]
    have hpow : (1 + y) ^ N ≤ 2 ^ N * y ^ N := by
      calc (1 + y) ^ N ≤ (2 * y) ^ N :=
            Real.rpow_le_rpow (by linarith) (by linarith) hN
        _ = 2 ^ N * y ^ N := Real.mul_rpow (by norm_num) (by linarith)
    rw [f1fun, norm_mul, hker]
    calc ‖Work.Kernels.Kfun ℓ d τ
            (UpperHalfPlane.ofComplex (((a : ℂ) + (y : ℂ) * Complex.I) - 1))‖
          * Real.exp (-(Real.pi * r ^ 2 * y))
        ≤ (C * (1 + y) ^ N * Real.exp (2 * Real.pi * y)) * Real.exp (-(Real.pi * r ^ 2 * y)) :=
          mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
      _ = C * (1 + y) ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y) := by
          rw [mul_assoc (C * (1 + y) ^ N) (Real.exp (2 * Real.pi * y))
                (Real.exp (-(Real.pi * r ^ 2 * y))), ← Real.exp_add]
          congr 1
          ring
      _ ≤ C * (2 ^ N * y ^ N) * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
            (Real.exp_nonneg _)
      _ = (C * 2 ^ N) * y ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y) := by ring
  have hunion := hInt_Ioc.union htail
  rwa [Set.Ioc_union_Ioi_eq_Ioi hM1] at hunion

/-- Elementary algebra: solving `(I·(K·X) - I·Y) + S = B` for `S`. -/
theorem shift_f1_algebra (I K X Y S B : ℂ)
    (h : I * (K * X) - I * Y + S = B) : S = B - I * K * X + I * Y := by
  rw [← h]; ring

/-- **The contour-shift identity for the `K(τ, ·-1)` ray on the line `Re τ = 1/2`.** -/
theorem shift_f1_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) (hre : τ.re = 1/2) (him : 12 ≤ τ.im) :
    (∫ x in (0:ℝ)..1, f1fun ℓ d τ r ((x:ℂ) + (1:ℂ)*Complex.I))
      = 2*(Real.pi:ℂ)*Complex.I*(Work.Kernels.gaussTerm τ r/(2*Real.pi))
        - Complex.I * Work.Asymptotics.kerExp r (1:ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t) := by
  obtain ⟨C, N, hC, hN, _, hbound⟩ :=
    Kfun_bound_shift ℓ d hd τ (Or.inl hre) him
  have hcont := continuousOn_f1fun ℓ d hd τ r hre him
  have hhol := differentiableAt_f1fun ℓ d hd τ r hre him
  have hres := tendsto_f1fun_residue ℓ d hd τ r him
  have htop := tendsto_topEdge_f1fun ℓ d hd τ r him hC.le hN hr hbound
  have hint0 := integrableOn_f1fun_ray ℓ d hd τ r hre him hC.le hN hr hbound 0 (Or.inl rfl)
  have hint1 := integrableOn_f1fun_ray ℓ d hd τ r hre him hC.le hN hr hbound 1 (Or.inr rfl)
  have hkey := vertical_ray_shift (f := f1fun ℓ d τ r) (z₀ := (τ : ℂ))
      (c := Work.Kernels.gaussTerm τ r / (2 * Real.pi))
      (x₁ := 0) (x₂ := 1) (y₁ := 1)
      (by rw [UpperHalfPlane.coe_re, hre]; norm_num)
      (by rw [UpperHalfPlane.coe_re, hre]; norm_num)
      (by rw [UpperHalfPlane.coe_im]; linarith)
      hcont hhol hres htop hint0 hint1
  have hA : (∫ y : ℝ in Set.Ioi 1, f1fun ℓ d τ r (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = Work.Asymptotics.kerExp r (1 : ℂ) * (∫ y : ℝ in Set.Ioi 1, A0fun ℓ d τ r y) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi 1)
      (f := fun y : ℝ => f1fun ℓ d τ r (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      (g := fun y : ℝ => Work.Asymptotics.kerExp r (1 : ℂ) * A0fun ℓ d τ r y)
      measurableSet_Ioi ?_
    intro y hy
    simpa using f1fun_one_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy])
  have hB : (∫ y : ℝ in Set.Ioi 1, f1fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in Set.Ioi 1, Amfun ℓ d τ r y) := by
    refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi 1)
      (f := fun y : ℝ => f1fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      (g := fun y : ℝ => Amfun ℓ d τ r y) measurableSet_Ioi ?_
    intro y hy
    simpa using f1fun_zero_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy])
  rw [hA, hB] at hkey
  simp only [Complex.ofReal_one] at hkey
  set X : ℂ := ∫ t : ℝ in Set.Ioi 1, A0fun ℓ d τ r t with hX
  set Y : ℂ := ∫ t : ℝ in Set.Ioi 1, Amfun ℓ d τ r t with hY
  set S : ℂ := ∫ x in (0 : ℝ)..1, f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I) with hS
  set Bq : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (Work.Kernels.gaussTerm τ r / (2 * Real.pi)) with hBq
  exact shift_f1_algebra Complex.I (Work.Asymptotics.kerExp r (1 : ℂ)) X Y S Bq hkey

end Work.CKFinal.LineDecay
