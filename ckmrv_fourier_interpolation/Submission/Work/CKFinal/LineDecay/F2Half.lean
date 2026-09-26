/-
# The contour-shift identity for the `K(τ, ·+1)` ray on the line `Re τ = 1/2`

CKMRV §5.3.  On the half-strip `{-1 ≤ Re ≤ 0, 1 ≤ Im}` the second variable `z + 1` of the kernel
avoids the divisor except at `z = τ` (the *diagonal*, whose residue vanishes), so the only
contribution of the shifted rectangle is the boundary term.  This file provides the continuity,
holomorphy and residue data for `f₂fun = K(τ, ·+1)·e^{iπr²·}`, together with the shift identity
itself; the growth bound on the top edge is `Work.CKFinal.LineDecay.f2fun_top_edge_of_bound` and
the two vertical sides are covered by `Work.CKFinal.LineDecay.ray_integrable`.
-/
import Mathlib
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.CKFinal.LineDecay.Kfun_strip_bound
import Submission.Work.CKFinal.LineDecay.ray_integrable
import Submission.Work.CKFinal.LineDecay.f2fun_top_edge_of_bound
import Submission.Work.CKFinal.LineDecay.F1Half.Basic
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two

noncomputable section

set_option maxHeartbeats 4000000

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

/-- The only point of the `SL(2,ℤ)`-orbit of `τ` (`Re τ = 1/2`, `Im τ ≥ 12`) with `Re ∈ [0,1]`
and `Im ≥ 1` is `τ` itself.  Equivalently, on the half-strip `{-1 ≤ Re ≤ 0, 1 ≤ Im}` the second
variable `z + 1` of the kernel avoids the divisor except at `z = τ - 1`. -/
theorem ofComplex_add_one_clean (τ : UpperHalfPlane) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) :
    ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 0 → 1 ≤ z.im → z ≠ (τ : ℂ) - 1 →
      Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z + 1)) := by
  intro z h0 h1 h2 hne hjeq
  have hwimpos : 0 < (z + 1).im := by simp [Complex.add_im]; linarith
  have hwim : 1 ≤ (z + 1).im := by simp [Complex.add_im]; linarith
  have hwre : -1 ≤ (z + 1).re := by simp [Complex.add_re]; linarith
  have hwre1 : (z + 1).re ≤ 1 := by simp [Complex.add_re]; linarith
  have hcoe : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ) = z + 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwimpos]
  have hc := ofComplex_mem_orbit τ (Or.inl hre) him hwim hwre hwre1 hjeq
  rcases hc with h | h | h
  · have hc1 : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ) = (τ : ℂ) := by
      rw [h]
    have hz : z + 1 = (τ : ℂ) := hcoe.symm.trans hc1
    have hzz : z = (τ : ℂ) - 1 := by linear_combination hz
    exact hne hzz
  · have hc2 : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ)
        = (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hz : z + 1 = (τ : ℂ) - 1 := by
      rw [hcoe.symm.trans hc2, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hre' : (z + 1).re = τ.re - 1 := by rw [hz]; simp
    have hre0 : 0 ≤ (z + 1).re := by simp [Complex.add_re]; linarith
    linarith [hre', hre, hre0]
  · have hc3 : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ)
        = (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hz : z + 1 = (τ : ℂ) + 1 := by
      rw [hcoe.symm.trans hc3, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hre' : (z + 1).re = τ.re + 1 := by rw [hz]; simp
    have hre1 : (z + 1).re ≤ 1 := by simp [Complex.add_re]; linarith
    linarith [hre', hre, hre1]

/-! ## Continuity and holomorphy of `f2fun` off the pole -/

/-- `z ↦ f₂(z) = K^{(d)}(τ, z+1) e^{iπr²z}` is continuous on the closed half-strip
`{-1 ≤ Re ≤ 0, 1 ≤ Im}` away from the pole `z = τ - 1`. -/
theorem continuousOn_f2fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) :
    ContinuousOn (f2fun ℓ d τ r)
      ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im} \ {((τ : ℂ) - 1)}) := by
  intro z hz
  have hz1 : -1 ≤ z.re := hz.1.1
  have hz2 : z.re ≤ 0 := hz.1.2.1
  have hz3 : 1 ≤ z.im := hz.1.2.2
  have hzτ : z ≠ (τ : ℂ) - 1 := by simpa using hz.2
  have hclean := ofComplex_add_one_clean τ hre him z hz1 hz2 hz3 hzτ
  have him1 : 0 < (z + 1).im := by simp [Complex.add_im]; linarith
  have hmem : {w : ℂ | 0 < w.im} ∈ 𝓝 (z + 1) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds him1
  have hadd : ContinuousAt (fun z : ℂ => z + 1) z := by fun_prop
  have hof : ContinuousAt (fun z : ℂ => UpperHalfPlane.ofComplex (z + 1)) z :=
    (Work.Asymptotics.continuousOn_ofComplex_of_im_pos.continuousAt hmem).comp
      (f := fun z : ℂ => z + 1) hadd
  have hg : ContinuousAt (fun z : ℂ => (τ, UpperHalfPlane.ofComplex (z + 1))) z :=
    ContinuousAt.prodMk continuousAt_const hof
  have hK : ContinuousAt
      (fun z : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z + 1))) z :=
    (Work.Asymptotics.continuousAt_Kfun_of_clean hd
      (p := (τ, UpperHalfPlane.ofComplex (z + 1))) hclean).comp
      (f := fun z : ℂ => (τ, UpperHalfPlane.ofComplex (z + 1))) hg
  have hker : ContinuousAt (fun z : ℂ => Work.Asymptotics.kerExp r z) z :=
    (continuous_kerExp r).continuousAt
  exact (hK.mul hker).continuousWithinAt

/-- `f₂` is complex differentiable on the open half-strip `{-1 < Re < 0, 1 < Im}` away from the
pole `z = τ - 1`. -/
theorem differentiableAt_f2fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) :
    ∀ z : ℂ, -1 < z.re → z.re < 0 → 1 < z.im → z ≠ (τ : ℂ) - 1 →
      DifferentiableAt ℂ (f2fun ℓ d τ r) z := by
  intro z h0 h1 h2 hne
  have hclean := ofComplex_add_one_clean τ hre him z (le_of_lt h0) (le_of_lt h1) (le_of_lt h2) hne
  have himpos : 0 < (z + 1).im := by simp [Complex.add_im]; linarith
  have hmd := Work.Residues.mdifferentiableAt_Kfun_snd ℓ d hd τ
    (UpperHalfPlane.ofComplex (z + 1)) hclean.symm
  have hbase : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w)) (z + 1) := by
    have h := UpperHalfPlane.mdifferentiableAt_iff.mp hmd
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos himpos] at h
    simpa only [Function.comp_def] using h
  have haddd : DifferentiableAt ℂ (fun z : ℂ => z + 1) z := by fun_prop
  have hK := hbase.comp z haddd
  have hker : DifferentiableAt ℂ (fun z : ℂ => Work.Asymptotics.kerExp r z) z := by
    unfold Work.Asymptotics.kerExp; fun_prop
  have hmain := hK.mul hker
  change DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z + 1))
      * Work.Asymptotics.kerExp r z) z
  exact hmain

/-- The residue limit of `f₂` at the pole `z = τ - 1` (the *diagonal* pole of the kernel, whose
residue vanishes). -/
theorem tendsto_f2fun_residue (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) :
    Filter.Tendsto (fun z : ℂ => (z - ((τ : ℂ) - 1)) * f2fun ℓ d τ r z)
      (nhdsWithin ((τ : ℂ) - 1) {((τ : ℂ) - 1)}ᶜ) (nhds 0) := by
  have hne : Work.Residues.jprime τ ≠ 0 :=
    Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two τ (by linarith)
  obtain ⟨_, _, hlim⟩ := Kfun_second_limits ℓ d hd τ hne
  have hshift := tendsto_shift_comp
    (F := fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w))
    (ζ₀ := (τ : ℂ)) (c := 0) (d := 1) hlim
  have hker : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
      (nhdsWithin ((τ : ℂ) - 1) {((τ : ℂ) - 1)}ᶜ)
      (nhds (Work.Asymptotics.kerExp r ((τ : ℂ) - 1))) :=
    ((continuous_kerExp r).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hshift.mul hker
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards with z
  simp only [f2fun]
  ring

/-! ## The two vertical rays of `f₂` -/

/-- The integrand on the ray `Re = 0`: `f₂(0 + iy) = A_{+}(y)`. -/
theorem f2fun_zero_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r y : ℝ)
    (hy : 0 < y) :
    f2fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = Apfun ℓ d τ r y := by
  have harg : (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) + 1
      = ((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by push_cast; ring
  have hker : Work.Asymptotics.kerExp r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.gaussWeight r y := by
    rw [show (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = (y : ℂ) * Complex.I by push_cast; ring]
    exact kerExp_mul_I r y
  simp only [f2fun, Apfun]
  rw [Kax_eq_K_ofComplex (K := Work.Kernels.Kfun ℓ d) τ 1 y hy, harg, hker]

/-- The integrand on the ray `Re = -1`: `f₂(-1 + iy) = e^{-iπr²} A_0(y)`. -/
theorem f2fun_neg_one_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r y : ℝ)
    (hy : 0 < y) :
    f2fun ℓ d τ r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)) * A0fun ℓ d τ r y := by
  have harg : ((((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I) + 1
      = ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by push_cast; ring
  have hker : Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)) * Work.Asymptotics.gaussWeight r y :=
    kerExp_decomp r (-1) y
  simp only [f2fun, A0fun]
  rw [Kax_eq_K_ofComplex (K := Work.Kernels.Kfun ℓ d) τ 0 y hy, harg, hker]
  ring

/-- **The contour-shift identity for the `K(τ, ·+1)` ray on the line `Re τ = 1/2`.** -/
theorem shift_f2_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) (hre : τ.re = 1/2) (him : 12 ≤ τ.im) :
    (∫ x in (-1:ℝ)..0, f2fun ℓ d τ r ((x:ℂ) + (1:ℂ)*Complex.I))
      = - Complex.I * (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
        + Complex.I * Work.Asymptotics.kerExp r (-1:ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t) := by
  obtain ⟨C, N, hC, hN, hbound⟩ := Kfun_strip_tail_bound_line ℓ d hd τ (Or.inl hre) him
  have hcont := continuousOn_f2fun ℓ d hd τ r hre him
  have hhol := differentiableAt_f2fun ℓ d hd τ r hre him
  have hres := tendsto_f2fun_residue ℓ d hd τ r him
  have htop := f2fun_top_edge_of_bound ℓ d hd τ hr hC.le hN hbound
  have hker_eq : Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ))
      = Work.Asymptotics.kerExp r (-1 : ℂ) := by
    congr 1
    push_cast
    ring
  -- the two vertical sides are integrable
  have hm0 : (fun y : ℝ => f2fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      =ᵐ[volume.restrict (Set.Ioi 1)] (fun y : ℝ => Apfun ℓ d τ r y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact f2fun_zero_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy])
  have hint0 : IntegrableOn (fun y : ℝ => f2fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi 1) :=
    (integrableOn_Kax_ray ℓ d hd τ hr (Or.inl hre) him (Or.inr rfl)).congr hm0.symm
  have hm1 : (fun y : ℝ => f2fun ℓ d τ r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      =ᵐ[volume.restrict (Set.Ioi 1)]
        (fun y : ℝ => Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)) * A0fun ℓ d τ r y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact f2fun_neg_one_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy])
  have hintm : IntegrableOn (fun y : ℝ => f2fun ℓ d τ r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi 1) :=
    ((integrableOn_A0fun ℓ d hd τ hr (mem_DomainD_of_line τ (Or.inl hre) him)).const_mul
      (Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)))).congr hm1.symm
  have hkey := vertical_ray_shift (f := f2fun ℓ d τ r) (z₀ := (τ : ℂ) - 1) (c := 0)
      (x₁ := -1) (x₂ := 0) (y₁ := 1)
      (by rw [show ((τ : ℂ) - 1).re = τ.re - 1 by simp, hre]; norm_num)
      (by rw [show ((τ : ℂ) - 1).re = τ.re - 1 by simp, hre]; norm_num)
      (by rw [show ((τ : ℂ) - 1).im = τ.im by simp]; linarith)
      hcont hhol hres htop hintm hint0
  have hA : (∫ y : ℝ in Set.Ioi 1, f2fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = (∫ t in Set.Ioi 1, Apfun ℓ d τ r t) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    exact f2fun_zero_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy])
  have hB : (∫ y : ℝ in Set.Ioi 1, f2fun ℓ d τ r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = Work.Asymptotics.kerExp r (-1 : ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [f2fun_neg_one_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy]), hker_eq]
  rw [hA, hB, mul_zero] at hkey
  linear_combination hkey

end Work.CKFinal.LineDecay
