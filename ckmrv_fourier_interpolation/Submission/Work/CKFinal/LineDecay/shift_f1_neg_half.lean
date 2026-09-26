import Mathlib
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.CKFinal.LineDecay.Kfun_strip_bound
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two

/-!
# The contour-shift identity `shift_f1_neg_half`

We shift the horizontal segment `[0,1] + i` of the integrand
`f₁(z) = K^{(d)}(τ, z-1)·e^{iπr²z}` up through the half-strip `{0 ≤ Re ≤ 1, Im ≥ 1}`.

For `τ.re = -1/2`, `Im τ ≥ 12`, the only pole of `z ↦ K^{(d)}(τ, z-1)` inside the closed
half-strip is the *diagonal* one at `z = τ + 1` (i.e. `z - 1 = τ`), whose residue vanishes
(`Work.CKFinal.LineDecay.Kfun_second_limits`, third conjunct).  Hence the contour shift is
residue-free and

  `∫_0^1 f₁(x+I) dx = -I·e^{iπr²}·∫_{1}^{∞} A₀ + I·∫_{1}^{∞} A₋`,

which is the negative-half-line analogue of `shift_f1_half`.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

set_option maxHeartbeats 4000000

/-! ## Elementary facts about the exponential factor -/

/-- `‖e^{iπr²x}‖ = 1` for real `x`. -/
private theorem norm_kerExp_ofReal (r x : ℝ) : ‖Work.Asymptotics.kerExp r (x : ℂ)‖ = 1 := by
  rw [Work.Asymptotics.kerExp,
    show (Real.pi : ℂ) * Complex.I * (r : ℂ) ^ 2 * (x : ℂ)
      = (((Real.pi * r ^ 2 * x : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `kerExp r (i y) = gaussWeight r y`. -/
private theorem kerExp_mul_I (r y : ℝ) :
    Work.Asymptotics.kerExp r ((y : ℂ) * Complex.I) = Work.Asymptotics.gaussWeight r y := by
  have h := kerExp_decomp r 0 y
  rw [show ((0:ℝ):ℂ) + (y : ℂ) * Complex.I = (y : ℂ) * Complex.I by push_cast; ring] at h
  rw [h]
  simp [Work.Asymptotics.kerExp]

private theorem continuous_kerExp (r : ℝ) :
    Continuous fun z : ℂ => Work.Asymptotics.kerExp r z := by
  unfold Work.Asymptotics.kerExp; fun_prop

/-! ## The point `τ + 1` -/

private theorem coe_vadd_one_re (τ : UpperHalfPlane) :
    ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ).re = τ.re + 1 := by
  rw [UpperHalfPlane.coe_vadd, Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re]
  ring

private theorem coe_vadd_one_im (τ : UpperHalfPlane) :
    ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ).im = τ.im := by
  rw [UpperHalfPlane.coe_vadd, Complex.add_im, Complex.ofReal_im, UpperHalfPlane.coe_im]
  ring

/-! ## The integrand on the two vertical rays -/

/-- The integrand on the ray `Re = 0`: `f₁(0 + iy) = A₋(y)`. -/
private theorem f1fun_zero_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (r y : ℝ) (hy : 0 < y) :
    f1fun ℓ d τ r ((0 : ℂ) + (y : ℂ) * Complex.I) = Amfun ℓ d τ r y := by
  have harg : ((0 : ℂ) + (y : ℂ) * Complex.I) - 1 = ((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast; ring
  have hker : Work.Asymptotics.kerExp r ((0 : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.gaussWeight r y := by
    rw [show ((0:ℂ) + (y : ℂ) * Complex.I) = (y : ℂ) * Complex.I by ring]
    exact kerExp_mul_I r y
  simp only [f1fun, Amfun]
  rw [Kax_eq_K_ofComplex (K := Work.Kernels.Kfun ℓ d) τ (-1) y hy, harg, hker]

/-- The integrand on the ray `Re = 1`: `f₁(1 + iy) = e^{iπr²} A₀(y)`. -/
private theorem f1fun_one_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (r y : ℝ) (hy : 0 < y) :
    f1fun ℓ d τ r ((1 : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.kerExp r (1 : ℂ) * A0fun ℓ d τ r y := by
  have harg : ((1 : ℂ) + (y : ℂ) * Complex.I) - 1 = ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast; ring
  have hker : Work.Asymptotics.kerExp r ((1 : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.kerExp r (1 : ℂ) * Work.Asymptotics.gaussWeight r y :=
    kerExp_decomp r 1 y
  simp only [f1fun, A0fun]
  rw [Kax_eq_K_ofComplex (K := Work.Kernels.Kfun ℓ d) τ 0 y hy, harg, hker]
  ring

/-! ## The divisor is avoided on the half-strip, away from the diagonal pole `τ + 1` -/

/-- For `τ.re = -1/2`, `Im τ ≥ 12` and `z` in the closed half-strip `{0 ≤ Re ≤ 1, Im ≥ 1}`
with `z ≠ τ + 1`, the point `z - 1` is not in the `SL(2,ℤ)`-orbit of `τ`: on the half-strip
`{−1 ≤ Re ≤ 1}` the only orbit point with `Im ≥ 1` whose real part lies in `[−1,0]` is `τ`
itself, which corresponds to `z = τ + 1`. -/
private theorem ofComplex_sub_one_clean_neg (τ : UpperHalfPlane) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → z ≠ (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) →
      Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1)) := by
  intro z h0 h1 h2 hne hjeq
  have hwimpos : 0 < (z - 1).im := by simp [Complex.sub_im]; linarith
  have hwim : 1 ≤ (z - 1).im := by simp [Complex.sub_im]; linarith
  have hwre : -1 ≤ (z - 1).re := by simp [Complex.sub_re]; linarith
  have hwre1 : (z - 1).re ≤ 1 := by simp [Complex.sub_re]; linarith
  have hcoe : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ) = z - 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwimpos]
  have hc := ofComplex_mem_orbit τ (Or.inr hre) him hwim hwre hwre1 hjeq
  rcases hc with h | h | h
  · -- `z - 1 = τ`, i.e. `z = τ + 1`
    have hc1 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ) = (τ : ℂ) := by
      rw [h]
    have hz : (z - 1) = (τ : ℂ) := hcoe.symm.trans hc1
    have hzz : z = (τ : ℂ) + 1 := by
      have h' := congrArg (fun w : ℂ => w + 1) hz
      simpa using h'
    have hz0 : ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) = (τ : ℂ) + 1 := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    exact hne (by rw [hzz, hz0])
  · -- `z - 1 = τ - 1`, which has real part `τ.re - 1 = -3/2 < -1`
    have hc2 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ)
        = ((((-1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) := by rw [h]
    have hz : (z - 1) = (τ : ℂ) - 1 := by
      rw [hcoe.symm.trans hc2, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hre' : (z - 1).re = τ.re - 1 := by rw [hz]; simp
    have hle : (z - 1).re ≤ 0 := by simp [Complex.sub_re]; linarith
    linarith [hre', hle, hre]
  · -- `z - 1 = τ + 1`, i.e. `z = τ + 2`, whose real part is `τ.re + 2 = 3/2 > 1`
    have hc3 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ)
        = ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) := by rw [h]
    have hz : (z - 1) = (τ : ℂ) + 1 := by
      rw [hcoe.symm.trans hc3, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hzz : z = (τ : ℂ) + 2 := by
      have h' := congrArg (fun w : ℂ => w + 1) hz
      have h2 : z = z - 1 + 1 := by ring
      rw [h2, h']; ring
    have hre' : z.re = τ.re + 2 := by rw [hzz]; simp
    linarith [hre', h1, hre]

/-! ## Continuity and holomorphy of the integrand -/

/-- `z ↦ f₁(z) = K^{(d)}(τ, z-1)·e^{iπr²z}` is continuous on the closed half-strip
`{0 ≤ Re ≤ 1, 1 ≤ Im}` away from the pole `z = τ + 1`. -/
private theorem continuousOn_f1fun_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) :
    ContinuousOn (f1fun ℓ d τ r)
      ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im}
        \ {(((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)}) := by
  intro z hz
  have hz1 : 0 ≤ z.re := hz.1.1
  have hz2 : z.re ≤ 1 := hz.1.2.1
  have hz3 : 1 ≤ z.im := hz.1.2.2
  have hzτ : z ≠ (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by simpa using hz.2
  have hclean := ofComplex_sub_one_clean_neg τ hre him z hz1 hz2 hz3 hzτ
  have him1 : 0 < (z - 1).im := by simp [Complex.sub_im]; linarith
  have hmem : {w : ℂ | 0 < w.im} ∈ 𝓝 (z - 1) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds him1
  have hsub : ContinuousAt (fun z : ℂ => z - 1) z := by fun_prop
  have hof : ContinuousAt (fun z : ℂ => UpperHalfPlane.ofComplex (z - 1)) z :=
    (Work.Asymptotics.continuousOn_ofComplex_of_im_pos.continuousAt hmem).comp
      (f := fun z : ℂ => z - 1) hsub
  have hg : ContinuousAt (fun z : ℂ => (τ, UpperHalfPlane.ofComplex (z - 1))) z :=
    ContinuousAt.prodMk continuousAt_const hof
  have hK : ContinuousAt
      (fun z : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z - 1))) z :=
    (Work.Asymptotics.continuousAt_Kfun_of_clean hd
      (p := (τ, UpperHalfPlane.ofComplex (z - 1))) hclean).comp
      (f := fun z : ℂ => (τ, UpperHalfPlane.ofComplex (z - 1))) hg
  have hker : ContinuousAt (fun z : ℂ => Work.Asymptotics.kerExp r z) z :=
    (continuous_kerExp r).continuousAt
  exact (hK.mul hker).continuousWithinAt

/-- `f₁` is complex differentiable on the open half-strip `{0 < Re < 1, 1 < Im}` away from the
pole `z = τ + 1`. -/
private theorem differentiableAt_f1fun_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) :
    ∀ z : ℂ, 0 < z.re → z.re < 1 → 1 < z.im → z ≠ (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) →
      DifferentiableAt ℂ (f1fun ℓ d τ r) z := by
  intro z h0 h1 h2 hne
  have hclean := ofComplex_sub_one_clean_neg τ hre him z (le_of_lt h0) (le_of_lt h1)
    (le_of_lt h2) hne
  have himpos : 0 < (z - 1).im := by simp [Complex.sub_im]; linarith
  have hmd := Work.Residues.mdifferentiableAt_Kfun_snd ℓ d hd τ
    (UpperHalfPlane.ofComplex (z - 1)) hclean.symm
  have hbase : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w)) (z - 1) := by
    have h := UpperHalfPlane.mdifferentiableAt_iff.mp hmd
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos himpos] at h
    simpa only [Function.comp_def] using h
  have hsubd : DifferentiableAt ℂ (fun z : ℂ => z - 1) z := by fun_prop
  have hK := hbase.comp z hsubd
  have hker : DifferentiableAt ℂ (fun z : ℂ => Work.Asymptotics.kerExp r z) z := by
    unfold Work.Asymptotics.kerExp; fun_prop
  have hmain := hK.mul hker
  change DifferentiableAt ℂ (fun z : ℂ =>
    Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
      * Work.Asymptotics.kerExp r z) z
  exact hmain

/-- The residue limit of `f₁` at the pole `z = τ + 1`: it vanishes, because the pole of the
kernel sits on the *diagonal* `ζ = τ` (`Work.Residues.hasResidue_Kfun_self`). -/
private theorem tendsto_f1fun_residue_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) :
    Filter.Tendsto (fun z : ℂ => (z - ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ))
        * f1fun ℓ d τ r z)
      (nhdsWithin ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)
        {((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)}ᶜ) (nhds 0) := by
  have hne : Work.Residues.jprime τ ≠ 0 :=
    Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two τ (by linarith)
  obtain ⟨_, _, h3⟩ := Kfun_second_limits ℓ d hd τ hne
  have hshift := tendsto_shift_comp
    (F := fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w))
    (ζ₀ := (τ : ℂ)) (c := 0) (d := -1) h3
  have hctr : (τ : ℂ) - (-1) = (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  rw [hctr] at hshift
  have hshift' : Filter.Tendsto
      (fun z : ℂ => (z - (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ))
        * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z - 1)))
      (nhdsWithin ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)
        {((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)}ᶜ) (nhds 0) := by
    refine hshift.congr' ?_
    filter_upwards with z
    rfl
  have hker : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
      (nhdsWithin ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)
        {((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)}ᶜ) (nhds (Work.Asymptotics.kerExp r
          ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ))) :=
    ((continuous_kerExp r).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hshift'.mul hker
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards with z
  simp only [f1fun]
  ring

/-! ## The growth bound on the strip implies the analytic inputs of the shift -/

/-- The pointwise bound on the shifted integrand along a horizontal line of the half-strip. -/
private theorem norm_f1fun_horizontal_le (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) {C N : ℝ}
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
  calc ‖Work.Kernels.Kfun ℓ d τ
          (UpperHalfPlane.ofComplex (((x : ℂ) + (R : ℂ) * Complex.I) - 1))‖
        * Real.exp (-(Real.pi * r ^ 2 * R))
      ≤ (C * (1 + R) ^ N * Real.exp (2 * Real.pi * R)) * Real.exp (-(Real.pi * r ^ 2 * R)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ = C * (1 + R) ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * R) := by
        rw [mul_assoc (C * (1 + R) ^ N) (Real.exp (2 * Real.pi * R))
              (Real.exp (-(Real.pi * r ^ 2 * R))), ← Real.exp_add]
        congr 1
        ring

/-- The top edge `∫_0^1 f₁(x + iR) dx` of the shift rectangle tends to `0`. -/
private theorem tendsto_topEdge_f1fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) {C N : ℝ}
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
private theorem integrableOn_f1fun_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) {C N : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hr : 2 < r ^ 2)
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
        ∈ ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im}
            \ {(((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)}) := by
    intro y hy
    have h1 : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by simp
    have h2 : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [h1]; rcases ha with h | h <;> rw [h] <;> norm_num
    · rw [h1]; rcases ha with h | h <;> rw [h] <;> norm_num
    · rw [h2]; exact hy
    · intro hτ
      have h' := congrArg Complex.re hτ
      rw [h1, coe_vadd_one_re, hre] at h'
      rcases ha with h | h <;> rw [h] at h' <;> norm_num at h'
  have hcontIcc : ContinuousOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc 1 M) :=
    (continuousOn_f1fun_neg ℓ d hd τ r hre him).comp
      (by fun_prop : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) (Set.Icc 1 M))
      (fun y hy => hmem y hy.1)
  have hInt_Icc := hcontIcc.integrableOn_compact (μ := volume) isCompact_Icc
  have hInt_Ioc : IntegrableOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioc 1 M) := hInt_Icc.mono_set Set.Ioc_subset_Icc_self
  -- the tail
  have hcontIoi : ContinuousOn (fun y : ℝ => f1fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi M) :=
    (continuousOn_f1fun_neg ℓ d hd τ r hre him).comp
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
        ≤ (C * (1 + y) ^ N * Real.exp (2 * Real.pi * y))
            * Real.exp (-(Real.pi * r ^ 2 * y)) :=
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

/-! ## The strip bound (interface) -/

/-- The growth bound for the kernel on the strip `{−1 ≤ Re ≤ 1, Im ≥ Im τ + 1}` — the
input shared with the sibling identities `shift_f1_half`, `shift_f2_half`,
`shift_f2_neg_half` (it is `Kfun_strip_tail_bound_line` of `LineDecay/Kfun_strip_bound`). -/
private theorem strip_bound_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = -1 / 2) (him : 12 ≤ τ.im) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R) :=
  Kfun_strip_tail_bound_line ℓ d hd τ (Or.inr hre) him

/-! ## Elementary algebra of the shift identity -/

/-- Elementary algebra: solving the residue-free identity `I·(K·X) - I·Y + S = 0` for `S`. -/
private theorem shift_f1_algebra_zero (I K X Y S : ℂ)
    (h : I * (K * X) - I * Y + S = 0) : S = - I * K * X + I * Y := by
  have h1 : S = -(I * (K * X) - I * Y) := eq_neg_of_add_eq_zero_right h
  rw [h1]; ring

/-! ## The contour-shift identity -/

theorem shift_f1_neg_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) (hre : τ.re = -1/2) (him : 12 ≤ τ.im) :
    (∫ x in (0:ℝ)..1, f1fun ℓ d τ r ((x:ℂ) + (1:ℂ)*Complex.I))
      = - Complex.I * Work.Asymptotics.kerExp r (1:ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t)
        + Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t) := by
  obtain ⟨C, N, hC, hN, hbound⟩ := strip_bound_neg ℓ d hd τ hre him
  have hcont := continuousOn_f1fun_neg ℓ d hd τ r hre him
  have hhol := differentiableAt_f1fun_neg ℓ d hd τ r hre him
  have hres := tendsto_f1fun_residue_zero ℓ d hd τ r him
  have htop := tendsto_topEdge_f1fun ℓ d hd τ r him hC.le hN hr hbound
  have hint0 := integrableOn_f1fun_ray ℓ d hd τ r hre him hC.le hN hr hbound 0 (Or.inl rfl)
  have hint1 := integrableOn_f1fun_ray ℓ d hd τ r hre him hC.le hN hr hbound 1 (Or.inr rfl)
  have hz₀re : ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ).re = 1 / 2 := by
    rw [coe_vadd_one_re, hre]; norm_num
  have hz₀im : ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ).im = τ.im := coe_vadd_one_im τ
  have hkey := vertical_ray_shift (f := f1fun ℓ d τ r)
    (z₀ := ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)) (c := 0)
    (x₁ := 0) (x₂ := 1) (y₁ := 1)
    (by rw [hz₀re]; norm_num)
    (by rw [hz₀re]; norm_num)
    (by rw [hz₀im]; linarith)
    hcont hhol hres htop hint0 hint1
  have hA : (∫ y : ℝ in Set.Ioi 1, f1fun ℓ d τ r (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = Work.Asymptotics.kerExp r (1 : ℂ) * (∫ y : ℝ in Set.Ioi 1, A0fun ℓ d τ r y) := by
    simp only [Complex.ofReal_one]
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => f1fun_one_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy]))
  have hB : (∫ y : ℝ in Set.Ioi 1, f1fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in Set.Ioi 1, Amfun ℓ d τ r y) := by
    simp only [Complex.ofReal_zero]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => f1fun_zero_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy]))
  rw [hA, hB] at hkey
  have hkey0 : Complex.I * (Work.Asymptotics.kerExp r (1 : ℂ)
        * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t))
      - Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t)
      + (∫ x in (0 : ℝ)..1, f1fun ℓ d τ r ((x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I)) = 0 := by
    rw [hkey]; ring
  have hgoal : (∫ x in (0 : ℝ)..1, f1fun ℓ d τ r ((x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I))
      = -(Complex.I * (Work.Asymptotics.kerExp r (1 : ℂ)
          * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t))
        - Complex.I * (∫ t in Set.Ioi 1, Amfun ℓ d τ r t)) :=
    eq_neg_of_add_eq_zero_right hkey0
  simp only [Complex.ofReal_one] at hgoal ⊢
  rw [hgoal]; ring

end Work.CKFinal.LineDecay
