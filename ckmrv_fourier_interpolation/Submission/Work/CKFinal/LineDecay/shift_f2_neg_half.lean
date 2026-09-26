import Mathlib
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.CKFinal.LineDecay.Kfun_bound_shift
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two
import Submission.Work.Residues.KernelPoleLocation

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-!
# The contour-shift identity `shift_f2_neg_half`

The shifted integrand `f2fun ℓ d τ r z = K^{(d)}(τ, z+1) e^{iπr²z}` has (for `Re τ = -1/2`,
`Im τ ≥ 12`) exactly one pole in the half-strip `{-1 ≤ Re ≤ 0, 1 ≤ Im}`, namely the image of the
pole `τ + 1` of `K(τ,·)` at `z = τ`, with residue `-(2π)⁻¹ e^{iπr²τ} = -gaussTerm τ r / (2π)`.
Shifting the horizontal edge of the half-strip to `+i∞` (where the integrand is killed by the
Gaussian, `r² > 2`) and applying `vertical_ray_shift` therefore gives the stated identity.
-/

/-! ## Elementary facts about the shifted argument -/

/-- `kerExp r (i y) = gaussWeight r y`. -/
private lemma kerExp_mul_I' (r y : ℝ) :
    Work.Asymptotics.kerExp r ((y : ℂ) * Complex.I) = Work.Asymptotics.gaussWeight r y := by
  have h := kerExp_decomp r 0 y
  rw [show ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I = (y : ℂ) * Complex.I by push_cast; ring] at h
  rw [h]
  simp [Work.Asymptotics.kerExp]

/-- The exponential factor is continuous. -/
private lemma continuous_kerExp' (r : ℝ) :
    Continuous fun z : ℂ => Work.Asymptotics.kerExp r z := by
  unfold Work.Asymptotics.kerExp; fun_prop

/-- **The only orbit point in the half-strip.**  For `Re τ = -1/2`, `Im τ ≥ 12` and `z` in the
half-strip `{-1 ≤ Re ≤ 0, 1 ≤ Im}` with `z ≠ τ`, the point `z + 1` is not in the `SL(2,ℤ)`-orbit
of `τ`: the second variable `z + 1` of `f2fun` avoids the divisor `j = j τ` there. -/
private theorem ofComplex_add_one_clean' (τ : UpperHalfPlane) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) :
    ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 0 → 1 ≤ z.im → z ≠ (τ : ℂ) →
      Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z + 1)) := by
  intro z h0 h1 h2 hne hjeq
  have hwimpos : 0 < (z + 1).im := by simp [Complex.add_im]; linarith
  have hwim : 1 ≤ (z + 1).im := by simp [Complex.add_im]; linarith
  have hwre : -1 ≤ (z + 1).re := by simp [Complex.add_re]; linarith
  have hwre1 : (z + 1).re ≤ 1 := by simp [Complex.add_re]; linarith
  have hcoe : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ) = z + 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwimpos]
  have hc := ofComplex_mem_orbit τ (Or.inr hre) him hwim hwre hwre1 hjeq
  rcases hc with h | h | h
  · have hc1 : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ) = (τ : ℂ) := by rw [h]
    have hz : (z + 1) = (τ : ℂ) := hcoe.symm.trans hc1
    have hre' : (z + 1).re = τ.re := by rw [hz]; rfl
    have hnonneg : (0 : ℝ) ≤ (z + 1).re := by simp [Complex.add_re]; linarith
    linarith [hre', hnonneg, hre]
  · have hc2 : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ)
        = (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hz : (z + 1) = (τ : ℂ) - 1 := by
      rw [hcoe.symm.trans hc2, UpperHalfPlane.coe_vadd]; push_cast; ring
    have hre' : (z + 1).re = τ.re - 1 := by rw [hz]; simp
    have hnonneg : (0 : ℝ) ≤ (z + 1).re := by simp [Complex.add_re]; linarith
    linarith [hre', hnonneg, hre]
  · have hc3 : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ)
        = (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hz : (z + 1) = (τ : ℂ) + 1 := by
      rw [hcoe.symm.trans hc3, UpperHalfPlane.coe_vadd]; push_cast; ring
    have hzz : z = (τ : ℂ) := by
      have h' := congrArg (fun w : ℂ => w - 1) hz
      simpa using h'
    exact hne hzz

/-! ## The two vertical rays of the shifted contour -/

/-- The integrand on the ray `Re = 0`: `f₂(0 + iy) = A_{+}(y)`. -/
private theorem f2fun_zero_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (r y : ℝ) (hy : 0 < y) :
    f2fun ℓ d τ r ((0 : ℂ) + (y : ℂ) * Complex.I) = Apfun ℓ d τ r y := by
  have harg : ((0 : ℂ) + (y : ℂ) * Complex.I) + 1 = ((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast; ring
  have hker : Work.Asymptotics.kerExp r ((0 : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.gaussWeight r y := by
    rw [show ((0 : ℂ) + (y : ℂ) * Complex.I) = (y : ℂ) * Complex.I by ring]
    exact kerExp_mul_I' r y
  simp only [f2fun, Apfun]
  rw [Kax_eq_K_ofComplex (K := Work.Kernels.Kfun ℓ d) τ 1 y hy, harg, hker]

/-- The two spellings of `e^{iπr²·(-1)}`. -/
private lemma kerExp_neg_one_coe' (r : ℝ) :
    Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)) = Work.Asymptotics.kerExp r (-1 : ℂ) := by
  rw [show ((-1 : ℝ) : ℂ) = (-1 : ℂ) by norm_num]

/-- The integrand on the ray `Re = -1`: `f₂(-1 + iy) = e^{-iπr²} A_0(y)`. -/
private theorem f2fun_neg_one_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (r y : ℝ) (hy : 0 < y) :
    f2fun ℓ d τ r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)) * A0fun ℓ d τ r y := by
  have harg : (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I) + 1
      = ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by push_cast; ring
  have hker : Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)) * Work.Asymptotics.gaussWeight r y :=
    kerExp_decomp r (-1) y
  simp only [f2fun, A0fun]
  rw [Kax_eq_K_ofComplex (K := Work.Kernels.Kfun ℓ d) τ 0 y hy, harg, hker]
  ring

/-! ## Continuity and holomorphy on the half-strip -/

/-- `z ↦ f₂(z) = K^{(d)}(τ, z+1) e^{iπr²z}` is continuous on the closed half-strip
`{-1 ≤ Re ≤ 0, 1 ≤ Im}` away from the pole `z = τ`. -/
private theorem continuousOn_f2fun' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) :
    ContinuousOn (f2fun ℓ d τ r)
      ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im} \ {(τ : ℂ)}) := by
  intro z hz
  have hz1 : -1 ≤ z.re := hz.1.1
  have hz2 : z.re ≤ 0 := hz.1.2.1
  have hz3 : 1 ≤ z.im := hz.1.2.2
  have hzτ : z ≠ (τ : ℂ) := by simpa using hz.2
  have hclean := ofComplex_add_one_clean' τ hre him z hz1 hz2 hz3 hzτ
  have him1 : 0 < (z + 1).im := by simp [Complex.add_im]; linarith
  have hmem : {w : ℂ | 0 < w.im} ∈ 𝓝 (z + 1) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds him1
  have hsub : ContinuousAt (fun z : ℂ => z + 1) z := by fun_prop
  have hof : ContinuousAt (fun z : ℂ => UpperHalfPlane.ofComplex (z + 1)) z :=
    (Work.Asymptotics.continuousOn_ofComplex_of_im_pos.continuousAt hmem).comp
      (f := fun z : ℂ => z + 1) hsub
  have hg : ContinuousAt (fun z : ℂ => (τ, UpperHalfPlane.ofComplex (z + 1))) z :=
    ContinuousAt.prodMk continuousAt_const hof
  have hK : ContinuousAt
      (fun z : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z + 1))) z :=
    (Work.Asymptotics.continuousAt_Kfun_of_clean hd
      (p := (τ, UpperHalfPlane.ofComplex (z + 1))) hclean).comp
      (f := fun z : ℂ => (τ, UpperHalfPlane.ofComplex (z + 1))) hg
  have hker : ContinuousAt (fun z : ℂ => Work.Asymptotics.kerExp r z) z :=
    (continuous_kerExp' r).continuousAt
  exact (hK.mul hker).continuousWithinAt

/-- `f₂` is complex differentiable on the open half-strip `{-1 < Re < 0, 1 < Im}` away from the
pole `z = τ`. -/
private theorem differentiableAt_f2fun' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) :
    ∀ z : ℂ, -1 < z.re → z.re < 0 → 1 < z.im → z ≠ (τ : ℂ) →
      DifferentiableAt ℂ (f2fun ℓ d τ r) z := by
  intro z h0 h1 h2 hne
  have hclean := ofComplex_add_one_clean' τ hre him z (le_of_lt h0) (le_of_lt h1)
    (le_of_lt h2) hne
  have himpos : 0 < (z + 1).im := by simp [Complex.add_im]; linarith
  have hmd := Work.Residues.mdifferentiableAt_Kfun_snd ℓ d hd τ
    (UpperHalfPlane.ofComplex (z + 1)) hclean.symm
  have hbase : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w)) (z + 1) := by
    have h := UpperHalfPlane.mdifferentiableAt_iff.mp hmd
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos himpos] at h
    simpa only [Function.comp_def] using h
  have hsubd : DifferentiableAt ℂ (fun z : ℂ => z + 1) z := by fun_prop
  have hK := hbase.comp z hsubd
  have hker : DifferentiableAt ℂ (fun z : ℂ => Work.Asymptotics.kerExp r z) z := by
    unfold Work.Asymptotics.kerExp; fun_prop
  have hmain := hK.mul hker
  change DifferentiableAt ℂ (fun z : ℂ =>
    Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z + 1))
      * Work.Asymptotics.kerExp r z) z
  exact hmain

/-! ## The residue at the pole -/

/-- The residue limit of `f₂` at the pole `z = τ` (where the kernel's pole `τ + 1` sits). -/
private theorem tendsto_f2fun_residue' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) :
    Filter.Tendsto (fun z : ℂ => (z - (τ : ℂ)) * f2fun ℓ d τ r z)
      (nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ)
      (nhds (-(Work.Kernels.gaussTerm τ r) / (2 * Real.pi))) := by
  have hne : Work.Residues.jprime τ ≠ 0 :=
    Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two τ (by linarith)
  obtain ⟨-, hlim, -⟩ := Kfun_second_limits ℓ d hd τ hne
  have hshift := tendsto_shift_comp
    (F := fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w))
    (ζ₀ := (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)) (c := -(1 / (2 * Real.pi))) (d := 1) hlim
  have hctr : ((((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)) - 1 = (τ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  rw [hctr] at hshift
  have hshift' : Filter.Tendsto
      (fun z : ℂ => (z - (τ : ℂ)) * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z + 1)))
      (nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ) (nhds (-(1 / (2 * Real.pi)))) := by
    refine hshift.congr' ?_
    filter_upwards with z
    rfl
  have hker : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
      (nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ) (nhds (Work.Asymptotics.kerExp r (τ : ℂ))) :=
    ((continuous_kerExp' r).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hshift'.mul hker
  have hval : (-(1 / (2 * Real.pi))) * Work.Asymptotics.kerExp r (τ : ℂ)
      = -(Work.Kernels.gaussTerm τ r) / (2 * Real.pi) := by
    rw [← gaussTerm_eq_kerExp τ r]; ring
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards with z
  simp only [f2fun]
  ring

/-! ## The top edge of the shifted rectangle -/

/-- `‖e^{iπr²x}‖ = 1` for real `x`. -/
private lemma norm_kerExp_ofReal' (r x : ℝ) : ‖Work.Asymptotics.kerExp r (x : ℂ)‖ = 1 := by
  rw [Work.Asymptotics.kerExp,
    show (Real.pi : ℂ) * Complex.I * (r : ℂ) ^ 2 * (x : ℂ)
      = (((Real.pi * r ^ 2 * x : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The top edge tends to `0`.**  On the horizontal line `Im = R` of the half-strip the shifted
integrand is bounded by `C (1+R)^N e^{-π(r²-2)R}` (the Gaussian `e^{-πr²R}` beats the kernel's
`e^{2πR}` because `r² > 2`), so the edge integral tends to `0`. -/
private theorem tendsto_topEdge_f2fun' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im)
    {C N T : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hr : 2 < r ^ 2)
    (hbound : ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → T ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R)) :
    Filter.Tendsto
      (fun R : ℝ => ∫ x in (-1 : ℝ)..0, f2fun ℓ d τ r ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  set c : ℝ := Real.pi * (r ^ 2 - 2) with hc
  have hcpos : 0 < c := by rw [hc]; nlinarith [Real.pi_pos]
  have hpt : ∀ x R : ℝ, -1 ≤ x → x ≤ 0 → max T 1 ≤ R →
      ‖f2fun ℓ d τ r ((x : ℂ) + (R : ℂ) * Complex.I)‖
        ≤ C * (1 + R) ^ N * Real.exp (-c * R) := by
    intro x R hx1 hx2 hR
    have hRT : T ≤ R := le_trans (le_max_left T 1) hR
    have harg : ((x : ℂ) + (R : ℂ) * Complex.I) + 1
        = ((x + 1 : ℝ) : ℂ) + (R : ℂ) * Complex.I := by push_cast; ring
    have hK := hbound (x + 1) R (by linarith) (by linarith) hRT
    have hker : ‖Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)‖
        = Real.exp (-(Real.pi * r ^ 2 * R)) := by
      rw [kerExp_decomp r x R, norm_mul, norm_kerExp_ofReal', one_mul,
        Work.Asymptotics.norm_gaussWeight]
    rw [f2fun, norm_mul, hker, harg]
    calc ‖Work.Kernels.Kfun ℓ d τ
            (UpperHalfPlane.ofComplex (((x + 1 : ℝ) : ℂ) + (R : ℂ) * Complex.I))‖
          * Real.exp (-(Real.pi * r ^ 2 * R))
        ≤ (C * (1 + R) ^ N * Real.exp (2 * Real.pi * R)) * Real.exp (-(Real.pi * r ^ 2 * R)) :=
          mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
      _ = C * (1 + R) ^ N * Real.exp (-c * R) := by
          rw [hc, mul_assoc (C * (1 + R) ^ N) (Real.exp (2 * Real.pi * R))
                (Real.exp (-(Real.pi * r ^ 2 * R))), ← Real.exp_add]
          congr 1
          ring
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
  · filter_upwards [eventually_ge_atTop (max T 1)] with R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 0) (C := C * (1 + R) ^ N * Real.exp (-c * R))
      (f := fun x : ℝ => f2fun ℓ d τ r ((x : ℂ) + (R : ℂ) * Complex.I))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        exact hpt x R (le_of_lt hx.1) hx.2 hR)
    simpa using h

/-! ## Integrability of the two vertical rays -/

/-- The ray integrand `y ↦ f₂(a + iy)`, `a ∈ {0,-1}`, is integrable on `(1,∞)`: the kernel
parts `K(τ, ·)` are polynomially bounded on the strip and the Gaussian decays. -/
private theorem integrableOn_f2fun_ray' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = -1 / 2)
    (him : 12 ≤ τ.im) {C N T : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hr : 2 < r ^ 2)
    (hbound : ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → T ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R))
    (a : ℝ) (ha : a = 0 ∨ a = -1) :
    IntegrableOn (fun y : ℝ => f2fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi 1) := by
  set M : ℝ := max T 1 with hM
  have hM1 : 1 ≤ M := le_max_right T 1
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hc : 0 < Real.pi * (r ^ 2 - 2) := by nlinarith [Real.pi_pos]
  have hmem : ∀ y : ℝ, 1 ≤ y → ((a : ℂ) + (y : ℂ) * Complex.I)
      ∈ ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im} \ {(τ : ℂ)}) := by
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
  have hcontIcc : ContinuousOn (fun y : ℝ => f2fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc 1 M) :=
    (continuousOn_f2fun' ℓ d hd τ r hre him).comp
      (by fun_prop : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) (Set.Icc 1 M))
      (fun y hy => hmem y hy.1)
  have hInt_Ioc : IntegrableOn (fun y : ℝ => f2fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioc 1 M) :=
    (hcontIcc.integrableOn_compact (μ := volume) isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hcontIoi : ContinuousOn (fun y : ℝ => f2fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi M) :=
    (continuousOn_f2fun' ℓ d hd τ r hre him).comp
      (by fun_prop : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) (Set.Ioi M))
      (fun y hy => hmem y (le_trans hM1 (le_of_lt hy)))
  have hmeas : AEStronglyMeasurable (fun y : ℝ => f2fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
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
  have htail : IntegrableOn (fun y : ℝ => f2fun ℓ d τ r ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi M) := by
    refine Integrable.mono' hgi hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy1 : 1 ≤ y := le_trans hM1 (le_of_lt hy)
    have hyT : T ≤ y := le_trans (le_max_left T 1) (le_of_lt hy)
    have harg : ((a : ℂ) + (y : ℂ) * Complex.I) + 1
        = ((a + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by push_cast; ring
    have hK := hbound (a + 1) y (by rcases ha with h | h <;> rw [h] <;> norm_num)
      (by rcases ha with h | h <;> rw [h] <;> norm_num) hyT
    have hker : ‖Work.Asymptotics.kerExp r ((a : ℂ) + (y : ℂ) * Complex.I)‖
        = Real.exp (-(Real.pi * r ^ 2 * y)) := by
      rw [kerExp_decomp r a y, norm_mul, norm_kerExp_ofReal', one_mul,
        Work.Asymptotics.norm_gaussWeight]
    have hpow : (1 + y) ^ N ≤ 2 ^ N * y ^ N := by
      calc (1 + y) ^ N ≤ (2 * y) ^ N :=
            Real.rpow_le_rpow (by linarith) (by linarith) hN
        _ = 2 ^ N * y ^ N := Real.mul_rpow (by norm_num) (by linarith)
    rw [f2fun, norm_mul, hker, harg]
    calc ‖Work.Kernels.Kfun ℓ d τ
            (UpperHalfPlane.ofComplex (((a + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
          * Real.exp (-(Real.pi * r ^ 2 * y))
        ≤ (C * (1 + y) ^ N * Real.exp (2 * Real.pi * y)) * Real.exp (-(Real.pi * r ^ 2 * y)) :=
          mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
      _ = C * (1 + y) ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y) := by
          rw [mul_assoc (C * (1 + y) ^ N) (Real.exp (2 * Real.pi * y))
                (Real.exp (-(Real.pi * r ^ 2 * y))), ← Real.exp_add]
          congr 1
          ring
      _ ≤ C * (2 ^ N * y ^ N) * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (Real.exp_nonneg _)
      _ = (C * 2 ^ N) * y ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y) := by ring
  have hunion := hInt_Ioc.union htail
  rwa [Set.Ioc_union_Ioi_eq_Ioi hM1] at hunion

/-! ## The strip membership of the two lines -/

/-- `τ` on the lines `Re = ±1/2`, `Im ≥ 12` lies in the fundamental region `𝒟`. -/
private theorem mem_DomainD_of_line' (τ : UpperHalfPlane) (hre : τ.re = 1/2 ∨ τ.re = -1/2)
    (him : 12 ≤ τ.im) : τ ∈ Work.Asymptotics.DomainD := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hre with h | h <;> rw [h] <;> norm_num
  · rcases hre with h | h <;> rw [h] <;> norm_num
  · have h1 : (((τ:ℂ) - (1/2:ℂ)).im) = τ.im := by simp [Complex.sub_im]
    have h2 := Complex.abs_im_le_norm ((τ:ℂ) - (1/2:ℂ))
    rw [h1, abs_of_pos τ.im_pos] at h2
    linarith
  · have h1 : (((τ:ℂ) + (1/2:ℂ)).im) = τ.im := by simp [Complex.add_im]
    have h2 := Complex.abs_im_le_norm ((τ:ℂ) + (1/2:ℂ))
    rw [h1, abs_of_pos τ.im_pos] at h2
    linarith

/-! ## The contour shift -/

/-- **The contour-shift identity**, given the strip bound on the kernel. -/
private theorem shift_f2_neg_half_of_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2)
    (hre : τ.re = -1/2) (him : 12 ≤ τ.im) {C N T : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hbound : ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → T ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R)) :
    (∫ x in (-1:ℝ)..0, f2fun ℓ d τ r ((x:ℂ) + (1:ℂ)*Complex.I))
      = - Complex.I * Work.Kernels.gaussTerm τ r
        - Complex.I * (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
        + Complex.I * Work.Asymptotics.kerExp r (-1:ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t) := by
  have hcont := continuousOn_f2fun' ℓ d hd τ r hre him
  have hhol := differentiableAt_f2fun' ℓ d hd τ r hre him
  have hres := tendsto_f2fun_residue' ℓ d hd τ r him
  have htop := tendsto_topEdge_f2fun' ℓ d hd τ r him hC hN hr hbound
  have hintm := integrableOn_f2fun_ray' ℓ d hd τ r hre him hC hN hr hbound (-1) (Or.inr rfl)
  have hint0 := integrableOn_f2fun_ray' ℓ d hd τ r hre him hC hN hr hbound 0 (Or.inl rfl)
  have hkey := vertical_ray_shift (f := f2fun ℓ d τ r) (z₀ := (τ : ℂ))
      (c := -(Work.Kernels.gaussTerm τ r) / (2 * Real.pi))
      (x₁ := -1) (x₂ := 0) (y₁ := 1)
      (by rw [UpperHalfPlane.coe_re, hre]; norm_num)
      (by rw [UpperHalfPlane.coe_re, hre]; norm_num)
      (by rw [UpperHalfPlane.coe_im]; linarith)
      hcont hhol hres htop hintm hint0
  have hAp : (∫ y : ℝ in Set.Ioi 1, f2fun ℓ d τ r (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in Set.Ioi 1, Apfun ℓ d τ r y := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    exact f2fun_zero_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy])
  have hA0 : (∫ y : ℝ in Set.Ioi 1,
        f2fun ℓ d τ r (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = Work.Asymptotics.kerExp r (((-1 : ℝ) : ℂ)) * (∫ y : ℝ in Set.Ioi 1, A0fun ℓ d τ r y) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    exact f2fun_neg_one_ray ℓ d τ r y (by linarith [Set.mem_Ioi.mp hy])
  rw [hAp, hA0] at hkey
  have h2pi : 2 * (Real.pi : ℂ) * Complex.I * (-(Work.Kernels.gaussTerm τ r) / (2 * Real.pi))
      = -Complex.I * Work.Kernels.gaussTerm τ r := by
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    field_simp
  rw [h2pi] at hkey
  rw [kerExp_neg_one_coe'] at hkey
  have hspell : (∫ x in (-1:ℝ)..0, f2fun ℓ d τ r ((x:ℂ) + (1:ℂ)*Complex.I))
      = ∫ x in (-1:ℝ)..0, f2fun ℓ d τ r ((x:ℂ) + ((1:ℝ):ℂ)*Complex.I) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    congr 1
  rw [hspell]
  rw [← hkey]
  ring

/-- **The strip bound for the kernel in the shape used by the contour shift**, obtained from the
strip bound `Work.CKFinal.LineDecay.Kfun_bound_shift` for `τ` on the two critical lines. -/
private theorem f2_bound_strip' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = -1/2) (him : 12 ≤ τ.im) :
    ∃ C N T : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 < T ∧ ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → T ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R) := by
  obtain ⟨C, N, hC, hN, -, hb⟩ := Kfun_bound_shift ℓ d hd τ (Or.inr hre) him
  exact ⟨C, N, τ.im + 1, hC, hN, by linarith [τ.im_pos], hb⟩

/-! ## The contour-shift identity -/

theorem shift_f2_neg_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) (hre : τ.re = -1/2) (him : 12 ≤ τ.im) :
    (∫ x in (-1:ℝ)..0, f2fun ℓ d τ r ((x:ℂ) + (1:ℂ)*Complex.I))
      = - Complex.I * Work.Kernels.gaussTerm τ r
        - Complex.I * (∫ t in Set.Ioi 1, Apfun ℓ d τ r t)
        + Complex.I * Work.Asymptotics.kerExp r (-1:ℂ) * (∫ t in Set.Ioi 1, A0fun ℓ d τ r t) := by
  obtain ⟨C, N, T, hC, hN, _hT, hb⟩ := f2_bound_strip' ℓ d hd τ hre him
  exact shift_f2_neg_half_of_bound ℓ d hd τ hr hre him hC.le hN hb


end Work.CKFinal.LineDecay
