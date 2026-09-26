import Mathlib
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two

/-!
# Pieces of the contour-shift identity `shift_f1_half`
-/

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

/-- The only point of the `SL(2,ℤ)`-orbit of `τ` (`Re τ = 1/2`, `Im τ ≥ 12`) that can have
`Re ∈ [-1,0]` and `Im ≥ 1` is `τ - 1`; equivalently, on the half-strip
`{0 ≤ Re ≤ 1, 1 ≤ Im}` the second variable `z - 1` of the kernel avoids the divisor except at
`z = τ`. -/
theorem ofComplex_sub_one_clean (τ : UpperHalfPlane) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → z ≠ (τ : ℂ) →
      Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1)) := by
  intro z h0 h1 h2 hne hjeq
  have hwimpos : 0 < (z - 1).im := by simp [Complex.sub_im]; linarith
  have hwim : 1 ≤ (z - 1).im := by simp [Complex.sub_im]; linarith
  have hwre : -1 ≤ (z - 1).re := by simp [Complex.sub_re]; linarith
  have hwre1 : (z - 1).re ≤ 1 := by simp [Complex.sub_re]; linarith
  have hcoe : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ) = z - 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwimpos]
  have hc := ofComplex_mem_orbit τ (Or.inl hre) him hwim hwre hwre1 hjeq
  rcases hc with h | h | h
  · have hc1 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ) = (τ : ℂ) := by
      rw [h]
    have hz : (z - 1) = (τ : ℂ) := hcoe.symm.trans hc1
    have hre' : (z - 1).re = τ.re := by rw [hz]; rfl
    have : (z - 1).re ≤ 0 := by simp [Complex.sub_re]; linarith
    linarith [hre', this, hre]
  · have hc2 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ)
        = (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hz : (z - 1) = (τ : ℂ) - 1 := by
      rw [hcoe.symm.trans hc2, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hzz : z = (τ : ℂ) := by
      have h' := congrArg (fun w : ℂ => w + 1) hz
      simpa using h'
    exact hne hzz
  · have hc3 : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ)
        = (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hz : (z - 1) = (τ : ℂ) + 1 := by
      rw [hcoe.symm.trans hc3, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hre' : (z - 1).re = τ.re + 1 := by rw [hz]; simp
    have : (z - 1).re ≤ 0 := by simp [Complex.sub_re]; linarith
    linarith [hre', this, hre]

/-- `kerExp r (i y) = gaussWeight r y`. -/
theorem kerExp_mul_I (r y : ℝ) :
    Work.Asymptotics.kerExp r ((y : ℂ) * Complex.I) = Work.Asymptotics.gaussWeight r y := by
  have h := kerExp_decomp r 0 y
  rw [show ((0:ℝ):ℂ) + (y : ℂ) * Complex.I = (y : ℂ) * Complex.I by push_cast; ring] at h
  rw [h]
  simp [Work.Asymptotics.kerExp]

/-- The integrand on the ray `Re = 0`: `f₁(0 + iy) = A_{-}(y)`. -/
theorem f1fun_zero_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r y : ℝ)
    (hy : 0 < y) :
    f1fun ℓ d τ r ((0 : ℂ) + (y : ℂ) * Complex.I) = Amfun ℓ d τ r y := by
  have harg : ((0 : ℂ) + (y : ℂ) * Complex.I) - 1 = ((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast; ring
  have hker : Work.Asymptotics.kerExp r ((0 : ℂ) + (y : ℂ) * Complex.I)
      = Work.Asymptotics.gaussWeight r y := by
    rw [show ((0:ℂ) + (y : ℂ) * Complex.I) = (y : ℂ) * Complex.I by ring]
    exact kerExp_mul_I r y
  simp only [f1fun, Amfun]
  rw [Kax_eq_K_ofComplex (K := Work.Kernels.Kfun ℓ d) τ (-1) y hy, harg, hker]

/-- The integrand on the ray `Re = 1`: `f₁(1 + iy) = e^{iπr²} A_0(y)`. -/
theorem f1fun_one_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r y : ℝ)
    (hy : 0 < y) :
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

end Work.CKFinal.LineDecay

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

/-- On the strip `{Re ∈ [-1,1], Im ≥ Im τ + 1}` the kernel's second variable `x + iR` avoids the
divisor `j = j τ`. -/
theorem ofComplex_strip_clean (τ : UpperHalfPlane) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) :
    ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)) := by
  intro x R hx1 hx2 hR hjeq
  have hRpos : 0 < R := by linarith [τ.im_pos]
  have hzim : 1 ≤ (((x : ℂ) + (R : ℂ) * Complex.I)).im := by simp; linarith
  have hzre : -1 ≤ (((x : ℂ) + (R : ℂ) * Complex.I)).re := by simp; linarith
  have hzre1 : (((x : ℂ) + (R : ℂ) * Complex.I)).re ≤ 1 := by simp; linarith
  have hcoe : ((UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)
      = (x : ℂ) + (R : ℂ) * Complex.I := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp; linarith)]
  have hc := ofComplex_mem_orbit τ (Or.inl hre) him hzim hzre hzre1 hjeq
  rcases hc with h | h | h
  · have hc1 : ((UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)
        = (τ : ℂ) := by rw [h]
    have hw : ((x : ℂ) + (R : ℂ) * Complex.I) = (τ : ℂ) := hcoe.symm.trans hc1
    have him_eq : (((x : ℂ) + (R : ℂ) * Complex.I)).im = τ.im := by rw [hw]; simp
    have : R = τ.im := by simpa using him_eq
    linarith
  · have hc2 : ((UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)
        = (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hw : ((x : ℂ) + (R : ℂ) * Complex.I) = (τ : ℂ) - 1 := by
      rw [hcoe.symm.trans hc2, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have him_eq : (((x : ℂ) + (R : ℂ) * Complex.I)).im = τ.im := by rw [hw]; simp
    have : R = τ.im := by simpa using him_eq
    linarith
  · have hc3 : ((UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)
        = (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by rw [h]
    have hw : ((x : ℂ) + (R : ℂ) * Complex.I) = (τ : ℂ) + 1 := by
      rw [hcoe.symm.trans hc3, UpperHalfPlane.coe_vadd]
      push_cast; ring
    have him_eq : (((x : ℂ) + (R : ℂ) * Complex.I)).im = τ.im := by rw [hw]; simp
    have : R = τ.im := by simpa using him_eq
    linarith

end Work.CKFinal.LineDecay

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

theorem continuous_kerExp (r : ℝ) : Continuous fun z : ℂ => Work.Asymptotics.kerExp r z := by
  unfold Work.Asymptotics.kerExp; fun_prop

/-- `z ↦ f₁(z) = K^{(d)}(τ, z-1) e^{iπr²z}` is continuous on the closed half-strip
`{0 ≤ Re ≤ 1, 1 ≤ Im}` away from the pole `z = τ`. -/
theorem continuousOn_f1fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) :
    ContinuousOn (f1fun ℓ d τ r)
      ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im} \ {(τ : ℂ)}) := by
  intro z hz
  have hz1 : 0 ≤ z.re := hz.1.1
  have hz2 : z.re ≤ 1 := hz.1.2.1
  have hz3 : 1 ≤ z.im := hz.1.2.2
  have hzτ : z ≠ (τ : ℂ) := by simpa using hz.2
  have hclean := ofComplex_sub_one_clean τ hre him z hz1 hz2 hz3 hzτ
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
pole `z = τ`. -/
theorem differentiableAt_f1fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (hre : τ.re = 1 / 2) (him : 12 ≤ τ.im) :
    ∀ z : ℂ, 0 < z.re → z.re < 1 → 1 < z.im → z ≠ (τ : ℂ) →
      DifferentiableAt ℂ (f1fun ℓ d τ r) z := by
  intro z h0 h1 h2 hne
  have hclean := ofComplex_sub_one_clean τ hre him z (le_of_lt h0) (le_of_lt h1) (le_of_lt h2) hne
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
  change DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
      * Work.Asymptotics.kerExp r z) z
  exact hmain

/-- The residue limit of `f₁` at the pole `z = τ` (where the kernel's pole `τ - 1` sits). -/
theorem tendsto_f1fun_residue (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (him : 12 ≤ τ.im) :
    Filter.Tendsto (fun z : ℂ => (z - (τ : ℂ)) * f1fun ℓ d τ r z)
      (nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ)
      (nhds (Work.Kernels.gaussTerm τ r / (2 * Real.pi))) := by
  have hne : Work.Residues.jprime τ ≠ 0 :=
    Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two τ (by linarith)
  obtain ⟨hlim, _, _⟩ := Kfun_second_limits ℓ d hd τ hne
  have hshift := tendsto_shift_comp
    (F := fun w : ℂ => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w))
    (ζ₀ := (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)) (c := 1 / (2 * Real.pi)) (d := -1) hlim
  have hctr : ((((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)) - (-1) = (τ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  rw [hctr] at hshift
  have hshift' : Filter.Tendsto
      (fun z : ℂ => (z - (τ : ℂ)) * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z - 1)))
      (nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ) (nhds (1 / (2 * Real.pi))) := by
    refine hshift.congr' ?_
    filter_upwards with z
    rfl
  have hker : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
      (nhdsWithin (τ : ℂ) {(τ : ℂ)}ᶜ) (nhds (Work.Asymptotics.kerExp r (τ : ℂ))) :=
    ((continuous_kerExp r).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hshift'.mul hker
  have hval : (1 / (2 * Real.pi)) * Work.Asymptotics.kerExp r (τ : ℂ)
      = Work.Kernels.gaussTerm τ r / (2 * Real.pi) := by
    rw [← gaussTerm_eq_kerExp τ r]; ring
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards with z
  simp only [f1fun]
  ring

end Work.CKFinal.LineDecay
