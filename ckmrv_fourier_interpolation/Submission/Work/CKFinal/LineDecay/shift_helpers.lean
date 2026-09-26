import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.Asymptotics.NonCoincidence.jInvariantFun_ne_imagAxis_of_re_notInt_im_gt_half
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.CKFinal.LineDecay.orbit_classification

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-! # Shared helpers for the contour-shift identities of `LineDecay -/

/-- `sinSq = sinSqC` (the two definitions are syntactically identical). -/
theorem sinSq_eq_sinSqC (r : ℝ) : Work.Asymptotics.sinSq r = Work.Asymptotics.sinSqC r := rfl

/-! ## Elementary: the exponential form of `sinSqC` -/

theorem sinSqC_eq_two_sub_exp (r : ℝ) :
    Work.Asymptotics.sinSqC r
      = 2 - Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2)
          - Complex.exp (-(Real.pi * Complex.I * (r : ℂ) ^ 2)) := by
  rw [Work.Asymptotics.sinSqC, Complex.sin_sq]
  rw [show (4 : ℂ) * (1 - Complex.cos (Real.pi * (r:ℂ)^2 / 2) ^ 2)
      = 2 - 2 * Complex.cos (2 * (Real.pi * (r:ℂ)^2 / 2)) by
    rw [Complex.cos_two_mul]; ring]
  rw [show (2 : ℂ) * (Real.pi * (r:ℂ)^2 / 2) = Real.pi * (r:ℂ)^2 by ring]
  rw [Complex.two_cos]
  ring_nf

/-! ## Helper lemmas -/

/-- Composition of a residue limit with a shift of the variable. -/
theorem tendsto_shift_comp {F : ℂ → ℂ} {ζ₀ c d : ℂ}
    (h : Filter.Tendsto (fun ζ => (ζ - ζ₀) * F ζ) (nhdsWithin ζ₀ {ζ₀}ᶜ) (nhds c)) :
    Filter.Tendsto (fun z => (z - (ζ₀ - d)) * F (z + d))
      (nhdsWithin (ζ₀ - d) {(ζ₀ - d)}ᶜ) (nhds c) := by
  have hmap : Filter.Tendsto (fun z : ℂ => z + d) (nhdsWithin (ζ₀ - d) {(ζ₀ - d)}ᶜ)
      (nhdsWithin ζ₀ {ζ₀}ᶜ) := by
    have hbase : Filter.Tendsto (fun z : ℂ => z + d) (nhds (ζ₀ - d)) (nhds ζ₀) := by
      have hc : Continuous fun z : ℂ => z + d := by fun_prop
      simpa using hc.tendsto (ζ₀ - d)
    refine tendsto_nhdsWithin_iff.mpr ⟨hbase.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    intro hh
    exact hz (by rw [← hh]; ring)
  have := h.comp hmap
  refine this.congr' ?_
  filter_upwards with z
  simp only [Function.comp_apply]
  ring_nf

/-- `Kax K τ x t` at `t > 0` is `K(τ, ofComplex (x + t·I))`. -/
theorem Kax_eq_K_ofComplex (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (x t : ℝ) (ht : 0 < t) :
    Work.CKFinal.Kax K τ x t = K τ (UpperHalfPlane.ofComplex ((x:ℂ) + (t:ℂ)*Complex.I)) := by
  rw [Work.CKFinal.Kax, dif_pos ht]
  congr 1
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_vadd, Work.Kernels.imagAxis]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)]

/-- The exponential factor factors over real and imaginary parts. -/
theorem kerExp_decomp (rr x y : ℝ) :
    Work.Asymptotics.kerExp rr ((x:ℂ) + (y:ℂ)*Complex.I)
      = Work.Asymptotics.kerExp rr (x:ℂ) * Work.Asymptotics.gaussWeight rr y := by
  have harg : (Real.pi:ℂ) * Complex.I * (rr:ℂ)^2 * ((x:ℂ) + (y:ℂ)*Complex.I)
      = (Real.pi:ℂ) * Complex.I * (rr:ℂ)^2 * (x:ℂ)
        + (-((Real.pi:ℂ) * (rr:ℂ)^2 * (y:ℂ))) := by
    have h1 : (Real.pi:ℂ) * Complex.I * (rr:ℂ)^2 * ((x:ℂ) + (y:ℂ)*Complex.I)
        = (Real.pi:ℂ) * Complex.I * (rr:ℂ)^2 * (x:ℂ)
          + (Real.pi:ℂ) * (rr:ℂ)^2 * (y:ℂ) * (Complex.I * Complex.I) := by ring
    rw [h1, Complex.I_mul_I]; ring
  rw [Work.Asymptotics.kerExp, Work.Asymptotics.kerExp, Work.Asymptotics.gaussWeight, harg,
    Complex.exp_add]

/-- The exponential factor in the form used by `P2`. -/
theorem kerExp_eq_phase (rr : ℝ) (z : ℂ) :
    Work.Asymptotics.kerExp rr z = Complex.exp ((((Real.pi * rr^2 : ℝ) : ℂ)) * Complex.I * z) := by
  simp only [Work.Asymptotics.kerExp]
  congr 1
  push_cast; ring

/-- `gaussTerm τ r` is `kerExp r τ`. -/
theorem gaussTerm_eq_kerExp (τ : UpperHalfPlane) (r : ℝ) :
    Work.Kernels.gaussTerm τ r = Work.Asymptotics.kerExp r (τ : ℂ) := by
  simp only [Work.Kernels.gaussTerm, Work.Asymptotics.kerExp]
  congr 1
  ring

/-- The only points of the `SL(2,ℤ)`-orbit of `τ` (`Re τ = ±1/2`, `Im τ ≥ 12`) with
`Re ∈ [-1,1]` and `Im ≥ 1` that lie at `ofComplex z` are `τ, τ-1, τ+1`. -/
theorem ofComplex_mem_orbit (τ : UpperHalfPlane) (hre : τ.re = 1/2 ∨ τ.re = -1/2)
    (him : 12 ≤ τ.im) {z : ℂ} (hz1 : 1 ≤ z.im) (hz2 : -1 ≤ z.re) (hz3 : z.re ≤ 1)
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    UpperHalfPlane.ofComplex z = τ ∨ UpperHalfPlane.ofComplex z = ((-1:ℝ)+ᵥτ)
      ∨ UpperHalfPlane.ofComplex z = ((1:ℝ)+ᵥτ) := by
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
  have h' : γ⁻¹ • τ = UpperHalfPlane.ofComplex z := by
    rw [← hγ, inv_smul_smul]
  have hz1' : (1:ℝ) ≤ (UpperHalfPlane.ofComplex z).im := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by linarith : 0 < z.im)]; exact hz1
  have hz2' : (-1:ℝ) ≤ (UpperHalfPlane.ofComplex z).re := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by linarith : 0 < z.im)]; exact hz2
  have hz3' : (UpperHalfPlane.ofComplex z).re ≤ 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by linarith : 0 < z.im)]; exact hz3
  have hc := orbit_classification τ hre him γ⁻¹ (by rw [h']; exact hz1')
    (by rw [h']; exact hz2') (by rw [h']; exact hz3')
  rwa [h'] at hc


/-- The shifted contour integrand for the `K(τ, ·-1)` ray. -/
def f1fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℂ → ℂ :=
  fun z => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z - 1)) * Work.Asymptotics.kerExp r z

/-- The shifted contour integrand for the `K(τ, ·+1)` ray. -/
def f2fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℂ → ℂ :=
  fun z => Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (z + 1)) * Work.Asymptotics.kerExp r z

/-- The tail integrand of the `K(τ, ·)` ray. -/
def A0fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℝ → ℂ :=
  fun t => Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ 0 t * Work.Asymptotics.gaussWeight r t

/-- The tail integrand of the `K(τ, ·-1)` ray. -/
def Amfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℝ → ℂ :=
  fun t => Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ (-1) t * Work.Asymptotics.gaussWeight r t

/-- The tail integrand of the `K(τ, ·+1)` ray. -/
def Apfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℝ → ℂ :=
  fun t => Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ 1 t * Work.Asymptotics.gaussWeight r t

/-- The barycentre of the `(0,1]`-piece of the `K(τ, ·)` ray. -/
def Blow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, A0fun ℓ d τ r t

end Work.CKFinal.LineDecay
