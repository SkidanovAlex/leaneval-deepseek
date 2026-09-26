/-
# Integrability of the kernel along the rays `Re z ∈ {-1, 1}` and on the axis

The contour shift of CKMRV §5.3 needs the two vertical sides of the shifted rectangle to be
integrable.  On the rays `Re z ∈ {-1, 1}` this follows from the ray growth bound
`Work.CKFinal.LineDecay.Kfun_bound_shift` (valid at every height `t ≥ 1`) together with the
Gaussian decay `e^{-πr²t}`, `r² > 2`; measurability comes from the continuity of the kernel on the
ray, which carries no coincidence.  The axis `Re z = 0` is handled by the cusp expansion
`Work.LayerCont.FarTail.tail_integrableOn_of_mem_DomainD` plus the model integrability
`Work.CKFinal.LineDecay.Aexp_gauss_integrable`.
-/
import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.Aexp_gauss_integrable
import Submission.Work.CKFinal.LineDecay.Kfun_bound_shift
import Submission.Work.CKFinal.LineDecay.Kfun_strip_bound
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.kerFormAux

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

/-- The `A0` tail integrand is integrable on `(1,∞)`. -/
theorem integrableOn_A0fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r^2) (hD : τ ∈ Work.Asymptotics.DomainD) :
    IntegrableOn (A0fun ℓ d τ r) (Set.Ioi 1) := by
  have h1 : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Work.Asymptotics.gaussWeight r t)
      (Set.Ioi 1) :=
    (Work.LayerCont.FarTail.tail_integrableOn_of_mem_DomainD ℓ d hd hD r).mono_set
      Set.Ioi_subset_Ici_self
  have h2 : IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ioi 1) :=
    (Aexp_gauss_integrable ℓ d τ hr).mono_set Set.Ioi_subset_Ici_self
  have h3 : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Work.Asymptotics.gaussWeight r t
      + Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
      (Set.Ioi 1) := h1.add h2
  refine h3.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [A0fun, Work.CKFinal.Kax_eq_Kaxis]
  ring


/-- **Non-coincidence on the rays `Re z ∈ {-1, 1}`.**  For `τ` on one of the two critical
lines and `1 ≤ t`, the point `±1 + i t` is never in the `SL(2,ℤ)`-orbit of `τ`: the orbit
points with `Im ≥ 1` and `-1 ≤ Re ≤ 1` are `τ`, `τ ± 1`, whose real parts are `±1/2`, `±3/2`. -/
theorem jInvariantFun_ne_ofComplex_ray (τ : UpperHalfPlane)
    (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (him : 12 ≤ τ.im) {a t : ℝ}
    (ha : a = -1 ∨ a = 1) (ht : 1 ≤ t) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun
      (UpperHalfPlane.ofComplex ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  intro hjeq
  have hzpos : 0 < ((a : ℂ) + (t : ℂ) * Complex.I).im := by simp; linarith
  have hzim : 1 ≤ ((a : ℂ) + (t : ℂ) * Complex.I).im := by simp; linarith
  have hzlo : -1 ≤ ((a : ℂ) + (t : ℂ) * Complex.I).re := by
    rcases ha with h | h <;> rw [h] <;> simp
  have hzhi : ((a : ℂ) + (t : ℂ) * Complex.I).re ≤ 1 := by
    rcases ha with h | h <;> rw [h] <;> simp
  have hcoe : ((UpperHalfPlane.ofComplex ((a : ℂ) + (t : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)
      = (a : ℂ) + (t : ℂ) * Complex.I :=
    congrArg (fun w : UpperHalfPlane => (w : ℂ))
      (UpperHalfPlane.ofComplex_apply_of_im_pos hzpos)
  have hc := ofComplex_mem_orbit τ hre him hzim hzlo hzhi hjeq
  rcases hc with h | h | h
  · have hw := hcoe.symm.trans (congrArg (fun w : UpperHalfPlane => (w : ℂ)) h)
    have h4 := congrArg Complex.re hw
    simp at h4
    rcases ha with h1 | h1 <;> rw [h1] at h4 <;>
      rcases hre with h2 | h2 <;> rw [h2] at h4 <;> norm_num at h4
  · have h2 : ((UpperHalfPlane.ofComplex ((a : ℂ) + (t : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)
        = (-1 : ℂ) + (τ : ℂ) := by
      rw [h, UpperHalfPlane.coe_vadd]; push_cast; ring
    have hw := hcoe.symm.trans h2
    have h4 := congrArg Complex.re hw
    simp at h4
    rcases ha with h1 | h1 <;> rw [h1] at h4 <;>
      rcases hre with h2 | h2 <;> rw [h2] at h4 <;> norm_num at h4
  · have h2 : ((UpperHalfPlane.ofComplex ((a : ℂ) + (t : ℂ) * Complex.I) : UpperHalfPlane) : ℂ)
        = (1 : ℂ) + (τ : ℂ) := by
      rw [h, UpperHalfPlane.coe_vadd]; push_cast; ring
    have hw := hcoe.symm.trans h2
    have h4 := congrArg Complex.re hw
    simp at h4
    rcases ha with h1 | h1 <;> rw [h1] at h4 <;>
      rcases hre with h2 | h2 <;> rw [h2] at h4 <;> norm_num at h4

/-- **Integrability of the kernel along the rays `Re z ∈ {-1, 1}`.**  The ray bound
`Work.CKFinal.LineDecay.Kfun_bound_shift` (valid at every height `t ≥ 1`) together with the
Gaussian decay `e^{-πr²t}` and `r² > 2` makes `t ↦ K^{(d)}(τ, ±1 + it) e^{-πr²t}` integrable on
`(1,∞)`; measurability comes from the continuity of the kernel on the ray, which carries no
coincidence. -/
theorem integrableOn_Kax_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2)
    (him : 12 ≤ τ.im) {a : ℝ} (ha : a = -1 ∨ a = 1) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ a t
      * Work.Asymptotics.gaussWeight r t) (Set.Ioi 1) := by
  obtain ⟨C, N, hC, hN, hray, _⟩ := Kfun_bound_shift ℓ d hd τ hre him
  have hc : 0 < Real.pi * (r ^ 2 - 2) := by nlinarith [Real.pi_pos]
  have hcontG : Continuous fun t : ℝ => Work.Asymptotics.gaussWeight r t := by
    unfold Work.Asymptotics.gaussWeight; fun_prop
  have hcontK : ContinuousOn (fun t : ℝ => Work.Kernels.Kfun ℓ d τ
      (UpperHalfPlane.ofComplex ((a : ℂ) + (t : ℂ) * Complex.I))) (Set.Ioi 1) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have hclean := jInvariantFun_ne_ofComplex_ray τ hre him ha ht1
    have hzpos : 0 < ((a : ℂ) + (t : ℂ) * Complex.I).im := by simp; linarith
    have hmem : {w : ℂ | 0 < w.im} ∈ 𝓝 ((a : ℂ) + (t : ℂ) * Complex.I) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzpos
    have hof : ContinuousAt
        (fun s : ℝ => UpperHalfPlane.ofComplex ((a : ℂ) + (s : ℂ) * Complex.I)) t :=
      (Work.Asymptotics.continuousOn_ofComplex_of_im_pos.continuousAt hmem).comp
        (f := fun s : ℝ => (a : ℂ) + (s : ℂ) * Complex.I) (by fun_prop)
    have hg : ContinuousAt (fun s : ℝ =>
        (τ, UpperHalfPlane.ofComplex ((a : ℂ) + (s : ℂ) * Complex.I))) t :=
      ContinuousAt.prodMk continuousAt_const hof
    have hKc : ContinuousAt (fun s : ℝ => Work.Kernels.Kfun ℓ d τ
        (UpperHalfPlane.ofComplex ((a : ℂ) + (s : ℂ) * Complex.I))) t :=
      (Work.Asymptotics.continuousAt_Kfun_of_clean hd
        (p := (τ, UpperHalfPlane.ofComplex ((a : ℂ) + (t : ℂ) * Complex.I))) hclean).comp
        (f := fun s : ℝ => (τ, UpperHalfPlane.ofComplex ((a : ℂ) + (s : ℂ) * Complex.I))) hg
    exact hKc.continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ => Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ a t
      * Work.Asymptotics.gaussWeight r t) (Set.Ioi 1) :=
    (hcontK.mul hcontG.continuousOn).congr (fun t ht => by
      rw [Pi.mul_apply]
      rw [Kax_eq_K_ofComplex _ τ a t (by linarith [Set.mem_Ioi.mp ht] : 0 < t)])
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ a t
      * Work.Asymptotics.gaussWeight r t) (volume.restrict (Set.Ioi 1)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hgi : Integrable (fun t : ℝ => (C * 2 ^ N) * t ^ N
      * Real.exp (-(Real.pi * (r ^ 2 - 2)) * t)) (volume.restrict (Set.Ioi 1)) := by
    have h0 : IntegrableOn (fun y : ℝ => y ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * y))
        (Set.Ioi 0) := by
      simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := N)
        (by linarith) (by norm_num) hc
    have h1 := h0.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    simpa [mul_assoc] using h1.const_mul (C * 2 ^ N)
  refine Integrable.mono' hgi hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := le_of_lt ht
  have ha' : a = -1 ∨ a = 0 ∨ a = 1 := by
    rcases ha with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hK := hray a ha' t ht1
  have hpow : (1 + t) ^ N ≤ 2 ^ N * t ^ N := by
    calc (1 + t) ^ N ≤ (2 * t) ^ N := Real.rpow_le_rpow (by linarith) (by linarith) hN
      _ = 2 ^ N * t ^ N := Real.mul_rpow (by norm_num) (by linarith)
  rw [norm_mul, Work.Asymptotics.norm_gaussWeight, Kax_eq_K_ofComplex _ τ a t
    (by linarith [Set.mem_Ioi.mp ht] : 0 < t)]
  calc ‖Work.Kernels.Kfun ℓ d τ
        (UpperHalfPlane.ofComplex ((a : ℂ) + (t : ℂ) * Complex.I))‖
        * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ (C * (1 + t) ^ N * Real.exp (2 * Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ = C * (1 + t) ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * t) := by
        rw [mul_assoc (C * (1 + t) ^ N) (Real.exp (2 * Real.pi * t))
            (Real.exp (-(Real.pi * r ^ 2 * t))), ← Real.exp_add]
        congr 1
        ring
    _ ≤ C * (2 ^ N * t ^ N) * Real.exp (-(Real.pi * (r ^ 2 - 2)) * t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) (Real.exp_nonneg _)
    _ = (C * 2 ^ N) * t ^ N * Real.exp (-(Real.pi * (r ^ 2 - 2)) * t) := by ring_nf

end Work.CKFinal.LineDecay
