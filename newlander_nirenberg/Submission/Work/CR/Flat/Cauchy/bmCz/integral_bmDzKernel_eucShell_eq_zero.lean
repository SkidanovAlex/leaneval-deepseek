import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

/-!
# Vanishing mean of `∂_{z_k}(bmKernel j)` over an annulus

The kernel `∂_{z_k}(bmKernel j) x = -n \bar x_j \bar x_k ‖x‖^{-2n-2}` is invariant under the
rotation `x ↦ i·x` of `ℂⁿ` up to the sign `-1`.  Since `x ↦ i·x` is a measure preserving
bijection of `ℂⁿ` (the product measure of Lebesgue measure on the coordinates) which maps every
Euclidean annulus centred at the origin to itself, the integral of the kernel over such an
annulus equals its own negative, hence vanishes.

The whole argument is carried out on the product space `Fin n → ℂ` with `volume` the product of
`volume` on `ℂ`, for which the change of variables is componentwise.
-/

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

/-- The quarter turn `u ↦ i·u` as a real linear isometry equivalence of `ℂ`. -/
def rotI : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun u := Complex.I * u
  invFun u := -Complex.I * u
  left_inv u := by
    show -Complex.I * (Complex.I * u) = u
    rw [← mul_assoc, neg_mul, Complex.I_mul_I]; simp
  right_inv u := by
    show Complex.I * (-Complex.I * u) = u
    rw [← mul_assoc, mul_neg, Complex.I_mul_I]; simp
  map_add' u v := by
    show Complex.I * (u + v) = Complex.I * u + Complex.I * v
    ring
  map_smul' c u := by
    show Complex.I * (c • u) = c • (Complex.I * u)
    rw [Complex.real_smul, Complex.real_smul]
    ring
  norm_map' u := by
    show ‖Complex.I * u‖ = ‖u‖
    rw [norm_mul, Complex.norm_I, one_mul]

@[simp] lemma rotI_apply (u : ℂ) : rotI u = Complex.I * u := rfl

/-- Multiplication by `i` preserves Lebesgue measure on `ℂ`. -/
lemma map_mul_I_volume : (volume : Measure ℂ).map (fun z => Complex.I * z) = volume := by
  have h : (fun z : ℂ => Complex.I * z) = ⇑rotI := rfl
  rw [h]
  exact (LinearIsometryEquiv.measurePreserving rotI).map_eq

/-- Componentwise multiplication by `i` preserves the product Lebesgue measure on `ℂⁿ`. -/
lemma map_smul_I_volume {n : ℕ} :
    (volume : Measure (Fin n → ℂ)).map (fun x => Complex.I • x) = volume := by
  have hfun : (fun x : Fin n → ℂ => Complex.I • x) = (fun x i => Complex.I * x i) := by
    funext x i; simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  have key := Measure.pi_map_pi (μ := fun _ : Fin n => (volume : Measure ℂ))
    (f := fun (_ : Fin n) (z : ℂ) => Complex.I * z)
    (hμ := fun i => by rw [map_mul_I_volume]; infer_instance)
    (fun _ => (continuous_const.mul continuous_id).aemeasurable)
  rw [MeasureTheory.volume_pi, key]
  simp only [map_mul_I_volume]

/-- The Euclidean norm on `ℂⁿ` is invariant under the rotation `x ↦ i·x`. -/
lemma eucNorm_smul_I {n : ℕ} (x : Fin n → ℂ) : eucNorm (Complex.I • x) = eucNorm x := by
  simp only [eucNorm, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]

/-- The kernel `∂_{z_k}(bmKernel j)` changes sign under the rotation `x ↦ i·x`. -/
lemma bmDzKernel_smul_I {n : ℕ} (k j : Fin n) (x : Fin n → ℂ) :
    bmDzKernel k j (Complex.I • x) = - bmDzKernel k j x := by
  simp only [bmDzKernel, eucNorm_smul_I, Pi.smul_apply, smul_eq_mul, Complex.conj_I, map_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The kernel `∂_{z_k}(bmKernel j)` has vanishing mean over any annulus avoiding the origin. -/
theorem integral_bmDzKernel_eucShell_eq_zero {n : ℕ} {k j : Fin n} {ε ρ : ℝ} (hε : 0 < ε) :
    ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ, Work.CR.Flat.Cauchy.bmDzKernel k j x = 0 := by
  classical
  -- the componentwise quarter turn, packaged as a measurable equivalence
  let e : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
    MeasurableEquiv.piCongrRight (fun _ : Fin n => rotI.toMeasurableEquiv)
  have hcoe : ⇑e = fun x : Fin n → ℂ => Complex.I • x := by
    funext x i
    simp [e, MeasurableEquiv.piCongrRight, rotI, Pi.smul_apply, smul_eq_mul]
  have hmap : Measure.map (⇑e) volume = volume := by
    rw [hcoe]; exact map_smul_I_volume
  -- the annulus is invariant
  have hpre : ⇑e ⁻¹' Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ
      = Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ := by
    ext x
    simp only [Set.mem_preimage, mem_eucShell]
    rw [hcoe, eucNorm_smul_I]
  -- the kernel changes sign
  have hpt : ∀ x : Fin n → ℂ,
      Work.CR.Flat.Cauchy.bmDzKernel k j (⇑e x) = - Work.CR.Flat.Cauchy.bmDzKernel k j x := by
    intro x; rw [hcoe]; exact bmDzKernel_smul_I k j x
  -- change of variables in the integral
  have hsub := (e.measurableEmbedding).setIntegral_map (μ := volume)
    (Work.CR.Flat.Cauchy.bmDzKernel k j) (Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ)
  rw [hmap, hpre] at hsub
  -- `∫ = ∫ (f ∘ e) = ∫ (-f) = -∫`, so `∫ = -∫`, forcing `∫ = 0`
  have hsym : ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
        Work.CR.Flat.Cauchy.bmDzKernel k j x
      = - ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
        Work.CR.Flat.Cauchy.bmDzKernel k j x := by
    calc ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
            Work.CR.Flat.Cauchy.bmDzKernel k j x
        = ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
            Work.CR.Flat.Cauchy.bmDzKernel k j (⇑e x) := hsub
      _ = ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
            - Work.CR.Flat.Cauchy.bmDzKernel k j x :=
            setIntegral_congr_fun (measurableSet_eucShell (n := n) ε ρ) (fun x _ => hpt x)
      _ = - ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
            Work.CR.Flat.Cauchy.bmDzKernel k j x := integral_neg _
  have h2 : (∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
        Work.CR.Flat.Cauchy.bmDzKernel k j x) * 2 = 0 := by
    have h3 : (∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
          Work.CR.Flat.Cauchy.bmDzKernel k j x)
        + (∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
          Work.CR.Flat.Cauchy.bmDzKernel k j x) = 0 := by
      nth_rewrite 1 [hsym]; abel
    rw [show (∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
          Work.CR.Flat.Cauchy.bmDzKernel k j x) * 2
        = (∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
            Work.CR.Flat.Cauchy.bmDzKernel k j x)
          + (∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) ε ρ,
            Work.CR.Flat.Cauchy.bmDzKernel k j x) from by ring]
    exact h3
  exact (mul_eq_zero.mp h2).resolve_right (by norm_num)

end Work.CR.Flat.Cauchy.bmCz
