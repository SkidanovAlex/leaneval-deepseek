import Mathlib

namespace Work.Analysis.Complex

open Function Metric

/-- If `f` is circle integrable, then so is `z ↦ a * f z` (for a constant `a : ℂ`). -/
private lemma circleIntegrable_const_mul (a : ℂ) {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) : CircleIntegrable (fun z => a * f z) c R := by
  refine (circleIntegrable_congr ?_).mp
    (hf.continuousOn_mul (continuousOn_const : ContinuousOn (fun _ : ℂ => a) (sphere c |R|)))
  intro z hz
  rfl

/-- **Residue form of the argument principle for a finite product of powers.** For `d : ℂ → ℤ` with
finite support contained in the open disc of radius `ρ > 0`,
`∮_{|z|=ρ} logDeriv (∏ᶠ_u (· - u)^{d u}) = 2πi · ∑ᶠ_u d u`.  (This holds for arbitrary integer
exponents, so poles and zeros are both allowed.)

Available ingredients (Mathlib): `circleIntegral.integral_sub_inv_of_mem_ball`,
`circleIntegral.integral_sub_zpow_of_ne`, `circleIntegral.integral_fun_sum`,
`logDeriv_prod`, `logDeriv_fun_zpow`, `finprod_eq_prod_of_mulSupport_subset`,
`finsum_eq_sum_of_support_subset`. -/
theorem circleIntegral_logDeriv_finprod {d : ℂ → ℤ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : (Function.support d).Finite)
    (hsub : Function.support d ⊆ Metric.ball (0 : ℂ) ρ) :
    circleIntegral (fun z => logDeriv (fun w => ∏ᶠ u : ℂ, (w - u) ^ (d u)) z) 0 ρ =
      2 * (Real.pi : ℂ) * Complex.I * (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ)) := by
  -- The finitely supported product is really a finite product over `s = hd.toFinset`.
  set s : Finset ℂ := hd.toFinset with hs
  have hmem : ∀ u : ℂ, u ∈ s ↔ d u ≠ 0 := by
    intro u; rw [hs, Set.Finite.mem_toFinset, Function.mem_support]
  have hball : ∀ u ∈ s, ‖u‖ < ρ := by
    intro u hu
    have h1 : u ∈ Function.support d := Function.mem_support.mpr ((hmem u).mp hu)
    simpa [Metric.mem_ball, dist_eq_norm] using hsub h1
  have hprod : ∀ w : ℂ, (∏ᶠ u : ℂ, (w - u) ^ (d u)) = ∏ u ∈ s, (w - u) ^ (d u) := by
    intro w
    refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
    exact (hmem u).mpr fun h0 => Function.mem_mulSupport.mp hu (by rw [h0, zpow_zero])
  have hsupp : Function.support (fun u : ℂ => ((d u : ℤ) : ℂ)) ⊆ (s : Set ℂ) := by
    intro u hu
    refine (hmem u).mpr fun h0 => Function.mem_support.mp hu ?_
    rw [h0]; simp
  -- On the circle of radius `ρ` the log-derivative of the product is the weighted sum of `(z-u)⁻¹`.
  have hstep1 : Set.EqOn (fun z => logDeriv (fun w => ∏ᶠ u : ℂ, (w - u) ^ (d u)) z)
      (fun z => ∑ u ∈ s, ((d u : ℤ) : ℂ) * (z - u)⁻¹) (sphere 0 ρ) := by
    intro z hz
    change logDeriv (fun w => ∏ᶠ u : ℂ, (w - u) ^ (d u)) z = ∑ u ∈ s, ((d u : ℤ) : ℂ) * (z - u)⁻¹
    have hzne : ‖z‖ = ρ := by simpa using (mem_sphere_iff_norm.mp hz)
    have hzni : ∀ i ∈ s, z ≠ i := by
      intro i hi hzi
      have h1 := hball i hi
      rw [hzi] at hzne
      linarith
    have hne : ∀ i ∈ s, (z - i) ≠ 0 := fun i hi => sub_ne_zero.mpr (hzni i hi)
    have hlog : ∀ i ∈ s, logDeriv (fun w : ℂ => w - i) z = (z - i)⁻¹ := by
      intro i hi
      simp [logDeriv_apply, one_div]
    have hfun : (fun w : ℂ => ∏ᶠ u : ℂ, (w - u) ^ (d u))
        = fun w : ℂ => ∏ u ∈ s, (w - u) ^ (d u) :=
      funext hprod
    rw [hfun, logDeriv_fun_prod (f := fun u (w : ℂ) => (w - u) ^ (d u))
      (fun i hi => zpow_ne_zero _ (hne i hi))
      (fun i hi => differentiableAt_id.sub_const i |>.zpow (Or.inl (hne i hi)))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [logDeriv_fun_zpow (f := fun w : ℂ => w - i) (differentiableAt_id.sub_const i) (d i),
      hlog i hi]
  -- Integrability of each summand on the circle.
  have hci : ∀ u ∈ s, CircleIntegrable (fun z => ((d u : ℤ) : ℂ) * (z - u)⁻¹) 0 ρ := by
    intro u hu
    have hu' : u ∈ Metric.ball (0 : ℂ) ρ := hsub (Function.mem_support.mpr ((hmem u).mp hu))
    have hne : u ∉ sphere (0 : ℂ) ρ := by
      simp only [mem_sphere_iff_norm, sub_zero]
      exact ne_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hu')
    exact circleIntegrable_const_mul _
      (circleIntegrable_sub_inv_iff.2 (Or.inr (by simpa [abs_of_pos hρ] using hne)))
  -- Perform the integral term by term.
  have hmain : circleIntegral (fun z => logDeriv (fun w => ∏ᶠ u : ℂ, (w - u) ^ (d u)) z) 0 ρ
      = ∑ u ∈ s, ((d u : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [circleIntegral.integral_congr hρ.le hstep1]
    rw [circleIntegral.integral_fun_sum hci]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball
        (hsub (Function.mem_support.mpr ((hmem u).mp hu)))]
  rw [hmain, ← Finset.sum_mul, mul_comm (∑ u ∈ s, ((d u : ℤ) : ℂ)),
    finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℂ)) hsupp]

end Work.Analysis.Complex
