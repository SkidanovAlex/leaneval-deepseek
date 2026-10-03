import Mathlib

namespace Work.FatouL1

/-- Second order Taylor formula with the integral form of the remainder, for a function
`Φ : ℂ → ℂ` which is complex differentiable on a set `U` containing the segment `z + [0,1]·v`,
and an open convex domain. -/
theorem taylorTwoIntegral {Φ : ℂ → ℂ} {z v : ℂ} {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → z + t • v ∈ U)
    (hΦ : DifferentiableOn ℂ Φ U) :
    Φ (z + v) - Φ z - v * deriv Φ z
      = v ^ 2 * ∫ t in (0:ℝ)..1, ((1 - t : ℝ) : ℂ) * iteratedDeriv 2 Φ (z + t • v) := by
  -- `iteratedDeriv 2 = deriv (deriv ·)`, and differentiability propagates
  have hiter : iteratedDeriv 2 Φ = deriv (deriv Φ) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hdd : DifferentiableOn ℂ (deriv Φ) U := hΦ.deriv hU
  have hddd : DifferentiableOn ℂ (iteratedDeriv 2 Φ) U := by
    rw [hiter]; exact hdd.deriv hU
  -- continuity of the two derivatives along the segment
  have hgamma : ContinuousOn (fun s : ℝ => z + s • v) (Set.Icc (0:ℝ) 1) := by fun_prop
  have hmap : Set.MapsTo (fun s : ℝ => z + s • v) (Set.Icc (0:ℝ) 1) U := hseg
  have hcontF : ContinuousOn (fun s : ℝ => deriv Φ (z + s • v)) (Set.Icc (0:ℝ) 1) :=
    hdd.continuousOn.comp hgamma hmap
  have hcont2 : ContinuousOn (fun s : ℝ => iteratedDeriv 2 Φ (z + s • v)) (Set.Icc (0:ℝ) 1) :=
    hddd.continuousOn.comp hgamma hmap
  have hcont2v : ContinuousOn (fun s : ℝ => iteratedDeriv 2 Φ (z + s • v) * v)
      (Set.Icc (0:ℝ) 1) := hcont2.mul continuousOn_const
  -- chain rule: `t ↦ deriv Φ (z + t v)` has derivative `iteratedDeriv 2 Φ (z + t v) * v`
  have hF' : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => deriv Φ (z + s • v))
      (iteratedDeriv 2 Φ (z + x • v) * v) x := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have hd2 : DifferentiableAt ℂ (deriv Φ) (z + x • v) :=
      (hdd _ (hseg x hx)).differentiableAt (hU.mem_nhds (hseg x hx))
    have hg : HasDerivAt (fun s : ℝ => z + s • v) v x := by
      simpa using ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v : ℂ)).hasDerivAt
        (x := x)).const_add z
    have h1 := (hd2.hasDerivAt).scomp x hg
    rw [hiter]
    have h2 : HasDerivAt (fun s : ℝ => deriv Φ (z + s • v))
        (v • deriv (deriv Φ) (z + x • v)) x := by
      simpa only [Function.comp_def] using h1
    simpa [smul_eq_mul, mul_comm] using h2
  -- first order FTC along the segment
  have hFTC : (∫ t in (0:ℝ)..1, deriv Φ (z + t • v)) * v = Φ (z + v) - Φ z := by
    have h := intervalIntegral.integral_unitInterval_deriv_eq_sub (f := Φ) (f' := deriv Φ)
      (z₀ := z) (z₁ := v) hcontF
      (fun t ht => ((hΦ _ (hseg t ht)).differentiableAt (hU.mem_nhds (hseg t ht))).hasDerivAt)
    simpa [smul_eq_mul, mul_comm] using h
  have hIntF : IntervalIntegrable (fun x : ℝ => deriv Φ (z + x • v)) MeasureTheory.volume (0:ℝ) 1 :=
    hcontF.intervalIntegrable_of_Icc zero_le_one
  have hInt2v : IntervalIntegrable (fun x : ℝ => iteratedDeriv 2 Φ (z + x • v) * v)
      MeasureTheory.volume (0:ℝ) 1 := hcont2v.intervalIntegrable_of_Icc zero_le_one
  -- integration by parts with the weight `1 - x`
  let u : ℝ → ℂ := fun x => (1:ℂ) - (x:ℂ)
  let u' : ℝ → ℂ := fun _ => (-1:ℂ)
  let G : ℝ → ℂ := fun x => deriv Φ (z + x • v) - deriv Φ z
  let G' : ℝ → ℂ := fun x => iteratedDeriv 2 Φ (z + x • v) * v
  have hu' : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt u (u' x) x := by
    intro x hx
    show HasDerivAt (fun x : ℝ => (1:ℂ) - (x:ℂ)) (-1:ℂ) x
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_sub (1:ℂ)
  have hG' : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt G (G' x) x := by
    intro x hx
    exact (hF' x hx).sub_const _
  have hIBP : ∫ x in (0:ℝ)..1, u x * G' x = ∫ x in (0:ℝ)..1, G x := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0:ℝ)) (b := 1)
      (u := u) (u' := u') (v := G) (v' := G') hu' hG' intervalIntegrable_const hInt2v
    have h1 : u 1 * G 1 = 0 := by simp [u, G]
    have h2 : u 0 * G 0 = 0 := by simp [u, G]
    have h3 : (∫ x in (0:ℝ)..1, u' x * G x) = - ∫ x in (0:ℝ)..1, G x := by
      simp only [u']
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    rw [h1, h2, h3] at h
    simpa using h
  have hLHS : ∫ x in (0:ℝ)..1, u x * G' x
      = (∫ x in (0:ℝ)..1, u x * iteratedDeriv 2 Φ (z + x • v)) * v := by
    rw [show (∫ x in (0:ℝ)..1, u x * G' x)
        = ∫ x in (0:ℝ)..1, (u x * iteratedDeriv 2 Φ (z + x • v)) * v from by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [G']
      ring]
    rw [intervalIntegral.integral_mul_const]
  have hRHS : ∫ x in (0:ℝ)..1, G x = (∫ x in (0:ℝ)..1, deriv Φ (z + x • v)) - deriv Φ z := by
    rw [show (∫ x in (0:ℝ)..1, G x)
        = ∫ x in (0:ℝ)..1, (deriv Φ (z + x • v) - deriv Φ z) from rfl]
    rw [intervalIntegral.integral_sub hIntF intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  have hmain : (∫ x in (0:ℝ)..1, u x * iteratedDeriv 2 Φ (z + x • v)) * v
      = (∫ x in (0:ℝ)..1, deriv Φ (z + x • v)) - deriv Φ z := by
    rw [← hLHS, hIBP, hRHS]
  have hconv : (∫ x in (0:ℝ)..1, u x * iteratedDeriv 2 Φ (z + x • v))
      = ∫ x in (0:ℝ)..1, ((1 - x : ℝ) : ℂ) * iteratedDeriv 2 Φ (z + x • v) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [u]
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  have key : (∫ x in (0:ℝ)..1, u x * iteratedDeriv 2 Φ (z + x • v)) * v ^ 2
      = Φ (z + v) - Φ z - v * deriv Φ z := by
    calc (∫ x in (0:ℝ)..1, u x * iteratedDeriv 2 Φ (z + x • v)) * v ^ 2
        = ((∫ x in (0:ℝ)..1, u x * iteratedDeriv 2 Φ (z + x • v)) * v) * v := by ring
      _ = ((∫ x in (0:ℝ)..1, deriv Φ (z + x • v)) - deriv Φ z) * v := by rw [hmain]
      _ = (∫ x in (0:ℝ)..1, deriv Φ (z + x • v)) * v - deriv Φ z * v := by ring
      _ = (Φ (z + v) - Φ z) - deriv Φ z * v := by rw [hFTC]
      _ = Φ (z + v) - Φ z - v * deriv Φ z := by ring
  rw [← key, hconv]
  ring

end Work.FatouL1
