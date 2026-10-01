import Mathlib

open scoped Interval Topology BigOperators

namespace Work.LinnikAreas.A5

/-- Change of variables `t = exp (u * log q)` in the interval integral
`∫_{1}^{q^{x₀}} t ^ (-(1 - lam / log q)) * f (log t / log q) dt`.

Indeed with `t = q^u` we have `dt = (log q) q^u du` and
`t ^ (-(1 - lam / log q)) = exp (u * log q * (-(1 - lam / log q)))
= exp (-u * log q + lam * u)`, so the product with `q^u = exp (u * log q)`
collapses to `log q * exp (lam * u)`. -/
theorem integral_rpow_log_subst (x₀ lam : ℝ) (hx₀ : 0 < x₀) {q : ℝ} (hq : 1 < q)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) x₀)) :
    (∫ t in (1:ℝ)..q^x₀, t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
      = Real.log q * ∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hLpos : 0 < Real.log q := Real.log_pos hq
  have hφ0 : Real.exp (0 * Real.log q) = 1 := by simp
  have hφx : Real.exp (x₀ * Real.log q) = q ^ x₀ := by
    rw [Real.rpow_def_of_pos hq0 x₀]
    congr 1; ring
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) x₀,
      HasDerivAt (fun u : ℝ => Real.exp (u * Real.log q))
        (Real.exp (u * Real.log q) * Real.log q) u := by
    intro u _
    simpa using ((hasDerivAt_id u).mul_const (Real.log q)).exp
  have hderiv_cont : ContinuousOn (fun u : ℝ => Real.exp (u * Real.log q) * Real.log q)
      (Set.uIcc (0:ℝ) x₀) :=
    (((Real.continuous_exp.comp (continuous_id.mul_const (Real.log q))).mul_const
      (Real.log q))).continuousOn
  have hgcont : ContinuousOn
      (fun t : ℝ => t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
      (Set.Icc (1:ℝ) (q^x₀)) := by
    have hpos : ∀ t ∈ Set.Icc (1:ℝ) (q^x₀), t ≠ 0 :=
      fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    have h1 : ContinuousOn (fun t : ℝ => t ^ (-(1 - lam / Real.log q)))
        (Set.Icc (1:ℝ) (q^x₀)) :=
      ContinuousOn.rpow_const continuous_id.continuousOn (fun t ht => Or.inl (hpos t ht))
    have h2 : ContinuousOn (fun t : ℝ => f (Real.log t / Real.log q))
        (Set.Icc (1:ℝ) (q^x₀)) := by
      have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc (1:ℝ) (q^x₀)) :=
        Real.continuousOn_log.mono (fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hpos t ht)
      have hmem : ∀ t ∈ Set.Icc (1:ℝ) (q^x₀),
          Real.log t / Real.log q ∈ Set.Icc (0:ℝ) x₀ := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
        constructor
        · exact div_nonneg (Real.log_nonneg ht.1) hLpos.le
        · rw [div_le_iff₀ hLpos]
          have hle : Real.log t ≤ Real.log (q^x₀) := Real.log_le_log ht0 ht.2
          rwa [Real.log_rpow hq0 x₀] at hle
      exact hf.comp (hlog.div_const (Real.log q)) hmem
    exact h1.mul h2
  have hsub_img : (fun u : ℝ => Real.exp (u * Real.log q)) '' Set.uIcc (0:ℝ) x₀
      ⊆ Set.Icc (1:ℝ) (q^x₀) := by
    rintro t ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le hx₀.le] at hu
    constructor
    · exact Real.one_le_exp (mul_nonneg hu.1 hLpos.le)
    · rw [← hφx]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu.2 hLpos.le)
  have hpt : ∀ u ∈ Set.uIcc (0:ℝ) x₀,
      ((fun t : ℝ => t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q)) ∘
          (fun u : ℝ => Real.exp (u * Real.log q))) u * (Real.exp (u * Real.log q) * Real.log q)
      = Real.log q * (Real.exp (lam * u) * f u) := by
    intro u _
    have hpos : 0 < Real.exp (u * Real.log q) := Real.exp_pos _
    have hdiv : u * Real.log q / Real.log q = u := by field_simp
    have hexp : Real.exp (u * Real.log q * (-(1 - lam / Real.log q)))
        * Real.exp (u * Real.log q) = Real.exp (lam * u) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    simp only [Function.comp_apply, Real.rpow_def_of_pos hpos, Real.log_exp, hdiv]
    have h1 : Real.exp (u * Real.log q * (-(1 - lam / Real.log q))) * f u
          * (Real.exp (u * Real.log q) * Real.log q)
        = (Real.exp (u * Real.log q * (-(1 - lam / Real.log q)))
            * Real.exp (u * Real.log q)) * (f u * Real.log q) := by ring
    rw [h1, hexp]; ring
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := (0:ℝ)) (b := x₀)
    (f := fun u : ℝ => Real.exp (u * Real.log q))
    (f' := fun u : ℝ => Real.exp (u * Real.log q) * Real.log q)
    (g := fun t : ℝ => t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
    hderiv hderiv_cont (hgcont.mono hsub_img)
  have hsub' : (∫ t in (1:ℝ)..q^x₀, t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
      = ∫ u in (0:ℝ)..x₀,
          (fun t : ℝ => t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
            (Real.exp (u * Real.log q)) * (Real.exp (u * Real.log q) * Real.log q) := by
    rw [hφ0, hφx] at hsub
    simpa [Function.comp_apply] using hsub.symm
  calc (∫ t in (1:ℝ)..q^x₀, t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
      = ∫ u in (0:ℝ)..x₀,
          (fun t : ℝ => t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
            (Real.exp (u * Real.log q)) * (Real.exp (u * Real.log q) * Real.log q) := hsub'
    _ = ∫ u in (0:ℝ)..x₀, Real.log q * (Real.exp (lam * u) * f u) :=
        intervalIntegral.integral_congr hpt
    _ = Real.log q * ∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u :=
        intervalIntegral.integral_const_mul _ _

end Work.LinnikAreas.A5
