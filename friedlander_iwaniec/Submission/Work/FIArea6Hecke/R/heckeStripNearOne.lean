import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

/-- `heckeArch d m s = (4d/π)^s·Γ(s+|m|/2)` does not vanish for `re s > 1`. -/
theorem heckeArch_ne_zero_of_one_lt_re {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ}
    (hs : 1 < s.re) : Work.FITop4.Bridge.heckeArch d m s ≠ 0 := by
  unfold Work.FITop4.Bridge.heckeArch
  apply mul_ne_zero
  · rw [Complex.cpow_def_of_ne_zero ?_]
    · exact Complex.exp_ne_zero _
    · have heq : (4 * (((d : ℝ)) : ℂ) / ((Real.pi : ℝ) : ℂ) : ℂ)
          = (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) := by push_cast; ring
      rw [heq, Complex.ofReal_ne_zero]
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
  · apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.ofReal_re]
    have h := abs_nonneg (m : ℝ)
    linarith

/-- `heckeArch d m` is holomorphic at every point with `re s > 0`. -/
theorem heckeArch_differentiableAt_of_pos {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s := by
  have hbase : (4 * (((d : ℝ)) : ℂ) / ((Real.pi : ℝ) : ℂ) : ℂ) ≠ 0 := by
    have heq : (4 * (((d : ℝ)) : ℂ) / ((Real.pi : ℝ) : ℂ) : ℂ)
        = (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [heq, Complex.ofReal_ne_zero]
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have harg : ∀ k : ℕ, s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre : (s + (((|((m : ℝ))| / 2 : ℝ)) : ℂ)).re = -(k : ℝ) := by rw [hk]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    have h := abs_nonneg (m : ℝ)
    linarith
  unfold Work.FITop4.Bridge.heckeArch
  apply DifferentiableAt.mul
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl hbase)
  · exact (Complex.differentiableAt_Gamma _ harg).comp s
      (differentiableAt_id.add_const ((((|((m : ℝ))| / 2 : ℝ)) : ℂ)))

/-- **The identity theorem for the general weight `m : ℤ`.** -/
theorem Lam_eq_heckeArch_mul_of_one_lt_re {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    {m : ℤ} {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {s : ℂ} (hs : 1 < s.re) :
    Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
  set U : Set ℂ := {z : ℂ | 1 < z.re} with hU
  have hmem : ∀ {z : ℂ}, z ∈ U → 1 < z.re := fun {z} hz => by
    simpa only [hU, Set.mem_ofPred_eq] using hz
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := by
    have h := (convex_Ioi (1 : ℝ)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
    have h2 : (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' (Set.Ioi 1) = U := by
      ext z; simp [hU]
    rwa [h2] at h
  have hUpre : IsPreconnected U := hUconv.isPreconnected
  have hf : AnalyticOnNhd ℂ Lam U :=
    ((hAn.mono (Set.subset_univ U)).differentiableOn).analyticOnNhd hUopen
  have hg : AnalyticOnNhd ℂ
      (fun z => Work.FITop4.Bridge.heckeArch d m z *
        Work.FIArea5.S16Hecke.heckeLSeries chi m z) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    refine DifferentiableOn.mul ?_ ?_
    · intro z hz
      exact (heckeArch_differentiableAt_of_pos hd m
        (by have := hmem hz; linarith)).differentiableWithinAt
    · intro z hz
      refine (LSeries_differentiableOn (Work.FIArea5.S16Hecke.heckeLam chi m) z ?_).mono ?_
      · show LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (z.re : EReal)
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr (hmem hz))
      · intro w hw
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr (hmem hw))
  have hz₀ : (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ) ∈ U := by
    simp only [hU, Set.mem_ofPred_eq, Complex.ofReal_re]
    have h := abs_nonneg (m : ℝ)
    linarith
  have hev : Lam =ᶠ[𝓝 (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ)]
      (fun z => Work.FITop4.Bridge.heckeArch d m z *
        Work.FIArea5.S16Hecke.heckeLSeries chi m z) := by
    refine Filter.eventually_of_mem
      (show {z : ℂ | 1 + |(m : ℝ)| / 2 < z.re} ∈ 𝓝 _ from ?_) ?_
    · apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
      have h := abs_nonneg (m : ℝ)
      linarith
    · intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      exact hagr z hz
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hUpre hz₀ hev) hs

/-- **Uniform form of the Euler-product inverse bound.** -/
theorem heckeLSeries_inv_bound_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ (chi : GaussianInt → ℂ) (k : ℤ),
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
        ‖(Work.FIArea5.S16Hecke.heckeLSeries chi k s)⁻¹‖ ≤ K / (s.re - 1) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FIArea5.S16Hecke.heckeB_finset_prod_bound
  refine ⟨C0, hC0pos, ?_⟩
  intro chi k h1 hmul hb s hs1 hs2
  have hsigpos : 0 < s.re := by linarith
  have hGp_mult : Multipliable (fun p : Nat.Primes => Work.FIArea5.S16Hecke.heckeGp chi k p s) :=
    Work.FIArea5.S16Hecke.multipliable_heckeGp chi k s hmul hb hs1
  have hEq : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeGp chi k p s)
      = (Work.FIArea5.S16Hecke.heckeLSeries chi k s)⁻¹ :=
    Work.FIArea5.S16Hecke.tprod_heckeGp_eq_inv chi k s hmul h1 hb hs1
  have hnorm : ‖(Work.FIArea5.S16Hecke.heckeLSeries chi k s)⁻¹‖
      = ∏' p : Nat.Primes, ‖Work.FIArea5.S16Hecke.heckeGp chi k p s‖ := by
    rw [← hEq, Multipliable.norm_tprod hGp_mult]
  rw [hnorm]
  refine Multipliable.tprod_le_of_prod_le hGp_mult.norm (fun t => ?_)
  have h1' : ∏ p ∈ t, ‖Work.FIArea5.S16Hecke.heckeGp chi k p s‖
      ≤ ∏ p ∈ t, Work.FIArea5.S16Hecke.heckeB p s.re :=
    Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      (fun p _ => Work.FIArea5.S16Hecke.norm_heckeGp_le chi k p s hmul hb hsigpos)
  have h2' : ∏ p ∈ t, Work.FIArea5.S16Hecke.heckeB p s.re ≤ C0 / (s.re - 1) :=
    hC0 s.re hs1 hs2 t
  linarith

/-- **The near-one anchor bound** `StripNearOne ε`. -/
theorem heckeStripNearOne (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    Work.FIArea6Hecke.StripNearOne ε := by
  obtain ⟨K, hKpos, hK⟩ := heckeLSeries_inv_bound_uniform
  refine ⟨K, hKpos, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hs1 hs2
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hid : Lam s = Work.FITop4.Bridge.heckeArch d m s *
      Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
    Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hs1
  have hArch : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
    heckeArch_ne_zero_of_one_lt_re hd m hs1
  have hLval : Work.FIArea6Hecke.Lval d m Lam s =
      Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
    rw [Work.FIArea6Hecke.Lval, hid]
    exact mul_div_cancel_left₀ (Work.FIArea5.S16Hecke.heckeLSeries chi m s) hArch
  rw [hLval]
  exact hK chi m h1 hmul hb s hs1 hs2

end

end Work.FIArea6Hecke.R
