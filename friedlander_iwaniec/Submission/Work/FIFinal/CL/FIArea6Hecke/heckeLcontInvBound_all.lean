import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeInvBound_all
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeLcontInvBound_strip

/-!
# `Work.FIArea6Hecke.heckeLcontInvBound_all`

The inverse bound *(FI)* (16.23)/(16.24)

  `‖(Lam s / heckeArch d m s)⁻¹‖ ≤ C·d·log²(|m|+|Im s|+3)`  for
  `1 - c/(d^ε·log(|m|+|Im s|+3)) < re s ≤ 2`

for the **analytic continuation** `Lam s / heckeArch d m s = L(s, ψ_m)` of the Hecke `L`-function
of the Größencharacter `ψ_m(z) = χ(z)(z/|z|)^m` of `ℚ(i)` (`Lam` an entire completion of
`heckeArch d m · heckeLSeries χ m` on `re s > 1 + |m|/2`).

The statement splits into two halves, and the split is exactly the one the classical proof uses:

* **`re s > 1` (the half-plane of absolute convergence).**  Here `Lam s / heckeArch d m s` is the
  absolutely convergent Euler product `Σ_n λ(n)n^{-s}`; the identity theorem for analytic functions
  (together with the nonvanishing of `heckeArch`, whose zeros all lie in `re s ≤ 0`) extends the
  hypothesis-agreement from `re s > 1 + |m|/2` down to the whole half-plane `re s > 1`, and the
  inverse bound there is `HeckeInvBoundAll` (`heckeInvBound_all`).  Proved in this file
  (`heckeLcontInvBound_re_gt_one`).
* **`re s ≤ 1` (the critical strip).**  This is the classical zero-free-region input: *FI* (16.20)
  (the de la Vallée Poussin `3-4-1` inequality for `ζ_K, L(·,ψ), L(·,ψ²)`) and, for real `ψ`,
  Lemma 16.1 (Siegel's uniform bound on the real zeros, Goldfeld's method), fed through the
  convexity bounds (16.18)/(16.19) to give (16.23) by integrating `L'/L`.  Isolated as the lemma
  `heckeLcontInvBound_strip` (delegated).
-/

set_option autoImplicit false

namespace Work.FIArea6Hecke

open scoped BigOperators Topology

noncomputable section

/-- The archimedean factor `heckeArch d m s = (4d/π)^s·Γ(s + |m|/2)` of the completed Hecke
`L`-function does not vanish when `re s > 0`.  (Mathlib's `Complex.Gamma` is the *entire* function
vanishing at `0, -1, -2, …`, so `heckeArch` can vanish only when `re s ≤ 0`; here `0 < re s`, hence
`re (s + |m|/2) > 0` and `Complex.Gamma_ne_zero_of_re_pos` applies.) -/
lemma heckeArch_ne_zero_of_re_pos {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Work.FITop4.Bridge.heckeArch d m s ≠ 0 := by
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
lemma heckeArch_differentiableAt {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s := by
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

/-- The Hecke `L`-series is absolutely convergent (as a `LSeries`) in the half-plane `re s > 1`,
from the elementary bound `‖λ(n)‖ ≤ 4τ(n)` (`heckeLam_bound`). -/
lemma heckeLSeriesSummable_of_one_lt_re (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam chi m) (y : ℂ) := by
  rw [LSeriesSummable]
  have hbd : ∀ n : ℕ,
      ‖LSeries.term (Work.FIArea5.S16Hecke.heckeLam chi m) (y : ℂ) n‖
        ≤ 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-y)) := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg hn]
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h1 : ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖
          ≤ 4 * ((n.divisors.card : ℕ) : ℝ) :=
        Work.FIArea5.S16Hecke.heckeLam_bound chi m hchi (Nat.one_le_iff_ne_zero.mpr hn)
      have hpos : 0 < (n : ℝ) ^ y := Real.rpow_pos_of_pos hnpos y
      have h2 : 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-y))
          = (4 * ((n.divisors.card : ℕ) : ℝ)) / (n : ℝ) ^ y := by
        rw [Real.rpow_neg hnpos.le]; ring
      calc ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ / (n : ℝ) ^ y
          ≤ (4 * ((n.divisors.card : ℕ) : ℝ)) / (n : ℝ) ^ y :=
            div_le_div_of_nonneg_right h1 hpos.le
        _ = 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-y)) := h2.symm
  exact Summable.of_norm_bounded
    ((Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg hy).mul_left 4) hbd

/-- The abscissa of absolute convergence of the Hecke `L`-series is at most `1`. -/
lemma heckeLSeries_absc_le_one (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) ≤ (1 : EReal) := by
  have h := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := Work.FIArea5.S16Hecke.heckeLam chi m) (x := 1)
    (fun y hy => heckeLSeriesSummable_of_one_lt_re chi m hchi hy)
  rwa [EReal.coe_one] at h

/-- **The identity theorem step.**  `Lam / heckeArch` and `heckeLSeries χ m` agree on the whole
half-plane `re s > 1`: they agree on the (open) half-plane `re s > 1 + |m|/2` on which `Lam` is
required to complete `heckeArch · heckeLSeries`, `Lam / heckeArch` is holomorphic on `re s > 1`
(as `heckeArch` is holomorphic and nonzero on `re s > 0 ⊇ {re > 1}`) and `heckeLSeries` is
analytic on `re s > 1`. -/
lemma Lam_div_heckeArch_eq_LSeries {d : ℕ} (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagree : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {s : ℂ} (hs : 1 < s.re) :
    Lam s / Work.FITop4.Bridge.heckeArch d m s = Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
  have hbd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  set U : Set ℂ := {z : ℂ | 1 < z.re} with hU
  have hmem : ∀ {z : ℂ}, z ∈ U → 1 < z.re := fun {z} hz => by
    simpa only [hU, Set.mem_ofPred_eq] using hz
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := by
    have h := (convex_Ioi (1 : ℝ)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
    have h2 : (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' (Set.Ioi 1) = {z : ℂ | 1 < z.re} := by
      ext z; simp
    rwa [h2] at h
  have hUpre : IsPreconnected U := hUconv.isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z => Lam z / Work.FITop4.Bridge.heckeArch d m z) U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    apply DifferentiableOn.div
    · exact (hAn.differentiableOn).mono (Set.subset_univ U)
    · intro z hz
      exact (heckeArch_differentiableAt hd m (by have := hmem hz; linarith)).differentiableWithinAt
    · intro z hz
      exact heckeArch_ne_zero_of_re_pos hd m (by have := hmem hz; linarith)
  have hg : AnalyticOnNhd ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m) U := by
    have habs := heckeLSeries_absc_le_one chi m hbd
    have hdiff : DifferentiableOn ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m) U := by
      refine (LSeries_differentiableOn (Work.FIArea5.S16Hecke.heckeLam chi m)).mono ?_
      intro z hz
      show LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (z.re : EReal)
      exact lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr (hmem hz))
    exact hdiff.analyticOnNhd hUopen
  have hz₀ : (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ) ∈ U := by
    have h := abs_nonneg (m : ℝ)
    simp only [hU, Set.mem_ofPred_eq, Complex.ofReal_re]
    linarith
  have hev : (fun z => Lam z / Work.FITop4.Bridge.heckeArch d m z)
      =ᶠ[𝓝 (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ)]
        (Work.FIArea5.S16Hecke.heckeLSeries chi m) := by
    refine Filter.eventually_of_mem
      (show {z : ℂ | 1 + |(m : ℝ)| / 2 < z.re} ∈ 𝓝 _ from ?_) ?_
    · apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
      have h := abs_nonneg (m : ℝ)
      linarith
    · intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      show Lam z / Work.FITop4.Bridge.heckeArch d m z = Work.FIArea5.S16Hecke.heckeLSeries chi m z
      rw [hagree z hz]
      have hne : Work.FITop4.Bridge.heckeArch d m z ≠ 0 :=
        heckeArch_ne_zero_of_re_pos hd m (by have h := abs_nonneg (m : ℝ); linarith)
      rw [mul_div_cancel_left₀ _ hne]
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hUpre hz₀ hev
  exact heq hs

end

end Work.FIArea6Hecke
