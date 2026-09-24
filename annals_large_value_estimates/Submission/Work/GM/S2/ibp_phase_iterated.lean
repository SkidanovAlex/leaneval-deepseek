import Mathlib
import Submission.Work.GM.S2.hhat_decay_defs

/-!
# Iterated integration by parts against the phase `u^{it}` (GM Lemma 4.3(2))

If `g` is `C^∞` on `ℝ` and `iteratedDeriv k g` vanishes at `1/2` and `5/2` for all
`k ≤ j`, then
`∫_{1/2}^{5/2} g u · u^{it} du = ((-1)^j / ∏_{k<j} (k+1+it)) ∫_{1/2}^{5/2} g^{(j)}(u) · u^j · u^{it} du`.

The mechanism: with `ψ_m(u) = u^m u^{it}` one has `ψ_m'(u) = (m+it) ψ_{m-1}(u)`, so one
integration by parts moves a derivative from the phase onto `g` at the cost of `(m+it)^{-1}`
and a sign, provided the boundary terms vanish.
-/

namespace Work.GM.S2

open scoped Interval
open Complex

/-- The phase is differentiable away from `0`, with derivative `it·u^{-1}·u^{it}`. -/
lemma hhatPhase_hasDerivAt (t u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => hhatPhase t v)
      (Complex.I * (t : ℂ) * (u : ℂ)⁻¹ * hhatPhase t u) u := by
  have hlog : HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) (((u⁻¹ : ℝ) : ℂ)) u :=
    (Real.hasDerivAt_log hu).ofReal_comp
  have h1 : HasDerivAt (fun v : ℝ => Complex.I * (t : ℂ) * ((Real.log v : ℝ) : ℂ))
      (Complex.I * (t : ℂ) * (((u⁻¹ : ℝ) : ℂ))) u := hlog.const_mul _
  have h2 := (Complex.hasDerivAt_exp (Complex.I * (t : ℂ) * ((Real.log u : ℝ) : ℂ))).comp u h1
  have hfun : (Complex.exp ∘ (fun v : ℝ => Complex.I * (t : ℂ) * ((Real.log v : ℝ) : ℂ)))
      = (fun v : ℝ => hhatPhase t v) := rfl
  rw [hfun] at h2
  refine h2.congr_deriv ?_
  simp only [hhatPhase, Complex.ofReal_inv]
  ring_nf

/-- `ψ_m(u) = u^m u^{it}` has derivative `(m+it) u^{m-1} u^{it}` for `m ≥ 1` and `u ≠ 0`. -/
lemma psi_hasDerivAt (t : ℝ) (m : ℕ) (hm : 1 ≤ m) (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => (v : ℂ) ^ m * hhatPhase t v)
      (((m : ℂ) + Complex.I * (t : ℂ)) * ((u : ℂ) ^ (m - 1) * hhatPhase t u)) u := by
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  have hpow : HasDerivAt (fun v : ℝ => (v : ℂ) ^ m) ((m : ℂ) * (u : ℂ) ^ (m - 1) * 1) u := by
    have h2 := ((hasDerivAt_id u).ofReal_comp).pow m
    exact h2
  have hφ := hhatPhase_hasDerivAt t u hu
  have hmul := hpow.mul hφ
  refine hmul.congr_deriv ?_
  have hpowinv : (u : ℂ) ^ m * (u : ℂ)⁻¹ = (u : ℂ) ^ (m - 1) := by
    simpa using (pow_sub₀ (u : ℂ) huc hm).symm
  rw [← hpowinv]
  ring

/-- The phase is continuous on `ℝ \ {0}`. -/
lemma continuousOn_hhatPhase (t : ℝ) : ContinuousOn (fun u : ℝ => hhatPhase t u) ({0}ᶜ : Set ℝ) := by
  have h1 : ContinuousOn (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) ({0}ᶜ : Set ℝ) :=
    Complex.continuous_ofReal.comp_continuousOn Real.continuousOn_log
  have h2 : ContinuousOn (fun u : ℝ => Complex.I * (t : ℂ) * ((Real.log u : ℝ) : ℂ)) ({0}ᶜ : Set ℝ) :=
    continuousOn_const.mul h1
  have h3 : ContinuousOn (Complex.exp ∘ fun u : ℝ => Complex.I * (t : ℂ) * ((Real.log u : ℝ) : ℂ))
      ({0}ᶜ : Set ℝ) := Complex.continuous_exp.comp_continuousOn h2
  exact h3

/-- One step of the iterated integration by parts: if `h` is differentiable on `[1/2, 5/2]`
with derivative `h'` and vanishes at the endpoints, then
`(m+it) ∫ h·u^{m-1}·u^{it} = -∫ h'·u^m·u^{it}`. -/
lemma ibp_step (h h' : ℝ → ℂ) (t : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hderiv : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) (5 / 2), HasDerivAt h (h' u) u)
    (hh' : IntervalIntegrable h' MeasureTheory.volume (1 / 2 : ℝ) (5 / 2))
    (ha : h (1 / 2) = 0) (hb : h (5 / 2) = 0) :
    ((m : ℂ) + Complex.I * (t : ℂ)) *
      (∫ u in (1 / 2 : ℝ)..(5 / 2), h u * ((u : ℂ) ^ (m - 1) * hhatPhase t u))
      = - ∫ u in (1 / 2 : ℝ)..(5 / 2), h' u * ((u : ℂ) ^ m * hhatPhase t u) := by
  have hmem : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) (5 / 2), u ≠ 0 := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 2)] at hu
    linarith [hu.1]
  have hv : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) (5 / 2),
      HasDerivAt (fun v : ℝ => (v : ℂ) ^ m * hhatPhase t v)
        (((m : ℂ) + Complex.I * (t : ℂ)) * ((u : ℂ) ^ (m - 1) * hhatPhase t u)) u :=
    fun u hu => psi_hasDerivAt t m hm u (hmem u hu)
  have hv'int : IntervalIntegrable
      (fun u : ℝ => ((m : ℂ) + Complex.I * (t : ℂ)) * ((u : ℂ) ^ (m - 1) * hhatPhase t u))
      MeasureTheory.volume (1 / 2 : ℝ) (5 / 2) := by
    refine (continuousOn_const.mul ?_).intervalIntegrable
    refine ((Complex.continuous_ofReal.continuousOn).pow (m - 1)).mul ?_
    exact (continuousOn_hhatPhase t).mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 2)] at hx
      linarith [hx.1])
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hderiv hv hh' hv'int
  have heq : (∫ u in (1 / 2 : ℝ)..(5 / 2),
        h u * (((m : ℂ) + Complex.I * (t : ℂ)) * ((u : ℂ) ^ (m - 1) * hhatPhase t u)))
      = ((m : ℂ) + Complex.I * (t : ℂ)) *
        ∫ u in (1 / 2 : ℝ)..(5 / 2), h u * ((u : ℂ) ^ (m - 1) * hhatPhase t u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu; ring
  rw [heq, hb, ha] at key
  simp only [zero_mul, sub_zero, zero_sub] at key
  exact key

/-- `(j : WithTop ℕ∞) < ⊤`, where the right hand side is `C^∞`. -/
lemma natCast_lt_top_withTop (j : ℕ) :
    (j : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  have h : (j : ℕ∞) < (⊤ : ℕ∞) := ENat.natCast_lt_top j
  exact_mod_cast h

/-- `(j : WithTop ℕ∞) ≤ ⊤`. -/
lemma natCast_le_top_withTop (j : ℕ) :
    (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := le_of_lt (natCast_lt_top_withTop j)

/-- The product-form (division-free) iterated integration by parts. -/
theorem main_aux (t : ℝ) : ∀ (j : ℕ) (g : ℝ → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    (∀ k ≤ j, iteratedDeriv k g (1 / 2) = 0) →
    (∀ k ≤ j, iteratedDeriv k g (5 / 2) = 0) →
    (∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ))) *
        (∫ u in (1 / 2 : ℝ)..(5 / 2), g u * hhatPhase t u)
      = (-1 : ℂ) ^ j *
        ∫ u in (1 / 2 : ℝ)..(5 / 2), iteratedDeriv j g u * ((u : ℂ) ^ j * hhatPhase t u) := by
  intro j
  induction j with
  | zero =>
      intro g hg hleft hright
      simp
  | succ j ih =>
      intro g hg hleft hright
      have hleft' : ∀ k ≤ j, iteratedDeriv k g (1 / 2) = 0 :=
        fun k hk => hleft k (le_trans hk (Nat.le_succ j))
      have hright' : ∀ k ≤ j, iteratedDeriv k g (5 / 2) = 0 :=
        fun k hk => hright k (le_trans hk (Nat.le_succ j))
      have ih' := ih g hg hleft' hright'
      have hdiff : Differentiable ℝ (iteratedDeriv j g) :=
        ContDiff.differentiable_iteratedDeriv j hg (natCast_lt_top_withTop j)
      have hderiv : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) (5 / 2),
          HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g u) u := by
        intro u _
        have h : HasDerivAt (iteratedDeriv j g) (deriv (iteratedDeriv j g) u) u :=
          (hdiff.differentiableAt (x := u)).hasDerivAt
        rwa [← iteratedDeriv_succ] at h
      have hint : IntervalIntegrable (iteratedDeriv (j + 1) g) MeasureTheory.volume
          (1 / 2 : ℝ) (5 / 2) :=
        (ContDiff.continuous_iteratedDeriv (j + 1) hg (natCast_le_top_withTop (j + 1)))
          |>.intervalIntegrable _ _
      have ha : iteratedDeriv j g (1 / 2) = 0 := hleft j (Nat.le_succ j)
      have hb : iteratedDeriv j g (5 / 2) = 0 := hright j (Nat.le_succ j)
      have step := ibp_step (iteratedDeriv j g) (iteratedDeriv (j + 1) g) t (j + 1)
        (by omega) hderiv hint ha hb
      have step' : (((j : ℂ) + 1) + Complex.I * (t : ℂ)) *
            (∫ u in (1 / 2 : ℝ)..(5 / 2), iteratedDeriv j g u * ((u : ℂ) ^ j * hhatPhase t u))
          = - ∫ u in (1 / 2 : ℝ)..(5 / 2),
              iteratedDeriv (j + 1) g u * ((u : ℂ) ^ (j + 1) * hhatPhase t u) := by
        simpa [Nat.cast_add, Nat.cast_one] using step
      calc (∏ k ∈ Finset.range (j + 1), (((k : ℂ) + 1) + Complex.I * (t : ℂ))) *
            (∫ u in (1 / 2 : ℝ)..(5 / 2), g u * hhatPhase t u)
          = (((j : ℂ) + 1) + Complex.I * (t : ℂ)) *
              ((∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ))) *
                (∫ u in (1 / 2 : ℝ)..(5 / 2), g u * hhatPhase t u)) := by
            rw [Finset.prod_range_succ]; ring
        _ = (((j : ℂ) + 1) + Complex.I * (t : ℂ)) *
              ((-1 : ℂ) ^ j * ∫ u in (1 / 2 : ℝ)..(5 / 2),
                iteratedDeriv j g u * ((u : ℂ) ^ j * hhatPhase t u)) := by
            rw [ih']
        _ = (-1 : ℂ) ^ j * ((((j : ℂ) + 1) + Complex.I * (t : ℂ)) *
              ∫ u in (1 / 2 : ℝ)..(5 / 2),
                iteratedDeriv j g u * ((u : ℂ) ^ j * hhatPhase t u)) := by
            ring
        _ = (-1 : ℂ) ^ j * (- ∫ u in (1 / 2 : ℝ)..(5 / 2),
                iteratedDeriv (j + 1) g u * ((u : ℂ) ^ (j + 1) * hhatPhase t u)) := by
            rw [step']
        _ = (-1 : ℂ) ^ (j + 1) * ∫ u in (1 / 2 : ℝ)..(5 / 2),
                iteratedDeriv (j + 1) g u * ((u : ℂ) ^ (j + 1) * hhatPhase t u) := by
            rw [pow_succ]; ring

theorem ibp_phase_iterated (g : ℝ → ℂ) (t : ℝ) (j : ℕ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hleft : ∀ k ≤ j, iteratedDeriv k g (1 / 2) = 0)
    (hright : ∀ k ≤ j, iteratedDeriv k g (5 / 2) = 0) :
    (∫ u in (1 / 2)..(5 / 2), g u * Work.GM.S2.hhatPhase t u)
      = ((-1 : ℂ) ^ j / ∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ))) *
        ∫ u in (1 / 2)..(5 / 2), iteratedDeriv j g u *
          ((u : ℂ) ^ j * Work.GM.S2.hhatPhase t u) := by
  have hP : (∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _ hz
    have hre := congrArg Complex.re hz
    simp [Complex.add_re, Complex.mul_re] at hre
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have key := main_aux t j g hg hleft hright
  have hdiv : (∫ u in (1 / 2 : ℝ)..(5 / 2), g u * hhatPhase t u)
      = (-1 : ℂ) ^ j * (∫ u in (1 / 2 : ℝ)..(5 / 2),
          iteratedDeriv j g u * ((u : ℂ) ^ j * hhatPhase t u)) /
        (∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ))) := by
    rw [eq_div_iff hP]
    rw [mul_comm (∫ u in (1 / 2 : ℝ)..(5 / 2), g u * hhatPhase t u)]
    exact key
  rw [hdiv, div_mul_eq_mul_div]

end Work.GM.S2
