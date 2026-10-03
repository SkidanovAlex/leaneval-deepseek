import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripWBoundDefs
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeStripWBasic
import Submission.Work.FIArea6Hecke.R.heckeStripW_upper
import Submission.Work.FIArea6Hecke.R.heckeStripW_lower
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.lvalLineOneBound
import Submission.Work.FIArea6Hecke.R.LHBDisc
import Submission.Work.FIArea6Hecke.R.LvalStripContAux
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **FI (16.18) in sharp form, with constants absolute in the modulus.**  For a strict character
`χ` mod `4d` which is odd, `‖χ‖ ≤ 1`, real (`χ = conj χ`) and nontrivial on some primary unit of
`ℤ[i]/(4d)`, and for any entire `Lam` agreeing with `heckeArch d 0 s · L(s,χ)` on `re s > 1`, the
continuation `Lval d 0 Lam` satisfies on the strip `1/2 ≤ re s ≤ 1` the convexity bound

  `‖Lval d 0 Lam s‖ ≤ C · (d(2+|Im s|))^{K(1-re s)} · (log(4d(2+|Im s|)))^k`

with absolute `C, K, k`.  The proof is the Phragmén–Lindelöf argument with the comparison weight
`heckeStripW`: the `re s = 1` boundary is the polylogarithmic line bound `lvalLineOneBound`
(fed by the mean-zero disc sums `LHBDisc`), the interior growth is the polynomial strip bound
`LvalStripContAux`, and the weight's level on `re s = 1` and `re s = 1/2` matches the two
boundary data. -/
theorem LvalStripSharpClean :
    ∃ C K k : ℝ, 0 < C ∧ 0 ≤ K ∧ 0 ≤ k ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, chi z = star (chi z)) →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
          ‖Work.FIArea6Hecke.Lval d 0 Lam s‖
            ≤ C * ((d : ℝ) * (2 + |s.im|)) ^ (K * (1 - s.re))
                * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ k := by
  classical
  obtain ⟨C_Wup, hC_Wup_pos, hWup⟩ := heckeStripW_upper
  obtain ⟨c_Wlow, hc_Wlow_pos, hWlow⟩ := heckeStripW_lower
  obtain ⟨Cdisc, hCdisc_pos, hdisc₀⟩ := LHBDisc
  obtain ⟨Cline, hCline_pos, hline⟩ := lvalLineOneBound
  obtain ⟨Cpoly, hCpoly_pos, hpoly⟩ := LvalStripContAux
  set A₁ : ℝ := 625 * Cline * (Cdisc + 1) with hA₁
  set A₂ : ℝ := Cpoly / (c_Wlow * 4 ^ (10 : ℕ)) with hA₂
  set Cpl : ℝ := max (A₁ / c_Wlow) A₂ with hCpl
  have hCpl_pos : 0 < Cpl := lt_max_of_lt_left (by rw [hA₁]; positivity)
  have hA₁_pos : 0 < A₁ := by rw [hA₁]; positivity
  have hA₂_pos : 0 < A₂ := by rw [hA₂]; positivity
  refine ⟨Cpl * C_Wup * 4 ^ (20 : ℕ), 20, 8, by positivity, by norm_num, by norm_num, ?_⟩
  intro d hd chi hchi hreal hb hnt Lam hAn hagr s hs1 hs2
  -- the disc-sum bound, with the nontriviality hypothesis
  have hdiscb : ∀ X : ℝ, 1 ≤ X →
      ‖∑ z ∈ Work.FIArea6Hecke.R.primaryBox d X, chi z‖ ≤ Cdisc * (d : ℝ) * Real.sqrt X := by
    intro X hX
    rw [Work.FIArea6Hecke.R.primaryBox_sum_eq]
    simpa only [Work.FIArea6Hecke.R.discSum] using hdisc₀ d hd chi hchi hnt X hX
  -- the bound on the line re s = 1
  have hline1 : ∀ t : ℝ,
      ‖Work.FIArea6Hecke.Lval d 0 Lam ((1 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ A₁ * (Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (4 : ℕ) := by
    intro t
    have := hline d hd chi hchi hnt Cdisc hCdisc_pos hdiscb Lam hAn hagr t
    rw [hA₁]
    exact this
  -- the polynomial bound on the strip 3/8 <= re s <= 1
  have hpoly1 : ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 1 →
      ‖Work.FIArea6Hecke.Lval d 0 Lam z‖ ≤ Cpoly * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ) :=
    fun z h1 h2 => hpoly d hd chi hchi hnt Lam hAn hagr z h1 h2
  -- ## the quotient and the Phragmén–Lindelöf principle
  set Q : ℂ → ℂ := fun z => Work.FIArea6Hecke.Lval d 0 Lam z / heckeStripW d z with hQ
  have hLval_an : AnalyticOn ℂ (Work.FIArea6Hecke.Lval d 0 Lam) Set.univ := by
    have hdiff : Differentiable ℂ (Work.FIArea5.S16Hecke.Lcont d Lam 0) :=
      Work.FIArea5.S16Hecke.differentiable_Lcont hd
        (differentiableOn_univ.mp hAn.differentiableOn) 0
    rw [Lval_eq_Lcont_zero d Lam]
    exact DifferentiableOn.analyticOn (Differentiable.differentiableOn hdiff) isOpen_univ
  have hQdiffOn : DifferentiableOn ℂ Q (Complex.re ⁻¹' Set.Ioo (1 / 2) 1) := by
    rw [hQ]
    refine DifferentiableOn.div ((hLval_an.mono (Set.subset_univ _)).differentiableOn) ?_ ?_
    · intro z hz
      rw [Set.mem_preimage] at hz
      exact (heckeStripW_differentiableAt hd (by linarith [hz.1])
        (by linarith [hz.2])).differentiableWithinAt
    · intro z hz
      rw [Set.mem_preimage] at hz
      exact heckeStripW_ne_zero hd (le_of_lt hz.1) (le_of_lt hz.2)
  have hQcont : ContinuousOn Q (Complex.re ⁻¹' Set.Icc (1 / 2) 1) := by
    rw [hQ]
    refine ContinuousOn.div (hLval_an.continuousOn.mono (Set.subset_univ _)) ?_ ?_
    · intro z hz
      rw [Set.mem_preimage] at hz
      exact (heckeStripW_differentiableAt hd (by linarith [hz.1])
        (by linarith [hz.2])).continuousAt.continuousWithinAt
    · intro z hz
      rw [Set.mem_preimage] at hz
      exact heckeStripW_ne_zero hd hz.1 hz.2
  have hcls : closure (Complex.re ⁻¹' Set.Ioo (1 / 2) 1) = Complex.re ⁻¹' Set.Icc (1 / 2) 1 := by
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  have hQdco : DiffContOnCl ℂ Q (Complex.re ⁻¹' Set.Ioo (1 / 2) 1) :=
    ⟨hQdiffOn, by rw [hcls]; exact hQcont⟩
  -- boundary bound on the line re s = 1
  have hbnd1 : ∀ z : ℂ, Complex.re z = 1 → ‖Q z‖ ≤ Cpl := by
    intro z hz
    have hz_eq : z = (1 : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    rw [hz_eq, hQ, norm_div]
    set L : ℝ := Real.log (4 * (d : ℝ) * (2 + |z.im|)) with hLdef
    have hL1 : (1 : ℝ) ≤ L := one_le_log_four_d_two_add d hd z.im
    have hnum : ‖Work.FIArea6Hecke.Lval d 0 Lam ((1 : ℂ) + (z.im : ℂ) * Complex.I)‖
        ≤ A₁ * L ^ (4 : ℕ) := by
      have h := hline1 z.im
      rwa [← hLdef] at h
    have hden : c_Wlow * L ^ (8 : ℕ)
        ≤ ‖heckeStripW d ((1 : ℂ) + (z.im : ℂ) * Complex.I)‖ := by
      have h := hWlow d hd (1 : ℝ) z.im (by norm_num) le_rfl
      have hexp : (20 : ℝ) * (1 - 1) = 0 := by norm_num
      rw [hexp, Real.rpow_zero, mul_one] at h
      rwa [← hLdef] at h
    have hpos8 : (0 : ℝ) < c_Wlow * L ^ (8 : ℕ) := by positivity
    have hL4 : L ^ (4 : ℕ) ≤ L ^ (8 : ℕ) := by
      have h1 : (1 : ℝ) ≤ L ^ (4 : ℕ) := one_le_pow₀ hL1
      calc L ^ (4 : ℕ) = L ^ (4 : ℕ) * 1 := (mul_one _).symm
        _ ≤ L ^ (4 : ℕ) * L ^ (4 : ℕ) := by nlinarith [h1]
        _ = L ^ (8 : ℕ) := by ring
    have hmid : (A₁ * L ^ (4 : ℕ)) / (c_Wlow * L ^ (8 : ℕ)) ≤ A₁ / c_Wlow := by
      rw [div_le_iff₀ hpos8]
      have h2 : (A₁ / c_Wlow) * (c_Wlow * L ^ (8 : ℕ)) = A₁ * L ^ (8 : ℕ) := by
        field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left hL4 (le_of_lt hA₁_pos)
    exact (div_le_div₀ (by positivity) hnum hpos8 hden).trans (hmid.trans (le_max_left _ _))
  -- boundary bound on the line re s = 1/2
  have hbnd_half : ∀ z : ℂ, Complex.re z = 1 / 2 → ‖Q z‖ ≤ Cpl := by
    intro z hz
    have hz_eq : z = (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [hz]
    rw [hz_eq, hQ, norm_div]
    have hre : (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I).re = (1 / 2 : ℝ) := by simp
    have him : (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I).im = z.im := by simp
    have hnum : ‖Work.FIArea6Hecke.Lval d 0 Lam (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)‖
        ≤ Cpoly * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ) := by
      have h := hpoly1 (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)
        (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      simpa only [him] using h
    have hden : c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ))
        ≤ ‖heckeStripW d (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)‖ := by
      have h := hWlow d hd (1 / 2 : ℝ) z.im (by norm_num) (by norm_num)
      have hexp : (20 : ℝ) * (1 - 1 / 2) = 10 := by norm_num
      rw [hexp] at h
      have hbaseN : ((4 * (d : ℝ)) * (2 + |z.im|)) ^ (10 : ℝ)
          = 4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ) := by
        rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, mul_pow,
          mul_pow]
      rw [hbaseN] at h
      have hL1 : (1 : ℝ) ≤ Real.log (4 * (d : ℝ) * (2 + |z.im|)) :=
        one_le_log_four_d_two_add d hd z.im
      have hlog : (1 : ℝ) ≤ (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ (8 : ℕ) :=
        one_le_pow₀ hL1
      have h0 : (0 : ℝ) ≤ c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ)
          * (2 + |z.im|) ^ (10 : ℕ)) := by positivity
      calc c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ))
          = c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ)) * 1 :=
            (mul_one _).symm
        _ ≤ c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ))
              * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ (8 : ℕ) :=
            mul_le_mul_of_nonneg_left hlog h0
        _ ≤ ‖heckeStripW d (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)‖ := h
    have hd10 : (0 : ℝ) < (d : ℝ) ^ (10 : ℕ) := by
      have hd0 : (0 : ℝ) < (d : ℝ) := by
        have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      positivity
    have hposD : (0 : ℝ) < c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ)
        * (2 + |z.im|) ^ (10 : ℕ)) := by positivity
    have h1t : (1 + |z.im|) ^ (10 : ℕ) ≤ (2 + |z.im|) ^ (10 : ℕ) := by
      refine pow_le_pow_left₀ (by positivity) ?_ 10
      have := abs_nonneg z.im; linarith
    have hmid : (Cpoly * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ))
          / (c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ)))
        ≤ A₂ := by
      rw [hA₂, div_le_div_iff₀ hposD (by positivity)]
      have hstep1 : (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ)
          ≤ (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ) :=
        mul_le_mul_of_nonneg_left h1t (le_of_lt hd10)
      have hstep2 : Cpoly * ((d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ))
          ≤ Cpoly * ((d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ)) :=
        mul_le_mul_of_nonneg_left hstep1 (le_of_lt hCpoly_pos)
      calc Cpoly * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ) * (c_Wlow * 4 ^ (10 : ℕ))
          = (Cpoly * ((d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ))) * (c_Wlow * 4 ^ (10 : ℕ)) :=
            by ring
        _ ≤ (Cpoly * ((d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ))) * (c_Wlow * 4 ^ (10 : ℕ)) :=
            mul_le_mul_of_nonneg_right hstep2 (by positivity)
        _ = Cpoly * (c_Wlow * (4 ^ (10 : ℕ) * (d : ℝ) ^ (10 : ℕ) * (2 + |z.im|) ^ (10 : ℕ))) :=
            by ring
    exact (div_le_div₀ (by positivity) hnum hposD hden).trans
      (hmid.trans (le_max_right (A₁ / c_Wlow) A₂))
  -- the growth of the quotient in the strip
  set X₀ : ℝ := Cpoly * (d : ℝ) ^ (10 : ℕ) / c_Wlow with hX₀
  have hX₀pos : 0 < X₀ := by rw [hX₀]; positivity
  set B : ℝ := 100 + max (Real.log X₀) 0 with hBdef
  have hQgrow : ∃ c < Real.pi / (1 - 1 / 2), ∃ B' : ℝ,
      Q =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Set.Ioo (1 / 2) 1)]
        (fun z : ℂ => Real.exp (B' * Real.exp (c * |z.im|))) := by
    have hpi : Real.pi / (1 - 1 / 2) = 2 * Real.pi := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, div_eq_iff (by norm_num : ((1 : ℝ) / 2) ≠ 0)]
      ring
    refine ⟨1, by rw [hpi]; linarith [Real.pi_gt_three], B, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    rw [Filter.eventually_inf_principal, Filter.eventually_comap]
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with b hb
    intro z hzim hz
    rw [Set.mem_preimage, Set.mem_Ioo] at hz
    have hzre1 : 3 / 8 ≤ z.re := by linarith [hz.1]
    have hzre2 : z.re ≤ 1 := le_of_lt hz.2
    have hnum := hpoly1 z hzre1 hzre2
    have hwlow := hWlow d hd z.re z.im (le_of_lt hz.1) (le_of_lt hz.2)
    have hwlow' : c_Wlow * ((4 * (d : ℝ)) * (2 + |z.im|)) ^ (20 * (1 - z.re))
          * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ (8 : ℕ) ≤ ‖heckeStripW d z‖ := by
      simpa only [Complex.re_add_im] using hwlow
    have hlog1 : (1 : ℝ) ≤ Real.log (4 * (d : ℝ) * (2 + |z.im|)) :=
      one_le_log_four_d_two_add d hd z.im
    have hb' : (1 : ℝ) ≤ (2 + |z.im|) := by
      have := abs_nonneg z.im
      linarith
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hw_lb : c_Wlow ≤ ‖heckeStripW d z‖ := by
      have h8 : (1 : ℝ) ≤ (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ (8 : ℕ) :=
        one_le_pow₀ hlog1
      have hpow1 : (1 : ℝ) ≤ ((4 * (d : ℝ)) * (2 + |z.im|)) ^ (20 * (1 - z.re)) := by
        refine Real.one_le_rpow ?_ ?_
        · nlinarith [hb', hd1]
        · linarith [hz.2]
      have hXY : (1 : ℝ) ≤ ((4 * (d : ℝ)) * (2 + |z.im|)) ^ (20 * (1 - z.re))
          * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ (8 : ℕ) := by
        nlinarith [hpow1, h8]
      calc c_Wlow = c_Wlow * 1 := by ring
        _ ≤ c_Wlow * (((4 * (d : ℝ)) * (2 + |z.im|)) ^ (20 * (1 - z.re))
              * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ (8 : ℕ)) :=
            mul_le_mul_of_nonneg_left hXY (le_of_lt hc_Wlow_pos)
        _ = c_Wlow * ((4 * (d : ℝ)) * (2 + |z.im|)) ^ (20 * (1 - z.re))
              * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ (8 : ℕ) := by ring
        _ ≤ ‖heckeStripW d z‖ := hwlow'
    have hQb : ‖Q z‖ ≤ X₀ * (1 + |z.im|) ^ (10 : ℕ) := by
      rw [hQ, norm_div, hX₀]
      calc ‖Work.FIArea6Hecke.Lval d 0 Lam z‖ / ‖heckeStripW d z‖
          ≤ (Cpoly * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ)) / c_Wlow :=
            div_le_div₀ (by positivity) hnum hc_Wlow_pos hw_lb
        _ = Cpoly * (d : ℝ) ^ (10 : ℕ) / c_Wlow * (1 + |z.im|) ^ (10 : ℕ) := by ring
    have hnorm : ‖Real.exp (B * Real.exp (1 * |z.im|))‖ = Real.exp (B * Real.exp |z.im|) := by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    rw [hnorm]
    refine hQb.trans ?_
    -- (1 + |z.im|)^10 <= exp (100 * exp |z.im|)
    have hb10 : (1 + |z.im|) ^ (10 : ℕ) ≤ Real.exp (100 * Real.exp |z.im|) := by
      have h1 : (1 + |z.im|) ≤ Real.exp |z.im| := by
        have := Real.add_one_le_exp |z.im|
        linarith
      have h2 : (1 + |z.im|) ^ (10 : ℕ) ≤ (Real.exp |z.im|) ^ (10 : ℕ) :=
        pow_le_pow_left₀ (by positivity) h1 10
      have h3 : (Real.exp |z.im|) ^ (10 : ℕ) = Real.exp (10 * |z.im|) :=
        (Real.exp_nat_mul |z.im| 10).symm
      have h4 : (10 : ℝ) * |z.im| ≤ 100 * Real.exp |z.im| := by
        have := Real.add_one_le_exp |z.im|
        nlinarith [abs_nonneg z.im]
      calc (1 + |z.im|) ^ (10 : ℕ) ≤ (Real.exp |z.im|) ^ (10 : ℕ) := h2
        _ = Real.exp (10 * |z.im|) := h3
        _ ≤ Real.exp (100 * Real.exp |z.im|) := Real.exp_le_exp.mpr h4
    by_cases hX1 : (1 : ℝ) ≤ X₀
    · have hlogX : (0 : ℝ) ≤ Real.log X₀ := Real.log_nonneg hX1
      have hBe : B * Real.exp |z.im| = 100 * Real.exp |z.im| + Real.log X₀ * Real.exp |z.im| := by
        rw [hBdef, max_eq_left hlogX]; ring
      have hXeq : X₀ ≤ Real.exp (Real.log X₀ * Real.exp |z.im|) := by
        have hexp1 : (1 : ℝ) ≤ Real.exp |z.im| := Real.one_le_exp (abs_nonneg z.im)
        have h2 : Real.log X₀ * 1 ≤ Real.log X₀ * Real.exp |z.im| :=
          mul_le_mul_of_nonneg_left hexp1 hlogX
        calc X₀ = Real.exp (Real.log X₀) := (Real.exp_log hX₀pos).symm
          _ ≤ Real.exp (Real.log X₀ * Real.exp |z.im|) := Real.exp_le_exp.mpr (by linarith)
      calc X₀ * (1 + |z.im|) ^ (10 : ℕ)
          ≤ Real.exp (Real.log X₀ * Real.exp |z.im|) * Real.exp (100 * Real.exp |z.im|) := by
            refine mul_le_mul hXeq hb10 (by positivity) (Real.exp_pos _).le
        _ = 1 * Real.exp (B * Real.exp |z.im|) := by
            rw [← Real.exp_add, hBe]; ring
    · have hlogX : Real.log X₀ < 0 :=
        (Real.log_neg_iff hX₀pos).mpr (not_le.mp hX1)
      have hBe : B * Real.exp |z.im| = 100 * Real.exp |z.im| := by
        rw [hBdef, max_eq_right (le_of_lt hlogX)]; ring
      have hXle : X₀ ≤ 1 := le_of_lt (not_le.mp hX1)
      calc X₀ * (1 + |z.im|) ^ (10 : ℕ) ≤ 1 * (1 + |z.im|) ^ (10 : ℕ) :=
            mul_le_mul_of_nonneg_right hXle (by positivity)
        _ ≤ Real.exp (100 * Real.exp |z.im|) := by rw [one_mul]; exact hb10
        _ = 1 * Real.exp (B * Real.exp |z.im|) := by rw [hBe]; ring
  -- the Phragmén–Lindelöf bound
  have hPL : ‖Q s‖ ≤ Cpl :=
    PhragmenLindelof.vertical_strip (a := 1 / 2) (b := 1) (C := Cpl) (f := Q) (z := s)
      hQdco hQgrow hbnd_half hbnd1 hs1 hs2
  -- convert back to 
  have hws : heckeStripW d s ≠ 0 := heckeStripW_ne_zero hd hs1 hs2
  have hnormpos : 0 < ‖heckeStripW d s‖ := norm_pos_iff.mpr hws
  have hLval_le : ‖Work.FIArea6Hecke.Lval d 0 Lam s‖ ≤ Cpl * ‖heckeStripW d s‖ := by
    rw [hQ, norm_div] at hPL
    exact (div_le_iff₀ hnormpos).mp hPL
  have hwup := hWup d hd s.re s.im hs1 hs2
  have hwup' : ‖heckeStripW d s‖ ≤ C_Wup * (4 * (d : ℝ) * (2 + |s.im|)) ^ (20 * (1 - s.re))
      * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ) := by
    simpa only [Complex.re_add_im] using hwup
  refine hLval_le.trans ?_
  -- final arithmetic
  have hstep : Cpl * ‖heckeStripW d s‖
      ≤ Cpl * C_Wup * ((4 * (d : ℝ)) * (2 + |s.im|)) ^ (20 * (1 - s.re))
        * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hwup' (le_of_lt hCpl_pos)
    calc Cpl * ‖heckeStripW d s‖
        ≤ Cpl * (C_Wup * ((4 * (d : ℝ)) * (2 + |s.im|)) ^ (20 * (1 - s.re))
            * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ)) := h
      _ = Cpl * C_Wup * ((4 * (d : ℝ)) * (2 + |s.im|)) ^ (20 * (1 - s.re))
            * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ) := by ring
  refine hstep.trans ?_
  have hpow : ((4 * (d : ℝ)) * (2 + |s.im|)) ^ (20 * (1 - s.re))
      ≤ (4 : ℝ) ^ (20 : ℕ) * ((d : ℝ) * (2 + |s.im|)) ^ (20 * (1 - s.re)) := by
    have hbase : (4 * (d : ℝ)) * (2 + |s.im|) = (4 : ℝ) * ((d : ℝ) * (2 + |s.im|)) := by ring
    rw [hbase, Real.mul_rpow (by norm_num) (by positivity)]
    have hexp : 20 * (1 - s.re) ≤ ((20 : ℕ) : ℝ) := by push_cast; linarith [hs1]
    have h4 : (4 : ℝ) ^ (20 * (1 - s.re)) ≤ (4 : ℝ) ^ ((20 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    rw [Real.rpow_natCast] at h4
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  rw [show (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ ((8 : ℝ))
      = (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ) from Real.rpow_natCast _ 8]
  calc Cpl * C_Wup * ((4 * (d : ℝ)) * (2 + |s.im|)) ^ (20 * (1 - s.re))
        * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ)
      ≤ Cpl * C_Wup * ((4 : ℝ) ^ (20 : ℕ) * ((d : ℝ) * (2 + |s.im|)) ^ (20 * (1 - s.re)))
          * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ) := by
        have h0 : (0 : ℝ) ≤ (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ) := by positivity
        have h1 : (0 : ℝ) ≤ Cpl * C_Wup := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow h1) h0
    _ = Cpl * C_Wup * (4 : ℝ) ^ (20 : ℕ) * ((d : ℝ) * (2 + |s.im|)) ^ (20 * (1 - s.re))
          * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (8 : ℕ) := by ring

end

end Work.FIArea6Hecke.R
