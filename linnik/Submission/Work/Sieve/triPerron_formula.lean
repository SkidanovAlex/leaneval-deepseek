import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Work.LinnikAreas.triPerronDefs
import Submission.Work.LinnikAreas.lamCoeffSummable
import Submission.Commons.Analysis.Complex.exists_perron_formula_bound

namespace Work.Sieve

open Work.LinnikAreas
open MeasureTheory
open scoped BigOperators

/-- The norm of a real number seen as a complex number. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]

/-- Continuity of a `cpow` along the vertical line `z + i·t`. -/
private lemma cont_cpow_line (x : ℝ) (hx : 0 < x) (z : ℂ) :
    Continuous (fun t : ℝ => (x : ℂ) ^ (z + (t : ℂ) * Complex.I)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [Complex.cpow_def_of_ne_zero hx0]
  fun_prop

/-- The vertical line `c + i·t` (with `c > 0`) is never zero. -/
private lemma line_ne_zero (c t : ℝ) (hc : 0 < c) :
    ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero, Complex.zero_re] at hre
  linarith

theorem triPerron_formula :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
      (hψ2 : ψ ^ 2 = 1) {β x T : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hx : 1 < x) (hT : 0 < T)
      (hxnn : ∀ n : ℕ, (n : ℝ) ≠ x),
      ∃ e : ℂ, ‖e‖ ≤ K * (x * Work.LinnikAreas.perrErr ψ β x T) ∧
        (1 / (2 * Real.pi)) *
            (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I))
          = Work.LinnikAreas.SsmC ψ β x + e := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.Complex.exists_perron_formula_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro N _ ψ hψ hψ2 β x T hβ hβ1 hx hT hxnn
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hβ0 : (0 : ℝ) < β := by linarith
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  set a : ℕ → ℂ := fun n => Work.LinnikAreas.lam ψ n * (n : ℂ) ^ (-(β : ℂ)) with hadef
  set b : ℕ → ℂ := fun n => Work.LinnikAreas.lam ψ n * (n : ℂ) ^ (-(((β - 1 : ℝ)) : ℂ)) with hbdef
  have hba : ∀ n : ℕ, b n = (n : ℂ) * a n := by
    intro n
    rw [hbdef, hadef]
    simp only []
    rcases eq_or_ne n 0 with h0 | hn
    · subst h0
      have hz : (0 : ℂ) ^ (-(((β - 1 : ℝ)) : ℂ)) = 0 := Complex.zero_cpow (by
        simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]; linarith)
      simp [hz]
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hcp : (n : ℂ) ^ (-(((β - 1 : ℝ)) : ℂ)) = (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ (-(β : ℂ)) := by
        rw [← Complex.cpow_add _ _ hn0]; congr 1; push_cast; ring
      rw [hcp, Complex.cpow_one]; ring
  have hsumm_a : Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (1 : ℝ)) := by
    rw [hadef]; exact Work.LinnikAreas.lamCoeffSummable ψ hβ0
  have hsumm_b : Summable (fun n : ℕ => ‖b n‖ / (n : ℝ) ^ (2 : ℝ)) := by
    refine hsumm_a.congr (fun n => ?_)
    rw [hadef, hbdef]
    simp only []
    rcases eq_or_ne n 0 with h0 | hn
    · subst h0; simp
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hcp : (n : ℂ) ^ (-(((β - 1 : ℝ)) : ℂ)) = (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ (-(β : ℂ)) := by
        rw [← Complex.cpow_add _ _ hn0]; congr 1; push_cast; ring
      have hnorm : ‖Work.LinnikAreas.lam ψ n * (n : ℂ) ^ (-(((β - 1 : ℝ)) : ℂ))‖
          = (n : ℝ) * ‖Work.LinnikAreas.lam ψ n * (n : ℂ) ^ (-(β : ℂ))‖ := by
        rw [hcp, Complex.cpow_one]
        simp only [norm_mul, Complex.norm_natCast]
        ring
      rw [hnorm]
      have h1 : (n : ℝ) ^ (1 : ℝ) = (n : ℝ) := Real.rpow_one _
      have h2 : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h1, h2]
      field_simp
  -- the error-series identities
  have hE1x : (∑' n : ℕ, ‖a n‖ * (x / (n : ℝ)) ^ (1 : ℝ)
        * min 1 (1 / (T * |Real.log (x / (n : ℝ))|)))
      = x * Work.LinnikAreas.perrErr ψ β x T := by
    simp only [hadef]
    rw [Work.LinnikAreas.perrErr, ← tsum_mul_left]
    apply tsum_congr
    intro n
    have hre := (Work.LinnikAreas.lamRealNonneg ψ hψ2).2.1
    have hcast := Work.LinnikAreas.lamR_cast ψ hψ2 n
    have h1 : ‖Work.LinnikAreas.lam ψ n‖ = Work.LinnikAreas.lamR ψ n := by
      rw [← hcast, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
      exact abs_of_nonneg (hre n)
    rw [norm_mul, h1]
    rcases eq_or_ne n 0 with h0 | hn
    · subst h0; simp
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [Complex.neg_re, Complex.ofReal_re]
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hkey' : (n : ℝ) ^ (-(1 + β)) = (n : ℝ) ^ (-β) * (n : ℝ)⁻¹ := by
        rw [show -(1 + β) = (-β) + (-1) by ring, Real.rpow_add hnpos, Real.rpow_neg_one]
      rw [Real.rpow_one, hkey']
      ring
  have hE2x : (∑' n : ℕ, ‖b n‖ * (x / (n : ℝ)) ^ (2 : ℝ)
        * min 1 (1 / (T * |Real.log (x / (n : ℝ))|)))
      = x * (∑' n : ℕ, ‖a n‖ * (x / (n : ℝ)) ^ (1 : ℝ)
        * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [hba n, norm_mul, Complex.norm_natCast]
    rcases eq_or_ne n 0 with h0 | hn
    · subst h0; simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hxdiv : 0 < x / (n : ℝ) := by positivity
      have hpow : (x / (n : ℝ)) ^ (1 : ℝ) = x / (n : ℝ) := Real.rpow_one _
      have hsq : (x / (n : ℝ)) ^ (2 : ℝ) = (x / (n : ℝ)) * (x / (n : ℝ)) := by
        rw [show (2 : ℝ) = (1 : ℝ) + (1 : ℝ) by norm_num, Real.rpow_add hxdiv, hpow]
      rw [hsq, hpow]
      field_simp
  -- the two Perron instances
  have key1 := hC a 1 x T (by norm_num) hx hT hxnn hsumm_a
  have key2 := hC b 2 x T (by norm_num) hx hT hxnn hsumm_b
  set F : ℝ → ℂ := fun t => LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I)
      * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) / ((1 : ℂ) + (t : ℂ) * Complex.I) with hFdef
  set G : ℝ → ℂ := fun t => LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I)
      * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) / ((2 : ℝ) + (t : ℂ) * Complex.I) with hGdef
  set H : ℝ → ℂ := fun t => LSeries b ((2 : ℝ) + (t : ℂ) * Complex.I)
      * (x : ℂ) ^ ((2 : ℝ) + (t : ℂ) * Complex.I) / ((2 : ℝ) + (t : ℂ) * Complex.I) with hHdef
  set A : ℂ := (1 / (2 * Real.pi)) * (∫ t in (-T)..T, F t) with hAdef
  set A' : ℂ := (1 / (2 * Real.pi)) * (∫ t in (-T)..T, G t) with hA'def
  set B : ℂ := (1 / (2 * Real.pi)) * (∫ t in (-T)..T, H t) with hBdef
  set M1 : ℂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n with hM1def
  set M2 : ℂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n with hM2def
  have hkey1 : ‖A - M1‖ ≤ C * (∑' n : ℕ, ‖a n‖ * (x / (n : ℝ)) ^ (1 : ℝ)
      * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := key1
  have hkey2 : ‖B - M2‖ ≤ C * (∑' n : ℕ, ‖b n‖ * (x / (n : ℝ)) ^ (2 : ℝ)
      * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := key2
  -- the identity `LSeries a (1+it) = zlFun ψ (1+it+β)`
  have hF_eq : ∀ t : ℝ, LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I)
      = Work.LinnikAreas.zlFun ψ ((1 : ℂ) + (t : ℂ) * Complex.I + (β : ℂ)) := by
    intro t
    rw [hadef]
    exact Work.LinnikAreas.LSeries_lam_shift ψ hψ (by simp; linarith)
  have hcont_zl : Continuous (fun t : ℝ =>
      Work.LinnikAreas.zlFun ψ ((1 : ℂ) + (t : ℂ) * Complex.I + (β : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hsre : ((1 : ℂ) + (t₀ : ℂ) * Complex.I + (β : ℂ)).re = 1 + β := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero, Complex.one_re]
    have hs : ((1 : ℂ) + (t₀ : ℂ) * Complex.I + (β : ℂ)) ≠ 1 := by
      intro hh
      have hh2 := congrArg Complex.re hh
      simp only [Complex.one_re] at hh2
      rw [hsre] at hh2
      linarith
    have hd : DifferentiableAt ℂ (Work.LinnikAreas.zlFun ψ)
        ((1 : ℂ) + (t₀ : ℂ) * Complex.I + (β : ℂ)) := by
      show DifferentiableAt ℂ (fun s => riemannZeta s * DirichletCharacter.LFunction ψ s) _
      exact (differentiableAt_riemannZeta hs).mul (ψ.differentiableAt_LFunction _ (Or.inl hs))
    have hline : ContinuousAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I + (β : ℂ)) t₀ := by
      fun_prop
    exact ContinuousAt.comp (g := Work.LinnikAreas.zlFun ψ)
      (f := fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I + (β : ℂ)) hd.continuousAt hline
  have hcont_La : Continuous (fun t : ℝ => LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I)) :=
    hcont_zl.congr (fun t => (hF_eq t).symm)
  have hcont_F : Continuous F := by
    rw [hFdef]
    have h1 : Continuous (fun t : ℝ => LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I)) := hcont_La
    have h2 : Continuous (fun t : ℝ => (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) :=
      cont_cpow_line x hx0 1
    have h3 : Continuous (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
    exact (h1.mul h2).div h3 (fun t => line_ne_zero 1 t one_pos)
  have hcont_G : Continuous G := by
    rw [hGdef]
    have h1 : Continuous (fun t : ℝ => LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I)) := hcont_La
    have h2 : Continuous (fun t : ℝ => (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) :=
      cont_cpow_line x hx0 1
    have h3 : Continuous (fun t : ℝ => ((2 : ℝ) + (t : ℂ) * Complex.I)) := by fun_prop
    exact (h1.mul h2).div h3 (fun t => line_ne_zero 2 t two_pos)
  have hIntF : IntervalIntegrable F volume (-T) T := hcont_F.intervalIntegrable _ _
  have hIntG : IntervalIntegrable G volume (-T) T := hcont_G.intervalIntegrable _ _
  -- the triangle splitting
  have hpt : ∀ y : ℝ, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I) = F y - G y := by
    intro y
    have hZ : LSeries a ((1 : ℂ) + (y : ℂ) * Complex.I)
        = Work.LinnikAreas.zlFun ψ ((1 : ℂ) + (y : ℂ) * Complex.I + (β : ℂ)) := hF_eq y
    rw [Work.LinnikAreas.triFun, hFdef, hGdef]
    simp only [hZ]
    have hs1 : ((1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro h; have hh := congrArg Complex.re h; simp at hh
    have hs2 : ((1 : ℂ) + (y : ℂ) * Complex.I) + 1 ≠ 0 := by
      intro h; have hh := congrArg Complex.re h; simp at hh
    have h2 : ((2 : ℝ) + (y : ℂ) * Complex.I) = ((1 : ℂ) + (y : ℂ) * Complex.I) + 1 := by
      push_cast; ring
    rw [h2]
    field_simp
    ring
  have htri : (1 / (2 * Real.pi)) *
      (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I)) = A - A' := by
    have hcongr : (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I))
        = ∫ y in (-T)..T, (F y - G y) :=
      intervalIntegral.integral_congr (fun y _ => hpt y)
    rw [hcongr, intervalIntegral.integral_sub hIntF hIntG, hAdef, hA'def]
    ring
  -- B = x * A'
  have hBx : B = x * A' := by
    have hLseries : ∀ t : ℝ, LSeries b ((2 : ℝ) + (t : ℂ) * Complex.I)
        = LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      intro t
      have hb_eq : LSeries b ((2 : ℝ) + (t : ℂ) * Complex.I)
          = Work.LinnikAreas.zlFun ψ ((2 : ℝ) + (t : ℂ) * Complex.I + (((β - 1 : ℝ)) : ℂ)) := by
        rw [hbdef]
        exact Work.LinnikAreas.LSeries_lam_shift ψ hψ (β := β - 1) (by simp; linarith)
      rw [hb_eq, hF_eq t]
      congr 1
      push_cast; ring
    have hxpow : ∀ t : ℝ, (x : ℂ) ^ ((2 : ℝ) + (t : ℂ) * Complex.I)
        = x * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      intro t
      rw [show ((2 : ℝ) + (t : ℂ) * Complex.I)
          = ((1 : ℂ) + (t : ℂ) * Complex.I) + 1 by push_cast; ring]
      rw [Complex.cpow_add _ _ hxne, Complex.cpow_one]; ring
    have hpt' : ∀ t : ℝ, H t = x * G t := by
      intro t
      simp only [H, G]
      rw [hLseries t, hxpow t]
      ring
    have hint : (∫ t in (-T)..T, H t) = x * (∫ t in (-T)..T, G t) := by
      rw [show (∫ t in (-T)..T, H t) = ∫ t in (-T)..T, x * G t from
        intervalIntegral.integral_congr (fun t _ => hpt' t)]
      rw [intervalIntegral.integral_const_mul]
    rw [hBdef, hA'def, hint]; ring
  -- the bound for A' - M2/x
  have hA'bound : ‖A' - M2 / (x : ℂ)‖ ≤ C * (x * Work.LinnikAreas.perrErr ψ β x T) := by
    have hkey : x * (A' - M2 / (x : ℂ)) = B - M2 := by
      rw [hBx]; field_simp
    have hnorm : (x : ℝ) * ‖A' - M2 / (x : ℂ)‖ = ‖B - M2‖ := by
      rw [← hkey, norm_mul, norm_ofReal_complex, abs_of_pos hx0]
    calc ‖A' - M2 / (x : ℂ)‖ = ‖B - M2‖ / x := by
          rw [← hnorm]; field_simp
      _ ≤ (C * (∑' n : ℕ, ‖b n‖ * (x / (n : ℝ)) ^ (2 : ℝ)
            * min 1 (1 / (T * |Real.log (x / (n : ℝ))|)))) / x :=
          div_le_div_of_nonneg_right hkey2 hx0.le
      _ = C * (x * Work.LinnikAreas.perrErr ψ β x T) := by
          rw [hE2x, hE1x]
          have hxne' : (x : ℝ) ≠ 0 := hx0.ne'
          field_simp
  -- the main term identity
  have hSsmC : Work.LinnikAreas.SsmC ψ β x = M1 - M2 / (x : ℂ) := by
    have h2 : M2 = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) * a n := by
      rw [hM2def]; exact Finset.sum_congr rfl (fun n _ => hba n)
    rw [hM1def, h2]
    simp only [Work.LinnikAreas.SsmC, hadef]
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  refine ⟨(A - M1) - (A' - M2 / (x : ℂ)), ?_, ?_⟩
  · calc ‖(A - M1) - (A' - M2 / (x : ℂ))‖ ≤ ‖A - M1‖ + ‖A' - M2 / (x : ℂ)‖ := norm_sub_le _ _
      _ ≤ C * (∑' n : ℕ, ‖a n‖ * (x / (n : ℝ)) ^ (1 : ℝ)
            * min 1 (1 / (T * |Real.log (x / (n : ℝ))|)))
          + C * (x * Work.LinnikAreas.perrErr ψ β x T) := add_le_add hkey1 hA'bound
      _ = 2 * C * (x * Work.LinnikAreas.perrErr ψ β x T) := by rw [hE1x]; ring
  · rw [htri, hSsmC]; ring

end Work.Sieve
