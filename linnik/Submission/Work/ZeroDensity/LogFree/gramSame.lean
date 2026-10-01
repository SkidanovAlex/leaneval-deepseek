import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramProps
import Submission.Work.ZeroDensity.LogFree.GramResidueDefs
import Submission.Work.ZeroDensity.LogFree.norm_gramPhi_shift
import Submission.Work.ZeroDensity.LogFree.CrossLine
import Submission.Work.ZeroDensity.LogFree.zetaReg_differentiable
import Submission.Work.ZeroDensity.LogFree.GramSameProof
import Submission.Work.ZeroDensity.Ingham.verticalShiftPatchedPoleSelf
import Submission.Work.LinnikAreas.JutilaPieces.GammaVerticalDecay
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth

/-!
# `Work.ZeroDensity.LogFree.gramSame` — the exact-contour proof of `GramSame`

The `q`-free Gram entry `gramEntryFree W X U' ρ ρ'` is the smoothed sum
`Σ_n (Σ_{d|n}θ_d)² n^{1-ρ-conjρ'}(e^{-n/X} - e^{-n/U'})`.  Shifting the inverse-Mellin contour of
that sum from `Re z = 2` down to the line `Re z = Re s`, `s = 1 - ρ - conj ρ'`, crosses the single
ζ-pole at `z = s+1` and yields the exact identity

  `gramEntryFree W X U' ρ ρ' = (poleResidue W) · poleK X U' ρ ρ' + (1/2π) ∫_ℝ gramPhi(s.re+it) dt`

(`gramEntryFree_eq_pole_add_aux`), on whose line `z - s` is purely imaginary, so that the *sharp*
imaginary-axis bound `zetaImagAxisBound` applies to the ζ factor and no strip (convexity) input is
needed.  Bounding that integral gives `GramSame`.
-/

open DirichletCharacter Complex Filter MeasureTheory
open scoped Classical BigOperators Topology
set_option maxHeartbeats 1000000
noncomputable section

namespace Work.ZeroDensity.LogFree


lemma gamma_mul_sub_pow_tendsto (X U' : ℝ) (hX : 0 < X) (hU' : 0 < U') :
    Tendsto (fun z : ℂ => Complex.Gamma z * ((X : ℂ) ^ z - (U' : ℂ) ^ z))
      (𝓝[≠] (0 : ℂ)) (𝓝 (Complex.log (X : ℂ) - Complex.log (U' : ℂ))) := by
  have hXne : ((X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hUne : ((U' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU'.ne'
  -- the derivative of `z ↦ X^z - U'^z` at `0` is `log X - log U'`
  have hderX : HasDerivAt (fun z : ℂ => (X : ℂ) ^ z)
      ((X : ℂ) ^ (0:ℂ) * Complex.log (X:ℂ) * 1) 0 :=
    (hasDerivAt_id (0:ℂ)).const_cpow (Or.inl hXne)
  have hderU : HasDerivAt (fun z : ℂ => (U' : ℂ) ^ z)
      ((U' : ℂ) ^ (0:ℂ) * Complex.log (U':ℂ) * 1) 0 :=
    (hasDerivAt_id (0:ℂ)).const_cpow (Or.inl hUne)
  have hder : HasDerivAt (fun z : ℂ => (X : ℂ) ^ z - (U' : ℂ) ^ z)
      (Complex.log (X : ℂ) - Complex.log (U' : ℂ)) 0 := by
    have h := hderX.sub hderU
    have hval : (X : ℂ) ^ (0:ℂ) * Complex.log (X:ℂ) * 1
        - ((U' : ℂ) ^ (0:ℂ) * Complex.log (U':ℂ) * 1)
        = Complex.log (X : ℂ) - Complex.log (U' : ℂ) := by
      rw [Complex.cpow_zero, Complex.cpow_zero]; ring
    rw [hval] at h
    exact h
  have h0f : (fun z : ℂ => (X : ℂ) ^ z - (U' : ℂ) ^ z) 0 = 0 := by
    simp [Complex.cpow_zero]
  have hslope : Tendsto (fun z : ℂ => ((X : ℂ) ^ z - (U' : ℂ) ^ z) / z)
      (𝓝[≠] (0:ℂ)) (𝓝 (Complex.log (X : ℂ) - Complex.log (U' : ℂ))) := by
    have h := hder.tendsto_slope
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [slope]
    simp only [Complex.cpow_zero, sub_self, vsub_eq_sub, sub_zero, smul_eq_mul]
    rw [div_eq_inv_mul]
  -- `z * Γ z → 1`
  have hone : ∀ m : ℕ, (1 : ℂ) ≠ -↑m := by
    intro m hm
    have h := congrArg Complex.re hm
    simp at h
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hgamma : Tendsto (fun z : ℂ => z * Complex.Gamma z) (𝓝[≠] (0:ℂ)) (𝓝 (1 : ℂ)) := by
    have hG : Tendsto Complex.Gamma (𝓝 (1:ℂ)) (𝓝 (1:ℂ)) := by
      have h := (Complex.continuousAt_Gamma (1:ℂ) hone).tendsto
      simpa [Complex.Gamma_one] using h
    have hz : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (0:ℂ)) (𝓝 (1:ℂ)) := by
      have h : Tendsto (fun z : ℂ => z + 1) (𝓝 (0:ℂ)) (𝓝 (1:ℂ)) := by
        have h0 : Tendsto (fun z : ℂ => z + 1) (𝓝 (0:ℂ)) (𝓝 ((0:ℂ) + 1)) :=
          (continuousAt_id.add_const (1:ℂ)).tendsto
        simpa using h0
      exact h.mono_left inf_le_left
    have hcomp : Tendsto (fun z : ℂ => Complex.Gamma (z + 1)) (𝓝[≠] (0:ℂ)) (𝓝 (1:ℂ)) :=
      hG.comp hz
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz0
    exact Complex.Gamma_add_one z hz0
  have h2 : Tendsto (fun z : ℂ => (z * Complex.Gamma z)
      * (((X : ℂ) ^ z - (U' : ℂ) ^ z) / z)) (𝓝[≠] (0:ℂ))
      (𝓝 (Complex.log (X : ℂ) - Complex.log (U' : ℂ))) := by
    have := hgamma.mul hslope
    simpa using this
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  field_simp


/-- `gramA` is bounded by `⌈W⌉²` as soon as `Re s ≤ Re z`. -/
lemma norm_gramA_le_aux (W : ℝ) (hW : 1 < W) (s z : ℂ) (hz : s.re ≤ z.re) :
    ‖gramA W s z‖ ≤ ((Nat.ceil W : ℝ)) ^ 2 := by
  classical
  rw [gramA]
  have hcard : ((Finset.Icc 1 (Nat.ceil W)).card : ℝ) ≤ (Nat.ceil W : ℝ) := by
    rw [Nat.card_Icc]; simp
  have hcard0 : (0 : ℝ) ≤ ((Finset.Icc 1 (Nat.ceil W)).card : ℝ) := Nat.cast_nonneg _
  have hterm : ∀ d ∈ Finset.Icc 1 (Nat.ceil W), ∀ e ∈ Finset.Icc 1 (Nat.ceil W),
      ‖((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
        * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
        * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖ ≤ 1 := by
    intro d hd e he
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hlcm : 0 < Nat.lcm d e := Nat.lcm_pos (by omega) (by omega)
    have hbase : ‖(((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hlcm]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hlcm) ?_
      simp only [Complex.sub_re]
      linarith
    rw [norm_mul, norm_mul]
    have h1 := abs_thetaM_le_one' hW d
    have h2 := abs_thetaM_le_one' hW e
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    calc |Work.LinnikAreas.Density4.thetaM W d| * |Work.LinnikAreas.Density4.thetaM W e|
          * ‖(((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖
        ≤ 1 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) hbase
            (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc ‖∑ d ∈ Finset.Icc 1 (Nat.ceil W), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
        ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
          * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
          * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖
      ≤ ∑ d ∈ Finset.Icc 1 (Nat.ceil W), ‖∑ e ∈ Finset.Icc 1 (Nat.ceil W),
          ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
            * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
            * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.ceil W), ∑ e ∈ Finset.Icc 1 (Nat.ceil W), (1:ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        refine le_trans (norm_sum_le _ _) ?_
        exact Finset.sum_le_sum fun e he => hterm d hd e he
    _ = ((Finset.Icc 1 (Nat.ceil W)).card : ℝ) * ((Finset.Icc 1 (Nat.ceil W)).card : ℝ) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp [nsmul_eq_mul]
    _ ≤ (Nat.ceil W : ℝ) ^ 2 := by nlinarith [hcard, hcard0]


lemma gammaPow_diffOn (X U' : ℝ) (hX : 0 < X) (hU' : 0 < U') :
    DifferentiableOn ℂ (gammaPow X U') {z : ℂ | -1 < z.re} := by
  have hXne : ((X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hUne : ((U' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU'.ne'
  have hlim := gamma_mul_sub_pow_tendsto X U' hX hU'
  set f : ℂ → ℂ := fun w => (X : ℂ) ^ w - (U' : ℂ) ^ w with hfdef
  have hfder : deriv f 0 = Complex.log (X:ℂ) - Complex.log (U':ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => (X : ℂ) ^ z)
        ((X:ℂ)^(0:ℂ) * Complex.log (X:ℂ) * 1) 0 :=
      (hasDerivAt_id (0:ℂ)).const_cpow (Or.inl hXne)
    have h2 : HasDerivAt (fun z : ℂ => (U' : ℂ) ^ z)
        ((U':ℂ)^(0:ℂ) * Complex.log (U':ℂ) * 1) 0 :=
      (hasDerivAt_id (0:ℂ)).const_cpow (Or.inl hUne)
    have h := h1.sub h2
    have hval : (X:ℂ)^(0:ℂ) * Complex.log (X:ℂ) * 1 - ((U':ℂ)^(0:ℂ) * Complex.log (U':ℂ) * 1)
        = Complex.log (X:ℂ) - Complex.log (U':ℂ) := by
      rw [Complex.cpow_zero, Complex.cpow_zero]; ring
    rw [hval] at h
    exact h.deriv
  have hf_diff : Differentiable ℂ f := by
    intro z
    rw [hfdef]
    exact ((hasDerivAt_id z).const_cpow (Or.inl hXne)).differentiableAt.sub
      ((hasDerivAt_id z).const_cpow (Or.inl hUne)).differentiableAt
  have hds : Differentiable ℂ (dslope f 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (f := f) (c := 0) (s := Set.univ)
      Filter.univ_mem).mpr hf_diff.differentiableOn
  have hgam : DifferentiableOn ℂ (fun z : ℂ => Complex.Gamma (z + 1)) {z : ℂ | -1 < z.re} := by
    intro z hz
    rw [Set.mem_setOf_eq] at hz
    have hg1 : DifferentiableAt ℂ Complex.Gamma (z + 1) := by
      refine Complex.differentiableAt_Gamma _ (fun m hm => ?_)
      have h := congrArg Complex.re hm
      simp at h
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    have hl : DifferentiableAt ℂ (fun z : ℂ => z + 1) z := by fun_prop
    have hcomp : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) z := by
      have := DifferentiableAt.comp (f := fun z : ℂ => z + 1) (x := z) hg1 hl
      simpa only [Function.comp_def] using this
    exact hcomp.differentiableWithinAt
  have heq : gammaPow X U' = fun z : ℂ => Complex.Gamma (z + 1) * dslope f 0 z := by
    funext z
    rcases eq_or_ne z 0 with hz | hz
    · subst hz
      rw [gammaPow, Function.update_self, hlim.limUnder_eq]
      show Complex.log (X:ℂ) - Complex.log (U':ℂ)
        = Complex.Gamma ((0:ℂ) + 1) * dslope f 0 0
      rw [dslope_same, hfder]
      norm_num
    · rw [gammaPow_of_ne X U' hz]
      have h1 : dslope f 0 z = ((X:ℂ)^z - (U':ℂ)^z)/z := by
        rw [dslope_of_ne f hz, slope]
        simp only [hfdef, Complex.cpow_zero, sub_self, vsub_eq_sub, sub_zero, smul_eq_mul]
        rw [div_eq_inv_mul]
      rw [h1, Complex.Gamma_add_one z hz]
      field_simp
  rw [heq]
  exact hgam.mul hds.differentiableOn


/-- Pointwise decay of `gramPhi` on a horizontal line at height `|Im z| → ∞`. -/
lemma norm_gramPhi_strip_decay_aux (W X U' : ℝ) (s : ℂ) (hW : 1 < W) (hX : 0 < X)
    (hU' : 0 < U') (hs1 : -1 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∃ n : ℕ, ∀ z : ℂ, s.re ≤ z.re → z.re ≤ 2 →
      2 * (1 + |s.im|) ≤ |z.im| →
      ‖gramPhi W X U' s z‖ ≤ C * (1 + |z.im|) ^ n * Real.exp (-(Real.pi / 2) * |z.im|) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.LinnikAreas.JutilaPieces.GammaVerticalDecay.1 s.re 2 hs1 le_rfl
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  set A : ℝ := Real.exp (2 * |Real.log X|) + Real.exp (2 * |Real.log U'|) with hA
  set B : ℝ := (3 + |s.im|) ^ 4 with hB
  have hA0 : 0 < A := by rw [hA]; positivity
  have hB1 : 1 ≤ B := by
    rw [hB]
    exact one_le_pow₀ (by linarith [abs_nonneg s.im])
  refine ⟨C₁ * A * (C₂ * B) * ((Nat.ceil W : ℝ) ^ 2) + 1, by positivity, 16, ?_⟩
  intro z hzre1 hzre2 hzim
  have hzre_ge2 : (2:ℝ) ≤ |z.im| := by
    have : (2:ℝ) ≤ 2 * (1 + |s.im|) := by nlinarith [abs_nonneg s.im]
    linarith
  have hzre_ge1 : (1:ℝ) ≤ |z.im| := by linarith
  have hzne : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    rw [him] at hzre_ge2
    norm_num at hzre_ge2
  -- `Γ` factor
  have hgam : ‖Complex.Gamma z‖ ≤ C₁ * (1 + |z.im|) ^ (3 / 2 : ℝ)
      * Real.exp (-(Real.pi / 2) * |z.im|) := by
    have h := hC₁ z.re ⟨hzre1, hzre2⟩ z.im hzre_ge1
    rwa [Complex.re_add_im] at h
  -- `X^z - U'^z` factor
  have hpow : ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖ ≤ A := by
    have h1 : ‖(X : ℂ) ^ z‖ = X ^ (z.re) := Complex.norm_cpow_eq_rpow_re_of_pos hX z
    have h2 : ‖(U' : ℂ) ^ z‖ = U' ^ (z.re) := Complex.norm_cpow_eq_rpow_re_of_pos hU' z
    have hzr2 : |z.re| ≤ 2 := by
      rw [abs_le]; exact ⟨by linarith, hzre2⟩
    have hXle : X ^ (z.re) ≤ Real.exp (2 * |Real.log X|) := by
      rw [Real.rpow_def_of_pos hX]
      refine Real.exp_le_exp.mpr ?_
      calc Real.log X * z.re ≤ |Real.log X * z.re| := le_abs_self _
        _ = |Real.log X| * |z.re| := abs_mul _ _
        _ ≤ 2 * |Real.log X| := by nlinarith [abs_nonneg (Real.log X)]
    have hUle : U' ^ (z.re) ≤ Real.exp (2 * |Real.log U'|) := by
      rw [Real.rpow_def_of_pos hU']
      refine Real.exp_le_exp.mpr ?_
      calc Real.log U' * z.re ≤ |Real.log U' * z.re| := le_abs_self _
        _ = |Real.log U'| * |z.re| := abs_mul _ _
        _ ≤ 2 * |Real.log U'| := by nlinarith [abs_nonneg (Real.log U')]
    calc ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖ ≤ ‖(X : ℂ) ^ z‖ + ‖(U' : ℂ) ^ z‖ := norm_sub_le _ _
      _ = X ^ (z.re) + U' ^ (z.re) := by rw [h1, h2]
      _ ≤ Real.exp (2 * |Real.log X|) + Real.exp (2 * |Real.log U'|) := by linarith
      _ = A := by rw [hA]
  -- `ζ` factor
  have hzeta : ‖riemannZeta (z - s)‖ ≤ C₂ * B * (1 + |z.im|) ^ 4 := by
    have hre2 : -1 ≤ (z - s).re := by rw [Complex.sub_re]; linarith
    have hre3 : (z - s).re ≤ 3 := by rw [Complex.sub_re]; linarith
    have him1 : 1 ≤ |(z - s).im| := by
      rw [Complex.sub_im]
      have h := abs_sub_abs_le_abs_sub z.im s.im
      linarith [hzre_ge2, abs_nonneg s.im]
    have h1 := hC₂ (z - s).re (z - s).im hre2 hre3 him1
    have harg : ((z - s).re : ℂ) + Complex.I * ((z - s).im : ℂ) = z - s := by
      rw [mul_comm]; exact Complex.re_add_im (z - s)
    have h1' : ‖riemannZeta (z - s)‖ ≤ C₂ * (|(z - s).im| + 3) ^ 4 := by
      rwa [harg] at h1
    refine le_trans h1' ?_
    have himb : |(z - s).im| ≤ |z.im| + |s.im| := by
      rw [Complex.sub_im]; exact abs_sub _ _
    have hstep : |(z - s).im| + 3 ≤ (1 + |z.im|) * (3 + |s.im|) := by
      have h0 : (0:ℝ) ≤ |z.im| := abs_nonneg _
      have h1 : (0:ℝ) ≤ |s.im| := abs_nonneg _
      nlinarith
    have h4 : (|(z - s).im| + 3) ^ 4 ≤ ((1 + |z.im|) * (3 + |s.im|)) ^ 4 :=
      pow_le_pow_left₀ (by linarith) hstep 4
    calc C₂ * (|(z - s).im| + 3) ^ 4 ≤ C₂ * ((1 + |z.im|) * (3 + |s.im|)) ^ 4 :=
          mul_le_mul_of_nonneg_left h4 hC₂pos.le
      _ = C₂ * B * (1 + |z.im|) ^ 4 := by rw [hB, mul_pow]; ring
  -- `gramA` factor
  have hga : ‖gramA W s z‖ ≤ (Nat.ceil W : ℝ) ^ 2 := norm_gramA_le_aux W hW s z hzre1
  -- assemble
  set L : ℝ := 1 + |z.im| with hL
  set E : ℝ := Real.exp (-(Real.pi / 2) * |z.im|) with hE
  have hL1 : (1:ℝ) ≤ L := by rw [hL]; linarith [abs_nonneg z.im]
  have hEpos : 0 < E := by rw [hE]; positivity
  have hKpos : 0 < C₁ * A * (C₂ * B) * ((Nat.ceil W : ℝ) ^ 2) := by
    have h2 : (0:ℝ) < (Nat.ceil W : ℝ) ^ 2 := by positivity
    positivity
  have hpow32 : L ^ (3 / 2 : ℝ) ≤ L ^ 8 := by
    calc L ^ (3 / 2 : ℝ) ≤ L ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L ^ 4 := Real.rpow_natCast _ 4
      _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
  have hpow4 : L ^ 4 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
  -- the `gramPhi` factorisation
  have hprod : ‖Complex.Gamma z‖ * ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖ * ‖riemannZeta (z - s)‖
      * ‖gramA W s z‖
      ≤ (C₁ * L ^ (3 / 2 : ℝ) * E) * A * (C₂ * B * L ^ 4) * ((Nat.ceil W : ℝ) ^ 2) := by
    rw [hL, hE]
    refine mul_le_mul (mul_le_mul (mul_le_mul hgam hpow (norm_nonneg _) (by positivity)) hzeta
      (norm_nonneg _) (by positivity)) hga (norm_nonneg _) (by positivity)
  rw [gramPhi, gammaPow_of_ne X U' hzne, norm_mul, norm_mul, norm_mul]
  refine le_trans hprod ?_
  rw [show (C₁ * L ^ (3 / 2 : ℝ) * E) * A * (C₂ * B * L ^ 4) * ((Nat.ceil W : ℝ) ^ 2)
      = (C₁ * A * (C₂ * B) * ((Nat.ceil W : ℝ) ^ 2)) * (L ^ (3 / 2 : ℝ) * L ^ 4 * E) by ring]
  have h16 : L ^ (3 / 2 : ℝ) * L ^ 4 * E ≤ L ^ 16 * E := by
    have h2 : L ^ (3 / 2 : ℝ) * L ^ 4 ≤ L ^ 16 := by
      calc L ^ (3 / 2 : ℝ) * L ^ 4 ≤ L ^ (3 / 2 : ℝ) * L ^ 8 :=
            mul_le_mul_of_nonneg_left hpow4 (by positivity)
        _ ≤ L ^ 8 * L ^ 8 := mul_le_mul_of_nonneg_right hpow32 (by positivity)
        _ = L ^ 16 := by rw [← pow_add]
    exact mul_le_mul_of_nonneg_right h2 hEpos.le
  calc (C₁ * A * (C₂ * B) * ((Nat.ceil W : ℝ) ^ 2)) * (L ^ (3 / 2 : ℝ) * L ^ 4 * E)
      ≤ (C₁ * A * (C₂ * B) * ((Nat.ceil W : ℝ) ^ 2)) * (L ^ 16 * E) :=
        mul_le_mul_of_nonneg_left h16 hKpos.le
    _ ≤ (C₁ * A * (C₂ * B) * ((Nat.ceil W : ℝ) ^ 2) + 1) * (L ^ 16 * E) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith
    _ = (C₁ * A * (C₂ * B) * ((Nat.ceil W : ℝ) ^ 2) + 1) * L ^ 16 * E := by ring


/-- Off the ζ-pole `z = s+1`, `gramPsi` is `(z-(s+1))` times `gramPhi`. -/
lemma gramPsi_eq_mul_gramPhi_aux (W X U' : ℝ) (s z : ℂ) (hz : z ≠ s + 1) :
    gramPsi W X U' s z = (z - (s + 1)) * gramPhi W X U' s z := by
  have hne : z - s - 1 ≠ 0 := by
    intro h; exact hz (by linear_combination h)
  have harg : z - s - 1 + 1 = z - s := by ring
  rw [gramPsi, gramPhi, zetaReg_of_ne hne, harg]
  ring

/-- `(1 + R)^n * exp (-(π/2) R) → 0` as `R → ∞`. -/
lemma tendsto_one_add_pow_mul_exp (n : ℕ) :
    Tendsto (fun R : ℝ => (1 + R) ^ n * Real.exp (-(Real.pi / 2) * R)) atTop (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hbase : Tendsto (fun R : ℝ => R ^ ((n : ℝ)) * Real.exp (-(Real.pi / 2) * R))
      atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (Real.pi / 2)
      (by positivity : (0:ℝ) < Real.pi / 2)
  have hupper : Tendsto (fun R : ℝ => (2 : ℝ) ^ n
      * (R ^ ((n : ℝ)) * Real.exp (-(Real.pi / 2) * R))) atTop (nhds 0) := by
    have h := hbase.const_mul ((2 : ℝ) ^ n)
    simpa using h
  refine squeeze_zero' (f := fun R : ℝ => ‖(1 + R) ^ n * Real.exp (-(Real.pi / 2) * R)‖)
    (g := fun R : ℝ => (2 : ℝ) ^ n
      * (R ^ ((n : ℝ)) * Real.exp (-(Real.pi / 2) * R)))
    (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have h1 : (1 + R) ^ n ≤ (2 * R) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  have h2 : (2 * R) ^ n = (2 : ℝ) ^ n * R ^ n := mul_pow 2 R n
  have hcast : ((n : ℝ)) = ((n : ℕ) : ℝ) := rfl
  have h3 : R ^ n = R ^ ((n : ℝ)) := by rw [Real.rpow_natCast]
  calc ‖(1 + R) ^ n * Real.exp (-(Real.pi / 2) * R)‖
      = (1 + R) ^ n * Real.exp (-(Real.pi / 2) * R) :=
        Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_nonneg _))
    _ ≤ ((2 : ℝ) ^ n * R ^ n) * Real.exp (-(Real.pi / 2) * R) :=
        mul_le_mul_of_nonneg_right (by rw [← h2]; exact h1) (Real.exp_nonneg _)
    _ = (2 : ℝ) ^ n * (R ^ ((n : ℝ)) * Real.exp (-(Real.pi / 2) * R)) := by
        rw [← h3]; ring

/-- Horizontal decay of the regularised difference quotient
`H z = (gramPsi W X U' s z - gramPsi W X U' s (s+1))/(z - (s+1))`. -/
lemma dslope_gramPsi_horiz_aux (W X U' : ℝ) (s : ℂ) (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U')
    (hs1 : -1 < s.re) (hs2 : s.re ≤ 1) :
    (Tendsto (fun R : ℝ => ∫ x in (s.re)..2,
        dslope (gramPsi W X U' s) (s + 1) ((x : ℂ) + (R : ℂ) * Complex.I)) atTop (nhds 0)) ∧
    (Tendsto (fun R : ℝ => ∫ x in (s.re)..2,
        dslope (gramPsi W X U' s) (s + 1) ((x : ℂ) - (R : ℂ) * Complex.I)) atTop (nhds 0)) := by
  obtain ⟨C, hCpos, n, hC⟩ := norm_gramPhi_strip_decay_aux W X U' s hW hX hU' hs1
  set Bc : ℝ := ‖gramPsi W X U' s (s + 1)‖ with hBc
  have hBc0 : 0 ≤ Bc := norm_nonneg _
  set B₁ : ℝ := 2 * (C * (3 + ‖s‖)) + 1 with hB₁
  set B₂ : ℝ := Bc + 1 with hB₂
  have hB₁1 : C * (3 + ‖s‖) ≤ B₁ := by
    rw [hB₁]; nlinarith [hCpos, norm_nonneg s]
  have hB₂1 : Bc ≤ B₂ := by rw [hB₂]; linarith [hBc0]
  have hLpos : (0:ℝ) < 2 - s.re := by linarith
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℝ, 1 ≤ N₀ ∧ 2 * (1 + |s.im|) ≤ N₀ ∧ 2 * ‖s + 1‖ ≤ N₀ := by
    refine ⟨max 1 (max (2 * (1 + |s.im|)) (2 * ‖s + 1‖)), ?_, ?_, ?_⟩
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hN₀pos : 0 < N₀ := lt_of_lt_of_le one_pos hN₀.1
  set gfun : ℝ → ℝ := fun R : ℝ => (2 - s.re) * ((2 / R) * (B₁ * ((1 + R) ^ (n + 1)
      * Real.exp (-(Real.pi / 2) * R)) + B₂)) with hgfun
  have hlim : Tendsto gfun atTop (nhds 0) := by
    have h1 : Tendsto (fun R : ℝ => (2 : ℝ) / R) atTop (nhds (0:ℝ)) := by
      have h2 : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds (0:ℝ)) := tendsto_inv_atTop_zero
      simpa [div_eq_mul_inv] using h2.const_mul 2
    have h3 : Tendsto (fun R : ℝ => B₁ * ((1 + R) ^ (n + 1) * Real.exp (-(Real.pi / 2) * R))
        + B₂) atTop (nhds B₂) := by
      have h4 : Tendsto (fun R : ℝ => B₁ * ((1 + R) ^ (n + 1)
          * Real.exp (-(Real.pi / 2) * R))) atTop (nhds 0) := by
        have h5 := (tendsto_one_add_pow_mul_exp (n + 1)).const_mul B₁
        simpa [mul_assoc] using h5
      have hconst : Tendsto (fun _ : ℝ => B₂) atTop (nhds B₂) := tendsto_const_nhds
      have h6 := h4.add hconst
      simpa using h6
    have h7 : Tendsto (fun R : ℝ => (2 / R) * (B₁ * ((1 + R) ^ (n + 1)
        * Real.exp (-(Real.pi / 2) * R)) + B₂)) atTop (nhds 0) := by
      have h8 := h1.mul h3
      simpa using h8
    have h9 := h7.const_mul (2 - s.re)
    simpa [hgfun] using h9
  have key : ∀ r : ℝ, N₀ ≤ |r| → ∀ x : ℝ, s.re ≤ x → x ≤ 2 →
      ‖dslope (gramPsi W X U' s) (s + 1) ((x : ℂ) + (r : ℂ) * Complex.I)‖
        ≤ (2 / |r|) * (B₁ * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|)) + B₂) := by
    intro r hr x hx1 hx2
    have hrabs1 : (1:ℝ) ≤ |r| := le_trans hN₀.1 hr
    have hrabs2 : 2 * (1 + |s.im|) ≤ |r| := le_trans hN₀.2.1 hr
    have hrabs3 : 2 * ‖s + 1‖ ≤ |r| := le_trans hN₀.2.2 hr
    have hrabs0 : 0 < |r| := by linarith
    have hrabs1' : (0:ℝ) ≤ 1 + |r| := by linarith
    set z : ℂ := (x : ℂ) + (r : ℂ) * Complex.I with hz
    have hzre : z.re = x := by rw [hz]; simp
    have hzim : z.im = r := by rw [hz]; simp
    have hzu_im : (z - (s + 1)).im = r - s.im := by
      rw [Complex.sub_im, hzim, Complex.add_im]; simp
    have hzunorm : |r| / 2 ≤ ‖z - (s + 1)‖ := by
      have h1 : |r - s.im| ≤ ‖z - (s + 1)‖ := by
        rw [← hzu_im]; exact Complex.abs_im_le_norm _
      have h2 : |r| - |s.im| ≤ |r - s.im| := abs_sub_abs_le_abs_sub r s.im
      have h3 : |r| / 2 ≤ |r| - |s.im| := by
        have := le_trans hN₀.2.1 hr
        linarith [abs_nonneg s.im]
      linarith
    have hzunormpos : 0 < ‖z - (s + 1)‖ := by linarith
    have hzune : z - (s + 1) ≠ 0 := by
      intro h; rw [h] at hzunormpos; simp at hzunormpos
    have hdec := hC z (by rw [hzre]; exact hx1) (by rw [hzre]; exact hx2) (by
      rw [hzim]; exact le_trans hN₀.2.1 hr)
    have hdec' : ‖gramPhi W X U' s z‖ ≤ C * (1 + |r|) ^ n * Real.exp (-(Real.pi / 2) * |r|) := by
      rw [hzim] at hdec; exact hdec
    have hdslope : dslope (gramPsi W X U' s) (s + 1) z
        = (gramPsi W X U' s z - gramPsi W X U' s (s + 1)) / (z - (s + 1)) := by
      rw [dslope_of_ne _ (by intro h; exact hzune (by rw [h]; ring)), slope]
      simp only [smul_eq_mul, vsub_eq_sub]
      rw [div_eq_inv_mul, mul_comm]
    have hznelcm : z ≠ s + 1 := by intro h; apply hzune; rw [h]; ring
    have hpsi : gramPsi W X U' s z = (z - (s + 1)) * gramPhi W X U' s z :=
      gramPsi_eq_mul_gramPhi_aux W X U' s z hznelcm
    have hznorm : ‖z - (s + 1)‖ ≤ (3 + ‖s‖) * (1 + |r|) := by
      have h1 : ‖z - (s + 1)‖ ≤ ‖z‖ + ‖s + 1‖ := norm_sub_le _ _
      have h2 : ‖z‖ ≤ 2 + |r| := by
        rw [hz]
        calc ‖(x : ℂ) + (r : ℂ) * Complex.I‖ ≤ ‖(x : ℂ)‖ + ‖(r : ℂ) * Complex.I‖ :=
              norm_add_le _ _
          _ = |x| + |r| := by simp
          _ ≤ 2 + |r| := by
              have hxabs : |x| ≤ 2 := by rw [abs_le]; exact ⟨by linarith [hs1, hx1], hx2⟩
              linarith
      have h3 : ‖s + 1‖ ≤ ‖s‖ + 1 := by
        calc ‖s + 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          _ = ‖s‖ + 1 := by simp
      nlinarith [hrabs1, norm_nonneg s, norm_nonneg (s + 1)]
    have hpsi_bd : ‖gramPsi W X U' s z‖ ≤ C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1)
        * Real.exp (-(Real.pi / 2) * |r|) := by
      rw [hpsi, norm_mul]
      calc ‖z - (s + 1)‖ * ‖gramPhi W X U' s z‖
          ≤ ((3 + ‖s‖) * (1 + |r|)) * (C * (1 + |r|) ^ n * Real.exp (-(Real.pi / 2) * |r|)) :=
            mul_le_mul hznorm hdec' (norm_nonneg _) (by positivity)
        _ = C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) := by
            rw [pow_succ]; ring
    rw [hdslope, norm_div]
    have hnum : ‖gramPsi W X U' s z - gramPsi W X U' s (s + 1)‖ ≤ C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1)
        * Real.exp (-(Real.pi / 2) * |r|) + Bc := by
      calc ‖gramPsi W X U' s z - gramPsi W X U' s (s + 1)‖
          ≤ ‖gramPsi W X U' s z‖ + ‖gramPsi W X U' s (s + 1)‖ := norm_sub_le _ _
        _ ≤ C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc := by
            rw [hBc]; linarith
    have hnumNN : (0:ℝ) ≤ C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1)
        * Real.exp (-(Real.pi / 2) * |r|) + Bc := by
      have h5 : (0:ℝ) ≤ (1 + |r|) ^ (n + 1) := pow_nonneg (by linarith [abs_nonneg r]) _
      have h6 : (0:ℝ) ≤ Real.exp (-(Real.pi / 2) * |r|) := (Real.exp_pos _).le
      have h7 : (0:ℝ) ≤ C * (3 + ‖s‖) := le_of_lt (mul_pos hCpos (by positivity))
      have h8 : (0:ℝ) ≤ C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) := mul_nonneg h7 h5
      have h9 : (0:ℝ) ≤ C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1)
          * Real.exp (-(Real.pi / 2) * |r|) := mul_nonneg h8 h6
      exact add_nonneg h9 hBc0
    have hstep : (‖gramPsi W X U' s z - gramPsi W X U' s (s + 1)‖) / ‖z - (s + 1)‖
        ≤ (C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc)
          * (2 / |r|) := by
      calc (‖gramPsi W X U' s z - gramPsi W X U' s (s + 1)‖) / ‖z - (s + 1)‖
          ≤ (C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc)
            / ‖z - (s + 1)‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
        _ ≤ (C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc)
            / (|r| / 2) := div_le_div_of_nonneg_left hnumNN (by linarith) hzunorm
        _ = (C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc)
            * (2 / |r|) := by
            rw [div_eq_mul_inv, inv_div]
    -- `(A + Bc) * (2/|r|) ≤ (2/|r|) * (B₁ * poly + B₂)`
    have hpoly0 : (0:ℝ) ≤ (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) :=
      mul_nonneg (by positivity) (Real.exp_nonneg _)
    have h2r : (0:ℝ) ≤ 2 / |r| := div_nonneg (by norm_num) hrabs0.le
    have hAB : C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc
        ≤ B₁ * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|)) + B₂ := by
      have h1 : C * (3 + ‖s‖) * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|))
          ≤ B₁ * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|)) :=
        mul_le_mul_of_nonneg_right hB₁1 hpoly0
      have h2 : Bc ≤ B₂ := hB₂1
      calc C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc
          = C * (3 + ‖s‖) * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|)) + Bc := by ring
        _ ≤ B₁ * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|)) + B₂ := add_le_add h1 h2
    calc ‖gramPsi W X U' s z - gramPsi W X U' s (s + 1)‖ / ‖z - (s + 1)‖
        ≤ (C * (3 + ‖s‖) * (1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|) + Bc)
          * (2 / |r|) := hstep
      _ ≤ (B₁ * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|)) + B₂) * (2 / |r|) :=
          mul_le_mul_of_nonneg_right hAB h2r
      _ = (2 / |r|) * (B₁ * ((1 + |r|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |r|)) + B₂) := by ring
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun R : ℝ => ‖∫ x in (s.re)..2,
        dslope (gramPsi W X U' s) (s + 1) ((x : ℂ) + (R : ℂ) * Complex.I)‖)
      (g := gfun) (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop N₀] with R hR
    have hRabs : |R| = R := abs_of_nonneg (le_trans hN₀pos.le hR)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := s.re) (b := 2)
      (C := (2 / |R|) * (B₁ * ((1 + |R|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |R|)) + B₂))
      (f := fun x : ℝ => dslope (gramPsi W X U' s) (s + 1) ((x : ℂ) + (R : ℂ) * Complex.I))
      (fun x hx => ?_)
    · rw [abs_of_pos hLpos] at hb
      refine le_trans hb (le_of_eq ?_)
      rw [hgfun, hRabs]; ring
    · obtain ⟨hx1, hx2⟩ : s.re ≤ x ∧ x ≤ 2 := by
        rcases Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_of_lt h1, h2⟩
        · exfalso
          have hlt : (2:ℝ) < 1 := lt_of_lt_of_le h1 (le_trans h2 hs2)
          linarith
      exact key R (by rw [hRabs]; exact hR) x hx1 hx2
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun R : ℝ => ‖∫ x in (s.re)..2,
        dslope (gramPsi W X U' s) (s + 1) ((x : ℂ) - (R : ℂ) * Complex.I)‖)
      (g := gfun) (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop N₀] with R hR
    have hRabs : |R| = R := abs_of_nonneg (le_trans hN₀pos.le hR)
    have hRabsneg : |(-R)| = R := by rw [abs_neg]; exact hRabs
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := s.re) (b := 2)
      (C := (2 / |R|) * (B₁ * ((1 + |R|) ^ (n + 1) * Real.exp (-(Real.pi / 2) * |R|)) + B₂))
      (f := fun x : ℝ => dslope (gramPsi W X U' s) (s + 1) ((x : ℂ) - (R : ℂ) * Complex.I))
      (fun x hx => ?_)
    · rw [abs_of_pos hLpos] at hb
      refine le_trans hb (le_of_eq ?_)
      rw [hgfun, hRabs]; ring
    · obtain ⟨hx1, hx2⟩ : s.re ≤ x ∧ x ≤ 2 := by
        rcases Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_of_lt h1, h2⟩
        · exfalso
          have hlt : (2:ℝ) < 1 := lt_of_lt_of_le h1 (le_trans h2 hs2)
          linarith
      have hthis := key (-R) (by rw [hRabsneg]; exact hR) x hx1 hx2
      have hneg : ((x : ℂ) - (R : ℂ) * Complex.I) = ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      simpa only [hneg, hRabsneg, hRabs] using hthis


/-- Integrability of the integrand on the initial line `Re z = 2`. -/
lemma integrable_gramPhi_two_aux (W X U' : ℝ) (s : ℂ) (hX : 0 < X) (hU' : 0 < U')
    (hs : s.re < 0) :
    Integrable (fun t : ℝ => gramPhi W X U' s ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have h1 := integrable_mellinGram W X hX hs
  have h2 := integrable_mellinGram W U' hU' hs
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]
  have hzre : (((2 : ℂ) + (t : ℂ) * Complex.I)).re = 2 := by simp
  have hzne : ((2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have : (((2 : ℂ) + (t : ℂ) * Complex.I)).re = 0 := by rw [h]; simp
    rw [hzre] at this; norm_num at this
  have hw : 1 < (((2 : ℂ) + (t : ℂ) * Complex.I) - s).re := by
    rw [Complex.sub_re, hzre]; linarith
  have hS : (∑' n : ℕ, ((thetaS W n : ℝ) : ℂ) ^ 2
      * (n : ℂ) ^ (-(-s + ((2 : ℂ) + (t : ℂ) * Complex.I))))
      = riemannZeta (((2 : ℂ) + (t : ℂ) * Complex.I) - s)
        * gramA W s ((2 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [show (∑' n : ℕ, ((thetaS W n : ℝ) : ℂ) ^ 2
        * (n : ℂ) ^ (-(-s + ((2 : ℂ) + (t : ℂ) * Complex.I))))
        = ∑' n : ℕ, ((thetaS W n : ℝ) : ℂ) ^ 2
          * (n : ℂ) ^ (-(((2 : ℂ) + (t : ℂ) * Complex.I) - s)) from
      tsum_congr fun n => by
        rw [show -(-s + ((2 : ℂ) + (t : ℂ) * Complex.I))
          = -(((2 : ℂ) + (t : ℂ) * Complex.I) - s) by ring]]
    rw [gramDS_eq W (((2 : ℂ) + (t : ℂ) * Complex.I) - s) hw]
    congr 1
    rw [← gramA_shift W s (((2 : ℂ) + (t : ℂ) * Complex.I) - s)]
    congr 1
    ring
  rw [hS, gramPhi, gammaPow_of_ne X U' hzne]
  ring

/-- **The value of `gramPsi` at the ζ-pole.** -/
lemma gramPsi_pole_aux (W X U' : ℝ) (ρ ρ' : ℂ) (hρ : ρ.re < 1) (hρ' : ρ'.re < 1) :
    gramPsi W X U' (1 - ρ - (starRingEnd ℂ) ρ') (2 - ρ - (starRingEnd ℂ) ρ')
      = ((poleResidue W : ℝ) : ℂ) * poleK X U' ρ ρ' := by
  set s : ℂ := 1 - ρ - (starRingEnd ℂ) ρ' with hsdef
  have hsre : s.re = 1 - ρ.re - ρ'.re := by rw [hsdef]; simp
  have hz : (2 - ρ - (starRingEnd ℂ) ρ') = s + 1 := by rw [hsdef]; ring
  have hz0 : s + 1 ≠ 0 := by
    intro h
    have h1 : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re, hsre] at h1
    linarith
  rw [gramPsi, poleK, hz, gammaPow_of_ne X U' hz0]
  have hzz : s + 1 - s - 1 = 0 := by ring
  rw [hzz, zetaReg_zero, mul_one, gramA_eq_poleResidue]
  ring


/-- `gramPsi` is holomorphic on the half-plane `Re z > -1`. -/
lemma gramPsi_diffOn_aux (W X U' : ℝ) (s : ℂ) (hX : 0 < X) (hU' : 0 < U') :
    DifferentiableOn ℂ (gramPsi W X U' s) {z : ℂ | -1 < z.re} := by
  have hgp : DifferentiableOn ℂ (gammaPow X U') {z : ℂ | -1 < z.re} := gammaPow_diffOn X U' hX hU'
  have hzr : DifferentiableOn ℂ (fun z : ℂ => zetaReg (z - s - 1)) {z : ℂ | -1 < z.re} := by
    intro z hz
    have h1 : DifferentiableAt ℂ zetaReg (z - s - 1) := zetaReg_differentiable (z - s - 1)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w - s - 1) z := by fun_prop
    have h := DifferentiableAt.comp (f := fun w : ℂ => w - s - 1) (x := z) h1 h2
    simpa only [Function.comp_def] using h.differentiableWithinAt
  have hga : DifferentiableOn ℂ (fun z : ℂ => gramA W s z) {z : ℂ | -1 < z.re} :=
    fun z _ => (gramA_differentiableAt W s z).differentiableWithinAt
  exact (hgp.mul hzr).mul hga

/-- Integrability of the integrand on the shifted line `Re z = s.re`. -/
lemma integrable_gramPhi_shift_aux (W X U' : ℝ) (s : ℂ) (hW : 1 < W) (hX : 0 < X)
    (hU' : 0 < U') (hs1 : -1 < s.re) (hs0 : s.re < 0) :
    Integrable (fun t : ℝ => gramPhi W X U' s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C, hCpos, hC⟩ := norm_gramPhi_shift (1 / 2) (by norm_num)
  have hδpos : 0 < -s.re / 2 := by linarith
  have hIntΓ := integrable_gamma_shifted (1 : ℝ) (by norm_num) (δ := -s.re / 2) hδpos s.re hs1
    (by linarith)
  have hK0 : 0 ≤ C * (2 + |s.im|) * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2 := by
    have h1 : (0:ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    have h2 : (0:ℝ) ≤ X ^ (s.re) + U' ^ (s.re) :=
      add_nonneg (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hU'.le _)
    have h3 : (0:ℝ) ≤ (2 * W) ^ 2 := by positivity
    positivity
  have hmaj : Integrable (fun t : ℝ => C * (2 + |s.im|) * (X ^ (s.re) + U' ^ (s.re))
      * (2 * W) ^ 2 * (‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        * (2 + |t|) ^ (1:ℝ))) :=
    hIntΓ.const_mul _
  have hzne : ∀ t : ℝ, (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hΓc : Continuous (fun t : ℝ => Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    continuous_gamma_line_of_neg_one_lt hs1 hs0
  have hlin : Continuous (fun t : ℝ => ((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hpowc : Continuous (fun t : ℝ => (X : ℂ) ^ (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      - (U' : ℂ) ^ (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    (hlin.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).sub
      (hlin.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hU'.ne')))
  have hζc : Continuous (fun t : ℝ =>
      riemannZeta ((((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) - s)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hft : Tendsto (fun u : ℝ => (((s.re : ℝ) : ℂ) + (u : ℂ) * Complex.I) - s) (𝓝 t)
        (𝓝 ((((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) - s)) := by
      have hcont : Continuous (fun u : ℝ => (((s.re : ℝ) : ℂ) + (u : ℂ) * Complex.I) - s) := by
        fun_prop
      exact hcont.tendsto t
    have hargne : (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) - s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
    have hgt : Tendsto riemannZeta (𝓝 ((((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) - s))
        (𝓝 (riemannZeta ((((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) - s))) :=
      ((differentiableAt_riemannZeta hargne).continuousAt)
    exact hgt.comp hft
  have hAc : Continuous (fun t : ℝ => gramA W s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    simp only [gramA]
    refine continuous_finsetSum _ (fun d hd => continuous_finsetSum _ (fun e he => ?_))
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hlcm : ((Nat.lcm d e : ℕ) : ℂ) ≠ 0 := by
      have : 0 < Nat.lcm d e := Nat.lcm_pos (by omega) (by omega)
      exact_mod_cast this.ne'
    have hcp : Continuous (fun t : ℝ => s - (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      fun_prop
    exact continuous_const.mul (hcp.const_cpow (Or.inl hlcm))
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => gramPhi W X U' s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    have heqfun : (fun t : ℝ => gramPhi W X U' s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        = fun t : ℝ => Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            * ((X : ℂ) ^ (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              - (U' : ℂ) ^ (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I))
            * riemannZeta ((((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) - s)
            * gramA W s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      funext t
      rw [gramPhi, gammaPow_of_ne X U' (hzne t)]
    rw [heqfun]
    exact (((hΓc.mul hpowc).mul hζc).mul hAc).aestronglyMeasurable
  refine hmaj.mono' hmeas ?_
  filter_upwards with t
  have h1 := hC W X U' s hW hX hU' hs1 hs0 t
  have h2 : ((1:ℝ)/2 + 1/2) = (1:ℝ) := by norm_num
  rw [h2] at h1
  have h3 : (2 + |s.im| + |t|) ≤ (2 + |s.im|) * (2 + |t|) := by
    have ha : (0:ℝ) ≤ |s.im| := abs_nonneg s.im
    have hb : (0:ℝ) ≤ |t| := abs_nonneg t
    nlinarith
  have h5 : (0:ℝ) ≤ (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2 := by
    have h2' : (0:ℝ) ≤ X ^ (s.re) + U' ^ (s.re) :=
      add_nonneg (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hU'.le _)
    have h3' : (0:ℝ) ≤ (2 * W) ^ 2 := by positivity
    positivity
  have h6 : (0:ℝ) ≤ ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  calc ‖gramPhi W X U' s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C * (2 + |s.im| + |t|) ^ (1:ℝ)
          * ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2 := h1
    _ ≤ C * ((2 + |s.im|) * (2 + |t|))
          * ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2 := by
        have hp : (2 + |s.im| + |t|) ^ (1:ℝ) ≤ (2 + |s.im|) * (2 + |t|) := by
          rw [Real.rpow_one]; exact h3
        have hstep : C * (2 + |s.im| + |t|) ^ (1:ℝ) ≤ C * ((2 + |s.im|) * (2 + |t|)) :=
          mul_le_mul_of_nonneg_left hp hCpos.le
        have hstep2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep h6) h5
        calc C * (2 + |s.im| + |t|) ^ (1:ℝ)
              * ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
              * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2
            = (C * (2 + |s.im| + |t|) ^ (1:ℝ)
                * ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
                * ((X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2) := by ring
          _ ≤ (C * ((2 + |s.im|) * (2 + |t|))
                * ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
                * ((X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2) := hstep2
          _ = C * ((2 + |s.im|) * (2 + |t|))
              * ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
              * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2 := by ring
    _ = C * (2 + |s.im|) * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2
          * (‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ (1:ℝ)) := by
        rw [Real.rpow_one]; ring

/-- **The exact contour identity**: the `q`-free Gram entry is the pole term plus the integral of
`gramPhi` on the shifted line `Re z = Re s`, `s = 1 - ρ - conj ρ'`. -/
theorem gramEntryFree_eq_pole_add_aux (W X U' : ℝ) (ρ ρ' : ℂ)
    (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hρ : ρ.re < 1) (hρ' : ρ'.re < 1)
    (hs0 : (1 - ρ - (starRingEnd ℂ) ρ').re < 0) :
    gramEntryFree W X U' ρ ρ'
      = ((poleResidue W : ℝ) : ℂ) * poleK X U' ρ ρ'
        + (1 / (2 * Real.pi)) * ∫ t : ℝ,
            gramPhi W X U' (1 - ρ - (starRingEnd ℂ) ρ')
              (((1 - ρ - (starRingEnd ℂ) ρ').re : ℝ) + (t : ℂ) * Complex.I) := by
  set s : ℂ := 1 - ρ - (starRingEnd ℂ) ρ' with hsd
  have hsre : s.re = 1 - ρ.re - ρ'.re := by rw [hsd]; simp
  have hs1 : -1 < s.re := by rw [hsre]; linarith
  have hs0' : s.re < 0 := hs0
  have hslt1 : s.re < 1 := by rw [hsre]; linarith
  have hsle1 : s.re ≤ 1 := le_of_lt hslt1
  have hsrlt2 : s.re < 2 := by linarith
  have hu_nhds : {z : ℂ | -1 < z.re} ∈ 𝓝 (s + 1) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by
      simp only [Set.mem_setOf_eq, Complex.add_re, Complex.one_re]
      linarith)
  have hHstrip : DifferentiableOn ℂ (dslope (gramPsi W X U' s) (s + 1)) {z : ℂ | -1 < z.re} :=
    (Complex.differentiableOn_dslope (f := gramPsi W X U' s) (c := s + 1)
      (s := {z : ℂ | -1 < z.re}) hu_nhds).mpr (gramPsi_diffOn_aux W X U' s hX hU')
  have hH : ∀ R : ℝ, DifferentiableOn ℂ (dslope (gramPsi W X U' s) (s + 1))
      (Set.uIcc (s.re) 2 ×ℂ Set.uIcc (-R) R) := by
    intro R
    refine hHstrip.mono ?_
    intro z hz
    rw [Set.mem_setOf_eq]
    have h1 : s.re ≤ z.re := by
      have hmem := (Complex.mem_reProdIm.mp hz).1
      rcases Set.mem_uIcc.mp hmem with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact le_trans (by linarith) h
    linarith
  have hdec : ∀ R : ℝ, 1 ≤ R → ∀ z ∈ Set.uIcc (s.re) 2 ×ℂ Set.uIcc (-R) R,
      z ≠ s + 1 → z ≠ 0 →
      gramPhi W X U' s z = gramPsi W X U' s (s + 1) / (z - (s + 1))
        + dslope (gramPsi W X U' s) (s + 1) z := by
    intro R hR z hz hzu hz0
    have h1 : gramPsi W X U' s z = (z - (s + 1)) * gramPhi W X U' s z :=
      gramPsi_eq_mul_gramPhi_aux W X U' s z hzu
    have h2 : dslope (gramPsi W X U' s) (s + 1) z
        = (gramPsi W X U' s z - gramPsi W X U' s (s + 1)) / (z - (s + 1)) := by
      rw [dslope_of_ne _ hzu, slope]
      simp only [smul_eq_mul, vsub_eq_sub]
      rw [div_eq_inv_mul, mul_comm]
    rw [h2, h1]
    field_simp
    ring
  have hhoriz := dslope_gramPsi_horiz_aux W X U' s hW hX hU' hs1 hsle1
  have hint2 : Integrable (fun t : ℝ => gramPhi W X U' s ((2 : ℂ) + (t : ℂ) * Complex.I)) :=
    integrable_gramPhi_two_aux W X U' s hX hU' hs0'
  have hintd : Integrable (fun t : ℝ =>
      gramPhi W X U' s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    integrable_gramPhi_shift_aux W X U' s hW hX hU' hs1 hs0'
  have hu : s.re < (s + 1).re ∧ (s + 1).re < 2 := by
    constructor
    · simp only [Complex.add_re, Complex.one_re]; linarith
    · simp only [Complex.add_re, Complex.one_re]; linarith
  have hshift := Work.ZeroDensity.Ingham.verticalShiftPatchedPoleSelf (gramPhi W X U' s)
    (dslope (gramPsi W X U' s) (s + 1)) (s.re) 2 hsrlt2 (s + 1)
    (gramPsi W X U' s (s + 1)) hu hH hdec hhoriz.1 hhoriz.2 hintd hint2
  have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have hmellin : gramEntryFree W X U' ρ ρ'
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, gramPhi W X U' s (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    have h := gramEntryFree_eq_line W X U' ρ ρ' hX hU' hs0
    convert h using 2
    all_goals simp only [← h2c, hsd]
  have hp : gramPsi W X U' s (s + 1) = ((poleResidue W : ℝ) : ℂ) * poleK X U' ρ ρ' := by
    have h := gramPsi_pole_aux W X U' ρ ρ' hρ hρ'
    rw [show (1 - ρ - (starRingEnd ℂ) ρ') = s from hsd.symm] at h
    rw [show (2 - ρ - (starRingEnd ℂ) ρ') = s + 1 from by rw [hsd]; ring] at h
    exact h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hkey : (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)
      * (((poleResidue W : ℝ) : ℂ) * poleK X U' ρ ρ'))
      = ((poleResidue W : ℝ) : ℂ) * poleK X U' ρ ρ' := by
    field_simp
  rw [hmellin, hshift, hp, mul_add, hkey]
  ring

set_option maxHeartbeats 4000000

/-- **The bound on the shifted contour integral.** -/
theorem gramPhi_shift_integral_bound_aux (p : Params) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ E : ℝ, ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T →
      scale q T ≥ 6 →
      ∀ (ρ ρ' : ℂ), p.σ₀ ≤ ρ.re → ρ.re < 1 → p.σ₀ ≤ ρ'.re → ρ'.re < 1 →
      |ρ.im| ≤ T → |ρ'.im| ≤ T →
      c₀ ≤ (1 - ρ.re) * Lscale q T → c₀ ≤ (1 - ρ'.re) * Lscale q T →
      ‖(1 / (2 * Real.pi)) * ∫ t : ℝ, gramPhi (Dpow q T p.w) (Dpow q T p.x)
          (Dpow q T p.u / (Lscale q T) ^ 2) (1 - ρ - (starRingEnd ℂ) ρ')
          ((((1 - ρ - (starRingEnd ℂ) ρ').re : ℝ)) + (t : ℂ) * Complex.I)‖
        ≤ C * (Lscale q T) ^ E * Dpow q T (-p.η) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := norm_gramPhi_shift p.η p.hη
  have hδpos : 0 < min (2 * p.σ₀ - 1) (1 / 2) :=
    lt_min (by linarith [p.hσ₀]) (by norm_num)
  have hδlt : min (2 * p.σ₀ - 1) (1 / 2) < 1 := by
    have h := min_le_right (2 * p.σ₀ - 1) (1 / 2 : ℝ); linarith
  obtain ⟨CΓ, hCΓpos, hCΓ⟩ :=
    gamma_integral_shifted_cross ((1 : ℝ) / 2 + p.η) (min (2 * p.σ₀ - 1) (1 / 2))
      (by linarith [p.hη]) hδpos hδlt
  refine ⟨max 1 (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
    * (1 / (2 * Real.pi)) + 1), by positivity, 3, ?_⟩
  intro q hq _ T hT hD6 ρ ρ' hρσ hρ1 hρ'σ hρ'1 him him' hlam hlam'
  have hDpos : 0 < scale q T := by rw [scale]; positivity
  have hDge1 : 1 ≤ scale q T := by linarith
  have hDgt1 : 1 < scale q T := by linarith
  have hLpos : 0 < Lscale q T := by
    rw [Lscale]; exact Real.log_pos hDgt1
  have hLge1 : 1 ≤ Lscale q T := by
    rw [Lscale]
    refine (Real.le_log_iff_exp_le hDpos).mpr ?_
    have := Real.exp_one_lt_d9; linarith
  have hW1 : 1 < Dpow q T p.w := by
    rw [Dpow]; exact Real.one_lt_rpow hDgt1 p.hw
  have hWpos : 0 < Dpow q T p.w := lt_trans one_pos hW1
  have hXpos : 0 < Dpow q T p.x := by
    rw [Dpow]; exact Real.rpow_pos_of_pos hDpos _
  have hL2pos : 0 < (Lscale q T) ^ 2 := by positivity
  have hU'pos : 0 < Dpow q T p.u / (Lscale q T) ^ 2 := by
    rw [Dpow]; exact div_pos (Real.rpow_pos_of_pos hDpos _) hL2pos
  set μ : ℝ := ρ.re + ρ'.re - 1 with hμ
  have hμge : 2 * p.σ₀ - 1 ≤ μ := by rw [hμ]; linarith
  have hsre : (1 - ρ - (starRingEnd ℂ) ρ').re = -μ := by
    rw [hμ]
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.conj_re]
    ring
  have hsre_gt : -1 < (1 - ρ - (starRingEnd ℂ) ρ').re := by
    rw [hsre]; linarith [hρ1, hρ'1, hμ]
  have hsre_lt : (1 - ρ - (starRingEnd ℂ) ρ').re < 0 := by
    rw [hsre]; linarith [hμge, p.hσ₀]
  have h1μ : 2 * c₀ ≤ (1 - μ) * Lscale q T := by
    have h2 : (1 - ρ.re) * Lscale q T + (1 - ρ'.re) * Lscale q T
        = (2 - ρ.re - ρ'.re) * Lscale q T := by ring
    have h3 : 2 * c₀ ≤ (2 - ρ.re - ρ'.re) * Lscale q T := by
      rw [← h2]; linarith
    have h4 : 2 - ρ.re - ρ'.re = 1 - μ := by rw [hμ]; ring
    rwa [h4] at h3
  have h1μpos : 0 < 1 - μ := by nlinarith [h1μ, hc₀, hLpos]
  have hμδ : min (2 * p.σ₀ - 1) (1 / 2) ≤ -((1 - ρ - (starRingEnd ℂ) ρ').re) := by
    rw [hsre]; linarith [hμge, min_le_left (2 * p.σ₀ - 1) (1 / 2 : ℝ)]
  set sg : ℂ := 1 - ρ - (starRingEnd ℂ) ρ' with hsg
  have hsg_re : sg.re = -μ := by rw [hsg]; exact hsre
  have hΓint := integrable_gamma_shifted ((1 : ℝ) / 2 + p.η) (by linarith [p.hη]) hδpos
    sg.re (by rw [hsg_re]; linarith [p.hσ₀])
    (by rw [hsg_re]; linarith [hμge, hμδ])
  have hΓbd : ∫ t : ℝ, ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
      * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η) ≤ CΓ / (1 + sg.re) :=
    hCΓ sg.re (by rw [hsg_re]; linarith [p.hσ₀]) (by rw [hsg_re]; linarith [hμge, hμδ])
  have hpt : ∀ t : ℝ, ‖gramPhi (Dpow q T p.w) (Dpow q T p.x)
      (Dpow q T p.u / (Lscale q T) ^ 2) sg ((sg.re : ℝ) + (t : ℂ) * Complex.I)‖
      ≤ C₀ * (2 + |sg.im| + |t|) ^ ((1 : ℝ) / 2 + p.η)
        * ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
        * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
        * (2 * Dpow q T p.w) ^ 2 :=
    fun t => hC₀ (Dpow q T p.w) (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) sg
      hW1 hXpos hU'pos (by simpa only [hsg] using hsre_gt) (by simpa only [hsg] using hsre_lt) t
  have hsgim : |sg.im| ≤ 2 * T := by
    rw [hsg]
    have h : (1 - ρ - (starRingEnd ℂ) ρ').im = -ρ.im + ρ'.im := by simp
    rw [h]
    calc |-ρ.im + ρ'.im| ≤ |-ρ.im| + |ρ'.im| := abs_add_le _ _
      _ = |ρ.im| + |ρ'.im| := by rw [abs_neg]
      _ ≤ 2 * T := by linarith [him, him']
  set A : ℝ := C₀ * (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η)
      * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
      * (2 * Dpow q T p.w) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    have h1 : (0:ℝ) ≤ (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η) :=
      Real.rpow_nonneg (by linarith [abs_nonneg sg.im]) _
    have h2 : (0:ℝ) ≤ (Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re) :=
      add_nonneg (Real.rpow_nonneg (le_of_lt hXpos) _) (Real.rpow_nonneg (le_of_lt hU'pos) _)
    positivity
  have hmaj : ∀ t : ℝ, ‖gramPhi (Dpow q T p.w) (Dpow q T p.x)
      (Dpow q T p.u / (Lscale q T) ^ 2) sg ((sg.re : ℝ) + (t : ℂ) * Complex.I)‖
      ≤ A * (‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
        * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η)) := by
    intro t
    have h1 := hpt t
    have h2 : (2 + |sg.im| + |t|) ^ ((1 : ℝ) / 2 + p.η)
        ≤ (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η) * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by linarith [p.hη])
      nlinarith [abs_nonneg sg.im, abs_nonneg t]
    rw [hA]
    have h3 : C₀ * (2 + |sg.im| + |t|) ^ ((1:ℝ)/2 + p.η)
        ≤ C₀ * ((2 + |sg.im|) ^ ((1:ℝ)/2 + p.η) * (2 + |t|) ^ ((1:ℝ)/2 + p.η)) :=
      mul_le_mul_of_nonneg_left h2 hC₀pos.le
    have h4 : (0:ℝ) ≤ ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
    have h5 : (0:ℝ) ≤ (Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re) :=
      add_nonneg (Real.rpow_nonneg (le_of_lt hXpos) _) (Real.rpow_nonneg (le_of_lt hU'pos) _)
    have h6 : (0:ℝ) ≤ (2 * Dpow q T p.w) ^ 2 := by positivity
    have h7 : (0:ℝ) ≤ (2 + |t|) ^ ((1:ℝ)/2 + p.η) :=
      Real.rpow_nonneg (by linarith [abs_nonneg t]) _
    calc ‖gramPhi (Dpow q T p.w) (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) sg
            ((sg.re : ℝ) + (t : ℂ) * Complex.I)‖
        ≤ C₀ * (2 + |sg.im| + |t|) ^ ((1 : ℝ) / 2 + p.η)
          * ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
          * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
          * (2 * Dpow q T p.w) ^ 2 := h1
      _ ≤ C₀ * ((2 + |sg.im|) ^ ((1:ℝ)/2 + p.η) * (2 + |t|) ^ ((1:ℝ)/2 + p.η))
          * ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
          * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
          * (2 * Dpow q T p.w) ^ 2 := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h4)
            (mul_nonneg h5 h6)
          calc C₀ * (2 + |sg.im| + |t|) ^ ((1 : ℝ) / 2 + p.η)
                * ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
                * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
                * (2 * Dpow q T p.w) ^ 2
              = (C₀ * (2 + |sg.im| + |t|) ^ ((1 : ℝ) / 2 + p.η)
                  * ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖)
                  * (((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
                    * (2 * Dpow q T p.w) ^ 2) := by ring
            _ ≤ (C₀ * ((2 + |sg.im|) ^ ((1:ℝ)/2 + p.η)
                  * (2 + |t|) ^ ((1:ℝ)/2 + p.η))
                  * ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖)
                  * (((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
                    * (2 * Dpow q T p.w) ^ 2) := this
            _ = C₀ * ((2 + |sg.im|) ^ ((1:ℝ)/2 + p.η) * (2 + |t|) ^ ((1:ℝ)/2 + p.η))
                * ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
                * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
                * (2 * Dpow q T p.w) ^ 2 := by ring
      _ = (C₀ * (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η)
            * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
            * (2 * Dpow q T p.w) ^ 2)
          * (‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
            * (2 + |t|) ^ ((1:ℝ)/2 + p.η)) := by ring
  -- integrability and the integral bound
  have hint_maj : Integrable (fun t : ℝ => A * (‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
      * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η))) := hΓint.const_mul A
  have hnorm : ‖∫ t : ℝ, gramPhi (Dpow q T p.w) (Dpow q T p.x)
      (Dpow q T p.u / (Lscale q T) ^ 2) sg ((sg.re : ℝ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t : ℝ, A * (‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
        * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hint_maj
      (Filter.Eventually.of_forall fun t => hmaj t)
  have hΓbd' : ∫ t : ℝ, ‖Complex.Gamma ((sg.re : ℂ) + (t : ℂ) * Complex.I)‖
      * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η) ≤ CΓ * (Lscale q T / (2 * c₀)) := by
    refine le_trans hΓbd ?_
    have h1 : 1 + sg.re = 1 - μ := by rw [hsg_re]; ring
    rw [h1]
    have hLc : (1:ℝ) / (1 - μ) ≤ Lscale q T / (2 * c₀) := by
      rw [div_le_div_iff₀ h1μpos (by positivity : (0:ℝ) < 2 * c₀)]
      nlinarith [h1μ]
    calc CΓ / (1 - μ) = CΓ * (1 / (1 - μ)) := by rw [div_eq_mul_one_div]
      _ ≤ CΓ * (Lscale q T / (2 * c₀)) := mul_le_mul_of_nonneg_left hLc hCΓpos.le
  -- the bound for the constant `A`
  -- ============ the numerical assembly ============
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hμ0 : 0 ≤ μ := by linarith [hμge, p.hσ₀]
  have h2μ0 : 0 ≤ 2 * μ := by linarith
  -- `(2W)^2 ≤ 4 D^{2w}`
  have hWsq' : (2 * Dpow q T p.w) ^ (2 : ℕ) ≤ 4 * Dpow q T (2 * p.w) := by
    have h1 : (Dpow q T p.w) ^ (2 : ℕ) = Dpow q T (2 * p.w) := by
      rw [← Real.rpow_natCast (Dpow q T p.w) 2, Dpow, Dpow, ← Real.rpow_mul hDpos.le]
      congr 1
      push_cast
      ring
    have h2 : (2 * Dpow q T p.w) ^ (2 : ℕ) = 4 * Dpow q T (2 * p.w) := by
      rw [show (2 * Dpow q T p.w) ^ (2 : ℕ) = 4 * (Dpow q T p.w) ^ (2 : ℕ) by ring, h1]
    exact le_of_eq h2
  -- `X^σ ≤ D^{-u μ}`
  have hXle : (Dpow q T p.x) ^ (sg.re) ≤ Dpow q T (-(p.u * μ)) := by
    rw [hsg_re, Dpow, Dpow, ← Real.rpow_mul hDpos.le]
    refine Real.rpow_le_rpow_of_exponent_le hDge1 ?_
    have hx1 : p.u < p.x := lt_trans p.huv p.hvx
    nlinarith [hx1, hμ0]
  -- `U'^σ = D^{-u μ} L^{2 μ}`
  have hUle : (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re)
      = Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ) := by
    have hL2 : (Lscale q T) ^ 2 = (Lscale q T) ^ ((2 : ℕ) : ℝ) :=
      (Real.rpow_natCast (Lscale q T) 2).symm
    have hexpL : ((2 : ℕ) : ℝ) * -μ = -(2 * μ) := by push_cast; ring
    have hexpU : p.u * -μ = -(p.u * μ) := by ring
    rw [hsg_re, hL2, Dpow, Dpow,
      Real.div_rpow (Real.rpow_nonneg hDpos.le p.u) (Real.rpow_nonneg hLpos.le ((2:ℕ):ℝ)),
      ← Real.rpow_mul hDpos.le, ← Real.rpow_mul hLpos.le, hexpL, Real.rpow_neg hLpos.le,
      div_eq_mul_inv, inv_inv, hexpU]
  -- nonnegativity helpers
  have hXsg_nn : 0 ≤ (Dpow q T p.x) ^ (sg.re) :=
    Real.rpow_nonneg (Real.rpow_nonneg hDpos.le p.x) sg.re
  have hUsg_nn : 0 ≤ (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re) :=
    Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hDpos.le p.u) (pow_nonneg hLpos.le 2)) sg.re
  have hsum_nn : 0 ≤ (Dpow q T p.x) ^ (sg.re)
      + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re) := add_nonneg hXsg_nn hUsg_nn
  have h2W_nn : 0 ≤ (2 * Dpow q T p.w) ^ (2 : ℕ) :=
    pow_nonneg (mul_nonneg (by norm_num) hWpos.le) 2
  have hDun_nn : 0 ≤ Dpow q T (-(p.u * μ)) := Real.rpow_nonneg hDpos.le _
  have hL2μ_nn : 0 ≤ (Lscale q T) ^ (2 * μ) := Real.rpow_nonneg hLpos.le _
  have hDuw_nn : 0 ≤ Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ) :=
    mul_nonneg hDun_nn hL2μ_nn
  have h4dw_nn : 0 ≤ 4 * Dpow q T (2 * p.w) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hDpos.le _)
  -- `(2+|Im s|)^r ≤ 4^r D^r`
  have hsgim' : (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η)
      ≤ 4 ^ ((1 : ℝ) / 2 + p.η) * Dpow q T ((1 : ℝ) / 2 + p.η) := by
    have h1 : 2 + |sg.im| ≤ 2 + 2 * T := by linarith [hsgim]
    have h2 : 2 + 2 * T ≤ 4 * T := by linarith
    have h3 : (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η) ≤ (4 * T) ^ ((1 : ℝ) / 2 + p.η) :=
      Real.rpow_le_rpow (by linarith [abs_nonneg sg.im]) (le_trans h1 h2) (by linarith [p.hη])
    have h4 : (4 * T) ^ ((1 : ℝ) / 2 + p.η)
        = 4 ^ ((1 : ℝ) / 2 + p.η) * T ^ ((1 : ℝ) / 2 + p.η) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h5 : T ^ ((1 : ℝ) / 2 + p.η) ≤ Dpow q T ((1 : ℝ) / 2 + p.η) := by
      rw [Dpow]
      refine Real.rpow_le_rpow (by linarith) ?_ (by linarith [p.hη])
      rw [scale]; nlinarith [hq2, hT]
    rw [h4] at h3
    calc (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η)
        ≤ 4 ^ ((1 : ℝ) / 2 + p.η) * T ^ ((1 : ℝ) / 2 + p.η) := h3
      _ ≤ 4 ^ ((1 : ℝ) / 2 + p.η) * Dpow q T ((1 : ℝ) / 2 + p.η) :=
          mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg (by norm_num) _)
  -- `X^σ + U'^σ ≤ 2 D^{-u μ} L^{2 μ}`
  have hL2μ1 : 1 ≤ (Lscale q T) ^ (2 * μ) := by
    simpa [Real.one_rpow] using
      (Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hLge1 h2μ0)
  have hsum : (Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re)
      ≤ 2 * (Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ)) := by
    rw [hUle]
    have hDun : 0 ≤ Dpow q T (-(p.u * μ)) := Real.rpow_nonneg hDpos.le _
    have h3 : Dpow q T (-(p.u * μ)) ≤ Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ) :=
      le_mul_of_one_le_right hDun hL2μ1
    linarith [hXle, h3]
  -- the bound for `A`
  have hA_bound : A ≤ C₀ * (4 ^ ((1 : ℝ) / 2 + p.η) * Dpow q T ((1 : ℝ) / 2 + p.η))
      * (2 * (Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ))) * (4 * Dpow q T (2 * p.w)) := by
    rw [hA]
    calc C₀ * (2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η)
          * ((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
          * (2 * Dpow q T p.w) ^ (2 : ℕ)
        = C₀ * ((2 + |sg.im|) ^ ((1 : ℝ) / 2 + p.η)
            * (((Dpow q T p.x) ^ (sg.re) + (Dpow q T p.u / (Lscale q T) ^ 2) ^ (sg.re))
              * (2 * Dpow q T p.w) ^ (2 : ℕ))) := by ring
      _ ≤ C₀ * ((4 ^ ((1 : ℝ) / 2 + p.η) * Dpow q T ((1 : ℝ) / 2 + p.η))
            * ((2 * (Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ)))
              * (4 * Dpow q T (2 * p.w)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
          refine mul_le_mul hsgim' ?_ (mul_nonneg hsum_nn h2W_nn) ?_
          · exact mul_le_mul hsum hWsq' h2W_nn (mul_nonneg (by norm_num) hDuw_nn)
          · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hDpos.le _)
      _ = C₀ * (4 ^ ((1 : ℝ) / 2 + p.η) * Dpow q T ((1 : ℝ) / 2 + p.η))
          * (2 * (Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ)))
          * (4 * Dpow q T (2 * p.w)) := by ring
  -- `Γ`-integral factor
  have hΓ' : CΓ / (1 + sg.re) ≤ CΓ * (Lscale q T / (2 * c₀)) := by
    have h1 : 1 + sg.re = 1 - μ := by rw [hsg_re]; ring
    rw [h1]
    have hLc : (1:ℝ) / (1 - μ) ≤ Lscale q T / (2 * c₀) := by
      rw [div_le_div_iff₀ h1μpos (by positivity : (0:ℝ) < 2 * c₀)]
      nlinarith [h1μ]
    calc CΓ / (1 - μ) = CΓ * (1 / (1 - μ)) := by rw [div_eq_mul_one_div]
      _ ≤ CΓ * (Lscale q T / (2 * c₀)) := mul_le_mul_of_nonneg_left hLc hCΓpos.le
  -- the `D`-exponent
  have hDexp : Dpow q T ((1 : ℝ) / 2 + p.η) * Dpow q T (-(p.u * μ)) * Dpow q T (2 * p.w)
      ≤ Dpow q T (-p.η) := by
    have hexp : (1 : ℝ) / 2 + p.η - p.u * μ + 2 * p.w ≤ -p.η := by
      have hP2 := p.P2
      have hu0 : 0 < p.u := lt_trans p.hw p.hwu
      nlinarith [hP2, hμge, hu0]
    have e1 : Dpow q T ((1 : ℝ) / 2 + p.η) * Dpow q T (-(p.u * μ))
        = Dpow q T ((1 : ℝ) / 2 + p.η + -(p.u * μ)) := by
      rw [Dpow, Dpow, Dpow, ← Real.rpow_add hDpos]
    have e2 : Dpow q T ((1 : ℝ) / 2 + p.η + -(p.u * μ)) * Dpow q T (2 * p.w)
        = Dpow q T ((1 : ℝ) / 2 + p.η + -(p.u * μ) + 2 * p.w) := by
      rw [Dpow, Dpow, Dpow, ← Real.rpow_add hDpos]
    rw [e1, e2, Dpow, Dpow]
    refine Real.rpow_le_rpow_of_exponent_le hDge1 ?_
    linarith [hexp]
  -- the `L`-exponent
  have hLexp : (Lscale q T) ^ (2 * μ) * Lscale q T ≤ (Lscale q T) ^ (3 : ℝ) := by
    have hμle : μ ≤ 1 := by rw [hμ]; linarith [hρ1, hρ'1]
    have h1 : (Lscale q T) ^ (2 * μ + 1) ≤ (Lscale q T) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLge1 (by linarith)
    have h2 : (Lscale q T) ^ (2 * μ + 1) = (Lscale q T) ^ (2 * μ) * Lscale q T := by
      rw [Real.rpow_add hLpos, Real.rpow_one]
    rw [← h2]
    exact h1
  -- nonnegativity of the assembled factors
  have hLprod_nn : 0 ≤ (Lscale q T) ^ (2 * μ) * Lscale q T := mul_nonneg hL2μ_nn hLpos.le
  have hDn_nn : 0 ≤ Dpow q T (-p.η) := Real.rpow_nonneg hDpos.le _
  have hL3_nn : 0 ≤ (Lscale q T) ^ (3 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hK0_nn : 0 ≤ C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
      * (1 / (2 * Real.pi)) := by positivity
  -- assembly of the size bound
  have hfac : (1 / (2 * Real.pi)) * (A * (CΓ / (1 + sg.re)))
      ≤ (1 / (2 * Real.pi))
          * ((C₀ * (4 ^ ((1 : ℝ) / 2 + p.η) * Dpow q T ((1 : ℝ) / 2 + p.η)))
            * (2 * (Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ)))
            * (4 * Dpow q T (2 * p.w)) * (CΓ * (Lscale q T / (2 * c₀)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hA_bound hΓ' (div_nonneg hCΓpos.le (by linarith [hsre_gt]))
      (le_trans hA0 hA_bound)
  have heq : (1 / (2 * Real.pi))
        * ((C₀ * (4 ^ ((1 : ℝ) / 2 + p.η) * Dpow q T ((1 : ℝ) / 2 + p.η)))
            * (2 * (Dpow q T (-(p.u * μ)) * (Lscale q T) ^ (2 * μ)))
            * (4 * Dpow q T (2 * p.w)) * (CΓ * (Lscale q T / (2 * c₀))))
      = (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀)) * (1 / (2 * Real.pi)))
        * ((Dpow q T ((1 : ℝ) / 2 + p.η) * Dpow q T (-(p.u * μ)) * Dpow q T (2 * p.w))
          * ((Lscale q T) ^ (2 * μ) * Lscale q T)) := by ring
  have hstep2 : (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
          * (1 / (2 * Real.pi)))
        * ((Dpow q T ((1 : ℝ) / 2 + p.η) * Dpow q T (-(p.u * μ)) * Dpow q T (2 * p.w))
          * ((Lscale q T) ^ (2 * μ) * Lscale q T))
      ≤ (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀)) * (1 / (2 * Real.pi)))
          * (Dpow q T (-p.η) * (Lscale q T) ^ (3 : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hDexp hLexp hLprod_nn hDn_nn) hK0_nn
  have hmain : (1 / (2 * Real.pi)) * (A * (CΓ / (1 + sg.re)))
      ≤ (max 1 (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
          * (1 / (2 * Real.pi)) + 1)) * (Lscale q T) ^ (3 : ℝ) * Dpow q T (-p.η) := by
    have hKle : C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
          * (1 / (2 * Real.pi))
        ≤ max 1 (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
            * (1 / (2 * Real.pi)) + 1) := by
      have h := le_max_right (1:ℝ) (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ
        * (1 / (2 * c₀)) * (1 / (2 * Real.pi)) + 1)
      linarith
    rw [heq] at hfac
    refine le_trans hfac ?_
    calc (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
            * (1 / (2 * Real.pi)))
          * ((Dpow q T ((1 : ℝ) / 2 + p.η) * Dpow q T (-(p.u * μ))
              * Dpow q T (2 * p.w)) * ((Lscale q T) ^ (2 * μ) * Lscale q T))
        ≤ (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
            * (1 / (2 * Real.pi))) * (Dpow q T (-p.η) * (Lscale q T) ^ (3 : ℝ)) := hstep2
      _ = (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
            * (1 / (2 * Real.pi))) * (Lscale q T) ^ (3 : ℝ) * Dpow q T (-p.η) := by ring
      _ ≤ max 1 (C₀ * 8 * 4 ^ ((1 : ℝ) / 2 + p.η) * CΓ * (1 / (2 * c₀))
            * (1 / (2 * Real.pi)) + 1) * (Lscale q T) ^ (3 : ℝ) * Dpow q T (-p.η) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKle hL3_nn) hDn_nn
  -- final
  have hpiC : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    have h1 : (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hpiC]
  have hinteg : ‖∫ t : ℝ, gramPhi (Dpow q T p.w) (Dpow q T p.x)
      (Dpow q T p.u / (Lscale q T) ^ 2) sg ((sg.re : ℝ) + (t : ℂ) * Complex.I)‖
      ≤ A * (CΓ / (1 + sg.re)) := by
    refine le_trans hnorm ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hΓbd hA0
  exact le_trans (mul_le_mul_of_nonneg_left hinteg (by positivity)) hmain

/-- `Work.ZeroDensity.LogFree.GramSame p` (defined in `Submission/Work/ZeroDensity/LogFree/GramProps.lean`): for every `c₀ > 0` there are `C, E, D₀` such that for every pair of complex numbers `ρ, ρ'` with `p.σ₀ ≤ Re ρ < 1`, `p.σ₀ ≤ Re ρ' < 1`, `|Im| ≤ T` and `λ = (1-Re ρ)·Lscale q T ≥ c₀`, `λ' ≥ c₀`, the `q`-free Gram entry differs from the pole term by at most `C·(Lscale q T)^E·Dpow q T (-p.η)`:
`‖gramEntryFree W X U' ρ ρ' - (poleResidue W : ℂ) * poleK X U' ρ ρ'‖ ≤ C (Lscale q T)^E Dpow q T (-p.η)`,
with `W = Dpow q T p.w`, `X = Dpow q T p.x`, `U' = Dpow q T p.u/L²`, `s₀ = ρ+\barρ'-1`. Route (**exact contour identity, no Taylor expansion**): with `a_n = (Σ_{d|n}θ_d)²` and `A(s) = Σ_n a_n n^{-s} = ζ(s)Q(s)`, `Q(s) = Σ_{d,e≤W}θ_dθ_e[d,e]^{-s}` (a finite, entire sum), one has `Σ_n a_n n^{-s₀}e^{-n/Y} = (1/2πi)∫Γ(w)Y^wζ(s₀+w)Q(s₀+w)dw` for `Re w` large (Mellin representation; `mellinSmoothedDirichlet` in the workspace is a model). Subtracting the `Y = X` and `Y = U'` evaluations: the `Γ`-pole at `w=0` contributes `ζ(s₀)Q(s₀)(X⁰-U'⁰) = 0`, the `ζ`-pole at `w = 1-s₀` contributes exactly `Γ(2-ρ-\barρ')(X^{2-ρ-\barρ'}-U'^{2-ρ-\barρ'})Q(1) = poleK·poleResidue`, and the remainder is the contour integral on `Re w = 1-2σ₀ ∈ (-1,0)`, which crosses no further pole (`-1 < 1-2σ₀ < 1-s₀`). On that line `‖X^w-U'^w‖ ≤ 2U'^{1-2σ₀}`, `‖Q(s₀+w)‖ ≤ W²` (because `Re(s₀+w) = Re ρ+Re ρ'-2σ₀ > 0` and `[d,e] ≥ 1`), `‖Γ(1-2σ₀+iu)‖ ≤ C e^{-|u|}` (distance `2σ₀-1 > 0` from the pole at `0`), and `‖ζ(s₀+w)‖ ≤ C(1+2T+|u|)^{1/2+ε}` uniformly for `Re ∈ [0,1]` (functional equation plus the trivial bound; the `σ = 0` case is the proved `principalImagAxisBound`). The `u`-integral converges, so the remainder is at most `C_ε (2T)^{1/2+ε} W² U'^{1-2σ₀} = C_ε L^{2(2σ₀-1)}D^{1/2+ε+2w-u(2σ₀-1)} ≤ D^{-η}` for `ε ≤ η`, by `p.P2` (`u(2σ₀-1) ≥ 1/2+2w+2η`). -/
theorem gramSame (p : Work.ZeroDensity.LogFree.Params) :
    Work.ZeroDensity.LogFree.GramSame p := by
  intro c₀ hc₀
  obtain ⟨C, hCpos, E, hE⟩ := gramPhi_shift_integral_bound_aux p c₀ hc₀
  refine ⟨C, hCpos, E, 6, by norm_num, ?_⟩
  intro q hq _ T hT hD6 ρ ρ' hρσ hρ1 hρ'σ hρ'1 him him' hlam hlam'
  have hDpos : 0 < scale q T := by rw [scale]; positivity
  have hDgt1 : 1 < scale q T := by linarith
  have hLpos : 0 < Lscale q T := by rw [Lscale]; exact Real.log_pos hDgt1
  have hW1 : 1 < Dpow q T p.w := by rw [Dpow]; exact Real.one_lt_rpow hDgt1 p.hw
  have hXpos : 0 < Dpow q T p.x := by rw [Dpow]; exact Real.rpow_pos_of_pos hDpos _
  have hU'pos : 0 < Dpow q T p.u / (Lscale q T) ^ 2 := by
    rw [Dpow]; exact div_pos (Real.rpow_pos_of_pos hDpos _) (pow_pos hLpos 2)
  have hs0 : (1 - ρ - (starRingEnd ℂ) ρ').re < 0 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hρσ, hρ'σ, p.hσ₀]
  rw [gramEntryFree_eq_pole_add_aux (Dpow q T p.w) (Dpow q T p.x)
    (Dpow q T p.u / (Lscale q T) ^ 2) ρ ρ' hW1 hXpos hU'pos hρ1 hρ'1 hs0]
  rw [add_sub_cancel_left]
  exact hE q hq T hT hD6 ρ ρ' hρσ hρ1 hρ'σ hρ'1 him him' hlam hlam'

end Work.ZeroDensity.LogFree
