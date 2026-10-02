/-
# Self-contained critical-line estimates used by `CoeffSumLower`

The two elementary inputs of the critical-line integral bounds:

* `kernel_inv_bound` — the triangle-kernel denominator `s(s+1)` on the line `Re s = 1/2 - β`,
* `integrable_abs_kernel` — the (finite) integral of the majorant `(1+|y|)^{-6/5}`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Work.LinnikAreas.primeFactors_prod_one_add_rpow_le
import Submission.Work.Sieve.LFunction_imprimitive_factor
import Submission.Work.Sieve.zeta_critical_line_bound
import Submission.Work.Sieve.LFunction_critical_line_bound

open DirichletCharacter Complex Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace Work.LinnikAreas.BGTZ.CoeffSum

open Work.LinnikAreas

set_option maxHeartbeats 1000000

/-- On the vertical line `Re s = 1/2 - β` with `3/4 ≤ β < 1`, the triangle-kernel denominator
`s (s+1)` is bounded below by `(1+y²)/8`, hence its inverse by `32/(1+|y|)²`. -/
lemma kernel_inv_bound (β y : ℝ) (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) :
    ‖(((((1 / 2 - β : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
        ((((1 / 2 - β : ℝ) : ℂ) + (y : ℂ) * Complex.I) + 1))⁻¹)‖
      ≤ 32 * (1 + |y|) ^ (-(2 : ℝ)) := by
  set s : ℂ := ((1 / 2 - β : ℝ) : ℂ) + (y : ℂ) * Complex.I with hs
  have hsre : s.re = 1 / 2 - β := by rw [hs]; simp
  have hsim : s.im = y := by rw [hs]; simp
  have hs1re : (s + 1).re = 3 / 2 - β := by rw [Complex.add_re, hsre]; norm_num; ring
  have hs1im : (s + 1).im = y := by rw [Complex.add_im, hsim]; norm_num
  have hnorms : ‖s‖ ^ 2 = (1 / 2 - β) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]; ring
  have hnorm1 : ‖s + 1‖ ^ 2 = (3 / 2 - β) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hs1re, hs1im]; ring
  have ha : (1 / 16 : ℝ) ≤ (1 / 2 - β) ^ 2 := by nlinarith only [hβ]
  have hb : (1 / 4 : ℝ) ≤ (3 / 2 - β) ^ 2 := by nlinarith only [hβ1]
  have haux : 0 < (1 + y ^ 2) / 8 := by positivity
  have hsqrt_le : (1 + y ^ 2) / 8 ≤ ‖s‖ * ‖s + 1‖ := by
    have hrhs : ‖s‖ * ‖s + 1‖ = Real.sqrt (‖s‖ ^ 2 * ‖s + 1‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _) (‖s + 1‖ ^ 2), Real.sqrt_sq (norm_nonneg _),
        Real.sqrt_sq (norm_nonneg _)]
    rw [hrhs, show (1 + y ^ 2) / 8 = Real.sqrt (((1 + y ^ 2) / 8) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [hnorms, hnorm1]
    nlinarith only [ha, hb, sq_nonneg y]
  have hprod_pos : 0 < ‖s‖ * ‖s + 1‖ := lt_of_lt_of_le haux hsqrt_le
  calc ‖(s * (s + 1))⁻¹‖ = (‖s * (s + 1)‖)⁻¹ := norm_inv _
    _ = (‖s‖ * ‖s + 1‖)⁻¹ := by rw [norm_mul]
    _ ≤ ((1 + y ^ 2) / 8)⁻¹ := (inv_le_inv₀ hprod_pos haux).mpr hsqrt_le
    _ = 8 / (1 + y ^ 2) := by rw [inv_div]
    _ ≤ 32 * (1 + |y|) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |y|) (2 : ℝ), Real.rpow_two]
        rw [show (32 : ℝ) * ((1 + |y|) ^ 2)⁻¹ = 32 / (1 + |y|) ^ 2 by ring]
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + y ^ 2)
          (by positivity : (0 : ℝ) < (1 + |y|) ^ 2)]
        linarith only [sq_abs y, abs_nonneg y, sq_nonneg (|y| - 1), sq_nonneg y, hβ, hβ1]

/-- The majorant `(1+|y|)^{-7/6}` is integrable with integral at most `12`. -/
lemma integrable_abs_kernel :
    MeasureTheory.Integrable (fun y : ℝ => (1 + |y|) ^ (-(7 / 6 : ℝ))) ∧
      (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ))) ≤ 12 := by
  have hbase : IntegrableOn (fun x : ℝ => (x + 1) ^ (-(7 / 6 : ℝ))) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -(7 / 6 : ℝ)) (c := 0) (m := 1) (by norm_num)
      (by norm_num)
  have hIoi : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-(7 / 6 : ℝ))) (Ioi 0) := by
    refine hbase.congr_fun (fun y hy => ?_) measurableSet_Ioi
    rw [abs_of_pos hy, add_comm]
  have hIic : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-(7 / 6 : ℝ))) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  have hI : MeasureTheory.Integrable (fun x : ℝ => (1 + |x|) ^ (-(7 / 6 : ℝ))) := by
    have hu := hIic.union hIoi
    rwa [Iic_union_Ioi, integrableOn_univ] at hu
  refine ⟨hI, ?_⟩
  have hval : (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ)))
      = 2 * ∫ y : ℝ in Ioi (0 : ℝ), (1 + y) ^ (-(7 / 6 : ℝ)) :=
    integral_comp_abs (f := fun u : ℝ => (1 + u) ^ (-(7 / 6 : ℝ)))
  rw [hval]
  have hF : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -6 * (1 + t) ^ (-(1 / 6 : ℝ))) ((1 + x) ^ (-(7 / 6 : ℝ))) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith only [hx0]
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h2 : HasDerivAt (fun t : ℝ => (1 + t) ^ (-(1 / 6 : ℝ)))
        (1 * (-(1 / 6 : ℝ)) * (1 + x) ^ (-(1 / 6 : ℝ) - 1)) x :=
      h1.rpow_const (Or.inl hx1.ne')
    have h3 := h2.const_mul (-6)
    have h4 : (-6 : ℝ) * (1 * (-(1 / 6 : ℝ)) * (1 + x) ^ (-(1 / 6 : ℝ) - 1))
        = (1 + x) ^ (-(7 / 6 : ℝ)) := by
      rw [show -(1 / 6 : ℝ) - 1 = -(7 / 6 : ℝ) by norm_num]
      ring
    rwa [h4] at h3
  have hlim : Filter.Tendsto (fun t : ℝ => -6 * (1 + t) ^ (-(1 / 6 : ℝ)))
      Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun t : ℝ => (1 + t)) Filter.atTop Filter.atTop := by
      have h := Filter.tendsto_atTop_add_const_right (Filter.atTop) (1 : ℝ)
        (f := fun t : ℝ => t) Filter.tendsto_id
      simpa [add_comm] using h
    have h1 : Filter.Tendsto (fun t : ℝ => (1 + t) ^ (-(1 / 6 : ℝ))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp h2
    simpa using h1.const_mul (-6)
  have hFint : IntegrableOn (fun x : ℝ => (1 + x) ^ (-(7 / 6 : ℝ))) (Ioi (0 : ℝ)) := by
    simpa only [add_comm] using hbase
  have hcalc := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (f := fun t : ℝ => -6 * (1 + t) ^ (-(1 / 6 : ℝ)))
    (f' := fun x : ℝ => (1 + x) ^ (-(7 / 6 : ℝ))) hF hFint hlim
  have hval2 : (∫ y : ℝ in Ioi (0 : ℝ), (1 + y) ^ (-(7 / 6 : ℝ))) = 6 := by
    rw [hcalc]; norm_num
  rw [hval2]
  norm_num

/-- **Hypothesis A on the critical line, for imprimitive characters** (BGTZ Lemma 2.1). -/
lemma LHalfCritBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ (A θ : ℝ), Work.LinnikAreas.BGTZ.HypA A θ → ∀ t : ℝ,
        ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ θ := by
  refine ⟨1, one_pos, ?_⟩
  intro q _inst χ hχ hq3 A θ hHyp t
  obtain ⟨hApos, hθpos, _hθle, hbound⟩ := hHyp
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 :=
    Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
  have hpb := hbound χ.primitiveCharacter hprim hprimne t
  have hred := Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le χ hχ
    (σ := (1 / 2 : ℝ)) (t := t) (by norm_num)
  have hprod := primeFactors_prod_one_add_rpow_le q hq3 (σ := (1 / 2 : ℝ)) le_rfl
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1t : (0 : ℝ) ≤ 1 + |t| := by positivity
  have hNq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hle : (χ.conductor : ℝ) * (1 + |t|) ≤ (q : ℝ) * (1 + |t|) :=
    mul_le_mul_of_nonneg_right hNq h1t
  have hpow : ((χ.conductor : ℝ) * (1 + |t|)) ^ θ ≤ ((q : ℝ) * (1 + |t|)) ^ θ :=
    Real.rpow_le_rpow (by positivity) hle hθpos.le
  have hmul : ((q : ℝ) * (1 + |t|)) ^ θ = (q : ℝ) ^ θ * (1 + |t|) ^ θ :=
    Real.mul_rpow hqpos.le h1t
  calc ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := hred
    _ ≤ Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
          * (A * (((χ.conductor : ℝ) * (1 + |t|)) ^ θ)) :=
        mul_le_mul hprod hpb (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (A * (((q : ℝ) * (1 + |t|)) ^ θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hApos.le)
          (Real.exp_pos _).le
    _ = Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (A * ((q : ℝ) ^ θ * (1 + |t|) ^ θ)) := by
        rw [hmul]
    _ = 1 * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ θ := by
        ring

/-- Continuity, in `y`, of the critical-line integrand `triFun χ β x (1/2-β+iy)`. -/
lemma continuous_triFun_critline {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {β x : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hx : 0 < x) :
    Continuous fun y : ℝ => triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I) := by
  set s : ℝ → ℂ := fun y => ((1 / 2 - β : ℝ) : ℂ) + (y : ℂ) * Complex.I with hsdef
  have hsre : ∀ y : ℝ, (s y).re = 1 / 2 - β := by intro y; rw [hsdef]; simp
  have hs : Continuous s := by rw [hsdef]; fun_prop
  have hne1 : ∀ y : ℝ, s y + (β : ℂ) ≠ 1 := by
    intro y h
    have h2 := congrArg Complex.re h
    rw [Complex.add_re, hsre y] at h2
    simp at h2
  have hζ : Continuous fun y : ℝ => riemannZeta (s y + (β : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact ContinuousAt.comp (f := fun y' : ℝ => s y' + (β : ℂ)) (x := y)
      ((differentiableAt_riemannZeta (hne1 y)).continuousAt)
      ((hs.add continuous_const).continuousAt)
  have hL : Continuous fun y : ℝ => DirichletCharacter.LFunction χ (s y + (β : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact ContinuousAt.comp (f := fun y' : ℝ => s y' + (β : ℂ)) (x := y)
      ((DirichletCharacter.differentiableAt_LFunction χ (s y + (β : ℂ))
        (Or.inl (hne1 y))).continuousAt)
      ((hs.add continuous_const).continuousAt)
  have hpow : Continuous fun y : ℝ => (x : ℂ) ^ (s y) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact ContinuousAt.comp (f := s) (x := y)
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hx.ne'))
      hs.continuousAt
  have hne0 : ∀ y : ℝ, s y * (s y + 1) ≠ 0 := by
    intro y h
    rcases mul_eq_zero.mp h with h1 | h1
    · have : (s y).re = 0 := by rw [h1]; simp
      rw [hsre y] at this; linarith only [hβ, this]
    · have h3 : (s y + 1).re = 0 := by rw [h1]; simp
      rw [Complex.add_re, hsre y, Complex.one_re] at h3
      linarith only [hβ, hβ1, h3]
  have hinv : Continuous fun y : ℝ => (s y * (s y + 1))⁻¹ :=
    (hs.mul (hs.add continuous_const)).inv₀ hne0
  have hfun : (fun y : ℝ => triFun χ β x (s y)) = fun y : ℝ =>
      riemannZeta (s y + (β : ℂ)) * DirichletCharacter.LFunction χ (s y + (β : ℂ))
        * (x : ℂ) ^ (s y) * (s y * (s y + 1))⁻¹ := by
    funext y
    simp only [triFun, zlFun, div_eq_mul_inv]
  rw [hfun]
  exact ((hζ.mul hL).mul hpow).mul hinv

/-- **The critical-line integral bound from Hypothesis A** (the `hJ` input of the
Deuring--Heilbronn assembly): the integral of `triFun` along `Re s = 1/2 - β` is
`≪ A q^θ exp((log q)^{3/4}) x^{1/2-β}`. -/
theorem critLineIntegralHypA_self :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ {A θ β x : ℝ}, Work.LinnikAreas.BGTZ.HypA A θ → 3 / 4 ≤ β → β < 1 → 1 ≤ x →
      MeasureTheory.Integrable
          (fun y : ℝ => triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) ∧
        ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
          ≤ CJ * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β) := by
  obtain ⟨CL, hCLpos, hCL⟩ := LHalfCritBound
  refine ⟨max 1 (4096 * CL), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro q _inst χ hχ hq3 A θ β x hA hβ34 hβ1 hx1
  have hApos : 0 < A := hA.1
  have hθle : θ ≤ 1 / 4 + 1 / 100 := hA.2.2.1
  have hθlt : θ ≤ 1 / 3 := by linarith only [hβ34, hβ1, hθle]
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hβ : 1 / 2 < β := by linarith only [hβ34, hβ1]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hm : (0 : ℝ) ≤ A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β) :=
    mul_nonneg (mul_nonneg (mul_nonneg hApos.le (Real.rpow_nonneg hqpos.le _))
      (Real.exp_pos _).le) (Real.rpow_nonneg hx0.le _)
  have hcont := continuous_triFun_critline χ hβ hβ1 hx0
  have hpt : ∀ y : ℝ, ‖triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)‖
      ≤ (288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
          * (1 + |y|) ^ (-(7 / 6 : ℝ)) := by
    intro y
    set t : ℂ := ((1 / 2 - β : ℝ) : ℂ) + (y : ℂ) * Complex.I with ht
    have htre : t.re = 1 / 2 - β := by rw [ht]; simp
    have htβ : t + (β : ℂ) = (((1 / 2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I := by
      rw [ht]; push_cast; ring
    have hζ : ‖riemannZeta (t + (β : ℂ))‖ ≤ 9 * (1 + |y|) ^ ((1 / 2 : ℝ)) := by
      rw [htβ]; simpa using Work.Sieve.zeta_critical_line_aux y
    have hLb : ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
        ≤ CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |y|) ^ θ := by
      rw [htβ]; simpa using hCL q χ hχ hq3 A θ hA y
    have hxp : ‖(x : ℂ) ^ t‖ = x ^ (1 / 2 - β) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0 t, htre]
    have hker : ‖(t * (t + 1))⁻¹‖ ≤ 32 * (1 + |y|) ^ (-(2 : ℝ)) := by
      have h := kernel_inv_bound β y hβ34 hβ1
      rwa [← ht] at h
    have hmain : ‖triFun χ β x t‖ =
        ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
          * ‖(x : ℂ) ^ t‖ * ‖(t * (t + 1))⁻¹‖ := by
      simp only [triFun, zlFun, div_eq_mul_inv, norm_mul]
    rw [hmain]
    have hA1 : ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
        ≤ (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |y|) ^ θ) :=
      mul_le_mul hζ hLb (norm_nonneg _) (by positivity)
    have hA2 : ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
          * ‖(x : ℂ) ^ t‖
        ≤ (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |y|) ^ θ)
            * x ^ (1 / 2 - β) :=
      mul_le_mul hA1 (le_of_eq hxp) (norm_nonneg _) (by positivity)
    have hA3 : ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
          * ‖(x : ℂ) ^ t‖ * ‖(t * (t + 1))⁻¹‖
        ≤ (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |y|) ^ θ)
            * x ^ (1 / 2 - β) * (32 * (1 + |y|) ^ (-(2 : ℝ))) :=
      mul_le_mul hA2 hker (norm_nonneg _) (by positivity)
    refine hA3.trans ?_
    have hbase1 : (1 : ℝ) ≤ 1 + |y| := by have := abs_nonneg y; linarith only [this]
    have hpow : (1 + |y|) ^ ((1 / 2 : ℝ)) * (1 + |y|) ^ θ * (1 + |y|) ^ (-(2 : ℝ))
        ≤ (1 + |y|) ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |y|) (1 / 2) θ,
        ← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |y|) (1 / 2 + θ) (-(2 : ℝ))]
      exact Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith only [hβ34, hβ1, hθle])
    have hgroup : (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (1 + |y|) ^ θ)
            * x ^ (1 / 2 - β) * (32 * (1 + |y|) ^ (-(2 : ℝ)))
        = (288 * CL) * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
            * ((1 + |y|) ^ ((1 / 2 : ℝ)) * (1 + |y|) ^ θ * (1 + |y|) ^ (-(2 : ℝ))) := by ring
    rw [hgroup]
    calc (288 * CL) * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
          * ((1 + |y|) ^ ((1 / 2 : ℝ)) * (1 + |y|) ^ θ * (1 + |y|) ^ (-(2 : ℝ)))
        ≤ (288 * CL) * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
          * (1 + |y|) ^ (-(7 / 6 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg (by norm_num) hCLpos.le) hm)
      _ = (288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
          * (1 + |y|) ^ (-(7 / 6 : ℝ)) := by ring
  have hint : MeasureTheory.Integrable
      (fun y : ℝ => triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) :=
    (integrable_abs_kernel.1.const_mul
        (288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  have hMnn : (0 : ℝ) ≤ 288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
      * x ^ (1 / 2 - β) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCLpos.le) hApos.le)
      (Real.rpow_nonneg hqpos.le _)) (Real.exp_pos _).le) (Real.rpow_nonneg hx0.le _)
  have hnormc : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    have he : (1 / (2 * Real.pi) : ℂ) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith only [Real.pi_gt_three, hβ34, hβ1]
  have step2 : (∫ y : ℝ, ‖triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)‖)
      ≤ (288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
        * (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ))) := by
    rw [← integral_const_mul]
    exact integral_mono_ae hint.norm (integrable_abs_kernel.1.const_mul _)
      (Filter.Eventually.of_forall (fun y => hpt y))
  have step4 : (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ))) ≤ 12 := integrable_abs_kernel.2
  calc ‖(1 / (2 * Real.pi)) *
        (∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
      ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ‖(∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖(∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ :=
        mul_le_mul_of_nonneg_right hnormc (norm_nonneg _)
    _ = ‖(∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ := one_mul _
    _ ≤ (∫ y : ℝ, ‖triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)‖) :=
        norm_integral_le_integral_norm _
    _ ≤ (288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
        * (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ))) := step2
    _ ≤ (288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
        * 12 := mul_le_mul_of_nonneg_left step4 hMnn
    _ ≤ max 1 (4096 * CL) * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
        * x ^ (1 / 2 - β) := by
        have h1 : (3456 : ℝ) * CL * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * x ^ (1 / 2 - β))
            ≤ 4096 * CL * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * x ^ (1 / 2 - β)) := by
          apply mul_le_mul_of_nonneg_right _ hm
          linarith only [hCLpos]
        have h2 : (4096 : ℝ) * CL * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * x ^ (1 / 2 - β))
            ≤ max 1 (4096 * CL) * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
              * x ^ (1 / 2 - β)) := by
          apply mul_le_mul_of_nonneg_right _ hm
          exact le_max_right _ _
        calc (288 * CL * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * x ^ (1 / 2 - β))
              * 12
            = (3456 * CL) * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
                * x ^ (1 / 2 - β)) := by ring
          _ ≤ 4096 * CL * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
                * x ^ (1 / 2 - β)) := h1
          _ ≤ max 1 (4096 * CL) * (A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
                * x ^ (1 / 2 - β)) := h2
          _ = max 1 (4096 * CL) * A * (q : ℝ) ^ θ * Real.exp ((Real.log q) ^ (3 / 4 : ℝ))
                * x ^ (1 / 2 - β) := by ring

/-- **The critical-line integral bound from convexity** (used for the Hecke lower bound):
`‖(1/2π)∫ triFun‖ ≪ q^{1/3} log(2q+2) x^{1/2-β}`. -/
theorem critLineIntegralConvex_self :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ {β x : ℝ}, 3 / 4 ≤ β → β < 1 → 1 ≤ x →
      MeasureTheory.Integrable (fun y : ℝ =>
          triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) ∧
      ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
        ≤ C * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.Sieve.LFunction_critical_line_bound
  refine ⟨max 1 (4096 * C₀), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro q _inst χ hχ hq3 β x hβ34 hβ1 hx1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hβ : 1 / 2 < β := by linarith only [hβ34, hβ1]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogpos : (0 : ℝ) < Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_pos; linarith only [hβ34, hβ1, hqpos]
  have hm : (0 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hqpos.le _) hlogpos.le) (Real.rpow_nonneg hx0.le _)
  have hcont := continuous_triFun_critline χ hβ hβ1 hx0
  have hpt : ∀ y : ℝ, ‖triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)‖
      ≤ (288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
          * (1 + |y|) ^ (-(7 / 6 : ℝ)) := by
    intro y
    set t : ℂ := ((1 / 2 - β : ℝ) : ℂ) + (y : ℂ) * Complex.I with ht
    have htre : t.re = 1 / 2 - β := by rw [ht]; simp
    have htβ : t + (β : ℂ) = (((1 / 2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I := by
      rw [ht]; push_cast; ring
    have hζ : ‖riemannZeta (t + (β : ℂ))‖ ≤ 9 * (1 + |y|) ^ ((1 / 2 : ℝ)) := by
      rw [htβ]; simpa using Work.Sieve.zeta_critical_line_aux y
    have hLb : ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
        ≤ C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * (1 + |y|) ^ ((1 : ℝ) / 3) := by
      rw [htβ]; simpa using hC₀ q χ hχ y
    have hxp : ‖(x : ℂ) ^ t‖ = x ^ (1 / 2 - β) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0 t, htre]
    have hker : ‖(t * (t + 1))⁻¹‖ ≤ 32 * (1 + |y|) ^ (-(2 : ℝ)) := by
      have h := kernel_inv_bound β y hβ34 hβ1
      rwa [← ht] at h
    have hmain : ‖triFun χ β x t‖ =
        ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
          * ‖(x : ℂ) ^ t‖ * ‖(t * (t + 1))⁻¹‖ := by
      simp only [triFun, zlFun, div_eq_mul_inv, norm_mul]
    rw [hmain]
    have hA1 : ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
        ≤ (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * (1 + |y|) ^ ((1 : ℝ) / 3)) :=
      mul_le_mul hζ hLb (norm_nonneg _) (by positivity)
    have hA2 : ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
          * ‖(x : ℂ) ^ t‖
        ≤ (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * (1 + |y|) ^ ((1 : ℝ) / 3))
            * x ^ (1 / 2 - β) :=
      mul_le_mul hA1 (le_of_eq hxp) (norm_nonneg _) (by positivity)
    have hA3 : ‖riemannZeta (t + (β : ℂ))‖ * ‖DirichletCharacter.LFunction χ (t + (β : ℂ))‖
          * ‖(x : ℂ) ^ t‖ * ‖(t * (t + 1))⁻¹‖
        ≤ (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * (1 + |y|) ^ ((1 : ℝ) / 3))
            * x ^ (1 / 2 - β) * (32 * (1 + |y|) ^ (-(2 : ℝ))) :=
      mul_le_mul hA2 hker (norm_nonneg _) (by positivity)
    refine hA3.trans ?_
    have hbase1 : (1 : ℝ) ≤ 1 + |y| := by have := abs_nonneg y; linarith only [this]
    have hpow : (1 + |y|) ^ ((1 / 2 : ℝ)) * (1 + |y|) ^ ((1 : ℝ) / 3) * (1 + |y|) ^ (-(2 : ℝ))
        ≤ (1 + |y|) ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |y|) (1 / 2) ((1 : ℝ) / 3),
        ← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |y|) (1 / 2 + (1 : ℝ) / 3) (-(2 : ℝ))]
      exact Real.rpow_le_rpow_of_exponent_le hbase1 (by norm_num)
    have hgroup : (9 * (1 + |y|) ^ ((1 / 2 : ℝ)))
            * (C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * (1 + |y|) ^ ((1 : ℝ) / 3))
            * x ^ (1 / 2 - β) * (32 * (1 + |y|) ^ (-(2 : ℝ)))
        = (288 * C₀) * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
            * ((1 + |y|) ^ ((1 / 2 : ℝ)) * (1 + |y|) ^ ((1 : ℝ) / 3)
                * (1 + |y|) ^ (-(2 : ℝ))) := by ring
    rw [hgroup]
    calc (288 * C₀) * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
          * ((1 + |y|) ^ ((1 / 2 : ℝ)) * (1 + |y|) ^ ((1 : ℝ) / 3)
              * (1 + |y|) ^ (-(2 : ℝ)))
        ≤ (288 * C₀) * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
          * (1 + |y|) ^ (-(7 / 6 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hm)
      _ = (288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
          * (1 + |y|) ^ (-(7 / 6 : ℝ)) := by ring
  have hint : MeasureTheory.Integrable
      (fun y : ℝ => triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) :=
    (integrable_abs_kernel.1.const_mul
        (288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
          * x ^ (1 / 2 - β))).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  have hMnn : (0 : ℝ) ≤ 288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
      * x ^ (1 / 2 - β) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le)
      (Real.rpow_nonneg hqpos.le _)) hlogpos.le) (Real.rpow_nonneg hx0.le _)
  have hnormc : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    have he : (1 / (2 * Real.pi) : ℂ) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith only [Real.pi_gt_three, hβ34, hβ1]
  have step2 : (∫ y : ℝ, ‖triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)‖)
      ≤ (288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
        * (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ))) := by
    rw [← integral_const_mul]
    exact integral_mono_ae hint.norm (integrable_abs_kernel.1.const_mul _)
      (Filter.Eventually.of_forall (fun y => hpt y))
  have step4 : (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ))) ≤ 12 := integrable_abs_kernel.2
  calc ‖(1 / (2 * Real.pi)) *
        (∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
      ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ‖(∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖(∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ :=
        mul_le_mul_of_nonneg_right hnormc (norm_nonneg _)
    _ = ‖(∫ y : ℝ, triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ := one_mul _
    _ ≤ (∫ y : ℝ, ‖triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)‖) :=
        norm_integral_le_integral_norm _
    _ ≤ (288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
        * (∫ y : ℝ, (1 + |y|) ^ (-(7 / 6 : ℝ))) := step2
    _ ≤ (288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
        * 12 := mul_le_mul_of_nonneg_left step4 hMnn
    _ ≤ max 1 (4096 * C₀) * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
        * x ^ (1 / 2 - β) := by
        have h1 : (3456 : ℝ) * C₀ * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
              * x ^ (1 / 2 - β))
            ≤ 4096 * C₀ * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
              * x ^ (1 / 2 - β)) := by
          apply mul_le_mul_of_nonneg_right _ hm
          linarith only [hC₀pos]
        have h2 : (4096 : ℝ) * C₀ * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
              * x ^ (1 / 2 - β))
            ≤ max 1 (4096 * C₀) * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
              * x ^ (1 / 2 - β)) := by
          apply mul_le_mul_of_nonneg_right _ hm
          exact le_max_right _ _
        calc (288 * C₀ * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
              * x ^ (1 / 2 - β)) * 12
            = (3456 * C₀) * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * x ^ (1 / 2 - β)) := by ring
          _ ≤ 4096 * C₀ * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * x ^ (1 / 2 - β)) := h1
          _ ≤ max 1 (4096 * C₀) * ((q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * x ^ (1 / 2 - β)) := h2
          _ = max 1 (4096 * C₀) * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2)
                * x ^ (1 / 2 - β) := by ring

end Work.LinnikAreas.BGTZ.CoeffSum
