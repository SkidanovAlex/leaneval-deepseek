import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.RatioAux
import Submission.Work.LinnikAreas.smoothedAbel
import Submission.Work.LinnikAreas.integrableOnEfunCpowIoi
import Submission.Work.LinnikAreas.normSetIntegralIoiEfunLe
import Submission.Work.LinnikAreas.normSetIntegralIocEfunLe

namespace Work.LinnikAreas

open MeasureTheory intervalIntegral Set
open scoped BigOperators

/-- Exponent bookkeeping: `-↑(1+β) = -(↑β+1)`. -/
lemma neg_ofReal_one_add_cast (β : ℝ) : (-(((1 + β : ℝ)) : ℂ)) = -((β : ℂ) + 1) := by
  push_cast; ring

/-- **Truncation of the Abel integral at `x`.**  With `f t = E(t) t^{-(β+1)}` integrable on
`(1,∞)` and `∫_1^∞ f = L(1,χ)/(1-β)`, the integral over `x..∞` splits off:

  `∫_1^x f = L(1,χ)/(1-β) - ∫_x^∞ f`.

This is the step that lets the identity `∫_1^∞ E(t) t^{-1-β} dt = L(1,χ)/(1-β)` (a hypothesis,
`hfac`) cancel the constant `-βL(1,χ)/(1-β)` coming from the Abel transform of the main term. -/
lemma intervalIntegral_Efun_cpow_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {β : ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1))) (Set.Ioi 1))
    (hfac : (∫ x in Set.Ioi (1:ℝ), Work.LinnikAreas.Efun χ x * (x : ℂ) ^ (-(((1 + β : ℝ)) : ℂ)))
        = DirichletCharacter.LFunction χ 1 / (1 - β))
    {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1:ℝ)..x, Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1))
      = DirichletCharacter.LFunction χ 1 / (1 - β)
        - ∫ t in Set.Ioi x, Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1)) := by
  have h1 : (∫ t in Set.Ioi (1:ℝ), Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1)))
      = DirichletCharacter.LFunction χ 1 / (1 - β) := by
    rw [← hfac]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [neg_ofReal_one_add_cast])
  exact ((integral_Ioi_sub_Ioi hint hx).symm).trans (by rw [h1])

/-- **The Abel split of the smoothed sum.**  Since `A(u) = E(u) + u·L(1,χ)`,

  `∫_1^x W(u)·A(u) du = ((1-β)/x)·∫_1^x u^{-β}E(u) du + β·∫_1^x u^{-(β+1)}E(u) du
      + L(1,χ)·∫_1^x W(u)·u du`,

with `W(u) = (1-β)u^{-β}/x + β u^{-(β+1)}` the Abel weight of `smoothedAbel`.  All the integrals
are over the compact interval `[1,x]`, so only linearity of the integral together with the local
boundedness of `E` is used. -/
lemma smoothedAbelSplitAux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ t : ℝ, 1 ≤ t → ‖Work.LinnikAreas.Efun χ t‖ ≤ K * Real.sqrt t)
    {β : ℝ} {x : ℕ} (hx : 1 ≤ x) :
    (∫ u in (1:ℝ)..(x:ℝ),
        (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)))
          * Work.LinnikAreas.Asum χ u)
      = (((1 - β : ℝ) : ℂ) / (x:ℂ)) * (∫ u in (1:ℝ)..(x:ℝ),
            (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)
        + (β:ℂ) * (∫ u in (1:ℝ)..(x:ℝ), (u:ℂ) ^ (-((β:ℂ) + 1)) * Work.LinnikAreas.Efun χ u)
        + DirichletCharacter.LFunction χ 1 * (∫ u in (1:ℝ)..(x:ℝ),
            (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) * (u:ℂ)) := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hpt : ∀ u : ℝ,
      (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)))
          * Work.LinnikAreas.Asum χ u
        = (((1 - β : ℝ) : ℂ) / (x:ℂ)) * ((u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)
          + (β:ℂ) * ((u:ℂ) ^ (-((β:ℂ) + 1)) * Work.LinnikAreas.Efun χ u)
          + DirichletCharacter.LFunction χ 1 *
              ((((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) * (u:ℂ)) := by
    intro u
    have hA : Work.LinnikAreas.Asum χ u
        = Work.LinnikAreas.Efun χ u + (u:ℂ) * DirichletCharacter.LFunction χ 1 := by
      rw [Work.LinnikAreas.Efun_apply]; ring
    rw [hA]; push_cast; ring
  rw [intervalIntegral.integral_congr (fun u _ => hpt u)]
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.uIoc (1:ℝ) (x:ℝ))),
      ‖Work.LinnikAreas.Efun χ t‖ ≤ K * Real.sqrt (x:ℝ) := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    rw [Set.uIoc_of_le hx1, Set.mem_Ioc] at ht
    exact le_trans (hE t (le_of_lt ht.1)) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2) hK)
  have hmeas : AEStronglyMeasurable (Work.LinnikAreas.Efun χ)
      (volume.restrict (Set.uIoc (1:ℝ) (x:ℝ))) :=
    (measurable_Efun_cpow χ).aestronglyMeasurable
  have hmem : ∀ u ∈ Set.uIcc (1:ℝ) (x:ℝ), (u:ℂ) ∈ Complex.slitPlane := by
    intro u hu
    rw [Set.uIcc_of_le hx1] at hu
    rw [Complex.ofReal_mem_slitPlane]
    linarith [hu.1]
  have hc1 : ContinuousOn (fun u : ℝ => (u:ℂ) ^ (-(β:ℂ))) (Set.uIcc (1:ℝ) (x:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.cpow continuousOn_const hmem
  have hc2 : ContinuousOn (fun u : ℝ => (u:ℂ) ^ (-((β:ℂ) + 1))) (Set.uIcc (1:ℝ) (x:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.cpow continuousOn_const hmem
  have hI1 : IntervalIntegrable
      (fun u : ℝ => (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u) volume (1:ℝ) (x:ℝ) :=
    intervalIntegrable_iff.mpr ((hc1.intervalIntegrable).def'.mul_bdd hmeas hbdd)
  have hI2 : IntervalIntegrable
      (fun u : ℝ => (u:ℂ) ^ (-((β:ℂ) + 1)) * Work.LinnikAreas.Efun χ u) volume (1:ℝ) (x:ℝ) :=
    intervalIntegrable_iff.mpr ((hc2.intervalIntegrable).def'.mul_bdd hmeas hbdd)
  have hI3 : IntervalIntegrable
      (fun u : ℝ => (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ)
        + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) * (u:ℂ)) volume (1:ℝ) (x:ℝ) :=
    ((((hc1.const_mul ((1 - β) : ℂ)).div_const ((x:ℂ))).add
        (hc2.const_mul ((β:ℂ)))).mul Complex.continuous_ofReal.continuousOn).intervalIntegrable
  rw [intervalIntegral.integral_add ((hI1.const_mul _).add (hI2.const_mul _)) (hI3.const_mul _),
      intervalIntegral.integral_add (hI1.const_mul _) (hI2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]

theorem smoothedMainError {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχre : ∀ n : ℕ, (Work.LinnikAreas.lam χ n).im = 0)
    {K : ℝ} (hK : 0 ≤ K) (hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖ ≤ K * Real.sqrt x)
    {β : ℝ} (hβ : 1/2 < β) (hβ1 : β < 1)
    (hfac : (∫ x in Set.Ioi (1:ℝ), Work.LinnikAreas.Efun χ x * (x:ℂ) ^ (-(((1 + β : ℝ)) : ℂ)))
        = DirichletCharacter.LFunction χ 1 / (1 - β))
    {x : ℕ} (hx : 1 ≤ x) :
    ‖(Work.LinnikAreas.Ssm χ β (x:ℝ) : ℂ) - Work.LinnikAreas.mainTerm χ β (x:ℝ)‖
      ≤ K * (x:ℝ) ^ (1/2-β) * (β/(β-1/2) + (1-β)/(3/2-β))
        + ‖DirichletCharacter.LFunction χ 1‖ * (1-β)/((x:ℝ)*(2-β)) := by
  have hx1R : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx0R : (0:ℝ) < (x:ℝ) := by linarith
  have h1mβpos : (0:ℝ) < 1 - β := by linarith
  have h2mβpos : (0:ℝ) < 2 - β := by linarith
  have hbpos : (0:ℝ) < β := by linarith
  have h3mβpos : (0:ℝ) < 3/2 - β := by linarith
  have h1mβc : ((1-β:ℝ):ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  have h2mβc : ((2-β:ℝ):ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  have hxc : ((x:ℝ):ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  -- integrability of the Abel integrand on `(1,∞)`
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1))) (Set.Ioi 1) :=
    integrableOnEfunCpowIoi χ hK hE hβ
  -- the truncation of the Abel integral
  have htail := intervalIntegral_Efun_cpow_split χ hint hfac hx1R
  -- the algebraic split of the smoothed Abel identity
  have hsplit := smoothedAbelSplitAux χ hK hE (β := β) hx
  -- the smoothed Abel identity
  have habel := smoothedAbel χ hχre β hx
  -- the value of the weight integral `∫ W(u) u du`
  have hI3val : (∫ u in (1:ℝ)..((x:ℝ)),
        (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) * (u:ℂ))
      = ((x:ℂ) ^ ((1-β:ℝ):ℂ)) / (((1-β:ℝ):ℂ) * ((2-β:ℝ):ℂ))
        - (β:ℂ)/((1-β:ℝ):ℂ)
        - ((1-β:ℝ):ℂ)/((x:ℂ) * ((2-β:ℝ):ℂ)) := by
    have h := integral_abel_weights_complex β hβ1 (x := (x:ℝ)) hx0R
    simpa using h
  -- the truncated `u^{-(β+1)}` integral
  have hI2val : (∫ u in (1:ℝ)..((x:ℝ)),
        (u:ℂ) ^ (-((β:ℂ) + 1)) * Work.LinnikAreas.Efun χ u)
      = DirichletCharacter.LFunction χ 1 / (1 - β)
        - ∫ t in Set.Ioi ((x:ℝ)), Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1)) := by
    rw [intervalIntegral.integral_congr (fun u _ => mul_comm _ _)]
    exact htail
  -- the main term as `L(1,χ)` times the bare weight integral
  have hMT : Work.LinnikAreas.mainTerm χ β ((x:ℝ))
      = DirichletCharacter.LFunction χ 1 *
          (((x:ℂ) ^ ((1-β:ℝ):ℂ)) / (((1-β:ℝ):ℂ) * ((2-β:ℝ):ℂ))) := by
    rw [Work.LinnikAreas.mainTerm_apply]
    push_cast
    ring
  -- the key identity
  have hkey : (Work.LinnikAreas.Ssm χ β ((x:ℝ)) : ℂ) - Work.LinnikAreas.mainTerm χ β ((x:ℝ))
      = (((1-β:ℝ):ℂ)/((x:ℝ):ℂ)) *
          (∫ u in (1:ℝ)..((x:ℝ)), (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)
        - (β:ℂ) * (∫ t in Set.Ioi ((x:ℝ)),
            Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1)))
        - DirichletCharacter.LFunction χ 1 * (((1-β:ℝ):ℂ)/(((x:ℝ):ℂ)*((2-β:ℝ):ℂ))) := by
    rw [habel, hsplit, hI3val, hI2val, hMT]
    push_cast
    ring_nf
  -- the three norm bounds
  have hnormI1 : ‖∫ u in (1:ℝ)..((x:ℝ)),
        (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u‖
      ≤ K * ((x:ℝ) ^ (3/2-β) - 1) / (3/2-β) := by
    rw [intervalIntegral.integral_congr (fun u _ => mul_comm _ _)]
    rw [intervalIntegral.integral_of_le hx1R]
    exact normSetIntegralIocEfunLe χ hK hE hβ hβ1 hx1R
  have hnormJ : ‖∫ t in Set.Ioi ((x:ℝ)),
        Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1))‖
      ≤ K * (x:ℝ) ^ (1/2-β) / (β-1/2) :=
    normSetIntegralIoiEfunLe χ hK hE hβ hx1R
  have hnorm1mβ : ‖((1-β:ℝ):ℂ)‖ = 1 - β := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt h1mβpos)]
  have hnormx : ‖((x:ℝ):ℂ)‖ = (x:ℝ) := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hx0R)]
  have hnorm2mβ : ‖((2-β:ℝ):ℂ)‖ = 2 - β := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt h2mβpos)]
  have hnormβ : ‖(β:ℂ)‖ = β := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hbpos)]
  have hdiff : ‖((((1-β:ℝ):ℂ)/((x:ℝ):ℂ)) *
        (∫ u in (1:ℝ)..((x:ℝ)), (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)
      - (β:ℂ) * (∫ t in Set.Ioi ((x:ℝ)), Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1)))
      - DirichletCharacter.LFunction χ 1 * (((1-β:ℝ):ℂ)/(((x:ℝ):ℂ)*((2-β:ℝ):ℂ))))‖
      ≤ K * (1-β) * (x:ℝ) ^ (1/2-β) / (3/2-β)
        + K * (x:ℝ) ^ (1/2-β) * (β/(β-1/2))
        + ‖DirichletCharacter.LFunction χ 1‖ * ((1-β)/((x:ℝ)*(2-β))) := by
    have hb1 : ‖(((1-β:ℝ):ℂ)/((x:ℝ):ℂ)) *
        (∫ u in (1:ℝ)..((x:ℝ)), (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)‖
        ≤ K * (1-β) * (x:ℝ) ^ (1/2-β) / (3/2-β) := by
      rw [norm_mul, norm_div, hnorm1mβ, hnormx]
      have hmain : (((x:ℝ) ^ (3/2-β) - 1)) / (x:ℝ) ≤ (x:ℝ) ^ (1/2-β) := by
        have hxpow : (x:ℝ) * (x:ℝ) ^ (1/2-β) = (x:ℝ) ^ (3/2-β) := by
          rw [show (3/2-β : ℝ) = (1/2-β) + 1 by ring, Real.rpow_add hx0R, Real.rpow_one,
            mul_comm]
        rw [div_le_iff₀ hx0R, ← hxpow]
        linarith [Real.rpow_nonneg hx0R.le (1/2-β),
          mul_comm ((x:ℝ) ^ (1/2-β)) (x:ℝ)]
      have hK1 : 0 ≤ K * (1-β) / (3/2-β) :=
        div_nonneg (mul_nonneg hK h1mβpos.le) h3mβpos.le
      have hle1 : 0 ≤ (1-β)/(x:ℝ) := div_nonneg h1mβpos.le hx0R.le
      calc (1-β)/(x:ℝ) * ‖∫ u in (1:ℝ)..((x:ℝ)),
              (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u‖
          ≤ (1-β)/(x:ℝ) * (K * ((x:ℝ) ^ (3/2-β) - 1) / (3/2-β)) :=
            mul_le_mul_of_nonneg_left hnormI1 hle1
        _ = (K * (1-β) / (3/2-β)) * (((x:ℝ) ^ (3/2-β) - 1)/(x:ℝ)) := by ring
        _ ≤ (K * (1-β) / (3/2-β)) * ((x:ℝ) ^ (1/2-β)) :=
              mul_le_mul_of_nonneg_left hmain hK1
        _ = K * (1-β) * (x:ℝ) ^ (1/2-β) / (3/2-β) := by ring
    have hb2 : ‖(β:ℂ) * (∫ t in Set.Ioi ((x:ℝ)),
        Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1)))‖
        ≤ K * (x:ℝ) ^ (1/2-β) * (β/(β-1/2)) := by
      rw [norm_mul, hnormβ]
      calc β * ‖∫ t in Set.Ioi ((x:ℝ)),
            Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1))‖
          ≤ β * (K * (x:ℝ) ^ (1/2-β) / (β-1/2)) :=
            mul_le_mul_of_nonneg_left hnormJ hbpos.le
        _ = K * (x:ℝ) ^ (1/2-β) * (β/(β-1/2)) := by ring
    have hb3 : ‖DirichletCharacter.LFunction χ 1 * (((1-β:ℝ):ℂ)/(((x:ℝ):ℂ)*((2-β:ℝ):ℂ)))‖
        = ‖DirichletCharacter.LFunction χ 1‖ * ((1-β)/((x:ℝ)*(2-β))) := by
      rw [norm_mul, norm_div, norm_mul, hnorm1mβ, hnormx, hnorm2mβ]
    have htri : ‖(((1-β:ℝ):ℂ)/((x:ℝ):ℂ)) *
            (∫ u in (1:ℝ)..((x:ℝ)), (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)
          - (β:ℂ) * (∫ t in Set.Ioi ((x:ℝ)),
              Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1)))
          - DirichletCharacter.LFunction χ 1 *
              (((1-β:ℝ):ℂ)/(((x:ℝ):ℂ)*((2-β:ℝ):ℂ)))‖
        ≤ (‖(((1-β:ℝ):ℂ)/((x:ℝ):ℂ)) *
            (∫ u in (1:ℝ)..((x:ℝ)), (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)‖
          + ‖(β:ℂ) * (∫ t in Set.Ioi ((x:ℝ)),
              Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1)))‖)
          + ‖DirichletCharacter.LFunction χ 1 *
              (((1-β:ℝ):ℂ)/(((x:ℝ):ℂ)*((2-β:ℝ):ℂ)))‖ :=
      le_trans (norm_sub_le _ _) (add_le_add (norm_sub_le _ _) le_rfl)
    refine le_trans htri ?_
    rw [hb3]; linarith [hb1, hb2]
  rw [hkey]
  calc ‖((((1-β:ℝ):ℂ)/((x:ℝ):ℂ)) *
        (∫ u in (1:ℝ)..((x:ℝ)), (u:ℂ) ^ (-(β:ℂ)) * Work.LinnikAreas.Efun χ u)
      - (β:ℂ) * (∫ t in Set.Ioi ((x:ℝ)), Work.LinnikAreas.Efun χ t * (t:ℂ) ^ (-((β:ℂ) + 1)))
      - DirichletCharacter.LFunction χ 1 * (((1-β:ℝ):ℂ)/(((x:ℝ):ℂ)*((2-β:ℝ):ℂ))))‖
      ≤ K * (1-β) * (x:ℝ) ^ (1/2-β) / (3/2-β)
        + K * (x:ℝ) ^ (1/2-β) * (β/(β-1/2))
        + ‖DirichletCharacter.LFunction χ 1‖ * ((1-β)/((x:ℝ)*(2-β))) := hdiff
    _ = K * (x:ℝ) ^ (1/2-β) * (β/(β-1/2) + (1-β)/(3/2-β))
        + ‖DirichletCharacter.LFunction χ 1‖ * (1-β)/((x:ℝ)*(2-β)) := by ring

end Work.LinnikAreas
