import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec

open Complex
open scoped Interval
open Set

namespace Commons.NumberTheory.Linnik

private lemma tentWeight_eq_left {L K x : ℝ} (hlo : L - 2 * K ≤ x) (hhi : x ≤ L - K) :
    tentWeight L K x = x - (L - 2 * K) := by
  rw [tentWeight_spec]
  by_cases hx : x ≤ L - 2 * K
  · have hx' : x = L - 2 * K := le_antisymm hx hlo
    simp [hx']
  · simp [hx, hhi]

private lemma tentWeight_eq_right {L K x : ℝ} (hK : 0 < K) (hlo : L - K ≤ x) (hhi : x ≤ L) :
    tentWeight L K x = L - x := by
  rw [tentWeight_spec]
  by_cases hx : x ≤ L - 2 * K
  · have : L - K ≤ L - 2 * K := hlo.trans hx
    linarith
  · by_cases hx2 : x ≤ L - K
    · have hx' : x = L - K := le_antisymm hx2 hlo
      rw [hx']
      have h1 : ¬ L - K ≤ L - 2 * K := by linarith
      simp [h1]; ring
    · simp [hx, hx2, hhi]

private lemma deriv_cexp_mul (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x := by
  have hinner : HasDerivAt (fun u : ℂ => c * u) c (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul c
  have hCe : HasDerivAt (fun u : ℂ => Complex.exp (c * u))
      (Complex.exp (c * (x : ℂ)) * c) (x : ℂ) := by
    exact HasDerivAt.comp (x : ℂ) (Complex.hasDerivAt_exp (c * (x : ℂ))) hinner
  exact (hCe.comp_ofReal).congr_deriv (by ring)

private lemma deriv_sub_A (A : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) - A)) (1 : ℂ) x := by
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
    simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
  simpa using hid.sub_const A

private lemma deriv_prim1 (c A : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) *
        (((y : ℂ) - A) / c - (1 : ℂ) / (c * c)))
      (Complex.exp (c * (x : ℂ)) * ((x : ℂ) - A)) x := by
  have hE := deriv_cexp_mul c x
  have hu : HasDerivAt (fun y : ℝ => ((y : ℂ) - A) / c - (1 : ℂ) / (c * c)) ((1 : ℂ) / c) x := by
    have hsub := deriv_sub_A A x
    simpa using (hsub.div_const c).sub_const ((1 : ℂ) / (c * c))
  refine (hE.mul hu).congr_deriv ?_
  field_simp [hc]
  ring

private lemma deriv_prim2 (c B : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) *
        (((B : ℂ) - (y : ℂ)) / c + (1 : ℂ) / (c * c)))
      (Complex.exp (c * (x : ℂ)) * ((B : ℂ) - (x : ℂ))) x := by
  have hE := deriv_cexp_mul c x
  have hB : HasDerivAt (fun y : ℝ => (B : ℂ) - (y : ℂ)) (-1 : ℂ) x := by
    have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    simpa using hid.const_sub B
  have hu : HasDerivAt (fun y : ℝ => ((B : ℂ) - (y : ℂ)) / c + (1 : ℂ) / (c * c)) ((-1 : ℂ) / c) x := by
    simpa using (hB.div_const c).add_const ((1 : ℂ) / (c * c))
  refine (hE.mul hu).congr_deriv ?_
  field_simp [hc]
  ring

private lemma integral_exp_mul_sub (c A : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Complex.exp (c * (x : ℂ)) * ((x : ℂ) - A)) =
      Complex.exp (c * (b : ℂ)) * (((b : ℂ) - A) / c - (1 : ℂ) / (c * c)) -
        Complex.exp (c * (a : ℂ)) * (((a : ℂ) - A) / c - (1 : ℂ) / (c * c)) := by
  let F : ℝ → ℂ := fun y => Complex.exp (c * (y : ℂ)) *
        (((y : ℂ) - A) / c - (1 : ℂ) / (c * c))
  let f' : ℝ → ℂ := fun x => Complex.exp (c * (x : ℂ)) * ((x : ℂ) - A)
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f' x) x := by
    intro x hx
    exact deriv_prim1 c A hc x
  have hint : IntervalIntegrable f' MeasureTheory.volume a b := by
    have hc1 : Continuous f' := by fun_prop
    exact hc1.intervalIntegrable a b
  rw [show (∫ x in a..b, Complex.exp (c * (x : ℂ)) * ((x : ℂ) - A)) = ∫ x in a..b, f' x by rfl]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private lemma integral_exp_mul_rev (c B : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Complex.exp (c * (x : ℂ)) * ((B : ℂ) - (x : ℂ))) =
      Complex.exp (c * (b : ℂ)) * (((B : ℂ) - (b : ℂ)) / c + (1 : ℂ) / (c * c)) -
        Complex.exp (c * (a : ℂ)) * (((B : ℂ) - (a : ℂ)) / c + (1 : ℂ) / (c * c)) := by
  let F : ℝ → ℂ := fun y => Complex.exp (c * (y : ℂ)) *
        (((B : ℂ) - (y : ℂ)) / c + (1 : ℂ) / (c * c))
  let f' : ℝ → ℂ := fun x => Complex.exp (c * (x : ℂ)) * ((B : ℂ) - (x : ℂ))
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f' x) x := by
    intro x hx
    exact deriv_prim2 c B hc x
  have hint : IntervalIntegrable f' MeasureTheory.volume a b := by
    have hc1 : Continuous f' := by fun_prop
    exact hc1.intervalIntegrable a b
  rw [show (∫ x in a..b, Complex.exp (c * (x : ℂ)) * ((B : ℂ) - (x : ℂ))) = ∫ x in a..b, f' x by rfl]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem tentWeight_laplace {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) (z : ℂ) (hz : z ≠ 0) :
    (∫ t in (L - 2 * K : ℝ)..(L : ℝ),
        Complex.exp (-(z * (t : ℂ))) * (tentWeight L K t : ℂ)) =
      Complex.exp (-(z * ((L - 2 * K : ℝ) : ℂ))) *
        (((1 - Complex.exp (-(z * ((K : ℝ) : ℂ)))) / z) ^ 2) := by
  let c : ℂ := -z
  have _h2 : 2 * K < L := h2K
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr hz
  have hcexp (t : ℝ) : Complex.exp (-(z * (t : ℂ))) = Complex.exp (c * (t : ℂ)) := by
    congr 1
    dsimp [c]
    ring
  have hLHS : (∫ t in (L - 2 * K : ℝ)..(L : ℝ),
        Complex.exp (-(z * (t : ℂ))) * (tentWeight L K t : ℂ)) =
      (∫ t in (L - 2 * K : ℝ)..(L : ℝ),
        Complex.exp (c * (t : ℂ)) * (tentWeight L K t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp [hcexp]
  have hAM : (L - 2 * K : ℝ) ≤ L - K := by linarith
  have hML : (L - K : ℝ) ≤ L := by linarith
  have htent_left (t : ℝ) (ht : t ∈ Set.Icc (L - 2 * K) (L - K)) :
      (tentWeight L K t : ℂ) = (t : ℂ) - ((L - 2 * K : ℝ) : ℂ) := by
    have ht' := tentWeight_eq_left ht.1 ht.2
    rw [ht']
    norm_num
  have htent_right (t : ℝ) (ht : t ∈ Set.Icc (L - K) L) :
      (tentWeight L K t : ℂ) = (L : ℂ) - (t : ℂ) := by
    have ht' := tentWeight_eq_right hK ht.1 ht.2
    rw [ht']
    norm_num
  let f0 : ℝ → ℂ := fun t => Complex.exp (c * (t : ℂ)) * (tentWeight L K t : ℂ)
  have hint_f_am : IntervalIntegrable f0 MeasureTheory.volume (L - 2 * K) (L - K) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hAM
    have hc_g1 : ContinuousOn (fun x : ℝ => Complex.exp (c * (x : ℂ)) *
        ((x : ℂ) - ((L - 2 * K : ℝ) : ℂ))) (Set.Icc (L - 2 * K) (L - K)) := by
      fun_prop
    exact hc_g1.congr (by
      intro x hx
      dsimp [f0]
      rw [htent_left x hx])
  have hint_f_ml : IntervalIntegrable f0 MeasureTheory.volume (L - K) L := by
    apply ContinuousOn.intervalIntegrable_of_Icc hML
    have hc_g2 : ContinuousOn (fun x : ℝ => Complex.exp (c * (x : ℂ)) *
        ((L : ℂ) - (x : ℂ))) (Set.Icc (L - K) L) := by
      fun_prop
    exact hc_g2.congr (by
      intro x hx
      dsimp [f0]
      rw [htent_right x hx])
  have hsplit : (∫ t in (L - 2 * K : ℝ)..(L : ℝ), f0 t) =
      (∫ t in (L - 2 * K : ℝ)..(L - K : ℝ), f0 t) +
        ∫ t in (L - K : ℝ)..(L : ℝ), f0 t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_f_am hint_f_ml]
  have hleft : (∫ t in (L - 2 * K : ℝ)..(L - K : ℝ), f0 t) =
      (∫ t in (L - 2 * K : ℝ)..(L - K : ℝ),
        Complex.exp (c * (t : ℂ)) * ((t : ℂ) - ((L - 2 * K : ℝ) : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (L - 2 * K) (L - K) := by
      simpa [Set.uIcc_of_le hAM] using ht
    dsimp [f0]
    rw [htent_left t ht']
  have hright : (∫ t in (L - K : ℝ)..(L : ℝ), f0 t) =
      (∫ t in (L - K : ℝ)..(L : ℝ),
        Complex.exp (c * (t : ℂ)) * ((L : ℂ) - (t : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (L - K) L := by
      simpa [Set.uIcc_of_le hML] using ht
    dsimp [f0]
    rw [htent_right t ht']
  rw [hLHS]
  rw [show (∫ t in (L - 2 * K : ℝ)..(L : ℝ),
        Complex.exp (c * (t : ℂ)) * (tentWeight L K t : ℂ)) = ∫ t in (L - 2 * K : ℝ)..(L : ℝ), f0 t by rfl]
  rw [hsplit, hleft, hright]
  -- now the two FTC lemmas
  rw [integral_exp_mul_sub (c := c) (A := ((L - 2 * K : ℝ) : ℂ)) hc (a := L - 2 * K) (b := L - K)]
  rw [integral_exp_mul_rev (c := c) (B := (L : ℂ)) hc (a := L - K) (b := L)]
  -- goal now closed forms; simplify algebra
  have hA1 : ((L - K : ℝ) : ℂ) - ((L - 2 * K : ℝ) : ℂ) = (K : ℂ) := by
    norm_num; ring
  have hA2 : ((L - 2 * K : ℝ) : ℂ) - ((L - 2 * K : ℝ) : ℂ) = (0 : ℂ) := by norm_num
  have hA3 : ((L : ℝ) : ℂ) - ((L : ℝ) : ℂ) = (0 : ℂ) := by norm_num
  have hA4 : ((L : ℝ) : ℂ) - ((L - K : ℝ) : ℂ) = (K : ℂ) := by norm_num
  set EA : ℂ := Complex.exp (c * ((L - 2 * K : ℝ) : ℂ))
  set EM : ℂ := Complex.exp (c * ((L - K : ℝ) : ℂ))
  set EB : ℂ := Complex.exp (c * ((L : ℝ) : ℂ))
  set EK : ℂ := Complex.exp (c * ((K : ℝ) : ℂ))
  rw [hA1, hA2, hA3, hA4]
  simp
  have hEMe : EM = EA * EK := by
    dsimp [EM, EA, EK]
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  have hEBe : EB = EA * EK ^ 2 := by
    dsimp [EB, EA, EK]
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    norm_num
    ring
  rw [hEMe, hEBe]
  dsimp [EA, EM, EB, EK, c]
  have hzA : Complex.exp ((-z) * ((L - 2 * K : ℝ) : ℂ)) =
      Complex.exp (-(z * ((L : ℂ) - 2 * (K : ℂ)))) := by
    congr 1
    norm_num
  have hzK : Complex.exp ((-z) * ((K : ℝ) : ℂ)) = Complex.exp (-(z * (K : ℂ))) := by
    congr 1
    norm_num
  rw [hzA, hzK]
  field_simp [hz]
  ring