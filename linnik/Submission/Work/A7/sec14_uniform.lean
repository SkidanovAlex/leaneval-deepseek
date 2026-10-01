import Mathlib
import Submission.Work.LinnikAreas.A7.Sec14
import Submission.Work.A7.sec14_num_rows
import Submission.Work.A7.box_api7
import Submission.Work.LinnikAreas.A7.Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 1000000

namespace Work.A7

open Work.LinnikContract Work.LinnikAreas.A7

/-! ## Elementary numeric facts for the Deuring--Heilbronn repulsion regime

These are the small rational enclosures needed to close the logarithmic-repulsion numeric
inequality `≤ 1 - λ/9` for `0 < λ ≤ 2/100` with `c = (99/100)·log(1/λ)` (the §14 branch of
Heath-Brown's proof).  Everything reduces to monotonicity of `exp`/`log` and a handful of
explicit rational estimates. -/

/-- `exp(-15) ≤ 1/3·10⁻⁶`, from the Taylor partial sum `Σ_{i<22} 15^i/i! ≥ 3·10⁶`. -/
private lemma exp_neg_15_le : Real.exp (-(15:ℝ)) ≤ 1/3000000 := by
  have h : (3000000:ℝ) ≤ Real.exp 15 := by
    have hs := Real.sum_le_exp_of_nonneg (x := (15:ℝ)) (by norm_num) 22
    have hnum : (3000000:ℝ) ≤ ∑ i ∈ Finset.range 22, (15:ℝ)^i / (i.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ]
    exact le_trans hnum hs
  rw [Real.exp_neg]
  simpa [one_div] using one_div_le_one_div_of_le (show (0:ℝ) < 3000000 by norm_num) h

/-- `exp(-28/5) ≤ 1/270`, from `Σ_{i<16} (28/5)^i/i! ≥ 270`. -/
private lemma exp_neg_28_5_le : Real.exp (-((28:ℝ)/5)) ≤ 1/270 := by
  have h : (270:ℝ) ≤ Real.exp ((28:ℝ)/5) := by
    have hs := Real.sum_le_exp_of_nonneg (x := ((28:ℝ)/5)) (by norm_num) 16
    have hnum : (270:ℝ) ≤ ∑ i ∈ Finset.range 16, ((28:ℝ)/5)^i / (i.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ]
    exact le_trans hnum hs
  rw [Real.exp_neg]
  simpa [one_div] using one_div_le_one_div_of_le (show (0:ℝ) < 270 by norm_num) h

/-- `B(3/10, 0) = 1/(3·(3/10)) + 1 = 19/9`. -/
private lemma Bfun_310_zero : Bfun ((3:ℝ)/10) 0 = 19/9 := by
  rw [Bfun, if_pos rfl]; norm_num

/-- The crude uniform bound `B(3/10, x) ≤ 19/9` for `x > 0`. -/
private lemma Bfun_310_le {x : ℝ} (hx : 0 < x) : Bfun ((3:ℝ)/10) x ≤ 19/9 := by
  rw [← Bfun_310_zero]
  exact Work.A7.Bfun_le_at_zero_of_pos (K := (3:ℝ)/10) (by norm_num) hx

/-- `exp(3.9) ≤ 50`, so that `log 50 ≥ 3.9`. -/
private lemma exp_3_9_le_50 : Real.exp ((39:ℝ)/10) ≤ 50 := by
  have hb := Work.LinnikAreas.A7.exp_rem_bound ((39:ℝ)/10) 7 (by norm_num)
  rw [abs_le] at hb
  have h2 : (∑ m ∈ Finset.range 7, ((39:ℝ)/10)^m / (m.factorial : ℝ))
      + ((39:ℝ)/10)^7 / ((7:ℕ).factorial:ℝ) * 2 ≤ 50 := by
    norm_num [Finset.sum_range_succ]
  linarith [hb.2]

/-- `x/(1+x) ≤ 1 - e^{-x}` for `x ≥ 0`. -/
private lemma one_sub_exp_neg_ge (x : ℝ) (hx : 0 ≤ x) : x/(1+x) ≤ 1 - Real.exp (-x) := by
  have h : Real.exp (-x) ≤ 1/(1+x) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (by linarith : (0:ℝ) < 1 + x)
      (by linarith [Real.add_one_le_exp x] : (1:ℝ) + x ≤ Real.exp x)
  have h3 : x/(1+x) = 1 - 1/(1+x) := by field_simp; ring
  rw [h3]; linarith [h]

/-- **The §14 Deuring--Heilbronn repulsion numeric inequality.**  For `0 < λ ≤ 2/100`, with
`c = (99/100)·log(1/λ)`, the model sum of the `§14` core is `≤ 1 - λ/9`. -/
private lemma sec14_repel_aux {lam η εw : ℝ} (hlam : 0 < lam) (hlam2 : lam ≤ 2/100)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/100000000) (hη2 : η ≤ lam/10)
    (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2
      + Real.exp (-(ac * (99/100 * Real.log (1/lam)))) * (Bfun ((3:ℝ)/10) lam + η)
      + (Phi (99/100 * Real.log (1/lam)) / Wf (99/100 * Real.log (1/lam))) * ((67:ℝ)/6 + εw)
      + η * ((Real.exp (-(ac * (99/100 * Real.log (1/lam)))) / Wf (99/100 * Real.log (1/lam))) * ((67:ℝ)/6 + εw) + 1)
      ≤ 1 - lam/9 := by
  have hacpos : (0:ℝ) < ac := by norm_num [Work.LinnikAreas.A7.ac]
  have hKcpos : (0:ℝ) < Kc := by norm_num [Work.LinnikAreas.A7.Kc]
  have hK2pos : (0:ℝ) < K2 := by norm_num [Work.LinnikAreas.A7.K2]
  set L : ℝ := Real.log (1/lam) with hL
  set c : ℝ := (99/100) * L with hc
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos
    rw [one_div, one_lt_inv₀ hlam]; linarith [hlam2]
  have h50 : (50:ℝ) ≤ 1/lam := by
    rw [le_div_iff₀ hlam]; linarith [hlam2]
  have hlog50 : (39:ℝ)/10 ≤ Real.log 50 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 50)]
    exact exp_3_9_le_50
  have hLge : (39:ℝ)/10 ≤ L := by
    rw [hL]; exact le_trans hlog50 (Real.log_le_log (by norm_num) h50)
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcge : (19:ℝ)/5 ≤ c := by rw [hc]; nlinarith [hLge]
  have hExpL : Real.exp (-L) = lam := by
    rw [hL, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  have hac_eq : ac * c = (4851:ℝ)/1000 * L := by rw [hc, Work.LinnikAreas.A7.ac]; ring
  have hExp3851 : Real.exp (-((3851:ℝ)/1000*L)) ≤ 1/3000000 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_15_le
    nlinarith [hLge]
  have hExp1442 : Real.exp (-((1442:ℝ)/1000*L)) ≤ 1/270 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_28_5_le
    nlinarith [hLge]
  have hEc : Real.exp (-(ac*c)) ≤ lam/3000000 := by
    have hsplit : -(ac*c) = -L + -((3851:ℝ)/1000*L) := by rw [hac_eq]; ring
    calc Real.exp (-(ac*c)) = Real.exp (-L) * Real.exp (-((3851:ℝ)/1000*L)) := by
          rw [hsplit, Real.exp_add]
      _ ≤ lam * (1/3000000) :=
          mul_le_mul (le_of_eq hExpL) hExp3851 (by positivity) (by positivity)
      _ = lam/3000000 := by ring
  have hT1 : Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2 ≤ Real.exp (-(ac*lam)) := by
    have hnum0 : 0 ≤ (1 - Real.exp (-(Kc*lam)))/lam := by
      refine div_nonneg ?_ hlam.le
      rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith [hKcpos, hlam]
    have hle : (1 - Real.exp (-(Kc*lam)))/lam ≤ Kc := by
      rw [div_le_iff₀ hlam]
      have := Real.one_sub_le_exp_neg (Kc*lam); linarith
    have hsq : ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2 ≤ 1 := by
      rw [div_le_one hK2pos]
      calc ((1 - Real.exp (-(Kc*lam)))/lam)^2 ≤ Kc^2 := pow_le_pow_left₀ hnum0 hle 2
        _ = K2 := by rw [Work.LinnikAreas.A7.Kc, Work.LinnikAreas.A7.K2]; norm_num
    calc Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2
        = Real.exp (-(ac*lam)) * (((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2) := by ring
      _ ≤ Real.exp (-(ac*lam)) * 1 := mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = Real.exp (-(ac*lam)) := by ring
  have hT1' : Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2 ≤ 1 - (2450:ℝ)/549*lam := by
    have hone : (2450:ℝ)/549*lam ≤ 1 - Real.exp (-(ac*lam)) := by
      have hx : ac*lam ≤ (49:ℝ)/500 := by rw [Work.LinnikAreas.A7.ac]; nlinarith [hlam2]
      have hx0 : 0 ≤ ac*lam := by positivity
      have hstep := one_sub_exp_neg_ge (ac*lam) hx0
      have hden : (2450:ℝ)/549*lam ≤ ac*lam/(1+ac*lam) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 1 + ac*lam)]
        have hac : ac = (49:ℝ)/10 := by rw [Work.LinnikAreas.A7.ac]
        have h1 : (1:ℝ) + ac*lam ≤ 549/500 := by linarith [hx]
        calc (2450:ℝ)/549*lam*(1+ac*lam) ≤ (2450:ℝ)/549*lam*(549/500) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ac*lam := by rw [hac]; ring
      linarith [hstep, hden]
    linarith [hT1, hone]
  have hT2 : Real.exp (-(ac*c)) * (Bfun ((3:ℝ)/10) lam + η) ≤ lam/1000000 := by
    have hB : Bfun ((3:ℝ)/10) lam ≤ 19/9 := Bfun_310_le hlam
    have hηle : η ≤ (1:ℝ)/500 := by linarith [hη2, hlam2]
    have hBη : Bfun ((3:ℝ)/10) lam + η ≤ 19/9 + 1/500 := by linarith
    have hBηpos : 0 ≤ Bfun ((3:ℝ)/10) lam + η := by
      have := (Work.LinnikContract.API.Bfun_pos (K := (3:ℝ)/10) (by norm_num) hlam).le; linarith
    calc Real.exp (-(ac*c)) * (Bfun ((3:ℝ)/10) lam + η)
        ≤ (lam/3000000) * (19/9 + 1/500) := mul_le_mul hEc hBη hBηpos (by positivity)
      _ ≤ lam/1000000 := by
          have he : (lam/3000000) * (19/9 + 1/500) = lam * ((9509:ℝ)/13500000000) := by ring
          rw [he]
          have hmono : lam * ((9509:ℝ)/13500000000) ≤ (2/100) * ((9509:ℝ)/13500000000) :=
            mul_le_mul_of_nonneg_right hlam2 (by norm_num)
          have hnum : (2/100) * ((9509:ℝ)/13500000000) ≤ (1:ℝ)/1000000 := by norm_num
          linarith
  have hWf_eq : Wf c = c / (Real.exp ((73:ℝ)/30*c) - Real.exp ((16:ℝ)/15*c)) := rfl
  have hWfpos : 0 < Wf c := by
    rw [hWf_eq]
    refine div_pos hcpos ?_
    have hlt : Real.exp ((16:ℝ)/15*c) < Real.exp ((73:ℝ)/30*c) := by
      rw [Real.exp_lt_exp]; nlinarith [hcpos]
    linarith
  have h37 : -(ac*c) + (73:ℝ)/30*c = (-(37:ℝ)/15)*c := by rw [Work.LinnikAreas.A7.ac]; ring
  have hE73 : Real.exp (-(ac*c) + (73:ℝ)/30*c) ≤ lam/270 := by
    have hsplit : (-(37:ℝ)/15)*c = -L + -((1442:ℝ)/1000*L) := by rw [hc]; ring
    have h1 : Real.exp (-(ac*c) + (73:ℝ)/30*c) = Real.exp (-L) * Real.exp (-((1442:ℝ)/1000*L)) := by
      rw [h37, hsplit, Real.exp_add]
    rw [h1, hExpL]
    calc lam * Real.exp (-((1442:ℝ)/1000*L)) ≤ lam * (1/270) := mul_le_mul_of_nonneg_left hExp1442 hlam.le
      _ = lam/270 := by ring
  have hWfinv : (Wf c)⁻¹ ≤ Real.exp ((73:ℝ)/30*c)/c := by
    rw [hWf_eq, inv_div]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos ((16:ℝ)/15*c)]) hcpos.le
  have hPhiWf : Phi c / Wf c ≤ lam/486 := by
    have hB : Bfun ((3:ℝ)/10) c ≤ 19/9 := Bfun_310_le hcpos
    have hPhi_le : Phi c ≤ (19/9) * Real.exp (-(ac*c)) := by
      rw [show Phi c = Real.exp (-(ac*c)) * Bfun ((3:ℝ)/10) c from rfl]
      calc Real.exp (-(ac*c)) * Bfun ((3:ℝ)/10) c ≤ Real.exp (-(ac*c)) * (19/9) :=
            mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
        _ = (19/9) * Real.exp (-(ac*c)) := by ring
    rw [div_eq_mul_inv]
    calc Phi c * (Wf c)⁻¹
        ≤ ((19:ℝ)/9 * Real.exp (-(ac*c))) * (Real.exp ((73:ℝ)/30*c)/c) :=
          mul_le_mul hPhi_le hWfinv (le_of_lt (inv_pos.mpr hWfpos)) (by positivity)
      _ = (19:ℝ)/9 * (Real.exp (-(ac*c)) * Real.exp ((73:ℝ)/30*c)) / c := by ring
      _ = (19:ℝ)/9 * Real.exp (-(ac*c) + (73:ℝ)/30*c) / c := by rw [← Real.exp_add]
      _ ≤ lam/486 := by
          have hmid : (19:ℝ)/9 * Real.exp (-(ac*c) + (73:ℝ)/30*c) / c
              ≤ (19:ℝ)/9 * (lam/270) / c :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE73 (by norm_num)) hcpos.le
          have hfin : (19:ℝ)/9 * (lam/270) / c ≤ lam/486 := by
            rw [div_le_iff₀ hcpos]
            have key : (19:ℝ)/2430 ≤ c/486 := by
              rw [le_div_iff₀ (by norm_num : (0:ℝ) < 486)]; nlinarith [hcge]
            calc (19:ℝ)/9 * (lam/270) = lam * ((19:ℝ)/2430) := by ring
              _ ≤ lam * (c/486) := mul_le_mul_of_nonneg_left key hlam.le
              _ = lam/486 * c := by ring
          linarith [hmid, hfin]
  have hEinvWf : Real.exp (-(ac*c)) / Wf c ≤ lam/1026 := by
    rw [div_eq_mul_inv]
    calc Real.exp (-(ac*c)) * (Wf c)⁻¹ ≤ Real.exp (-(ac*c)) * (Real.exp ((73:ℝ)/30*c)/c) :=
          mul_le_mul_of_nonneg_left hWfinv (Real.exp_pos _).le
      _ = Real.exp (-(ac*c)) * Real.exp ((73:ℝ)/30*c) / c := by rw [mul_div_assoc]
      _ = Real.exp (-(ac*c) + (73:ℝ)/30*c) / c := by rw [← Real.exp_add]
      _ ≤ (lam/270)/c := div_le_div_of_nonneg_right hE73 hcpos.le
      _ ≤ lam/1026 := by
          rw [div_le_iff₀ hcpos]
          have key : (1:ℝ)/270 ≤ c/1026 := by
            rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1026)]; nlinarith [hcge]
          calc lam/270 = lam * ((1:ℝ)/270) := by ring
            _ ≤ lam * (c/1026) := mul_le_mul_of_nonneg_left key hlam.le
            _ = lam/1026 * c := by ring
  have hT3 : (Phi c / Wf c) * ((67:ℝ)/6 + εw) ≤ lam * ((67006:ℝ)/2916000) := by
    have hεw' : (67:ℝ)/6 + εw ≤ (67:ℝ)/6 + 1/1000 := by linarith
    calc (Phi c / Wf c) * ((67:ℝ)/6 + εw) ≤ (lam/486) * ((67:ℝ)/6 + 1/1000) :=
          mul_le_mul hPhiWf hεw' (by linarith) (by positivity)
      _ = lam * ((67006:ℝ)/2916000) := by ring
  have hT4 : η * ((Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1) ≤ lam * (4001/40000) := by
    have hεw' : (67:ℝ)/6 + εw ≤ (67:ℝ)/6 + 1/1000 := by linarith
    have h1 : (Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) ≤ (lam/1026) * ((67:ℝ)/6 + 1/1000) :=
      mul_le_mul hEinvWf hεw' (by linarith) (by positivity)
    have h2 : (lam/1026) * ((67:ℝ)/6 + 1/1000) ≤ (1:ℝ)/4000 := by
      have he : (lam/1026) * ((67:ℝ)/6 + 1/1000) = lam * ((33503:ℝ)/3078000) := by ring
      rw [he]
      have hmono : lam * ((33503:ℝ)/3078000) ≤ (2/100) * ((33503:ℝ)/3078000) :=
        mul_le_mul_of_nonneg_right hlam2 (by norm_num)
      have hnum : (2/100) * ((33503:ℝ)/3078000) ≤ (1:ℝ)/4000 := by norm_num
      linarith
    have h3 : (Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1 ≤ 1 + 1/4000 := by linarith
    have h4 : 0 ≤ (Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1 := by
      have hEW : 0 ≤ Real.exp (-(ac*c)) / Wf c := div_nonneg (Real.exp_pos _).le hWfpos.le
      have : 0 ≤ (Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) := mul_nonneg hEW (by linarith)
      linarith
    calc η * ((Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1)
        ≤ (lam/10) * (1 + 1/4000) := mul_le_mul hη2 h3 h4 (by positivity)
      _ = lam * (4001/40000) := by ring
  linarith [hT1', hT2, hT3, hT4]

theorem sec14_uniform {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R lamS η εw lam₁ : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/100000000) (hη2 : η ≤ lamS/10)
    (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hlamS : 0 < lamS) (hnotSiegel : ¬ Work.LinnikContract.SiegelZero q lamS)
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (h348 : lam₁ < (348:ℝ)/1000)
    (hZ1 : Work.LinnikContract.lamOf q ρ₁ < (348:ℝ)/1000 → χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 ∧
        ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) → (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ)
    (hZ5a : ∀ r ∈ Work.LinnikContract.rows14, lamS ≤ Work.LinnikContract.lamOf q ρ₁ → r.1 ≤ Work.LinnikContract.lamOf q ρ₁ → Work.LinnikContract.lamOf q ρ₁ < r.2.1 →
        Work.LinnikContract.Lam0Bound χ₁ ρ₁ r.2.2 ∧ Work.LinnikContract.Lam2Bound χ₁ r.2.2)
    (hZ5b : lamS ≤ Work.LinnikContract.lamOf q ρ₁ → Work.LinnikContract.lamOf q ρ₁ < 2/10 →
        Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((99/100) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁)) ∧
        Work.LinnikContract.Lam2Bound χ₁ ((99/100) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁)))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η)) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (1 - lam₁/9) := by
  classical
  -- (Z1) is available unconditionally because `lam₁ < 348/1000`
  have hZ1' : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 ∧
      ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) →
        (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ :=
    hZ1 (by rw [hlam1]; exact h348)
  have hSle : lamS ≤ lam₁ := by
    rw [← hlam1]
    exact box_api7_p4 hmin.1.1 hZ1'.1 hZ1'.2.1 hZ1'.2.2.1 hnotSiegel hq (by rw [hlam1]; linarith)
  have hSle' : lamS ≤ Work.LinnikContract.lamOf q ρ₁ := by rw [hlam1]; exact hSle
  have hlam0 : 0 < lam₁ := lt_of_lt_of_le hlamS hSle
  -- core reduction: a single `core14` call + one numeric inequality per regime
  have key : ∀ c : ℝ, 0 < c → Work.LinnikContract.Lam0Bound χ₁ ρ₁ c →
      Work.LinnikContract.Lam2Bound χ₁ c →
      (Real.exp (-(ac*lam₁))*((1 - Real.exp (-(Kc*lam₁)))/lam₁)^2/K2
        + Real.exp (-(ac*c))*(Bfun ((3:ℝ)/10) lam₁ + η)
        + (Phi c / Wf c)*((67:ℝ)/6 + εw)
        + η*((Real.exp (-(ac*c))/Wf c)*((67:ℝ)/6 + εw) + 1) ≤ 1 - lam₁/9) →
      ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ((9:ℝ)/100)*(1 - lam₁/9) := by
    intro c hcpos hl0 hl2 hnum
    have hcore := core14 (q := q) (R := R) (c := c) (η := η) (εw := εw) (lam := lam₁)
      hq hR hRlog hRmax hη hcpos hmin hlam1 hlam0 hZ1' hl0 hl2 hS hSiff hD1 hPC
    have hstep : Work.LinnikAreas.A7.core14RHS c η εw lam₁ ≤ ((9:ℝ)/100)*(1 - lam₁/9) := by
      simp only [Work.LinnikAreas.A7.core14RHS, Kc, K2, ac] at hnum ⊢
      ring_nf at hnum ⊢
      linarith
    exact le_trans hcore hstep
  have hle348 : lam₁ ≤ (348:ℝ)/1000 := le_of_lt h348
  have hmem1 : ((3:ℝ)/10, (348:ℝ)/1000, (127:ℝ)/100) ∈ Work.LinnikContract.rows14 := by
    simp [Work.LinnikContract.rows14]
  have hmem2 : ((25:ℝ)/100, (3:ℝ)/10, (141:ℝ)/100) ∈ Work.LinnikContract.rows14 := by
    simp [Work.LinnikContract.rows14]
  have hmem3 : ((2:ℝ)/10, (25:ℝ)/100, (158:ℝ)/100) ∈ Work.LinnikContract.rows14 := by
    simp [Work.LinnikContract.rows14]
  have hmem4 : ((0:ℝ), (2:ℝ)/10, (18:ℝ)/10) ∈ Work.LinnikContract.rows14 := by
    simp [Work.LinnikContract.rows14]
  rcases lt_or_ge lam₁ (2/100) with hlt | hge
  · -- repulsion regime: `c = (99/100)·log(1/λ₁)`
    have hlt210 : Work.LinnikContract.lamOf q ρ₁ < 2/10 := by rw [hlam1]; linarith
    obtain ⟨hl0, hl2⟩ := hZ5b hSle' hlt210
    have hl0' : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((99:ℝ)/100 * Real.log (1/lam₁)) := by
      simpa only [hlam1] using hl0
    have hl2' : Work.LinnikContract.Lam2Bound χ₁ ((99:ℝ)/100 * Real.log (1/lam₁)) := by
      simpa only [hlam1] using hl2
    refine key ((99:ℝ)/100 * Real.log (1/lam₁)) ?_ hl0' hl2' ?_
    · have h1 : lam₁ < 1 := by linarith
      have hlog : 0 < Real.log (1/lam₁) := by
        rw [one_div, Real.log_inv]
        exact neg_pos.mpr (Real.log_neg hlam0 h1)
      have : (0:ℝ) < (99:ℝ)/100 := by norm_num
      positivity
    · have hη2' : η ≤ lam₁/10 := by linarith
      exact sec14_repel_aux (lam := lam₁) (η := η) (εw := εw)
        hlam0 (le_of_lt hlt) hη hη1 hη2' hεw hεw1
  · rcases lt_or_ge lam₁ (25/100) with h2 | h2
    · rcases lt_or_ge lam₁ (2/10) with h3 | h3
      · -- `c = 18/10`
        obtain ⟨hl0, hl2⟩ := hZ5a _ hmem4 hSle' (by rw [hlam1]; linarith [hlam0])
          (by rw [hlam1]; linarith)
        refine key ((18:ℝ)/10) (by norm_num) hl0 hl2 ?_
        exact sec14_num_rows (lam := lam₁) (c := (18:ℝ)/10) (η := η) (εw := εw)
          hlam0 hle348 (Or.inr (Or.inr (Or.inr ⟨rfl, hge, le_of_lt h3⟩))) hη hη1 hεw hεw1
      · -- `c = 158/100`
        obtain ⟨hl0, hl2⟩ := hZ5a _ hmem3 hSle' (by rw [hlam1]; linarith [hlam0])
          (by rw [hlam1]; linarith)
        refine key ((158:ℝ)/100) (by norm_num) hl0 hl2 ?_
        exact sec14_num_rows (lam := lam₁) (c := (158:ℝ)/100) (η := η) (εw := εw)
          hlam0 hle348 (Or.inr (Or.inr (Or.inl ⟨rfl, h3, le_of_lt h2⟩))) hη hη1 hεw hεw1
    · rcases lt_or_ge lam₁ (3/10) with h1 | h1
      · -- `c = 141/100`
        obtain ⟨hl0, hl2⟩ := hZ5a _ hmem2 hSle' (by rw [hlam1]; linarith [hlam0])
          (by rw [hlam1]; linarith)
        refine key ((141:ℝ)/100) (by norm_num) hl0 hl2 ?_
        exact sec14_num_rows (lam := lam₁) (c := (141:ℝ)/100) (η := η) (εw := εw)
          hlam0 hle348 (Or.inr (Or.inl ⟨rfl, h2, le_of_lt h1⟩)) hη hη1 hεw hεw1
      · -- `c = 127/100`
        obtain ⟨hl0, hl2⟩ := hZ5a _ hmem1 hSle' (by rw [hlam1]; linarith [hlam0])
          (by rw [hlam1]; linarith)
        refine key ((127:ℝ)/100) (by norm_num) hl0 hl2 ?_
        exact sec14_num_rows (lam := lam₁) (c := (127:ℝ)/100) (η := η) (εw := εw)
          hlam0 hle348 (Or.inl ⟨rfl, h1⟩) hη hη1 hεw hεw1

end Work.A7
