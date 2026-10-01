import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.LinnikAreas.A7.ValueLemmas
import Submission.Work.LinnikAreas.A7.NumPoints
import Submission.Work.A7.Bfun_antitone
import Submission.Work.A7.Bfun_le_at_zero_of_pos

namespace Work.A7

open Work.LinnikContract
open Work.LinnikAreas.A7

/-!
# AREA 7 — the §14 rows (`0 < λ ≤ 348/1000`), numeric verification

This file proves `Work.A7.sec14_num_rows`, the "four explicit rows" numeric input of the
`§14` branch of the assembly (`Work.LinnikAreas.A7.sec14_bound`).

For `λ` in the row `[a,b]` with associated value `c` we bound each of the four summands by a
rational constant, using

* antitonicity of `B(3/10,·)` (`Work.A7.Bfun_antitone`) and the crude bound `B ≤ B(0) = 19/9`
  (`Work.A7.Bfun_le_at_zero_of_pos`),
* monotonicity of `t ↦ (1-e^{-Kt})/t` (proved here elementarily, `one_sub_antitone`),
* the tabulated rational certificates `v_*` of `A7/NumPoints.lean` for the value of `c`
  (`Phi c`, `Wf c`) and for the row values `λ = 1/5, 1/4, 3/10`,
* the tabulated exponentials `exF_a_*` of `A7/NumExp.lean`; at the two remaining points
  `λ = 1/50, 3/100` the needed enclosures are produced here from
  `Work.LinnikAreas.A7.exp_neg_le_rat`/`exp_neg_ge_rat`.

The remaining step is a single rational inequality per row, discharged by `norm_num`.
-/

/-! ## Elementary bounds -/

/-- `B(K,0) = 1/(3K)+1`; for `K = 3/10` this is `19/9`. -/
private lemma Bfun_at_zero : Work.LinnikContract.Bfun ((3:ℝ)/10) 0 = 19/9 := by
  rw [Work.LinnikContract.Bfun, if_pos rfl]; norm_num

/-- Crude but uniform upper bound `B(3/10, x) ≤ 19/9` for `x > 0`. -/
private lemma Bfun_le_crude {x : ℝ} (hx : 0 < x) :
    Work.LinnikContract.Bfun ((3:ℝ)/10) x ≤ 19/9 := by
  rw [← Bfun_at_zero]
  exact Work.A7.Bfun_le_at_zero_of_pos (K := (3:ℝ)/10) (by norm_num) hx

/-- Key elementary inequality: for `0 < u ≤ v`, `u(1-e^{-v}) ≤ v(1-e^{-u})`. -/
private lemma key_uv {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    u * (1 - Real.exp (-v)) ≤ v * (1 - Real.exp (-u)) := by
  have hle : u ≤ Real.exp u - 1 := by have := Real.add_one_le_exp u; linarith
  have h1 : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    have hmul : (u * Real.exp (-u)) * Real.exp u ≤ (1 - Real.exp (-u)) * Real.exp u := by
      calc (u * Real.exp (-u)) * Real.exp u = u := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ Real.exp u - 1 := hle
        _ = (1 - Real.exp (-u)) * Real.exp u := by
            rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    exact le_of_mul_le_mul_right hmul (Real.exp_pos u)
  have h2 : 1 - Real.exp (-(v - u)) ≤ v - u := by
    have h := Real.one_sub_le_exp_neg (v - u)
    linarith
  have hneg : 0 ≤ 1 - Real.exp (-u) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; linarith
  have hnegh : 0 ≤ 1 - Real.exp (-(v - u)) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; linarith
  have hm1 : u * Real.exp (-u) * (1 - Real.exp (-(v - u)))
      ≤ (1 - Real.exp (-u)) * (1 - Real.exp (-(v - u))) :=
    mul_le_mul_of_nonneg_right h1 hnegh
  have hm2 : (1 - Real.exp (-u)) * (1 - Real.exp (-(v - u))) ≤ (1 - Real.exp (-u)) * (v - u) :=
    mul_le_mul_of_nonneg_left h2 hneg
  have hexpv : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e1 : u * (1 - Real.exp (-v))
      = u * (1 - Real.exp (-u)) + u * Real.exp (-u) * (1 - Real.exp (-(v - u))) := by
    rw [hexpv]; ring
  have e2 : v * (1 - Real.exp (-u)) = u * (1 - Real.exp (-u)) + (v - u) * (1 - Real.exp (-u)) := by
    ring
  rw [e1, e2]
  linarith

/-- `t ↦ (1-e^{-Kt})/t` is non-increasing on `(0,∞)` for `K > 0`. -/
private lemma one_sub_antitone {K : ℝ} (hK : 0 < K) :
    ∀ {x y : ℝ}, 0 < x → x ≤ y →
      (1 - Real.exp (-(K * y))) / y ≤ (1 - Real.exp (-(K * x))) / x := by
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [div_le_div_iff₀ hy hx]
  have h := key_uv (u := K * x) (v := K * y) (mul_pos hK hx)
    (mul_le_mul_of_nonneg_left hxy hK.le)
  have : K * ((1 - Real.exp (-(K * y))) * x) ≤ K * ((1 - Real.exp (-(K * x))) * y) := by
    calc K * ((1 - Real.exp (-(K * y))) * x) = (K * x) * (1 - Real.exp (-(K * y))) := by ring
      _ ≤ (K * y) * (1 - Real.exp (-(K * x))) := h
      _ = K * ((1 - Real.exp (-(K * x))) * y) := by ring
  exact le_of_mul_le_mul_left this hK

/-- Combine an upper enclosure of `e^{-aλ}` with one of `((1-e^{-Kλ})/λ)^2/K²`. -/
private lemma T1_ub {a Et F2b : ℝ} (hE : Real.exp (-(ac*a)) ≤ Et) (hEt0 : 0 ≤ Et)
    (hF : ((1 - Real.exp (-(Kc*a)))/a)^2 / K2 ≤ F2b) :
    Real.exp (-(ac*a)) * ((1 - Real.exp (-(Kc*a)))/a)^2 / K2 ≤ Et * F2b := by
  rw [mul_div_assoc]
  refine mul_le_mul hE hF ?_ hEt0
  refine div_nonneg (sq_nonneg _) (by norm_num [Work.LinnikAreas.A7.K2])

/-! ## The two row values `λ = 1/50`, `3/100` missing from the tables -/

private lemma expF_a_1_50 : Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/50))) ≤ ((906648904:ℝ)/(1000000000)) := by
  apply Work.LinnikAreas.A7.exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])

private lemma expG_c_1_50 : ((994017964:ℝ)/(1000000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/50))) := by
  apply Work.LinnikAreas.A7.exp_neg_ge_rat (n := 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])

private lemma expF_a_3_100 : Real.exp (-(((49:ℝ)/10) * ((3:ℝ)/100))) ≤ ((863293979:ℝ)/(1000000000)) := by
  apply Work.LinnikAreas.A7.exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])

private lemma expG_c_3_100 : ((991040378:ℝ)/(1000000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((3:ℝ)/100))) := by
  apply Work.LinnikAreas.A7.exp_neg_ge_rat (n := 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])

private lemma T1_at_1_50 :
    Real.exp (-(Work.LinnikAreas.A7.ac * ((1:ℝ)/50))) *
        ((1 - Real.exp (-(Work.LinnikAreas.A7.Kc * ((1:ℝ)/50))))/((1:ℝ)/50))^2
        / Work.LinnikAreas.A7.K2
      ≤ (902:ℝ)/1000 := by
  rw [Work.LinnikAreas.A7.ac_eq, Work.LinnikAreas.A7.Kc_eq, Work.LinnikAreas.A7.K2_eq]
  have hX0 : 0 ≤ (1 - Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/50))))/((1:ℝ)/50) := by
    refine div_nonneg ?_ (by norm_num)
    rw [sub_nonneg, Real.exp_le_one_iff]; norm_num
  have hXY : (1 - Real.exp (-(((3:ℝ)/10)*((1:ℝ)/50))))/((1:ℝ)/50)
      ≤ (1 - (994017964:ℝ)/1000000000)/((1:ℝ)/50) := by
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    linarith [expG_c_1_50]
  have hX2 : ((1 - Real.exp (-(((3:ℝ)/10)*((1:ℝ)/50))))/((1:ℝ)/50))^2
      ≤ ((1 - (994017964:ℝ)/1000000000)/((1:ℝ)/50))^2 := pow_le_pow_left₀ hX0 hXY 2
  have hmul : Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/50)))
        * ((1 - Real.exp (-(((3:ℝ)/10)*((1:ℝ)/50))))/((1:ℝ)/50))^2
      ≤ (906648904:ℝ)/1000000000 * ((1 - (994017964:ℝ)/1000000000)/((1:ℝ)/50))^2 :=
    mul_le_mul expF_a_1_50 hX2 (sq_nonneg _) (by norm_num)
  calc Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/50)))
          * ((1 - Real.exp (-(((3:ℝ)/10)*((1:ℝ)/50))))/((1:ℝ)/50))^2 / ((9:ℝ)/100)
      ≤ (906648904:ℝ)/1000000000 * ((1 - (994017964:ℝ)/1000000000)/((1:ℝ)/50))^2
          / ((9:ℝ)/100) := div_le_div_of_nonneg_right hmul (by norm_num)
    _ ≤ (902:ℝ)/1000 := by norm_num

private lemma T1_at_3_100 :
    Real.exp (-(Work.LinnikAreas.A7.ac * ((3:ℝ)/100))) *
        ((1 - Real.exp (-(Work.LinnikAreas.A7.Kc * ((3:ℝ)/100))))/((3:ℝ)/100))^2
        / Work.LinnikAreas.A7.K2
      ≤ (856:ℝ)/1000 := by
  rw [Work.LinnikAreas.A7.ac_eq, Work.LinnikAreas.A7.Kc_eq, Work.LinnikAreas.A7.K2_eq]
  have hX0 : 0 ≤ (1 - Real.exp (-(((3:ℝ)/10) * ((3:ℝ)/100))))/((3:ℝ)/100) := by
    refine div_nonneg ?_ (by norm_num)
    rw [sub_nonneg, Real.exp_le_one_iff]; norm_num
  have hXY : (1 - Real.exp (-(((3:ℝ)/10)*((3:ℝ)/100))))/((3:ℝ)/100)
      ≤ (1 - (991040378:ℝ)/1000000000)/((3:ℝ)/100) := by
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    linarith [expG_c_3_100]
  have hX2 : ((1 - Real.exp (-(((3:ℝ)/10)*((3:ℝ)/100))))/((3:ℝ)/100))^2
      ≤ ((1 - (991040378:ℝ)/1000000000)/((3:ℝ)/100))^2 := pow_le_pow_left₀ hX0 hXY 2
  have hmul : Real.exp (-(((49:ℝ)/10) * ((3:ℝ)/100)))
        * ((1 - Real.exp (-(((3:ℝ)/10)*((3:ℝ)/100))))/((3:ℝ)/100))^2
      ≤ (863293979:ℝ)/1000000000 * ((1 - (991040378:ℝ)/1000000000)/((3:ℝ)/100))^2 :=
    mul_le_mul expF_a_3_100 hX2 (sq_nonneg _) (by norm_num)
  calc Real.exp (-(((49:ℝ)/10) * ((3:ℝ)/100)))
          * ((1 - Real.exp (-(((3:ℝ)/10)*((3:ℝ)/100))))/((3:ℝ)/100))^2 / ((9:ℝ)/100)
      ≤ (863293979:ℝ)/1000000000 * ((1 - (991040378:ℝ)/1000000000)/((3:ℝ)/100))^2
          / ((9:ℝ)/100) := div_le_div_of_nonneg_right hmul (by norm_num)
    _ ≤ (856:ℝ)/1000 := by norm_num

private lemma step {a b lam c η εw η1 εw1 T1b Bb Ecl Pcu Wfl : ℝ}
    (ha : 0 < a) (hla : a ≤ lam) (hlb : lam ≤ b)
    (hη : 0 ≤ η) (hη1 : η ≤ η1) (hη10 : 0 ≤ η1)
    (hεw : 0 ≤ εw) (hεw1 : εw ≤ εw1)
    (hT1 : Real.exp (-(ac*a)) * ((1 - Real.exp (-(Kc*a)))/a)^2 / K2 ≤ T1b)
    (hBb : Bfun Kc a ≤ Bb)
    (hEcl : Real.exp (-(ac*c)) ≤ Ecl)
    (hPcu : Phi c ≤ Pcu) (hPcu0 : 0 ≤ Pcu) (hWfl : Wfl ≤ Wf c) (hWfl0 : 0 < Wfl)
    (hmain : T1b + Ecl*(Bb + η1) + (Pcu/Wfl)*((67:ℝ)/6+εw1)
        + η1*((Ecl/Wfl)*((67:ℝ)/6+εw1) + 1) ≤ 1 - b/9) :
    Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2
      + Real.exp (-(ac*c)) * (Bfun Kc lam + η)
      + (Phi c / Wf c) * ((67:ℝ)/6 + εw)
      + η * ((Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1)
      ≤ 1 - lam/9 := by
  have hacpos : (0:ℝ) < ac := by norm_num [Work.LinnikAreas.A7.ac]
  have hKcpos : (0:ℝ) < Kc := by norm_num [Work.LinnikAreas.A7.Kc]
  have hK2pos : (0:ℝ) < K2 := by norm_num [Work.LinnikAreas.A7.K2]
  have hlampos : 0 < lam := lt_of_lt_of_le ha hla
  -- (1) the first term decreases from `lam` to `a`
  have hterm1 : Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2 ≤ T1b := by
    refine le_trans ?_ hT1
    have hmono := one_sub_antitone (K := Kc) hKcpos ha hla
    have hsq : ((1 - Real.exp (-(Kc*lam)))/lam)^2 ≤ ((1 - Real.exp (-(Kc*a)))/a)^2 := by
      refine pow_le_pow_left₀ ?_ hmono 2
      refine div_nonneg ?_ hlampos.le
      rw [sub_nonneg, Real.exp_le_one_iff]
      nlinarith [hKcpos, hlampos]
    have hexp : Real.exp (-(ac*lam)) ≤ Real.exp (-(ac*a)) := by
      rw [Real.exp_le_exp]; nlinarith [hacpos, hla]
    exact div_le_div_of_nonneg_right (mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le)
      hK2pos.le
  -- (2) second term
  have hterm2 : Real.exp (-(ac*c)) * (Bfun Kc lam + η) ≤ Ecl * (Bb + η1) := by
    have hBle : Bfun Kc lam ≤ Bb :=
      le_trans (Bfun_antitone (K := Kc) hKcpos ha hla) hBb
    have hEcl0 : 0 ≤ Ecl := le_trans (Real.exp_pos _).le hEcl
    have h1 : Bfun Kc lam + η ≤ Bb + η1 := by linarith
    have hBpos := Work.LinnikContract.API.Bfun_pos hKcpos hlampos
    have h2 : Real.exp (-(ac*c)) * (Bfun Kc lam + η) ≤ Ecl * (Bfun Kc lam + η) :=
      mul_le_mul_of_nonneg_right hEcl (by linarith)
    exact le_trans h2 (mul_le_mul_of_nonneg_left h1 hEcl0)
  -- (3) third term
  have hterm3 : (Phi c / Wf c) * ((67:ℝ)/6 + εw) ≤ (Pcu/Wfl) * ((67:ℝ)/6 + εw1) := by
    have hWfc : 0 < Wf c := lt_of_lt_of_le hWfl0 hWfl
    have hEcl0 : 0 ≤ Ecl := le_trans (Real.exp_pos _).le hEcl
    have hdiv : Phi c / Wf c ≤ Pcu / Wfl := by
      have h1 : Phi c / Wf c ≤ Pcu / Wf c := div_le_div_of_nonneg_right hPcu hWfc.le
      have h2 : Pcu / Wf c ≤ Pcu / Wfl :=
        div_le_div_of_nonneg_left hPcu0 hWfl0 hWfl
      linarith
    exact mul_le_mul hdiv (by linarith) (by linarith)
      (div_nonneg hPcu0 hWfl0.le)
  -- (4) fourth term
  have hterm4 : η * ((Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1)
      ≤ η1 * ((Ecl / Wfl) * ((67:ℝ)/6 + εw1) + 1) := by
    have hWfc : 0 < Wf c := lt_of_lt_of_le hWfl0 hWfl
    have hEcl0 : 0 ≤ Ecl := le_trans (Real.exp_pos _).le hEcl
    have hdiv : Real.exp (-(ac*c)) / Wf c ≤ Ecl / Wfl := by
      have h1 : Real.exp (-(ac*c)) / Wf c ≤ Ecl / Wf c :=
        div_le_div_of_nonneg_right hEcl hWfc.le
      have h2 : Ecl / Wf c ≤ Ecl / Wfl :=
        div_le_div_of_nonneg_left hEcl0 hWfl0 hWfl
      linarith
    have hinner : (Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1
        ≤ (Ecl / Wfl) * ((67:ℝ)/6 + εw1) + 1 := by
      have h := mul_le_mul hdiv (by linarith : (67:ℝ)/6 + εw ≤ (67:ℝ)/6 + εw1)
        (by linarith) (div_nonneg hEcl0 hWfl0.le)
      linarith
    have hEdiv : 0 ≤ Real.exp (-(ac*c)) / Wf c := div_nonneg (Real.exp_pos _).le hWfc.le
    have hin1 : 0 ≤ (Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1 := by
      have := mul_nonneg hEdiv (by linarith : (0:ℝ) ≤ (67:ℝ)/6 + εw); linarith
    exact mul_le_mul hη1 hinner hin1 hη10
  linarith [hterm1, hterm2, hterm3, hterm4, hmain, hlb]


theorem sec14_num_rows {lam c η εw : ℝ} (hlam : 0 < lam) (hlam348 : lam ≤ 348/1000)
    (hc : (c = 127/100 ∧ 3/10 ≤ lam) ∨ (c = 141/100 ∧ 25/100 ≤ lam ∧ lam ≤ 3/10)
       ∨ (c = 158/100 ∧ 2/10 ≤ lam ∧ lam ≤ 25/100) ∨ (c = 18/10 ∧ 2/100 ≤ lam ∧ lam ≤ 2/10))
    (hη : 0 ≤ η) (hη1 : η ≤ 1/100000000) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    Real.exp (-(Work.LinnikAreas.A7.ac*lam)) * ((1 - Real.exp (-(Work.LinnikAreas.A7.Kc*lam)))/lam)^2
        / Work.LinnikAreas.A7.K2
      + Real.exp (-(Work.LinnikAreas.A7.ac*c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)
      + (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw)
      + η * ((Real.exp (-(Work.LinnikAreas.A7.ac*c)) / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw) + 1)
      ≤ 1 - lam/9 := by
  rcases hc with ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · -- c = 127/100,  λ ∈ [3/10, 348/1000]
    exact step (a := (3:ℝ)/10) (b := (348:ℝ)/1000) (c := (127:ℝ)/100)
      (η1 := (1:ℝ)/100000000) (εw1 := (1:ℝ)/1000)
      (T1b := ((22992549:ℝ)/100000000) * ((91454837:ℝ)/100000000))
      (Bb := (19:ℝ)/9) (Ecl := (198329:ℝ)/100000000)
      (Pcu := (310473:ℝ)/100000000) (Wfl := (701311:ℝ)/10000000)
      (by norm_num) (by linarith [h, hlam]) hlam348 hη hη1 (by norm_num) hεw hεw1
      (T1_ub (Et := (22992549:ℝ)/100000000) (F2b := (91454837:ℝ)/100000000)
        exF_a_3_10 (by norm_num) (v_3_10).2.2.2.2.2.2)
      (Bfun_le_crude (by norm_num))
      exF_a_127_100 (v_127_100).1 (by norm_num) (v_127_100).2.2.2.1 (by norm_num)
      (by norm_num)
  · -- c = 141/100,  λ ∈ [25/100, 3/10]
    exact step (a := (1:ℝ)/4) (b := (3:ℝ)/10) (c := (141:ℝ)/100)
      (η1 := (1:ℝ)/100000000) (εw1 := (1:ℝ)/1000)
      (T1b := ((29375771:ℝ)/100000000) * ((46408931:ℝ)/50000000))
      (Bb := (19:ℝ)/9) (Ecl := (24969:ℝ)/25000000)
      (Pcu := (151671:ℝ)/100000000) (Wfl := (2669657:ℝ)/50000000)
      (by norm_num) (by linarith) h2 hη hη1 (by norm_num) hεw hεw1
      (T1_ub (Et := (29375771:ℝ)/100000000) (F2b := (46408931:ℝ)/50000000)
        exF_a_1_4 (by norm_num) (v_1_4).2.2.2.2.2.2)
      (Bfun_le_crude (by norm_num))
      exF_a_141_100 (v_141_100).1 (by norm_num) (v_141_100).2.2.2.1 (by norm_num)
      (by norm_num)
  · -- c = 158/100,  λ ∈ [2/10, 25/100]
    rw [show (158:ℝ)/100 = (79:ℝ)/50 by norm_num]
    exact step (a := (1:ℝ)/5) (b := (25:ℝ)/100) (c := (79:ℝ)/50)
      (η1 := (1:ℝ)/100000000) (εw1 := (1:ℝ)/1000)
      (T1b := ((3753111:ℝ)/10000000) * ((47102361:ℝ)/50000000))
      (Bb := (19:ℝ)/9) (Ecl := (43421:ℝ)/100000000)
      (Pcu := (7949:ℝ)/12500000) (Wfl := (764229:ℝ)/20000000)
      (by norm_num) (by linarith) h2 hη hη1 (by norm_num) hεw hεw1
      (T1_ub (Et := (3753111:ℝ)/10000000) (F2b := (47102361:ℝ)/50000000)
        exF_a_1_5 (by norm_num) (v_1_5).2.2.2.2.2.2)
      (Bfun_le_crude (by norm_num))
      exF_a_79_50 (v_79_50).1 (by norm_num) (v_79_50).2.2.2.1 (by norm_num)
      (by norm_num)
  · -- c = 18/10,  λ ∈ [2/100, 2/10]
    rw [show (18:ℝ)/10 = (9:ℝ)/5 by norm_num]
    rcases lt_or_ge lam ((3:ℝ)/100) with h3 | h3
    · -- λ ∈ [2/100, 3/100]
      exact step (a := (1:ℝ)/50) (b := (3:ℝ)/100) (c := (9:ℝ)/5)
        (η1 := (1:ℝ)/100000000) (εw1 := (1:ℝ)/1000) (T1b := (902:ℝ)/1000)
        (Bb := (19:ℝ)/9) (Ecl := (591:ℝ)/4000000)
        (Pcu := (20669:ℝ)/100000000) (Wfl := (98607:ℝ)/4000000)
        (by norm_num) (by linarith) (le_of_lt h3) hη hη1 (by norm_num) hεw hεw1
        T1_at_1_50 (Bfun_le_crude (by norm_num))
        exF_a_9_5 (v_9_5).1 (by norm_num) (v_9_5).2.2.2.1 (by norm_num)
        (by norm_num)
    · -- λ ∈ [3/100, 2/10]
      exact step (a := (3:ℝ)/100) (b := (2:ℝ)/10) (c := (9:ℝ)/5)
        (η1 := (1:ℝ)/100000000) (εw1 := (1:ℝ)/1000) (T1b := (856:ℝ)/1000)
        (Bb := (19:ℝ)/9) (Ecl := (591:ℝ)/4000000)
        (Pcu := (20669:ℝ)/100000000) (Wfl := (98607:ℝ)/4000000)
        (by norm_num) h3 h2 hη hη1 (by norm_num) hεw hεw1
        T1_at_3_100 (Bfun_le_crude (by norm_num))
        exF_a_9_5 (v_9_5).1 (by norm_num) (v_9_5).2.2.2.1 (by norm_num)
        (by norm_num)

end Work.A7
