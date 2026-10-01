/-
# Toolkit: rational bounds for `Phi`, `Wf`, `Bfun`, `F2`, `Cf`, `Aref`

The numerical verification of AREA 7 reduces every estimate about the explicit functions
`Phi p = e^{-(49/10)p}B(3/10,p)`, `Wf p = w(p)`, `Cf L p = max 0 (Phi p - Phi L · Wf p/Wf L)`,
`Aref c0 p = (e^{-a p}-e^{-a c0})(B(3/10,p) - (9/100)⁻¹F₂(p))` at explicit rationals to

* rational enclosures of four exponentials (generated in `A7/Numerics.lean`), and
* one rational inequality closed by `norm_num`.

Monotonicity facts about `Bfun`, `Phi`, `Cf` enter only through explicit hypotheses.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.LinnikAreas.A7.ExpBounds
import Submission.Work.LinnikContract.API.Bfun_pos

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

lemma Kc_eq : Kc = (3:ℝ)/10 := rfl
lemma K2_eq : K2 = (9:ℝ)/100 := rfl
lemma ac_eq : ac = (49:ℝ)/10 := rfl

/-! ## `Bfun` -/

lemma Bfun_le {p gl gh r : ℝ} (hp : 0 < p)
    (hgl : gl ≤ Real.exp (-((3:ℝ)/5*p))) (hgh : Real.exp (-((3:ℝ)/5*p)) ≤ gh)
    (hr : (1-gl)/(6*((9:ℝ)/100)*p) + (2*((3:ℝ)/10)*p - 1 + gh)/(2*((9:ℝ)/100)*p^2) ≤ r) :
    Bfun ((3:ℝ)/10) p ≤ r := by
  have hB : Bfun ((3:ℝ)/10) p
      = (1 - Real.exp (-((3:ℝ)/5*p)))/(6*((9:ℝ)/100)*p)
        + (2*((3:ℝ)/10)*p - 1 + Real.exp (-((3:ℝ)/5*p)))/(2*((9:ℝ)/100)*p^2) := by
    rw [Bfun, if_neg (ne_of_gt hp)]
    norm_num
  rw [hB]
  have h1 : (1 - Real.exp (-((3:ℝ)/5*p)))/(6*((9:ℝ)/100)*p) ≤ (1-gl)/(6*((9:ℝ)/100)*p) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : (2*((3:ℝ)/10)*p - 1 + Real.exp (-((3:ℝ)/5*p)))/(2*((9:ℝ)/100)*p^2)
      ≤ (2*((3:ℝ)/10)*p - 1 + gh)/(2*((9:ℝ)/100)*p^2) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

lemma Bfun_ge {p gl gh r : ℝ} (hp : 0 < p)
    (hgl : gl ≤ Real.exp (-((3:ℝ)/5*p))) (hgh : Real.exp (-((3:ℝ)/5*p)) ≤ gh)
    (hr : r ≤ (1-gh)/(6*((9:ℝ)/100)*p) + (2*((3:ℝ)/10)*p - 1 + gl)/(2*((9:ℝ)/100)*p^2)) :
    r ≤ Bfun ((3:ℝ)/10) p := by
  have hB : Bfun ((3:ℝ)/10) p
      = (1 - Real.exp (-((3:ℝ)/5*p)))/(6*((9:ℝ)/100)*p)
        + (2*((3:ℝ)/10)*p - 1 + Real.exp (-((3:ℝ)/5*p)))/(2*((9:ℝ)/100)*p^2) := by
    rw [Bfun, if_neg (ne_of_gt hp)]
    norm_num
  rw [hB]
  have h1 : (1-gh)/(6*((9:ℝ)/100)*p) ≤ (1 - Real.exp (-((3:ℝ)/5*p)))/(6*((9:ℝ)/100)*p) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : (2*((3:ℝ)/10)*p - 1 + gl)/(2*((9:ℝ)/100)*p^2)
      ≤ (2*((3:ℝ)/10)*p - 1 + Real.exp (-((3:ℝ)/5*p)))/(2*((9:ℝ)/100)*p^2) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-! ## `Phi` -/

lemma Phi_le {p E B r : ℝ} (hp : 0 < p) (hE : Real.exp (-((49:ℝ)/10*p)) ≤ E)
    (hB : Bfun ((3:ℝ)/10) p ≤ B) (hr : E*B ≤ r) : Phi p ≤ r := by
  have hE0 : 0 ≤ E := le_trans (Real.exp_pos _).le hE
  have hB0 : (0:ℝ) ≤ Bfun ((3:ℝ)/10) p :=
    (Work.LinnikContract.API.Bfun_pos (K := (3:ℝ)/10) (lam := p) (by norm_num) hp).le
  rw [Phi, Kc_eq, ac_eq]
  calc Real.exp (-((49:ℝ)/10*p)) * Bfun ((3:ℝ)/10) p
      ≤ E * Bfun ((3:ℝ)/10) p := mul_le_mul_of_nonneg_right hE hB0
    _ ≤ E * B := mul_le_mul_of_nonneg_left hB hE0
    _ ≤ r := hr

lemma Phi_ge {p E B r : ℝ} (hp : 0 < p) (hE : E ≤ Real.exp (-((49:ℝ)/10*p)))
    (hB : B ≤ Bfun ((3:ℝ)/10) p) (hB0 : 0 ≤ B) (hr : r ≤ E*B) : r ≤ Phi p := by
  have hE0 : 0 ≤ Real.exp (-((49:ℝ)/10*p)) := (Real.exp_pos _).le
  rw [Phi, Kc_eq, ac_eq]
  calc r ≤ E * B := hr
    _ ≤ Real.exp (-((49:ℝ)/10*p)) * B := mul_le_mul_of_nonneg_right hE hB0
    _ ≤ Real.exp (-((49:ℝ)/10*p)) * Bfun ((3:ℝ)/10) p :=
        mul_le_mul_of_nonneg_left hB hE0

/-! ## `K⁻²F₂` -/

lemma F2K2_le {p al r : ℝ} (hp : 0 < p) (hal : al ≤ Real.exp (-((3:ℝ)/10*p)))
    (hr : ((1-al)/p)^2 / ((9:ℝ)/100) ≤ r) :
    ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2 / ((9:ℝ)/100) ≤ r := by
  have h1 : (1 - Real.exp (-((3:ℝ)/10*p)))/p ≤ (1-al)/p :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hp)
  have h2 : (0:ℝ) ≤ (1 - Real.exp (-((3:ℝ)/10*p)))/p := by
    apply div_nonneg _ (le_of_lt hp)
    rw [sub_nonneg, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity)
  have h3 : ((1 - Real.exp (-((3:ℝ)/10*p)))/p)^2 ≤ ((1-al)/p)^2 :=
    pow_le_pow_left₀ h2 h1 2
  exact le_trans (div_le_div_of_nonneg_right h3 (by norm_num)) hr

/-! ## `Wf` -/

lemma Wf_eq (p : ℝ) :
    Wf p = (Real.exp ((73:ℝ)/30*p))⁻¹ * (p / (1 - Real.exp (-((41:ℝ)/30*p)))) := by
  have h1 : Real.exp ((73:ℝ)/30*p) * (1 - Real.exp (-((41:ℝ)/30*p)))
      = Real.exp ((73:ℝ)/30*p) - Real.exp ((16:ℝ)/15*p) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [Wf, wHB, ← h1, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

lemma Wf_le {p Pu Qu r : ℝ} (hp : 0 ≤ p) (hPu : 0 ≤ Pu)
    (hP : Real.exp (-((73:ℝ)/30*p)) ≤ Pu)
    (hQ : Real.exp (-((41:ℝ)/30*p)) ≤ Qu) (hQu : Qu < 1)
    (hr : Pu*p/(1-Qu) ≤ r) : Wf p ≤ r := by
  rw [Real.exp_neg] at hP
  have hQlt : Real.exp (-((41:ℝ)/30*p)) < 1 := lt_of_le_of_lt hQ hQu
  rw [Wf_eq]
  have hden : 0 < 1 - Qu := by linarith
  have hden2 : 0 < 1 - Real.exp (-((41:ℝ)/30*p)) := by linarith
  have h1 : p/(1 - Real.exp (-((41:ℝ)/30*p))) ≤ p/(1-Qu) := by
    rw [div_le_div_iff₀ hden2 hden]
    nlinarith
  calc (Real.exp ((73:ℝ)/30*p))⁻¹ * (p/(1 - Real.exp (-((41:ℝ)/30*p))))
      ≤ Pu * (p/(1-Qu)) :=
        mul_le_mul hP h1 (div_nonneg hp (le_of_lt hden2)) hPu
    _ = Pu*p/(1-Qu) := by ring
    _ ≤ r := hr

lemma Wf_ge {p Pl Ql r : ℝ} (hp : 0 < p) (hP : Pl ≤ Real.exp (-((73:ℝ)/30*p)))
    (hQ : Ql ≤ Real.exp (-((41:ℝ)/30*p))) (hQl : Ql < 1)
    (hr : r ≤ Pl*p/(1-Ql)) : r ≤ Wf p := by
  rw [Real.exp_neg] at hP
  have hQlt : Real.exp (-((41:ℝ)/30*p)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  rw [Wf_eq]
  have hden : 0 < 1 - Real.exp (-((41:ℝ)/30*p)) := by linarith
  have hden2 : 0 < 1 - Ql := by linarith
  have h1 : p/(1-Ql) ≤ p/(1 - Real.exp (-((41:ℝ)/30*p))) := by
    rw [div_le_div_iff₀ hden2 hden]
    nlinarith
  calc r ≤ Pl*p/(1-Ql) := hr
    _ = Pl * (p/(1-Ql)) := by ring
    _ ≤ (Real.exp ((73:ℝ)/30*p))⁻¹ * (p/(1 - Real.exp (-((41:ℝ)/30*p)))) :=
        mul_le_mul hP h1 (div_nonneg (le_of_lt hp) (le_of_lt hden2))
          (inv_nonneg.mpr (Real.exp_pos _).le)

/-! ## `Cf` and `Aref` -/

lemma Cf_le {L x Px Wxl PL WLu r : ℝ} (hPx : Phi x ≤ Px) (hPL : PL ≤ Phi L)
    (hPL0 : 0 ≤ PL) (hwx : Wxl ≤ Wf x) (hwx0 : 0 ≤ Wxl)
    (hwL : Wf L ≤ WLu) (hW0 : 0 < Wf L) (hr0 : 0 ≤ r)
    (hr : max 0 (Px - PL * Wxl / WLu) ≤ r) : Cf L x ≤ r := by
  have hWLu0 : 0 < WLu := lt_of_lt_of_le hW0 hwL
  have hPLpos : 0 ≤ Phi L := le_trans hPL0 hPL
  rw [Cf]
  refine max_le hr0 ?_
  have hstep : PL * Wxl / WLu ≤ Phi L * Wf x / Wf L := by
    have h1 : PL * Wxl ≤ Phi L * Wf x := by
      have h2 : Phi L * Wxl ≤ Phi L * Wf x :=
        mul_le_mul_of_nonneg_left hwx hPLpos
      have h3 : PL * Wxl ≤ Phi L * Wxl := mul_le_mul_of_nonneg_right hPL hwx0
      linarith
    have h4 : WLu⁻¹ ≤ (Wf L)⁻¹ := by
      have h5 : 1 / WLu ≤ 1 / (Wf L) := one_div_le_one_div_of_le hW0 hwL
      simpa [one_div] using h5
    calc PL * Wxl / WLu = (PL * Wxl) * WLu⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (Phi L * Wf x) * (Wf L)⁻¹ :=
          mul_le_mul h1 h4 (inv_nonneg.mpr (le_of_lt hWLu0))
            (mul_nonneg hPLpos (le_trans hwx0 hwx))
      _ = Phi L * Wf x / Wf L := by rw [div_eq_mul_inv]
  have hx : Phi x - Phi L * Wf x / Wf L ≤ Px - PL * Wxl / WLu := by linarith
  have hr' : Px - PL * Wxl / WLu ≤ r := le_trans (le_max_right _ _) hr
  exact le_trans hx hr'

lemma Aref_nonneg {c0 p : ℝ} (hpc : p ≤ c0)
    (hBF : ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) p) :
    0 ≤ Aref c0 p := by
  rw [Aref, Kc_eq, K2_eq, ac_eq]
  apply mul_nonneg _ (by linarith)
  rw [sub_nonneg]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma Cst1_le {L c0 p a b Ec0u Ec0l Ea Ba F2a PLl Wlb Wupu r : ℝ}
    (hp : 0 < p) (hpc : p ≤ c0) (hBF : ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) p)
    (hEc0u : Real.exp (-((49:ℝ)/10*c0)) ≤ Ec0u) (hEc0l : Ec0l ≤ Real.exp (-((49:ℝ)/10*c0)))
    (hEa : Real.exp (-((49:ℝ)/10*a)) ≤ Ea) (hBa : Bfun ((3:ℝ)/10) a ≤ Ba)
    (hF2a : ((1-Real.exp (-((3:ℝ)/10*a)))/a)^2/((9:ℝ)/100) ≤ F2a)
    (hEp : Real.exp (-((49:ℝ)/10*p)) ≤ Ea) (hBp : Bfun ((3:ℝ)/10) p ≤ Ba)
    (hF2p : ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ F2a)
    (hPL : PLl ≤ Phi L) (hPL0 : 0 ≤ PLl) (hWlb : Wlb ≤ Wf p) (hWlb0 : 0 ≤ Wlb)
    (hWu : Wf L ≤ Wupu) (hWu0 : 0 < Wupu) (hW0 : 0 < Wf L) (hr0 : 0 ≤ r)
    (hr : Ec0u * Ba + max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu ≤ r) :
    Cf L p - Aref c0 p ≤ r := by
  have hA0 : 0 ≤ Aref c0 p := Aref_nonneg hpc hBF
  have hmax : Cf L p - Aref c0 p ≤ max 0 (Phi p - Aref c0 p - Phi L * Wf p / Wf L) := by
    rw [Cf]
    by_cases h : Phi p - Phi L * Wf p / Wf L ≤ 0
    · have hC : max 0 (Phi p - Phi L * Wf p / Wf L) = 0 := max_eq_left h
      rw [hC]
      have h1 : (0:ℝ) ≤ max 0 (Phi p - Aref c0 p - Phi L * Wf p / Wf L) := le_max_left _ _
      linarith
    · have hpos : 0 < Phi p - Phi L * Wf p / Wf L := not_le.mp h
      have hC : max 0 (Phi p - Phi L * Wf p / Wf L) = Phi p - Phi L * Wf p / Wf L :=
        max_eq_right hpos.le
      rw [hC]
      have h1 : Phi p - Phi L * Wf p / Wf L - Aref c0 p
          ≤ max 0 (Phi p - Aref c0 p - Phi L * Wf p / Wf L) := by
        have h2 := le_max_right (0:ℝ) (Phi p - Aref c0 p - Phi L * Wf p / Wf L)
        linarith
      linarith
  have hid : Phi p - Aref c0 p - Phi L * Wf p / Wf L
      = Real.exp (-((49:ℝ)/10*c0)) * Bfun ((3:ℝ)/10) p
        + (Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0)))
            * (((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100))
        - Phi L * Wf p / Wf L := by
    rw [Aref, Phi, Kc_eq, K2_eq, ac_eq]; ring
  have hBp0 : (0:ℝ) ≤ Bfun ((3:ℝ)/10) p :=
    (Work.LinnikContract.API.Bfun_pos (K := (3:ℝ)/10) (lam := p) (by norm_num) hp).le
  have h1 : Real.exp (-((49:ℝ)/10*c0)) * Bfun ((3:ℝ)/10) p ≤ Ec0u * Ba :=
    mul_le_mul hEc0u hBp hBp0 (le_trans (Real.exp_pos _).le hEc0u)
  have h2 : (Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0)))
        * (((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100))
      ≤ max 0 (Ea - Ec0l) * F2a := by
    by_cases h : 0 ≤ Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0))
    · have hle : max 0 (Ea - Ec0l) = Ea - Ec0l := by
        apply max_eq_right; linarith
      rw [hle]
      exact mul_le_mul (by linarith) hF2p (by positivity) (by linarith)
    · have hsq : (0:ℝ) ≤ ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2 := sq_nonneg _
      have hdiv : (0:ℝ) ≤ ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) :=
        div_nonneg hsq (by norm_num)
      have h0 : 0 ≤ max 0 (Ea - Ec0l) * F2a := mul_nonneg (le_max_left _ _) (le_trans hdiv hF2p)
      have hneg : Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0)) ≤ 0 :=
        le_of_lt (not_le.mp h)
      have hle0 : (Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0)))
          * (((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg hdiv
      linarith [hle0, h0]
  have h3 : PLl * Wlb / Wupu ≤ Phi L * Wf p / Wf L := by
    have hPLpos : 0 ≤ Phi L := le_trans hPL0 hPL
    have h1' : PLl * Wlb ≤ Phi L * Wf p := by
      have ha : PLl * Wlb ≤ Phi L * Wlb := mul_le_mul_of_nonneg_right hPL hWlb0
      have hb : Phi L * Wlb ≤ Phi L * Wf p := mul_le_mul_of_nonneg_left hWlb hPLpos
      linarith
    have h4 : Wupu⁻¹ ≤ (Wf L)⁻¹ := by
      have h5 : 1 / Wupu ≤ 1 / (Wf L) := one_div_le_one_div_of_le hW0 hWu
      simpa [one_div] using h5
    calc PLl * Wlb / Wupu = (PLl * Wlb) * Wupu⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (Phi L * Wf p) * (Wf L)⁻¹ :=
          mul_le_mul h1' h4 (inv_nonneg.mpr (le_of_lt hWu0))
            (mul_nonneg hPLpos (le_trans hWlb0 hWlb))
      _ = Phi L * Wf p / Wf L := by rw [div_eq_mul_inv]
  have hstr : Phi p - Aref c0 p - Phi L * Wf p / Wf L
      ≤ Ec0u * Ba + max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu := by
    rw [hid]; linarith
  have hfin : max 0 (Phi p - Aref c0 p - Phi L * Wf p / Wf L)
      ≤ max 0 (Ec0u * Ba + max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu) := by
    rw [max_le_iff]
    exact ⟨le_max_left _ _, le_trans hstr (le_max_right _ _)⟩
  have hr' : max 0 (Ec0u * Ba + max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu) ≤ r :=
    max_le hr0 hr
  linarith [hmax, hfin, hr']

lemma Cst2_le {L p c Pc PLl Wlc WLu r : ℝ}
    (hPc : Phi c ≤ Pc) (hPL : PLl ≤ Phi L) (hPL0 : 0 ≤ PLl)
    (hWlc : Wlc ≤ Wf c) (hWlc0 : 0 ≤ Wlc)
    (hWu : Wf L ≤ WLu) (hW0 : 0 < Wf L)
    (hCf : Cf L p ≤ Cf L c) (hr0 : 0 ≤ r)
    (hr : max 0 (Pc - PLl * Wlc / WLu) ≤ r) : Cf L p ≤ r :=
  le_trans hCf (Cf_le hPc hPL hPL0 hWlc hWlc0 hWu hW0 hr0 hr)

end Work.LinnikAreas.A7
