/-
# Area 7 — the refinement term `Aref2` (χ₁ real, ρ₁ complex)

When χ₁ is a real character and ρ₁ is non-real, HB §15 uses the *doubled* refinement term

  `A₂ = (e^{-aλ} - e^{-ac})(B(λ) - 2K⁻²F₂(λ))`

because then both ρ₁ and its conjugate (with the same λ) are zeros of χ₁.  This file provides the
definition `Aref2`, its basic identity, its non-negativity for `λ ≤ c`, and the arithmetic lemma
`Cst1_le2` (the analogue of `ValueLemmas.Cst1_le`) turning rational enclosures at `λ, c, Λ` into an
upper bound for `Cf Λ λ - Aref2 c λ`.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.ValueLemmas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

/-- `A₂ = (e^{-aλ} - e^{-ac})(B(3/10,λ) - 2K⁻²F₂(λ))`. -/
def Aref2 (c lam : ℝ) : ℝ :=
  (Real.exp (-(ac * lam)) - Real.exp (-(ac * c))) *
    (Bfun Kc lam - 2 * ((1 - Real.exp (-(Kc * lam))) / lam) ^ 2 / K2)

/-- The rewritten form used in the estimates. -/
lemma Aref2_identity {c p : ℝ} (hp : p ≠ 0) :
    Phi p - Aref2 c p = Real.exp (-(ac * c)) * Bfun Kc p
      + 2 * (Real.exp (-(ac * p)) - Real.exp (-(ac * c))) *
          (((1 - Real.exp (-(Kc * p))) / p) ^ 2 / K2) := by
  rw [Aref2, Phi]
  ring

/-- `Aref2 c p ≥ 0` when `p ≤ c`. -/
lemma Aref2_nonneg {c p : ℝ} (hpc : p ≤ c)
    (hBF : 2 * ((1 - Real.exp (-(Kc * p))) / p) ^ 2 / K2 ≤ Bfun Kc p) : 0 ≤ Aref2 c p := by
  have hac : (0:ℝ) < ac := by norm_num [ac]
  rw [Aref2]
  apply mul_nonneg _ (by linarith)
  rw [sub_nonneg]
  exact Real.exp_le_exp.mpr (by nlinarith [hac])

/-- The `α = 2` analogue of `ValueLemmas.Cst1_le`:
`Cf L p - Aref2 c0 p ≤ r` from rational enclosures of `e^{-a·}`, `B(3/10,·)` and `K⁻²F₂` at `p`,
`c0` and `L`. -/
lemma Cst1_le2 {L c0 p a b Ec0u Ec0l Ea Ba F2a PLl Wlb Wupu r : ℝ}
    (hp : 0 < p) (hpc : p ≤ c0) (hBF : 2*((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) p)
    (hEc0u : Real.exp (-((49:ℝ)/10*c0)) ≤ Ec0u) (hEc0l : Ec0l ≤ Real.exp (-((49:ℝ)/10*c0)))
    (hEa : Real.exp (-((49:ℝ)/10*a)) ≤ Ea) (hBa : Bfun ((3:ℝ)/10) a ≤ Ba)
    (hF2a : ((1-Real.exp (-((3:ℝ)/10*a)))/a)^2/((9:ℝ)/100) ≤ F2a)
    (hEp : Real.exp (-((49:ℝ)/10*p)) ≤ Ea) (hBp : Bfun ((3:ℝ)/10) p ≤ Ba)
    (hF2p : ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ F2a)
    (hPL : PLl ≤ Phi L) (hPL0 : 0 ≤ PLl) (hWlb : Wlb ≤ Wf p) (hWlb0 : 0 ≤ Wlb)
    (hWu : Wf L ≤ Wupu) (hWu0 : 0 < Wupu) (hW0 : 0 < Wf L) (hr0 : 0 ≤ r)
    (hr : Ec0u * Ba + 2 * max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu ≤ r) :
    Cf L p - Aref2 c0 p ≤ r := by
  have hA0 : 0 ≤ Aref2 c0 p := Aref2_nonneg hpc hBF
  have hmax : Cf L p - Aref2 c0 p ≤ max 0 (Phi p - Aref2 c0 p - Phi L * Wf p / Wf L) := by
    rw [Cf]
    by_cases h : Phi p - Phi L * Wf p / Wf L ≤ 0
    · have hC : max 0 (Phi p - Phi L * Wf p / Wf L) = 0 := max_eq_left h
      rw [hC]
      have h1 : (0:ℝ) ≤ max 0 (Phi p - Aref2 c0 p - Phi L * Wf p / Wf L) := le_max_left _ _
      linarith
    · have hpos : 0 < Phi p - Phi L * Wf p / Wf L := not_le.mp h
      have hC : max 0 (Phi p - Phi L * Wf p / Wf L) = Phi p - Phi L * Wf p / Wf L :=
        max_eq_right hpos.le
      rw [hC]
      have h1 : Phi p - Phi L * Wf p / Wf L - Aref2 c0 p
          ≤ max 0 (Phi p - Aref2 c0 p - Phi L * Wf p / Wf L) := by
        have h2 := le_max_right (0:ℝ) (Phi p - Aref2 c0 p - Phi L * Wf p / Wf L)
        linarith
      linarith
  have hid : Phi p - Aref2 c0 p - Phi L * Wf p / Wf L
      = Real.exp (-((49:ℝ)/10*c0)) * Bfun ((3:ℝ)/10) p
        + 2 * (Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0)))
            * (((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100))
        - Phi L * Wf p / Wf L := by
    rw [Aref2, Phi, Kc_eq, K2_eq, ac_eq]; ring
  have hBp0 : (0:ℝ) ≤ Bfun ((3:ℝ)/10) p :=
    (Work.LinnikContract.API.Bfun_pos (K := (3:ℝ)/10) (lam := p) (by norm_num) hp).le
  have h1 : Real.exp (-((49:ℝ)/10*c0)) * Bfun ((3:ℝ)/10) p ≤ Ec0u * Ba :=
    mul_le_mul hEc0u hBp hBp0 (le_trans (Real.exp_pos _).le hEc0u)
  have h2 : 2 * (Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0)))
        * (((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100))
      ≤ 2 * max 0 (Ea - Ec0l) * F2a := by
    have h2' : (Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0)))
        * (((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100))
        ≤ max 0 (Ea - Ec0l) * F2a := by
      by_cases h : 0 ≤ Real.exp (-((49:ℝ)/10*p)) - Real.exp (-((49:ℝ)/10*c0))
      · have hle : max 0 (Ea - Ec0l) = Ea - Ec0l := by apply max_eq_right; linarith
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
    linarith
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
  have hstr : Phi p - Aref2 c0 p - Phi L * Wf p / Wf L
      ≤ Ec0u * Ba + 2 * max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu := by
    rw [hid]; linarith
  have hfin : max 0 (Phi p - Aref2 c0 p - Phi L * Wf p / Wf L)
      ≤ max 0 (Ec0u * Ba + 2 * max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu) := by
    rw [max_le_iff]
    exact ⟨le_max_left _ _, le_trans hstr (le_max_right _ _)⟩
  have hr' : max 0 (Ec0u * Ba + 2 * max 0 (Ea - Ec0l) * F2a - PLl * Wlb / Wupu) ≤ r :=
    max_le hr0 hr
  linarith [hmax, hfin, hr']

end Work.LinnikAreas.A7
