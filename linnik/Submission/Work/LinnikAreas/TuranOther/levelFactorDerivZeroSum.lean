import Mathlib
import Submission.Work.LinnikAreas.TuranOther.PFZeroSumDefs
import Submission.Work.LinnikAreas.TuranOther.levelFactorDefs
import Submission.Work.LinnikAreas.TuranOther.levelFactorAux

noncomputable section

open scoped BigOperators Topology
open Filter

namespace Work.LinnikAreas.TuranOther

/-- The change of variable `t - u_n = c^{k+1}·(c(t-u₀) + n)^{-(k+1)}·c^{...}`: more precisely
`(t - u_n)^{-(k+1)} = c^{k+1}·(c·(t-u₀) + n)^{-(k+1)}` with `c = iL/(2π)`. -/
lemma tsub_lvlZero_zpow {p : ℕ} (hL : lvlL p ≠ 0) (a : ℂ) (n : ℤ) (t : ℂ) (k : ℕ) :
    (t - lvlZero p a n) ^ (-(k + 1) : ℤ)
      = (lvlC p) ^ (k + 1) *
          (lvlC p * (t - lvlRoot p a) + (n : ℂ)) ^ (-(k + 1) : ℤ) := by
  rw [sub_lvlZero_eq hL, mul_zpow, inv_zpow, zpow_neg, inv_inv]
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

theorem levelFactorDerivZeroSum {p : ℕ} (hp : p.Prime) (a : ℂ) (ha : ‖a‖ = 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s)) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)) ∧
      iteratedDeriv k (logDeriv (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s))) t =
        (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * Work.LinnikAreas.TuranOther.zeroSumK (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s)) t k := by
  have hL := lvlL_ne_zero hp
  have ha0 : a ≠ 0 := nei_of_norm_eq_one ha
  have hLc : (lvlL p : ℂ) ≠ 0 := by exact_mod_cast hL
  have hc : lvlC p ≠ 0 := lvlC_ne_zero' hL
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- abbreviations
  set z : ℂ := lvlC p * (t - lvlRoot p a) with hzdef
  set Psi : ℂ → ℂ := fun x => Real.pi * Complex.cot (Real.pi * x) with hPsidef
  set S : ℂ := ∑' n : ℤ, (z + (n : ℂ)) ^ (-(k + 1) : ℤ) with hSdef
  -- the statement's function is `lvlE p a`
  have hfeq : (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s)) = lvlE p a := (lvlE_eq hp a).symm
  -- `z` lies in the upper half plane
  have hzmem : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
    rw [hzdef]
    exact lvlC_mul_im_pos hp ha ht
  have hzim : 0 < z.im := hzmem
  -- `Psi` is analytic at `z`
  have hzexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) ≠ 1 := by
    have hlt := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hzim⟩
    intro hh
    rw [hh, norm_one] at hlt
    exact lt_irrefl 1 hlt
  have hPsi_an : AnalyticAt ℂ Psi z := by
    rw [hPsidef]
    have h_eq : (fun x : ℂ => Real.pi * Complex.cot (Real.pi * x))
        = fun x => Real.pi * ((Complex.exp (2 * Real.pi * Complex.I * x) + 1)
            / (Complex.I * (1 - Complex.exp (2 * Real.pi * Complex.I * x)))) := by
      funext x; rw [Complex.cot_pi_eq_exp_ratio]
    rw [h_eq]
    refine AnalyticAt.mul (analyticAt_const) ?_
    refine AnalyticAt.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · rw [mul_ne_zero_iff]
      exact ⟨Complex.I_ne_zero, sub_ne_zero.mpr hzexp.symm⟩
  -- the cotangent lattice identity in terms of `S`
  have hPsi : iteratedDeriv k Psi z = (-1) ^ k * (k.factorial : ℂ) * S := by
    rw [hPsidef]
    rw [← (iteratedDerivWithin_of_isOpen (n := k)
          (f := fun x : ℂ => Real.pi * Complex.cot (Real.pi * x))
          UpperHalfPlane.isOpen_upperHalfPlaneSet) hzmem,
        iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := k) hk hzmem, hSdef]
    congr 1
    refine tsum_congr (fun n => ?_)
    rw [zpow_neg]
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring]
    rw [zpow_natCast, inv_eq_one_div]
  -- summability of the lattice series
  have hsumZ : Summable (fun n : ℤ => (z + (n : ℂ)) ^ (-(k + 1) : ℤ)) :=
    summable_int_add_zpow (z := z) (k := k) hk
  -- the summed function is supported on the lattice
  have hsupp : ∀ u : ℂ, (∀ n : ℤ, u ≠ lvlZero p a n) →
      ((analyticOrderNatAt (lvlE p a) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ) = 0 := by
    intro u hu
    have hne : lvlE p a u ≠ 0 := by
      intro h0
      obtain ⟨n, hn⟩ := (lvlE_zero_iff hp a ha u).mp h0
      exact hu n hn
    have h0 : analyticOrderNatAt (lvlE p a) u = 0 := by
      have hh := (analyticAt_lvlE p a u).analyticOrderAt_eq_zero.mpr hne
      rw [analyticOrderNatAt, hh]
      rfl
    rw [h0]; simp
  have hfn : ∀ n : ℤ,
      ((analyticOrderNatAt (lvlE p a) (lvlZero p a n) : ℕ) : ℂ)
          * (t - lvlZero p a n) ^ (-(k + 1) : ℤ)
        = (lvlC p) ^ (k + 1) * (z + (n : ℂ)) ^ (-(k + 1) : ℤ) := by
    intro n
    rw [analyticOrderNatAt_lvlE_lvlZero hp a ha n, Nat.cast_one, one_mul]
    rw [hzdef]
    exact tsub_lvlZero_zpow hL a n t k
  have hfsum : Summable (fun n : ℤ =>
      ((analyticOrderNatAt (lvlE p a) (lvlZero p a n) : ℕ) : ℂ)
        * (t - lvlZero p a n) ^ (-(k + 1) : ℤ)) :=
    (hsumZ.mul_left ((lvlC p) ^ (k + 1))).congr (fun n => (hfn n).symm)
  obtain ⟨hSummE, htsumE⟩ := tsum_eq_tsum_of_supported (φ := lvlZero p a)
      (f := fun u : ℂ =>
        ((analyticOrderNatAt (lvlE p a) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
      (lvlZero_injective hL a) hsupp hfsum
  -- value of the zero sum
  have hzero : zeroSumK (lvlE p a) t k = (lvlC p) ^ (k + 1) * S := by
    rw [zeroSumK, htsumE, hSdef, tsum_congr hfn, tsum_mul_left]
  -- derivative of `logDeriv (lvlE p a)`
  have hev : logDeriv (lvlE p a) =ᶠ[𝓝 t]
      (fun s : ℂ => lvlC p * Psi (lvlC p * (s - lvlRoot p a)) - (lvlL p : ℂ) / 2) := by
    have ht_val : ‖a * Complex.exp (-((lvlL p : ℂ) * t))‖ < 1 := by
      rw [norm_mul, ha, one_mul, Complex.norm_exp]
      rw [show (-((lvlL p : ℂ) * t)).re = -(lvlL p * t.re) by
        rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero]]
      rw [Real.exp_lt_one_iff]
      have := lvlL_pos hp
      nlinarith [ht]
    have hcont : Continuous (fun s : ℂ => ‖a * Complex.exp (-((lvlL p : ℂ) * s))‖) := by
      fun_prop
    filter_upwards [hcont.continuousAt.eventually (isOpen_Iio.mem_nhds ht_val)] with s hs
    rw [hPsidef]
    refine logDeriv_lvlE hp a ha s ?_
    intro h0
    rw [lvlE_apply] at h0
    have h1 : a * Complex.exp (-((lvlL p : ℂ) * s)) = 1 := by
      have := sub_eq_zero.mp h0; rw [eq_comm] at this; exact this
    rw [h1, norm_one] at hs
    exact absurd hs (lt_irrefl 1)
  have hchain : iteratedDeriv k (fun s : ℂ => Psi (lvlC p * (s - lvlRoot p a))) t
      = (lvlC p) ^ k * iteratedDeriv k Psi z := by
    have hPsi_an' : AnalyticAt ℂ Psi (lvlC p * t + (-(lvlC p * lvlRoot p a))) := by
      rw [show lvlC p * t + (-(lvlC p * lvlRoot p a)) = z by rw [hzdef]; ring]
      exact hPsi_an
    rw [show (fun s : ℂ => Psi (lvlC p * (s - lvlRoot p a)))
          = (fun s : ℂ => Psi (lvlC p * s + (-(lvlC p * lvlRoot p a)))) by
        funext s; ring_nf]
    rw [iteratedDeriv_comp_const_mul_add (c := lvlC p) (b := -(lvlC p * lvlRoot p a))
      (x := t) (n := k) hPsi_an']
    rw [show lvlC p * t + (-(lvlC p * lvlRoot p a)) = z by rw [hzdef]; ring]
  have hlog : iteratedDeriv k (logDeriv (lvlE p a)) t
      = lvlC p * iteratedDeriv k (fun s : ℂ => Psi (lvlC p * (s - lvlRoot p a))) t := by
    rw [hev.iteratedDeriv_eq k]
    rw [show (fun s : ℂ => lvlC p * Psi (lvlC p * (s - lvlRoot p a)) - (lvlL p : ℂ) / 2)
          = fun s : ℂ =>
              -((lvlL p : ℂ) / 2 - lvlC p * Psi (lvlC p * (s - lvlRoot p a))) by
        funext s; ring]
    rw [iteratedDeriv_fun_neg,
      iteratedDeriv_const_sub (x := t) (by omega : 0 < k) ((lvlL p : ℂ) / 2)]
    simp only [Pi.neg_def]
    rw [iteratedDeriv_fun_neg, iteratedDeriv_const_mul_field (lvlC p)]
    ring
  have hLHS : iteratedDeriv k (logDeriv (lvlE p a)) t
      = (lvlC p) ^ (k + 1) * iteratedDeriv k Psi z := by
    rw [hlog, hchain]; ring
  have hkey : (-1 : ℂ) ^ k * (k.factorial : ℂ) * zeroSumK (lvlE p a) t k
      = (lvlC p) ^ (k + 1) * iteratedDeriv k Psi z := by
    rw [hzero, hPsi]; ring
  refine ⟨?_, ?_⟩
  · rw [hfeq]; exact hSummE
  · rw [hfeq, hLHS, ← hkey]

end Work.LinnikAreas.TuranOther
