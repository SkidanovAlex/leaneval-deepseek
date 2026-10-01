import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount

namespace Work.ZeroFreeTables.P9.prim

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- **Pointwise near/far bound.**  Outside the near-disk `‖1 + i·Im s - u‖ ≤ δ`, the real part
of `(1/(s-u))³` is bounded below by `-C/(1+‖s-u‖²)` with `C = (2/δ)(1+4/δ²)`; inside the disk the
indicator `1 - nearInd` vanishes.  Since `1 ≤ Re s ≤ 1 + δ/2`, the two points `u` and `1 + i·Im s`
are controlled through `‖s - u‖ > δ/2`. -/
private lemma farNearInd_re_bound {s u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s.re)
    (hsδ : s.re ≤ 1 + δ / 2) :
    |(1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re|
      ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) := by
  classical
  by_cases hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · have hni : Work.ZeroFreeTables.P9.nearInd s δ u = 1 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hnear]
    rw [hni, sub_self, zero_mul, abs_zero]
    positivity
  · have hni : Work.ZeroFreeTables.P9.nearInd s δ u = 0 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hnear]
    rw [hni, sub_zero, one_mul]
    have hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hnear
    have hre1 : |s.re - 1| ≤ δ / 2 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hdecomp : s - u
        = ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) + ((s.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have hc : ‖((s.re - 1 : ℝ) : ℂ)‖ = |s.re - 1| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have htri : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖
        ≤ ‖((1 : ℂ) + (s.im : ℂ) * Complex.I - u) + ((s.re - 1 : ℝ) : ℂ)‖
          + ‖((s.re - 1 : ℝ) : ℂ)‖ := by
      have h := norm_sub_le (((1 : ℂ) + (s.im : ℂ) * Complex.I - u) + ((s.re - 1 : ℝ) : ℂ))
        (((s.re - 1 : ℝ) : ℂ))
      rwa [add_sub_cancel_right] at h
    have hr : δ / 2 < ‖s - u‖ := by
      rw [hdecomp]; linarith
    have hrpos : 0 < ‖s - u‖ := by linarith
    have hnorm3 : ‖(1 / (s - u)) ^ 3‖ = (1 / ‖s - u‖) ^ 3 := by
      rw [norm_pow, norm_div, norm_one]
    have hre : |((1 / (s - u)) ^ 3).re| ≤ (1 / ‖s - u‖) ^ 3 :=
      (Complex.abs_re_le_norm _).trans_eq hnorm3
    have hlt1 : 1 / ‖s - u‖ < 2 / δ := by
      have h := one_div_lt_one_div_of_lt (show (0:ℝ) < δ / 2 by linarith) hr
      rwa [one_div_div] at h
    have hlt3 : 1 / ‖s - u‖ ^ 3 < 8 / δ ^ 3 := by
      have hpow : (δ / 2) ^ 3 < ‖s - u‖ ^ 3 :=
        pow_lt_pow_left₀ hr (by linarith : (0:ℝ) ≤ δ / 2) (by norm_num)
      have h := one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < (δ / 2) ^ 3) hpow
      have heq : (1:ℝ) / (δ / 2) ^ 3 = 8 / δ ^ 3 := by field_simp; ring
      rwa [heq] at h
    have hkey : (1 / ‖s - u‖) ^ 3
        ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) := by
      have hC : (2 / δ) * (1 + 4 / δ ^ 2) = 2 / δ + 8 / δ ^ 3 := by field_simp; ring
      rw [hC, div_pow, one_pow, mul_one_div,
        le_div_iff₀ (by positivity : (0:ℝ) < 1 + ‖s - u‖ ^ 2)]
      have heq : (1:ℝ) / ‖s - u‖ ^ 3 * (1 + ‖s - u‖ ^ 2) = 1 / ‖s - u‖ ^ 3 + 1 / ‖s - u‖ := by
        field_simp [ne_of_gt hrpos]
      rw [heq]; linarith
    exact hre.trans hkey

/-- The multiplicity-weighted inverse-square kernel over the zeros of a primitive non-principal
Dirichlet `L`-function is summable.  This is the summability half of
`Work.ZeroFreeTables.P9.zeroSum_invSq_tsum`: the uniform ball count of `Λ(·,χ)` turned into a
finite-set bound for the Poisson kernel. -/
private lemma invSqSum_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (s : ℂ) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
  obtain ⟨c, hcpos, hc⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count hcpos.le
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    exact Real.log_nonneg hN1
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hfin : ∀ S : Finset ℂ, ∑ u ∈ S,
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))
      ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := by
    intro S
    exact hC (DirichletCharacter.completedLFunction χ) hΛan (Real.log (N : ℝ)) hlogN
      (fun a ρ hρ => hc χ hχ hprim a ρ hρ) s S
  have hnn : ∀ u : ℂ, 0 ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
      * (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    have : (0 : ℝ) ≤ 1 / (1 + ‖s - u‖ ^ 2) := by positivity
    positivity
  have hsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))) :=
    summable_of_sum_le hnn hfin
  exact hsumm.congr (fun u => by
    rw [← Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u])

theorem cubicNearFar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 1 < s.re) (hsδ : s.re ≤ 1 + δ / 2) (hsum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)) : -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re ≤ -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 3).re) + (2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s := by
  classical
  -- summability of the real part of the complex summand
  have hRf : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 3).re) := by
    have h1 : Summable (fun u : ℂ =>
        ((Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re) :=
      Summable.of_norm_bounded hsum.norm
        (fun u => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
    exact h1.congr (fun u => by simp [Complex.mul_re])
  have hTsum : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 3).re)
      = (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_congr (fun u => by simp [Complex.mul_re])
  -- summability of the inverse-square kernel
  have hK : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) :=
    invSqSum_summable χ hχ hprim s
  -- the far part
  have hHnorm : ∀ u : ℂ,
      ‖(Work.LinnikContract.zeroMult χ u : ℝ) * (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
          * ((1 / (s - u)) ^ 3).re‖
        ≤ (2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
    intro u
    have hb := farNearInd_re_bound hδ hs.le hsδ (u := u)
    have ha : 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := Nat.cast_nonneg _
    have hN : ‖(Work.LinnikContract.zeroMult χ u : ℝ)
          * (1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re‖
        = (Work.LinnikContract.zeroMult χ u : ℝ)
          * |(1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re| := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
      ring
    rw [hN]
    calc (Work.LinnikContract.zeroMult χ u : ℝ)
          * |(1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re|
        ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
          * ((2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hb ha
      _ = (2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by ring
  have hH : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
        * ((1 / (s - u)) ^ 3).re) :=
    Summable.of_norm_bounded (hK.mul_left ((2 / δ) * (1 + 4 / δ ^ 2))) hHnorm
  -- the near part is the real part minus the far part
  have hG : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u
        * ((1 / (s - u)) ^ 3).re) :=
    (hRf.sub hH).congr (fun u => by ring)
  have hG_eq : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 3).re)
      = (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 3).re)
        - (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re) := by
    rw [← Summable.tsum_sub hRf hH]
    exact tsum_congr (fun u => by ring)
  -- lower bound on the far part
  have hHlow : -((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s)
      ≤ (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
          * (1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re) := by
    have hle : ∀ u : ℂ, -((2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))))
        ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
          * ((1 / (s - u)) ^ 3).re := by
      intro u
      have hb := farNearInd_re_bound hδ hs.le hsδ (u := u)
      have ha : 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := Nat.cast_nonneg _
      have hx : -|(1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re|
          ≤ (1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re := neg_abs_le _
      have h1 : (Work.LinnikContract.zeroMult χ u : ℝ)
            * (-|(1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re|)
          ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * ((1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re) :=
        mul_le_mul_of_nonneg_left hx ha
      have h2 : (Work.LinnikContract.zeroMult χ u : ℝ)
            * |(1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re|
          ≤ (2 / δ) * (1 + 4 / δ ^ 2)
            * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
        calc (Work.LinnikContract.zeroMult χ u : ℝ)
              * |(1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re|
            ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
              * ((2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2))) :=
              mul_le_mul_of_nonneg_left hb ha
          _ = (2 / δ) * (1 + 4 / δ ^ 2)
              * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by ring
      nlinarith [h1, h2]
    have hsumneg : Summable (fun u : ℂ => -((2 / δ) * (1 + 4 / δ ^ 2)
        * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))))) :=
      (hK.mul_left ((2 / δ) * (1 + 4 / δ ^ 2))).neg
    have h2 := Summable.tsum_le_tsum hle hsumneg hH
    have e1 : (∑' u : ℂ, -((2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))))
        = -((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s) := by
      rw [tsum_neg, tsum_mul_left]
      rfl
    rwa [e1] at h2
  -- assemble
  have hfin : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 3).re)
      - (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re
      ≤ (2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s := by
    have e : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
          * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 3).re)
        - (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re
        = -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (1 - Work.ZeroFreeTables.P9.nearInd s δ u) * ((1 / (s - u)) ^ 3).re) := by
      rw [hG_eq, hTsum]; ring
    rw [e]; linarith [hHlow]
  linarith [hfin]

end Work.ZeroFreeTables.P9.prim
