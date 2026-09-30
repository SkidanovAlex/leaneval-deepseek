import Mathlib
import Submission.Work.BMF.VKF.defs
import Submission.Work.BMF.vkford_lemma51
import Submission.Work.BMF.vkford_incomplete_crude
import Submission.Work.BMF.vkford_Wproduct_self
import Submission.Work.BMF.liouville.vmvt_stechkin_small

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bracket of Ford's Lemma 5.1, evaluated

`Work.BMF.VKF.vkf_bracket` evaluates the bracket
`(5r)^k M₂^{-2s} M₁^{-2r+k(k+1)/2} J_{r,k}(M₁) · Jincom_{s,g,h}([1,M₂]) · ∏_{j=h}^{g} W_j`
of Ford's Lemma 5.1 (`Work.BMF.vkford_lemma51`) using

* the sharp Vinogradov–Linnik bound `Work.BMF.liouville.main_sharp`
  (`J_{kr,k}(Q) ≤ stechF k r · Q^{2kr-k(k+1)/2+(k²/2)(1-1/k)^r}`) for both complete systems,
* Ford's (1.9) `Work.BMF.vkford_incomplete_crude` for the incomplete system, and
* the `W`-product bound `Work.BMF.vkford_Wproduct_self`.

With `M₁ = M₂ = M = N^μ`, the powers of `M` cancel exactly and the bracket is at most
`κ · M^{Δ₁+Δ₂} · N^{-H}` with `κ = (5r)^k s^{h-1} 2^{(g+3)(g-h+1)} stechF k r' stechF g s'`,
`Δ₁ = (k²/2)(1-1/k)^{r'}`, `Δ₂ = (g²/2)(1-1/g)^{s'}` and Ford's
`H = Σ_{j=h}^{g} min(jμ, j-λ, λ-j(1-2μ))`.
-/

namespace Work.BMF.VKF

open Finset
open scoped BigOperators
open LeanEval.NumberTheory.VinogradovMeanValue

noncomputable section

set_option maxHeartbeats 1000000

/-- `((h·(h-1)/2 : ℕ) : ℝ) = h(h-1)/2`. -/
private lemma cast_half (h : ℕ) :
    (((h * (h - 1) / 2 : ℕ)) : ℝ) = (h : ℝ) * ((h : ℝ) - 1) / 2 := by
  rcases Nat.even_mul_pred_self h with ⟨m, hm⟩
  have hdiv : h * (h - 1) / 2 = m := by omega
  have hcast : (((h * (h - 1) : ℕ)) : ℝ) = (h : ℝ) * ((h : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0; simp
    · rw [Nat.cast_mul, Nat.cast_pred hpos]
  have hmul : (((h * (h - 1) : ℕ)) : ℝ) = 2 * (m : ℝ) := by rw [hm]; push_cast; ring
  have hm' : (m : ℝ) = (((h * (h - 1) : ℕ)) : ℝ) / 2 := by rw [hmul]; ring
  rw [hdiv, hm', hcast]

/-- **Ford's Lemma 5.1, bracket evaluated.**  With `M₁ = M₂ = M = N^μ`, `r = k·r'`, `s = g·s'`,
`R = (k r' : ℕ)` and `S = (g s' : ℕ)`, the bracket of `Work.BMF.vkford_lemma51` is at most
`(5R)^k S^{h-1} 2^{(g+3)(g-h+1)} stechF k r' stechF g s' · M^{Δ₁+Δ₂} · N^{-H}` with `Δ₁`, `Δ₂`
and `H` as displayed.  (Only the `M`-powers of the four inputs are used; the `N`-power `-H`
is Ford's saving, and the `M₂`-powers cancel exactly.) -/
theorem vkf_bracket (N t : ℝ) (h g k rp sp M : ℕ) (mu lam R S : ℝ)
    (hR : R = ((k * rp : ℕ) : ℝ)) (hS : S = ((g * sp : ℕ) : ℝ))
    (hN : 1 < N) (ht : 1 ≤ t) (hMpos : 0 < (M : ℝ)) (hMpow : (M : ℝ) = N ^ mu)
    (hk : 2 ≤ k) (hrp : 1 ≤ rp) (hsp : 1 ≤ sp) (hM1 : 1 ≤ M)
    (hh : 1 ≤ h) (hhg : h ≤ g) (hgk : g ≤ k) (hg2 : 2 ≤ g)
    (hmu0 : 0 ≤ mu) (hsum : mu + mu < 1)
    (hlam : lam = Real.log t / Real.log N)
    (hr13 : 13 * (g : ℝ) ≤ R) (hs2 : S ≤ (2 : ℝ) ^ g) (hrs : S ≤ R) (hs1 : 1 ≤ S) :
    (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + (k : ℝ) * ((k : ℝ) + 1) / 2)
        * LeanEval.NumberTheory.VinogradovMeanValue.J (k * rp) k M
        * Work.BMF.Jincom (g * sp) g h (Finset.Icc 1 M)
        * ∏ j ∈ Finset.Icc h g, Work.BMF.fordW R S t N (M : ℝ) (M : ℝ) j
      ≤ ((5 * R) ^ k * S ^ (h - 1) * 2 ^ ((g + 3) * (g - h + 1))
          * Work.BMF.liouville.stechF k rp * Work.BMF.liouville.stechF g sp)
        * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ rp
            + (g : ℝ) ^ 2 / 2 * (1 - 1 / (g : ℝ)) ^ sp)
        * N ^ (-(∑ j ∈ Finset.Icc h g,
            min ((j : ℝ) * mu) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - mu - mu))))) := by
  set KK : ℝ := (k : ℝ) * ((k : ℝ) + 1) / 2 with hKK
  set GG : ℝ := (g : ℝ) * ((g : ℝ) + 1) / 2 with hGG
  set D1 : ℝ := (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ rp with hD1
  set D2 : ℝ := (g : ℝ) ^ 2 / 2 * (1 - 1 / (g : ℝ)) ^ sp with hD2
  set EE : ℝ := ((h : ℝ) + (g : ℝ)) * ((g : ℝ) - (h : ℝ) + 1) / 2 with hEE
  set H0 : ℝ := ∑ j ∈ Finset.Icc h g,
      min ((j : ℝ) * mu) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - mu - mu))) with hH0
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := hMpos.le
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  -- the two complete mean values
  have hth1 : Work.BMF.th k rp = 2 * R - KK + D1 := by
    rw [hKK, hD1, Work.BMF.th, hR, Nat.cast_mul]
  have hth2 : Work.BMF.th g sp = 2 * S - GG + D2 := by
    rw [hGG, hD2, Work.BMF.th, hS, Nat.cast_mul]
  have hJ1 : LeanEval.NumberTheory.VinogradovMeanValue.J (k * rp) k M
      ≤ Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1) := by
    refine (Work.BMF.liouville.main_sharp k hk rp hrp M hM1).trans (le_of_eq ?_)
    rw [hth1]
  have hJ2 : LeanEval.NumberTheory.VinogradovMeanValue.J (g * sp) g M
      ≤ Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2) := by
    refine (Work.BMF.liouville.main_sharp g hg2 sp hsp M hM1).trans (le_of_eq ?_)
    rw [hth2]
  -- the incomplete system
  have hs1nat : 1 ≤ g * sp := by
    have h : (1 : ℝ) ≤ ((g * sp : ℕ) : ℝ) := by rw [← hS]; exact hs1
    exact_mod_cast h
  have hJin1 : Work.BMF.Jincom (g * sp) g h (Finset.Icc 1 M)
      ≤ S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
          * LeanEval.NumberTheory.VinogradovMeanValue.J (g * sp) g M := by
    refine (Work.BMF.vkford_incomplete_crude (g * sp) g h M (Finset.Icc 1 M)
      hs1nat hh hhg le_rfl).trans (le_of_eq ?_)
    rw [hS]
  have hJin2 : Work.BMF.Jincom (g * sp) g h (Finset.Icc 1 M)
      ≤ S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
          * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2)) := by
    refine hJin1.trans ?_
    exact mul_le_mul_of_nonneg_left hJ2 (by positivity)
  -- the W product
  have hW := Work.BMF.vkford_Wproduct_self h g hh hhg R S t N (M : ℝ) (M : ℝ) mu mu lam
    hN ht hMpos hMpos hMpow hMpow le_rfl hsum hlam hs1 hr13 hs2 hrs
  have hW' : (∏ j ∈ Finset.Icc h g, Work.BMF.fordW R S t N (M : ℝ) (M : ℝ) j)
      ≤ 2 ^ ((g + 3) * (g - h + 1)) * (M : ℝ) ^ EE * N ^ (-H0) := by
    refine hW.trans (le_of_eq ?_)
    rw [hEE, hH0]
  -- assemble
  have hABC0 : 0 ≤ (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) k) (Real.rpow_nonneg hMnn _))
      (Real.rpow_nonneg hMnn _)
  have hD'0 : 0 ≤ Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1) :=
    mul_nonneg (le_of_lt (Work.BMF.liouville.stechF_pos k rp)) (Real.rpow_nonneg hMnn _)
  have hE0 : 0 ≤ Work.BMF.Jincom (g * sp) g h (Finset.Icc 1 M) := by
    rw [Work.BMF.Jincom]; positivity
  have hE'0 : 0 ≤ S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
      * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2)) :=
    mul_nonneg (mul_nonneg (pow_nonneg hS0 _) (pow_nonneg hMnn _))
      (mul_nonneg (le_of_lt (Work.BMF.liouville.stechF_pos g sp)) (Real.rpow_nonneg hMnn _))
  have hF0 : 0 ≤ ∏ j ∈ Finset.Icc h g, Work.BMF.fordW R S t N (M : ℝ) (M : ℝ) j :=
    Finset.prod_nonneg fun j hj => Work.BMF.fordW_nonneg R S t N (M : ℝ) (M : ℝ) j hR0 hS0
      hMnn hMnn (by linarith) hN0 (le_trans hh (Finset.mem_Icc.mp hj).1)
  have hF'0 : 0 ≤ 2 ^ ((g + 3) * (g - h + 1)) * (M : ℝ) ^ EE * N ^ (-H0) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg hMnn _))
      (Real.rpow_nonneg hN0.le _)
  have hstep :
      (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
        * J (k * rp) k M
        * Work.BMF.Jincom (g * sp) g h (Finset.Icc 1 M)
        * ∏ j ∈ Finset.Icc h g, Work.BMF.fordW R S t N (M : ℝ) (M : ℝ) j
      ≤ (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
        * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1))
        * (S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
            * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2)))
        * (2 ^ ((g + 3) * (g - h + 1)) * (M : ℝ) ^ EE * N ^ (-H0)) := by
    have hm1 : (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK) * J (k * rp) k M
        ≤ (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
          * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1)) :=
      mul_le_mul_of_nonneg_left hJ1 hABC0
    have hm2 : (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
          * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1))
        * Work.BMF.Jincom (g * sp) g h (Finset.Icc 1 M)
        ≤ (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
          * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1))
          * (S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
              * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2))) :=
      mul_le_mul_of_nonneg_left hJin2 (mul_nonneg hABC0 hD'0)
    have hm3 : (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
          * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1))
          * (S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
              * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2)))
        * ∏ j ∈ Finset.Icc h g, Work.BMF.fordW R S t N (M : ℝ) (M : ℝ) j
        ≤ (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
          * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1))
          * (S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
              * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2)))
          * (2 ^ ((g + 3) * (g - h + 1)) * (M : ℝ) ^ EE * N ^ (-H0)) :=
      mul_le_mul_of_nonneg_left hW' (mul_nonneg (mul_nonneg hABC0 hD'0) hE'0)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm1 hE0) hF0).trans
      ((mul_le_mul_of_nonneg_right hm2 hF0).trans hm3)

  -- the powers of `M` combine
  have hpowers :
      (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK) * (M : ℝ) ^ (2 * R - KK + D1)
        * (M : ℝ) ^ (h * (h - 1) / 2) * (M : ℝ) ^ (2 * S - GG + D2) * (M : ℝ) ^ EE
      = (M : ℝ) ^ (D1 + D2) := by
    rw [← Real.rpow_natCast (M : ℝ) (h * (h - 1) / 2)]
    simp only [← Real.rpow_add hMpos]
    congr 1
    rw [cast_half h, hKK, hGG, hD1, hD2, hEE]
    ring
  have hfinal :
      (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
        * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1))
        * (S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
            * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2)))
        * (2 ^ ((g + 3) * (g - h + 1)) * (M : ℝ) ^ EE * N ^ (-H0))
      = ((5 * R) ^ k * S ^ (h - 1) * 2 ^ ((g + 3) * (g - h + 1))
            * Work.BMF.liouville.stechF k rp * Work.BMF.liouville.stechF g sp)
          * (M : ℝ) ^ (D1 + D2) * N ^ (-H0) := by
    calc (5 * R) ^ k * (M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK)
          * (Work.BMF.liouville.stechF k rp * (M : ℝ) ^ (2 * R - KK + D1))
          * (S ^ (h - 1) * (M : ℝ) ^ (h * (h - 1) / 2)
              * (Work.BMF.liouville.stechF g sp * (M : ℝ) ^ (2 * S - GG + D2)))
          * (2 ^ ((g + 3) * (g - h + 1)) * (M : ℝ) ^ EE * N ^ (-H0))
        = ((5 * R) ^ k * S ^ (h - 1) * 2 ^ ((g + 3) * (g - h + 1))
              * Work.BMF.liouville.stechF k rp * Work.BMF.liouville.stechF g sp)
            * ((M : ℝ) ^ (-(2 * S)) * (M : ℝ) ^ (-(2 * R) + KK) * (M : ℝ) ^ (2 * R - KK + D1)
                * (M : ℝ) ^ (h * (h - 1) / 2) * (M : ℝ) ^ (2 * S - GG + D2) * (M : ℝ) ^ EE)
            * N ^ (-H0) := by ac_rfl
      _ = ((5 * R) ^ k * S ^ (h - 1) * 2 ^ ((g + 3) * (g - h + 1))
              * Work.BMF.liouville.stechF k rp * Work.BMF.liouville.stechF g sp)
            * (M : ℝ) ^ (D1 + D2) * N ^ (-H0) := by rw [hpowers]
  exact hstep.trans (le_of_eq hfinal)
end

end Work.BMF.VKF
