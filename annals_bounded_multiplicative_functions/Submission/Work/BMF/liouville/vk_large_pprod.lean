import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs
import Submission.Work.BMF.vkford_lemma51
import Submission.Work.BMF.vkford_incomplete_crude
import Submission.Work.BMF.vkford_Wproduct_self

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Substitution into Ford's `Pprod`

The bound on `Work.BMF.Pprod` obtained from the two Stechkin inputs (`main_sharp`), Ford's crude
incomplete-system bound (`vkford_incomplete_crude`) and the `W`-product bound
(`vkford_Wproduct_self`): the `M₂`-powers cancel and the `M = M₁ = M₂` power is exactly `dDelta`.
-/

namespace Work.BMF.liouville

open Finset
open scoped BigOperators

noncomputable section

/-- Merging six powers of the same base. -/
lemma rpow_six {x : ℝ} (hx : 0 < x) (a b c d e f : ℝ) :
    x ^ a * x ^ b * x ^ c * x ^ d * x ^ e * x ^ f = x ^ (a + b + c + d + e + f) := by
  conv_lhs => rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx,
    ← Real.rpow_add hx, ← Real.rpow_add hx]

/-- `(n(n-1)/2 : ℕ)` cast to `ℝ` is `n(n-1)/2`. -/
lemma cast_mul_pred_div_two (n : ℕ) :
    ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have hdvd : (2 : ℕ) ∣ n * (n - 1) := by
      obtain ⟨k, hk⟩ := Nat.even_mul_pred_self n
      exact ⟨k, by omega⟩
    rw [Nat.cast_div hdvd (by norm_num : ((2 : ℕ) : ℝ) ≠ 0)]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring

/-- The elementary algebra identity behind the cancellation of the `M₂`-powers. -/
lemma bracket_zero (h g : ℕ) :
    (h : ℝ) * ((h : ℝ) - 1) / 2 - (g : ℝ) * ((g : ℝ) + 1) / 2
      + ((h : ℝ) + (g : ℝ)) * ((g : ℝ) - (h : ℝ) + 1) / 2 = 0 := by ring

/-- The total exponent of `M = M₁ = M₂` that survives after substituting the two Stechkin
bounds, Ford's crude incomplete-system bound and the `W`-product bound into `Pprod` is exactly
`dDelta lam`. -/
lemma dDelta_eq_exponent (lam : ℝ) :
    Work.BMF.th (dK lam) (dRp lam) + Work.BMF.th (dG lam) (dSp lam)
      - 2 * (dR lam : ℝ) - 2 * (dS lam : ℝ)
      + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2
      + (dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2
      + ((dH lam : ℝ) + (dG lam : ℝ)) * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2
    = dDelta lam := by
  have hr : (dR lam : ℝ) = (dK lam : ℝ) * (dRp lam : ℝ) := by rw [dR, Nat.cast_mul]
  have hs : (dS lam : ℝ) = (dG lam : ℝ) * (dSp lam : ℝ) := by rw [dS, Nat.cast_mul]
  rw [Work.BMF.th, Work.BMF.th, dDelta]
  have hb := bracket_zero (dH lam) (dG lam)
  nlinarith [hb, hr, hs]

/-- **Substitution into `Pprod`.**  Under the standing hypotheses, `Pprod` is bounded by
`dC0 lam · M^{dDelta lam} · N^{-H}`. -/
lemma Pprod_le_C0 (lam : ℝ) (N t : ℝ) (hNr : 1 < N) (ht : 1 ≤ t)
    (hMpos : 0 < (dM N : ℝ)) (hM1 : 1 ≤ dM N)
    (hlam : lam = Real.log t / Real.log N)
    (h2μ : 2 * dMu N < 1)
    (hk : 2 ≤ dK lam) (hrp : 1 ≤ dRp lam) (hg : 2 ≤ dG lam) (hsp : 1 ≤ dSp lam)
    (hh : 1 ≤ dH lam) (hhg : dH lam ≤ dG lam)
    (hs1 : (1 : ℝ) ≤ (dS lam : ℝ)) (hr13 : 13 * (dG lam : ℝ) ≤ (dR lam : ℝ))
    (hs2 : (dS lam : ℝ) ≤ (2 : ℝ) ^ (dG lam)) (hrs : (dS lam : ℝ) ≤ (dR lam : ℝ)) :
    Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N)
      ≤ dC0 lam * (dM N : ℝ) ^ (dDelta lam)
        * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) := by
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hNr
  have hlogNd : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hNr)
  have hMμ : (dM N : ℝ) = N ^ (dMu N) := by
    rw [dMu, Real.rpow_def_of_pos hNpos]
    rw [show Real.log N * (Real.log (dM N) / Real.log N) = Real.log (dM N) from
      mul_div_cancel₀ _ hlogNd, Real.exp_log hMpos]
  have hSFv : 0 ≤ stechF (dK lam) (dRp lam) := (stechF_pos _ _).le
  have hSFw : 0 ≤ stechF (dG lam) (dSp lam) := (stechF_pos _ _).le
  have hMp : ∀ e : ℝ, (0 : ℝ) ≤ (dM N : ℝ) ^ e := fun e => Real.rpow_nonneg hMpos.le e
  -- (1) the Stechkin bound for `J r k M`
  have hvJ : LeanEval.NumberTheory.VinogradovMeanValue.J (dR lam) (dK lam) (dM N)
      ≤ stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)) := by
    have h := main_sharp (dK lam) hk (dRp lam) hrp (dM N) hM1
    simpa only [dR] using h
  -- (2) Ford's crude incomplete-system bound, followed by Stechkin at `(g, s')`
  have hIn : Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N))
      ≤ (dS lam : ℝ) ^ (dH lam - 1)
        * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
        * (stechF (dG lam) (dSp lam)
            * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))) := by
    have h1 := Work.BMF.vkford_incomplete_crude (dS lam) (dG lam) (dH lam) (dM N)
      (Icc 1 (dM N)) (by exact_mod_cast hs1) hh hhg (le_refl _)
    rw [← Real.rpow_natCast (dM N : ℝ) (dH lam * (dH lam - 1) / 2),
        cast_mul_pred_div_two (dH lam)] at h1
    have h2 : LeanEval.NumberTheory.VinogradovMeanValue.J (dS lam) (dG lam) (dM N)
        ≤ stechF (dG lam) (dSp lam) * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam)) := by
      have h := main_sharp (dG lam) hg (dSp lam) hsp (dM N) hM1
      simpa only [dS] using h
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- (3) the `W`-product bound
  have hW : (∏ j ∈ Icc (dH lam) (dG lam),
        Work.BMF.fordW (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) j)
      ≤ (2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1))
        * (dM N : ℝ) ^ (((dH lam : ℝ) + (dG lam : ℝ)) * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2)
        * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) := by
    have h := Work.BMF.vkford_Wproduct_self (dH lam) (dG lam) hh hhg
      (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) (dMu N) (dMu N) lam
      hNr ht hMpos hMpos hMμ hMμ (le_refl _) (by linarith [h2μ]) hlam hs1 hr13 hs2 hrs
    simpa only [dHsum] using h
  -- positivity
  have hA0nn : 0 ≤ (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
      * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2) := by
    positivity
  have hVnn : 0 ≤ stechF (dK lam) (dRp lam)
      * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)) := mul_nonneg hSFv (hMp _)
  have hInnn : 0 ≤ (dS lam : ℝ) ^ (dH lam - 1)
      * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
      * (stechF (dG lam) (dSp lam)
          * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))) :=
    mul_nonneg (mul_nonneg (by positivity) (hMp _)) (mul_nonneg hSFw (hMp _))
  have hJinnn : 0 ≤ Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N)) := by
    rw [Work.BMF.Jincom]; exact Nat.cast_nonneg _
  have hWoriNN : 0 ≤ ∏ j ∈ Icc (dH lam) (dG lam),
      Work.BMF.fordW (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) j :=
    Finset.prod_nonneg (fun j hj => Work.BMF.fordW_nonneg _ _ t N _ _ j
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by linarith) hNpos (le_trans hh (Finset.mem_Icc.mp hj).1))
  rw [Work.BMF.Pprod]
  -- (4) monotonicity in the three bounded factors
  have hstep1 : (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * LeanEval.NumberTheory.VinogradovMeanValue.J (dR lam) (dK lam) (dM N)
        * Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N))
        * ∏ j ∈ Icc (dH lam) (dG lam),
            Work.BMF.fordW (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) j
      ≤ (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N))
        * ∏ j ∈ Icc (dH lam) (dG lam),
            Work.BMF.fordW (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) j := by
    have h2 : (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * LeanEval.NumberTheory.VinogradovMeanValue.J (dR lam) (dK lam) (dM N)
        ≤ (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam))) :=
      mul_le_mul_of_nonneg_left hvJ hA0nn
    have h3 : (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * LeanEval.NumberTheory.VinogradovMeanValue.J (dR lam) (dK lam) (dM N)
        * Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N))
        ≤ (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N)) :=
      mul_le_mul_of_nonneg_right h2 hJinnn
    exact mul_le_mul_of_nonneg_right h3 hWoriNN
  have hstep2 : (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N))
        * ∏ j ∈ Icc (dH lam) (dG lam),
            Work.BMF.fordW (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) j
      ≤ (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * ((dS lam : ℝ) ^ (dH lam - 1)
            * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
            * (stechF (dG lam) (dSp lam)
                * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))))
        * ∏ j ∈ Icc (dH lam) (dG lam),
            Work.BMF.fordW (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) j := by
    have h2 : (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Icc 1 (dM N))
        ≤ (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * ((dS lam : ℝ) ^ (dH lam - 1)
            * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
            * (stechF (dG lam) (dSp lam)
                * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam)))) :=
      mul_le_mul_of_nonneg_left hIn (mul_nonneg hA0nn hVnn)
    exact mul_le_mul_of_nonneg_right h2 hWoriNN
  have hstep3 : (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * ((dS lam : ℝ) ^ (dH lam - 1)
            * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
            * (stechF (dG lam) (dSp lam)
                * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))))
        * ∏ j ∈ Icc (dH lam) (dG lam),
            Work.BMF.fordW (dR lam : ℝ) (dS lam : ℝ) t N (dM N : ℝ) (dM N : ℝ) j
      ≤ (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * ((dS lam : ℝ) ^ (dH lam - 1)
            * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
            * (stechF (dG lam) (dSp lam)
                * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))))
        * ((2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1))
            * (dM N : ℝ) ^ (((dH lam : ℝ) + (dG lam : ℝ))
                * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2)
            * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam))) :=
    mul_le_mul_of_nonneg_left hW (mul_nonneg (mul_nonneg hA0nn hVnn) hInnn)
  have hfinal := le_trans hstep1 (le_trans hstep2 hstep3)
  -- (5) collapse the product
  have hE : (-(2 * (dS lam : ℝ)))
      + (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
      + (Work.BMF.th (dK lam) (dRp lam)) + ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
      + (Work.BMF.th (dG lam) (dSp lam))
      + (((dH lam : ℝ) + (dG lam : ℝ)) * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2)
      = dDelta lam := by
    have h := dDelta_eq_exponent lam
    linarith [h]
  have hMmerge : (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
      * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
      * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam))
      * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
      * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))
      * (dM N : ℝ) ^ (((dH lam : ℝ) + (dG lam : ℝ)) * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2)
      = (dM N : ℝ) ^ (dDelta lam) := by
    rw [rpow_six hMpos (-(2 * (dS lam : ℝ)))
      (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
      (Work.BMF.th (dK lam) (dRp lam)) ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
      (Work.BMF.th (dG lam) (dSp lam))
      (((dH lam : ℝ) + (dG lam : ℝ)) * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2)]
    rw [hE]
  have hrearr : (5 * (dR lam : ℝ)) ^ (dK lam) * (dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
        * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
        * (stechF (dK lam) (dRp lam) * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam)))
        * ((dS lam : ℝ) ^ (dH lam - 1)
            * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
            * (stechF (dG lam) (dSp lam)
                * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))))
        * ((2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1))
            * (dM N : ℝ) ^ (((dH lam : ℝ) + (dG lam : ℝ))
                * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2)
            * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)))
      = (5 * (dR lam : ℝ)) ^ (dK lam) * (dS lam : ℝ) ^ (dH lam - 1)
        * stechF (dK lam) (dRp lam) * stechF (dG lam) (dSp lam)
        * (2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1))
        * ((dM N : ℝ) ^ (-(2 * (dS lam : ℝ)))
            * (dM N : ℝ) ^ (-(2 * (dR lam : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
            * (dM N : ℝ) ^ (Work.BMF.th (dK lam) (dRp lam))
            * (dM N : ℝ) ^ ((dH lam : ℝ) * ((dH lam : ℝ) - 1) / 2)
            * (dM N : ℝ) ^ (Work.BMF.th (dG lam) (dSp lam))
            * (dM N : ℝ) ^ (((dH lam : ℝ) + (dG lam : ℝ))
                * ((dG lam : ℝ) - (dH lam : ℝ) + 1) / 2))
        * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) := by
    ring
  refine hfinal.trans ?_
  rw [hrearr, hMmerge, dC0]

/-- The `1/(2rs)`-th power of the `Pprod` bound, with the `M`-power converted to a power of `N`
and the constant factor bounded by `2·exp(10^33(1+stechK))`. -/
lemma Pprod_rpow_bound (lam : ℝ) (N t : ℝ)
    (hNpos : 0 < N) (hMpos : 0 < (dM N : ℝ)) (hM1 : 1 ≤ dM N)
    (hMle : (dM N : ℝ) ≤ 2 * N ^ ((2 : ℝ) / 5))
    (hr1 : 1 ≤ dR lam) (hs1 : 1 ≤ dS lam) (hh1 : 1 ≤ dH lam) (ht : 0 < t)
    (hDnn : 0 ≤ dDelta lam) (hDle : dDelta lam ≤ 2 * (dR lam : ℝ) * (dS lam : ℝ))
    (hrs : 0 < 2 * (dR lam : ℝ) * (dS lam : ℝ))
    (hc0pos : 0 < dC0 lam)
    (hconst : Real.log (2 * dC0 lam) / (2 * (dR lam : ℝ) * (dS lam : ℝ))
      ≤ 10 ^ 33 * (1 + stechK))
    (hPprod : Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N)
      ≤ dC0 lam * (dM N : ℝ) ^ (dDelta lam)
        * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam))) :
    (Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N))
        ^ (1 / (2 * (dR lam : ℝ) * (dS lam : ℝ)))
      ≤ 2 * Real.exp (10 ^ 33 * (1 + stechK))
        * N ^ (-((dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam)
            / (2 * (dR lam : ℝ) * (dS lam : ℝ)))) := by
  set e : ℝ := 1 / (2 * (dR lam : ℝ) * (dS lam : ℝ)) with he
  have henn : 0 ≤ e := by rw [he]; positivity
  have hMnn : 0 ≤ (dM N : ℝ) := hMpos.le
  have hPnn : 0 ≤ Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N) :=
    Work.BMF.Pprod_nonneg (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N)
      hr1 hs1 hM1 hM1 hh1 ht hNpos
  have hD2 : dDelta lam * e ≤ 1 := by
    rw [he, one_div, ← div_eq_mul_inv]
    exact (div_le_one hrs).mpr hDle
  have hsplit : (dC0 lam * (dM N : ℝ) ^ (dDelta lam)
        * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam))) ^ e
      = (dC0 lam) ^ e * ((dM N : ℝ) ^ (dDelta lam)) ^ e
        * (N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam))) ^ e := by
    rw [Real.mul_rpow (mul_nonneg hc0pos.le (Real.rpow_nonneg hMnn _))
          (Real.rpow_nonneg hNpos.le _),
        Real.mul_rpow hc0pos.le (Real.rpow_nonneg hMnn _)]
  have hc0 : (dC0 lam) ^ e ≤ Real.exp (10 ^ 33 * (1 + stechK)) := by
    rw [Real.rpow_def_of_pos hc0pos]
    apply Real.exp_le_exp.mpr
    have h2 : Real.log (dC0 lam) * e ≤ Real.log (2 * dC0 lam) * e :=
      mul_le_mul_of_nonneg_right (Real.log_le_log hc0pos (by linarith)) henn
    have h3 : Real.log (2 * dC0 lam) * e
        = Real.log (2 * dC0 lam) / (2 * (dR lam : ℝ) * (dS lam : ℝ)) := by
      rw [he, one_div, ← div_eq_mul_inv]
    linarith [hconst, h2, h3]
  have hMe : ((dM N : ℝ) ^ (dDelta lam)) ^ e ≤ 2 * N ^ ((2 / 5 : ℝ) * (dDelta lam * e)) := by
    rw [← Real.rpow_mul hMnn]
    calc (dM N : ℝ) ^ (dDelta lam * e)
        ≤ (2 * N ^ ((2 : ℝ) / 5)) ^ (dDelta lam * e) :=
          Real.rpow_le_rpow hMnn hMle (mul_nonneg hDnn henn)
      _ = (2 : ℝ) ^ (dDelta lam * e) * (N ^ ((2 : ℝ) / 5)) ^ (dDelta lam * e) :=
          Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _)
      _ = (2 : ℝ) ^ (dDelta lam * e) * N ^ (((2 : ℝ) / 5) * (dDelta lam * e)) := by
          rw [← Real.rpow_mul hNpos.le]
      _ ≤ 2 * N ^ ((2 / 5 : ℝ) * (dDelta lam * e)) := by
          have h2e : (2 : ℝ) ^ (dDelta lam * e) ≤ 2 := by
            calc (2 : ℝ) ^ (dDelta lam * e) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hD2
              _ = 2 := Real.rpow_one 2
          exact mul_le_mul_of_nonneg_right h2e (Real.rpow_nonneg hNpos.le _)
  have hNe : (N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam))) ^ e
      = N ^ ((-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) * e) :=
    (Real.rpow_mul hNpos.le _ _).symm
  calc (Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N)) ^ e
      ≤ (dC0 lam * (dM N : ℝ) ^ (dDelta lam)
          * N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam))) ^ e :=
        Real.rpow_le_rpow hPnn hPprod henn
    _ = (dC0 lam) ^ e * ((dM N : ℝ) ^ (dDelta lam)) ^ e
        * (N ^ (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam))) ^ e := hsplit
    _ = (dC0 lam) ^ e * ((dM N : ℝ) ^ (dDelta lam)) ^ e
        * N ^ ((-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) * e) := by rw [hNe]
    _ ≤ Real.exp (10 ^ 33 * (1 + stechK)) * (2 * N ^ ((2 / 5 : ℝ) * (dDelta lam * e)))
        * N ^ ((-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) * e) := by
        gcongr
    _ = (2 * Real.exp (10 ^ 33 * (1 + stechK)))
        * (N ^ ((2 / 5 : ℝ) * (dDelta lam * e))
            * N ^ ((-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) * e)) := by ring
    _ = (2 * Real.exp (10 ^ 33 * (1 + stechK)))
        * N ^ (((2 / 5 : ℝ) * (dDelta lam * e))
            + (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) * e) := by
        rw [Real.rpow_add hNpos]
    _ = 2 * Real.exp (10 ^ 33 * (1 + stechK))
        * N ^ (((2 / 5 : ℝ) * (dDelta lam * e))
            + (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) * e) := by ring
    _ = 2 * Real.exp (10 ^ 33 * (1 + stechK))
        * N ^ (-((dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam)
            / (2 * (dR lam : ℝ) * (dS lam : ℝ)))) := by
        have hexp : (2 / 5 : ℝ) * (dDelta lam * e)
            + (-(dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam)) * e
            = -((dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam)
                / (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
          rw [he]
          field_simp
          ring
        rw [hexp]

end

end Work.BMF.liouville
