import Submission.Vinogradov.Localise
import Submission.Vinogradov.NikolskiiGlobal
import Submission.Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm
import Submission.Commons.Analysis.Integral.integrable_and_integral_one_add_norm_neg_mul_le
import Submission.Commons.Measure.Integral.integral_integral_swap_of_lintegral_bound

noncomputable section
open MeasureTheory Complex
open scoped Real BigOperators FourierTransform RealInnerProductSpace Interval

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov
open Classical

/-!
# BDG's `L²`-decoupling lemma (their Lemma 8.2 / (ne89))

This module formalises the `L²`-decoupling step of Bourgain–Demeter–Guth
(*Proof of the main conjecture in Vinogradov's mean value theorem for degrees
higher than three*, Ann. of Math. **184** (2016), §8, Lemma `nl3` / (ne89)):

    ‖E_{[0,1]} g‖²_{L²(w_{B_R})}
      ≲ Σ_{|Δ| = R^{-1}, Δ ⊂ [0,1]} ‖E_Δ g‖²_{L²(w_{B_R})} .

The proof (BDG, §8) multiplies `E_J g` by a **localisation weight** whose Fourier
transform is compactly supported (`locWeight`, from `Localise.lean`): two pieces of
`E_J g` with `1/R`-separated arcs are then orthogonal in `L²`, and the transition
from the localisation weight back to the ball weight `w_{B_R}` is the continuous
version of the cover argument (BDG's Lemma `nl9`, proved here by integrating over
all centres `c'` rather than over a discrete cover).

## Contents

* `theta`, `one_le_theta`, `two_locBand_lt_theta` — the constant `θ = max 1 (4·locBand k)`
  relating the localisation scale `θR` to the ball radius `R`;
* `locBump_decay_sq` — the (Schwartz) decay `‖locBump k z‖² ≤ C (1+‖z‖)^{-100k}`;
* `exists_locWeight_transfer` — the `η_{B'}`-step of `nl9`: the replacement of the
  localisation weight by the ball weight by integrating over the centre;
* `extOp_sum_pieces` — `E_{[0,1]} g = Σ_i E_{[i/N,(i+1)/N]} g`;
* `integral_ball_normSq_le_locWeight` — the localised `≥`-bound on a ball;
* `l2_decoupling_pieces` — the local (per-ball) decoupling;
* `l2_decoupling_extOp` — **(ne89)**: the global `L²`-decoupling.
-/

/-- The constant `θ k = max 1 (4·locBand k)` relating the localisation scale `θR`
to the ball radius `R`.  It satisfies `θ ≥ 1` (so that a `θR`-weight is `≥ 1` on
`B(c,R)`) and `2·locBand k < θ` (so that the Fourier support radius
`locBand k/(θR)` is smaller than half the `1/R`-piece separation). -/
noncomputable def theta (k : ℕ) : ℝ := max 1 (4 * locBand k)

lemma one_le_theta (k : ℕ) : 1 ≤ theta k := le_max_left _ _

lemma theta_pos (k : ℕ) : 0 < theta k := lt_of_lt_of_le one_pos (one_le_theta k)

lemma two_locBand_lt_theta (k : ℕ) : 2 * locBand k < theta k := by
  by_cases h : locBand k ≤ 0
  · have h1 : 2 * locBand k ≤ 0 := by linarith
    have h2 : (0:ℝ) < theta k := theta_pos k
    linarith
  · rw [not_le] at h
    have : 4 * locBand k ≤ theta k := le_max_right _ _
    linarith

/-- The decay of the localisation bump: `‖locBump k z‖² ≤ C (1+‖z‖)^{-100k}`. -/
lemma locBump_decay_sq (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : E k,
      ‖locBump k z‖ ^ 2 ≤ C * (1 + ‖z‖) ^ (-(100 * (k:ℝ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm (locBump k) (100*k)
  refine ⟨C₀ ^ 2, by positivity, fun z => ?_⟩
  have hCz : ‖locBump k z‖ ≤ C₀ * (1 + ‖z‖) ^ (-(100 * (k:ℝ))) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hC₀ z
  have hb : 1 ≤ 1 + ‖z‖ := by have h := norm_nonneg z; linarith
  have hz : 0 ≤ ‖locBump k z‖ := norm_nonneg _
  have hstep : ‖locBump k z‖ ^ 2 ≤ (C₀ * (1 + ‖z‖) ^ (-(100 * (k:ℝ)))) ^ 2 :=
    pow_le_pow_left₀ hz hCz 2
  have hsq : (C₀ * (1 + ‖z‖) ^ (-(100 * (k:ℝ)))) ^ 2
      = C₀ ^ 2 * (1 + ‖z‖) ^ (-(2 * (100 * (k:ℝ)))) := by
    rw [mul_pow, ← Real.rpow_natCast ((1 + ‖z‖) ^ (-(100 * (k:ℝ)))) 2,
      ← Real.rpow_mul (by linarith)]
    ring_nf
  have hcmp : (1 + ‖z‖) ^ (-(2 * (100 * (k:ℝ)))) ≤ (1 + ‖z‖) ^ (-(100 * (k:ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le hb ?_
    have : (0:ℝ) ≤ (k:ℝ) := by positivity
    linarith
  calc ‖locBump k z‖ ^ 2
      ≤ C₀ ^ 2 * (1 + ‖z‖) ^ (-(2 * (100 * (k:ℝ)))) := hstep.trans (le_of_eq hsq)
    _ ≤ C₀ ^ 2 * (1 + ‖z‖) ^ (-(100 * (k:ℝ))) :=
        mul_le_mul_of_nonneg_left hcmp (by positivity)

/-- **Transfer of the localisation weight to the ball weight** (the `η_{B'}`-step of
BDG's Lemma `nl9`, proved here by integrating over *all* centres `c'` instead of over a
discrete cover):
`∫_{c'} w_{B(c,R)}(c') · ‖locWeight k c' (θR) y‖² dc' ≤ C Rᵏ w_{B(c,R)}(y)`,
uniformly in `c`, `R > 0`, `y`. -/
lemma exists_locWeight_transfer (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E k) {R : ℝ}, 0 < R → ∀ y : E k,
      ∫ c' : E k, ballWeight k c R c' * ‖locWeight k c' (theta k * R) y‖ ^ 2
        ≤ C * R^k * ballWeight k c R y := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := locBump_decay_sq k
  have hknn : (0:ℝ) ≤ k := by positivity
  have hAc : (k:ℝ) < (100 * (k:ℝ)) := by
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    nlinarith
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Commons.Analysis.Integral.integrable_and_integral_one_add_norm_neg_mul_le
      (k := k) (A := (100 * (k:ℝ))) (B := (100 * (k:ℝ))) hAc hAc
  refine ⟨(theta k) ^ (100 * (k:ℝ)) * (C₀ * C₁),
    mul_pos (Real.rpow_pos_of_pos (theta_pos k) _) (mul_pos hC₀pos hC₁pos), ?_⟩
  intro c R hR y
  set th : ℝ := theta k with hth
  have hth1 : 1 ≤ th := one_le_theta k
  have hth0 : 0 < th := theta_pos k
  have hthne : th ≠ 0 := hth0.ne'
  have hthkne : th ^ k ≠ 0 := (by positivity : (0:ℝ) < th ^ k).ne'
  set Rθ : ℝ := th * R with hRθdef
  have hRθ : 0 < Rθ := by rw [hRθdef]; exact mul_pos (theta_pos k) (by positivity)
  set z : E k := (Rθ)⁻¹ • (y - c) with hz
  have hyc : y - c = Rθ • z := by rw [hz, smul_inv_smul₀ hRθ.ne']
  have hpos1 : ∀ v : E k, (0:ℝ) < 1 + th * ‖z - v‖ := fun v => by
    have h := norm_nonneg (z - v); nlinarith [hth1, h]
  have hpos2 : ∀ v : E k, (0:ℝ) < 1 + ‖v‖ := fun v => by
    have h := norm_nonneg v; linarith
  have hpos0 : ∀ v : E k, (0:ℝ) < 1 + ‖z - v‖ := fun v => by
    have h := norm_nonneg (z - v); linarith
  set H : E k → ℝ := fun c' => ballWeight k c R c' * ‖locWeight k c' Rθ y‖ ^ 2 with hH
  have hmeas : AEStronglyMeasurable H volume := by
    have hcont1 : Continuous (fun c' : E k => locWeight k c' Rθ y) :=
      (locBump k).continuous.comp (by fun_prop)
    have : Continuous H := by
      simp only [hH]
      exact (ballWeight_continuous k c hR).mul (hcont1.norm.pow 2)
    exact this.aestronglyMeasurable
  have h1 : ∫ c' : E k, H c' = ∫ u : E k, H (y - u) := integral_sub_left k y H hmeas
  set G : E k → ℝ := fun v => ballWeight k c R (y - Rθ • v) * ‖locBump k v‖ ^ 2 with hG
  have h2 : (fun u : E k => H (y - u)) = fun u : E k => G ((Rθ)⁻¹ • u) := by
    funext u
    simp only [hH, hG, locWeight]
    have e1 : y - (y - u) = u := by abel
    rw [e1, smul_inv_smul₀ hRθ.ne']
  have h3 : ∫ u : E k, G ((Rθ)⁻¹ • u) = Rθ^k * ∫ v : E k, G v :=
    integral_smul_inv k hRθ G
  have h4 : ∫ v : E k, G v
      = ∫ v : E k, (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hG]
    rw [ballWeight_eq_rpow k c hR (y - Rθ • v)]
    have hfac : ‖y - Rθ • v - c‖ / R = th * ‖z - v‖ := by
      have hsub : y - Rθ • v - c = Rθ • (z - v) := by rw [smul_sub, ← hyc]; abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hRθ, hRθdef]
      field_simp
    rw [hfac]
  -- (iv) Schwartz decay and the convolution bound
  set f : E k → ℝ := fun v => (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ)))
      * (1 + ‖v‖) ^ (-(100 * (k:ℝ))) with hf
  have hfcont : Continuous f := by
    simp only [hf]
    exact ((continuous_const.add (continuous_const.mul
        (by fun_prop : Continuous fun v : E k => ‖z - v‖))).rpow_const
      (fun v => Or.inl (hpos1 v).ne')).mul
      ((continuous_const.add (by fun_prop : Continuous fun v : E k => ‖v‖)).rpow_const
        (fun v => Or.inl (hpos2 v).ne'))
  have h5 : ∫ v : E k, (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ 2
      ≤ C₀ * ∫ v : E k, f v := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with v
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
    · refine ((hC₁ z).1.const_mul C₀).mono' (hfcont.const_mul C₀).aestronglyMeasurable ?_
      filter_upwards with v
      rw [Real.norm_of_nonneg (mul_nonneg hC₀pos.le (by simp only [hf]; positivity))]
      refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
      calc f v = (1 + ‖v‖) ^ (-(100 * (k:ℝ))) * (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) := by
            simp only [hf]; ring
        _ ≤ (1 + ‖v‖) ^ (-(100 * (k:ℝ))) * (1 + ‖z - v‖) ^ (-(100 * (k:ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
            refine Real.rpow_le_rpow_of_nonpos (hpos0 v) ?_ (by nlinarith [hknn])
            nlinarith [hth1, norm_nonneg (z - v)]
    · filter_upwards with v
      have hw : 0 ≤ (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) := Real.rpow_nonneg (by positivity) _
      calc (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ 2
          ≤ (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ)))
              * (C₀ * (1 + ‖v‖) ^ (-(100 * (k:ℝ)))) :=
            mul_le_mul_of_nonneg_left (hC₀ v) hw
        _ = C₀ * f v := by simp only [hf]; ring
  -- the substitution `v = th⁻¹ • w`
  set G' : E k → ℝ := fun w => (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))
      * (1 + ‖th⁻¹ • w‖) ^ (-(100 * (k:ℝ))) with hG'
  have hfG' : ∀ w : E k, f (th⁻¹ • w) = G' w := by
    intro w
    simp only [hf, hG']
    have e : th * ‖z - th⁻¹ • w‖ = ‖th • z - w‖ := by
      rw [show th • z - w = th • (z - th⁻¹ • w) from by rw [smul_sub, smul_inv_smul₀ hthne],
        norm_smul, Real.norm_eq_abs, abs_of_pos hth0]
    rw [e]
  have hfg : ∫ v : E k, f v = (th ^ k)⁻¹ * ∫ w : E k, G' w := by
    have hc := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := (volume : Measure (E k))) (f := f) (R := th) hth0.le
    rw [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hc
    rw [show (fun x : E k => f (th⁻¹ • x)) = fun w : E k => G' w from funext hfG'] at hc
    rw [hc, ← mul_assoc, inv_mul_cancel₀ hthkne, one_mul]
  have hG'bound : ∫ w : E k, G' w
      ≤ th ^ (100 * (k:ℝ)) * (C₁ * (1 + th * ‖z‖) ^ (-(100 * (k:ℝ)))) := by
    set Φ : E k → ℝ := fun w => th ^ (100 * (k:ℝ))
        * ((1 + ‖w‖) ^ (-(100 * (k:ℝ))) * (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))) with hΦ
    have hposw : ∀ w : E k, (0:ℝ) < 1 + ‖w‖ := fun w => by
      have h := norm_nonneg w; linarith
    have hpt : ∀ w, G' w ≤ Φ w := by
      intro w
      simp only [hG', hΦ]
      have hw1 : 1 ≤ 1 + ‖w‖ := by have h := norm_nonneg w; linarith
      have hle : (1 + ‖w‖) / th ≤ 1 + ‖th⁻¹ • w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hth0), inv_mul_eq_div]
        rw [div_le_iff₀ hth0]
        nlinarith [hth1, div_mul_cancel₀ (‖w‖) hthne]
      have hb0 : 0 < (1 + ‖w‖) / th := by positivity
      have hneg : -(100 * (k:ℝ)) ≤ 0 := by nlinarith [hknn]
      have h1' : (1 + ‖th⁻¹ • w‖) ^ (-(100 * (k:ℝ)))
          ≤ ((1 + ‖w‖) / th) ^ (-(100 * (k:ℝ))) :=
        Real.rpow_le_rpow_of_nonpos hb0 hle hneg
      have h2' : ((1 + ‖w‖) / th) ^ (-(100 * (k:ℝ)))
          = th ^ (100 * (k:ℝ)) * (1 + ‖w‖) ^ (-(100 * (k:ℝ))) := by
        rw [Real.div_rpow (hposw w).le hth0.le, Real.rpow_neg hth0.le, div_inv_eq_mul]
        ring
      calc (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ))) * (1 + ‖th⁻¹ • w‖) ^ (-(100 * (k:ℝ)))
          ≤ (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))
              * (((1 + ‖w‖) / th) ^ (-(100 * (k:ℝ)))) :=
            mul_le_mul_of_nonneg_left h1' (Real.rpow_nonneg (by positivity) _)
        _ = th ^ (100 * (k:ℝ)) * ((1 + ‖w‖) ^ (-(100 * (k:ℝ)))
              * (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))) := by rw [h2']; ring
    have hΦint : Integrable Φ volume := by
      have h' : Integrable (fun w : E k => (1 + ‖w‖) ^ (-(100 * (k:ℝ)))
          * (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))) volume := (hC₁ (th • z)).1
      exact h'.const_mul (th ^ (100 * (k:ℝ)))
    refine le_trans (integral_mono_of_nonneg ?_ hΦint (Filter.Eventually.of_forall hpt)) ?_
    · filter_upwards with w
      simp only [hG']
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
    · rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.rpow_pos_of_pos hth0 (100 * (k:ℝ))))
      have h := (hC₁ (th • z)).2
      rw [min_self] at h
      have hnorm : ‖th • z‖ = th * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hth0]
      rw [hnorm] at h
      exact h
  have hzb : (1 + th * ‖z‖) ^ (-(100 * (k:ℝ))) = ballWeight k c R y := by
    have hval : th * ‖z‖ = ‖y - c‖ / R := by
      rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRθ), inv_mul_eq_div,
        hRθdef]
      field_simp
    rw [hval, ballWeight_eq_rpow k c hR y]
  calc ∫ c' : E k, H c'
      = Rθ^k * ∫ v : E k, G v := by rw [h1, h2, h3]
    _ = Rθ^k * ∫ v : E k, (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ 2 := by
        rw [h4]
    _ ≤ Rθ^k * (C₀ * ∫ v : E k, f v) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = Rθ^k * (C₀ * ((th ^ k)⁻¹ * ∫ w : E k, G' w)) := by rw [hfg]
    _ ≤ Rθ^k * (C₀ * ((th ^ k)⁻¹
          * (th ^ (100 * (k:ℝ)) * (C₁ * (1 + th * ‖z‖) ^ (-(100 * (k:ℝ))))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
        exact mul_le_mul_of_nonneg_left hG'bound (by positivity)
    _ = (theta k) ^ (100 * (k:ℝ)) * (C₀ * C₁) * R^k * ballWeight k c R y := by
        rw [hzb, hRθdef, mul_pow]
        have key : th ^ k * R ^ k * (C₀ * ((th ^ k)⁻¹
              * (th ^ (100 * (k:ℝ)) * (C₁ * ballWeight k c R y))))
            = th ^ (100 * (k:ℝ)) * (C₀ * C₁) * R ^ k * ballWeight k c R y := by
          field_simp [hthkne]
        rw [key, hth]


/-! ## The almost-orthogonality summation

For a family `F i` of `L²` functions whose pairwise products `F i · conj (F j)` have vanishing
integral (which holds for `|i - j| ≥ 2` by the weighted `L²` orthogonality
`extOp_locWeight_orthogonal`), the `L²`-norm of the sum is exactly the `ℓ²`-sum of the norms. -/

/-- The product of two `L²` functions is `L¹`. -/
lemma integrable_mul_star_of_sq (k : ℕ) {f g : E k → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume)
    (hf : Integrable (fun x : E k => ‖f x‖ ^ 2) volume)
    (hg : Integrable (fun x : E k => ‖g x‖ ^ 2) volume) :
    Integrable (fun x : E k => f x * star (g x)) volume := by
  have hdom : Integrable (fun x : E k => ‖f x‖ ^ 2 + ‖g x‖ ^ 2) volume := by
    refine (hf.add hg).congr ?_
    filter_upwards with x; rfl
  refine hdom.mono' (hfm.mul hgm.star) ?_
  filter_upwards with x
  have ha : (0:ℝ) ≤ ‖f x‖ := norm_nonneg _
  have hb : (0:ℝ) ≤ ‖g x‖ := norm_nonneg _
  rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖f x‖ - ‖g x‖), sq_nonneg (‖f x‖ + ‖g x‖)]

/-- The `L²`-norm of a finite sum of `L²` functions is integrable (`L²` is a vector space). -/
lemma integrable_normSq_finset_sum (k : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → E k → ℂ) (hm : ∀ i ∈ s, AEStronglyMeasurable (F i) volume)
    (hint : ∀ i ∈ s, Integrable (fun x : E k => ‖F i x‖ ^ 2) volume) :
    Integrable (fun x : E k => ‖∑ i ∈ s, F i x‖ ^ 2) volume := by
  classical
  revert hm hint
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a t hat IH hm hint
    have ha : Integrable (fun x : E k => ‖F a x‖ ^ 2) := hint a (Finset.mem_insert_self a t)
    have ht : Integrable (fun x : E k => ‖∑ i ∈ t, F i x‖ ^ 2) :=
      IH (fun i hi => hm i (Finset.mem_insert_of_mem hi))
        (fun i hi => hint i (Finset.mem_insert_of_mem hi))
    have hsum : (fun x : E k => ‖∑ i ∈ insert a t, F i x‖ ^ 2)
        = fun x : E k => ‖F a x + ∑ i ∈ t, F i x‖ ^ 2 := by
      funext x; rw [Finset.sum_insert hat]
    rw [hsum]
    have hmsum : AEStronglyMeasurable (fun x : E k => F a x + ∑ i ∈ t, F i x) volume :=
      ((hm a (Finset.mem_insert_self a t)).add
        (Finset.aestronglyMeasurable_sum t (fun i hi =>
          hm i (Finset.mem_insert_of_mem hi)))).congr
        (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply, Finset.sum_apply])
    have hdom : Integrable (fun x : E k => 2 * ‖F a x‖ ^ 2 + 2 * ‖∑ i ∈ t, F i x‖ ^ 2) volume := by
      refine ((ha.const_mul 2).add (ht.const_mul 2)).congr ?_
      filter_upwards with x; rfl
    refine hdom.mono' (hmsum.norm.pow 2) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖F a x + ∑ i ∈ t, F i x‖ ≤ ‖F a x‖ + ‖∑ i ∈ t, F i x‖ := norm_add_le _ _
    have h2 : ‖F a x + ∑ i ∈ t, F i x‖ ^ 2 ≤ (‖F a x‖ + ‖∑ i ∈ t, F i x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖F a x‖ + ‖∑ i ∈ t, F i x‖) ^ 2 ≤ 2 * ‖F a x‖ ^ 2 + 2 * ‖∑ i ∈ t, F i x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖F a x‖ - ‖∑ i ∈ t, F i x‖)]
    exact le_trans h2 h3

/-- **Almost-orthogonality summation.**  If the pairwise products `F i · conj (F j)` of an `L²`
family have vanishing integral, then `∫ ‖Σ_i F i‖² = Σ_i ∫ ‖F i‖²`. -/
lemma integral_normSq_finset_sum_eq (k : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → E k → ℂ) (hm : ∀ i ∈ s, AEStronglyMeasurable (F i) volume)
    (hint : ∀ i ∈ s, Integrable (fun x : E k => ‖F i x‖ ^ 2) volume)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∫ x : E k, F i x * star (F j x)) = 0) :
    (∫ x : E k, ‖∑ i ∈ s, F i x‖ ^ 2) = ∑ i ∈ s, ∫ x : E k, ‖F i x‖ ^ 2 := by
  classical
  revert hm hint horth
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _; simp
  · intro a t hat IH hm hint horth
    have ha : Integrable (fun x : E k => ‖F a x‖ ^ 2) := hint a (Finset.mem_insert_self a t)
    have hma : AEStronglyMeasurable (F a) volume := hm a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, Integrable (fun x : E k => ‖F i x‖ ^ 2) :=
      fun i hi => hint i (Finset.mem_insert_of_mem hi)
    have hmt : ∀ i ∈ t, AEStronglyMeasurable (F i) volume :=
      fun i hi => hm i (Finset.mem_insert_of_mem hi)
    have hHt : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → (∫ x : E k, F i x * star (F j x)) = 0 :=
      fun i hi j hj hij => horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hIH := IH hmt ht hHt
    set G : E k → ℂ := fun x => ∑ i ∈ t, F i x with hG
    have hGm : AEStronglyMeasurable G volume := by
      rw [hG]
      exact (Finset.aestronglyMeasurable_sum t hmt).congr
        (Filter.Eventually.of_forall fun x => by simp only [Finset.sum_apply])
    have hGint : Integrable (fun x : E k => ‖G x‖ ^ 2) := by
      rw [hG]; exact integrable_normSq_finset_sum k t F hmt ht
    have hsum : (fun x : E k => ‖∑ i ∈ insert a t, F i x‖ ^ 2)
        = fun x : E k => ‖F a x + G x‖ ^ 2 := by
      funext x; rw [Finset.sum_insert hat]
    rw [hsum]
    -- the pointwise identity `‖u + v‖² = ‖u‖² + ‖v‖² + 2 Re(u · conj v)`
    have hpoint : ∀ x : E k, ‖F a x + G x‖ ^ 2
        = (‖F a x‖ ^ 2 + ‖G x‖ ^ 2) + 2 * (F a x * star (G x)).re := by
      intro x
      rw [Complex.sq_norm, Complex.normSq_add, Complex.sq_norm, Complex.sq_norm]
      simp only [starRingEnd_apply]
    -- integrability of the cross term
    have hcross_int : Integrable (fun x : E k => F a x * star (G x)) :=
      integrable_mul_star_of_sq k hma hGm ha hGint
    have hre_int : Integrable (fun x : E k => (F a x * star (G x)).re) :=
      Complex.reCLM.integrable_comp hcross_int
    -- the cross integral vanishes
    have hcross_zero : (∫ x : E k, F a x * star (G x)) = 0 := by
      have hGs : ∀ x : E k, star (G x) = ∑ i ∈ t, star (F i x) := by
        intro x; rw [hG]; exact map_sum (starRingEnd ℂ) (fun i => F i x) t
      have hterm : ∀ i ∈ t, Integrable (fun x : E k => F a x * star (F i x)) :=
        fun i hi => integrable_mul_star_of_sq k hma (hmt i hi) ha (ht i hi)
      calc (∫ x : E k, F a x * star (G x))
          = ∫ x : E k, ∑ i ∈ t, F a x * star (F i x) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only []
            rw [hGs x, Finset.mul_sum]
        _ = ∑ i ∈ t, ∫ x : E k, F a x * star (F i x) := by
            rw [integral_finset_sum]; exact hterm
        _ = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            exact horth a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
              (fun h => hat (h ▸ hi))
    have hnorm_sum : (∫ x : E k, (‖F a x‖ ^ 2 + ‖G x‖ ^ 2) + 2 * (F a x * star (G x)).re)
        = (∫ x : E k, ‖F a x‖ ^ 2) + (∫ x : E k, ‖G x‖ ^ 2) := by
      have hA : Integrable (fun x : E k => ‖F a x‖ ^ 2 + ‖G x‖ ^ 2) volume := by
        refine (ha.add hGint).congr ?_
        filter_upwards with x; rfl
      rw [integral_add hA (hre_int.const_mul 2), integral_add ha hGint]
      have hz : (∫ x : E k, 2 * (F a x * star (G x)).re) = 0 := by
        rw [integral_const_mul]
        have h0 : (∫ x : E k, (F a x * star (G x)).re) = 0 := by
          change (∫ x : E k, Complex.reCLM (F a x * star (G x))) = 0
          rw [Complex.reCLM.integral_comp_comm hcross_int, hcross_zero, map_zero]
        rw [h0, mul_zero]
      rw [hz]
      ring
    have hswap : (∫ x : E k, ‖F a x + G x‖ ^ 2)
        = ∫ x : E k, (‖F a x‖ ^ 2 + ‖G x‖ ^ 2) + 2 * (F a x * star (G x)).re :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    have hGsum : (∫ x : E k, ‖G x‖ ^ 2) = ∑ i ∈ t, ∫ x : E k, ‖F i x‖ ^ 2 := by
      rw [hG]; exact hIH
    rw [hswap, hnorm_sum, hGsum, Finset.sum_insert hat]


/-! ## The `1/N`-piece decomposition and the arc separation -/

/-- The first coordinate of `γ(t) - γ(s)` is `t - s`. -/
lemma gammaVec_sub_apply_zero (k : ℕ) (hk : 1 ≤ k) (t s : ℝ) :
    (gammaVec k t - gammaVec k s) ⟨0, hk⟩ = t - s := by
  rw [PiLp.sub_apply, gammaVec_apply, gammaVec_apply]
  norm_num

/-- The moment curve moves at least as fast as its first coordinate:
`|t - s| ≤ ‖γ(t) - γ(s)‖`. -/
lemma abs_sub_le_gammaVec (k : ℕ) (hk : 1 ≤ k) (t s : ℝ) :
    |t - s| ≤ ‖gammaVec k t - gammaVec k s‖ := by
  have h := PiLp.norm_apply_le (gammaVec k t - gammaVec k s) ⟨0, hk⟩
  rw [gammaVec_sub_apply_zero k hk t s, Real.norm_eq_abs] at h
  exact h

/-- **The extension operator is the sum of its `1/N`-pieces.** -/
lemma extOp_sum_pieces (k : ℕ) (N : ℕ) (hN : 1 ≤ N) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume) (x : E k) :
    extOp k g 0 1 x = ∑ i : Fin N, extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x := by
  have hNpos : (0:ℝ) < N := by positivity
  have hNne : ((N:ℝ)) ≠ 0 := hNpos.ne'
  have hprod : IntegrableOn (fun t : ℝ => g t * momChar k x t) (Set.Icc (0:ℝ) 1) volume :=
    hg.mul_continuousOn (momChar_continuous_t k x).continuousOn isCompact_Icc
  set a : ℕ → ℝ := fun i => (i:ℝ)/N with ha
  have hle : ∀ i : ℕ, a i ≤ a (i+1) := by
    intro i
    simp only [ha]
    rw [div_le_div_iff_of_pos_right hNpos]
    push_cast; linarith
  have hint : ∀ i < N, IntervalIntegrable (fun t : ℝ => g t * momChar k x t) volume
      (a i) (a (i+1)) := by
    intro i hi
    refine intervalIntegrable_iff.mpr ?_
    refine hprod.mono_set ?_
    intro t ht
    rw [Set.uIoc_of_le (hle i)] at ht
    rw [Set.mem_Ioc] at ht
    rw [Set.mem_Icc]
    have hi1 : a (i+1) ≤ 1 := by
      simp only [ha]
      rw [div_le_one hNpos]
      have h1 : i + 1 ≤ N := hi
      have h2 : (((i+1:ℕ)):ℝ) ≤ (N:ℝ) := by exact_mod_cast h1
      exact h2
    have hnn : (0:ℝ) ≤ a i := by simp only [ha]; positivity
    exact ⟨le_of_lt (lt_of_le_of_lt hnn ht.1), le_trans ht.2 hi1⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := a)
      (μ := volume) (n := N) hint
  have h0 : a 0 = 0 := by simp only [ha]; simp
  have hN1 : a N = 1 := by
    simp only [ha]
    rw [div_eq_one_iff_eq hNne]
  rw [h0, hN1] at hsum
  have hsum' : (∑ j ∈ Finset.range N,
      extOp k g ((j:ℝ)/N) ((((j+1:ℕ)):ℝ)/N) x) = extOp k g 0 1 x := hsum
  rw [← hsum', Fin.sum_univ_eq_sum_range
    (fun j : ℕ => extOp k g ((j:ℝ)/N) (((j:ℝ)+1)/N) x) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((((i+1:ℕ)):ℝ))/N = ((i:ℝ)+1)/N := by push_cast; ring
  rw [h2]



/-! ## The separation of non-adjacent pieces and the local `L²` estimate -/

lemma two_locBand_div_theta_lt_one (k : ℕ) : 2 * (locBand k / theta k) < 1 := by
  rw [← mul_div_assoc]
  exact (div_lt_one (theta_pos k)).mpr (two_locBand_lt_theta k)

lemma theta_sep_bound (k N : ℕ) (hN : 1 ≤ N) :
    2 * (locBand k / (theta k * (N:ℝ))) < 1/(N:ℝ) := by
  have hNpos : (0:ℝ) < N := by positivity
  have heq : 2 * (locBand k / (theta k * (N:ℝ)))
      = (2 * (locBand k / theta k)) / (N:ℝ) := by
    field_simp
  rw [heq, div_lt_div_iff_of_pos_right hNpos]
  exact two_locBand_div_theta_lt_one k

/-- The separation bound for a ball radius `R ≥ N` (the pieces have length `1/N`). -/
lemma theta_sep_bound' (k N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : (N:ℝ) ≤ R) :
    2 * (locBand k / (theta k * R)) < 1/(N:ℝ) := by
  have hNpos : (0:ℝ) < N := by positivity
  have hθ := theta_pos k
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  by_cases hL : locBand k ≤ 0
  · have h1 : 2 * (locBand k / (theta k * R)) ≤ 0 := by
      have h3 : locBand k / (theta k * R) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hL (by positivity)
      nlinarith
    have h2 : (0:ℝ) < 1/(N:ℝ) := by positivity
    linarith
  · rw [not_le] at hL
    have h1 : 2 * (locBand k / (theta k * R)) ≤ 2 * (locBand k / (theta k * (N:ℝ))) := by
      rw [← mul_div_assoc, ← mul_div_assoc]
      exact div_le_div_of_nonneg_left (by linarith) (mul_pos hθ hNpos)
        (mul_le_mul_of_nonneg_left hR hθ.le)
    exact lt_of_le_of_lt h1 (theta_sep_bound k N hN)

/-- Two `1/N`-pieces with index gap at least `2` are separated by at least `1/N`. -/
lemma abs_sub_ge_pieces {N i j : ℕ} (hN : 1 ≤ N) (hij : i + 2 ≤ j) {t s : ℝ}
    (ht : t ∈ Set.uIcc ((i:ℝ)/N) (((i:ℝ)+1)/N))
    (hs : s ∈ Set.uIcc ((j:ℝ)/N) (((j:ℝ)+1)/N)) :
    (1:ℝ)/N ≤ |t - s| := by
  have hNpos : (0:ℝ) < N := by positivity
  have hab : ((i:ℝ)/N) ≤ ((i:ℝ)+1)/N := by
    rw [div_le_div_iff_of_pos_right hNpos]; linarith
  have hcd : ((j:ℝ)/N) ≤ ((j:ℝ)+1)/N := by
    rw [div_le_div_iff_of_pos_right hNpos]; linarith
  rw [Set.uIcc_of_le hab] at ht
  rw [Set.uIcc_of_le hcd] at hs
  rw [Set.mem_Icc] at ht hs
  have hlt : ((i:ℝ)+1)/N < (j:ℝ)/N := by
    rw [div_lt_div_iff_of_pos_right hNpos]
    have h3 : i + 1 + 1 ≤ j := by omega
    have h4 : ((i:ℝ)+1) + 1 ≤ (j:ℝ) := by exact_mod_cast h3
    linarith
  have hgap : (1:ℝ)/N ≤ (j:ℝ)/N - ((i:ℝ)+1)/N := by
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hNpos]
    have h4 : ((i:ℝ)+1) + 1 ≤ (j:ℝ) := by
      have h3 : i + 1 + 1 ≤ j := by omega
      exact_mod_cast h3
    linarith
  have hsgt : t < s := by linarith [ht.2, hs.1]
  rw [abs_of_neg (by linarith : t - s < 0), neg_sub]
  linarith [hs.1, ht.2, hgap]

/-- **Arc separation for pieces of equal parity**: two distinct `1/N`-pieces whose indices have the
same parity have arcs separated by more than `2·locBand k/(θR)`, for any ball radius `R ≥ N`; this is
the hypothesis of the weighted `L²` orthogonality `extOp_locWeight_orthogonal`. -/
lemma sepArcs (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) {R : ℝ} (hR : (N:ℝ) ≤ R)
    {i j : ℕ} (hiN : i < N) (hjN : j < N)
    (hij : i ≠ j) (hpar : i % 2 = j % 2) :
    ∀ t ∈ Set.uIcc ((i:ℝ)/N) (((i:ℝ)+1)/N),
      ∀ s ∈ Set.uIcc ((j:ℝ)/N) (((j:ℝ)+1)/N),
      2 * (locBand k / (theta k * R)) < ‖gammaVec k t - gammaVec k s‖ := by
  intro t ht s hs
  have hsep := theta_sep_bound' k N hN hR
  have hmono : |t - s| ≤ ‖gammaVec k t - gammaVec k s‖ := abs_sub_le_gammaVec k hk t s
  have hone : (1:ℝ)/N ≤ |t - s| := by
    have h2le : i + 2 ≤ j ∨ j + 2 ≤ i := by omega
    rcases h2le with h2le | h2le
    · exact abs_sub_ge_pieces hN h2le ht hs
    · rw [abs_sub_comm]
      exact abs_sub_ge_pieces hN h2le hs ht
  linarith [hsep, hone]

/-- `g` is interval-integrable on every `1/N`-piece. -/
lemma intervalIntegrable_piece (N : ℕ) (hN : 1 ≤ N) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume) (i : ℕ) (hi : i < N) :
    IntervalIntegrable g volume ((i:ℝ)/N) (((i:ℝ)+1)/N) := by
  have hNpos : (0:ℝ) < N := by positivity
  refine intervalIntegrable_iff.mpr ?_
  refine hg.mono_set ?_
  intro t ht
  have hle : ((i:ℝ)/N : ℝ) ≤ ((i:ℝ)+1)/N := by
    rw [div_le_div_iff_of_pos_right hNpos]; linarith
  rw [Set.uIoc_of_le hle] at ht
  rw [Set.mem_Ioc] at ht
  rw [Set.mem_Icc]
  have hi1 : ((i:ℝ)+1)/N ≤ 1 := by
    rw [div_le_one hNpos]
    have h2 : (((i+1:ℕ)):ℝ) ≤ (N:ℝ) := by exact_mod_cast hi
    push_cast at h2 ⊢
    linarith
  exact ⟨le_of_lt (lt_of_le_of_lt (by positivity : (0:ℝ) ≤ (i:ℝ)/N) ht.1),
    le_trans ht.2 hi1⟩

/-- The piece bounds are increasing: `(i)/N ≤ (i+1)/N`. -/
lemma piece_le (N : ℕ) (i : ℕ) : ((i:ℝ)/N : ℝ) ≤ ((i:ℝ)+1)/N := by
  rcases eq_or_ne N 0 with hN | hN
  · simp [hN]
  · exact (div_le_div_iff_of_pos_right
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr (by linarith)

/-- **The local `L²`-estimate.**  For each centre `c'`, the `L²`-norm of `E_{[0,1]}g` over the ball
`B(c',N)` is bounded by twice the `ℓ²`-sum of the localised `1/N`-pieces. -/
theorem local_estimate (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : (N:ℝ) ≤ R)
    (c' : E k) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume) :
    ∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ 2
      ≤ 2 * ∑ i : Fin N, ∫ x : E k,
          ‖locWeight k c' (theta k * R) x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2 := by
  set Rθ : ℝ := theta k * R with hRθdef
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hRθ : 0 < Rθ := by rw [hRθdef]; exact mul_pos (theta_pos k) hRpos
  have hgi : IntervalIntegrable g volume 0 1 := by
    refine intervalIntegrable_iff.mpr ?_
    refine hg.mono_set ?_
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rw [Set.mem_Ioc] at ht
    rw [Set.mem_Icc]
    exact ⟨le_of_lt ht.1, ht.2⟩
  set F : Fin N → E k → ℂ := fun i x =>
    locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x with hF
  have hFm : ∀ i : Fin N, AEStronglyMeasurable (F i) volume := fun i => by
    rw [hF]
    exact aestronglyMeasurable_locWeight_mul_extOp k c' Rθ g (piece_le N i.val)
      (intervalIntegrable_piece N hN g hg i.val i.isLt)
  have hFi : ∀ i : Fin N, Integrable (fun x : E k => ‖F i x‖ ^ 2) volume := fun i => by
    rw [hF]
    exact integrable_normSq_locWeight_mul_extOp k c' hRθ g (piece_le N i.val)
      (intervalIntegrable_piece N hN g hg i.val i.isLt)
  -- (a) the localisation weight dominates `1` on `B(c',R)`
  have hdom : ∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ 2
      ≤ ∫ x : E k, ‖locWeight k c' Rθ x * extOp k g 0 1 x‖ ^ 2 := by
    have hpt : ∀ x : E k, (Metric.ball c' R).indicator
        (fun x => ‖extOp k g 0 1 x‖ ^ 2) x
        ≤ ‖locWeight k c' Rθ x * extOp k g 0 1 x‖ ^ 2 := by
      intro x
      by_cases hx : x ∈ Metric.ball c' R
      · rw [Set.indicator_of_mem hx, norm_mul, mul_pow]
        have hx' : ‖x - c'‖ < R := by
          rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx
        have hNR : R ≤ Rθ := by
          rw [hRθdef]
          have h1 := one_le_theta k
          nlinarith [h1, hRpos]
        have h1 : ‖(Rθ)⁻¹ • (x - c')‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRθ), inv_mul_le_iff₀ hRθ]
          linarith [le_of_lt hx']
        have h2 : 1 ≤ (locBump k ((Rθ)⁻¹ • (x - c'))).re := locBump_re_ge_one k h1
        have h3 : 1 ≤ ‖locWeight k c' Rθ x‖ := by
          rw [locWeight]
          exact h2.trans (Complex.re_le_norm _)
        have h4 : (1:ℝ) ≤ ‖locWeight k c' Rθ x‖ ^ 2 := by
          nlinarith [norm_nonneg (locWeight k c' Rθ x)]
        calc ‖extOp k g 0 1 x‖ ^ 2
            = 1 * ‖extOp k g 0 1 x‖ ^ 2 := by ring
          _ ≤ ‖locWeight k c' Rθ x‖ ^ 2 * ‖extOp k g 0 1 x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      · rw [Set.indicator_of_notMem hx]; positivity
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    refine integral_mono_of_nonneg ?_ ?_ (Filter.Eventually.of_forall hpt)
    · filter_upwards with x
      by_cases hx : x ∈ Metric.ball c' R
      · rw [Set.indicator_of_mem hx]; positivity
      · rw [Set.indicator_of_notMem hx]; simp
    · exact integrable_normSq_locWeight_mul_extOp k c' hRθ g (by norm_num) hgi
  -- (b) expand `E_{[0,1]}g` into its `1/N`-pieces
  have hsplit : ∫ x : E k, ‖locWeight k c' Rθ x * extOp k g 0 1 x‖ ^ 2
      = ∫ x : E k, ‖∑ i : Fin N, F i x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have h1 : locWeight k c' Rθ x * extOp k g 0 1 x
        = ∑ i : Fin N, F i x := by
      rw [extOp_sum_pieces k N hN g hg x, Finset.mul_sum]
    simp only []
    rw [h1]
  -- (c) the parity split and the almost-orthogonality summation
  set ev : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => i.val % 2 = 0) with hev
  set od : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => ¬ i.val % 2 = 0) with hod
  have hmem_od : ∀ i : Fin N, i ∈ od → ¬ i.val % 2 = 0 := by
    intro i hi; rw [hod] at hi; exact (Finset.mem_filter.mp hi).2
  have hmem_ev : ∀ i : Fin N, i ∈ ev → i.val % 2 = 0 := by
    intro i hi; rw [hev] at hi; exact (Finset.mem_filter.mp hi).2
  have hmev : ∀ i ∈ ev, AEStronglyMeasurable (F i) volume := fun i _ => hFm i
  have hint_ev : ∀ i ∈ ev, Integrable (fun x : E k => ‖F i x‖ ^ 2) volume := fun i _ => hFi i
  have hmod : ∀ i ∈ od, AEStronglyMeasurable (F i) volume := fun i _ => hFm i
  have hint_od : ∀ i ∈ od, Integrable (fun x : E k => ‖F i x‖ ^ 2) volume := fun i _ => hFi i
  have horth_ev : ∫ x : E k, ‖∑ i ∈ ev, F i x‖ ^ 2
      = ∑ i ∈ ev, ∫ x : E k, ‖F i x‖ ^ 2 := by
    refine integral_normSq_finset_sum_eq k ev F hmev hint_ev ?_
    intro i hi j hj hij
    refine extOp_locWeight_orthogonal k c' hRθ (piece_le N i.val) (piece_le N j.val) g g
      (intervalIntegrable_piece N hN g hg i.val i.isLt)
      (intervalIntegrable_piece N hN g hg j.val j.isLt) ?_
    exact sepArcs k N hk hN hR i.isLt j.isLt (fun h => hij (Fin.ext h))
      (by rw [hmem_ev i hi, hmem_ev j hj])
  have horth_od : ∫ x : E k, ‖∑ i ∈ od, F i x‖ ^ 2
      = ∑ i ∈ od, ∫ x : E k, ‖F i x‖ ^ 2 := by
    refine integral_normSq_finset_sum_eq k od F hmod hint_od ?_
    intro i hi j hj hij
    have hi1 : i.val % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one i.val with h | h
      · exact absurd h (hmem_od i hi)
      · exact h
    have hj1 : j.val % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one j.val with h | h
      · exact absurd h (hmem_od j hj)
      · exact h
    refine extOp_locWeight_orthogonal k c' hRθ (piece_le N i.val) (piece_le N j.val) g g
      (intervalIntegrable_piece N hN g hg i.val i.isLt)
      (intervalIntegrable_piece N hN g hg j.val j.isLt) ?_
    exact sepArcs k N hk hN hR i.isLt j.isLt (fun h => hij (Fin.ext h)) (by rw [hi1, hj1])
  have hpart : ∀ x : E k, (∑ i : Fin N, F i x)
      = (∑ i ∈ ev, F i x) + (∑ i ∈ od, F i x) := by
    intro x
    rw [hev, hod]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin N => i.val % 2 = 0) (fun i => F i x)).symm
  have horth : ∫ x : E k, ‖∑ i : Fin N, F i x‖ ^ 2
      ≤ 2 * ∑ i : Fin N, ∫ x : E k, ‖F i x‖ ^ 2 := by
    calc ∫ x : E k, ‖∑ i : Fin N, F i x‖ ^ 2
        = ∫ x : E k, ‖(∑ i ∈ ev, F i x) + (∑ i ∈ od, F i x)‖ ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => by
            simp only []; rw [hpart x])
      _ ≤ ∫ x : E k, (2 * ‖∑ i ∈ ev, F i x‖ ^ 2 + 2 * ‖∑ i ∈ od, F i x‖ ^ 2) := by
          refine integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards with x; positivity
          · refine (((integrable_normSq_finset_sum k ev F hmev hint_ev).const_mul 2).add
              ((integrable_normSq_finset_sum k od F hmod hint_od).const_mul 2)).congr ?_
            filter_upwards with x; rfl
          · filter_upwards with x
            have h1 : ‖(∑ i ∈ ev, F i x) + (∑ i ∈ od, F i x)‖
                ≤ ‖∑ i ∈ ev, F i x‖ + ‖∑ i ∈ od, F i x‖ := norm_add_le _ _
            have h2 : ‖(∑ i ∈ ev, F i x) + (∑ i ∈ od, F i x)‖ ^ 2
                ≤ (‖∑ i ∈ ev, F i x‖ + ‖∑ i ∈ od, F i x‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
            nlinarith [h2, sq_nonneg (‖∑ i ∈ ev, F i x‖ - ‖∑ i ∈ od, F i x‖)]
      _ = 2 * (∑ i ∈ ev, ∫ x : E k, ‖F i x‖ ^ 2)
            + 2 * (∑ i ∈ od, ∫ x : E k, ‖F i x‖ ^ 2) := by
          rw [integral_add ((integrable_normSq_finset_sum k ev F hmev hint_ev).const_mul 2)
                ((integrable_normSq_finset_sum k od F hmod hint_od).const_mul 2),
            integral_const_mul, integral_const_mul, horth_ev, horth_od]
      _ = 2 * ∑ i : Fin N, ∫ x : E k, ‖F i x‖ ^ 2 := by
          rw [hev, hod, Finset.sum_filter, Finset.sum_filter]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : i.val % 2 = 0 <;> simp [h]
  calc ∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ 2
      ≤ ∫ x : E k, ‖locWeight k c' Rθ x * extOp k g 0 1 x‖ ^ 2 := hdom
    _ = ∫ x : E k, ‖∑ i : Fin N, F i x‖ ^ 2 := hsplit
    _ ≤ 2 * ∑ i : Fin N, ∫ x : E k, ‖F i x‖ ^ 2 := horth
    _ = 2 * ∑ i : Fin N, ∫ x : E k,
          ‖locWeight k c' (theta k * R) x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2 := by
        simp only [hF, hRθdef]


/-! ## The transfer of a single piece to the ball weight -/

/-- The `L²`-norm of the localisation weight scales as `Rᵏ`. -/
lemma integral_normSq_locWeight (k : ℕ) (c' : E k) {R : ℝ} (hR : 0 < R) :
    ∫ x : E k, ‖locWeight k c' R x‖ ^ 2 = R^k * ∫ x : E k, ‖locBump k x‖ ^ 2 := by
  have htr : (∫ x : E k, (fun w : E k => ‖locBump k ((R⁻¹:ℝ) • w)‖ ^ 2) (-c' + x))
      = ∫ x : E k, ‖locBump k ((R⁻¹:ℝ) • x)‖ ^ 2 :=
    integral_translate k (-c') (fun w : E k => ‖locBump k ((R⁻¹:ℝ) • w)‖ ^ 2) (by fun_prop)
  calc ∫ x : E k, ‖locWeight k c' R x‖ ^ 2
      = ∫ x : E k, (fun w : E k => ‖locBump k ((R⁻¹:ℝ) • w)‖ ^ 2) (-c' + x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [locWeight]
        congr 2
        rw [sub_eq_add_neg]
        abel
    _ = ∫ x : E k, ‖locBump k ((R⁻¹:ℝ) • x)‖ ^ 2 := htr
    _ = R^k * ∫ x : E k, ‖locBump k x‖ ^ 2 := integral_smul_inv k hR (fun y : E k => ‖locBump k y‖ ^ 2)

/-- The squared localisation weight is integrable. -/
lemma integrable_normSq_locWeight (k : ℕ) (c' : E k) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : E k => ‖locWeight k c' R x‖ ^ 2) volume := by
  have h := memLp_locWeight k c' hR (p := 2) (by norm_num)
  have h' : MemLp (locWeight k c' R) (2 : ℕ) volume := by simpa using h
  exact MemLp.integrable_norm_pow (p := 2) h' (by norm_num)


/-- The extension operator over a subinterval of `[0,1]` is AE-strongly-measurable. -/
lemma aestronglyMeasurable_extOp (k : ℕ) (g : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    AEStronglyMeasurable (fun x : E k => extOp k g a b x) volume := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc a b) with hν
  have hgw : Integrable g ν := by rw [hν]; exact hg.1
  have hF : AEStronglyMeasurable (fun z : E k × ℝ => g z.2 * momChar k z.1 z.2)
      (volume.prod ν) :=
    (hgw.aestronglyMeasurable.comp_snd).mul
      ((continuous_momChar_uncurry k).aestronglyMeasurable)
  have hint : AEStronglyMeasurable (fun x : E k => ∫ t, g t * momChar k x t ∂ν) volume :=
    hF.integral_prod_right'
  have heq : (extOp k g a b) = fun x : E k => ∫ t, g t * momChar k x t ∂ν := by
    funext x
    rw [extOp, hν, intervalIntegral.integral_of_le hab]
  rw [heq]
  exact hint

/-- **Transfer of one `1/N`-piece**: the `c'`-average of the localised `L²`-norm of a single piece
is dominated by `C3·Nᵏ` times its weighted `L²`-norm. -/
lemma locWeight_piece_transfer (k : ℕ) (hk : 1 ≤ k) (c : E k) {N : ℝ} (hN : 0 < N) {C3 : ℝ}
    (hC3nn : 0 ≤ C3)
    (hC3 : ∀ y : E k, ∫ c' : E k, ballWeight k c N c' *
        ‖locWeight k c' (theta k * N) y‖ ^ 2 ≤ C3 * N^k * ballWeight k c N y)
    {Φ : E k → ℂ} (hEm : AEMeasurable Φ volume) {M : ℝ} (hMM : 0 ≤ M)
    (hM : ∀ x, ‖Φ x‖ ≤ M) :
    ∫ c' : E k, ballWeight k c N c' *
        (∫ x : E k, ‖locWeight k c' (theta k * N) x * Φ x‖ ^ 2)
      ≤ C3 * N^k * wLpPow k c N 2 Φ := by
  set Rθ : ℝ := theta k * N with hRθdef
  have hRθ : 0 < Rθ := by rw [hRθdef]; exact mul_pos (theta_pos k) hN
  set IB : ℝ := ∫ x : E k, ‖locBump k x‖ ^ 2 with hIB
  have hKint : ∀ y : E k, ∫ x : E k, ‖locWeight k y Rθ x‖ ^ 2 = Rθ^k * IB := fun y => by
    rw [hIB, hRθdef]; exact integral_normSq_locWeight k y hRθ
  have hCbd : ∀ a : E k, ∫⁻ b, ENNReal.ofReal (‖locWeight k a Rθ b‖ ^ 2) ∂volume
      ≤ ENNReal.ofReal (Rθ^k * IB) := fun a => by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_normSq_locWeight k a hRθ)
      (Filter.Eventually.of_forall fun b => sq_nonneg _)]
    exact le_of_eq (congrArg ENNReal.ofReal (hKint a))
  have hKm : AEMeasurable (Function.uncurry (fun a b : E k => ‖locWeight k a Rθ b‖ ^ 2))
      (volume.prod volume) := by
    have hcont : Continuous (fun p : E k × E k => ‖locWeight k p.1 Rθ p.2‖ ^ 2) := by
      simp only [locWeight]
      fun_prop
    exact hcont.aemeasurable
  have hFm : AEMeasurable (fun b : E k => ‖Φ b‖ ^ 2) volume := by
    have h1 : AEMeasurable (fun b : E k => ‖Φ b‖) volume := hEm.norm
    exact h1.pow_const 2
  have hkey := Commons.Measure.Integral.integral_integral_swap_of_lintegral_bound
    (μ := (volume : MeasureTheory.Measure (E k))) (ν := (volume : MeasureTheory.Measure (E k)))
    (w := ballWeight k c N) (K := fun a b : E k => ‖locWeight k a Rθ b‖ ^ 2)
    (F := fun b : E k => ‖Φ b‖ ^ 2)
    (fun a => (ballWeight_pos k c hN a).le) (fun a b => sq_nonneg _) (fun b => sq_nonneg _)
    (ballWeight_continuous k c hN).aemeasurable hKm hFm hCbd
    (fun b => pow_le_pow_left₀ (norm_nonneg _) (hM b) 2)
    (ballWeight_integrable k hk c hN)
  obtain ⟨hint, hswap⟩ := hkey
  have hLHS1 : (∫ c' : E k, ballWeight k c N c' *
        (∫ x : E k, ‖locWeight k c' Rθ x * Φ x‖ ^ 2))
      = ∫ c' : E k, ∫ x : E k,
          ballWeight k c N c' * ‖locWeight k c' Rθ x‖ ^ 2 * ‖Φ x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
    simp only []
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, mul_pow]; ring
  have hLHS2 : (∫ p : E k × E k,
        ballWeight k c N p.1 * ‖locWeight k p.1 Rθ p.2‖ ^ 2 * ‖Φ p.2‖ ^ 2 ∂(volume.prod volume))
      = ∫ c' : E k, ∫ x : E k,
          ballWeight k c N c' * ‖locWeight k c' Rθ x‖ ^ 2 * ‖Φ x‖ ^ 2 :=
    MeasureTheory.integral_prod _ hint
  have hstep : (∫ c' : E k, ballWeight k c N c' *
        (∫ x : E k, ‖locWeight k c' Rθ x * Φ x‖ ^ 2))
      = ∫ x : E k, ‖Φ x‖ ^ 2 * (∫ c' : E k, ballWeight k c N c' * ‖locWeight k c' Rθ x‖ ^ 2) := by
    rw [hLHS1, ← hLHS2, hswap]
  rw [hstep]
  have hfin : (∫ x : E k, ‖Φ x‖ ^ 2 *
        (∫ c' : E k, ballWeight k c N c' * ‖locWeight k c' Rθ x‖ ^ 2))
      ≤ ∫ x : E k, ‖Φ x‖ ^ 2 * (C3 * N^k * ballWeight k c N x) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with x
      refine mul_nonneg (sq_nonneg _) (integral_nonneg fun c' => ?_)
      exact mul_nonneg (le_of_lt (ballWeight_pos k c hN c')) (sq_nonneg _)
    · refine ((ballWeight_integrable k hk c hN).const_mul (M^2 * (C3 * N^k))).mono'
        (by
          have h1 : AEMeasurable (fun x : E k => ‖Φ x‖ ^ 2) volume := (hEm.norm).pow_const 2
          have h2 : AEMeasurable (fun x : E k => ballWeight k c N x * (C3 * N^k)) volume :=
            (ballWeight_continuous k c hN).aemeasurable.mul_const _
          exact ((h1.mul h2).congr (Filter.Eventually.of_forall fun x => by
            simp only [Pi.mul_apply]; ring)).aestronglyMeasurable)
        ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (by
        refine mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hC3nn (by positivity)) ?_)
        exact (ballWeight_pos k c hN x).le)]
      calc ‖Φ x‖ ^ 2 * (C3 * N^k * ballWeight k c N x)
          ≤ M ^ 2 * (C3 * N^k * ballWeight k c N x) := by
            refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM x) 2) ?_
            exact mul_nonneg (mul_nonneg hC3nn (by positivity)) (ballWeight_pos k c hN x).le
        _ = (M ^ 2 * (C3 * N^k)) * ballWeight k c N x := by ring
    · filter_upwards with x
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [hRθdef] at hC3
      exact hC3 x
  refine hfin.trans (le_of_eq ?_)
  have hfinal : (∫ x : E k, ‖Φ x‖ ^ 2 * (C3 * N^k * ballWeight k c N x))
      = C3 * N^k * wLpPow k c N 2 Φ := by
    have h1 : (∫ x : E k, ‖Φ x‖ ^ 2 * (C3 * N^k * ballWeight k c N x))
        = C3 * N^k * ∫ x : E k, ‖Φ x‖ ^ 2 * ballWeight k c N x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h1]
    congr 1
    unfold wLpPow
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_ofNat]
  exact hfinal


/-- A nonnegative function dominated by a constant, times the ball weight, is integrable. -/
lemma integrable_ballWeight_mul_bound (k : ℕ) (hk : 1 ≤ k) (c : E k) {N : ℝ} (hN : 0 < N)
    {h : E k → ℝ} (hm : AEMeasurable h volume) {C : ℝ} (hC0 : 0 ≤ C)
    (hh0 : ∀ c', 0 ≤ h c') (hb : ∀ c', h c' ≤ C) :
    Integrable (fun c' : E k => ballWeight k c N c' * h c') volume := by
  have hdom : Integrable (fun c' : E k => C * ballWeight k c N c') volume :=
    (ballWeight_integrable k hk c hN).const_mul C
  refine hdom.mono' ((ballWeight_continuous k c hN).aemeasurable.mul hm).aestronglyMeasurable ?_
  filter_upwards with c'
  rw [Real.norm_of_nonneg (mul_nonneg (ballWeight_pos k c hN c').le (hh0 c')), mul_comm]
  exact mul_le_mul_of_nonneg_right (hb c') (ballWeight_pos k c hN c').le

/-- `wLpPow` at exponent `2` in terms of the plain square. -/
lemma wLpPow_two_eq (k : ℕ) (c : E k) (R : ℝ) (f : E k → ℂ) :
    wLpPow k c R 2 f = ∫ x : E k, ‖f x‖ ^ (2:ℝ) * ballWeight k c R x := rfl

/-- **BDG's `L²`-decoupling lemma (their Lemma 8.2, (ne89)), for the extension operator.**
There is `C > 0` such that for every `N ≥ 1`, every ball radius `R ≥ N`, every centre `c` and every
`g` integrable on `[0,1]`,
`‖E_{[0,1]}g‖²_{L²(w_{B(c,R)})} ≤ C Σ_{i<N} ‖E_{((i)/N,(i+1)/N]}g‖²_{L²(w_{B(c,R)})}`. -/
theorem l2_decoupling_extOp (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (R : ℝ), (N:ℝ) ≤ R → ∀ (c : E k) (g : ℝ → ℂ),
      IntegrableOn g (Set.Icc (0:ℝ) 1) volume →
      wLpPow k c R 2 (extOp k g 0 1)
        ≤ C * ∑ i : Fin N, wLpPow k c R 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)) := by
  obtain ⟨C3, hC3pos, hC3⟩ := exists_locWeight_transfer k hk
  have hV : (0:ℝ) < ballVol k 0 1 := ballVol_pos k hk 0 (by norm_num)
  refine ⟨2 * ((2:ℝ)^(100*k) / ballVol k 0 1) * C3 + 1, by positivity, ?_⟩
  intro N hN R hR c g hg
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hR1 : 1 ≤ R := le_trans (by exact_mod_cast hN) hR
  set Rθ : ℝ := theta k * R with hRθdef
  have hRθ : 0 < Rθ := by rw [hRθdef]; exact mul_pos (theta_pos k) hRpos
  set K1 : ℝ := (2:ℝ)^(100*k) / ballVol k 0 1 with hK1
  have hK1pos : 0 < K1 := by
    rw [hK1]; exact div_pos (pow_pos (by norm_num : (0:ℝ) < 2) _) hV
  set IB : ℝ := ∫ x : E k, ‖locBump k x‖ ^ 2 with hIB
  have hIBnn : 0 ≤ IB := by rw [hIB]; exact integral_nonneg fun x => sq_nonneg _
  set M0 : ℝ := (∑ i : Fin N, ∫ t in ((i:ℝ)/N)..(((i:ℝ)+1)/N), ‖g t‖) + 1 with hM0
  have hM0nn : 0 ≤ M0 := by
    rw [hM0]
    exact add_nonneg (Finset.sum_nonneg fun i _ =>
      intervalIntegral.integral_nonneg (piece_le N i.val) fun t _ => norm_nonneg _) zero_le_one
  -- (a) measurability and boundedness of the pieces
  have hpiece_meas : ∀ i : Fin N, AEMeasurable
      (fun x : E k => extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x) volume := fun i =>
    (aestronglyMeasurable_extOp k g (piece_le N i.val)
      (intervalIntegrable_piece N hN g hg i.val i.isLt)).aemeasurable
  have hpiece_bd : ∀ i : Fin N, ∀ x : E k,
      ‖extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ≤ M0 := by
    intro i x
    refine (extOp_norm_le k g (piece_le N i.val) x).trans ?_
    rw [hM0]
    have hle := Finset.single_le_sum
      (f := fun i : Fin N => ∫ t in ((i:ℝ)/N)..(((i:ℝ)+1)/N), ‖g t‖)
      (fun j _ => intervalIntegral.integral_nonneg (piece_le N j.val) fun t _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  -- (b) the localisation weight has `L²`-mass `Rθᵏ·IB`
  have hKmass : ∀ c' : E k, ∫ x : E k, ‖locWeight k c' Rθ x‖ ^ 2 = Rθ^k * IB := by
    intro c'; rw [hIB, hRθdef]; exact integral_normSq_locWeight k c' hRθ
  have hgib : ∀ i : Fin N, ∀ c' : E k,
      ∫ x : E k, ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2
        ≤ M0 ^ 2 * (Rθ^k * IB) := by
    intro i c'
    have hdom : Integrable (fun x : E k => M0 ^ 2 * ‖locWeight k c' Rθ x‖ ^ 2) volume :=
      (integrable_normSq_locWeight k c' hRθ).const_mul _
    have hle := integral_mono_of_nonneg
      (f := fun x : E k => ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)
      (g := fun x : E k => M0 ^ 2 * ‖locWeight k c' Rθ x‖ ^ 2)
      (Filter.Eventually.of_forall fun x => by simp only []; positivity) hdom
      (Filter.Eventually.of_forall fun x => by
        simp only []
        rw [norm_mul, mul_pow, mul_comm (‖locWeight k c' Rθ x‖ ^ 2)]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hpiece_bd i x) 2) (sq_nonneg _))
    rw [integral_const_mul, hKmass c'] at hle
    exact hle
  -- (c) the steps
  have hstep1 : wLpPow k c R 2 (extOp k g 0 1) ≤ K1 * (R^k)⁻¹ *
      (∫ c' : E k, ballWeight k c R c' *
        (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ 2)) := by
    have h := local_average_step k hk g hg (Q := 2) (by norm_num) c (R := R) hR1
    rw [hK1]
    rw [← wLpPow_two_eq] at h
    simp only [Real.rpow_ofNat] at h
    exact h
  have hint_meas : ∀ i : Fin N, AEMeasurable (fun c' : E k => ∫ x : E k,
      ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2) volume := by
    intro i
    have hF : AEStronglyMeasurable (fun p : E k × E k =>
        ‖locWeight k p.1 Rθ p.2 * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) p.2‖ ^ 2)
        (volume.prod volume) := by
      have hc : AEMeasurable (fun p : E k × E k => locWeight k p.1 Rθ p.2)
          (volume.prod volume) := by
        have hcc : Continuous (fun p : E k × E k => locWeight k p.1 Rθ p.2) := by
          simp only [locWeight]; fun_prop
        exact hcc.aemeasurable
      exact ((hc.mul ((hpiece_meas i).comp_snd)).norm.pow_const 2).aestronglyMeasurable
    exact (hF.integral_prod_right').aemeasurable
  have hRHSm : AEMeasurable (fun c' : E k => 2 * ∑ i : Fin N, ∫ x : E k,
      ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2) volume := by
    have h1 : AEMeasurable (fun c' : E k => ∑ i : Fin N, ∫ x : E k,
        ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2) volume := by
      exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin N))
        (fun i _ => hint_meas i)).congr
        (Filter.Eventually.of_forall fun x => by simp only [Finset.sum_apply])
    exact h1.const_mul (2:ℝ)
  have hRHSb : ∀ c' : E k, (2 * ∑ i : Fin N, ∫ x : E k,
      ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)
      ≤ 2 * N * M0 ^ 2 * (Rθ^k * IB) := by
    intro c'
    have hsum : (∑ i : Fin N, ∫ x : E k,
        ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)
        ≤ (N : ℝ) * (M0 ^ 2 * (Rθ^k * IB)) := by
      calc (∑ i : Fin N, ∫ x : E k, ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)
          ≤ ∑ _i : Fin N, M0 ^ 2 * (Rθ^k * IB) :=
            Finset.sum_le_sum fun i _ => hgib i c'
        _ = (Finset.univ.card : ℝ) * (M0 ^ 2 * (Rθ^k * IB)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (N : ℝ) * (M0 ^ 2 * (Rθ^k * IB)) := by rw [Finset.card_univ, Fintype.card_fin]
    calc 2 * (∑ i : Fin N, ∫ x : E k,
            ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)
        ≤ 2 * ((N:ℝ) * (M0 ^ 2 * (Rθ^k * IB))) := by linarith
      _ = 2 * N * M0 ^ 2 * (Rθ^k * IB) := by ring
  have hRHSint : Integrable (fun c' : E k => ballWeight k c R c' * (2 * ∑ i : Fin N,
      ∫ x : E k, ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)) volume :=
    integrable_ballWeight_mul_bound k hk c hRpos hRHSm (by positivity)
      (fun c' => by positivity) hRHSb
  have hstep2 : (∫ c' : E k, ballWeight k c R c' *
        (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ 2))
      ≤ ∫ c' : E k, ballWeight k c R c' * (2 * ∑ i : Fin N, ∫ x : E k,
          ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2) := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun c' =>
        mul_nonneg (ballWeight_pos k c hRpos c').le (by positivity)) hRHSint
      (Filter.Eventually.of_forall fun c' => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (ballWeight_pos k c hRpos c').le
    rw [hRθdef]
    exact local_estimate k hk N hN hR c' g hg
  have hTint : ∀ i : Fin N, Integrable (fun c' : E k => 2 * (ballWeight k c R c' *
      (∫ x : E k, ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2))) volume := by
    intro i
    have hb : ∀ c' : E k, (∫ x : E k,
        ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)
        ≤ 2 * N * M0 ^ 2 * (Rθ^k * IB) := fun c' => (hgib i c').trans (by
      have h3 : (0:ℝ) ≤ M0 ^ 2 * (Rθ^k * IB) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) hIBnn)
      calc M0 ^ 2 * (Rθ^k * IB) = 1 * (M0 ^ 2 * (Rθ^k * IB)) := by rw [one_mul]
        _ ≤ (N:ℝ) * (M0 ^ 2 * (Rθ^k * IB)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hN) h3
        _ ≤ 2 * N * M0 ^ 2 * (Rθ^k * IB) := by
            have h2 : (1:ℝ) ≤ 2 := by norm_num
            nlinarith [h3, hNpos])
    exact (integrable_ballWeight_mul_bound k hk c hRpos (hint_meas i) (by positivity)
      (fun c' => by positivity) hb).const_mul 2
  have hstep3 : (∫ c' : E k, ballWeight k c R c' * (2 * ∑ i : Fin N, ∫ x : E k,
          ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2))
      = 2 * ∑ i : Fin N, ∫ c' : E k, ballWeight k c R c' * (∫ x : E k,
          ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2) := by
    have hcongr : (∫ c' : E k, ballWeight k c R c' * (2 * ∑ i : Fin N, ∫ x : E k,
          ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2))
        = ∫ c' : E k, ∑ i : Fin N, 2 * (ballWeight k c R c' * (∫ x : E k,
            ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
      simp only []
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [hcongr, integral_finsetSum Finset.univ (fun i _ => hTint i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  have hstep4 : ∀ i : Fin N, (∫ c' : E k, ballWeight k c R c' * (∫ x : E k,
          ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2))
      ≤ C3 * R^k * wLpPow k c R 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)) := fun i => by
    rw [hRθdef]
    exact locWeight_piece_transfer k hk c hRpos hC3pos.le
      (fun y => hC3 c hRpos y) (hpiece_meas i) hM0nn (hpiece_bd i)
  have hsumpos : 0 ≤ ∑ i : Fin N, wLpPow k c R 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)) :=
    Finset.sum_nonneg fun i _ => by
      rw [wLpPow_two_eq]
      exact integral_nonneg fun x => by
        exact mul_nonneg (by positivity) (ballWeight_pos k c hRpos x).le
  have hTle : (∑ i : Fin N, ∫ c' : E k, ballWeight k c R c' * (∫ x : E k,
          ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2))
      ≤ C3 * R^k * ∑ i : Fin N, wLpPow k c R 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact hstep4 i
  calc wLpPow k c R 2 (extOp k g 0 1)
      ≤ K1 * (R^k)⁻¹ * (∫ c' : E k, ballWeight k c R c' *
          (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ 2)) := hstep1
    _ ≤ K1 * (R^k)⁻¹ * (∫ c' : E k, ballWeight k c R c' * (2 * ∑ i : Fin N,
          ∫ x : E k, ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = K1 * (R^k)⁻¹ * (2 * ∑ i : Fin N, ∫ c' : E k, ballWeight k c R c' *
          (∫ x : E k, ‖locWeight k c' Rθ x * extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N) x‖ ^ 2)) := by
        rw [hstep3]
    _ ≤ K1 * (R^k)⁻¹ * (2 * (C3 * R^k * ∑ i : Fin N,
          wLpPow k c R 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hTle (by norm_num)) (by positivity)
    _ = (2 * K1 * C3) * ∑ i : Fin N,
          wLpPow k c R 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)) := by
        have hRk : (0:ℝ) < R^k := by positivity
        field_simp
    _ ≤ (2 * ((2:ℝ)^(100*k) / ballVol k 0 1) * C3 + 1) * ∑ i : Fin N,
          wLpPow k c R 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)) := by
        rw [hK1, add_mul, one_mul, add_comm]
        exact le_add_of_nonneg_left (by simpa using hsumpos)


/-- The ball-averaged (`♯`-normalised) form of `l2_decoupling_extOp`: with
`wLpPowAvg = wLpPow/|B|` (BDG's normalisation), the same `L²`-decoupling holds. -/
theorem l2_decoupling_extOp_avg (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (c : E k) (g : ℝ → ℂ),
      IntegrableOn g (Set.Icc (0:ℝ) 1) volume →
      wLpPowAvg k c (N:ℝ) 2 (extOp k g 0 1)
        ≤ C * ∑ i : Fin N, wLpPowAvg k c (N:ℝ) 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)) := by
  obtain ⟨C, hCpos, hC⟩ := l2_decoupling_extOp k hk
  refine ⟨C, hCpos, fun N hN c g hg => ?_⟩
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hV : 0 < ballVol k c (N:ℝ) := ballVol_pos k hk c hNpos
  have h := hC N hN (N:ℝ) (le_refl _) c g hg
  have hsum : (∑ i : Fin N, wLpPowAvg k c (N:ℝ) 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)))
      = (∑ i : Fin N, wLpPow k c (N:ℝ) 2 (extOp k g ((i:ℝ)/N) (((i:ℝ)+1)/N)))
        / ballVol k c (N:ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wLpPowAvg]
  rw [wLpPowAvg, hsum, ← mul_div_assoc, div_le_div_iff_of_pos_right hV]
  exact h


/-- **The interval form of `l2_decoupling_extOp`.**  For an interval `[i/N, j/N]` that is a union of
`1/N`-pieces, the same `L²`-decoupling holds with the sum restricted to those pieces.  (This is the
form in which BDG's `nl3` is applied in the iteration scheme.) -/
theorem l2_decoupling_extOp_Ico (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (R : ℝ), (N:ℝ) ≤ R →
      ∀ (c : E k) (g : ℝ → ℂ), IntegrableOn g (Set.Icc (0:ℝ) 1) volume →
      ∀ (i j : ℕ), i ≤ j → j ≤ N →
      wLpPow k c R 2 (extOp k g ((i:ℝ)/N) ((j:ℝ)/N))
        ≤ C * ∑ l ∈ Finset.Ico i j, wLpPow k c R 2 (extOp k g ((l:ℝ)/N) (((l:ℝ)+1)/N)) := by
  obtain ⟨C, hCpos, hC⟩ := l2_decoupling_extOp k hk
  refine ⟨C, hCpos, ?_⟩
  intro N hN R hR c g hg i j hij hjN
  have hNpos : (0:ℝ) < N := by positivity
  have hdivle : ((i:ℝ)/N) ≤ ((j:ℝ)/N) := by
    rw [div_le_div_iff_of_pos_right hNpos]; exact_mod_cast hij
  set S : Set ℝ := Set.Ioc ((i:ℝ)/N) ((j:ℝ)/N) with hS
  have hSm : MeasurableSet S := measurableSet_Ioc
  set g' : ℝ → ℂ := S.indicator g with hg'def
  have hg'int : IntegrableOn g' (Set.Icc (0:ℝ) 1) volume := hg.indicator hSm
  have hmain := hC N hN R hR c g' hg'int
  -- `g' · e = 1_S · (g · e)` pointwise
  have hpt : ∀ (x : E k) (t : ℝ),
      g' t * momChar k x t = S.indicator (fun t : ℝ => g t * momChar k x t) t := by
    intro x t
    simp only [hg'def, Set.indicator_apply]
    by_cases ht : t ∈ S <;> simp [ht]
  -- (1) the LHS is `E_{[i/N, j/N]}g`
  have hLHS : wLpPow k c R 2 (extOp k g' 0 1)
      = wLpPow k c R 2 (extOp k g ((i:ℝ)/N) ((j:ℝ)/N)) := by
    congr 1
    funext x
    rw [extOp, extOp]
    rw [show (fun t : ℝ => g' t * momChar k x t)
        = S.indicator (fun t : ℝ => g t * momChar k x t) from funext (hpt x)]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      MeasureTheory.setIntegral_indicator hSm]
    have hsub : S ⊆ Set.Ioc (0:ℝ) 1 := by
      intro t ht
      rw [hS, Set.mem_Ioc] at ht
      rw [Set.mem_Ioc]
      have h1 : ((j:ℝ))/N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hjN
      exact ⟨lt_of_le_of_lt (by positivity) ht.1, le_trans ht.2 h1⟩
    rw [Set.inter_eq_right.mpr hsub, ← intervalIntegral.integral_of_le hdivle]
  -- (2) the summands
  have hpiece : ∀ l : ℕ, l < N →
      wLpPow k c R 2 (extOp k g' ((l:ℝ)/N) (((l:ℝ)+1)/N))
        = if i ≤ l ∧ l + 1 ≤ j
          then wLpPow k c R 2 (extOp k g ((l:ℝ)/N) (((l:ℝ)+1)/N)) else 0 := by
    intro l hl
    have hle : ((l:ℝ)/N) ≤ (((l:ℝ)+1)/N) := by
      rw [div_le_div_iff_of_pos_right hNpos]; linarith
    have hpc : ∀ x : E k, extOp k g' ((l:ℝ)/N) (((l:ℝ)+1)/N) x
        = if i ≤ l ∧ l + 1 ≤ j then extOp k g ((l:ℝ)/N) (((l:ℝ)+1)/N) x else 0 := by
      intro x
      rw [extOp, extOp]
      rw [show (fun t : ℝ => g' t * momChar k x t)
          = S.indicator (fun t : ℝ => g t * momChar k x t) from funext (hpt x)]
      rw [intervalIntegral.integral_of_le hle, MeasureTheory.setIntegral_indicator hSm]
      by_cases hc : i ≤ l ∧ l + 1 ≤ j
      · rw [if_pos hc]
        have hsub : Set.Ioc ((l:ℝ)/N) (((l:ℝ)+1)/N) ⊆ S := by
          intro t ht
          rw [Set.mem_Ioc] at ht
          rw [hS, Set.mem_Ioc]
          have h1 : ((i:ℝ)/N) ≤ ((l:ℝ)/N) := by
            rw [div_le_div_iff_of_pos_right hNpos]; exact_mod_cast hc.1
          have h2 : (((l:ℝ)+1)/N) ≤ ((j:ℝ)/N) := by
            rw [div_le_div_iff_of_pos_right hNpos]; exact_mod_cast hc.2
          exact ⟨lt_of_le_of_lt h1 ht.1, le_trans ht.2 h2⟩
        rw [Set.inter_eq_left.mpr hsub, ← intervalIntegral.integral_of_le hle]
      · rw [if_neg hc]
        have hempty : Set.Ioc ((l:ℝ)/N) (((l:ℝ)+1)/N) ∩ S = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          rw [Set.mem_inter_iff, Set.mem_Ioc, hS, Set.mem_Ioc] at ht
          obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ht
          rw [not_and_or] at hc
          rcases hc with hc | hc
          · have h5 : l + 1 ≤ i := by omega
            have : (((l:ℝ)+1)/N) ≤ ((i:ℝ)/N) := by
              rw [div_le_div_iff_of_pos_right hNpos]; exact_mod_cast h5
            exact absurd (lt_of_le_of_lt this h3) (not_lt.mpr h2)
          · have hj : j ≤ l := by omega
            have : ((j:ℝ)/N) ≤ ((l:ℝ)/N) := by
              rw [div_le_div_iff_of_pos_right hNpos]; exact_mod_cast hj
            exact absurd (lt_of_le_of_lt this h1) (not_lt.mpr h4)
        rw [hempty, MeasureTheory.setIntegral_empty]
    by_cases hc : i ≤ l ∧ l + 1 ≤ j
    · rw [if_pos hc]
      congr 1
      funext x
      rw [hpc x, if_pos hc]
    · rw [if_neg hc]
      have hz : (extOp k g' ((l:ℝ)/N) (((l:ℝ)+1)/N)) = fun _ : E k => 0 :=
        funext fun x => by rw [hpc x, if_neg hc]
      rw [hz]
      simp [wLpPow]
  -- (3) collapse the sum
  have hsum : (∑ l ∈ Finset.range N, wLpPow k c R 2 (extOp k g' ((l:ℝ)/N) (((l:ℝ)+1)/N)))
      = ∑ l ∈ Finset.Ico i j, wLpPow k c R 2 (extOp k g ((l:ℝ)/N) (((l:ℝ)+1)/N)) := by
    rw [Finset.sum_congr rfl (fun l hl => hpiece l (Finset.mem_range.mp hl)),
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    refine Finset.ext fun l => ?_
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hlN, hc1, hc2⟩
      exact ⟨hc1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨lt_of_lt_of_le h2 hjN, h1, by omega⟩
  rw [Fin.sum_univ_eq_sum_range
    (fun l : ℕ => wLpPow k c R 2 (extOp k g' ((l:ℝ)/N) (((l:ℝ)+1)/N))) N] at hmain
  rw [hLHS, hsum] at hmain
  exact hmain

end Submission.Vinogradov
