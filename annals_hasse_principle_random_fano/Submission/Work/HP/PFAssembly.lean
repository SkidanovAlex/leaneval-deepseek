import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.IntForm
import Submission.Work.HP.PFDefs
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.evaldefs
import Submission.Work.HP.bigW_le_pow

/-!
# The product-factors bound (node N13): final assembly

`product_factors_of` is the last step of the paper's Lemma 5.1 and of node N13: it takes

* `htube`  : the tube threshold `Work.HP.HP2.tube_ok_threshold`,
* `hclass` : the per-residue-class lower bound `Work.HP.HP2.class_count_lower`,
* `hsigma` : the summation over the `σ W^n` good classes `Work.HP.HP2.primConeSet_sigma_lower`,
* `hNV`    : `Work.HP.HP2.NVloc_ge_ncard` (rewritten in terms of `primConeSet`),
* `hevent` : `Work.HP.HP2.PF_eventually`,

and produces `σ · τ ≤ C · N_V^loc(B)/φ` for `B = A φ`, `A ≥ A₀`.  The only mathematics here is the
final chain of inequalities:

`N_V^loc ≥ (1/2)(α W/‖a‖)·#primConeSet/(√N R^d) ≥ (1/2)(α W/‖a‖)·(1/8)σ·vol/W/(√N R^d)`
`       = (1/16)σ τ R^{n+1}/(‖a‖ √N R^d) = (1/16)σ τ R^{n+1-d}/(‖a‖√N)`
`       = (1/16)σ τ B/(‖a‖√N) ≥ (1/16)σ τ φ/√N`,
using `vol(coneRegion R) = R^{n+1}τ/α` (`Work.HP.volume_coneRegion`), `R^{n+1-d} = B`,
`B = Aφ` and `‖a‖ ≤ A`.

See `Submission/Work/HP/PF_PLAN.md` §4.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators Pointwise

namespace Work.HP

/-- A primitive vector is nonzero. -/
private lemma isPrim_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : IsPrim v) : v ≠ 0 := by
  intro h0
  have h1 : Finset.univ.gcd (0 : ι → ℤ) = 1 := by rw [← h0]; exact h
  have hz : Finset.univ.gcd (0 : ι → ℤ) = 0 := Finset.gcd_eq_zero_iff.mpr (fun i _ => rfl)
  rw [hz] at h1
  exact one_ne_zero h1.symm

/-- The Euclidean norm of a nonzero integer vector is positive. -/
lemma pf_eNorm_pos_of_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) : 0 < eNorm v := by
  rw [eNorm, Real.sqrt_pos]
  refine lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Ne.symm ?_)
  intro hsum
  exact hv (funext fun i => by
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsum i
      (Finset.mem_univ i)
    exact_mod_cast (sq_eq_zero_iff.mp h2))

/-- `(B^{1/s})^t = B^{t/s}` for `B > 0` and `s ≠ 0`. -/
lemma rpow_one_div_pow (B s t : ℝ) (hB : 0 < B) (hs : s ≠ 0) :
    (B ^ (1 / s)) ^ t = B ^ (t / s) := by
  rw [← Real.rpow_mul hB.le (1 / s) t]
  congr 1
  field_simp

/-- **The product-factors bound (paper's Lemma 5.1), final assembly.** -/
theorem product_factors_of (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (m : ℕ) (κ : ℝ) (hκ : 1 ≤ κ)
    (htube : ∀ᶠ B in atTop, ∀ (a : Mon d n → ℤ) (T : ℝ),
      a ≠ 0 → RealSol d n a → 1 ≤ T →
      (bigW (wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ T →
      TubeOk d n a (Real.log B) T (bigW (wOf B) : ℝ))
    (hclass : ∀ᶠ B in atTop, ∀ (a : Mon d n → ℤ) (b : Fin (n + 1) → ℤ),
      a ≠ 0 → RealSol d n a →
      (∀ i, 0 ≤ b i ∧ b i < bigW (wOf B)) →
      (∀ p : ℕ, p.Prime → p ∣ bigW (wOf B) → ∃ i, ¬ (p : ℤ) ∣ b i) →
      ((bigW (wOf B) : ℤ) ∣ formEval d n a b) →
      (∀ T : ℝ, 1 ≤ T → (bigW (wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ T →
        TubeOk d n a (Real.log B) T (bigW (wOf B) : ℝ)) →
      (1 / 8) * (volume (coneRegion d n a (Real.log B)
          (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
        / (bigW (wOf B) : ℝ) ^ (n + 1)
        ≤ ((classPrimSet d n a b (bigW (wOf B)) (Real.log B)
            (B ^ (1 / ((n : ℝ) + 1 - d)))).ncard : ℝ))
    (hsigma : ∀ᶠ B in atTop, ∀ (a : Mon d n → ℤ),
      a ≠ 0 → RealSol d n a →
      (∀ (b : Fin (n + 1) → ℤ),
        (∀ i, 0 ≤ b i ∧ b i < bigW (wOf B)) →
        (∀ p : ℕ, p.Prime → p ∣ bigW (wOf B) → ∃ i, ¬ (p : ℤ) ∣ b i) →
        ((bigW (wOf B) : ℤ) ∣ formEval d n a b) →
        (1 / 8) * (volume (coneRegion d n a (Real.log B)
            (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
          / (bigW (wOf B) : ℝ) ^ (n + 1)
          ≤ ((classPrimSet d n a b (bigW (wOf B)) (Real.log B)
              (B ^ (1 / ((n : ℝ) + 1 - d)))).ncard : ℝ)) →
      (1 / 8) * sigmaLoc d n a (bigW (wOf B))
          * (volume (coneRegion d n a (Real.log B)
              (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
        / (bigW (wOf B) : ℝ)
        ≤ ((primConeSet d n a (Real.log B) (B ^ (1 / ((n : ℝ) + 1 - d)))
            (bigW (wOf B))).ncard : ℝ))
    (hNV : ∀ (a : Mon d n → ℤ) (B R : ℝ),
      R = B ^ (1 / ((n : ℝ) + 1 - d)) → 0 < R → 0 < eNorm a →
      (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
        (((primConeSet d n a (Real.log B) R (bigW (wOf B))).ncard : ℝ) /
          (Real.sqrt ((NN d n : ℕ) : ℝ) * R ^ d)) ≤ NVloc d n a B)
    (hevent : ∀ (m : ℕ) (κ : ℝ), 0 < κ → ∀ᶠ B in atTop,
      1 ≤ Real.log B ∧ 8 ≤ wOf B ∧
        (bigW (wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ B ^ (1 / ((n : ℝ) + 1 - d))) :
    ∃ C A₀ : ℝ, 0 < C ∧ ∀ A φ : ℝ, A₀ ≤ A → 1 < φ → ∀ a : Mon d n → ℤ,
      IsPrim a → eNorm a ≤ A → RealSol d n a →
        sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ))
          ≤ C * NVloc d n a (A * φ) / φ := by
  set N : ℝ := Real.sqrt ((NN d n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    have h1 : (0 : ℝ) < (NN d n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_NN d n))
    exact Real.sqrt_pos.mpr h1
  have hmain : ∀ᶠ B in atTop, ∀ a : Mon d n → ℤ, IsPrim a → RealSol d n a →
      (1 / 16) * sigmaLoc d n a (bigW (wOf B)) * tauArch d n (toR a) (Real.log B)
        * (B / eNorm a) / N ≤ NVloc d n a B := by
    filter_upwards [hevent 0 1 (by norm_num), eventually_ge_atTop (1 : ℝ), htube, hclass, hsigma]
      with B hB hB1 htubeB hclassB hsigmaB
    intro a hprim hsol
    obtain ⟨hlog1, hw8, -⟩ := hB
    have hα : 0 < Real.log B := lt_of_lt_of_le zero_lt_one hlog1
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
    have hW1 : 1 ≤ bigW (wOf B) := one_le_bigW _
    have hWpos : 0 < (bigW (wOf B) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hW1)
    have ha_ne : a ≠ 0 := isPrim_ne_zero hprim
    have hepos : 0 < eNorm a := pf_eNorm_pos_of_ne_zero ha_ne
    have hs1 : (1 : ℝ) ≤ (n : ℝ) + 1 - d := by
      have : (d : ℝ) ≤ n := by exact_mod_cast hdn
      linarith
    have hspos : 0 < (n : ℝ) + 1 - d := lt_of_lt_of_le zero_lt_one hs1
    have hsne : (n : ℝ) + 1 - d ≠ 0 := ne_of_gt hspos
    have hRpos : 0 < B ^ (1 / ((n : ℝ) + 1 - d)) := Real.rpow_pos_of_pos hBpos _
    have htb : ∀ T : ℝ, 1 ≤ T →
        (bigW (wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ T →
        TubeOk d n a (Real.log B) T (bigW (wOf B) : ℝ) :=
      fun T hT hTT => htubeB a T ha_ne hsol hT hTT
    have hperclass : ∀ (b : Fin (n + 1) → ℤ),
        (∀ i, 0 ≤ b i ∧ b i < bigW (wOf B)) →
        (∀ p : ℕ, p.Prime → p ∣ bigW (wOf B) → ∃ i, ¬ (p : ℤ) ∣ b i) →
        ((bigW (wOf B) : ℤ) ∣ formEval d n a b) →
        (1 / 8) * (volume (coneRegion d n a (Real.log B)
            (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
          / (bigW (wOf B) : ℝ) ^ (n + 1)
          ≤ ((classPrimSet d n a b (bigW (wOf B)) (Real.log B)
              (B ^ (1 / ((n : ℝ) + 1 - d)))).ncard : ℝ) :=
      fun b hbox hprimW hdiv => hclassB a b ha_ne hsol hbox hprimW hdiv htb
    have hsig := hsigmaB a ha_ne hsol hperclass
    have hnv := hNV a B (B ^ (1 / ((n : ℝ) + 1 - d))) rfl hRpos hepos
    have hRs : (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) + 1 - d) = B := by
      rw [rpow_one_div_pow B ((n : ℝ) + 1 - d) ((n : ℝ) + 1 - d) hBpos hsne,
        div_self hsne, Real.rpow_one]
    have hRn1 : (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (n + 1)
        = (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d * B := by
      have h1 : (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (n + 1)
          = (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((d : ℝ) + ((n : ℝ) + 1 - d)) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        ring
      rw [h1, Real.rpow_add hRpos, ← Real.rpow_natCast, hRs, Real.rpow_natCast]
    have hvol : (volume (coneRegion d n a (Real.log B)
          (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
        = (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (n + 1) * tauArch d n (toR a) (Real.log B)
            / Real.log B :=
      volume_coneRegion d n a (α := Real.log B) (T := B ^ (1 / ((n : ℝ) + 1 - d)))
        hα hRpos
    have hαne : Real.log B ≠ 0 := ne_of_gt hα
    have hWne : (bigW (wOf B) : ℝ) ≠ 0 := ne_of_gt hWpos
    have hene : eNorm a ≠ 0 := ne_of_gt hepos
    have hNne : N ≠ 0 := ne_of_gt hNpos
    have hRne : (B ^ (1 / ((n : ℝ) + 1 - d))) ≠ 0 := ne_of_gt hRpos
    have hRdn : (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d ≠ 0 := pow_ne_zero _ hRne
    have hmul1 : (1 / 16) * sigmaLoc d n a (bigW (wOf B)) * tauArch d n (toR a) (Real.log B)
          * (B / eNorm a) / N
        = (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
            ((1 / 8) * sigmaLoc d n a (bigW (wOf B))
                * (volume (coneRegion d n a (Real.log B)
                    (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
                / (bigW (wOf B) : ℝ)
              / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d)) := by
      rw [hvol, hRn1]
      field_simp
      ring
    have hmul2 : (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
            ((1 / 8) * sigmaLoc d n a (bigW (wOf B))
                * (volume (coneRegion d n a (Real.log B)
                    (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
                / (bigW (wOf B) : ℝ)
              / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d))
        ≤ (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
            (((primConeSet d n a (Real.log B) (B ^ (1 / ((n : ℝ) + 1 - d)))
                (bigW (wOf B))).ncard : ℝ)
              / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d)) := by
      have hc : 0 ≤ (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a)
          / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d) := by positivity
      have h4 := mul_le_mul_of_nonneg_left hsig hc
      have e1 : (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
            ((1 / 8) * sigmaLoc d n a (bigW (wOf B))
                * (volume (coneRegion d n a (Real.log B)
                    (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
                / (bigW (wOf B) : ℝ)
              / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d))
          = (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a)
              / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d)
              * ((1 / 8) * sigmaLoc d n a (bigW (wOf B))
                  * (volume (coneRegion d n a (Real.log B)
                      (B ^ (1 / ((n : ℝ) + 1 - d))))).toReal
                  / (bigW (wOf B) : ℝ)) := by ring
      have e2 : (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
            (((primConeSet d n a (Real.log B) (B ^ (1 / ((n : ℝ) + 1 - d)))
                (bigW (wOf B))).ncard : ℝ)
              / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d))
          = (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a)
              / (N * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d)
              * ((primConeSet d n a (Real.log B) (B ^ (1 / ((n : ℝ) + 1 - d)))
                  (bigW (wOf B))).ncard : ℝ) := by ring
      rw [e1, e2]
      exact h4
    linarith [hmul1.le, hmul1.ge, hmul2, hnv]

  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hmain
  refine ⟨16 * N, max A₀ 1, by positivity, ?_⟩
  intro A φ hA hφ a hprim hnorm hsol
  have hA0 : A₀ ≤ A := le_trans (le_max_left _ _) hA
  have hA1 : (1 : ℝ) ≤ A := le_trans (le_max_right _ _) hA
  have hφpos : 0 < φ := lt_trans zero_lt_one hφ
  have hAle : A ≤ A * φ := by nlinarith
  have hkey := hA₀ (A * φ) (le_trans hA0 hAle) a hprim hsol
  have hepos : 0 < eNorm a := pf_eNorm_pos_of_ne_zero (isPrim_ne_zero hprim)
  have hσnn : 0 ≤ sigmaLoc d n a (bigW (wOf (A * φ))) := by
    rw [sigmaLoc]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hτnn : 0 ≤ tauArch d n (toR a) (Real.log (A * φ)) := by
    rw [tauArch]
    exact mul_nonneg (Real.log_nonneg (by nlinarith [hA1, hφpos])) ENNReal.toReal_nonneg
  have hquot : φ ≤ (A * φ) / eNorm a := by
    rw [le_div_iff₀ hepos]
    nlinarith
  have hc : 0 ≤ (1 / 16) * sigmaLoc d n a (bigW (wOf (A * φ)))
      * tauArch d n (toR a) (Real.log (A * φ)) / N :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσnn) hτnn) hNpos.le
  have hstep : (1 / 16) * (sigmaLoc d n a (bigW (wOf (A * φ)))
        * tauArch d n (toR a) (Real.log (A * φ))) * φ / N
      ≤ NVloc d n a (A * φ) := by
    have h1 : ((1 / 16) * sigmaLoc d n a (bigW (wOf (A * φ)))
          * tauArch d n (toR a) (Real.log (A * φ)) / N) * φ
        ≤ ((1 / 16) * sigmaLoc d n a (bigW (wOf (A * φ)))
            * tauArch d n (toR a) (Real.log (A * φ)) / N) * ((A * φ) / eNorm a) :=
      mul_le_mul_of_nonneg_left hquot hc
    have e3 : ((1 / 16) * sigmaLoc d n a (bigW (wOf (A * φ)))
          * tauArch d n (toR a) (Real.log (A * φ)) / N) * ((A * φ) / eNorm a)
        = (1 / 16) * sigmaLoc d n a (bigW (wOf (A * φ)))
            * tauArch d n (toR a) (Real.log (A * φ)) * ((A * φ) / eNorm a) / N := by ring
    have h2 : ((1 / 16) * sigmaLoc d n a (bigW (wOf (A * φ)))
          * tauArch d n (toR a) (Real.log (A * φ)) / N) * ((A * φ) / eNorm a)
        ≤ NVloc d n a (A * φ) := by
      rw [e3]
      exact hkey
    have e4 : (1 / 16) * (sigmaLoc d n a (bigW (wOf (A * φ)))
          * tauArch d n (toR a) (Real.log (A * φ))) * φ / N
        = ((1 / 16) * sigmaLoc d n a (bigW (wOf (A * φ)))
            * tauArch d n (toR a) (Real.log (A * φ)) / N) * φ := by ring
    rw [e4]
    exact le_trans h1 h2
  have hφne : φ ≠ 0 := ne_of_gt hφpos
  have hNne : N ≠ 0 := ne_of_gt hNpos
  calc sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ))
      = (1 / 16) * (sigmaLoc d n a (bigW (wOf (A * φ)))
            * tauArch d n (toR a) (Real.log (A * φ))) * φ / N * (16 * N / φ) := by
        field_simp
    _ ≤ NVloc d n a (A * φ) * (16 * N / φ) := mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = 16 * N * NVloc d n a (A * φ) / φ := by ring

end Work.HP
