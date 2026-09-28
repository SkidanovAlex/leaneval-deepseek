import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDEstimates.ell44_56_bound
import Submission.Work.HP.MDEstimates.ell34_bound
import Submission.Work.HP.MDEstimates.ballCount_R0_j0
import Submission.Work.HP.MDEstimates.detGam_lower
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.MDEstimates.muXY_le
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.Sig2.key_lemma_two_vectors
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.le_mul_log_of_div_log_le
import Submission.Work.HP.Sig2.log_pow_le_rpow
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.lam_basic
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.Q44Child.witness_class_count
import Submission.Work.HP.MDEstimates.dyadic_sum_le
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.MinGeomRpowSumAux
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.DyadicRpowLeIndicatorSum
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.CountXYD3
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.MDEstimates

open Work.HP

/-! ## A Fintype-free dyadic layer-cake sum

`DyadicMinSumFinset` of `Sigma2_44_I_lo_aux` carries an unused `Fintype` hypothesis, so it
cannot be instantiated for a sum over a `Finset` in an infinite type such as
`(Fin 5 → ℤ) × (Fin 5 → ℤ)`.  The same proof yields the following form. -/

theorem dyadic_min_sum_finset_free {ι : Type*} [DecidableEq ι] (m s : ℝ) (hm : 0 < m)
    (hms : m < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : Finset ι) (D : ι → ℝ) (Λ N C : ℝ), 1 ≤ Λ →
      (∀ p ∈ F, 1 ≤ D p) → (∀ p ∈ F, D p ≤ Λ) → 0 ≤ N → 0 ≤ C →
      (∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => D p ≤ Δ)).card : ℝ) ≤ N) →
      (∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => D p ≤ Δ)).card : ℝ) ≤ C * Δ ^ s) →
      (∑ p ∈ F, (D p) ^ (-m)) ≤ K * C ^ (m / s) * N ^ (1 - m / s) := by
  obtain ⟨K1, hK1pos, hK1⟩ := Sigma2_44_I_lo_aux.MinGeomRpowSumAux hm hms
  refine ⟨K1 * (2:ℝ)^m, by positivity, ?_⟩
  intro F D Λ N C hΛ hD1 hDΛ hN hC hN1 hN2
  set J : ℕ := ⌈Real.logb 2 Λ⌉₊ with hJdef
  have hpt : ∀ p ∈ F, (D p)^(-m) ≤ ∑ j ∈ Finset.range (J+1),
      (2:ℝ)^(-(j:ℝ)*m) * (if D p < (2:ℝ)^(j+1) then (1:ℝ) else 0) := by
    intro p hp
    refine Sigma2_44_I_lo_aux.DyadicRpowLeIndicatorSum (D p) (hD1 p hp) m (le_of_lt hm) J ?_
    exact (dyadic_index_props (D p) Λ (hD1 p hp) (hDΛ p hp)).2.2
  have hstep1 : (∑ p ∈ F, (D p)^(-m)) ≤ ∑ p ∈ F, ∑ j ∈ Finset.range (J+1),
      (2:ℝ)^(-(j:ℝ)*m) * (if D p < (2:ℝ)^(j+1) then (1:ℝ) else 0) :=
    Finset.sum_le_sum hpt
  have hstep2 : (∑ p ∈ F, ∑ j ∈ Finset.range (J+1),
        (2:ℝ)^(-(j:ℝ)*m) * (if D p < (2:ℝ)^(j+1) then (1:ℝ) else 0))
      = ∑ j ∈ Finset.range (J+1),
        (2:ℝ)^(-(j:ℝ)*m) * ((F.filter (fun p => D p < (2:ℝ)^(j+1))).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_boole]
  have hcard : ∀ j ∈ Finset.range (J+1),
      ((F.filter (fun p => D p < (2:ℝ)^(j+1))).card : ℝ)
        ≤ min N (C * ((2:ℝ)^(j+1))^s) := by
    intro j hj
    have hΔ1 : (1:ℝ) ≤ (2:ℝ)^(j+1) := one_le_pow₀ (by norm_num)
    have hsub : F.filter (fun p => D p < (2:ℝ)^(j+1))
        ⊆ F.filter (fun p => D p ≤ (2:ℝ)^(j+1)) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, le_of_lt hp.2⟩
    have hc1 : ((F.filter (fun p => D p < (2:ℝ)^(j+1))).card : ℝ)
        ≤ ((F.filter (fun p => D p ≤ (2:ℝ)^(j+1))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact le_min (le_trans hc1 (hN1 _ hΔ1)) (le_trans hc1 (hN2 _ hΔ1))
  have hstep3 : ∑ j ∈ Finset.range (J+1),
        (2:ℝ)^(-(j:ℝ)*m) * ((F.filter (fun p => D p < (2:ℝ)^(j+1))).card : ℝ)
      ≤ ∑ j ∈ Finset.range (J+1),
        (2:ℝ)^(-(j:ℝ)*m) * min N (C * ((2:ℝ)^(j+1))^s) :=
    Finset.sum_le_sum
      (fun j hj => mul_le_mul_of_nonneg_left (hcard j hj) (Real.rpow_nonneg (by norm_num) _))
  have hstep4 : ∑ j ∈ Finset.range (J+1),
        (2:ℝ)^(-(j:ℝ)*m) * min N (C * ((2:ℝ)^(j+1))^s)
      = ∑ j ∈ Finset.range (J+1),
        min N ((C * (2:ℝ)^s) * (2:ℝ)^((j:ℝ)*s)) * (2:ℝ)^(-(j:ℝ)*m) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h2 : ((2:ℝ)^(j+1))^s = (2:ℝ)^s * (2:ℝ)^((j:ℝ)*s) := by
      rw [← Real.rpow_natCast (2:ℝ) (j+1)]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (((j+1:ℕ):ℝ)) s]
      rw [show (((j+1:ℕ):ℝ))*s = (j:ℝ)*s + s by push_cast; ring]
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      ring
    have h3 : C * ((2:ℝ)^s * (2:ℝ)^((j:ℝ)*s)) = (C * (2:ℝ)^s) * (2:ℝ)^((j:ℝ)*s) := by ring
    rw [h2, h3]
    ring
  have hstep5 := hK1 N (C * (2:ℝ)^s) J hN (by positivity)
  have hfinal : K1 * (C * (2:ℝ)^s) ^ (m/s) * N ^ (1 - m/s)
      = (K1 * (2:ℝ)^m) * C^(m/s) * N^(1-m/s) := by
    have hsne : s ≠ 0 := ne_of_gt (lt_trans hm hms)
    rw [Real.mul_rpow hC (Real.rpow_nonneg (by norm_num) s)]
    have h2s : ((2:ℝ)^s)^(m/s) = (2:ℝ)^m := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) s (m/s)]
      rw [show s * (m/s) = m by rw [mul_div_cancel₀ m hsne]]
    rw [h2s]; ring
  have hchain : (∑ p ∈ F, (D p)^(-m)) ≤ K1 * (C * (2:ℝ)^s) ^ (m/s) * N ^ (1 - m/s) := by
    refine le_trans hstep1 ?_
    rw [hstep2]
    refine le_trans hstep3 ?_
    rw [hstep4]
    exact hstep5
  exact hchain.trans hfinal.le


/-
# `Sigma2_44_I_lo`

The `𝔡₃ ≤ A^{1/20}` part of the case-`I` sum for `(d,n) = (4,4)`.

Route: for every pair `p` of the region,
`pairS₀ ≤ Kp (A^{65} μ³/det Γ + (2A)^{55}((2A/λ_{56})^{9} + 1))` (Lemma R0, second part,
`ballCount_R0_j0` with `R = 68`, `j₀ = 55`, `j = 3`, `M = 1/2`, `J = λ_{56}(Γ)/2`), and
`μ³/det Γ ≤ 48³ /(Cdet · 𝔡₃ · ‖x‖‖y‖)`.  Summing over the region: the `𝔡₃`-part is bounded
with the counting function `#{‖x‖‖y‖𝔡₃ ≤ Δ} ≤ K Δ⁴` (`CountXYD3`) and the `λ_{56}`-part with
`ℓ^{(56)} ≤ K Z⁴Δ²⁴J¹⁵` (`ell44_56_bound`) and `#Ω ≤ K B⁶Δ³(log)²` (`ell34_bound`), the two
layer-cake sums being `DyadicMinSumFinset`.  The exponent arithmetic is `arith_three`.
-/

/-! ## Elementary facts -/

private lemma eNorm_pos_of_ne_zero {v : Fin 5 → ℤ} (hv : v ≠ 0) : 0 < eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext fun i => by simpa using h i)
  have hne : ((v i : ℤ) : ℝ) ≠ 0 := by
    intro h0
    exact hi (by exact_mod_cast h0)
  have h1 : (0:ℝ) < (((v i : ℤ)) : ℝ)^2 := by positivity
  have h2 : (((v i : ℤ)) : ℝ)^2 ≤ ∑ j, (((v j : ℤ)) : ℝ)^2 :=
    Finset.single_le_sum (f := fun j : Fin 5 => (((v j : ℤ)) : ℝ)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [eNorm]
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le h1 h2)

private lemma one_le_eNorm {v : Fin 5 → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext fun i => by simpa using h i)
  have h1 : (1:ℤ) ≤ (v i)^2 := by
    rcases lt_or_gt_of_ne hi with h | h <;> nlinarith
  have h2 : ((v i : ℤ) : ℝ)^2 ≤ ∑ j, (((v j : ℤ)) : ℝ)^2 :=
    Finset.single_le_sum (f := fun j : Fin 5 => (((v j : ℤ)) : ℝ)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : (1:ℝ) ≤ ∑ j, (((v j : ℤ)) : ℝ)^2 := by
    have h4 : (1:ℝ) ≤ ((v i : ℤ) : ℝ)^2 := by exact_mod_cast h1
    linarith
  calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (∑ j, (((v j : ℤ)) : ℝ)^2) := Real.sqrt_le_sqrt h3
    _ = eNorm v := rfl

private lemma ne_zero_of_LI1 {v w : Fin 5 → ℤ} (h : LinearIndependent ℤ ![v, w]) : v ≠ 0 := by
  intro h0
  rw [h0] at h
  rw [LinearIndependent.pair_iff] at h
  exact one_ne_zero (h 1 0 (by simp)).1

private lemma ne_zero_of_LI2 {v w : Fin 5 → ℤ} (h : LinearIndependent ℤ ![v, w]) : w ≠ 0 := by
  intro h0
  rw [h0] at h
  rw [LinearIndependent.pair_iff] at h
  exact one_ne_zero (h 0 1 (by simp)).2

private lemma eNorm_le_of_mem_Xi {B : ℝ} {v : Fin 5 → ℤ}
    (hv : eNorm v ≤ B ^ (1 / ((4:ℝ) + 1 - 4))) : eNorm v ≤ B := by
  rwa [show (1:ℝ) / ((4:ℝ) + 1 - 4) = 1 by norm_num, Real.rpow_one] at hv

/-- The index set of the `𝔡₃ ≤ A^{1/20}` part of the case-`I` sum. -/
private def SLset (A B : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p ∈ Omega 4 4 B ∧ ¬ (muXY 4 p.1 p.2 ≤ A) ∧
      ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
      dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1 : ℝ) / 20)}

private lemma SLset_eq_state (A B : ℝ) :
    SLset A B = {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧
          ¬ (muXY 4 p.1 p.2 ≤ A) ∧
          ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
              ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
          dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1 : ℝ) / 20)} := rfl

private lemma SLset_finite (A B : ℝ) : (SLset A B).Finite :=
  (MDBasic.finite_sets 4 4 A B (fun _ => True)).2.2.subset (fun p hp => hp.1)

/-- `pairS0` is at most the number of lattice points of `Γ_{x,y}` in the ball of radius `A`. -/
private lemma pairS0_le_ballCount (A : ℝ) (p : (Fin 5 → ℤ) × (Fin 5 → ℤ)) :
    pairS0 4 4 A p ≤ (ballCount (Gam 4 4 p.1 p.2) A : ℝ) := by
  have hsub : ({a : Mon 4 4 → ℤ | a ∈ primSet 4 4 A (fun _ => True) ∧
      formEval 4 4 a p.1 = 0 ∧ formEval 4 4 a p.2 = 0})
      ⊆ {a : Mon 4 4 → ℤ | a ∈ Gam 4 4 p.1 p.2 ∧ eNorm a ≤ A} := by
    rintro a ⟨⟨-, h2, -⟩, h3, h4⟩
    exact ⟨(MDBasic.mem_Gam_iff 4 4 p.1 p.2 a).mpr ⟨h3, h4⟩, h2⟩
  have hfin : ({a : Mon 4 4 → ℤ | a ∈ Gam 4 4 p.1 p.2 ∧ eNorm a ≤ A}).Finite :=
    (MDBasic.finite_eNorm_le (ι := Mon 4 4) A).subset (fun a ha => ha.2)
  have h := Set.ncard_le_ncard hsub hfin
  have h1 : pairS0 4 4 A p = (({a : Mon 4 4 → ℤ | a ∈ primSet 4 4 A (fun _ => True) ∧
      formEval 4 4 a p.1 = 0 ∧ formEval 4 4 a p.2 = 0}).ncard : ℝ) := rfl
  have h2 : (ballCount (Gam 4 4 p.1 p.2) A : ℝ) =
      (({a : Mon 4 4 → ℤ | a ∈ Gam 4 4 p.1 p.2 ∧ eNorm a ≤ A}).ncard : ℝ) := rfl
  rw [h1, h2]
  exact_mod_cast h

/-- In case `I` (`𝔡₂³ > 𝔡₃‖x‖‖y‖`) the maximum in `muXY` is the first argument. -/
private lemma muXY_eq_of_caseI {x y : Fin 5 → ℤ}
    (hd2pos : 0 < dmin 2 ({x, y} : Set (Fin 5 → ℤ)))
    (hd3pos : 0 < dmin 3 ({x, y} : Set (Fin 5 → ℤ)))
    (hcase : ¬ (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({x, y} : Set (Fin 5 → ℤ)) * (eNorm x * eNorm y))) :
    muXY 4 x y = 48 * (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) / dmin 3 ({x, y} : Set (Fin 5 → ℤ))) := by
  have h := not_le.mp hcase
  have hmax : max (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) / dmin 3 ({x, y} : Set (Fin 5 → ℤ)))
      (eNorm x * eNorm y / dmin 2 ({x, y} : Set (Fin 5 → ℤ)) ^ 2)
      = dmin 2 ({x, y} : Set (Fin 5 → ℤ)) / dmin 3 ({x, y} : Set (Fin 5 → ℤ)) := by
    refine max_eq_left ?_
    rw [div_le_div_iff₀ (pow_pos hd2pos 2) hd3pos]
    nlinarith [h]
  rw [muXY, hmax]
  norm_num

/-- `μ³ / det Γ ≤ 48³/(Cdet 𝔡₃ ‖x‖‖y‖)` in case `I`. -/
private lemma mu_cube_div_det (Cdet : ℝ)
    (hCdet : ∀ x y : Fin 5 → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      Cdet * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * eNorm x ^ 3 * eNorm y ^ 3
        ≤ detL (Gam 4 4 x y))
    (hCdetpos : 0 < Cdet)
    {x y : Fin 5 → ℤ} (hx : IsPrim x) (hy : IsPrim y) (hLI : LinearIndependent ℤ ![x, y])
    (hcase : ¬ (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({x, y} : Set (Fin 5 → ℤ)) * (eNorm x * eNorm y))) :
    (muXY 4 x y) ^ 3 / detL (Gam 4 4 x y)
      ≤ 48 ^ 3 * (1 / (eNorm x * eNorm y * dmin 3 ({x, y} : Set (Fin 5 → ℤ)))) / Cdet := by
  have hdf := dmin_facts 4 (by norm_num)
  set d2 := dmin 2 ({x, y} : Set (Fin 5 → ℤ)) with hd2
  set d3 := dmin 3 ({x, y} : Set (Fin 5 → ℤ)) with hd3
  have hd2pos : 0 < d2 := lt_of_lt_of_le zero_lt_one (hdf.1 x y hLI)
  have hd3pos : 0 < d3 := lt_of_lt_of_le zero_lt_one (hdf.2.2.1 x y hLI)
  have hXpos : 0 < eNorm x := eNorm_pos_of_ne_zero (ne_zero_of_LI1 hLI)
  have hYpos : 0 < eNorm y := eNorm_pos_of_ne_zero (ne_zero_of_LI2 hLI)
  have hXn : (0:ℝ) ≤ eNorm x := le_of_lt hXpos
  have hYn : (0:ℝ) ≤ eNorm y := le_of_lt hYpos
  have hmu_eq : muXY 4 x y = 48 * (d2 / d3) := by
    have hmain := muXY_eq_of_caseI (x := x) (y := y) (by rw [← hd2]; exact hd2pos)
      (by rw [← hd3]; exact hd3pos) (by rw [← hd2, ← hd3]; exact hcase)
    rw [hmain, hd2, hd3]
  have hmuXYle : muXY 4 x y ≤ 48 * (eNorm x * eNorm y) := by
    have h := muXY_le 4 4 x y hx hy hLI
    norm_num at h
    exact h
  have hd2le2 : d2 ≤ (eNorm x * eNorm y) * d3 := by
    have h1 : d2 / d3 ≤ eNorm x * eNorm y := by
      have h2 : 48 * (d2 / d3) ≤ 48 * (eNorm x * eNorm y) := by rw [← hmu_eq]; exact hmuXYle
      nlinarith
    rw [div_le_iff₀ hd3pos] at h1
    linarith
  have hdet : Cdet * d2 * (eNorm x) ^ 3 * (eNorm y) ^ 3 ≤ detL (Gam 4 4 x y) :=
    hCdet x y hx hy hLI
  have hdet' : Cdet * d2 * (eNorm x * eNorm y) ^ 3 ≤ detL (Gam 4 4 x y) := by
    have h : (eNorm x) ^ 3 * (eNorm y) ^ 3 = (eNorm x * eNorm y) ^ 3 := (mul_pow _ _ 3).symm
    linarith [hdet, h.symm.le, h.le]
  have hdetpos : 0 < detL (Gam 4 4 x y) := by
    have h0 : 0 < Cdet * d2 * (eNorm x * eNorm y) ^ 3 := by positivity
    linarith [hdet']
  have hkey : Cdet * (eNorm x * eNorm y) * d3 * d2 ^ 3 ≤ d3 ^ 3 * detL (Gam 4 4 x y) := by
    have h3 := mul_le_mul_of_nonneg_right hdet' (by positivity : (0:ℝ) ≤ d3 ^ 3)
    have h5 : d2 ^ 2 ≤ (d3 * (eNorm x * eNorm y)) ^ 2 := by
      nlinarith [hd2le2, hd2pos, hd3pos, hXpos, hYpos]
    have h6 : (eNorm x * eNorm y) * d3 * d2 ^ 3 ≤ d3 ^ 3 * (d2 * (eNorm x * eNorm y) ^ 3) := by
      have h5' := mul_le_mul_of_nonneg_right h5 (by positivity : (0:ℝ) ≤ (eNorm x * eNorm y) * d3 * d2)
      nlinarith [h5', hd2pos, hd3pos, hXpos, hYpos]
    have h7 := mul_le_mul_of_nonneg_left h6 hCdetpos.le
    linarith [h3, h7]
  have hgoal : 48 ^ 3 * (d2 ^ 3 * (Cdet * ((eNorm x * eNorm y) * d3)))
      ≤ 48 ^ 3 * (d3 ^ 3 * detL (Gam 4 4 x y)) := by
    have h := mul_le_mul_of_nonneg_left hkey (by norm_num : (0:ℝ) ≤ 48 ^ 3)
    nlinarith [h]
  have hLHS : (48 * (d2 / d3)) ^ 3 / detL (Gam 4 4 x y)
      = 48 ^ 3 * d2 ^ 3 / (d3 ^ 3 * detL (Gam 4 4 x y)) := by
    field_simp
  have hR : 48 ^ 3 * (1 / (eNorm x * eNorm y * d3)) / Cdet
      = 48 ^ 3 / (Cdet * (eNorm x * eNorm y * d3)) := by
    have h1 : (eNorm x * eNorm y * d3) ≠ 0 := by positivity
    have h2 : Cdet ≠ 0 := ne_of_gt hCdetpos
    field_simp
  have hBpos' : (0:ℝ) < d3 ^ 3 * detL (Gam 4 4 x y) := by positivity
  have hDpos' : (0:ℝ) < Cdet * (eNorm x * eNorm y * d3) := by positivity
  rw [hmu_eq, hLHS, hR]
  rw [le_div_iff₀ hDpos', div_mul_eq_mul_div, div_le_iff₀ hBpos']
  nlinarith [hgoal]

/-- **The pointwise bound.** -/
private lemma pointwise (Kp Cd Cdet : ℝ)
    (hCd : ∀ x y : Fin 5 → ℤ, IsPrim x → IsPrim y → x ≠ y → x ≠ -y →
      lam (Gam 4 4 x y) (NN 4 4 - 2) ≤ Cd * muXY 4 x y)
    (hKp : ∀ (L : Submodule ℤ (Mon 4 4 → ℤ)) (R j0 j : ℕ) (M J Y T : ℝ),
      rk L = R → 2 ≤ R → j0 ≤ R - 1 → j ≤ R - 1 - j0 → 1 ≤ T → M ≤ T → T ≤ Y →
      lam L R ≤ Y → 0 < detL L → detL L ≤ ∏ i ∈ Finset.range R, lam L (i + 1) →
      0 < M → 2 * M ≤ lam L 1 → 0 < J → 2 * J ≤ lam L (j0 + 1) →
      (ballCount L T : ℝ) ≤ Kp * (T ^ (R - j) * Y ^ j / detL L
          + (T / M) ^ j0 * ((T / J) ^ (R - 1 - j0 - j) + 1)))
    (hCdet : ∀ x y : Fin 5 → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      Cdet * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * eNorm x ^ 3 * eNorm y ^ 3
        ≤ detL (Gam 4 4 x y))
    (hKppos : 0 < Kp) (hCdpos : 0 < Cd) (hCdetpos : 0 < Cdet)
    {A B : ℝ} (hA1 : 1 ≤ A) {p : (Fin 5 → ℤ) × (Fin 5 → ℤ)} (hp : p ∈ SLset A B) :
    pairS0 4 4 A p ≤ Kp * (48 ^ 3 * (max Cd 1) ^ 3 / Cdet
        * (A ^ (68 - 3) * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))))
      + (2 * A) ^ 55 * ((2 * A / lam (Gam 4 4 p.1 p.2) 56) ^ 9 + 1)) := by
  obtain ⟨hOm, hmu, hcase, hd3A⟩ := hp
  have hx : IsPrim p.1 := hOm.1.1
  have hy : IsPrim p.2 := hOm.2.1.1
  have hne : p.1 ≠ p.2 := hOm.2.2.1
  have hne' : p.1 ≠ -p.2 := hOm.2.2.2
  have hLI : LinearIndependent ℤ ![p.1, p.2] := Sig2.li_of_mem_Omega 4 4 B p hOm
  have hnu : LinearIndependent ℤ ![veronese 4 4 p.1, veronese 4 4 p.2] :=
    Sig2.nu_indep 4 4 (by norm_num) p.1 p.2 hx hy hne hne'
  obtain ⟨hrk, hdetpos⟩ := Sig2.gam_rank_det 4 4 p.1 p.2 hnu
  have h70 : NN 4 4 = 70 := by
    rw [show NN 4 4 = Fintype.card (Mon 4 4) from rfl, Q44Child.card_mon44]
  have hR : rk (Gam 4 4 p.1 p.2) = 68 := by rw [hrk, h70]
  have hMink : detL (Gam 4 4 p.1 p.2) ≤ ∏ i ∈ Finset.range 68, lam (Gam 4 4 p.1 p.2) (i + 1) := by
    have h := FM.minkowski_lower (Gam 4 4 p.1 p.2)
    rwa [hR] at h
  have hmupos : 0 < muXY 4 p.1 p.2 := by linarith [hA1, not_le.mp hmu]
  have hY : A ≤ max Cd 1 * muXY 4 p.1 p.2 := by
    have h1 : (1:ℝ) ≤ max Cd 1 := le_max_right _ _
    have h2 : muXY 4 p.1 p.2 ≤ max Cd 1 * muXY 4 p.1 p.2 := by
      calc muXY 4 p.1 p.2 = 1 * muXY 4 p.1 p.2 := (one_mul _).symm
        _ ≤ max Cd 1 * muXY 4 p.1 p.2 := mul_le_mul_of_nonneg_right h1 hmupos.le
    linarith [not_le.mp hmu]
  have hlamR : lam (Gam 4 4 p.1 p.2) 68 ≤ max Cd 1 * muXY 4 p.1 p.2 := by
    have h := hCd p.1 p.2 hx hy hne hne'
    have h1 : lam (Gam 4 4 p.1 p.2) (NN 4 4 - 2) ≤ Cd * muXY 4 p.1 p.2 := h
    rw [h70] at h1
    have h2 : Cd * muXY 4 p.1 p.2 ≤ max Cd 1 * muXY 4 p.1 p.2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hmupos.le
    linarith
  have hlam1 : 1 ≤ lam (Gam 4 4 p.1 p.2) 1 :=
    one_le_lam (Gam 4 4 p.1 p.2) (i := 1) (by norm_num) (by rw [hR]; norm_num)
  have hlam56 : 1 ≤ lam (Gam 4 4 p.1 p.2) 56 :=
    one_le_lam (Gam 4 4 p.1 p.2) (i := 56) (by norm_num) (by rw [hR]; norm_num)
  have hJpos : 0 < lam (Gam 4 4 p.1 p.2) 56 / 2 := by linarith
  have hJ1 : 2 * (lam (Gam 4 4 p.1 p.2) 56 / 2) ≤ lam (Gam 4 4 p.1 p.2) (55 + 1) := by
    have h : (55 + 1 : ℕ) = 56 := by norm_num
    have h2 : 2 * (lam (Gam 4 4 p.1 p.2) 56 / 2) = lam (Gam 4 4 p.1 p.2) 56 := by ring
    rw [h, h2]
  have hM1 : 2 * (1/2 : ℝ) ≤ lam (Gam 4 4 p.1 p.2) 1 := by
    norm_num
    exact hlam1
  have hbc := hKp (Gam 4 4 p.1 p.2) 68 55 3 (1/2)
      (lam (Gam 4 4 p.1 p.2) 56 / 2) (max Cd 1 * muXY 4 p.1 p.2) A
      hR (by norm_num) (by norm_num) (by norm_num) hA1 (by linarith) hY hlamR hdetpos hMink
      (by norm_num) hM1 hJpos hJ1
  have hmudet := mu_cube_div_det Cdet hCdet hCdetpos hx hy hLI hcase
  have hpc := pairS0_le_ballCount A p
  have hpart1 : A ^ (68 - 3) * (max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
      ≤ 48 ^ 3 * (max Cd 1) ^ 3 / Cdet
        * (A ^ (68 - 3)
            * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))))) := by
    have h1 : (max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
        ≤ (max Cd 1) ^ 3
          * (48 ^ 3 * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))) / Cdet) := by
      rw [mul_pow]
      calc (max Cd 1) ^ 3 * (muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
          = (max Cd 1) ^ 3 * ((muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)) := by ring
        _ ≤ (max Cd 1) ^ 3
              * (48 ^ 3 * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))) / Cdet) :=
            mul_le_mul_of_nonneg_left hmudet (by positivity)
    have hA65 : (0:ℝ) ≤ A ^ (68 - 3) := by positivity
    have hstep : A ^ (68 - 3) * (max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
        ≤ A ^ (68 - 3) * ((max Cd 1) ^ 3
            * (48 ^ 3 * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))) / Cdet)) := by
      calc A ^ (68 - 3) * (max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
          = A ^ (68 - 3) * ((max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)) := by ring
        _ ≤ A ^ (68 - 3) * ((max Cd 1) ^ 3
              * (48 ^ 3 * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))) / Cdet)) :=
            mul_le_mul_of_nonneg_left h1 hA65
    calc A ^ (68 - 3) * (max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
        ≤ A ^ (68 - 3) * ((max Cd 1) ^ 3
            * (48 ^ 3 * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))) / Cdet)) := hstep
      _ = 48 ^ 3 * (max Cd 1) ^ 3 / Cdet
            * (A ^ (68 - 3)
              * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))))) := by ring_nf
  have hpart2 : (A / (1/2)) ^ 55 * ((A / (lam (Gam 4 4 p.1 p.2) 56 / 2)) ^ 9 + 1)
      = (2 * A) ^ 55 * ((2 * A / lam (Gam 4 4 p.1 p.2) 56) ^ 9 + 1) := by
    have h1 : A / (1/2) = 2 * A := by ring
    have h2 : A / (lam (Gam 4 4 p.1 p.2) 56 / 2) = 2 * A / lam (Gam 4 4 p.1 p.2) 56 := by
      field_simp
    rw [h1, h2]
  calc pairS0 4 4 A p
      ≤ (ballCount (Gam 4 4 p.1 p.2) A : ℝ) := hpc
    _ ≤ Kp * (A ^ (68 - 3) * (max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
          + (A / (1/2)) ^ 55 * ((A / (lam (Gam 4 4 p.1 p.2) 56 / 2)) ^ 9 + 1)) := hbc
    _ = Kp * (A ^ (68 - 3) * (max Cd 1 * muXY 4 p.1 p.2) ^ 3 / detL (Gam 4 4 p.1 p.2)
          + (2 * A) ^ 55 * ((2 * A / lam (Gam 4 4 p.1 p.2) 56) ^ 9 + 1)) := by rw [hpart2]
    _ ≤ Kp * (48 ^ 3 * (max Cd 1) ^ 3 / Cdet
          * (A ^ (68 - 3)
            * (1 / (eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))))
          + (2 * A) ^ 55 * ((2 * A / lam (Gam 4 4 p.1 p.2) 56) ^ 9 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hKppos.le
        linarith [hpart1]

/-! ## Counting -/

private lemma count_d3_le (A B Δ : ℝ) :
    (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ SLset A B ∧
        dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ}.ncard : ℝ))
      ≤ (ellXY 4 3 B B Δ : ℝ) := by
  have hsub : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ SLset A B ∧
        dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ})
      ⊆ {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
          eNorm p.1 ≤ B ∧ eNorm p.2 ≤ B ∧ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ} := by
    rintro p ⟨hp, hd3⟩
    exact ⟨Sig2.li_of_mem_Omega 4 4 B p hp.1, eNorm_le_of_mem_Xi hp.1.1.2,
      eNorm_le_of_mem_Xi hp.1.2.1.2, hd3⟩
  have hfin : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
          eNorm p.1 ≤ B ∧ eNorm p.2 ≤ B ∧ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ}).Finite :=
    ((MDBasic.finite_eNorm_le (ι := Fin 5) B).prod
      (MDBasic.finite_eNorm_le (ι := Fin 5) B)).subset (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
  have hle := Set.ncard_le_ncard hsub hfin
  have hcast : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
          eNorm p.1 ≤ B ∧ eNorm p.2 ≤ B ∧ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ}).ncard
      = (ellXY 4 3 B B Δ : ℕ) := rfl
  rw [hcast] at hle
  exact_mod_cast hle

/-- The number of pairs of the region, bounded by the `ℓ_{3,4}` count. -/
private lemma SL_card_bound (Kc A B : ℝ)
    (hKc : ∀ Z Δ : ℝ, 1 ≤ Z → 1 ≤ Δ →
      (ellXY 4 3 Z Z Δ : ℝ) ≤ Kc * Z ^ 6 * Δ ^ 3 * Real.log (2 * Δ) ^ 2)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) :
    ((SLset A B).ncard : ℝ)
      ≤ Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2 := by
  have hΔ1 : 1 ≤ A ^ ((1:ℝ)/20) := Real.one_le_rpow hA1 (by norm_num)
  have hset : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ SLset A B ∧
        dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1:ℝ)/20)}) = SLset A B := by
    ext p
    constructor
    · rintro ⟨hp, -⟩; exact hp
    · intro hp; exact ⟨hp, hp.2.2.2⟩
  have h1 := count_d3_le A B (A ^ ((1:ℝ)/20))
  rw [hset] at h1
  have h2 := hKc B (A ^ ((1:ℝ)/20)) hB1 hΔ1
  linarith


/-! ## The two layer-cake sums -/

/-- The multiplier `‖x‖‖y‖𝔡₃` attached to a pair. -/
private def Dp (p : (Fin 5 → ℤ) × (Fin 5 → ℤ)) : ℝ :=
  eNorm p.1 * eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))

/-- `λ₅₆(Γ_{x,y})`. -/
private def Lp (p : (Fin 5 → ℤ) × (Fin 5 → ℤ)) : ℝ := lam (Gam 4 4 p.1 p.2) 56

private lemma sum_D_le (Kc Kct Kdm A B : ℝ) (hKcpos : 0 ≤ Kc) (hKctpos : 0 ≤ Kct)
    (F : Finset ((Fin 5 → ℤ) × (Fin 5 → ℤ)))
    (hF : (F : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))) = SLset A B)
    (hN : (F.card : ℝ) ≤ Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2)
    (hKct : ∀ B Δ : ℝ, 1 ≤ B → 1 ≤ Δ →
      (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧ Dp p ≤ Δ}.ncard : ℝ))
        ≤ Kct * Δ ^ 4)
    (hKdm : ∀ (F : Finset ((Fin 5 → ℤ) × (Fin 5 → ℤ))) (D : (Fin 5 → ℤ) × (Fin 5 → ℤ) → ℝ)
        (Λ N C : ℝ), 1 ≤ Λ → (∀ p ∈ F, 1 ≤ D p) → (∀ p ∈ F, D p ≤ Λ) → 0 ≤ N → 0 ≤ C →
      (∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => D p ≤ Δ)).card : ℝ) ≤ N) →
      (∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => D p ≤ Δ)).card : ℝ) ≤ C * Δ ^ (4:ℝ)) →
      (∑ p ∈ F, (D p) ^ (-(1:ℝ))) ≤ Kdm * C ^ ((1:ℝ)/4) * N ^ (1 - (1:ℝ)/4))
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) :
    (∑ p ∈ F, (Dp p) ^ (-(1:ℝ)))
      ≤ Kdm * Kct ^ ((1:ℝ)/4)
        * (Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2)
            ^ (1 - (1:ℝ)/4) := by
  have hΔ1 : 1 ≤ A ^ ((1:ℝ)/20) := Real.one_le_rpow hA1 (by norm_num)
  have hΛ : 1 ≤ B ^ 2 * A ^ ((1:ℝ)/20) := by
    have h1 : (1:ℝ) ≤ B ^ 2 := one_le_pow₀ hB1
    nlinarith [h1, hΔ1]
  have hD1 : ∀ p ∈ F, 1 ≤ Dp p := by
    intro p hp
    have hpS : p ∈ SLset A B := by rw [← hF]; exact hp
    have hLI := Sig2.li_of_mem_Omega 4 4 B p hpS.1
    have h1 : 1 ≤ eNorm p.1 := one_le_eNorm (ne_zero_of_LI1 hLI)
    have h2 : 1 ≤ eNorm p.2 := one_le_eNorm (ne_zero_of_LI2 hLI)
    have h3 : 1 ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) :=
      (dmin_facts 4 (by norm_num)).2.2.1 p.1 p.2 hLI
    have hbc : 1 ≤ eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) := by
      have := mul_le_mul h2 h3 (by positivity) (by positivity)
      simpa using this
    have habc := mul_le_mul h1 hbc (by positivity) (by positivity)
    unfold Dp
    simpa only [one_mul, mul_assoc] using habc
  have hDΛ : ∀ p ∈ F, Dp p ≤ B ^ 2 * A ^ ((1:ℝ)/20) := by
    intro p hp
    have hpS : p ∈ SLset A B := by rw [← hF]; exact hp
    have hLI := Sig2.li_of_mem_Omega 4 4 B p hpS.1
    have h1 : eNorm p.1 ≤ B := eNorm_le_of_mem_Xi hpS.1.1.2
    have h2 : eNorm p.2 ≤ B := eNorm_le_of_mem_Xi hpS.1.2.1.2
    have h3 : dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1:ℝ)/20) := hpS.2.2.2
    have h4 : (0:ℝ) ≤ eNorm p.1 := eNorm_nonneg p.1
    have h5 : (0:ℝ) ≤ eNorm p.2 := eNorm_nonneg p.2
    have h6 : (0:ℝ) ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) :=
      le_trans zero_le_one ((dmin_facts 4 (by norm_num)).2.2.1 p.1 p.2 hLI)
    have hb : eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ B * A ^ ((1:ℝ)/20) :=
      mul_le_mul h2 h3 h6 (le_trans h4 h1)
    have htop : eNorm p.1 * (eNorm p.2 * dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))
        ≤ B * (B * A ^ ((1:ℝ)/20)) :=
      mul_le_mul h1 hb (by positivity) (le_trans zero_le_one hB1)
    unfold Dp
    rw [← mul_assoc] at htop
    have hbb : B * (B * A ^ ((1:ℝ)/20)) = B ^ 2 * A ^ ((1:ℝ)/20) := by ring
    rw [hbb] at htop
    exact htop
  have hcount1 : ∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => Dp p ≤ Δ)).card : ℝ)
      ≤ Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2 := by
    intro Δ hΔ
    have h1 : (F.filter (fun p => Dp p ≤ Δ)).card ≤ F.card := Finset.card_filter_le _ _
    have h2 : ((F.filter (fun p => Dp p ≤ Δ)).card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast h1
    linarith
  have hcount2 : ∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => Dp p ≤ Δ)).card : ℝ) ≤ Kct * Δ ^ (4:ℝ) := by
    intro Δ hΔ
    have hcoe : (((↑(F.filter (fun p => Dp p ≤ Δ)) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)))).ncard : ℝ)
        = ((F.filter (fun p => Dp p ≤ Δ)).card : ℝ) := by
      rw [Set.ncard_coe_finset]
    have hsub : (↑(F.filter (fun p => Dp p ≤ Δ)) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)))
        ⊆ {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧ Dp p ≤ Δ} := by
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      have hpS : p ∈ SLset A B := by rw [← hF]; exact hp.1
      exact ⟨hpS.1, hp.2⟩
    have hfin : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧ Dp p ≤ Δ}).Finite :=
      (MDBasic.finite_sets 4 4 A B (fun _ => True)).2.2.subset (fun p hp => hp.1)
    have hle := Set.ncard_le_ncard hsub hfin
    have hle' : ((F.filter (fun p => Dp p ≤ Δ)).card : ℝ)
        ≤ (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧ Dp p ≤ Δ}.ncard : ℝ)) := by
      rw [← hcoe]
      exact_mod_cast hle
    have h3 : (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧ Dp p ≤ Δ}.ncard : ℝ))
        ≤ Kct * Δ ^ ((4:ℕ):ℝ) := by
      simpa only [Real.rpow_natCast] using hKct B Δ hB1 hΔ
    exact le_trans hle' h3
  have hNnonneg : (0:ℝ) ≤ Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3
      * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2 := by
    have hlog : (0:ℝ) ≤ Real.log (2 * A ^ ((1:ℝ)/20)) := Real.log_nonneg (by linarith [hΔ1])
    positivity
  exact hKdm F Dp (B ^ 2 * A ^ ((1:ℝ)/20))
    (Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2) Kct
    hΛ hD1 hDΛ hNnonneg hKctpos hcount1 hcount2

private lemma sum_lam_le (Kc K44 Klm A B : ℝ) (hKcpos : 0 ≤ Kc) (hK44pos : 0 ≤ K44)
    (F : Finset ((Fin 5 → ℤ) × (Fin 5 → ℤ)))
    (hF : (F : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))) = SLset A B)
    (hN : (F.card : ℝ) ≤ Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2)
    (hK44 : ∀ Z Δ J : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ J →
      (ell44 56 Z Δ J : ℝ) ≤ K44 * Z ^ 4 * Δ ^ 24 * J ^ 15)
    (hKlm : ∀ (F : Finset ((Fin 5 → ℤ) × (Fin 5 → ℤ))) (D : (Fin 5 → ℤ) × (Fin 5 → ℤ) → ℝ)
        (Λ N C : ℝ), 1 ≤ Λ → (∀ p ∈ F, 1 ≤ D p) → (∀ p ∈ F, D p ≤ Λ) → 0 ≤ N → 0 ≤ C →
      (∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => D p ≤ Δ)).card : ℝ) ≤ N) →
      (∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => D p ≤ Δ)).card : ℝ) ≤ C * Δ ^ (15:ℝ)) →
      (∑ p ∈ F, (D p) ^ (-(9:ℝ))) ≤ Klm * C ^ ((9:ℝ)/15) * N ^ (1 - (9:ℝ)/15))
    (Cd : ℝ) (hCd : ∀ x y : Fin 5 → ℤ, IsPrim x → IsPrim y → x ≠ y → x ≠ -y →
      lam (Gam 4 4 x y) (NN 4 4 - 2) ≤ Cd * muXY 4 x y)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) :
    (∑ p ∈ F, (Lp p) ^ (-(9:ℝ)))
      ≤ Klm * (K44 * B ^ 4 * (A ^ ((1:ℝ)/20)) ^ 24) ^ ((9:ℝ)/15)
        * (Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2)
            ^ (1 - (9:ℝ)/15) := by
  have hΔ1 : 1 ≤ A ^ ((1:ℝ)/20) := Real.one_le_rpow hA1 (by norm_num)
  have h70 : NN 4 4 = 70 := by
    rw [show NN 4 4 = Fintype.card (Mon 4 4) from rfl, Q44Child.card_mon44]
  have hΛ : 1 ≤ max Cd 1 * 48 * B ^ 2 := by
    have h1 : (1:ℝ) ≤ max Cd 1 := le_max_right _ _
    have h2 : (1:ℝ) ≤ B ^ 2 := one_le_pow₀ hB1
    nlinarith [h1, h2]
  have hD1 : ∀ p ∈ F, 1 ≤ Lp p := by
    intro p hp
    have hpS : p ∈ SLset A B := by rw [← hF]; exact hp
    have hLI := Sig2.li_of_mem_Omega 4 4 B p hpS.1
    have hnu := Sig2.nu_indep 4 4 (by norm_num) p.1 p.2 hpS.1.1.1 hpS.1.2.1.1
      hpS.1.2.2.1 hpS.1.2.2.2
    obtain ⟨hrk, -⟩ := Sig2.gam_rank_det 4 4 p.1 p.2 hnu
    have h68 : rk (Gam 4 4 p.1 p.2) = 68 := by rw [hrk, h70]
    exact one_le_lam (Gam 4 4 p.1 p.2) (i := 56) (by norm_num) (by rw [h68]; norm_num)
  have hDΛ : ∀ p ∈ F, Lp p ≤ max Cd 1 * 48 * B ^ 2 := by
    intro p hp
    have hpS : p ∈ SLset A B := by rw [← hF]; exact hp
    have hLI := Sig2.li_of_mem_Omega 4 4 B p hpS.1
    have hnu := Sig2.nu_indep 4 4 (by norm_num) p.1 p.2 hpS.1.1.1 hpS.1.2.1.1
      hpS.1.2.2.1 hpS.1.2.2.2
    obtain ⟨hrk, -⟩ := Sig2.gam_rank_det 4 4 p.1 p.2 hnu
    have h68 : rk (Gam 4 4 p.1 p.2) = 68 := by rw [hrk, h70]
    have hmono : lam (Gam 4 4 p.1 p.2) 56 ≤ lam (Gam 4 4 p.1 p.2) 68 :=
      lam_mono (Gam 4 4 p.1 p.2) (by norm_num) (by rw [h68])
    have hkey : lam (Gam 4 4 p.1 p.2) 68 ≤ max Cd 1 * muXY 4 p.1 p.2 := by
      have h := hCd p.1 p.2 hpS.1.1.1 hpS.1.2.1.1 hpS.1.2.2.1 hpS.1.2.2.2
      rw [h70] at h
      norm_num at h
      have hmupos : 0 < muXY 4 p.1 p.2 := by linarith [hA1, not_le.mp hpS.2.1]
      have h2 : Cd * muXY 4 p.1 p.2 ≤ max Cd 1 * muXY 4 p.1 p.2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hmupos.le
      linarith
    have hle := muXY_le 4 4 p.1 p.2 hpS.1.1.1 hpS.1.2.1.1 hLI
    norm_num at hle
    have hXY : muXY 4 p.1 p.2 ≤ 48 * (B * B) := by
      have hx1 : eNorm p.1 ≤ B := eNorm_le_of_mem_Xi hpS.1.1.2
      have hy1 : eNorm p.2 ≤ B := eNorm_le_of_mem_Xi hpS.1.2.1.2
      have h1 : eNorm p.1 * eNorm p.2 ≤ B * B :=
        mul_le_mul hx1 hy1 (eNorm_nonneg p.2) (le_trans (eNorm_nonneg p.1) hx1)
      linarith [hle, h1]
    have h1 : (1:ℝ) ≤ max Cd 1 := le_max_right _ _
    have hX : 0 < muXY 4 p.1 p.2 := by linarith [hA1, not_le.mp hpS.2.1]
    have h2 : max Cd 1 * muXY 4 p.1 p.2 ≤ max Cd 1 * (48 * (B * B)) :=
      mul_le_mul_of_nonneg_left hXY (by positivity)
    have h3 : lam (Gam 4 4 p.1 p.2) 56 ≤ max Cd 1 * (48 * (B * B)) := by
      linarith [hmono, hkey, h2]
    have h4 : max Cd 1 * (48 * (B * B)) = max Cd 1 * 48 * B ^ 2 := by ring
    unfold Lp
    rw [h4] at h3
    exact h3
  have hcount1 : ∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => Lp p ≤ Δ)).card : ℝ)
      ≤ Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2 := by
    intro Δ hΔ
    have h1 : (F.filter (fun p => Lp p ≤ Δ)).card ≤ F.card := Finset.card_filter_le _ _
    have h2 : ((F.filter (fun p => Lp p ≤ Δ)).card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast h1
    linarith
  have hcount2 : ∀ Δ : ℝ, 1 ≤ Δ → ((F.filter (fun p => Lp p ≤ Δ)).card : ℝ)
      ≤ (K44 * B ^ 4 * (A ^ ((1:ℝ)/20)) ^ 24) * Δ ^ (15:ℝ) := by
    intro Δ hΔ
    have hcoe : (((↑(F.filter (fun p => Lp p ≤ Δ)) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)))).ncard : ℝ)
        = ((F.filter (fun p => Lp p ≤ Δ)).card : ℝ) := by
      rw [Set.ncard_coe_finset]
    have hsub : (↑(F.filter (fun p => Lp p ≤ Δ)) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)))
        ⊆ {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
            eNorm p.1 ≤ B ∧ eNorm p.2 ≤ B ∧
            dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1:ℝ)/20) ∧
            lam (Gam 4 4 p.1 p.2) 56 ≤ Δ} := by
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      have hpS : p ∈ SLset A B := by rw [← hF]; exact hp.1
      exact ⟨Sig2.li_of_mem_Omega 4 4 B p hpS.1, eNorm_le_of_mem_Xi hpS.1.1.2,
        eNorm_le_of_mem_Xi hpS.1.2.1.2, hpS.2.2.2, hp.2⟩
    have hfin : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
            eNorm p.1 ≤ B ∧ eNorm p.2 ≤ B ∧
            dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1:ℝ)/20) ∧
            lam (Gam 4 4 p.1 p.2) 56 ≤ Δ}).Finite :=
      ((MDBasic.finite_eNorm_le (ι := Fin 5) B).prod
        (MDBasic.finite_eNorm_le (ι := Fin 5) B)).subset (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
    have hle := Set.ncard_le_ncard hsub hfin
    have hle' : ((F.filter (fun p => Lp p ≤ Δ)).card : ℝ)
        ≤ ((ell44 56 B (A ^ ((1:ℝ)/20)) Δ : ℕ) : ℝ) := by
      rw [← hcoe]
      have hcast : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
              eNorm p.1 ≤ B ∧ eNorm p.2 ≤ B ∧
              dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1:ℝ)/20) ∧
              lam (Gam 4 4 p.1 p.2) 56 ≤ Δ}).ncard
          = (ell44 56 B (A ^ ((1:ℝ)/20)) Δ : ℕ) := rfl
      rw [hcast] at hle
      exact_mod_cast hle
    have h3 : ((ell44 56 B (A ^ ((1:ℝ)/20)) Δ : ℕ) : ℝ)
        ≤ K44 * B ^ 4 * (A ^ ((1:ℝ)/20)) ^ 24 * Δ ^ ((15:ℕ):ℝ) := by
      simpa only [Real.rpow_natCast] using hK44 B (A ^ ((1:ℝ)/20)) Δ hB1 hΔ1 hΔ
    exact le_trans hle' h3
  have hNnonneg : (0:ℝ) ≤ Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3
      * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2 := by
    have hlog : (0:ℝ) ≤ Real.log (2 * A ^ ((1:ℝ)/20)) := Real.log_nonneg (by linarith [hΔ1])
    positivity
  have hCnonneg : (0:ℝ) ≤ K44 * B ^ 4 * (A ^ ((1:ℝ)/20)) ^ 24 := by positivity
  exact hKlm F Lp (max Cd 1 * 48 * B ^ 2)
    (Kc * B ^ 6 * (A ^ ((1:ℝ)/20)) ^ 3 * Real.log (2 * A ^ ((1:ℝ)/20)) ^ 2)
    (K44 * B ^ 4 * (A ^ ((1:ℝ)/20)) ^ 24)
    hΛ hD1 hDΛ hNnonneg hCnonneg hcount1 hcount2

/-! ## `rpow` decompositions -/

private lemma rpow_34_split {B Δ₀ L Kc : ℝ} (hB : 0 < B) (hΔ : 0 < Δ₀) (hL : 0 < L)
    (hKc : 0 ≤ Kc) :
    (4 * Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2) ^ ((3:ℝ)/4)
      = (4 * Kc) ^ ((3:ℝ)/4) * B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2) := by
  rw [show (4 * Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 : ℝ) = (4 * Kc * B ^ 6 * Δ₀ ^ 3) * L ^ 2 by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [show (4 * Kc * B ^ 6 * Δ₀ ^ 3 : ℝ) = (4 * Kc * B ^ 6) * Δ₀ ^ 3 by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [show (4 * Kc * B ^ 6 : ℝ) = (4 * Kc) * B ^ 6 by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast B 6, ← Real.rpow_natCast Δ₀ 3, ← Real.rpow_natCast L 2]
  rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hΔ.le, ← Real.rpow_mul hL.le]
  have e1 : (((6:ℕ)) : ℝ) * ((3:ℝ)/4) = (9:ℝ)/2 := by norm_num
  have e2 : (((3:ℕ)) : ℝ) * ((3:ℝ)/4) = (9:ℝ)/4 := by norm_num
  have e3 : (((2:ℕ)) : ℝ) * ((3:ℝ)/4) = (3:ℝ)/2 := by norm_num
  rw [e1, e2, e3]

private lemma rpow_915_split {B Δ₀ L K44 Kc : ℝ} (hB : 0 < B) (hΔ : 0 < Δ₀) (hL : 0 < L)
    (hK44 : 0 ≤ K44) (hKc : 0 ≤ Kc) :
    (K44 * B ^ 4 * Δ₀ ^ 24) ^ ((9:ℝ)/15) * (Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2) ^ ((6:ℝ)/15)
      = (K44 ^ ((9:ℝ)/15) * Kc ^ ((6:ℝ)/15))
        * (B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)) := by
  rw [show (K44 * B ^ 4 * Δ₀ ^ 24 : ℝ) = K44 * (B ^ 4 * Δ₀ ^ 24) by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [show (B ^ 4 * Δ₀ ^ 24 : ℝ) = B ^ 4 * Δ₀ ^ 24 by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [show (Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 : ℝ) = Kc * (B ^ 6 * Δ₀ ^ 3 * L ^ 2) by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [show (B ^ 6 * Δ₀ ^ 3 * L ^ 2 : ℝ) = (B ^ 6 * Δ₀ ^ 3) * L ^ 2 by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [show (B ^ 6 * Δ₀ ^ 3 : ℝ) = B ^ 6 * Δ₀ ^ 3 by ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast B 4, ← Real.rpow_natCast Δ₀ 24,
      ← Real.rpow_natCast B 6, ← Real.rpow_natCast Δ₀ 3, ← Real.rpow_natCast L 2]
  rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hΔ.le, ← Real.rpow_mul hB.le,
      ← Real.rpow_mul hΔ.le, ← Real.rpow_mul hL.le]
  have f1 : (((4:ℕ)) : ℝ) * ((9:ℝ)/15) = (12:ℝ)/5 := by norm_num
  have f2 : (((24:ℕ)) : ℝ) * ((9:ℝ)/15) = (72:ℝ)/5 := by norm_num
  have f3 : (((6:ℕ)) : ℝ) * ((6:ℝ)/15) = (12:ℝ)/5 := by norm_num
  have f4 : (((3:ℕ)) : ℝ) * ((6:ℝ)/15) = (6:ℝ)/5 := by norm_num
  have f5 : (((2:ℕ)) : ℝ) * ((6:ℝ)/15) = (4:ℝ)/5 := by norm_num
  rw [f1, f2, f3, f4, f5]
  rw [show K44 ^ ((9:ℝ)/15) * (B ^ ((12:ℝ)/5) * Δ₀ ^ ((72:ℝ)/5))
        * (Kc ^ ((6:ℝ)/15) * (B ^ ((12:ℝ)/5) * Δ₀ ^ ((6:ℝ)/5) * L ^ ((4:ℝ)/5)))
      = K44 ^ ((9:ℝ)/15) * Kc ^ ((6:ℝ)/15)
        * ((B ^ ((12:ℝ)/5) * B ^ ((12:ℝ)/5)) * (Δ₀ ^ ((72:ℝ)/5) * Δ₀ ^ ((6:ℝ)/5))
          * L ^ ((4:ℝ)/5)) by ring]
  rw [← Real.rpow_add hB, ← Real.rpow_add hΔ]
  norm_num
/-- Monomial comparison: with `B ≤ Cb * A * L`, `L^8 ≤ A^(1/10)`, `Δ₀ = A^(1/20)` and
`α + γ/20 + (β-2) + 1/10 ≤ 68 - 1/32`, `2 ≤ β`, `β - 2 + δ ≤ 8`, the monomial
`c * A^α * B^β * Δ₀^γ * L^δ` is at most `c * Cb^(β-2) * (A^(68-1/32) * B^2)`. -/
theorem mono_bound (A B L Δ₀ Cb c α β γ δ : ℝ)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hL1 : 1 ≤ L) (hΔ₀ : Δ₀ = A ^ ((1:ℝ)/20))
    (hL8 : L ^ (8:ℝ) ≤ A ^ ((1:ℝ)/10)) (hB : B ≤ Cb * A * L) (hCbpos : 0 < Cb) (hc : 0 < c)
    (hβ : 2 ≤ β) (hβδ : β - 2 + δ ≤ 8)
    (hα : α + γ/20 + (β - 2) + 1/10 ≤ (68:ℝ) - 1/32) :
    c * A ^ α * B ^ β * Δ₀ ^ γ * L ^ δ ≤ c * Cb ^ (β - 2) * (A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ)) := by
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hLpos : 0 < L := by linarith
  have hA0 : 0 ≤ A := hApos.le
  have hL0 : 0 ≤ L := hLpos.le
  have hCAL : 0 ≤ Cb * A * L := by positivity
  have hCAL' : 0 ≤ Cb * (A * L) := by positivity
  have hBβ : B ^ β = B ^ (2:ℝ) * B ^ (β - 2) := by
    rw [← Real.rpow_add hBpos]
    congr 1
    ring
  have hAL : (A * L) ^ (β - 2) = A ^ (β - 2) * L ^ (β - 2) := Real.mul_rpow hA0 hL0
  have hCbAL'' : (Cb * (A * L)) ^ (β - 2) = Cb ^ (β - 2) * (A * L) ^ (β - 2) :=
    Real.mul_rpow hCbpos.le (by positivity : (0:ℝ) ≤ A * L)
  have hCbAL : (Cb * A * L) ^ (β - 2) = Cb ^ (β - 2) * (A ^ (β - 2) * L ^ (β - 2)) := by
    rw [show Cb * A * L = Cb * (A * L) by ring, hCbAL'', hAL]
  have hBL : B ^ (β - 2) ≤ Cb ^ (β - 2) * (A ^ (β - 2) * L ^ (β - 2)) := by
    rw [← hCbAL]
    exact Real.rpow_le_rpow (by positivity) hB (by linarith)
  have hLpow : L ^ (β - 2) * L ^ δ = L ^ ((β - 2) + δ) := by
    rw [← Real.rpow_add hLpos]
  have hL8' : L ^ ((β - 2) + δ) ≤ A ^ ((1:ℝ)/10) := by
    calc L ^ ((β - 2) + δ) ≤ L ^ (8:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hβδ
      _ ≤ A ^ ((1:ℝ)/10) := hL8
  have hΔ : Δ₀ ^ γ = A ^ (γ/20) := by
    rw [hΔ₀, ← Real.rpow_mul hA0]
    congr 1
    ring
  have hAcomb : A ^ α * A ^ (γ/20) * A ^ (β - 2) * A ^ ((1:ℝ)/10) = A ^ (α + γ/20 + (β - 2) + 1/10) := by
    rw [← Real.rpow_add hApos, ← Real.rpow_add hApos, ← Real.rpow_add hApos]
  have hAfin : A ^ (α + γ/20 + (β - 2) + 1/10) ≤ A ^ ((68:ℝ) - 1/32) :=
    Real.rpow_le_rpow_of_exponent_le hA1 hα
  calc c * A ^ α * B ^ β * Δ₀ ^ γ * L ^ δ
      = c * (A ^ α * A ^ (γ/20)) * (B ^ (2:ℝ) * B ^ (β - 2)) * L ^ δ := by
        rw [hΔ, hBβ]
        ring
    _ = c * (A ^ α * A ^ (γ/20)) * B ^ (2:ℝ) * (B ^ (β - 2) * L ^ δ) := by ring
    _ ≤ c * (A ^ α * A ^ (γ/20)) * B ^ (2:ℝ)
          * ((Cb ^ (β - 2) * (A ^ (β - 2) * L ^ (β - 2))) * L ^ δ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hL0 δ)
    _ = c * Cb ^ (β - 2) * (A ^ α * A ^ (γ/20) * A ^ (β - 2)) * B ^ (2:ℝ)
          * (L ^ (β - 2) * L ^ δ) := by ring
    _ = c * Cb ^ (β - 2) * (A ^ α * A ^ (γ/20) * A ^ (β - 2)) * B ^ (2:ℝ)
          * L ^ ((β - 2) + δ) := by rw [hLpow]
    _ ≤ c * Cb ^ (β - 2) * (A ^ α * A ^ (γ/20) * A ^ (β - 2)) * B ^ (2:ℝ)
          * A ^ ((1:ℝ)/10) := by
        apply mul_le_mul_of_nonneg_left hL8' (by positivity)
    _ = c * Cb ^ (β - 2) * (A ^ (α + γ/20 + (β - 2) + 1/10)) * B ^ (2:ℝ) := by
        rw [← hAcomb]
        ring
    _ ≤ c * Cb ^ (β - 2) * (A ^ ((68:ℝ) - 1/32)) * B ^ (2:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hBpos.le _)
        apply mul_le_mul_of_nonneg_left hAfin (by positivity)
    _ = c * Cb ^ (β - 2) * (A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ)) := by ring

/-- The final arithmetic: the sum of the three regime contributions. -/
theorem arith_three (A B L Δ₀ Cb c₁ c₂ c₃ : ℝ)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hL1 : 1 ≤ L) (hΔ₀ : Δ₀ = A ^ ((1:ℝ)/20))
    (hL8 : L ^ (8:ℝ) ≤ A ^ ((1:ℝ)/10)) (hB : B ≤ Cb * A * L) (hCbpos : 0 < Cb)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    c₁ * A ^ (65:ℝ) * B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2)
      + c₂ * A ^ (64:ℝ) * B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)
      + c₃ * A ^ (55:ℝ) * B ^ (6:ℝ) * Δ₀ ^ (3:ℝ) * L ^ (2:ℝ)
    ≤ (c₁ * Cb ^ ((5:ℝ)/2) + c₂ * Cb ^ ((14:ℝ)/5) + c₃ * Cb ^ (4:ℝ) + 1)
        * A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ) := by
  have h1 := mono_bound A B L Δ₀ Cb c₁ 65 ((9:ℝ)/2) ((9:ℝ)/4) ((3:ℝ)/2) hA1 hB1 hL1 hΔ₀ hL8 hB
    hCbpos hc₁ (by norm_num) (by norm_num) (by norm_num)
  have h2 := mono_bound A B L Δ₀ Cb c₂ 64 ((24:ℝ)/5) ((78:ℝ)/5) ((4:ℝ)/5) hA1 hB1 hL1 hΔ₀ hL8 hB
    hCbpos hc₂ (by norm_num) (by norm_num) (by norm_num)
  have h3 := mono_bound A B L Δ₀ Cb c₃ 55 (6:ℝ) (3:ℝ) (2:ℝ) hA1 hB1 hL1 hΔ₀ hL8 hB
    hCbpos hc₃ (by norm_num) (by norm_num) (by norm_num)
  have hfin : (0:ℝ) ≤ A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ) := by positivity
  have h4 : (0:ℝ) ≤ c₁ * Cb ^ ((5:ℝ)/2) := by positivity
  have h5 : (0:ℝ) ≤ c₂ * Cb ^ ((14:ℝ)/5) := by positivity
  have h6 : (0:ℝ) ≤ c₃ * Cb ^ (4:ℝ) := by positivity
  have hsum2 : c₁ * Cb ^ ((5:ℝ)/2) * (A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ))
      + c₂ * Cb ^ ((14:ℝ)/5) * (A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ))
      + c₃ * Cb ^ (4:ℝ) * (A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ))
      ≤ (c₁ * Cb ^ ((5:ℝ)/2) + c₂ * Cb ^ ((14:ℝ)/5) + c₃ * Cb ^ (4:ℝ) + 1)
          * A ^ ((68:ℝ) - 1/32) * B ^ (2:ℝ) := by
    nlinarith [hfin, h4, h5, h6]
  linarith [h1, h2, h3, hsum2]



/-! ## The main estimate -/

theorem Sigma2_44_I_lo :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧
          ¬ (muXY 4 p.1 p.2 ≤ A) ∧
          ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
              ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
          dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1 : ℝ) / 20)},
        pairS0 4 4 A p)
        ≤ K * A ^ ((NN 4 4 : ℝ) - 2 - (1 : ℝ) / 32) * B ^ 2 := by
  obtain ⟨Cd, hCdpos, hCd⟩ := Sig2.key_lemma_two_vectors 4 4 (by norm_num) (by norm_num)
  obtain ⟨Kp, hKppos, hKp⟩ := ballCount_R0_j0 (ι := Mon 4 4)
  obtain ⟨Cl, hClpos, hCl⟩ := detGam_lower 4 4 (by norm_num) (by norm_num)
  obtain ⟨Kc, hKcpos, hKc⟩ := ell34_bound
  obtain ⟨K44, hK44pos, hK44⟩ := ell44_56_bound
  obtain ⟨Kdm, hKdmpos, hKdm⟩ := dyadic_min_sum_finset_free
    (ι := (Fin 5 → ℤ) × (Fin 5 → ℤ)) (1:ℝ) 4 (by norm_num) (by norm_num)
  obtain ⟨Klm, hKlmpos, hKlm⟩ := dyadic_min_sum_finset_free
    (ι := (Fin 5 → ℤ) × (Fin 5 → ℤ)) (9:ℝ) 15 (by norm_num) (by norm_num)
  obtain ⟨Kct, hKctpos, hKct⟩ := Sigma2_44_I_lo_aux.CountXYD3
  obtain ⟨Cb, hCbpos, hCb⟩ := Sig2.le_mul_log_of_div_log_le 16 (by norm_num)
  obtain ⟨A₀, hA₀1, hA₀b⟩ := Sig2.log_pow_le_rpow 8 (1/10) (by norm_num)
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = Kp * (48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹)
      * (Kdm * Kct ^ ((1:ℝ)/4) * (4 * Kc) ^ ((3:ℝ)/4)) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ, c2 = Kp * 2 ^ 64
      * (Klm * K44 ^ ((9:ℝ)/15) * (4 * Kc) ^ ((6:ℝ)/15)) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c3 : ℝ, c3 = Kp * 2 ^ 55 * (4 * Kc) := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hc2pos : 0 < c2 := by rw [hc2]; positivity
  have hc3pos : 0 < c3 := by rw [hc3]; positivity
  refine ⟨c1 * Cb ^ ((5:ℝ)/2) + c2 * Cb ^ ((14:ℝ)/5) + c3 * Cb ^ ((4:ℝ)) + 1,
    max 16 (4 * (max A₀ 1) ^ 2 + 1), ?_, ?_⟩
  · have h1 : 0 ≤ c1 * Cb ^ ((5:ℝ)/2) := by positivity
    have h2 : 0 ≤ c2 * Cb ^ ((14:ℝ)/5) := by positivity
    have h3 : 0 ≤ c3 * Cb ^ ((4:ℝ)) := by positivity
    linarith
  · intro A B hB hAB hAB2
    have hB16 : (16:ℝ) ≤ B := le_trans (le_max_left _ _) hB
    have hBbig : 4 * (max A₀ 1) ^ 2 + 1 ≤ B := le_trans (le_max_right _ _) hB
    have hB1 : (1:ℝ) ≤ B := by linarith
    have hBpos : 0 < B := by linarith
    have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith)
    have hlogB1 : 1 ≤ Real.log B := by
      rw [Real.le_log_iff_exp_le hBpos]
      linarith [Real.exp_one_lt_three]
    have hsqrtlog : Real.log B ≤ 2 * Real.sqrt B := by
      have h := Real.log_le_rpow_div (x := B) (ε := (1:ℝ)/2) hBpos.le (by norm_num)
      rw [show (1:ℝ)/2 = 1/2 by norm_num] at h
      have h2 : B ^ ((1:ℝ)/2) / (1/2 : ℝ) = 2 * B ^ ((1:ℝ)/2) := by ring
      rw [h2, ← Real.sqrt_eq_rpow] at h
      linarith
    have hAge : max A₀ 1 ≤ A := by
      have h1 : B / (2 * Real.sqrt B) ≤ B / Real.log B :=
        div_le_div_of_nonneg_left hBpos.le hlogBpos hsqrtlog
      have h2 : B / (2 * Real.sqrt B) = Real.sqrt B / 2 := by
        have hs : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hBpos)
        have hs2 : (2:ℝ) * Real.sqrt B ≠ 0 := by positivity
        field_simp
        rw [Real.sq_sqrt hBpos.le]
      have h3 : Real.sqrt (4 * (max A₀ 1) ^ 2) / 2 ≤ Real.sqrt B / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply Real.sqrt_le_sqrt
        linarith
      have h4 : Real.sqrt (4 * (max A₀ 1) ^ 2) / 2 = max A₀ 1 := by
        rw [show (4:ℝ) * (max A₀ 1) ^ 2 = (2 * max A₀ 1) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
        ring
      linarith [hAB, h1, h2, h3, h4]
    have hA1 : 1 ≤ A := le_trans (le_max_right _ _) hAge
    have hAA₀ : A₀ ≤ A := le_trans (le_max_left _ _) hAge
    have hApos : 0 < A := by linarith
    set L : ℝ := Real.log A + 1 with hLdef
    set Δ₀ : ℝ := A ^ ((1:ℝ)/20) with hΔ₀def
    have hL1 : 1 ≤ L := by rw [hLdef]; linarith [Real.log_nonneg hA1]
    have hLpos : 0 < L := by linarith
    have hΔ₀1 : 1 ≤ Δ₀ := by rw [hΔ₀def]; exact Real.one_le_rpow hA1 (by norm_num)
    have hΔ₀pos : 0 < Δ₀ := by linarith
    have hΔ₀leA : Δ₀ ≤ A := by
      rw [hΔ₀def]
      calc A ^ ((1:ℝ)/20) ≤ A ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
        _ = A := Real.rpow_one A
    have hL8 : L ^ (8:ℝ) ≤ A ^ ((1:ℝ)/10) := by
      rw [hLdef]; simpa using hA₀b A hAA₀
    have hBLe : B ≤ Cb * A * L := by
      have h := hCb A B hB16 hAB hAB2
      rw [hLdef]; linarith
    have hlog2Δ : Real.log (2 * Δ₀) ≤ L := by
      have h1 : Real.log (2 * Δ₀) = Real.log 2 + Real.log Δ₀ :=
        Real.log_mul (by norm_num) (ne_of_gt hΔ₀pos)
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      have h3 : Real.log Δ₀ ≤ Real.log A := Real.log_le_log hΔ₀pos hΔ₀leA
      rw [h1, hLdef]; linarith
    have hlog2sq : Real.log (2 * Δ₀) ^ 2 ≤ L ^ 2 := by
      have h2 : (0:ℝ) ≤ Real.log (2 * Δ₀) := Real.log_nonneg (by linarith)
      nlinarith [hlog2Δ, hL1]
    set F : Finset ((Fin 5 → ℤ) × (Fin 5 → ℤ)) := (SLset_finite A B).toFinset with hFdef
    have hFcoe : (F : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))) = SLset A B :=
      (SLset_finite A B).coe_toFinset
    have hN : (F.card : ℝ) ≤ Kc * B ^ 6 * Δ₀ ^ 3 * Real.log (2 * Δ₀) ^ 2 := by
      have h := SL_card_bound Kc A B hKc hA1 hB1
      rw [← hΔ₀def] at h
      have h1 : ((SLset A B).ncard : ℝ) = (F.card : ℝ) := by
        rw [← hFcoe, Set.ncard_coe_finset]
      linarith
    have hN2 : (F.card : ℝ) ≤ 4 * Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 := by
      have h0 : (0:ℝ) ≤ Kc * B ^ 6 * Δ₀ ^ 3 := by positivity
      have h2 : Kc * B ^ 6 * Δ₀ ^ 3 * Real.log (2 * Δ₀) ^ 2 ≤ Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hlog2sq h0
      have h4 : Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 ≤ 4 * (Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2) := by
        nlinarith [h0, sq_nonneg L]
      linarith
    have hN2r : (F.card : ℝ) ≤ 4 * Kc * B ^ (6:ℝ) * Δ₀ ^ (3:ℝ) * L ^ (2:ℝ) := by
      have h := hN2
      rw [← Real.rpow_natCast B 6, ← Real.rpow_natCast Δ₀ 3, ← Real.rpow_natCast L 2] at h
      exact h
    have hNlog : Kc * B ^ 6 * Δ₀ ^ 3 * Real.log (2 * Δ₀) ^ 2 ≤ 4 * Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 := by
      have h0 : (0:ℝ) ≤ Kc * B ^ 6 * Δ₀ ^ 3 := by positivity
      have h2 : Kc * B ^ 6 * Δ₀ ^ 3 * Real.log (2 * Δ₀) ^ 2 ≤ Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hlog2sq h0
      have h4 : Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2 ≤ 4 * (Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2) := by
        nlinarith [h0, sq_nonneg L]
      linarith
    have hSumD0 := sum_D_le Kc Kct Kdm A B hKcpos.le hKctpos.le F hFcoe hN hKct hKdm hA1 hB1
    have hSumD : (∑ p ∈ F, (Dp p) ^ (-(1:ℝ)))
        ≤ (Kdm * Kct ^ ((1:ℝ)/4) * (4 * Kc) ^ ((3:ℝ)/4))
          * (B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2)) := by
      refine le_trans hSumD0 ?_
      have h1 : (1:ℝ) - (1:ℝ)/4 = (3:ℝ)/4 := by norm_num
      rw [h1]
      have h2 := Real.rpow_le_rpow (by positivity) hNlog (by norm_num : (0:ℝ) ≤ (3:ℝ)/4)
      rw [rpow_34_split (B := B) (Δ₀ := Δ₀) (L := L) (Kc := Kc) hBpos
        hΔ₀pos hLpos (by positivity)] at h2
      calc Kdm * Kct ^ ((1:ℝ)/4)
            * (Kc * B ^ 6 * Δ₀ ^ 3 * Real.log (2 * Δ₀) ^ 2) ^ ((3:ℝ)/4)
          ≤ Kdm * Kct ^ ((1:ℝ)/4)
              * ((4 * Kc) ^ ((3:ℝ)/4) * B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (Kdm * Kct ^ ((1:ℝ)/4) * (4 * Kc) ^ ((3:ℝ)/4))
              * (B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2)) := by ring
    have hSumL0 := sum_lam_le Kc K44 Klm A B hKcpos.le hK44pos.le F hFcoe hN hK44 hKlm Cd hCd hA1 hB1
    have hSumL : (∑ p ∈ F, (Lp p) ^ (-(9:ℝ)))
        ≤ (Klm * K44 ^ ((9:ℝ)/15) * (4 * Kc) ^ ((6:ℝ)/15))
          * (B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)) := by
      refine le_trans hSumL0 ?_
      have h1 : (1:ℝ) - (9:ℝ)/15 = (6:ℝ)/15 := by norm_num
      rw [h1]
      have h2 := Real.rpow_le_rpow (by positivity) hNlog (by norm_num : (0:ℝ) ≤ (6:ℝ)/15)
      have hsplit := rpow_915_split (B := B) (Δ₀ := Δ₀) (L := L) (K44 := K44) (Kc := 4 * Kc)
        hBpos hΔ₀pos hLpos (by positivity) (by positivity)
      calc Klm * (K44 * B ^ 4 * Δ₀ ^ 24) ^ ((9:ℝ)/15)
            * (Kc * B ^ 6 * Δ₀ ^ 3 * Real.log (2 * Δ₀) ^ 2) ^ ((6:ℝ)/15)
          ≤ Klm * (K44 * B ^ 4 * Δ₀ ^ 24) ^ ((9:ℝ)/15)
              * ((4 * Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2) ^ ((6:ℝ)/15)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Klm * ((K44 * B ^ 4 * Δ₀ ^ 24) ^ ((9:ℝ)/15)
              * ((4 * Kc * B ^ 6 * Δ₀ ^ 3 * L ^ 2) ^ ((6:ℝ)/15))) := by ring
        _ = Klm * ((K44 ^ ((9:ℝ)/15) * (4 * Kc) ^ ((6:ℝ)/15))
              * (B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5))) := by rw [hsplit]
        _ = (Klm * K44 ^ ((9:ℝ)/15) * (4 * Kc) ^ ((6:ℝ)/15))
              * (B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)) := by ring
    have hCdetCl : ∀ x y : Fin 5 → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
        Cl⁻¹ * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * eNorm x ^ 3 * eNorm y ^ 3
          ≤ detL (Gam 4 4 x y) := by
      intro x y hx hy hLI
      have h := hCl x y hx hy hLI
      have h2 := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hClpos))
      have h4 : Cl⁻¹ * (Cl * detL (Gam 4 4 x y)) = detL (Gam 4 4 x y) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hClpos), one_mul]
      rw [h4] at h2
      have h5 : Cl⁻¹ * (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * eNorm x ^ (4 - 1) * eNorm y ^ (4 - 1))
          = Cl⁻¹ * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * eNorm x ^ 3 * eNorm y ^ 3 := by
        rw [show (4:ℕ) - 1 = 3 by norm_num]
        ring
      rw [h5] at h2
      exact h2
    have h70b : NN 4 4 = 70 := by
      rw [show NN 4 4 = Fintype.card (Mon 4 4) from rfl, Q44Child.card_mon44]
    have hDpos : ∀ p ∈ F, 0 < Dp p := by
      intro p hp
      have hpS : p ∈ SLset A B := by rw [← hFcoe]; exact hp
      have hLI := Sig2.li_of_mem_Omega 4 4 B p hpS.1
      have h1 : 0 < eNorm p.1 := eNorm_pos_of_ne_zero (ne_zero_of_LI1 hLI)
      have h2 : 0 < eNorm p.2 := eNorm_pos_of_ne_zero (ne_zero_of_LI2 hLI)
      have h3 : 0 < dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) :=
        lt_of_lt_of_le zero_lt_one ((dmin_facts 4 (by norm_num)).2.2.1 p.1 p.2 hLI)
      unfold Dp
      positivity
    have hLlpos : ∀ p ∈ F, 0 < Lp p := by
      intro p hp
      have hpS : p ∈ SLset A B := by rw [← hFcoe]; exact hp
      have hnu := Sig2.nu_indep 4 4 (by norm_num) p.1 p.2 hpS.1.1.1 hpS.1.2.1.1
        hpS.1.2.2.1 hpS.1.2.2.2
      obtain ⟨hrk, -⟩ := Sig2.gam_rank_det 4 4 p.1 p.2 hnu
      have h68 : rk (Gam 4 4 p.1 p.2) = 68 := by rw [hrk, h70b]
      have h1 := one_le_lam (Gam 4 4 p.1 p.2) (i := 56) (by norm_num) (by rw [h68]; norm_num)
      unfold Lp
      linarith
    have hpt : ∀ p ∈ F, pairS0 4 4 A p
        ≤ Kp * (48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹ * (A ^ (68 - 3) * (1 / Dp p))
            + (2 * A) ^ 55 * ((2 * A / Lp p) ^ 9 + 1)) := by
      intro p hp
      have hpS : p ∈ SLset A B := by rw [← hFcoe]; exact hp
      exact pointwise Kp Cd Cl⁻¹ hCd hKp hCdetCl hKppos hCdpos (inv_pos.mpr hClpos) hA1 hpS
    have hpw : ∀ p ∈ F, (2 * A / Lp p) ^ 9 = (2 * A) ^ 9 * (Lp p) ^ (-(9:ℝ)) := by
      intro p hp
      have h0 := hLlpos p hp
      rw [div_pow, div_eq_mul_inv, ← Real.rpow_natCast (Lp p) 9, ← Real.rpow_neg h0.le]
      norm_num
    have hpinv : ∀ p ∈ F, (1 / Dp p) = (Dp p) ^ (-(1:ℝ)) := by
      intro p hp
      have h0 := hDpos p hp
      rw [Real.rpow_neg h0.le, Real.rpow_one, one_div]
    have hsum_eq : ∑ p ∈ F, (Kp * (48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹
            * (A ^ (68 - 3) * (1 / Dp p)) + (2 * A) ^ 55 * ((2 * A / Lp p) ^ 9 + 1)))
        = Kp * ((48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹)
            * (A ^ (68 - 3) * (∑ p ∈ F, (Dp p) ^ (-(1:ℝ))))
            + (2 * A) ^ 55 * ((2 * A) ^ 9 * (∑ p ∈ F, (Lp p) ^ (-(9:ℝ))) + (F.card : ℝ))) := by
      rw [← Finset.mul_sum]
      congr 1
      have hpt2 : ∀ p ∈ F, (48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹ * (A ^ (68 - 3) * (1 / Dp p))
            + (2 * A) ^ 55 * ((2 * A / Lp p) ^ 9 + 1))
          = ((48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹) * (A ^ (68 - 3) * (Dp p) ^ (-(1:ℝ)))
            + ((2 * A) ^ 55 * ((2 * A) ^ 9 * (Lp p) ^ (-(9:ℝ))) + (2 * A) ^ 55 * 1)) := by
        intro p hp
        rw [hpinv p hp, hpw p hp, mul_add, mul_one]
      rw [Finset.sum_congr rfl hpt2]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      ring
    have hbound : ∑ p ∈ F, (Kp * (48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹
            * (A ^ (68 - 3) * (1 / Dp p)) + (2 * A) ^ 55 * ((2 * A / Lp p) ^ 9 + 1)))
        ≤ Kp * ((48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹)
            * (A ^ (68 - 3) * ((Kdm * Kct ^ ((1:ℝ)/4) * (4 * Kc) ^ ((3:ℝ)/4))
                * (B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2))))
        + (2 * A) ^ 55 * ((2 * A) ^ 9
            * ((Klm * K44 ^ ((9:ℝ)/15) * (4 * Kc) ^ ((6:ℝ)/15))
                * (B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)))
          + 4 * Kc * B ^ (6:ℝ) * Δ₀ ^ (3:ℝ) * L ^ (2:ℝ))) := by
      rw [hsum_eq]
      apply mul_le_mul_of_nonneg_left _ hKppos.le
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹)
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ A ^ (68 - 3))
        exact hSumD
      · apply mul_le_mul_of_nonneg_left
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hSumL (by positivity)
          · exact hN2r
        · positivity
    have hmono : Kp * ((48 ^ 3 * (max Cd 1) ^ 3 / Cl⁻¹)
            * (A ^ (68 - 3) * ((Kdm * Kct ^ ((1:ℝ)/4) * (4 * Kc) ^ ((3:ℝ)/4))
                * (B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2))))
        + (2 * A) ^ 55 * ((2 * A) ^ 9
            * ((Klm * K44 ^ ((9:ℝ)/15) * (4 * Kc) ^ ((6:ℝ)/15))
                * (B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)))
          + 4 * Kc * B ^ (6:ℝ) * Δ₀ ^ (3:ℝ) * L ^ (2:ℝ)))
        = c1 * A ^ 65 * B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2)
          + c2 * A ^ 64 * B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)
          + c3 * A ^ 55 * B ^ (6:ℝ) * Δ₀ ^ (3:ℝ) * L ^ (2:ℝ) := by
      rw [hc1, hc2, hc3]
      ring_nf
    have hsum_le : ∑ p ∈ F, pairS0 4 4 A p
        ≤ c1 * A ^ 65 * B ^ ((9:ℝ)/2) * Δ₀ ^ ((9:ℝ)/4) * L ^ ((3:ℝ)/2)
          + c2 * A ^ 64 * B ^ ((24:ℝ)/5) * Δ₀ ^ ((78:ℝ)/5) * L ^ ((4:ℝ)/5)
          + c3 * A ^ 55 * B ^ (6:ℝ) * Δ₀ ^ (3:ℝ) * L ^ (2:ℝ) := by
      refine le_trans (Finset.sum_le_sum hpt) ?_
      refine le_trans hbound ?_
      exact le_of_eq hmono
    have harith := arith_three A B L Δ₀ Cb c1 c2 c3 hA1 hB1 hL1 hΔ₀def hL8 hBLe hCbpos
      hc1pos hc2pos hc3pos
    have hfinsum : (∑ᶠ p ∈ {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧
          ¬ (muXY 4 p.1 p.2 ≤ A) ∧
          ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
              ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
          dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1 : ℝ) / 20)},
        pairS0 4 4 A p) = ∑ p ∈ F, pairS0 4 4 A p := by
      rw [← SLset_eq_state A B, ← hFcoe, finsum_mem_coe_finset]
    have hexp : ((NN 4 4 : ℝ) - 2 - (1 : ℝ) / 32) = ((68:ℝ) - 1/32) := by
      rw [h70b]; norm_num
    rw [hfinsum, hexp]
    rw [← Real.rpow_natCast B 2]
    refine le_trans hsum_le ?_
    rw [← Real.rpow_natCast A 65, ← Real.rpow_natCast A 64, ← Real.rpow_natCast A 55]
    exact harith

end Work.HP.MDEstimates
