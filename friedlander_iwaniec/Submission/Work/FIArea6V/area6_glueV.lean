/-
# `Submission.Work.FIArea6V.area6_glueV` — the numerical step of *FI* §16, τ-vacuous lane

The V-analogue of `Submission/Work/FIArea6c/area6_glueC.lean`: the paper's display for `U(β)`
(with `H = X`, `K = X³`) implies the τ-vacuous area-6 contract `Area6_6V`

  `‖U(β)‖ ≤ cν (P^{-1} + X^{-1}) N² log N`.

The only difference from the pinned lane is that the datum hypothesis `Pa.τ = tauOf Pa.x Asave`
is replaced by `TauVac Pa φ` (and the `IsAxisFree` clause is already present in the §16 display
itself); `Pa.τ` is not used in the numerical step, so the proof is a shape-for-shape
transliteration of the pinned one, with the elementary numerical lemmas restated here in
namespace `Work.FIArea6V` (they are `private` in the pinned lane).
-/
import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FITop4.Areas6c
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6.S16UDefs

set_option autoImplicit false

namespace Work.FIArea6V

open Work.FITop4

noncomputable section

/-! ## Elementary auxiliary lemmas for the §16 numerical step -/

/-- `0 < nuU = 3 * sigmaChoice Asave + 4`. -/
private lemma area6glueV_nuU_pos : 0 < Work.FITop4.nuU := by
  unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
  norm_num

/-- **Exponential beats any polynomial.**  For `c > 0`, `K ≥ 1` and `p ≥ 0` there is `L₀ ≥ 0` with
`K * L^p ≤ exp(c * L)` for every `L ≥ L₀`.  With `s = √L` this is `c·s² ≥ log K + 2p·s`, using
`log L ≤ 2√L`. -/
private lemma area6glueV_cst_mul_rpow_le_exp (c K p : ℝ) (hc : 0 < c) (hK : 1 ≤ K) (hp : 0 ≤ p) :
    ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → K * L ^ p ≤ Real.exp (c * L) := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  refine ⟨max 1 (((2*p + Real.log K)/c)^2), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hA0 : 0 ≤ (2*p + Real.log K)/c := by positivity
  have hs_ge : (2*p + Real.log K)/c ≤ Real.sqrt L := by
    have h2 : ((2*p + Real.log K)/c)^2 ≤ L := le_trans (le_max_right _ _) hL
    calc (2*p + Real.log K)/c = Real.sqrt (((2*p + Real.log K)/c)^2) := (Real.sqrt_sq hA0).symm
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt h2
  have hcs : 2*p + Real.log K ≤ c * Real.sqrt L := by
    have := mul_le_mul_of_nonneg_left hs_ge hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have hineq : Real.log K + p * Real.log L ≤ c * L := by
    have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
      have h := Real.log_le_rpow_div hLpos.le (by norm_num : (0:ℝ) < 1/2)
      have h2 : L ^ ((1:ℝ)/2) / (1/2) = 2 * Real.sqrt L := by
        rw [← Real.sqrt_eq_rpow]; ring
      linarith [h, h2.le]
    have hp_logL : p * Real.log L ≤ p * (2 * Real.sqrt L) := mul_le_mul_of_nonneg_left hlogL hp
    have hsq : Real.sqrt L * Real.sqrt L = L := by rw [← pow_two]; exact Real.sq_sqrt hLpos.le
    have hcs2 : c * Real.sqrt L * Real.sqrt L = c * L := by rw [mul_assoc, hsq]
    nlinarith [hp_logL, hcs, hcs2, Real.sqrt_nonneg L]
  rw [← Real.exp_log (lt_of_lt_of_le one_pos hK)]
  rw [Real.rpow_def_of_pos hLpos]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [hineq])

/-- **A quadratic eventually dominates a linear function.**  For `A > 0`, `B ≥ 0`, `D ≥ 0` there is
`u₀ ≥ 0` with `B*u + D ≤ A*u²` for `u ≥ u₀` (take `u₀ = max 1 ((B+D)/A)`). -/
private lemma area6glueV_lin_le_quad (A B D : ℝ) (hA : 0 < A) (_hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ u₀ : ℝ, 0 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → B*u + D ≤ A*u^2 := by
  refine ⟨max 1 ((B+D)/A), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro u hu
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hAu : B + D ≤ A*u := by
    have h2 : (B+D)/A ≤ u := le_trans (le_max_right _ _) hu
    have h3 := mul_le_mul_of_nonneg_left h2 hA.le
    rwa [mul_div_cancel₀ (B+D) hA.ne'] at h3
  have h1 : B*u + D ≤ (B+D)*u := by nlinarith [hu1]
  have h2 : (B+D)*u ≤ A*u^2 := by
    have h3 := mul_le_mul_of_nonneg_right hAu (le_of_lt hu0)
    nlinarith [h3]
  linarith

/-! ## The two thresholds -/

/-- **The `exp(-c₁(log N)^{1/4})` term is absorbed for large `x`**: there is `x₀ > 0` such that for
every admissible datum with `x₀ ≤ x`, `2^14 (log N)^{6ν+12} ≤ exp(c₁(log N)^{1/4})` (with
`ν = nuU`).  This is `X⁵(log(2+N))^{13} exp(-c₁(log N)^{1/4}) ≤ (1/2)X^{-1}log N` after using
`X ≤ (log N)^ν`. -/
private lemma area6glueV_factA (c1 : ℝ) (hc1 : 0 < c1) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ (Pa : Work.FITop.Params), x₀ ≤ (Pa.x : ℝ) →
      (2:ℝ)^14 * (Real.log Pa.N)^(6 * Work.FITop4.nuU + 12)
        ≤ Real.exp (c1 * (Real.log Pa.N)^((1:ℝ)/4)) := by
  have hν : 0 < Work.FITop4.nuU := area6glueV_nuU_pos
  have h4p : (0:ℝ) ≤ 4 * (6 * Work.FITop4.nuU + 12) := by linarith
  obtain ⟨L₀, hL₀0, hL₀⟩ :=
    area6glueV_cst_mul_rpow_le_exp c1 ((2:ℝ)^14) (4*(6*Work.FITop4.nuU+12)) hc1 (by norm_num) h4p
  refine ⟨Real.exp (L₀^4 / (1/4)) + 1, by positivity, ?_⟩
  intro Pa hx
  have hx3 : (3:ℝ) ≤ (Pa.x:ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0:ℝ) < (Pa.x:ℝ) := by linarith
  have hT : L₀^4 / (1/4) < Real.log (Pa.x:ℝ) := by
    have hxlarge : Real.exp (L₀^4 / (1/4)) < (Pa.x : ℝ) := by linarith
    have := Real.log_lt_log (Real.exp_pos _) hxlarge
    rwa [Real.log_exp] at this
  have hbase : (1:ℝ) ≤ (Pa.x:ℝ) := by linarith
  have hexp : (1/4:ℝ) ≤ 1/4 + Pa.η := by linarith [Pa.hη]
  have hle := Real.rpow_le_rpow_of_exponent_le hbase hexp (x := (Pa.x:ℝ))
  have hlt := lt_of_le_of_lt hle Pa.hNlo
  have hlogn : (1/4:ℝ) * Real.log (Pa.x:ℝ) < Real.log Pa.N := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) hlt
    rwa [Real.log_rpow hxpos] at h
  have hT4 : L₀^4 < (1/4:ℝ) * Real.log (Pa.x:ℝ) := by
    have : (1/4:ℝ) * (L₀^4/(1/4)) = L₀^4 := by
      rw [mul_comm, div_mul_cancel₀ _ (by norm_num : (1/4:ℝ) ≠ 0)]
    nlinarith [hT, this]
  have hn_gt_L04 : L₀^4 < Real.log Pa.N := lt_trans hT4 hlogn
  have hnpos : (0:ℝ) < Real.log Pa.N := lt_of_le_of_lt (pow_nonneg hL₀0 4) hn_gt_L04
  have hLge : L₀ ≤ (Real.log Pa.N)^((1:ℝ)/4) := by
    have h4 : L₀^4 ≤ Real.log Pa.N := le_of_lt hn_gt_L04
    calc L₀ = (L₀^4)^((1:ℝ)/4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL₀0]; norm_num
      _ ≤ (Real.log Pa.N)^((1:ℝ)/4) := Real.rpow_le_rpow (pow_nonneg hL₀0 4) h4 (by norm_num)
  have hkey := hL₀ ((Real.log Pa.N)^((1:ℝ)/4)) hLge
  have hrw : ((Real.log Pa.N)^((1:ℝ)/4))^(4*(6*Work.FITop4.nuU+12))
      = (Real.log Pa.N)^(6*Work.FITop4.nuU+12) := by
    rw [← Real.rpow_mul hnpos.le]
    congr 1
    ring
  rwa [hrw] at hkey

/-- **The `exp(-c₂ log N/log P)` term is absorbed for large `x`**: there is `x₀ > 0` such that for
every admissible datum with `x₀ ≤ x`, `2^14 (log N)^{6ν+12} ≤ exp(c₂ log N/log P)` (with
`ν = nuU`).  Uses `log N > (1/4)log x`, `log P ≤ log x (loglog x)^{-2}` (so
`log N/log P ≥ (1/4)(loglog x)²`) and `log N ≤ log x`. -/
private lemma area6glueV_factB (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ (Pa : Work.FITop.Params), x₀ ≤ (Pa.x : ℝ) →
      (2:ℝ)^14 * (Real.log Pa.N)^(6 * Work.FITop4.nuU + 12)
        ≤ Real.exp (c2 * Real.log Pa.N / Real.log (Pa.Pz:ℝ)) := by
  have hν : 0 < Work.FITop4.nuU := area6glueV_nuU_pos
  have hp : (0:ℝ) ≤ 6 * Work.FITop4.nuU + 12 := by linarith
  have hD : (0:ℝ) ≤ 14 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  obtain ⟨u₀, hu₀0, hu₀⟩ := area6glueV_lin_le_quad (c2/4) (6*Work.FITop4.nuU+12)
      (14*Real.log 2) (by linarith) hp hD
  refine ⟨Real.exp (max 4 (Real.exp u₀)) + 1, by positivity, ?_⟩
  intro Pa hx
  have hx3 : (3:ℝ) ≤ (Pa.x:ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0:ℝ) < (Pa.x:ℝ) := by linarith
  have hIpos : (0:ℝ) < 1/4 + Pa.η := by linarith [Pa.hη]
  set lx : ℝ := Real.log (Pa.x:ℝ) with hlx
  have hlpos : (0:ℝ) < lx := by rw [hlx]; exact Real.log_pos (by linarith)
  have hTlt : max 4 (Real.exp u₀) < lx := by
    rw [hlx]
    have hxlarge : Real.exp (max 4 (Real.exp u₀)) < (Pa.x:ℝ) := by linarith
    have h := Real.log_lt_log (Real.exp_pos _) hxlarge
    rwa [Real.log_exp] at h
  have hlogx4 : (4:ℝ) < lx := lt_of_le_of_lt (le_max_left _ _) hTlt
  set u : ℝ := Real.log lx with hu
  have hu_gt : u₀ < u := by
    rw [hu]
    have h1 : Real.log (Real.exp u₀) < Real.log lx :=
      Real.log_lt_log (Real.exp_pos u₀) (lt_of_le_of_lt (le_max_right _ _) hTlt)
    rwa [Real.log_exp] at h1
  have hupos : (0:ℝ) < u := lt_of_le_of_lt hu₀0 hu_gt
  have hle1 : (1/4 + Pa.η) * lx ≤ Real.log Pa.N := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos ((1:ℝ)/4 + Pa.η)) Pa.hNlo
    rw [Real.log_rpow hxpos] at h
    exact le_of_lt h
  have hNpos : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
  have hNlex : Pa.N ≤ (Pa.x:ℝ) := by
    have h1 : Pa.N ≤ Pa.M * Pa.N := by nlinarith [Pa.hM1, Pa.hN1]
    exact le_trans h1 Pa.hMNx
  have hnpos : (0:ℝ) < Real.log Pa.N :=
    lt_of_lt_of_le (mul_pos hIpos hlpos) hle1
  have hnle_lx : Real.log Pa.N ≤ lx := by
    rw [hlx]; exact Real.log_le_log hNpos hNlex
  have hlogn_le : Real.log (Real.log Pa.N) ≤ u := by
    have h := Real.log_le_log hnpos hnle_lx
    rw [hu]; exact h
  have hPz1 : (1:ℝ) < (Pa.Pz:ℝ) := by
    have : (2:ℝ) ≤ (Pa.Pz:ℝ) := by exact_mod_cast Pa.hP2
    linarith
  have hpPpos : (0:ℝ) < Real.log (Pa.Pz:ℝ) := Real.log_pos hPz1
  have hPhi' : Real.log (Pa.Pz:ℝ) ≤ lx / u^2 := by
    have h := Pa.hPhi
    have hz : Real.log (Real.log (Pa.x:ℝ)) ^ (-2:ℤ) = (u^2)⁻¹ := by
      rw [hu, hlx]
      rw [show (-2:ℤ) = -((2:ℕ):ℤ) by norm_num, zpow_neg, zpow_natCast]
    rw [hz] at h
    rw [← hlx] at h
    simpa [div_eq_mul_inv] using h
  have hAstep : (1/4+Pa.η)*u^2 ≤ Real.log Pa.N / Real.log (Pa.Pz:ℝ) := by
    rw [le_div_iff₀ hpPpos]
    have h1 : (1/4+Pa.η)*u^2 * Real.log (Pa.Pz:ℝ) ≤ (1/4+Pa.η)*u^2 * (lx/u^2) :=
      mul_le_mul_of_nonneg_left hPhi' (by positivity)
    have h2 : (1/4+Pa.η)*u^2 * (lx/u^2) = (1/4+Pa.η)*lx := by
      field_simp
    rw [h2] at h1
    exact le_trans h1 hle1
  have hA_ge : c2/4 * u^2 ≤ c2*(1/4+Pa.η)*u^2 := by
    have hc : c2/4 ≤ c2*(1/4+Pa.η) := by
      have h1 : (1/4:ℝ) * c2 ≤ (1/4+Pa.η)*c2 :=
        mul_le_mul_of_nonneg_right (by linarith [Pa.hη]) hc2.le
      linarith
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg u)
  have hpu : (6*Work.FITop4.nuU+12)*u + 14*Real.log 2 ≤ c2*(1/4+Pa.η)*u^2 :=
    le_trans (hu₀ u (le_of_lt hu_gt)) hA_ge
  have h2pow : (2:ℝ)^14 = Real.exp ((14:ℝ)*Real.log 2) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < (2:ℝ)^14), Real.log_pow]
    norm_num
  have hnpow : (Real.log Pa.N)^(6*Work.FITop4.nuU+12)
      = Real.exp (Real.log (Real.log Pa.N) * (6*Work.FITop4.nuU+12)) :=
    Real.rpow_def_of_pos hnpos _
  rw [h2pow, hnpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hstep : Real.log (Real.log Pa.N) * (6*Work.FITop4.nuU+12)
      ≤ u * (6*Work.FITop4.nuU+12) :=
    mul_le_mul_of_nonneg_right hlogn_le hp
  have hstep2 : (6*Work.FITop4.nuU+12) * u ≤ c2*(1/4+Pa.η)*u^2 - 14*Real.log 2 := by linarith
  have hstep3 : c2*(1/4+Pa.η)*u^2 ≤ c2*(Real.log Pa.N/Real.log (Pa.Pz:ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hAstep hc2.le
    rwa [← mul_assoc] at h
  rw [mul_div_assoc]
  linarith [hstep, hstep2, hstep3]

/-! ## The numerical combination -/

/-- From `2^14 A^{6ν+12} ≤ exp(cB)`: `exp(-(cB)) · 2^13 A^{6ν+13} ≤ A/2`. -/
private lemma area6glueV_exp_mul_rpow_le (A c B : ℝ) (hA : 0 < A)
    (h : (2:ℝ)^14 * A^(6*Work.FITop4.nuU+12) ≤ Real.exp (c*B)) :
    Real.exp (-(c*B)) * ((2:ℝ)^13 * A^(6*Work.FITop4.nuU+13)) ≤ A/2 := by
  have heB : 0 < Real.exp (-(c*B)) := Real.exp_pos _
  have h1 : (2:ℝ)^14 * A^(6*Work.FITop4.nuU+12) * Real.exp (-(c*B)) ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_right h heB.le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
    exact h2
  have hb : (2:ℝ)^13 * A^(6*Work.FITop4.nuU+12) * Real.exp (-(c*B)) ≤ 1/2 := by
    have heq : (2:ℝ)^14 * A^(6*Work.FITop4.nuU+12) * Real.exp (-(c*B))
        = 2 * ((2:ℝ)^13 * A^(6*Work.FITop4.nuU+12) * Real.exp (-(c*B))) := by ring
    rw [heq] at h1
    linarith [h1]
  have h2 : (2:ℝ)^13 * A^(6*Work.FITop4.nuU+12) * Real.exp (-(c*B)) * A ≤ A/2 := by
    have := mul_le_mul_of_nonneg_right hb hA.le
    linarith [this]
  have hApa : A^(6*Work.FITop4.nuU+13) = A^(6*Work.FITop4.nuU+12) * A := by
    rw [show (6*Work.FITop4.nuU+13) = (6*Work.FITop4.nuU+12) + 1 by ring,
        Real.rpow_add hA, Real.rpow_one]
  have hconv : Real.exp (-(c*B)) * ((2:ℝ)^13 * A^(6*Work.FITop4.nuU+13))
      = (2:ℝ)^13 * A^(6*Work.FITop4.nuU+12) * Real.exp (-(c*B)) * A := by
    rw [hApa]; ring
  rw [hconv]; exact h2

/-- **The numerical assembly**: given the two absorbed-term inequalities, the paper's display for
`U(β)` gives the `Area6_6V` bound `(E₁+E₂)X⁵(log(2+N))^{13} ≤ X^{-1}log N`. -/
private lemma area6glueV_key_numeric (Pa : Work.FITop.Params) (n c1 c2 : ℝ)
    (hn : Real.log Pa.N = n)
    (X : ℕ) (hX1 : 1 ≤ X) (hXle : (X:ℝ) ≤ n^Work.FITop4.nuU)
    (hN : 2 ≤ n)
    (hA : (2:ℝ)^14 * n^(6*Work.FITop4.nuU+12) ≤ Real.exp (c1 * n^((1:ℝ)/4)))
    (hB : (2:ℝ)^14 * n^(6*Work.FITop4.nuU+12) ≤ Real.exp (c2 * n / Real.log (Pa.Pz:ℝ))) :
    (Real.exp (-(c1 * n^((1:ℝ)/4)))
      + Real.exp (-(c2 * (n / Real.log (Pa.Pz:ℝ)))))
      * (X:ℝ)^5 * (Real.log (2 + Pa.N))^(13:ℕ)
      ≤ (X:ℝ)⁻¹ * n := by
  have hnpos : 0 < n := by rw [← hn]; linarith
  have hnbase : (0:ℝ) ≤ n := le_of_lt hnpos
  have hXpos : (0:ℝ) < (X:ℝ) := by
    have : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
    linarith
  have hX6 : (X:ℝ)^6 ≤ n^(6*Work.FITop4.nuU) := by
    have h1 : (X:ℝ)^6 ≤ (n^Work.FITop4.nuU)^6 := pow_le_pow_left₀ (by positivity) hXle 6
    have h2 : (n^Work.FITop4.nuU)^6 = n^(6*Work.FITop4.nuU) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnbase]
      congr 1; ring
    rwa [h2] at h1
  have hN2 : (2:ℝ) ≤ (Pa.N:ℝ) := by
    have h1 : Real.exp 2 ≤ Real.exp (Real.log Pa.N) := Real.exp_le_exp.mpr (by rw [hn]; exact hN)
    rw [Real.exp_log (by linarith [Pa.hN1])] at h1
    have h2 : (2:ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2:ℝ); linarith [this]
    linarith
  have hlog2N : Real.log (2 + Pa.N) ≤ 2 * n := by
    have h1 : Real.log (2 + Pa.N) ≤ Real.log (2 * Pa.N) :=
      Real.log_le_log (by linarith [Pa.hN1]) (by nlinarith [hN2])
    have h2 : Real.log (2 * Pa.N) = Real.log 2 + n := by
      rw [Real.log_mul (by norm_num) (by linarith [Pa.hN1]), hn]
    rw [h2] at h1
    have h3 : Real.log 2 ≤ n := by
      rw [← hn]; exact Real.log_le_log (by norm_num) hN2
    linarith
  have hlog13 : (Real.log (2+Pa.N))^(13:ℕ) ≤ (2*n)^(13:ℕ) :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith [Pa.hN1])) hlog2N 13
  have hnmul : n^(6*Work.FITop4.nuU) * n^(13:ℕ) = n^(6*Work.FITop4.nuU+13) := by
    have h1 : n^(13:ℕ) = n^((13:ℕ):ℝ) := (Real.rpow_natCast n 13).symm
    rw [h1, ← Real.rpow_add hnpos]
    norm_num
  have hstep : (X:ℝ)^6 * (Real.log (2+Pa.N))^(13:ℕ) ≤ (2:ℝ)^13 * n^(6*Work.FITop4.nuU+13) := by
    calc (X:ℝ)^6 * (Real.log (2+Pa.N))^(13:ℕ)
        ≤ n^(6*Work.FITop4.nuU) * (2*n)^(13:ℕ) :=
          mul_le_mul hX6 hlog13 (pow_nonneg (Real.log_nonneg (by linarith [Pa.hN1])) 13)
            (Real.rpow_nonneg hnbase _)
      _ = n^(6*Work.FITop4.nuU) * ((2:ℝ)^13 * n^(13:ℕ)) := by rw [mul_pow]
      _ = (2:ℝ)^13 * (n^(6*Work.FITop4.nuU) * n^(13:ℕ)) := by ring
      _ = (2:ℝ)^13 * n^(6*Work.FITop4.nuU+13) := by rw [hnmul]
  have hE1 : Real.exp (-(c1 * n^((1:ℝ)/4))) * ((2:ℝ)^13 * n^(6*Work.FITop4.nuU+13)) ≤ n/2 :=
    area6glueV_exp_mul_rpow_le n c1 (n^((1:ℝ)/4)) hnpos hA
  have hB' : (2:ℝ)^14 * n^(6*Work.FITop4.nuU+12) ≤ Real.exp (c2 * (n / Real.log (Pa.Pz:ℝ))) := by
    rw [mul_div_assoc] at hB; exact hB
  have hE2 : Real.exp (-(c2 * (n / Real.log (Pa.Pz:ℝ))))
      * ((2:ℝ)^13 * n^(6*Work.FITop4.nuU+13)) ≤ n/2 :=
    area6glueV_exp_mul_rpow_le n c2 (n / Real.log (Pa.Pz:ℝ)) hnpos hB'
  have hbound : (Real.exp (-(c1 * n^((1:ℝ)/4))) + Real.exp (-(c2 * (n / Real.log (Pa.Pz:ℝ)))))
      * ((X:ℝ)^6 * (Real.log (2 + Pa.N))^(13:ℕ)) ≤ n := by
    refine le_trans (mul_le_mul_of_nonneg_left hstep (by positivity)) ?_
    have h4 : (Real.exp (-(c1*n^((1:ℝ)/4))) + Real.exp (-(c2*(n/Real.log (Pa.Pz:ℝ)))))
        * ((2:ℝ)^13 * n^(6*Work.FITop4.nuU+13))
        = Real.exp (-(c1*n^((1:ℝ)/4))) * ((2:ℝ)^13 * n^(6*Work.FITop4.nuU+13))
          + Real.exp (-(c2*(n/Real.log (Pa.Pz:ℝ)))) * ((2:ℝ)^13 * n^(6*Work.FITop4.nuU+13)) := by
      ring
    rw [h4]
    linarith [add_le_add hE1 hE2]
  have hb : (X:ℝ) * ((Real.exp (-(c1*n^((1:ℝ)/4))) + Real.exp (-(c2*(n/Real.log (Pa.Pz:ℝ)))))
      * (X:ℝ)^5 * (Real.log (2 + Pa.N))^(13:ℕ))
      = (Real.exp (-(c1*n^((1:ℝ)/4))) + Real.exp (-(c2*(n/Real.log (Pa.Pz:ℝ)))))
        * ((X:ℝ)^6 * (Real.log (2 + Pa.N))^(13:ℕ)) := by ring
  have hc : (X:ℝ) * ((X:ℝ)⁻¹ * n) = n := by
    rw [← mul_assoc, mul_inv_cancel₀ hXpos.ne', one_mul]
  have hfin : (X:ℝ) * ((Real.exp (-(c1*n^((1:ℝ)/4))) + Real.exp (-(c2*(n/Real.log (Pa.Pz:ℝ)))))
      * (X:ℝ)^5 * (Real.log (2 + Pa.N))^(13:ℕ)) ≤ (X:ℝ) * ((X:ℝ)⁻¹ * n) := by
    rw [hb, hc]; exact hbound
  exact (mul_le_mul_iff_of_pos_left hXpos).mp hfin

/-! ## The main glue -/

/-- **The numerical step of *FI* §16 in the τ-vacuous lane**: the paper's display for `U(β)` (with
`H = X`, `K = X³`) implies `Area6_6V`, i.e.

  `‖U(β)‖ ≤ cν(P^{-1} + X^{-1})N²log N`

for every `IsBetaCoeff6` coefficient `β` at τ-vacuous data and every `1 ≤ X ≤ (log N)^{nuU}` with
`X³ ≤ exp(√log N)`, once the threshold `x₀` is taken large enough (it depends on `η` only). -/
theorem area6_glueV : Work.FIArea6V.Section16UV → Work.FIArea6V.Area6_6V := by
  intro h16 η hη0 hη32
  obtain ⟨C, c1, c2, x₀, hC, hc1, hc2, hx0, h16'⟩ := h16 η hη0 hη32
  obtain ⟨xA, hxA, hA⟩ := area6glueV_factA c1 hc1
  obtain ⟨xB, hxB, hB⟩ := area6glueV_factB c2 hc2
  refine ⟨2*C, max (max x₀ xA) (max xB (Real.exp 8 + 1)) + 1, by positivity, ?_⟩
  intro Pa hPax hPaη X φ z0 β hτv hβ hfar hX1 hXle hX3
  have hx0' : x₀ ≤ (Pa.x:ℝ) := by
    have h1 : x₀ ≤ max (max x₀ xA) (max xB (Real.exp 8 + 1)) :=
      le_trans (le_max_left x₀ xA) (le_max_left _ _)
    linarith
  have hxA' : xA ≤ (Pa.x:ℝ) := by
    have h1 : xA ≤ max (max x₀ xA) (max xB (Real.exp 8 + 1)) :=
      le_trans (le_max_right x₀ xA) (le_max_left _ _)
    linarith
  have hxB' : xB ≤ (Pa.x:ℝ) := by
    have h1 : xB ≤ max (max x₀ xA) (max xB (Real.exp 8 + 1)) :=
      le_trans (le_max_left xB (Real.exp 8 + 1)) (le_max_right _ _)
    linarith
  have hxbig : Real.exp 8 + 1 ≤ (Pa.x:ℝ) := by
    have h1 : Real.exp 8 + 1 ≤ max (max x₀ xA) (max xB (Real.exp 8 + 1)) :=
      le_trans (le_max_right xB (Real.exp 8 + 1)) (le_max_right _ _)
    linarith
  have hx3 : (3:ℝ) ≤ (Pa.x:ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0:ℝ) < (Pa.x:ℝ) := by linarith
  have hbase : (1:ℝ) ≤ (Pa.x:ℝ) := by linarith
  have hlogx8 : (8:ℝ) < Real.log (Pa.x:ℝ) := by
    have h := Real.log_lt_log (x := Real.exp 8) (y := (Pa.x:ℝ)) (Real.exp_pos 8)
      (show Real.exp 8 < (Pa.x:ℝ) from by linarith [hxbig])
    rwa [Real.log_exp] at h
  have hle := Real.rpow_le_rpow_of_exponent_le hbase
    (show (1/4:ℝ) ≤ 1/4 + Pa.η from by linarith [Pa.hη]) (x := (Pa.x:ℝ))
  have hlt := lt_of_le_of_lt hle Pa.hNlo
  have hlogn : (1/4:ℝ) * Real.log (Pa.x:ℝ) < Real.log Pa.N := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) hlt
    rwa [Real.log_rpow hxpos] at h
  have hn2 : (2:ℝ) ≤ Real.log Pa.N := by linarith [hlogx8, hlogn]
  have hkey := area6glueV_key_numeric Pa (Real.log Pa.N) c1 c2 rfl X hX1 hXle hn2
    (hA Pa hxA') (hB Pa hxB')
  have h16'' := h16' Pa hx0' hPaη X φ z0 β hβ hτv hfar hX1 hXle hX3
  rw [mul_div_assoc] at h16''
  have hN2nn : (0:ℝ) ≤ Pa.N^2 := sq_nonneg _
  have hnn : (0:ℝ) ≤ Real.log Pa.N := le_of_lt (by linarith [hn2])
  have hterm1 : C * ((Real.exp (-(c1 * (Real.log Pa.N)^((1:ℝ)/4)))
        + Real.exp (-(c2 * (Real.log Pa.N / Real.log (Pa.Pz:ℝ)))))
        * (X:ℝ)^5 * Pa.N^2 * (Real.log (2 + Pa.N))^(13:ℕ))
      ≤ C * (((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N) := by
    have h1 : (Real.exp (-(c1 * (Real.log Pa.N)^((1:ℝ)/4)))
        + Real.exp (-(c2 * (Real.log Pa.N / Real.log (Pa.Pz:ℝ)))))
        * (X:ℝ)^5 * Pa.N^2 * (Real.log (2 + Pa.N))^(13:ℕ)
        ≤ ((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N := by
      have hxinv : (X:ℝ)⁻¹ * Real.log Pa.N ≤ ((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Real.log Pa.N := by
        have h2 : (X:ℝ)⁻¹ ≤ (Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹ := by
          have : (0:ℝ) ≤ (Pa.Pz:ℝ)⁻¹ := by positivity
          linarith
        exact mul_le_mul_of_nonneg_right h2 hnn
      calc (Real.exp (-(c1 * (Real.log Pa.N)^((1:ℝ)/4)))
            + Real.exp (-(c2 * (Real.log Pa.N / Real.log (Pa.Pz:ℝ)))))
            * (X:ℝ)^5 * Pa.N^2 * (Real.log (2 + Pa.N))^(13:ℕ)
          = ((Real.exp (-(c1 * (Real.log Pa.N)^((1:ℝ)/4)))
              + Real.exp (-(c2 * (Real.log Pa.N / Real.log (Pa.Pz:ℝ)))))
              * (X:ℝ)^5 * (Real.log (2 + Pa.N))^(13:ℕ)) * Pa.N^2 := by ring
        _ ≤ ((X:ℝ)⁻¹ * Real.log Pa.N) * Pa.N^2 := mul_le_mul_of_nonneg_right hkey hN2nn
        _ ≤ (((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Real.log Pa.N) * Pa.N^2 :=
            mul_le_mul_of_nonneg_right hxinv hN2nn
        _ = ((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N := by ring
    exact mul_le_mul_of_nonneg_left h1 hC.le
  calc ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖
      ≤ C * ((Real.exp (-(c1 * (Real.log Pa.N)^((1:ℝ)/4)))
          + Real.exp (-(c2 * (Real.log Pa.N / Real.log (Pa.Pz:ℝ)))))
          * (X:ℝ)^5 * Pa.N^2 * (Real.log (2 + Pa.N))^(13:ℕ))
        + C * ((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N := h16''
    _ = C * ((Real.exp (-(c1 * (Real.log Pa.N)^((1:ℝ)/4)))
          + Real.exp (-(c2 * (Real.log Pa.N / Real.log (Pa.Pz:ℝ)))))
          * (X:ℝ)^5 * Pa.N^2 * (Real.log (2 + Pa.N))^(13:ℕ))
        + C * (((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N) := by ring
    _ ≤ 2 * (C * (((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N)) := by linarith [hterm1]
    _ = (2*C) * ((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N := by ring

end

end Work.FIArea6V
