/-
# `FTS/PhiStar/Honesty/NodeAux` — a clean uniform tail estimate for the mode series

Auxiliary module for `Honesty/bslSolExists_moment_of_node_hyp`.  It provides the
uniform-in-`z` (and uniform-in-`θ`) bound on the tails of the mode series of the modal solution
`ModalSol.Psi α F`, its continuity on the open quadrant, its pointwise bound and its decay.

**Why this exists.**  The corresponding facts for `ModalSol.Psi` are stated in
`FTS/H2/ModalSol/Basic.lean`, but that module rests on the statement-only `sorry` of
`FTS/H2/ModalSol/TailBound/psiTrunc_tail.lean` (and on `ModalSol/Prelim/support.lean`), so
nothing on the solution path may import it.  Everything here is reproved from the clean
ingredients:

* `ModalSolution.psiTrunc_tail_bound` (clean): `|ψ_N − ψ_M| ≤ K√(P+Q)` with
  `P+Q = Σ_{M<m≤N}(1+λ_m)𝔄_m a_m(z)²`;
* `ModalSolution.radGreen_abs_le` (clean): `|a_m(z)| ≤ √(∫cmode m F²)·z^{-1/2}/(α(4m+5)√m)`;
* `ModalSolR.coeffL2_sum_le` (clean, Bessel): `Σ_{m≤N} 𝔄_m∫cmode m F² ≤ ∫_{Q0}F²`;
* `Gegenbauer.eFam_norm_fts` (clean): `𝔄_m = (2m+2)(2m+3)/(4m+5)`,
  `λ_m = 2m(2m+5)`.

Since `(1+λ_m)𝔄_m ≤ 4(4m+5)²m`, the tail is dominated by `(4/α²)z^{-1}Σ_{m>M}∫cmode m F²`,
and `Σ_m ∫cmode m F² < ∞` is exactly Bessel's inequality.  The mode `m = 0` never occurs in the
tail index set, so no `OrthCond` enters the *bound*; the orthogonality is used only for the
pointwise convergence `ψ_N → Psi` (imported, clean) and for the vanishing of `ψ_0`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.ModalSolR.PsiFacts
import Submission.Work.FTS.H2.ModalSolR.LimitFacts
import Submission.Work.FTS.H2.ModalSolR.CoeffBound
import Submission.Work.EllipticEst.ModalSolution.psiTrunc_tail_bound
import Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.NodeAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "cmode" => Work.FTS.PhiStar.Series.cmode
local notation "acoeff" => Work.FTS.PhiStar.Series.acoeff
local notation "psiTrunc" => Work.FTS.PhiStar.Series.psiTrunc
local notation "eNorm" => Work.EllipticEst.ModalSolution.eNorm
local notation "lam" => Work.FTS.PhiStar.Gegenbauer.lam
local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-! ## Uniform bounds on the mode coefficients -/

lemma lam_eq (m : ℕ) : lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := by
  rw [Work.FTS.PhiStar.Gegenbauer.lam]

lemma eNorm_ge_one (m : ℕ) : 1 ≤ eNorm m := by
  rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (m : ℝ) + 5)]
  nlinarith

/-- The arithmetic core: `(1+λ_m)𝔄_m` is comparable to `(4m+5)²m` (the quotient tends to `1/4`;
`4` is a generous constant). -/
lemma arith_ratio {m : ℕ} (hm : 1 ≤ m) :
    (1 + lam m) * eNorm m ≤ 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts, lam_eq]
  have hpos : (0 : ℝ) < 4 * (m : ℝ) + 5 := by linarith
  rw [div_eq_mul_inv]
  have hkey : (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
      ≤ 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) * (4 * (m : ℝ) + 5) := by
    have h3 : (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
        ≤ 4 * (4 * (m : ℝ) + 5) ^ 3 * (m : ℝ) := by
      nlinarith [sq_nonneg ((m : ℝ) - 1), sq_nonneg ((m : ℝ) ^ 2 - 1),
        sq_nonneg ((m : ℝ) ^ 3 - 1)]
    calc _ ≤ 4 * (4 * (m : ℝ) + 5) ^ 3 * (m : ℝ) := h3
      _ = 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) * (4 * (m : ℝ) + 5) := by ring
  calc (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5))
        * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) * (4 * (m : ℝ) + 5)⁻¹)
      = (1 + 2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
          * (4 * (m : ℝ) + 5)⁻¹ := by ring
    _ ≤ (4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) * (4 * (m : ℝ) + 5)) * (4 * (m : ℝ) + 5)⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by field_simp

/-- **Bessel's inequality in the form used below**: `Σ_m ∫_0^∞ (cmode m F)² < ∞`. -/
lemma cmode_sq_summable {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0) :
    Summable (fun m : ℕ => ∫ t in Set.Ioi 0, (cmode m F t) ^ 2) := by
  have hnn : ∀ m : ℕ, 0 ≤ ∫ t in Set.Ioi 0, (cmode m F t) ^ 2 :=
    fun m => integral_nonneg (fun t => sq_nonneg _)
  have hIF : (0 : ℝ) ≤ ∫ p in Q0, F p.1 p.2 ^ 2 := integral_nonneg (fun p => sq_nonneg _)
  have hg : Summable (fun m : ℕ => eNorm m * ∫ t in Set.Ioi 0, (cmode m F t) ^ 2) := by
    refine summable_of_sum_range_le (c := ∫ p in Q0, F p.1 p.2 ^ 2)
      (fun m => mul_nonneg (Work.EllipticEst.ModalSolution.eNorm_pos m).le (hnn m))
      (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]; simpa using hIF
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
      simpa using Work.FTS.H2.ModalSolR.coeffL2_sum_le hsm hL2 k
  exact Summable.of_nonneg_of_le hnn (fun m => le_mul_of_one_le_left (hnn m) (eNorm_ge_one m)) hg

/-- **The pointwise coefficient bound** for `m ≥ 1` (squared form). -/
lemma acoeff_sq_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {m : ℕ} (hm : 1 ≤ m) {z : ℝ} (hz : 0 < z) :
    (acoeff α m F z) ^ 2 ≤ (∫ t in Set.Ioi 0, (cmode m F t) ^ 2) * z ^ (-(1 : ℝ))
      / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hDnn : 0 ≤ ∫ t in Set.Ioi 0, (cmode m F t) ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have h := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm
    (Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m) hz
  have hden : 0 < α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) :=
    mul_pos (mul_pos hα (by linarith)) (Real.sqrt_pos.mpr hm0)
  set Y : ℝ := Real.sqrt (∫ t in Set.Ioi 0, (cmode m F t) ^ 2) * z ^ (-(1 / 2) : ℝ)
      / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) with hYdef
  have hY : 0 ≤ Y :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hz.le _)) hden.le
  have h1 : acoeff α m F z ≤ Y := (abs_le.mp h).2
  have h2 : -Y ≤ acoeff α m F z := (abs_le.mp h).1
  have hsq : (acoeff α m F z) ^ 2 ≤ Y ^ 2 := by
    have h3 : 0 ≤ Y + acoeff α m F z := by linarith
    have hprod : 0 ≤ (Y - acoeff α m F z) * (Y + acoeff α m F z) := mul_nonneg (by linarith) h3
    nlinarith [hprod]
  refine le_trans hsq (le_of_eq ?_)
  rw [hYdef, div_pow, mul_pow, mul_pow, Real.sq_sqrt hDnn, Real.sq_sqrt hm0.le,
    show (z ^ (-(1 / 2) : ℝ)) ^ 2 = z ^ (-(1 : ℝ)) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
      norm_num]
  ring

/-! ## The uniform tail estimate -/

/-- **The tail of the mode series is small, uniformly in `z` and `θ`.**  For `0 < c < d < π/2`
there are `K > 0` and a null sequence `b` with
`|ψ_N(z,θ) − ψ_M(z,θ)| ≤ K·z^{-1/2}·(b N + b M)` for every `z > 0` and `θ ∈ [c,d]`. -/
lemma psiTrunc_tail_uniform {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {c d : ℝ} (hcd : c < d) (hc0 : 0 < c) (hd : d < π / 2) :
    ∃ K : ℝ, 0 < K ∧ ∃ b : ℕ → ℝ, (∀ N, 0 ≤ b N) ∧ Tendsto b atTop (nhds 0) ∧
      ∀ (N M : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Icc c d →
        |psiTrunc α F N z θ - psiTrunc α F M z θ| ≤ K * z ^ (-(1 / 2) : ℝ) * (b N + b M) := by
  obtain ⟨K, hK0, hK⟩ := Work.EllipticEst.ModalSolution.psiTrunc_tail_bound (α := α) hcd hc0 hd
  set D : ℕ → ℝ := fun m => ∫ t in Set.Ioi 0, (cmode m F t) ^ 2 with hDdef
  have hDnn : ∀ m : ℕ, 0 ≤ D m := fun m => integral_nonneg (fun t => sq_nonneg _)
  have hDsum : Summable D := cmode_sq_summable hsm hL2
  set b : ℕ → ℝ := fun N => Real.sqrt ((∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m) with hbdef
  have hbnn : ∀ N : ℕ, 0 ≤ b N := fun N => Real.sqrt_nonneg _
  have hbsq : ∀ N : ℕ, (b N) ^ 2 = (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m := by
    intro N
    have h : 0 ≤ (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m :=
      sub_nonneg.mpr (hDsum.sum_le_tsum _ (fun i _ => hDnn i))
    rw [hbdef]
    exact Real.sq_sqrt h
  have hb : Tendsto b atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), D m) atTop (nhds (∑' m, D m)) :=
      hDsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N : ℕ => (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m) atTop
        (nhds ((∑' m, D m) - ∑' m, D m)) := tendsto_const_nhds.sub h1
    have h3 : Tendsto (fun N : ℕ => (∑' m, D m) - ∑ m ∈ Finset.range (N + 1), D m) atTop
        (nhds 0) := by simpa using h2
    have h4 := Real.continuous_sqrt.continuousAt.tendsto.comp h3
    simpa only [hbdef, Function.comp_def, Real.sqrt_zero] using h4
  have hkey : ∀ (N M : ℕ), M ≤ N → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Icc c d →
      |psiTrunc α F N z θ - psiTrunc α F M z θ| ≤ K * (2 / α) * z ^ (-(1 / 2) : ℝ) * b M := by
    intro N M hMN z θ hz hθ
    have h1 := hK z θ M N hθ hMN
    have hsum_eq : (∑ m ∈ Finset.Icc (M + 1) N,
            (∫ θ' in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
              * (acoeff α m F z) ^ 2)
        + (∑ m ∈ Finset.Icc (M + 1) N, (lam m
            * (∫ θ' in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ'))
              * (acoeff α m F z) ^ 2)
        = ∑ m ∈ Finset.Icc (M + 1) N, (1 + lam m)
            * (∫ θ' in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
            * (acoeff α m F z) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsum_eq] at h1
    have hterm : ∀ m ∈ Finset.Icc (M + 1) N,
        (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
          ≤ (4 / α ^ 2) * z ^ (-(1 : ℝ)) * D m := by
      intro m hm
      have hm1 : 1 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
      have hcoef := acoeff_sq_le hα hα1 hsm hL2 hm1 hz
      have hratio := arith_ratio hm1
      have hfac : 0 ≤ (1 + lam m) * eNorm m := by
        refine mul_nonneg ?_ (Work.EllipticEst.ModalSolution.eNorm_pos m).le
        have : (0 : ℝ) ≤ lam m := by rw [lam_eq]; positivity
        linarith
      have hquot : 0 ≤ D m * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) :=
        div_nonneg (mul_nonneg (hDnn m) (Real.rpow_nonneg hz.le _)) (by positivity)
      calc (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
          ≤ (1 + lam m) * eNorm m
              * (D m * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hcoef hfac
        _ ≤ (4 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))
              * (D m * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) :=
            mul_le_mul_of_nonneg_right hratio hquot
        _ = (4 / α ^ 2) * z ^ (-(1 : ℝ)) * D m := by
            field_simp
    have hPQ : ∑ m ∈ Finset.Icc (M + 1) N,
          (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
        ≤ (4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2 := by
      calc ∑ m ∈ Finset.Icc (M + 1) N, (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2
          ≤ ∑ m ∈ Finset.Icc (M + 1) N, (4 / α ^ 2) * z ^ (-(1 : ℝ)) * D m :=
            Finset.sum_le_sum hterm
        _ = (4 / α ^ 2) * z ^ (-(1 : ℝ)) * ∑ m ∈ Finset.Icc (M + 1) N, D m := by
            rw [Finset.mul_sum]
        _ ≤ (4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hbsq M]
            have hIccIco : (Finset.Icc (M + 1) N : Finset ℕ) = Finset.Ico (M + 1) (N + 1) := by
              ext k
              simp only [Finset.mem_Icc, Finset.mem_Ico]
              omega
            rw [hIccIco, Finset.sum_Ico_eq_sub _ (by omega : M + 1 ≤ N + 1)]
            exact sub_le_sub_right (hDsum.sum_le_tsum _ (fun i _ => hDnn i)) _
    have hsqrt : Real.sqrt ((4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2)
        = (2 / α) * z ^ (-(1 / 2) : ℝ) * b M := by
      rw [show (4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2
            = (4 / α ^ 2) * (z ^ (-(1 : ℝ)) * (b M) ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_mul (Real.rpow_nonneg hz.le _)]
      have h1 : Real.sqrt (4 / α ^ 2) = 2 / α := by
        rw [show (4 / α ^ 2 : ℝ) = (2 / α) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      have h2 : Real.sqrt (z ^ (-(1 : ℝ))) = z ^ (-(1 / 2) : ℝ) := by
        rw [show (z ^ (-(1 : ℝ))) = (z ^ (-(1 / 2) : ℝ)) ^ 2 by
              rw [sq, ← Real.rpow_add hz]; norm_num,
          Real.sqrt_sq (Real.rpow_nonneg hz.le _)]
      have h3 : Real.sqrt ((b M) ^ 2) = b M := Real.sqrt_sq (hbnn M)
      rw [h1, h2, h3]
      ring
    calc |psiTrunc α F N z θ - psiTrunc α F M z θ|
        ≤ K * Real.sqrt (∑ m ∈ Finset.Icc (M + 1) N,
              (1 + lam m) * eNorm m * (acoeff α m F z) ^ 2) := h1
      _ ≤ K * Real.sqrt ((4 / α ^ 2) * z ^ (-(1 : ℝ)) * (b M) ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hPQ) hK0.le
      _ = K * (2 / α) * z ^ (-(1 / 2) : ℝ) * b M := by rw [hsqrt]; ring
  refine ⟨K * (2 / α), mul_pos hK0 (by positivity), b, hbnn, hb, fun N M z θ hz hθ => ?_⟩
  rcases le_total M N with hMN | hNM
  · refine le_trans (hkey N M hMN z θ hz hθ) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hbnn N]
  · rw [abs_sub_comm]
    refine le_trans (hkey M N hNM z θ hz hθ) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hbnn M]

end Work.FTS.PhiStar.Honesty.NodeAux
