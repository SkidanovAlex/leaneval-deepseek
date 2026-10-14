import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Deleg.psiRadFacts
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.E4R3.N4C.T4Honest.T4EasyInt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Asm
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.FaDens
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.bmodeUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.Series.Weil.bmodeUniform`

The partial sums `Σ_{m ≤ N} bmode m ψ · eFam m θ` of the angular eigen-expansion of a model
function `ψ` (`Work.FTS.PhiStar.AngModel α ψ`) are

* **uniformly bounded** on `Iθ`, and
* **uniformly convergent** to `ψ` on `Iθ`,

for `0 < α ≤ 1/5`.

Both statements follow from the single term majorant

  `|bmode m ψ · eFam m θ| ≤ Cd · Cg · (m+1)^{-3/2}`   (`m ≥ 1`),

which combines the coefficient decay `|bmode m ψ| ≤ Cd (m+1)^{-5/2}` (`bmode_decay_pow`, from
`bmode_decay15`) with the uniform growth bound `|eFam m θ| ≤ Cg (m+1)` on `Iθ`
(`eFam_sup_le`).  The `m = 0` term vanishes because `AngModel.moment` forces `bmode 0 ψ = 0`.
The majorant is summable (`(m+1)^{-3/2}`), giving the uniform bound; and its tails tend to `0`,
giving uniform convergence once the pointwise identity `Σ'_m bmode m ψ · eFam m θ = ψ θ` on the
*open* interval (`sum_bmode_eFam_eq`) is used for the interior points.  At the endpoints
`θ = 0, π/2` every `eFam m` vanishes (`eFam_zero_right`, `eFam_zero_left`) and so does `ψ`
(`AngModel.bdry0`, `AngModel.bdry1`), so the difference is exactly `0` there.
-/

/-! ## The mode majorant `Cd · Cg · (m+1)^{-3/2}` -/

/-- The majorant of the mode terms `|bmode m ψ · eFam m θ|`, dictated by the coefficient decay
`|bmode m ψ| ≲ (m+1)^{-5/2}` and the uniform growth `|eFam m θ| ≲ (m+1)`. -/
private def maj (Cd Cg : ℝ) (m : ℕ) : ℝ := Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))

private lemma maj_nonneg {Cd Cg : ℝ} (hCd : 0 ≤ Cd) (hCg : 0 ≤ Cg) (m : ℕ) :
    0 ≤ maj Cd Cg m := by
  change 0 ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))
  exact mul_nonneg (mul_nonneg hCd hCg) (Real.rpow_nonneg (by positivity) _)

private lemma maj_summable (Cd Cg : ℝ) : Summable (maj Cd Cg) := by
  change Summable (fun m : ℕ => Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))
  exact (Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2) (by norm_num)).mul_left
    (Cd * Cg)

private lemma abs_bmode_mul_eFam_le_maj {α : ℝ} {ψ : ℝ → ℝ} {Cd Cg : ℝ}
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hsup : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * ((m : ℝ) + 1))
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ maj Cd Cg m := by
  change |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))
  exact Work.FTS.PhiStar.Series.abs_bmode_mul_eFam_le_aux α ψ hψ hCg hCd hsup hdec m hθ

/-! ## The tails of a summable majorant tend to zero -/

private lemma tail_tsum_tendsto_zero {G : ℕ → ℝ} (hG : Summable G) :
    Tendsto (fun k : ℕ => ∑' i : ℕ, G (i + k)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun k : ℕ => ∑ i ∈ Finset.range k, G i) atTop (𝓝 (∑' i : ℕ, G i)) :=
    hG.hasSum.tendsto_sum_nat
  have heq : (fun k : ℕ => ∑' i : ℕ, G (i + k))
      = fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i := by
    funext k
    have h := hG.sum_add_tsum_nat_add k
    linarith
  rw [heq]
  have h2 : Tendsto (fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i) atTop
      (𝓝 ((∑' i : ℕ, G i) - (∑' i : ℕ, G i))) :=
    tendsto_const_nhds.sub hsum
  simpa using h2

/-! ## The theorem -/

theorem bmodeUniform (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    (∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |(∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ| ≤ ε) := by
  obtain ⟨Cg, hCg, hsup⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  obtain ⟨Cd, hCd, hdec⟩ := Work.FTS.PhiStar.Series.bmode_decay_pow α ψ hα hα5 hψ
  have hsum : Summable (maj Cd Cg) := maj_summable Cd Cg
  have hnn : ∀ m : ℕ, 0 ≤ maj Cd Cg m := fun m => maj_nonneg (le_of_lt hCd) (le_of_lt hCg) m
  have hterm : ∀ (m : ℕ) {θ : ℝ}, θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ maj Cd Cg m :=
    fun m θ hθ => abs_bmode_mul_eFam_le_maj hψ hCd hCg hsup hdec m hθ
  refine ⟨?_, ?_⟩
  · refine ⟨(∑' m : ℕ, maj Cd Cg m) + 1, ?_, ?_⟩
    · have h0 : 0 ≤ ∑' m : ℕ, maj Cd Cg m := tsum_nonneg hnn
      linarith
    · intro N θ hθ
      have h1 : |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ ∑ m ∈ Finset.range (N + 1), maj Cd Cg m := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
        intro m _
        exact hterm m hθ
      have h2 : ∑ m ∈ Finset.range (N + 1), maj Cd Cg m ≤ ∑' m : ℕ, maj Cd Cg m :=
        hsum.sum_le_tsum (Finset.range (N + 1)) (fun m _ => hnn m)
      linarith
  · intro ε hε
    have htail := tail_tsum_tendsto_zero hsum
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail ε hε
    have hN' : ∀ k : ℕ, N ≤ k → |∑' i : ℕ, maj Cd Cg (i + k)| < ε := by
      intro k hk
      have hk2 := hN k hk
      simpa only [Real.dist_eq, sub_zero] using hk2
    refine ⟨N, fun n hn θ hθ => ?_⟩
    have hmem : θ ∈ Work.Spaces.Iθ := hθ
    have hθ' : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := by
      rw [Work.Spaces.Iθ] at hθ
      exact hθ
    rcases eq_or_lt_of_le hθ'.1 with h0 | h0
    · subst h0
      have hz : (∑ m ∈ Finset.range (n + 1),
          Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = 0 :=
        Finset.sum_eq_zero (fun m _ => by
          rw [Work.FTS.PhiStar.Series.eFam_zero_right m, mul_zero])
      rw [hz, hψ.bdry0, sub_zero, abs_zero]
      exact le_of_lt hε
    · rcases eq_or_lt_of_le hθ'.2 with h2 | h2
      · subst h2
        have hz : (∑ m ∈ Finset.range (n + 1),
            Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = 0 :=
          Finset.sum_eq_zero (fun m _ => by
            rw [Work.FTS.PhiStar.Series.eFam_zero_left m, mul_zero])
        rw [hz, hψ.bdry1, sub_zero, abs_zero]
        exact le_of_lt hε
      · have hpsi : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ :=
          Work.FTS.PhiStar.Series.sum_bmode_eFam_eq α ψ hα hψ ⟨Cg, hCg, hsup⟩
            ⟨Cd, hCd, hdec⟩ θ h0 h2
        have hsumθ : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
          Summable.of_norm_bounded hsum (fun m => by
            rw [Real.norm_eq_abs]
            exact hterm m hmem)
        have hsplit := hsumθ.sum_add_tsum_nat_add (n + 1)
        have hdiff : (∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ
            = -(∑' i : ℕ, Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ) := by
          rw [← hpsi]
          linarith
        rw [hdiff, abs_neg]
        have hshift : Summable (fun i : ℕ => maj Cd Cg (i + (n + 1))) :=
          hsum.comp_injective (fun a b hab => Nat.add_right_cancel hab)
        have hnorms : Summable (fun i : ℕ => ‖Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ‖) :=
          Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => by
            rw [Real.norm_eq_abs]
            exact hterm _ hmem) hshift
        calc |∑' i : ℕ, Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ|
            = ‖∑' i : ℕ, Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
                * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ∑' i : ℕ, ‖Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
                * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ‖ :=
              norm_tsum_le_tsum_norm hnorms
          _ ≤ ∑' i : ℕ, maj Cd Cg (i + (n + 1)) :=
              Summable.tsum_le_tsum (fun i => by
                rw [Real.norm_eq_abs]
                exact hterm _ hmem) hnorms hshift
          _ ≤ ε := by
              have hlt : |∑' i : ℕ, maj Cd Cg (i + (n + 1))| < ε := hN' (n + 1) (by omega)
              calc ∑' i : ℕ, maj Cd Cg (i + (n + 1))
                  ≤ |∑' i : ℕ, maj Cd Cg (i + (n + 1))| := le_abs_self _
                _ ≤ ε := le_of_lt hlt

end Work.FTS.PhiStar.Series.Weil
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.modeTermBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Weil

open scoped Real

/-! ## Elementary facts about `λ_m = 2m(2m+5)` -/

/-- `(m+1)^{5/2} ≤ λ_m·√(2m+1)` for `m ≥ 1`: indeed `λ_m ≥ (m+1)²` and
`√(2m+1) ≥ √(m+1)`. -/
private lemma lam_mul_sqrt_ge (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ (5 / 2 : ℝ)
      ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlam0 : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]; positivity
  have h1 : ((m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  have h2 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
    apply Real.sqrt_le_sqrt; linarith
  have h3 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) hlam0
  calc ((m : ℝ) + 1) ^ (5 / 2 : ℝ) = ((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1) := by
        rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hx, Real.sqrt_eq_rpow]
        norm_num
    _ ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := h3

/-- `1/(λ_m·√(2m+1)) ≤ (m+1)^{-5/2}` for `m ≥ 1`. -/
private lemma inv_lam_mul_sqrt_le (m : ℕ) (hm : 1 ≤ m) :
    1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hB : (0 : ℝ) < ((m : ℝ) + 1) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have h := one_div_le_one_div_of_le hB (lam_mul_sqrt_ge m hm)
  rw [one_div, one_div] at h
  rw [← Real.rpow_neg (le_of_lt hx)] at h
  rw [one_div]
  exact h

/-- `x^{-5/2}·(x^{-2}·x) = x^{-7/2}` — the exponent bookkeeping of the mode bound. -/
private lemma rpow_factor (x : ℝ) (hx : 0 < x) :
    x ^ (-(5 / 2 : ℝ)) * (x ^ (-(2 : ℝ)) * x) = x ^ (-(7 / 2 : ℝ)) := by
  have h2 : x ^ (-(5 / 2 : ℝ)) * x ^ (-(2 : ℝ)) = x ^ (-(9 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx]; norm_num
  have h3 : x ^ (-(9 / 2 : ℝ)) * x = x ^ (-(7 / 2 : ℝ)) := by
    have h : x ^ (-(9 / 2 : ℝ)) * x ^ (1 : ℝ) = x ^ (-(7 / 2 : ℝ)) := by
      rw [← Real.rpow_add hx]; norm_num
    simpa using h
  calc x ^ (-(5 / 2 : ℝ)) * (x ^ (-(2 : ℝ)) * x)
      = (x ^ (-(5 / 2 : ℝ)) * x ^ (-(2 : ℝ))) * x := by ring
    _ = x ^ (-(9 / 2 : ℝ)) * x := by rw [h2]
    _ = x ^ (-(7 / 2 : ℝ)) := h3

/-- **Decay of the mode terms of the remainder series.**  For `0 < α ≤ 1/5` and an angular
model `ψ`, the mode terms of `psiSeries α (RemSource α ψ)` decay at the rate
`(m+1)^{-7/2}`, uniformly in the angle and with the radial singularity `(1+1/z)`. -/
theorem modeTermBound (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
  obtain ⟨Cb, hCb, hbm⟩ := Work.FTS.PhiStar.Series.bmode_decay15
  obtain ⟨Cr, hCr, hr⟩ := Work.FTS.PhiStar.Series.radGreen_phiA_bound
  obtain ⟨Ce, hCe, he⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have hα1 : α ≤ 1 := by linarith
  refine ⟨Cb * Cr * Ce, by positivity, ?_⟩
  intro m hm z θ hz hθ
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs : (0 : ℝ) ≤ 1 + 1 / z := by positivity
  have hx5 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
  have hxi2 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ (-(2 : ℝ)) := Real.rpow_nonneg hx.le _
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα, hα5]
  -- the three factor bounds
  have hBd : |Work.FTS.PhiStar.Series.bmode m ψ|
      ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
    have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [Work.FTS.PhiStar.Series.bmode_eq_cmode m ψ 0]
      exact hbm α ψ hα hα5 hψ m hm
    calc |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := hb
      _ = Cb * (1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
          rw [div_eq_mul_one_div]
      _ ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (inv_lam_mul_sqrt_le m hm) hCb.le
  have hRg : |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
      ≤ Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) := (hr α hα hα1 m hm).1 z hz
  have hEf : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * ((m : ℝ) + 1) := he m θ hθ
  have hCbx5 : (0 : ℝ) ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := mul_nonneg hCb.le hx5
  have hCrs : (0 : ℝ) ≤ Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) :=
    mul_nonneg (mul_nonneg hCr.le hs) hxi2
  -- assemble
  have hsplit : |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      = α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
        * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
    rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
    rw [abs_mul ((α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
      * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)
      (Work.FTS.PhiStar.Gegenbauer.eFam m θ)]
    rw [abs_mul (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
      (Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)]
    rw [abs_mul (α ^ 2) (Work.FTS.PhiStar.Series.bmode m ψ)]
    rw [abs_of_nonneg (sq_nonneg α)]
  have step1 : α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
        * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ (1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
        * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)))
        * (Ce * ((m : ℝ) + 1)) := by
    have h1 : α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ 1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul hα2 hBd (abs_nonneg _) (by norm_num)
    have h2 : α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
          * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ (1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
          * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ))) :=
      mul_le_mul h1 hRg (abs_nonneg _) (by simpa using hCbx5)
    exact mul_le_mul h2 hEf (abs_nonneg _) (mul_nonneg (by simpa using hCbx5) hCrs)
  have heq : (1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
        * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)))
        * (Ce * ((m : ℝ) + 1))
      = Cb * Cr * Ce * (1 + 1 / z)
        * (((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
          * (((m : ℝ) + 1) ^ (-(2 : ℝ)) * ((m : ℝ) + 1))) := by ring
  rw [hsplit]
  refine le_trans step1 ?_
  rw [heq, rpow_factor ((m : ℝ) + 1) hx]

end Work.FTS.PhiStar.Series.Weil
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.T4Honest.T4Slot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.T4Honest

open Work.FTS.StrongPersist.N6Trans.T1Hon

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The per-slot `D_θ`-transport bound with a `D`-sup coefficient, honest class.** -/
theorem T4SlotBound : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.WDMem 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.DecayAll 4 g →
      ∀ (a b : ℕ), a + b ≤ 4 → ∀ (q : ℝ),
        (a = 0 → q = 0 ∨ q = Work.Spaces.eta) →
        (1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
        |Work.FTS.TransportS.slotPairing (t1W q) a b
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
          ≤ C * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by
  obtain ⟨CH, hCHpos, hCH⟩ := T4HardSlot
  obtain ⟨CE, hCEpos, hCE⟩ := T4EasyInt
  refine ⟨CH + CE, by linarith, ?_⟩
  intro α f g hα hα1 hf hwf hg hmg hdg a b hab q hq0 hqa
  obtain ⟨hEEint, hEEle⟩ := SlotWeightHkSq α g a b q hα hα1 hg hmg hab hq0 hqa
  obtain ⟨hELint, hELle⟩ := hCE α f g hα hα1 hf hwf hg hmg a b hab q hq0 hqa
  set W : ℝ := Work.FTS.VocabO.WDp 4 f with hWdef
  have hWnn : 0 ≤ W := by rw [hWdef]; exact Work.FTS.OpenPkg.WDp_nonneg 4 f
  set u : ℝ → ℝ → ℝ := fun z θ => f z θ * Work.Spaces.Dth g z θ with hu
  -- ### the `z`-integral of the hard bound
  have hHb_int : MeasureTheory.Integrable
      (fun z => CH * W * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      (volume.restrict Work.Spaces.Iz) :=
    hEEint.const_mul (CH * W)
  have hHb_le : (∫ z in Work.Spaces.Iz, CH * W
        * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      ≤ CH * W * Work.Spaces.HkSq α 4 g := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hEEle (mul_nonneg (le_of_lt hCHpos) hWnn)
  -- ### the `z`-integral of the easy bound
  have hEz_int : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)
      (volume.restrict Work.Spaces.Iz) := hELint.integral_prod_left
  have hELle' : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)
      ≤ CE * W * Work.Spaces.HkSq α 4 g := by
    have h := hELle
    rw [show Work.FTS.H2.pm
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) from rfl] at h
    rwa [← MeasureTheory.integral_integral hELint] at h
  -- ### the Leibniz identity
  have hId : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ
        = t1Hard q f g a b z θ + t1Easy q f g a b z θ := by
    intro z θ hz hθ
    rw [hu]
    have hlei := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f
      (fun z θ => Work.Spaces.Dth g z θ) hf (hg.Dth) z θ hz hθ.1 hθ.2
    have hsplit : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 a1 f z θ
               * Work.Spaces.mixed (b - b1) (a - a1) (Work.Spaces.Dth g) z θ))
        = (f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ)
          + (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
              (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
                ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                  * (Work.Spaces.mixed b1 a1 f z θ
                     * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))) := by
      rw [sum_split_zero a b (fun a1 b1 => ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ
           * Work.Spaces.mixed (b - b1) (a - a1) (Work.Spaces.Dth g) z θ))]
      congr 1
      · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
          Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero]
        rw [mixed_Dth, ← Dth_mixed_eq hg b a hz hθ]
      · refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 _ => ?_
        by_cases hh : a1 = 0 ∧ b1 = 0
        · rw [if_pos hh, if_pos hh]
        · rw [if_neg hh, if_neg hh]
          rw [mixed_Dth]
    rw [hlei, hsplit]
    simp only [t1Hard, t1Easy, t1Leib]
    ring
  -- ### the pointwise-in-`z` bound
  have hpt : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |∫ θ in Work.Spaces.Iθ, t1W q z θ * Work.Spaces.mixed b a u z θ
          * Work.Spaces.mixed b a g z θ|
        ≤ (CH * W * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ) := by
    filter_upwards [ae_Iz_pos, hELint.prod_right_ae] with z hzpos hEaz
    have hEz_nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ _ => t1EasyAbs_nonneg q f g a b z θ))
    have hHb_nn : 0 ≤ CH * W * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
      mul_nonneg (mul_nonneg (le_of_lt hCHpos) hWnn)
        (mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (sq_nonneg _)
              (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)))))
    have hTe_int : MeasureTheory.Integrable (fun θ => t1Easy q f g a b z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.Integrable.mono' hEaz
        (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => t1Easy q f g a b p.1 p.2)
          (continuousOn_t1Easy hf hg a b q) hzpos)
        (Filter.Eventually.of_forall fun θ => by
          rw [Real.norm_eq_abs]; exact abs_t1Easy_le q f g a b z θ)
    have hhard : |∫ θ in Work.Spaces.Iθ, t1Hard q f g a b z θ| ≤ CH * W
        * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
      have h := hCH α f g q hα hα1 hf hwf hg hmg hdg a b hab hq0 hqa z
        (Set.mem_Ici.mpr hzpos.le)
      simpa only [hWdef, t1Hard, t1W] using h
    have heasy : |∫ θ in Work.Spaces.Iθ, t1Easy q f g a b z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ :=
      le_trans MeasureTheory.abs_integral_le_integral_abs
        (MeasureTheory.integral_mono_ae hTe_int.abs hEaz
          (Filter.Eventually.of_forall fun θ => abs_t1Easy_le q f g a b z θ))
    have hcongr : (∫ θ in Work.Spaces.Iθ, t1W q z θ * Work.Spaces.mixed b a u z θ
          * Work.Spaces.mixed b a g z θ)
        = ∫ θ in Work.Spaces.Iθ, (t1Hard q f g a b z θ + t1Easy q f g a b z θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ae_Iθ_mem_Ioo] with θ hθ
      exact hId z θ hzpos hθ
    by_cases hAint : MeasureTheory.Integrable (fun θ => t1Hard q f g a b z θ)
        (volume.restrict Work.Spaces.Iθ)
    · rw [hcongr, MeasureTheory.integral_add hAint hTe_int]
      exact le_trans (abs_add_le _ _) (add_le_add hhard heasy)
    · have hnot : ¬ MeasureTheory.Integrable
          (fun θ => t1Hard q f g a b z θ + t1Easy q f g a b z θ)
          (volume.restrict Work.Spaces.Iθ) := fun hh =>
        hAint ((hh.sub hTe_int).congr (Filter.Eventually.of_forall fun θ => by
          simp only [Pi.sub_apply, Pi.add_apply]; ring))
      rw [hcongr, MeasureTheory.integral_undef hnot, abs_zero]
      exact add_nonneg hHb_nn hEz_nn
  -- ### assembly
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ|
      ≤ ∫ z in Work.Spaces.Iz, ((CH * W * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)) := by
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    have hrhs : MeasureTheory.Integrable
        (fun z => (CH * W * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ))
        (volume.restrict Work.Spaces.Iz) := hHb_int.add hEz_int
    by_cases hI : MeasureTheory.Integrable
        (fun z => |∫ θ in Work.Spaces.Iθ, t1W q z θ * Work.Spaces.mixed b a u z θ
          * Work.Spaces.mixed b a g z θ|) (volume.restrict Work.Spaces.Iz)
    · exact MeasureTheory.integral_mono_ae hI hrhs hpt
    · rw [MeasureTheory.integral_undef hI]
      refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => ?_)
      have h1 : 0 ≤ CH * W * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
        mul_nonneg (mul_nonneg (le_of_lt hCHpos) hWnn)
          (mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
              (fun θ hθ => mul_nonneg (sq_nonneg _)
                (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)))))
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ :=
        MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ _ => t1EasyAbs_nonneg q f g a b z θ))
      exact add_nonneg h1 h2
  have hslot : Work.FTS.TransportS.slotPairing (t1W q) a b u g
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ := rfl
  calc |Work.FTS.TransportS.slotPairing (t1W q) a b u g|
      = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          t1W q z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a g z θ| := by
        rw [hslot]
    _ ≤ ∫ z in Work.Spaces.Iz, ((CH * W * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ)) := hmain
    _ = (∫ z in Work.Spaces.Iz, CH * W * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t1EasyAbs q f g a b z θ) :=
        MeasureTheory.integral_add hHb_int hEz_int
    _ ≤ CH * W * Work.Spaces.HkSq α 4 g + CE * W * Work.Spaces.HkSq α 4 g :=
        add_le_add hHb_le hELle'
    _ = (CH + CE) * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by
        rw [hWdef]; ring

end Work.FTS.StrongEps.E4R3.N4C.T4Honest
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.sg_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)
open Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Row `N₁^{sg} = 2ℛ(Φ̃_*)·f` -/

theorem row1sg_open {α Cs : ℝ} {f Φs : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Fa (Work.FTS.Nonlin.N1sg α Φs f)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α f) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.continuousOn
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := Work.FTS.NonlinRows.Rl1.star_Rop_le hα hs r hr θ hθ
    calc |Work.Spaces.K θ
          * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
        = 2 * |Work.Spaces.K θ|
            * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
      _ ≤ 2 * 3 * (max Cs 0 * α) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2
            (abs_nonneg _) (by positivity)
      _ = 6 * max Cs 0 * α := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable (fun θ => ENNReal.ofReal ((f r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_g hα hr hθ f)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α)
    (A := fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := f) (g := f) (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs f r θ|
      = |Work.Spaces.K θ
          * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) * f r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N1sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Row `N₂^{sg} = -2𝒰(Φ̃_*)·∂_θf` -/

/-- Row 2 with the pointwise bound on `𝒰(Φ̃_*)` exposed. -/
theorem row2sg_open {α MU : ℝ} {f Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hMU : 0 ≤ MU)
    (hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ MU)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Fa (Work.FTS.Nonlin.N2sg α Φs f)
      ≤ ENNReal.ofReal (3 * MU * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) := by
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dth f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.Dth.continuousOn
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            / Real.sin (2 * θ)) r θ| ≤ 3 * MU := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos hθ)
    have hU0 := hU r θ hr hθI
    have hK : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
      rw [Work.Spaces.K, Real.sin_two_mul]
      ring
    have hratio : Work.Spaces.K θ / Real.sin (2 * θ) = (3 / 2) * Real.cos θ := by
      rw [hK]
      field_simp
    have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have habs : |Work.Spaces.K θ
          * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ))|
        = 2 * ((3 / 2) * |Real.cos θ|)
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
      have hsplit : Work.Spaces.K θ
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
                / Real.sin (2 * θ))
          = (Work.Spaces.K θ / Real.sin (2 * θ))
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) := by ring
      rw [hsplit, hratio]
      rw [show (3 / 2 : ℝ) * Real.cos θ
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
          = (-3) * (Real.cos θ
            * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) from by ring,
        abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_mul]
      ring
    rw [habs]
    have h1 : (3 / 2) * |Real.cos θ| ≤ (3 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hcos (by norm_num)
    calc 2 * ((3 / 2) * |Real.cos θ|)
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 2 * ((3 / 2) * 1) * MU := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hU0
            (abs_nonneg _) ?_
          positivity
      _ = 3 * MU := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dth f r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dth f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dth hα hr hθ f)
  have hE := rl1_slot_le (α := α) (C := 3 * MU)
    (A := fun z θ => -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Real.sin (2 * θ))
    (B := Work.Spaces.Dth f) (g := f) (mul_nonneg (by norm_num) hMU)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs f r θ|
        = |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ)) * Work.Spaces.Dth f r θ| := by
    intro r θ hθ
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos hθ)
    rw [Work.FTS.Nonlin.N2sg]
    congr 1
    simp only [Work.Spaces.Dth]
    field_simp
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [ae_Iθ_of_forall_Ioo
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun θ hθ => hθ)] with θ hθ
  rw [hid r θ hθ]

/-! ## Row `N₃^{sg} = -2α𝒱(Φ̃_*)·D_zf` -/

theorem row3sg_open {α Cs : ℝ} {f Φs : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Fa (Work.FTS.Nonlin.N3sg α Φs f)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α ^ 2 * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α f) := by
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.Dz.continuousOn
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α ^ 2 := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := Work.FTS.NonlinRows.Rl1.star_Vop_le hα hs r hr θ hθ
    calc |Work.Spaces.K θ
          * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
        = 2 * α * |Work.Spaces.K θ|
            * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
          rw [show Work.Spaces.K θ
                * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
              = (-(2 * α)) * (Work.Spaces.K θ
                * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ) from by ring,
            abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hα.le), abs_mul]
          ring
      _ ≤ 2 * α * 3 * (max Cs 0 * α) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1
            (mul_nonneg (by norm_num) hα.le)) hb2 (abs_nonneg _) (by positivity)
      _ = 6 * max Cs 0 * α ^ 2 := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz f r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dz f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dz hα hr hθ f)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α ^ 2)
    (A := fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := Work.Spaces.Dz f) (g := f)
    (mul_nonneg (mul_nonneg (by norm_num) hCs0) (sq_nonneg α))
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs f r θ|
      = |Work.Spaces.K θ
          * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
          * Work.Spaces.Dz f r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N3sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Elementary arithmetic -/

/-- `√(π/2) ≤ 2`. -/
theorem sqrt_pi_div_two_le_two : Real.sqrt (Real.pi / 2) ≤ 2 := by
  have h : Real.sqrt (Real.pi / 2) ≤ Real.sqrt 4 :=
    Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
  rwa [show Real.sqrt (4 : ℝ) = 2 from by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

/-- `1 ≤ α^{-2}` for `0 < α ≤ 1`. -/
theorem one_le_rpow_neg_two {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg hα.le]
  rw [one_le_inv₀ (Real.rpow_pos_of_pos hα 2)]
  exact Real.rpow_le_one hα.le hα1 (by norm_num)


/-! ## Assembly -/


end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
end
