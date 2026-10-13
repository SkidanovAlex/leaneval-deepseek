/-
# `Work.FTS.PhiStar.FlatWAux.Fam1Bound` — the `∂_z`-family of the flat estimate

Clause 1 of `FlatW 7 f` for `f z θ = (z+1)/z · (psiSeries α (RemSource α ψ) z θ / sin 2θ)`:
the estimate `|(z+1)^k ∂_z^k f z θ| ≤ C α²` for `k ≤ 7`, with `C` independent of `α` and `ψ`.

**Route.**  `Fam1Id` turns the left-hand side into
`α²·(Σ_{j<J} α^j·Rl_j(z)·Wt ψ (j+1) θ + α^J·Σ'_m b_m λ_m^{-J}·Rm_m(z)·Q_m θ)`, where
`Rl_j(z) = (z+1)^k∂^k((z+1)/z·𝒜^jφ)` and `Rm_m(z) = (z+1)^k∂^k((z+1)/z·radGreen α m (𝒜^Jφ))`.
The finite sum is bounded with `PhiAjDivFlat` (`|Rl_j| ≤ CAF`) and `AngBoundU` (`|Wt ψ (j+1)| ≤ Kw`),
the remainder termwise with `RadGreenPhiAjFlat` (`|Rm_m| ≤ CRG/λ_m`), `CmodeDecay`
(`|b_m| ≤ Cd/(λ_m√(2m+1))`) and `QmDerivBound` (`|Q_m| ≤ CQ₀(2m+1)²`), and the resulting series is
summed with `ModeMajorant`.  All constants are `α`-free, so the final `C` is too.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Fam1Id
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat
import Submission.Work.FTS.PhiStar.FlatWAux.AngBoundU
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.FlatWAux.PhiAjDivFlat
import Submission.Work.FTS.PhiStar.FlatWAux.ModeMajorant
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenExpansionPhiAj
import Submission.Work.FTS.PhiStar.FlatWAux.ModeExpansion
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.FlatWAux.eFamSupBound
import Submission.Work.FTS.PhiStar.Series.RemSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Fam1Bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    ∀ k : ℕ, k ≤ 7 →
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * (Work.FTS.PhiStar.Series.psiSeries α
            (Work.FTS.PhiStar.RemSource α ψ) z' θ' / Work.Construction.s2 θ')) z θ|
        ≤ C * α ^ 2 := by
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS.PhiStar.Series.CmodeDecay
  obtain ⟨Cgr, hCgr0, hCgr⟩ := eFamSupBound
  obtain ⟨CQf, hCQf0, hCQf⟩ := QmDerivBound
  obtain ⟨CRG, hCRG0, hRG⟩ := RadGreenPhiAjFlat
  obtain ⟨Kmaj, hKmaj0, hmaj⟩ := ModeMajorant
  obtain ⟨CAF, hCAF0, hAF⟩ := PhiAjDivFlat
  obtain ⟨Kw, KcU, hKw0, hKcU0, hAB⟩ := AngBoundU
  have hlamnn : ∀ m : ℕ, (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := fun m => by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hlam : Work.FTS.PhiStar.Gegenbauer.lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := rfl
    rw [hlam]
    nlinarith [hm]
  have hKsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J, Kw (j + 1) :=
    Finset.sum_nonneg fun j _ => hKw0 (j + 1)
  refine ⟨8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
      + Kmaj * Cd * CRG * (CQf 0) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) :=
      mul_nonneg (by positivity) hKsum0
    have h2 : (0 : ℝ) ≤ Kmaj * Cd * CRG * (CQf 0) :=
      mul_nonneg (mul_nonneg (mul_nonneg hKmaj0 (le_of_lt hCd0)) (le_of_lt hCRG0)) (hCQf0 0)
    linarith
  · intro α ψ hα hα5 hang z θ hz hθ0 hθ2 k hk
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ2⟩
    have hWt : ∀ j : ℕ, j ≤ J → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
        |Wt ψ j θ'| ≤ Kw j := (hAB α ψ hα hα5 hang).1
    have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := bmode_zero_of_moment hang.moment
    have hdecf : ∀ m : ℕ, 1 ≤ m →
        |Work.FTS.PhiStar.Series.bmode m ψ|
          ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      fun m hm => by
        rw [Work.FTS.PhiStar.Series.bmode_eq_cmode m ψ 0]
        exact hCd α ψ hα hα5 hang m hm
    have hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
        |Work.FTS.PhiStar.Series.bmode m ψ|
          ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      ⟨Cd, hCd0, hdecf⟩
    have hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1) :=
      ⟨Cgr, hCgr0, hCgr⟩
    have hrbf : ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
          ≤ CRG / Work.FTS.PhiStar.Gegenbauer.lam m :=
      fun m hm k' hk' z' hz' => hRG.1 α hα hα5 m hm k' hk' z' hz'
    have hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
          ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m :=
      ⟨CRG, hCRG0, hrbf⟩
    have hrbJf : ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) z'') z'|
          ≤ CRG / Work.FTS.PhiStar.Gegenbauer.lam m :=
      fun m hm k' hk' z' hz' => hRG.2 α hα hα5 m hm k' hk' z' hz'
    have hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k' : ℕ, k' ≤ 7 → ∀ z' : ℝ, 0 < z' →
        |(z' + 1) ^ k' * iteratedDeriv k' (fun z'' => (z'' + 1) / z''
            * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) z'') z'|
          ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m :=
      ⟨CRG, hCRG0, hrbJf⟩
    have hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
        Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
          = (∑ j ∈ Finset.range J, (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
                * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
            + (α ^ J / (Work.FTS.PhiStar.Radial.lamR m) ^ J)
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z' :=
      fun m hm z' hz' => RadGreenExpansionPhiAj α hα hα5 m hm z' hz'
    have hid := Fam1Id α ψ z θ hz hθ hb0 hdec hgr hrb hrbJ hexp k hk
    -- the finite (resummed) part
    have hF1 : |∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
          (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
            (Work.FTS.VocabO.phiA α) z'') z) * Wt ψ (j + 1) θ|
        ≤ CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjJ : j < J := Finset.mem_range.mp hj
      have hj9 : j + 1 ≤ 9 := by simp only [J] at hjJ; omega
      have hR := hAF α hα hα5 (j + 1) hj9 k hk z hz
      rw [← Work.FTS.PhiStar.FlatWAux.Ajit_phiA α j] at hR
      have hW := hWt (j + 1) (by simp only [J] at hjJ ⊢; omega) θ hθ
      have hp : α ^ j ≤ 1 := pow_le_one₀ (le_of_lt hα) (le_trans hα5 (by norm_num))
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) j)]
      calc α ^ j * |(z + 1) ^ k * iteratedDeriv k
              (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
                (Work.FTS.VocabO.phiA α) z'') z| * |Wt ψ (j + 1) θ|
          ≤ 1 * CAF * Kw (j + 1) := by
            refine mul_le_mul (mul_le_mul hp hR (abs_nonneg _) (by norm_num))
              hW (abs_nonneg _) (by positivity)
        _ = CAF * Kw (j + 1) := by ring
    -- the remainder series
    have hcmp : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
            * Work.FTS.PhiStar.FlatWAux.Qm m θ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2) := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        rw [hb0]
        have hl0 : Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 := by
          simp only [Work.FTS.PhiStar.Gegenbauer.lam]; norm_num
        simp only [abs_zero, zero_mul, hl0, Nat.cast_zero, add_zero, mul_one,
          Work.FTS.PhiStar.FlatWAux.J]
        norm_num
      · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
        have hlam : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
          simp only [Work.FTS.PhiStar.Gegenbauer.lam]; positivity
        have hs2 : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos_of_pos (by linarith)
        have hb := hdecf m hmpos
        have hR := hrbJf m hmpos k hk z hz
        have hQ := hCQf m hmpos 0 (by norm_num : (0 : ℕ) ≤ 8) θ hθ
        simp only [iteratedDeriv_zero] at hQ
        have hQ' : |Work.FTS.PhiStar.FlatWAux.Qm m θ|
            ≤ CQf 0 * (2 * (m : ℝ) + 1) ^ 2 := by
          simpa using hQ
        have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_pos hlam hs2
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt hlam)) J)]
        have s1 : |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J :=
          mul_le_mul_of_nonneg_right hb (by positivity)
        have s2 : |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
            ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m) :=
          mul_le_mul s1 hR (abs_nonneg _) (by positivity)
        exact mul_le_mul s2 hQ' (abs_nonneg _) (by positivity)
    have hcmpA : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ|
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
            * |Work.FTS.PhiStar.FlatWAux.Qm m θ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2) := by
      intro m
      have h := hcmp m
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)] at h
      exact h
    have hHsum : Summable (fun m : ℕ =>
        Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2)) :=
      (hmaj Cd CRG (CQf 0) (le_of_lt hCd0) (le_of_lt hCRG0) (hCQf0 0)).1
    have hHle : (∑' m : ℕ,
        Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2))
        ≤ Kmaj * Cd * CRG * (CQf 0) :=
      (hmaj Cd CRG (CQf 0) (le_of_lt hCd0) (le_of_lt hCRG0) (hCQf0 0)).2
    have hGsum : Summable (fun m : ℕ =>
        ‖Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
          * Work.FTS.PhiStar.FlatWAux.Qm m θ‖) := by
      refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hHsum
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)]
      exact hcmpA m
    have hGsumA : Summable (fun m : ℕ =>
        |Work.FTS.PhiStar.Series.bmode m ψ|
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
          * |Work.FTS.PhiStar.FlatWAux.Qm m θ|) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)) (abs_nonneg _)) (abs_nonneg _)) hcmpA hHsum
    have hF2 : |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
            * Work.FTS.PhiStar.FlatWAux.Qm m θ|
        ≤ Kmaj * Cd * CRG * (CQf 0) := by
      calc |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ|
          ≤ ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ| := by
            simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hGsum
        _ = ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ|
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * |(z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z|
              * |Work.FTS.PhiStar.FlatWAux.Qm m θ| := by
            refine tsum_congr fun m => ?_
            rw [abs_mul, abs_mul, abs_mul,
              abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hlamnn m)) J)]
        _ ≤ ∑' m : ℕ, Cd / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
              * ((CQf 0) * (2 * (m : ℝ) + 1) ^ 2) :=
            Summable.tsum_le_tsum hcmpA hGsumA hHsum
        _ ≤ Kmaj * Cd * CRG * (CQf 0) := hHle
    -- assemble
    rw [hid, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) 2)]
    have hab : |(∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
            (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
              (Work.FTS.VocabO.phiA α) z'') z) * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ)|
        ≤ CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) + Kmaj * Cd * CRG * (CQf 0) := by
      refine le_trans (abs_add_le _ _) ?_
      have h2 : |α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.Radial.radGreen α m
                      (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
              * Work.FTS.PhiStar.FlatWAux.Qm m θ)|
          ≤ Kmaj * Cd * CRG * (CQf 0) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hα) J)]
        calc α ^ J * |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Qm m θ|
            ≤ 1 * |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Qm m θ| :=
              mul_le_mul_of_nonneg_right
                (pow_le_one₀ (le_of_lt hα) (le_trans hα5 (by norm_num))) (abs_nonneg _)
          _ = _ := one_mul _
          _ ≤ Kmaj * Cd * CRG * (CQf 0) := hF2
      linarith [hF1, h2]
    have hC1 : CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
        ≤ 8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) := by
      have h0 : (0 : ℝ) ≤ CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) :=
        mul_nonneg (le_of_lt hCAF0) hKsum0
      nlinarith [h0]
    calc α ^ 2 * |(∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k
              (fun z'' => (z'' + 1) / z'' * Work.FTS.PhiStar.FlatWAux.Ajit α j
                (Work.FTS.VocabO.phiA α) z'') z) * Wt ψ (j + 1) θ)
            + α ^ J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
                * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                    * Work.FTS.PhiStar.Radial.radGreen α m
                        (Work.FTS.PhiStar.FlatWAux.Ajit α J (Work.FTS.VocabO.phiA α)) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Qm m θ)|
        ≤ α ^ 2 * (CAF * (∑ j ∈ Finset.range J, Kw (j + 1)) + Kmaj * Cd * CRG * (CQf 0)) :=
          mul_le_mul_of_nonneg_left hab (pow_nonneg (le_of_lt hα) 2)
      _ ≤ α ^ 2 * (8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
            + Kmaj * Cd * CRG * (CQf 0) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt hα) 2)
          linarith [hC1]
      _ = (8 * 2 ^ 8 * CAF * (∑ j ∈ Finset.range J, Kw (j + 1))
            + Kmaj * Cd * CRG * (CQf 0) + 1) * α ^ 2 := by ring

end Work.FTS.PhiStar.FlatWAux
