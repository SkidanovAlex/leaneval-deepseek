import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Helpers
import Submission.Work.CPhi.phiC_analytic
import Submission.Work.CRed.threeLogs_pos
import Submission.Work.CAsm.exists_int_relation
import Submission.Work.CAsm.log_bound

/-! Guidance from the project lead (the requester):

# Area CAsm — assembly of Theorem C (`CPos` from the contracts)
Given m,n ≥ 1, m ≠ n, 10⁶|m−n| ≤ n. Suppose a ℚ-relation p + q·lm + r·ln + s·lm·ln = 0 (component
form via `Submission.Helpers.linearIndependent_cons4_iff`). lm = 2η_a with a = 2m+1
(`Submission.CDT.beukersEta_one_add_two_mul` in LogHadamard). Clear denominators to integers.
- s = 0: independence of 1, lm, ln.
- s ≠ 0: r_ab := 4s ≠ 0 (after scaling), CRel holds.
-/

namespace Work.CAsm

open Submission.CDTPlan Metric

/-- `phiC = hauptH ∘ psiC` is continuous on the closed unit disc: `psiC` maps the closed disc into
`closedBall 0 (3/4)`, on which `hauptH` (holomorphic on the unit disc) is continuous. -/
private lemma phiC_continuousOn_closedBall (hM : HauptFacts) (hP : PsiCFacts) :
    ContinuousOn phiC (closedBall (0 : ℂ) 1) := by
  have hHcont : ContinuousOn hauptH (closedBall (0 : ℂ) (3 / 4)) := by
    refine (hM.1.mono ?_).continuousOn
    intro z hz
    rw [mem_ball, dist_zero_right]
    rw [mem_closedBall, dist_zero_right] at hz
    linarith
  have hmaps : Set.MapsTo psiC (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) (3 / 4)) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    exact hP.2.2.2.2.1 z (by simpa [mem_closedBall, dist_zero_right] using hz)
  have hcomp := hHcont.comp hP.1 hmaps
  have hfun : phiC = fun x => hauptH (psiC x) := rfl
  rw [hfun]
  exact hcomp

/-- `φ_C = h ∘ ψ_C` is an admissible map for the holonomy bound, with `|φ_C'(0)| = 82368/629`. -/
private lemma phiC_admissible_aux (hM : HauptFacts) (hP : PsiCFacts) :
    AdmissibleMap phiC ∧ ‖deriv phiC 0‖ = (82368 : ℝ) / 629 := by
  obtain ⟨hφdiff, hφ0, hφderiv, _h1, _h2, _h3⟩ := Work.CPhi.phiC_analytic hM hP
  refine ⟨⟨phiC_continuousOn_closedBall hM hP, hφdiff, hφ0, ?_⟩, ?_⟩
  · intro z hz
    have hmem : psiC z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right]
      have h := hP.2.2.2.2.1 z (by simpa [mem_closedBall, dist_zero_right] using le_of_eq hz)
      linarith
    have hne : psiC z ≠ 0 := by
      intro h
      have hz0 : z = 0 :=
        hP.2.2.2.2.2 z (by simpa [mem_closedBall, dist_zero_right] using le_of_eq hz) h
      rw [hz0] at hz
      norm_num at hz
    intro h0
    exact hne (hM.2.2.1 (psiC z) hmem (by simpa [phiC] using h0))
  · have hnorm : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ)‖ = x := by
      intro x hx
      have hsq : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      nlinarith [norm_nonneg (x : ℂ), hsq, hx]
    have hcast : (-256 : ℂ) * -(1287 / 2516) = (((82368 : ℝ) / 629 : ℝ) : ℂ) := by
      push_cast
      norm_num
    rw [hφderiv, hcast, hnorm _ (by norm_num)]

theorem c_pos (hH : HolonomyBoundL2) (h17 : Seventeen) (hD : CDenoms) (hC : CDClosed)
    (hPB : CPullbacks) (hN : CNumerics) (hT : TauValues) (hP : PsiCFacts) (hM : HauptFacts) :
    CPos := by
  intro m n hm hn hmn hgap
  rw [Submission.Helpers.linearIndependent_cons4_iff]
  intro p q r s hrel
  have hrelR : (p : ℝ) + (q : ℝ) * Real.log (1 + 1 / (m : ℝ))
      + (r : ℝ) * Real.log (1 + 1 / (n : ℝ))
      + (s : ℝ) * (Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ))) = 0 := by
    simpa [Algebra.smul_def] using hrel
  by_cases hs : s = 0
  · -- the relation only involves `1, lm, ln`
    have h3 := Work.CRed.threeLogs_pos m n hm hn hmn
    rw [Submission.Helpers.linearIndependent_cons3_iff] at h3
    have h0 : (p : ℝ) + (q : ℝ) * Real.log (1 + 1 / (m : ℝ))
        + (r : ℝ) * Real.log (1 + 1 / (n : ℝ)) = 0 := by
      rw [hs] at hrelR
      simpa using hrelR
    obtain ⟨hp, hq, hr⟩ := h3 p q r (by simpa [Algebra.smul_def] using h0)
    exact ⟨hp, hq, hr, hs⟩
  · exfalso
    -- clear denominators to integers
    obtain ⟨A, B, C, E, hE, hIntRel⟩ :=
      Work.CAsm.exists_int_relation p q r s hs hrelR
    -- the `η`-bridge
    have hηm : Submission.CDT.beukersEta (2 * (m : ℝ) + 1)
        = (1 / 2) * Real.log (1 + 1 / (m : ℝ)) := by
      have hm0 : (m : ℤ) ≠ 0 := by omega
      have h := Submission.CDT.beukersEta_one_add_two_mul (m : ℤ) hm0
      simpa [add_comm] using h
    have hηn : Submission.CDT.beukersEta (2 * (n : ℝ) + 1)
        = (1 / 2) * Real.log (1 + 1 / (n : ℝ)) := by
      have hn0 : (n : ℤ) ≠ 0 := by omega
      have h := Submission.CDT.beukersEta_one_add_two_mul (n : ℤ) hn0
      simpa [add_comm] using h
    have hCRel : CRel m n (2 * B) (2 * C) (4 * E) (-A) := by
      unfold CRel
      rw [hηm, hηn]
      push_cast
      ring_nf at hIntRel ⊢
      linarith [hIntRel]
    have hCAdm : CAdm m n := ⟨hm, hn, hmn, hgap⟩
    have hrab : (4 * E : ℤ) ≠ 0 := by omega
    -- the 17-function data
    have hPoly : PolyIndependent (seventeen m n (2 * B) (2 * C) (4 * E) (-A)) :=
      h17 m n (2 * B) (2 * C) (4 * E) (-A) hCAdm hCRel hrab
    have hDen : ∀ i, HasDenomType (eC i) (bC i) (seventeen m n (2 * B) (2 * C) (4 * E) (-A) i) :=
      fun i => hD m n (2 * B) (2 * C) (4 * E) (-A) i
    have hDcl : DClosed (seventeen m n (2 * B) (2 * C) (4 * E) (-A)) :=
      hC m n (2 * B) (2 * C) (4 * E) (-A) hCAdm
    have hPull : ∀ i, PullbackMero (seventeen m n (2 * B) (2 * C) (4 * E) (-A) i) phiC :=
      fun i => hPB m n (2 * B) (2 * C) (4 * E) (-A) hCAdm hCRel i
    -- analytic facts on `phiC`
    obtain ⟨hAdm, hderiv⟩ := phiC_admissible_aux hM hP
    have hCol : ColumnShape bC := by
      intro j
      fin_cases j
      · exact ⟨1, 2, by intro i; fin_cases i <;> simp [bC]⟩
      · exact ⟨3, 2, by intro i; fin_cases i <;> simp [bC]⟩
    -- numeric input
    have hlogb : (3 / 5 : ℝ) + 1032659 / 242760 < Real.log ((82368 : ℝ) / 629) :=
      Work.CAsm.log_bound
    have htau : tauFlat bC + tauSharpAt eC (7 / 4) < Real.log ‖deriv phiC 0‖ := by
      rw [hT.1, hderiv]
      linarith [hlogb]
    -- the holonomy bound
    have hbound := hH 17 2 0 bC eC (seventeen m n (2 * B) (2 * C) (4 * E) (-A))
        (fun _ : Fin (0 + 1) => phiC) ![0, (17 : ℝ)] (7 / 4)
        (by norm_num) (by norm_num) hCol hDen hPoly hDcl
        (fun k => by fin_cases k; exact hAdm)
        (fun i k => by fin_cases k; exact hPull i)
        (fun k => by fin_cases k; rw [hderiv]; norm_num)
        (fun a b hab => by fin_cases a; fin_cases b; exact absurd hab (by omega))
        (by simp) (by simp)
        (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all <;> norm_num)
        (by norm_num) (by norm_num) htau
    rw [Fin.sum_univ_zero, mul_zero, add_zero] at hbound
    have hw : (fun k : Fin (0 + 1) =>
        ((![0, (17 : ℝ)] : Fin (0 + 2) → ℝ) k.succ
          - (![0, (17 : ℝ)] : Fin (0 + 2) → ℝ) k.castSucc) / ((17 : ℕ) : ℝ))
        = fun _ : Fin 1 => (1 : ℝ) := by
      funext k
      fin_cases k
      norm_num
    have hfinal : (17 : ℝ) *
        (Real.log ‖deriv phiC 0‖ - (tauFlat bC + tauSharpAt eC (7 / 4))) ≤ (102 : ℝ) / 10 := by
      refine le_trans hbound ?_
      rw [hw]
      exact hN.1
    have hlog2 : tauFlat bC + tauSharpAt eC (7 / 4) + 3 / 5 < Real.log ‖deriv phiC 0‖ := by
      rw [hT.1, hderiv]
      linarith [hlogb]
    have hgt : (102 : ℝ) / 10 < (17 : ℝ) *
        (Real.log ‖deriv phiC 0‖ - (tauFlat bC + tauSharpAt eC (7 / 4))) := by
      linarith [hlog2]
    linarith [hfinal, hgt]

end Work.CAsm
