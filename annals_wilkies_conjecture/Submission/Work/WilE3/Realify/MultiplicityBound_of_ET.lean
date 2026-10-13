import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Sep
import Submission.Work.WilE3.Realify.MultiplicityBound_proved
import Submission.Work.WilE3.Realify.ET.EvalIdent
import Submission.Work.WilE3.Realify.ET.SumDeg

namespace Work.WilE3.Realify

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

variable {k r : ℕ}

/-- E3's realified chain `mkChain c cc` is of exp/tan type: for every chain function `j` either
`φ_j = Real.exp` with `R_j = X 0`, or `φ_j = Real.tan` with `R_j = 1 + X 0 ^ 2`.  This discharges
the chain-type hypothesis `SepKhovanskiiET` carries (and `SepKhovanskiiLocal` did not). -/
theorem mkChain_isET (c : EAChain k r) (cc : Fin r → ℝ) :
    ∀ j, ((mkChain c cc).phi j = Real.exp ∧
          (mkChain c cc).R j = MvPolynomial.X 0) ∨
         ((mkChain c cc).phi j = Real.tan ∧
          (mkChain c cc).R j = 1 + MvPolynomial.X 0 ^ 2) := by
  intro j
  refine Fin.addCases (motive := fun j =>
      ((mkChain c cc).phi j = Real.exp ∧
        (mkChain c cc).R j = MvPolynomial.X 0) ∨
      ((mkChain c cc).phi j = Real.tan ∧
        (mkChain c cc).R j = 1 + MvPolynomial.X 0 ^ 2)) ?_ ?_ j
  · intro i
    left
    exact ⟨by simp only [mkChain, chainPhi, Fin.addCases_left],
      by simp only [mkChain, chainR, Fin.addCases_left]⟩
  · intro i
    right
    exact ⟨by simp only [mkChain, chainPhi, Fin.addCases_right],
      by simp only [mkChain, chainR, Fin.addCases_right]⟩

/-- **Node K4 of the lead's E3/E9 design** (`sources/wilkiesE3E9/wilkies_E3E9_gaps.md`, GAP 1):
Gabrielov's multiplicity bound for complexified EA systems, from the corrected separable-chain
Khovanskii bound `Work.WilE3.SepKhovanskiiET` (a convex domain forces each `tan` chain function
onto one branch; the eventual home of that statement is `Work.WilE3K.SepKhovanskiiET`, proved
there from the frozen `E2_khovanskii`).

This is `MultiplicityBound_proved` with the hypothesis retyped to `SepKhovanskiiET`: the ball is
convex (`convex_ball`, in place of the now-absent `Metric.isBounded_ball`) and the extra
chain-type hypothesis is discharged by `mkChain_isET`. -/
theorem MultiplicityBound_of_ET (hK : ∀ F : ℕ, Work.WilE3.SepKhovanskiiET F) :
    Work.WilE3.MultiplicityBound := by
  intro F
  obtain ⟨p, hp⟩ := hK (2 * F)
  refine ⟨p.comp (Polynomial.C (6 * F * (F + 1) + 1) * Polynomial.X
      + Polynomial.C (12 * F * F + 5 * F + 1)), ?_⟩
  intro k r c f g x ρ hkr hfx hρpos hρtend
  set N₀ : ℕ := ∑ i, atomDeg (f i) + ∑ i, atomDeg (g i) with hN₀
  set N : ℕ := N₀ + 1 with hN
  -- the chart choice
  have hchart : ∀ j : Fin r, ∃ (cc e : ℝ), (∃ n : ℤ, cc = n * Real.pi) ∧ e = Real.cos cc ∧
      |(∑ i, c.a j i * (x i).im) - cc| ≤ Real.pi / 2 ∧
      (∀ w : ℝ, |w - (∑ i, c.a j i * (x i).im)| < Real.pi / 2 →
        Real.cos ((w - cc) / 2) ≠ 0) ∧
      ((e : ℂ) = Complex.exp ((cc : ℂ) * Complex.I)) :=
    fun j => exists_chart_offset _
  choose cc e hcc hee hβ hccdom hec using hchart
  set A : ℝ := ∑ j : Fin r, ∑ i : Fin k, |c.a j i| with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hρsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ρ ε < Real.pi / (8 * (A + 1)) := by
    have hc : 0 < Real.pi / (8 * (A + 1)) := by positivity
    filter_upwards [hρtend.eventually (Metric.ball_mem_nhds (0 : ℝ) hc)] with ε hε
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (hρpos ε)] at hε
    exact hε
  filter_upwards [hρsmall] with ε hρε
  intro s hs hsz
  -- the perturbation is `ε = a + i b`
  set a : ℝ := ε.re with ha
  set b : ℝ := ε.im with hb
  have heps : eps a b = ε := by
    rw [ha, hb, eps]
    exact Complex.re_add_im ε
  -- the total-degree bound for the perturbed system
  have hftd : ∀ i, (f i).totalDegree ≤ N₀ := by
    intro i
    refine le_trans (Nat.le_succ _) ?_
    rw [hN₀]
    exact le_trans (Finset.single_le_sum (f := fun i => atomDeg (f i))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
  have hgtd : ∀ i, (g i).totalDegree ≤ N₀ := by
    intro i
    refine le_trans (Nat.le_succ _) ?_
    rw [hN₀]
    exact le_trans (Finset.single_le_sum (f := fun i => atomDeg (g i))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
  have hdeg := ET.sum_deg_le c cc e N N₀ F f g a b (by omega) (by omega)
    (le_of_eq hN) hftd hgtd
  -- the ball and the chart estimates
  have hρpos' : 0 < ρ ε := hρpos ε
  have hR0 : 0 ≤ ρ ε := le_of_lt hρpos'
  have hsmall2 : 2 * ρ ε * A < Real.pi / 2 := by
    rcases eq_or_lt_of_le hA0 with h0 | h0
    · rw [← h0, mul_zero]
      linarith [Real.pi_pos]
    · have h4 : 2 * ρ ε * A < 2 * (Real.pi / (8 * (A + 1))) * A :=
        mul_lt_mul_of_pos_right (by linarith) h0
      have h5 : 2 * (Real.pi / (8 * (A + 1))) * A = Real.pi * A / (4 * (A + 1)) := by
        field_simp; ring
      rw [h5] at h4
      have h6 : Real.pi * A / (4 * (A + 1)) ≤ Real.pi / 2 := by
        have h7 : Real.pi / 2 - Real.pi * A / (4 * (A + 1))
            = Real.pi * (2 * (A + 1) - A) / (4 * (A + 1)) := by
          field_simp
          ring
        have h8 : 0 ≤ Real.pi * (2 * (A + 1) - A) / (4 * (A + 1)) :=
          div_nonneg (by nlinarith [Real.pi_pos]) (by linarith)
        linarith
      linarith
  have hvclose : ∀ {w : Fin (k + k) → ℝ}, dist w (cplxPt x) < 2 * ρ ε →
      ∀ i, |(vOf w) i - (x i).im| < 2 * ρ ε := by
    intro w hw i
    have h1 : (cplxPt x) (Fin.natAdd k i) = (x i).im := by
      simp only [cplxPt, mkPt_apply_natAdd]
    have h2 : |(vOf w) i - (x i).im| = dist (w (Fin.natAdd k i)) ((cplxPt x) (Fin.natAdd k i)) := by
      rw [Real.dist_eq, h1]
      simp only [vOf]
    rw [h2]
    exact lt_of_le_of_lt (dist_le_pi_dist w (cplxPt x) (Fin.natAdd k i)) hw
  -- membership in the ball
  have hsub : ∀ z ∈ s, cplxPt z ∈ Metric.ball (cplxPt x) (2 * ρ ε) := by
    intro z hz
    rw [Metric.mem_ball]
    have h1 := dist_cplxPt_le z x
    have h2 := hsz z hz
    linarith
  -- the domain condition on the ball
  have hdomD : ∀ w ∈ Metric.ball (cplxPt x) (2 * ρ ε),
      ∀ j, (∑ i, (mkChain c cc).a j i * w i) + (mkChain c cc).b j ∈ (mkChain c cc).dom j := by
    intro w hw j
    revert j
    refine Fin.addCases (motive := fun j => (∑ i, (mkChain c cc).a j i * w i)
        + (mkChain c cc).b j ∈ (mkChain c cc).dom j) ?_ ?_
    · intro j
      rw [mkChain_dom_castAdd]
      exact Set.mem_univ _
    · intro j
      rw [mkChain_dom_natAdd, mkChain_arg_natAdd', Set.mem_ofPred_eq]
      exact chart_hcos c cc x hccdom hR0 hsmall2 (hvclose (Metric.mem_ball.mp hw)) j
  -- the nondegeneracy
  have hnd : ∀ w ∈ s.image (cplxPt (k := k)),
      (mkChain c cc).Nondegen (realSys c cc e N f g a b) w := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    obtain ⟨hz0, hzd⟩ := hs z hz
    have hcosz : ∀ j, Real.cos ((∑ i, c.a j i * (z i).im - cc j) / 2) ≠ 0 := by
      intro j
      simpa [vOf_cplxPt] using
        chart_hcos c cc x hccdom hR0 hsmall2 (hvclose (Metric.mem_ball.mp (hsub z hz))) j
    refine ET.nondegen_of_cplx c cc e hec N f g a b z hcosz ?_ ?_ ?_ ?_
    · intro i
      exact le_trans (hftd i) (le_of_eq hN.symm |>.trans' (Nat.le_succ N₀))
    · intro i
      exact le_trans (hgtd i) (le_of_eq hN.symm |>.trans' (Nat.le_succ N₀))
    · intro i
      rw [heps]
      exact hz0 i
    · have hmeq : (Matrix.of fun i j => eaEvalC c (eaD c j (f i)) z
            + eps a b * eaEvalC c (eaD c j (g i)) z)
          = Matrix.of fun i j => eaEvalC c (eaD c j (f i)) z
            + ε * eaEvalC c (eaD c j (g i)) z := by
        ext i j
        simp only [Matrix.of_apply]
        rw [heps]
      rw [hmeq]
      exact hzd
  -- Khovanskii's bound
  have hle := hp (k + k) (r + r) (mkChain c cc)
    (realSys c cc e N f g a b)
    (Metric.ball (cplxPt x) (2 * ρ ε)) (s.image (cplxPt (k := k))) (by omega)
    (mkChain_isET c cc) (convex_ball _ _) hdomD
    (fun w hw => by
      rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
      exact hsub z hz) hnd
  -- the conclusion
  calc s.card
      = (s.image (cplxPt (k := k))).card := (Finset.card_image_of_injective s cplxPt_injective).symm
    _ ≤ p.eval (∑ i, atomDeg (realSys c cc e N f g a b i)
          + ∑ j, ((mkChain c cc).R j).totalDegree) := hle
    _ ≤ p.eval (6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F)) := eval_mono_nat p hdeg
    _ ≤ (p.comp (Polynomial.C (6 * F * (F + 1) + 1) * Polynomial.X
          + Polynomial.C (12 * F * F + 5 * F + 1))).eval N₀ := by
        rw [Polynomial.eval_comp]
        refine eval_mono_nat p ?_
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_C]
        nlinarith

end

end Work.WilE3.Realify
