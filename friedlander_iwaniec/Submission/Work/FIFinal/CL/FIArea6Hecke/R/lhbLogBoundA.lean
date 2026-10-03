
/-
# Submission.Work.FIArea6Hecke.R.lhbLogBoundA

The polylogarithmic bound for the Hecke L-series on re s > 1, with an absolute constant, in the
DiscDefs-world of the primary disc sums:

  ||L(s)|| <= C.log(4.d.(2+||s||))   for   re s > 1,

for a strict character chi mod 4d which is nontrivial on a primary unit.

Assembly: the mean-zero cancellation of the primary disc sums (LHBDisc, with an absolute constant),
the head bound sum_{n<=M}||lambda(n)||/n <= Kh log(M+2) (LHBHead), the Abel estimate for partial
sums O(N^{1/2}) (abelThetaHalf), and the reindexing identity
sum_{n<=N} lambda(n) = discSum N (LHBPartialSum), fed into
heckeLSeries_ReGtOne_bound (LHBReGtOne).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LHBDisc
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.LHBHead
import Submission.Work.FIArea6Hecke.R.LHBPartialSum
import Submission.Work.FIArea6Hecke.R.LHBReGtOne
import Submission.Work.FIArea6Hecke.R.abelThetaHalf

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

theorem heckeLSeriesReGtOneBoundA :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ s : ℂ, 1 < s.re →
          ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 s‖
            ≤ C * Real.log (4 * (d : ℝ) * (2 + ‖s‖)) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := LHBDisc
  obtain ⟨Kh, hKhpos, hKh⟩ := LHBHead
  obtain ⟨Ka, hKapos, hKa⟩ := abelThetaHalf
  refine ⟨(10 * (Kh + 1) * (Ka + 1) + 10) * (1 + max (Real.log (max Cd 1)) 0), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 10 * (Kh + 1) * (Ka + 1) + 10 := by positivity
    have h2 : (0 : ℝ) < 1 + max (Real.log (max Cd 1)) 0 := by
      have : (0 : ℝ) ≤ max (Real.log (max Cd 1)) 0 := le_max_right _ _
      linarith
    positivity
  · intro d hd chi hchi hnt s hs
    have hCd1 : (1 : ℝ) ≤ max Cd 1 := le_max_right _ _
    have hdisc : ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ X : ℝ, 1 ≤ X →
          ‖Work.FIArea6Hecke.R.discSum X chi‖ ≤ max Cd 1 * (d : ℝ) * Real.sqrt X := by
      intro d' hd' chi' hchi' hnt' X hX
      have h1 : Cd * (d' : ℝ) * Real.sqrt X ≤ max Cd 1 * (d' : ℝ) * Real.sqrt X := by
        have hle : Cd ≤ max Cd 1 := le_max_left Cd 1
        have h0 : (0 : ℝ) ≤ (d' : ℝ) * Real.sqrt X := by positivity
        have h2 := mul_le_mul_of_nonneg_right hle h0
        calc Cd * (d' : ℝ) * Real.sqrt X = Cd * ((d' : ℝ) * Real.sqrt X) := by ring
          _ ≤ (max Cd 1) * ((d' : ℝ) * Real.sqrt X) := h2
          _ = max Cd 1 * (d' : ℝ) * Real.sqrt X := by ring
      exact (hCd d' hd' chi' hchi' hnt' X hX).trans h1
    have hbound := heckeLSeries_ReGtOne_bound (d := d) (hd := hd) (chi := chi)
      hCd1 hKhpos hKapos (fun chi' N => LHBPartialSum chi' N) hdisc
      (fun chi' hb M => hKh chi' hb M)
      (fun {a} {C} hC hA => hKa hC hA) hchi hnt s hs
    refine hbound.trans ?_
    -- absorb the constant  inside the logarithm
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hlog1 : (1 : ℝ) ≤ Real.log (4 * (d : ℝ) * (2 + ‖s‖)) := by
      have h8 : (12 : ℝ) ≤ 4 * (d : ℝ) * (2 + ‖s‖) := by
        have hsn : (1 : ℝ) ≤ ‖s‖ := by
          have h := Complex.abs_re_le_norm s
          rw [abs_of_pos (by linarith : (0 : ℝ) < s.re)] at h
          linarith
        have h2s : (3 : ℝ) ≤ 2 + ‖s‖ := by linarith
        nlinarith [hd1, h2s]
      have hlog12 : (1 : ℝ) < Real.log 12 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith [Real.exp_one_lt_three]
      exact le_trans (le_of_lt hlog12) (Real.log_le_log (by norm_num) h8)
    have hsplit : Real.log (4 * max Cd 1 * (d : ℝ) * (2 + ‖s‖))
        ≤ (1 + max (Real.log (max Cd 1)) 0) * Real.log (4 * (d : ℝ) * (2 + ‖s‖)) := by
      have hCd1pos : (0 : ℝ) < max Cd 1 := lt_of_lt_of_le one_pos hCd1
      have hargpos : (0 : ℝ) < 4 * (d : ℝ) * (2 + ‖s‖) := by
        have h2s : (0 : ℝ) < 2 + ‖s‖ := by have := norm_nonneg s; linarith
        positivity
      have hre : 4 * max Cd 1 * (d : ℝ) * (2 + ‖s‖)
          = max Cd 1 * (4 * (d : ℝ) * (2 + ‖s‖)) := by ring
      rw [hre, Real.log_mul (ne_of_gt hCd1pos) (ne_of_gt hargpos)]
      have hlogCd : Real.log (max Cd 1) ≤ max (Real.log (max Cd 1)) 0 := le_max_left _ _
      nlinarith [hlog1, hlogCd, Real.log_nonneg hCd1]
    calc (10 * (Kh + 1) * (Ka + 1) + 10) * Real.log (4 * max Cd 1 * (d : ℝ) * (2 + ‖s‖))
        ≤ (10 * (Kh + 1) * (Ka + 1) + 10)
            * ((1 + max (Real.log (max Cd 1)) 0) * Real.log (4 * (d : ℝ) * (2 + ‖s‖))) := by
          refine mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ = (10 * (Kh + 1) * (Ka + 1) + 10) * (1 + max (Real.log (max Cd 1)) 0)
            * Real.log (4 * (d : ℝ) * (2 + ‖s‖)) := by ring

end

end Work.FIArea6Hecke.R
