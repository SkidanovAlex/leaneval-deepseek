import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.A7.Wf_Cf_mono
import Submission.Work.LinnikContract.API.Bfun_pos
import Submission.Work.A7.Bfun_antitone_all
import Submission.Work.A7.Wf_antitone_ne
import Submission.Work.A7.ExpWf_antitone_ne
import Submission.Work.A7.Wf_pos_ne

noncomputable section

namespace Work.A7

open Work.LinnikContract
open Work.LinnikContract.API
open Work.LinnikAreas.A7

/-- `B(0) = 1/(3K) + 1 = 19/9` for `K = 3/10`. -/
private lemma Bfun_Kc_zero : Bfun Kc 0 = 19/9 := by
  rw [Bfun]
  norm_num [Kc]

/-- `B(3/10,·)` is strictly positive away from `0`. -/
private lemma Bfun_Kc_pos_ne {x : ℝ} (hx : x ≠ 0) : 0 < Bfun Kc x := by
  have hKc : (0:ℝ) < Kc := by norm_num [Kc]
  rcases lt_or_gt_of_ne hx with hl | hg
  · have h := Bfun_antitone_all hKc (x := x) (y := 0) hl.le
    rw [Bfun_Kc_zero] at h
    linarith
  · exact Bfun_pos hKc hg

/-- The ratio `R(λ) = Φ(λ)/w(λ)` is non-increasing on `ℝ ∖ {0}`. -/
theorem PhiWf_antitone_ne : ∀ {x y : ℝ}, x ≤ y → x ≠ 0 → y ≠ 0 → Phi y / Wf y ≤ Phi x / Wf x := by
  have hKc : (0:ℝ) < Kc := by norm_num [Kc]
  have hfac : ∀ z : ℝ, Phi z / Wf z = Bfun Kc z * (Real.exp (-((49:ℝ)/10 * z)) / Wf z) := by
    intro z
    have hac : ac = (49:ℝ)/10 := by norm_num [ac]
    unfold Phi
    rw [hac, div_eq_mul_inv, div_eq_mul_inv]
    ring
  intro x y hxy hx hy
  rw [hfac x, hfac y]
  refine mul_le_mul (Bfun_antitone_all hKc hxy) (ExpWf_antitone_ne hxy hx hy)
    (le_of_lt (div_pos (Real.exp_pos _) (Wf_pos_ne hy)))
    (le_of_lt (Bfun_Kc_pos_ne hx))

/-- **Area 7.**  If `348/1000 ≤ λ₁ ≤ Λ` then `C(Λ,λ₁) ≤ C(Λ,z)` for every `z ≤ 0`. -/
theorem Cf_nonpos {Lam lam1 z : ℝ} (h348 : (348:ℝ)/1000 ≤ lam1) (h1Lam : lam1 ≤ Lam) (hz : z ≤ 0) :
    Work.LinnikAreas.A7.Cf Lam lam1 ≤ Work.LinnikAreas.A7.Cf Lam z := by
  have hKc : (0:ℝ) < Kc := by norm_num [Kc]
  have hcpos : (0:ℝ) < (348:ℝ)/1000 := by norm_num
  have hlam1pos : 0 < lam1 := lt_of_lt_of_le hcpos h348
  have hLam : 0 < Lam := lt_of_lt_of_le hlam1pos h1Lam
  have hcLam : (348:ℝ)/1000 ≤ Lam := le_trans h348 h1Lam
  have hPhiLam : 0 < Phi Lam := mul_pos (Real.exp_pos _) (Bfun_pos hKc hLam)
  rcases lt_or_eq_of_le hz with hzlt | hz0
  · -- `z < 0`
    have hz0' : z ≠ 0 := ne_of_lt hzlt
    have hzc : z ≤ (348:ℝ)/1000 := le_trans hz hcpos.le
    have hWfz : Wf z ≠ 0 := ne_of_gt (Wf_pos_ne hz0')
    have hA : Cf Lam lam1 ≤ Cf Lam ((348:ℝ)/1000) :=
      Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hLam hcpos h348
    have hRc : Phi Lam / Wf Lam ≤ Phi ((348:ℝ)/1000) / Wf ((348:ℝ)/1000) :=
      PhiWf_antitone hcpos hcLam
    have hRz : Phi ((348:ℝ)/1000) / Wf ((348:ℝ)/1000) ≤ Phi z / Wf z :=
      PhiWf_antitone_ne hzc hz0' (ne_of_gt hcpos)
    have hWfcz : Wf ((348:ℝ)/1000) ≤ Wf z :=
      Wf_antitone_ne hzc hz0' (ne_of_gt hcpos)
    have hCfeq : Cf Lam ((348:ℝ)/1000)
        = Wf ((348:ℝ)/1000) *
            (Phi ((348:ℝ)/1000) / Wf ((348:ℝ)/1000) - Phi Lam / Wf Lam) := by
      have hprod : 0 ≤ Wf ((348:ℝ)/1000) *
          (Phi ((348:ℝ)/1000) / Wf ((348:ℝ)/1000) - Phi Lam / Wf Lam) :=
        mul_nonneg (Wf_pos hcpos).le (by linarith)
      rw [Cf_eq_max hLam hcpos, max_eq_right hprod]
    have hCfz : Cf Lam z = max 0 (Wf z * (Phi z / Wf z - Phi Lam / Wf Lam)) := by
      rw [Cf]
      congr 1
      field_simp
    have hstep : Wf ((348:ℝ)/1000) *
          (Phi ((348:ℝ)/1000) / Wf ((348:ℝ)/1000) - Phi Lam / Wf Lam)
        ≤ Wf z * (Phi z / Wf z - Phi Lam / Wf Lam) :=
      mul_le_mul hWfcz (by linarith) (by linarith) (Wf_pos_ne hz0').le
    have hB : Cf Lam ((348:ℝ)/1000) ≤ Cf Lam z := by
      rw [hCfeq, hCfz]
      exact le_trans hstep (le_max_right 0 _)
    exact le_trans hA hB
  · -- `z = 0`
    subst hz0
    have hW0 : Wf 0 = 0 := by unfold Wf Work.LinnikContract.wHB; norm_num
    have hPhi0 : Phi 0 = 19/9 := by
      unfold Phi
      rw [Bfun_Kc_zero]
      norm_num
    have hCf0 : Cf Lam 0 = 19/9 := by
      rw [Cf, hPhi0, hW0, mul_zero, zero_div, sub_zero, max_eq_right (by norm_num)]
    rw [hCf0]
    have h1 : Cf Lam lam1 ≤ Phi lam1 := by
      rw [Cf]
      refine max_le (mul_pos (Real.exp_pos _) (Bfun_pos hKc hlam1pos)).le ?_
      have : 0 ≤ Phi Lam * Wf lam1 / Wf Lam :=
        div_nonneg (mul_nonneg hPhiLam.le (Wf_pos hlam1pos).le) (Wf_pos hLam).le
      linarith
    have h2 : Phi lam1 ≤ 19/9 := by
      have hBle : Bfun Kc lam1 ≤ Bfun Kc 0 := Bfun_antitone_all hKc hlam1pos.le
      rw [Bfun_Kc_zero] at hBle
      have hexp : Real.exp (-(ac * lam1)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hac : 0 < ac := by norm_num [ac]
        nlinarith
      have hBnn : 0 ≤ Bfun Kc lam1 := (Bfun_pos hKc hlam1pos).le
      have h := mul_le_mul hexp hBle hBnn (by norm_num : (0:ℝ) ≤ 1)
      simpa [Phi] using h
    linarith

end Work.A7
