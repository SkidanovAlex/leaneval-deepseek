import Mathlib
import Submission.Work.BMF.liouville.vkbl_defs
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weyl's inequality for `TrelP`
-/

open Finset

namespace Work.BMF.liouville

noncomputable section

/-- `TrelP` in the shape used by `weyl_inequality` (`M₀ = 1`, summation over `range M`). -/
lemma TrelP_eq_weyl_form (k M : ℕ) (n : ℕ) (u t : ℝ) :
    TrelP k M n u t
      = ∑ x ∈ Finset.range M,
          Complex.exp ((↑(2 * Real.pi * (Work.BMF.zpt.tayPoly k t (n : ℝ) u).eval
            (((1 : ℤ) : ℝ) + (x : ℝ))) : ℂ) * Complex.I) := by
  have h1 : TrelP k M n u t
      = ∑ m ∈ Finset.Icc 1 M,
          Work.BMF.eC ((Work.BMF.zpt.tayPoly k t (n : ℝ) u).eval (m : ℝ)) := by
    unfold TrelP tayRel Work.BMF.zpt.tayPhase
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eval_tayPoly]
  rw [h1]
  rw [show Finset.Icc 1 M = Finset.Ico 1 (M + 1) from by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold Work.BMF.eC
  congr 1
  push_cast
  ring_nf

theorem TrelP_weyl (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (n : ℕ) (u t : ℝ),
      1 ≤ M → 0 < t → 0 < u → 1 ≤ n →
      0 < |Work.BMF.zpt.gam k t (n : ℝ) u| → |Work.BMF.zpt.gam k t (n : ℝ) u| ≤ 1 →
      ‖TrelP k M n u t‖ ≤
        C * (M : ℝ) ^ (1 + ε) *
          (1 / ((⌊1 / |Work.BMF.zpt.gam k t (n : ℝ) u|⌋₊ : ℝ)) + 1 / (M : ℝ)
            + 1 / (M : ℝ) ^ (k - 1)
            + ((⌊1 / |Work.BMF.zpt.gam k t (n : ℝ) u|⌋₊ : ℝ)) / (M : ℝ) ^ k)
            ^ ((2 : ℝ) ^ (1 - (k : ℝ))) := by
  obtain ⟨C, hC, hW⟩ :=
    Commons.Analysis.ExponentialSums.weyl_inequality k hk hε (t := 1) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro M n u t hM ht hu hn hA0 hA1
  set A : ℝ := |Work.BMF.zpt.gam k t (n : ℝ) u| with hA
  set q : ℕ := ⌊1 / A⌋₊ with hq
  set a : ℤ := if 0 < Work.BMF.zpt.gam k t (n : ℝ) u then 1 else -1 with ha
  have hq1 : 1 ≤ q := by
    rw [hq]
    apply Nat.le_floor
    rw [le_div_iff₀ (by exact hA0)]
    simpa using hA1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqle : (q : ℝ) ≤ 1 / A := by
    rw [hq]; exact Nat.floor_le (by positivity)
  have hqlt : 1 / A < (q : ℝ) + 1 := by
    rw [hq]; exact Nat.lt_floor_add_one (1 / A)
  have hle1 : A ≤ 1 / (q : ℝ) := by
    rw [le_div_iff₀ hqpos, mul_comm]
    have h := hqle
    rw [le_div_iff₀ hA0] at h
    exact h
  have hkey : 1 / (q : ℝ) - A ≤ 1 / (q : ℝ) ^ 2 := by
    have h1 : 1 < A * ((q : ℝ) + 1) := by
      have h := hqlt
      rw [div_lt_iff₀ hA0] at h
      rwa [mul_comm] at h
    have h2 : 1 / ((q : ℝ) + 1) < A := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < (q : ℝ) + 1)]
      exact h1
    have h3 : 1 / (q : ℝ) - A < 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) := by linarith
    have h4 : 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) = 1 / ((q : ℝ) * ((q : ℝ) + 1)) := by
      field_simp; ring
    have h5 : 1 / ((q : ℝ) * ((q : ℝ) + 1)) ≤ 1 / (q : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hqpos]
    linarith
  have hgcd : Int.gcd a (q : ℤ) = 1 := by
    have ha1 : a = 1 ∨ a = -1 := by rw [ha]; split <;> simp
    rcases ha1 with h | h <;> rw [h]
    · exact Int.gcd_one_left _
    · simp [Int.gcd_def]
  have hsign : (a : ℝ) = if 0 < Work.BMF.zpt.gam k t (n : ℝ) u then (1 : ℝ) else -1 := by
    rw [ha]
    by_cases h : 0 < Work.BMF.zpt.gam k t (n : ℝ) u
    · rw [if_pos h, if_pos h]; norm_num
    · rw [if_neg h, if_neg h]; norm_num
  have habs : |Work.BMF.zpt.gam k t (n : ℝ) u - (a : ℝ) / (((q : ℤ)) : ℝ)|
      ≤ 1 / (((q : ℤ)) : ℝ) ^ 2 := by
    have hcast : (((q : ℤ)) : ℝ) = (q : ℝ) := by push_cast; ring
    rw [hcast]
    rcases lt_trichotomy (Work.BMF.zpt.gam k t (n : ℝ) u) 0 with hlt | heq | hgt
    · have hγ : Work.BMF.zpt.gam k t (n : ℝ) u = -A := by rw [hA]; linarith [abs_of_neg hlt]
      rw [hsign, if_neg (not_lt.mpr hlt.le), hγ]
      rw [show -A - (-1) / (q : ℝ) = -(A - 1 / (q : ℝ)) by ring, abs_neg,
          abs_of_nonpos (by linarith [hle1])]
      linarith [hkey]
    · rw [heq] at hA
      simp at hA
      linarith [hA0, hA]
    · have hγ : Work.BMF.zpt.gam k t (n : ℝ) u = A := by rw [hA]; linarith [abs_of_pos hgt]
      rw [hsign, if_pos hgt, hγ, abs_of_nonpos (by linarith [hle1])]
      linarith [hkey]
  have hne : Work.BMF.zpt.gam k t (n : ℝ) u ≠ 0 := by
    intro h0
    have h2 : A = 0 := by rw [hA, h0]; simp
    linarith [hA0, h2]
  have hnd : (Work.BMF.zpt.tayPoly k t (n : ℝ) u).natDegree = k := natDegree_tayPoly k hk t u n hne
  have hlc : (Work.BMF.zpt.tayPoly k t (n : ℝ) u).leadingCoeff = Work.BMF.zpt.gam k t (n : ℝ) u :=
    leadingCoeff_tayPoly k hk t u n hne
  rw [← hlc] at habs
  have hb := hW (1 : ℤ) M a (q : ℤ) (Work.BMF.zpt.tayPoly k t (n : ℝ) u)
      (by exact_mod_cast hq1) hgcd hnd habs
  rw [TrelP_eq_weyl_form]
  simpa using hb

end

end Work.BMF.liouville
