import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A4c.PtCutId

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Linearity of `Tcut` in its cut -/

/-- `Work.FITop4.Tcut` is linear in the cut under multiplication by a real scalar. -/
theorem Tcut_smul_cut (Rz : ℤ) (lam : ℝ)
    (c : GaussianInt → GaussianInt → ℕ → ℝ) (β : GaussianInt → ℂ) :
    (lam : ℂ) * Work.FITop4.Tcut Rz c β
      = Work.FITop4.Tcut Rz (fun z1 z2 d => lam * c z1 z2 d) β := by
  rw [Work.FIArea4.Tcut_eq_sum_ofReal Rz c β,
      Work.FIArea4.Tcut_eq_sum_ofReal Rz (fun z1 z2 d => lam * c z1 z2 d) β]
  conv_lhs => rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z1 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hg, if_pos hg]
    have hinner : (lam : ℂ) * (((∑ d ∈ Work.FITop4.Sset z1 z2,
          (Nat.totient d : ℝ) / (d : ℝ) * c z1 z2 d
            * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℝ) : ℂ)
        = (((∑ d ∈ Work.FITop4.Sset z1 z2,
          (Nat.totient d : ℝ) / (d : ℝ) * (lam * c z1 z2 d)
            * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro d _
      ring
    rw [← hinner]
    ring
  · rw [if_neg hg, if_neg hg, mul_zero]

/-- Sums of scalar multiples of `Tcut`s merge into a single `Tcut`. -/
theorem Tcut_sum_smul_cut {ι : Type*} (s : Finset ι) (Rz : ℤ) (lam : ι → ℝ)
    (c : ι → GaussianInt → GaussianInt → ℕ → ℝ) (β : GaussianInt → ℂ) :
    (∑ i ∈ s, (lam i : ℂ) * Work.FITop4.Tcut Rz (c i) β)
      = Work.FITop4.Tcut Rz (fun z1 z2 d => ∑ i ∈ s, lam i * c i z1 z2 d) β := by
  rw [← Work.FIArea4.Tcut_sum_cut s Rz (fun i z1 z2 d => lam i * c i z1 z2 d) β]
  apply Finset.sum_congr rfl; intro i _
  exact Tcut_smul_cut Rz (lam i) (c i) β

/-! ## 2. Membership helpers for `Sset` -/

lemma mem_Icc_of_mem_Sset {z1 z2 : GaussianInt} {d : ℕ}
    (hd : d ∈ Work.FITop4.Sset z1 z2) :
    d ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) :=
  (Finset.mem_filter.mp hd).1

lemma dvd_of_mem_Sset {z1 z2 : GaussianInt} {d : ℕ}
    (hd : d ∈ Work.FITop4.Sset z1 z2) : 4 * d ∣ Work.FIPlan.absDelta z1 z2 :=
  (Finset.mem_filter.mp hd).2

lemma one_le_of_mem_Sset {z1 z2 : GaussianInt} {d : ℕ}
    (hd : d ∈ Work.FITop4.Sset z1 z2) : 1 ≤ d :=
  (Finset.mem_Icc.mp (mem_Icc_of_mem_Sset hd)).1

/-! ## 3. The exact splitting of `Vcut` -/

/-- **The new exact splitting of `Vcut`** (design `Submission/Work/FIArea4/AREA4_ENGINES_LEAD.md`
§3.2, node N6). -/
theorem Vcut_eq_A4c (Rz : ℤ) (X : ℕ) (hX : 2 ≤ X) (β : GaussianInt → ℂ) (J : ℕ)
    (hJ : ∀ z1 z2 d, z1 ∈ Work.FIPlan.gBox Rz → z2 ∈ Work.FIPlan.gBox Rz →
      d ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) →
      2 * ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ))) ≤ 2 ^ J) :
    Work.FITop4.Vcut Rz X β
      = (∑ j ∈ Finset.range J,
          Work.FITop4.Tcut Rz (Work.FIArea4.A6cut Work.FIArea4.A4c.psiA X j) β)
        - (Work.FITop4.Wcut Rz X β + Work.FITop4.Bcut Rz X β)
        + ∑ m ∈ Finset.Ico 1 X, ((Work.FIArea4.A4c.wA X m : ℝ) : ℂ) *
            (Work.FITop4.Wcut Rz m β + Work.FITop4.Bcut Rz m β
              - Work.FITop4.Tcut Rz (Work.FIArea4.A4c.junkCut X m) β) := by
  classical
  have hA : (∑ j ∈ Finset.range J, Work.FITop4.Tcut Rz (Work.FIArea4.A6cut psiA X j) β)
      = Work.FITop4.Tcut Rz (fun z1 z2 d =>
          ∑ j ∈ Finset.range J, Work.FIArea4.A6cut psiA X j z1 z2 d) β :=
    Work.FIArea4.Tcut_sum_cut (Finset.range J) Rz (Work.FIArea4.A6cut psiA X) β
  have hWB : Work.FITop4.Wcut Rz X β + Work.FITop4.Bcut Rz X β
      = Work.FITop4.Tcut Rz (fun z1 z2 d =>
          (if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          + (if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)) β := by
    rw [show Work.FITop4.Wcut Rz X β = Work.FITop4.Tcut Rz (fun z1 z2 d =>
          if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β from rfl,
        show Work.FITop4.Bcut Rz X β = Work.FITop4.Tcut Rz (fun z1 z2 d =>
          if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β from rfl,
        Work.FIArea4.Tcut_add_cut]
  have hC : (∑ m ∈ Finset.Ico 1 X, (wA X m : ℂ) *
        (Work.FITop4.Wcut Rz m β + Work.FITop4.Bcut Rz m β
          - Work.FITop4.Tcut Rz (junkCut X m) β))
      = Work.FITop4.Tcut Rz (fun z1 z2 d => ∑ m ∈ Finset.Ico 1 X, wA X m *
          (((if m < d ∧ 4 * d * m > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
            + (if m < d ∧ 4 * d * m = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0))
           - junkCut X m z1 z2 d)) β := by
    rw [← Tcut_sum_smul_cut (Finset.Ico 1 X) Rz (fun m => wA X m)
          (fun m z1 z2 d =>
            ((if m < d ∧ 4 * d * m > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
              + (if m < d ∧ 4 * d * m = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0))
            - junkCut X m z1 z2 d) β]
    apply Finset.sum_congr rfl; intro m _
    have hm : Work.FITop4.Wcut Rz m β + Work.FITop4.Bcut Rz m β
        - Work.FITop4.Tcut Rz (junkCut X m) β
        = Work.FITop4.Tcut Rz (fun z1 z2 d =>
            ((if m < d ∧ 4 * d * m > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
              + (if m < d ∧ 4 * d * m = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0))
            - junkCut X m z1 z2 d) β := by
      rw [show Work.FITop4.Wcut Rz m β = Work.FITop4.Tcut Rz (fun z1 z2 d =>
            if m < d ∧ 4 * d * m > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β from rfl,
          show Work.FITop4.Bcut Rz m β = Work.FITop4.Tcut Rz (fun z1 z2 d =>
            if m < d ∧ 4 * d * m = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β from rfl,
          Work.FIArea4.Tcut_add_cut, Work.FIArea4.Tcut_sub_cut]
    rw [hm]
  rw [hA, hWB, hC]
  rw [Work.FIArea4.Tcut_sub_cut, Work.FIArea4.Tcut_add_cut]
  rw [show Work.FITop4.Vcut Rz X β = Work.FITop4.Tcut Rz (fun z1 z2 d =>
        if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β from rfl]
  refine Work.FIArea4.Tcut_congr_cut_local Rz _ _ β ?_
  intro z1 z2 d hz1 hz2 hd
  have hdIcc : d ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) := mem_Icc_of_mem_Sset hd
  have hdvd : 4 * d ∣ Work.FIPlan.absDelta z1 z2 := dvd_of_mem_Sset hd
  have hd1 : 1 ≤ d := one_le_of_mem_Sset hd
  have hJd := hJ z1 z2 d hz1 hz2 hdIcc
  show (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
    = (∑ j ∈ Finset.range J, (if X < d then psiA
          ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) else 0))
      - ((if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          + (if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0))
      + ∑ m ∈ Finset.Ico 1 X, wA X m *
          (((if m < d ∧ 4 * d * m > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
            + (if m < d ∧ 4 * d * m = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0))
           - junkCut X m z1 z2 d)
  exact (PtCutId X hX z1 z2 d hd1 hdvd J hJd).symm

end

end Work.FIArea4.A4c
