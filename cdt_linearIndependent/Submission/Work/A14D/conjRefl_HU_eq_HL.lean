import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.conj_toolkit
import Submission.Work.A14D.H_cont
import Submission.Work.A14D.eqOn_of_sol_LZ
import Submission.Work.A14D.LZ_sub_const_mul
import Submission.Work.A14D.Dzc_helpers

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## Elementary reflection lemmas for the half-planes -/

lemma star_mem_SU_iff (z : ℂ) : star z ∈ SU ↔ z ∈ SL := by
  rw [mem_SU_iff, mem_SL_iff, Complex.star_def]
  simp only [Complex.conj_re, Complex.conj_im]
  constructor <;> intro h <;> linarith

lemma star_mem_SL_iff (z : ℂ) : star z ∈ SL ↔ z ∈ SU := by
  rw [mem_SL_iff, mem_SU_iff, Complex.star_def]
  simp only [Complex.conj_re, Complex.conj_im]
  constructor <;> intro h <;> linarith

lemma star_mem_ball_one (z : ℂ) :
    star z ∈ Metric.ball (0 : ℂ) 1 ↔ z ∈ Metric.ball 0 1 := by
  rw [Metric.mem_ball, Metric.mem_ball, Complex.dist_eq, Complex.dist_eq, sub_zero, sub_zero,
    norm_star]

/-! ## Uniqueness of the inhomogeneous equation `LZ y = rhsZ b c` -/

/-- Two functions which are holomorphic on an open preconnected `U ⊆ {PZ ≠ 0}`, solve the same
inhomogeneous equation `LZ y = rhsZ b c` there, and agree on a nonempty open subset `V ⊆ U`,
agree on all of `U`. -/
private lemma eqOn_of_same_rhs {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hP : ∀ z ∈ U, PZ z ≠ 0) {b c : ℤ} {G H : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G U) (hHd : DifferentiableOn ℂ H U)
    (hGL : ∀ z ∈ U, LZ G z = rhsZ b c z) (hHL : ∀ z ∈ U, LZ H z = rhsZ b c z)
    (hVsub : V ⊆ U) (hVo : IsOpen V) (hVne : V.Nonempty) (hag : Set.EqOn G H V) :
    Set.EqOn G H U := by
  -- the difference solves the homogeneous equation
  set d : ℂ → ℂ := fun w => G w - H w with hd_def
  have hd_eq : d = fun w => G w - (1 : ℂ) * H w := by funext w; simp [hd_def]
  have hd1 : DifferentiableOn ℂ d U := by
    rw [hd_def]; exact hGd.sub hHd
  have hL₁ : ∀ z ∈ U, LZ d z = 0 := by
    intro z hz
    have h := LZ_sub_const_mul hUo (1 : ℂ) hGd hHd hz
    rw [hd_eq, h, hGL z hz, hHL z hz]
    ring
  have hL₂ : ∀ z ∈ U, LZ (0 : ℂ → ℂ) z = 0 := fun z _ => by rw [LZ_def]; simp
  have hag' : Set.EqOn d 0 V := by
    intro z hz
    have h1 := hag hz
    show d z = 0
    simp only [hd_def, h1, sub_self]
  have hEq := Dzc_eqOn_of_agree_open hUo hUc hP hd1 (differentiableOn_const (0 : ℂ)) hL₁ hL₂
    hVsub hVo hVne hag'
  intro z hz
  have h := hEq hz
  simp only [hd_eq, one_mul] at h
  exact sub_eq_zero.mp h

/-- The continuation `HU` of `Hfun a b c` to the half-plane `SU` and the continuation `HL` to `SL`
are conjugate reflections of one another: `conjRefl HU = HL` on `SL` and `conjRefl HL = HU` on
`SU`, where `conjRefl f z = star (f (star z))`. -/
theorem conjRefl_HU_eq_HL (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ Metric.ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ Metric.ball 0 1, HL z = Hfun a b c z) :
    (∀ z ∈ SL, conjRefl HU z = HL z) ∧ (∀ z ∈ SU, conjRefl HL z = HU z) := by
  have hpt_L : ((-(1 / 2 : ℂ) * Complex.I : ℂ)) ∈ SL ∩ Metric.ball (0 : ℂ) 1 := by
    constructor
    · rw [mem_SL_iff]
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
      norm_num [Complex.normSq]
  have hpt_U : (((1 / 2 : ℂ) * Complex.I : ℂ)) ∈ SU ∩ Metric.ball (0 : ℂ) 1 := by
    constructor
    · rw [mem_SU_iff]
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      norm_num
    · rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
      norm_num [Complex.normSq]
  have hVneL : (SL ∩ Metric.ball (0 : ℂ) 1).Nonempty := ⟨_, hpt_L⟩
  have hVneU : (SU ∩ Metric.ball (0 : ℂ) 1).Nonempty := ⟨_, hpt_U⟩
  -- `G = conjRefl HU` on `SL`
  have hGd : DifferentiableOn ℂ (conjRefl HU) SL :=
    conjRefl_differentiableOn hHU.1 isOpen_SU_H_cont (fun z hz => (star_mem_SU_iff z).mpr hz)
  have hGL : ∀ z ∈ SL, LZ (conjRefl HU) z = rhsZ b c z := by
    intro z hz
    rw [LZ_conjRefl, hHU.2.1 (star z) ((star_mem_SU_iff z).mpr hz), star_rhsZ]
  have hGH : Set.EqOn (conjRefl HU) HL (SL ∩ Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hzU : star z ∈ SU := (star_mem_SU_iff z).mpr hz.1
    have hzb : star z ∈ Metric.ball (0 : ℂ) 1 := (star_mem_ball_one z).mpr hz.2
    show conjRefl HU z = HL z
    rw [conjRefl_apply, hHU.2.2 (star z) ⟨hzU, hzb⟩, Hfun_conj]
    exact (hHL.2.2 z hz).symm
  -- `G' = conjRefl HL` on `SU`
  have hG'd : DifferentiableOn ℂ (conjRefl HL) SU :=
    conjRefl_differentiableOn hHL.1 isOpen_SL_H_cont (fun z hz => (star_mem_SL_iff z).mpr hz)
  have hG'L : ∀ z ∈ SU, LZ (conjRefl HL) z = rhsZ b c z := by
    intro z hz
    rw [LZ_conjRefl, hHL.2.1 (star z) ((star_mem_SL_iff z).mpr hz), star_rhsZ]
  have hG'H : Set.EqOn (conjRefl HL) HU (SU ∩ Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hzL : star z ∈ SL := (star_mem_SL_iff z).mpr hz.1
    have hzb : star z ∈ Metric.ball (0 : ℂ) 1 := (star_mem_ball_one z).mpr hz.2
    show conjRefl HL z = HU z
    rw [conjRefl_apply, hHL.2.2 (star z) ⟨hzL, hzb⟩, Hfun_conj]
    exact (hHU.2.2 z hz).symm
  exact ⟨eqOn_of_same_rhs isOpen_SL_H_cont convex_SL.isPreconnected
      (fun z hz => PZ_ne_zero_of_mem_SL hz) hGd hHL.1 hGL hHL.2.1
      Set.inter_subset_left (isOpen_SL_H_cont.inter Metric.isOpen_ball) hVneL hGH,
    eqOn_of_same_rhs isOpen_SU_H_cont convex_SU.isPreconnected
      (fun z hz => PZ_ne_zero_of_mem_SU hz) hG'd hHU.1 hG'L hHU.2.1
      Set.inter_subset_left (isOpen_SU_H_cont.inter Metric.isOpen_ball) hVneU hG'H⟩

end

end Work.A14D
