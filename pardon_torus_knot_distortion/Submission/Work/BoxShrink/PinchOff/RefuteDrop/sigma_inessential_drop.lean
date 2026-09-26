import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## Coordinates of `dropVec` -/

theorem dvc0 (x : R3) : (dropVec x).ofLp 0 = (-2/25) * x.ofLp 0 + (-39/100) * x.ofLp 1 + (97/100) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]; simp [dropA]

theorem dvc1 (x : R3) : (dropVec x).ofLp 1 = (81/100) * x.ofLp 0 + (53/50) * x.ofLp 1 + (-3/25) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]; simp [dropA]

theorem dvc2 (x : R3) : (dropVec x).ofLp 2 = (49/100) * x.ofLp 0 + (31/25) * x.ofLp 1 + (59/100) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]; simp [dropA]

theorem sin_09_ge : (0.7785:ℝ) ≤ Real.sin (9/10) := by
  have h := Real.sin_gt_sub_cube (x := (9/10:ℝ)) (by norm_num)
  norm_num at h ⊢
  linarith

theorem sin_09_20_ge : (0.4348125:ℝ) ≤ Real.sin (9/20) := by
  have h := Real.sin_gt_sub_cube (x := (9/20:ℝ)) (by norm_num)
  norm_num at h ⊢
  linarith

theorem cos_09_le : Real.cos (9/10) ≤ 0.63 := by
  have h2 : (9/10:ℝ) = 2*(9/20) := by norm_num
  rw [h2, Real.cos_two_mul]
  have h := sin_09_20_ge
  have hcs : Real.cos (9/20)^2 + Real.sin (9/20)^2 = 1 := Real.cos_sq_add_sin_sq (9/20)
  have hnn : 0 ≤ Real.sin (9/20) := by linarith
  nlinarith [h, hcs, hnn, sq_nonneg (Real.sin (9/20) - 0.4348125)]

/-- sin is decreasing on [π/2, π]. -/
theorem sin_ge_of_mem_Icc {x y : ℝ} (hx : Real.pi/2 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.pi) :
    Real.sin y ≤ Real.sin x := by
  rw [← Real.sin_pi_sub x, ← Real.sin_pi_sub y]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · linarith [Real.pi_pos]
  · linarith
  · linarith

theorem abs_sin_ge_of_mem {φ : ℝ} (h1 : (503:ℝ)/100 ≤ φ) (h2 : φ ≤ 2*Real.pi - 9/10) :
    (0.7785:ℝ) ≤ |Real.sin φ| := by
  have hmem : φ - Real.pi ∈ Set.Ioo (0:ℝ) Real.pi :=
    ⟨by linarith [Real.pi_lt_d2], by linarith⟩
  have hpos : 0 < Real.sin (φ - Real.pi) := Real.sin_pos_of_mem_Ioo hmem
  have hsin : Real.sin (φ - Real.pi) = - Real.sin φ := by
    rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]; ring
  have hneg : Real.sin φ < 0 := by linarith [hsin, hpos]
  have habs : |Real.sin φ| = Real.sin (φ - Real.pi) := by
    rw [abs_of_neg hneg, ← hsin]
  rw [habs]
  have hx : Real.pi/2 ≤ φ - Real.pi := by linarith [Real.pi_lt_d2]
  have hy : φ - Real.pi ≤ Real.pi - 9/10 := by linarith
  have hyπ : Real.pi - 9/10 ≤ Real.pi := by linarith
  have hstep : Real.sin (Real.pi - 9/10) ≤ Real.sin (φ - Real.pi) :=
    sin_ge_of_mem_Icc hx hy hyπ
  have hsin09 : Real.sin (Real.pi - 9/10) = Real.sin (9/10) := Real.sin_pi_sub (9/10)
  rw [hsin09] at hstep
  linarith [hstep, sin_09_ge]

theorem cos_le_of_mem {φ : ℝ} (h1 : (503:ℝ)/100 ≤ φ) (h2 : φ ≤ 2*Real.pi - 9/10) :
    Real.cos φ ≤ 0.63 := by
  rw [← Real.cos_two_pi_sub φ]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := (9/10:ℝ)) (y := 2*Real.pi - φ)
    (by norm_num) (by linarith [Real.pi_lt_d2]) (by linarith)
  linarith [h, cos_09_le]

/-- **Fact A**: on the plane `x = 0` with `φ` in the bad window, the `z`-coordinate is large. -/
theorem factA {u v w φ : ℝ} (hpl : -8*u - 39*v + 97*w = 0)
    (hnorm : u^2 + v^2 = (2 + Real.cos φ)^2)
    (hw : w = Real.sin φ)
    (hφ1 : (503:ℝ)/100 ≤ φ) (hφ2 : φ ≤ 2*Real.pi - 9/10) :
    (7:ℝ)/5 < |(49/100)*u + (31/25)*v + (59/100)*w| := by
  have hz : 3900 * ((49/100)*u + (31/25)*v + (59/100)*w) = 919*u + 14329*w := by linarith
  have hwabs : (0.7785:ℝ) ≤ |w| := by rw [hw]; exact abs_sin_ge_of_mem hφ1 hφ2
  have hrle : 2 + Real.cos φ ≤ 2.63 := by linarith [cos_le_of_mem hφ1 hφ2]
  have hrpos : (0:ℝ) ≤ 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have hul : |u| ≤ 2 + Real.cos φ := by
    have h2 : u^2 ≤ (2 + Real.cos φ)^2 := by nlinarith [hnorm, sq_nonneg v]
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_nonneg hrpos] at h3
  have hzabs : |(49/100)*u + (31/25)*v + (59/100)*w| = |919*u + 14329*w| / 3900 := by
    have hh := congrArg abs hz
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3900)] at hh
    linarith
  rw [hzabs]
  have hua : |919*u| = 919*|u| := by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<919)]
  have hwa : |14329*w| = 14329*|w| := by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<14329)]
  have h1 : 14329 * |w| - 919 * |u| ≤ |919*u + 14329*w| := by
    have h := abs_add_le (919*u + 14329*w) (-(919*u))
    have h' : 919*u + 14329*w + -(919*u) = 14329*w := by ring
    rw [h', hwa] at h
    have hneg : |-(919*u)| = 919*|u| := by rw [abs_neg, hua]
    rw [hneg] at h
    linarith
  have h2 : (14329 * (0.7785:ℝ) - 919 * 2.63) ≤ 14329 * |w| - 919 * |u| := by
    have h3 : 919 * |u| ≤ 919 * 2.63 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith [hul, hrle]
    have h4 : (14329:ℝ) * 0.7785 ≤ 14329 * |w| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hwabs
    linarith
  have h3 : (7:ℝ)/5 < (14329 * (0.7785:ℝ) - 919 * 2.63) / 3900 := by norm_num
  have h4 : |919*u + 14329*w| / 3900 ≥ (14329 * (0.7785:ℝ) - 919 * 2.63) / 3900 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith
  linarith [h4, h3]


theorem cos_14132_ge : (0.15:ℝ) ≤ Real.cos (1.4132) := by
  have hd0 : 0 < Real.pi/2 - 1.4132 := by linarith [Real.pi_gt_d20]
  have h := Real.sin_gt_sub_cube hd0
  have hd1 : Real.pi/2 - 1.4132 < 0.1576 := by linarith [Real.pi_lt_d20]
  have hd2 : (0.1575:ℝ) < Real.pi/2 - 1.4132 := by linarith [Real.pi_gt_d20]
  have hcos : Real.cos (1.4132) = Real.sin (Real.pi/2 - 1.4132) := by
    conv_lhs => rw [show (1.4132:ℝ) = Real.pi/2 - (Real.pi/2 - 1.4132) by ring]
    rw [Real.cos_pi_div_two_sub]
  rw [hcos]
  nlinarith [h, hd0, hd1, hd2, sq_nonneg (Real.pi/2 - 1.4132 - 0.1576)]

theorem sin_132_ge : (0.96:ℝ) ≤ Real.sin (1.32) := by
  have hg0 : 0 < Real.pi/2 - 1.32 := by linarith [Real.pi_gt_d20]
  have hg1 : Real.pi/2 - 1.32 < 0.2508 := by linarith [Real.pi_lt_d20]
  have hsin : Real.sin (1.32) = Real.cos (Real.pi/2 - 1.32) := by
    conv_lhs => rw [show (1.32:ℝ) = Real.pi/2 - (Real.pi/2 - 1.32) by ring]
    rw [Real.sin_pi_div_two_sub]
  rw [hsin]
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi/2 - 1.32)
  nlinarith [h, hg0, hg1, sq_nonneg (Real.pi/2 - 1.32 - 0.2508)]

/-- **Fact B**: on the plane `x = 0` with `θ` in the bad window, the `z`-coordinate is large. -/
theorem factB {u v w φ θ : ℝ} (hpl : -8*u - 39*v + 97*w = 0)
    (hu : u = (2 + Real.cos φ) * Real.cos θ) (hv : v = (2 + Real.cos φ) * Real.sin θ)
    (hθ1 : (33:ℝ)/25 ≤ θ) (hθ2 : θ ≤ 1.4132) :
    (7:ℝ)/5 < (49/100)*u + (31/25)*v + (59/100)*w := by
  have hrpos : (0:ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have hr1 : (1:ℝ) ≤ 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have hcosθ : 0.15 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := (1.4132:ℝ))
      (by linarith) (by linarith [Real.pi_gt_d20]) hθ2
    linarith [h, cos_14132_ge]
  have hsinθ : 0.96 ≤ Real.sin θ := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := (33:ℝ)/25) (y := θ)
      (by linarith [Real.pi_gt_d20]) (by linarith [Real.pi_gt_d20]) hθ1
    linarith [h, sin_132_ge]
  have hu1 : 0.15 * (2 + Real.cos φ) ≤ u := by rw [hu]; nlinarith [hrpos, hcosθ]
  have hv1 : 0.96 * (2 + Real.cos φ) ≤ v := by rw [hv]; nlinarith [hrpos, hsinθ]
  have hw1 : 0.39835 * (2 + Real.cos φ) ≤ w := by
    have h : 97 * w = 8*u + 39*v := by linarith
    nlinarith [h, hu1, hv1, hrpos]
  have hmain : (49/100)*(0.15*(2+Real.cos φ)) + (31/25)*(0.96*(2+Real.cos φ))
      + (59/100)*(0.39835*(2+Real.cos φ)) ≤
      (49/100)*u + (31/25)*v + (59/100)*w := by
    have h2 : (59/100)*(0.39835*(2+Real.cos φ)) ≤ (59/100)*w := by
      apply mul_le_mul_of_nonneg_left hw1 (by norm_num)
    have h3 : (49/100)*(0.15*(2+Real.cos φ)) ≤ (49/100)*u := by
      apply mul_le_mul_of_nonneg_left hu1 (by norm_num)
    have h4 : (31/25)*(0.96*(2+Real.cos φ)) ≤ (31/25)*v := by
      apply mul_le_mul_of_nonneg_left hv1 (by norm_num)
    linarith
  have hfin : (49/100)*(0.15*(2+Real.cos φ)) + (31/25)*(0.96*(2+Real.cos φ))
      + (59/100)*(0.39835*(2+Real.cos φ)) ≥ (7:ℝ)/5 := by
    nlinarith [hr1]
  linarith [hmain, hfin]

/-! ## The window -/

abbrev Ptorus : Work.CoreTopology.ParamTorus := Work.Smooth.Morse.torus dropDiffeo

abbrev Sigma : Set R3 := Work.BoxShrink.Core.sliceRegion Ptorus dropS dropC dropCyc dropU

def tLo : ℝ := -4.87
def tHi : ℝ := 1.32
def pLo : ℝ := -0.9
def pHi : ℝ := 5.03

theorem wθ : tHi - tLo < 2 * Real.pi := by norm_num [tHi, tLo]; linarith [Real.pi_gt_d2]
theorem wφ : pHi - pLo < 2 * Real.pi := by norm_num [pHi, pLo]; linarith [Real.pi_gt_d2]

def W (k l : ℤ) : Set (ℝ × ℝ) :=
  Set.Ioo (tLo + (k : ℝ) * (2 * Real.pi)) (tHi + (k : ℝ) * (2 * Real.pi)) ×ˢ
  Set.Ioo (pLo + (l : ℝ) * (2 * Real.pi)) (pHi + (l : ℝ) * (2 * Real.pi))

def Wfam : Set (Set (ℝ × ℝ)) := {S | ∃ k l : ℤ, S = W k l}

/-! ## Facts extracted from membership in the slice -/

theorem plane_of_mem {θ φ : ℝ} (h : dropVec (Work.Core.torusMap θ φ) ∈ Sigma) :
    -8 * (Work.Core.torusMap θ φ).ofLp 0 - 39 * (Work.Core.torusMap θ φ).ofLp 1
      + 97 * (Work.Core.torusMap θ φ).ofLp 2 = 0 := by
  obtain ⟨-, -, hpl⟩ := (Work.BoxShrink.Core.mem_sliceRegion).mp h
  have h0 : (dropVec (Work.Core.torusMap θ φ)).ofLp 0 = 0 := by
    have hc : dropCyc (2 : Fin 3) = (0 : Fin 3) := by decide
    rw [hc] at hpl
    simpa [dropC, dropU] using hpl
  rw [dvc0] at h0
  linarith

theorem box_of_mem {θ φ : ℝ} (h : dropVec (Work.Core.torusMap θ φ) ∈ Sigma) :
    |(dropVec (Work.Core.torusMap θ φ)).ofLp 2| < 7/5 := by
  obtain ⟨-, hbox, -⟩ := (Work.BoxShrink.Core.mem_sliceRegion).mp h
  have h2 := (Submission.mem_PBox).mp hbox (0 : Fin 3)
  have hc : dropCyc (0 : Fin 3) = (2 : Fin 3) := by decide
  rw [hc, Submission.boxSide_zero, dropS, one_mul] at h2
  have hc2 : dropC.ofLp (2 : Fin 3) = 0 := by simp [dropC]
  rw [hc2] at h2
  simpa using h2

theorem tm_shift (θ φ : ℝ) (k : ℤ) :
    Work.Core.torusMap (θ - (k : ℝ) * (2 * Real.pi)) φ = Work.Core.torusMap θ φ := by
  rw [Work.Core.torusMap_eq_iff]
  exact ⟨⟨-k, by push_cast; ring⟩, ⟨0, by ring⟩⟩

/-! ## Shifting to a representative -/

theorem tm_shift2 (θ φ : ℝ) (l : ℤ) :
    Work.Core.torusMap θ (φ - (l : ℝ) * (2 * Real.pi)) = Work.Core.torusMap θ φ := by
  rw [Work.Core.torusMap_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨-l, by push_cast; ring⟩⟩

theorem exists_shift_mem_Ico (x a : ℝ) :
    ∃ k : ℤ, x - (k : ℝ) * (2 * Real.pi) ∈ Set.Ico a (a + 2 * Real.pi) := by
  refine ⟨⌊(x - a) / (2 * Real.pi)⌋, ?_, ?_⟩
  · have ht : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := Int.floor_le ((x - a) / (2 * Real.pi))
    rw [le_div_iff₀ ht] at h
    show a ≤ x - (⌊(x - a) / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi)
    linarith
  · have ht : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := Int.lt_floor_add_one ((x - a) / (2 * Real.pi))
    rw [div_lt_iff₀ ht] at h
    show x - (⌊(x - a) / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi) < a + 2 * Real.pi
    push_cast at h ⊢
    linarith

theorem exists_shift_mem_Icc_of_not_mem_Ioo {a b x : ℝ} (hba : b < a + 2 * Real.pi)
    (h : ∀ k : ℤ, x - (k : ℝ) * (2 * Real.pi) ∉ Set.Ioo a b) :
    ∃ k : ℤ, x - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc b (a + 2 * Real.pi) := by
  obtain ⟨k, hk1, hk2⟩ := exists_shift_mem_Ico x b
  have hshift : ∀ j : ℤ, x - ((k + j : ℤ) : ℝ) * (2 * Real.pi)
      = x - (k : ℝ) * (2 * Real.pi) - (j : ℝ) * (2 * Real.pi) := by
    intro j; push_cast; ring
  rcases lt_or_ge (x - (k : ℝ) * (2 * Real.pi)) (a + 2 * Real.pi) with hlt | hge
  · exact ⟨k, hk1, hlt.le⟩
  · have hlo : a ≤ x - (k : ℝ) * (2 * Real.pi) - 2 * Real.pi := by linarith
    have hhi : x - (k : ℝ) * (2 * Real.pi) - 2 * Real.pi < b := by linarith
    have heq : x - (k : ℝ) * (2 * Real.pi) - 2 * Real.pi = a := by
      rcases lt_or_eq_of_le hlo with hlt2 | heq2
      · exfalso
        have hmem : x - ((k + 1 : ℤ) : ℝ) * (2 * Real.pi) ∈ Set.Ioo a b := by
          rw [hshift 1]; simp only [Int.cast_one, one_mul]; exact ⟨hlt2, hhi⟩
        exact h (k+1) hmem
      · exact heq2.symm
    exact ⟨k, by linarith, by linarith⟩

theorem psi_eq (θ φ : ℝ) :
    Ptorus.psi θ φ = dropVec (Work.Core.torusMap θ φ) := by
  rw [Work.Smooth.Morse.torus_psi, param_dropDiffeo]

theorem slice_phi_shift {θ φ : ℝ} (h : dropVec (Work.Core.torusMap θ φ) ∈ Sigma) :
    ∃ l : ℤ, φ - (l : ℝ) * (2 * Real.pi) ∈ Set.Ioo pLo pHi := by
  by_contra hcon
  push Not at hcon
  have hba : pHi < pLo + 2 * Real.pi := by norm_num [pHi, pLo]; linarith [Real.pi_gt_d2]
  obtain ⟨l, hl⟩ := exists_shift_mem_Icc_of_not_mem_Ioo hba hcon
  set φ' := φ - (l : ℝ) * (2 * Real.pi) with hφ'
  have hmem : dropVec (Work.Core.torusMap θ φ') ∈ Sigma := by
    rw [hφ', tm_shift2]; exact h
  have hpl := plane_of_mem hmem
  have hw : (Work.Core.torusMap θ φ').ofLp 2 = Real.sin φ' :=
    Work.CoreTopology.torusMap_apply_two θ φ'
  have hnorm : (Work.Core.torusMap θ φ').ofLp 0 ^ 2 + (Work.Core.torusMap θ φ').ofLp 1 ^ 2
      = (2 + Real.cos φ') ^ 2 := by
    rw [Work.CoreTopology.torusMap_apply_zero, Work.CoreTopology.torusMap_apply_one]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hl1 : (503:ℝ)/100 ≤ φ' := by have := hl.1; norm_num [pHi] at this; exact this
  have hl2 : φ' ≤ 2 * Real.pi - 9/10 := by have := hl.2; norm_num [pLo] at this; linarith
  have hzbig := factA hpl hnorm hw hl1 hl2
  have hzbox := box_of_mem hmem
  rw [dvc2] at hzbox
  have hb := (abs_lt.mp hzbox).2
  linarith [hzbig, hb]

theorem slice_theta_shift {θ φ : ℝ} (h : dropVec (Work.Core.torusMap θ φ) ∈ Sigma) :
    ∃ k : ℤ, θ - (k : ℝ) * (2 * Real.pi) ∈ Set.Ioo tLo tHi := by
  by_contra hcon
  push Not at hcon
  have hba : tHi < tLo + 2 * Real.pi := by norm_num [tHi, tLo]; linarith [Real.pi_gt_d2]
  obtain ⟨k, hk⟩ := exists_shift_mem_Icc_of_not_mem_Ioo hba hcon
  set θ' := θ - (k : ℝ) * (2 * Real.pi) with hθ'
  have hmem : dropVec (Work.Core.torusMap θ' φ) ∈ Sigma := by
    rw [hθ', tm_shift]; exact h
  have hpl := plane_of_mem hmem
  have hu : (Work.Core.torusMap θ' φ).ofLp 0 = (2 + Real.cos φ) * Real.cos θ' :=
    Work.CoreTopology.torusMap_apply_zero θ' φ
  have hv : (Work.Core.torusMap θ' φ).ofLp 1 = (2 + Real.cos φ) * Real.sin θ' :=
    Work.CoreTopology.torusMap_apply_one θ' φ
  have hk1 : (33:ℝ)/25 ≤ θ' := by have := hk.1; norm_num [tHi] at this; exact this
  have hk2 : θ' ≤ 1.4132 := by
    have := hk.2
    have hp : tLo + 2 * Real.pi ≤ 1.4132 := by norm_num [tLo]; linarith [Real.pi_lt_d20]
    linarith
  have hzbig := factB (u := (Work.Core.torusMap θ' φ).ofLp 0)
    (v := (Work.Core.torusMap θ' φ).ofLp 1) (w := (Work.Core.torusMap θ' φ).ofLp 2)
    hpl hu hv hk1 hk2
  have hzbox := box_of_mem hmem
  rw [dvc2] at hzbox
  have hb := (abs_lt.mp hzbox).2
  linarith [hzbig, hb]

/-! ## The windows -/

theorem isWindow_W (k l : ℤ) : Work.BoxShrink.Pinch.IsWindow (W k l) := by
  refine Work.BoxShrink.Pinch.isWindow_Ioo ?_ ?_
  · have h : tHi + (k:ℝ) * (2*Real.pi) - (tLo + (k:ℝ) * (2*Real.pi)) = tHi - tLo := by ring
    rw [h]; exact wθ
  · have h : pHi + (l:ℝ) * (2*Real.pi) - (pLo + (l:ℝ) * (2*Real.pi)) = pHi - pLo := by ring
    rw [h]; exact wφ

theorem isOpen_W (k l : ℤ) : IsOpen (W k l) := by
  simp only [W]; exact isOpen_Ioo.prod isOpen_Ioo

theorem W_inter_eq {k l k' l' : ℤ} (h : (W k l ∩ W k' l').Nonempty) : k = k' ∧ l = l' := by
  obtain ⟨p, hp, hp'⟩ := h
  simp only [W, Set.mem_prod, Set.mem_Ioo] at hp hp'
  have keyθ : ∀ a b : ℤ, tLo + (a:ℝ)*(2*Real.pi) < p.1 →
      p.1 < tHi + (a:ℝ)*(2*Real.pi) →
      tLo + (b:ℝ)*(2*Real.pi) < p.1 → p.1 < tHi + (b:ℝ)*(2*Real.pi) → a = b := by
    intro a b ha1 ha2 hb1 hb2
    by_contra hne
    have h2 : tHi < tLo + 2*Real.pi := by linarith [wθ]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh : a + 1 ≤ b := Int.add_one_le_iff.mpr hlt
      have h1 : ((a+1:ℤ):ℝ) ≤ (b:ℝ) := by exact_mod_cast hh
      push_cast at h1
      have hbig : tHi + (a:ℝ)*(2*Real.pi) < tLo + (b:ℝ)*(2*Real.pi) := by nlinarith [h2, h1]
      linarith
    · have hh : b + 1 ≤ a := Int.add_one_le_iff.mpr hlt
      have h1 : ((b+1:ℤ):ℝ) ≤ (a:ℝ) := by exact_mod_cast hh
      push_cast at h1
      have hbig : tHi + (b:ℝ)*(2*Real.pi) < tLo + (a:ℝ)*(2*Real.pi) := by nlinarith [h2, h1]
      linarith
  have keyφ : ∀ a b : ℤ, pLo + (a:ℝ)*(2*Real.pi) < p.2 →
      p.2 < pHi + (a:ℝ)*(2*Real.pi) →
      pLo + (b:ℝ)*(2*Real.pi) < p.2 → p.2 < pHi + (b:ℝ)*(2*Real.pi) → a = b := by
    intro a b ha1 ha2 hb1 hb2
    by_contra hne
    have h2 : pHi < pLo + 2*Real.pi := by linarith [wφ]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh : a + 1 ≤ b := Int.add_one_le_iff.mpr hlt
      have h1 : ((a+1:ℤ):ℝ) ≤ (b:ℝ) := by exact_mod_cast hh
      push_cast at h1
      have hbig : pHi + (a:ℝ)*(2*Real.pi) < pLo + (b:ℝ)*(2*Real.pi) := by nlinarith [h2, h1]
      linarith
    · have hh : b + 1 ≤ a := Int.add_one_le_iff.mpr hlt
      have h1 : ((b+1:ℤ):ℝ) ≤ (a:ℝ) := by exact_mod_cast hh
      push_cast at h1
      have hbig : pHi + (b:ℝ)*(2*Real.pi) < pLo + (a:ℝ)*(2*Real.pi) := by nlinarith [h2, h1]
      linarith
  exact ⟨keyθ k k' hp.1.1 hp.1.2 hp'.1.1 hp'.1.2, keyφ l l' hp.2.1 hp.2.2 hp'.2.1 hp'.2.2⟩

theorem hdisj : Wfam.Pairwise Disjoint := by
  intro S hS S' hS' hne
  obtain ⟨k, l, rfl⟩ := hS
  obtain ⟨k', l', rfl⟩ := hS'
  rw [Set.disjoint_left]
  intro p hp hp'
  have h := W_inter_eq ⟨p, hp, hp'⟩
  exact hne (by rw [h.1, h.2])

theorem hcov : Work.BoxShrink.Pinch.planePreimage Ptorus Sigma ⊆ ⋃₀ Wfam := by
  intro p hp
  rw [Work.BoxShrink.Pinch.mem_planePreimage] at hp
  have hp' : dropVec (Work.Core.torusMap p.1 p.2) ∈ Sigma := by
    rw [psi_eq] at hp; exact hp
  obtain ⟨k, hk⟩ := slice_theta_shift hp'
  obtain ⟨l, hl⟩ := slice_phi_shift hp'
  refine Set.mem_sUnion.mpr ⟨W k l, ⟨k, l, rfl⟩, ?_⟩
  simp only [W, Set.mem_prod, Set.mem_Ioo]
  exact ⟨⟨by linarith [hk.1], by linarith [hk.2]⟩, ⟨by linarith [hl.1], by linarith [hl.2]⟩⟩

theorem sigma_inessential_drop_aux :
    ¬ Ptorus.ContainsEssentialLoop Sigma := by
  refine Work.BoxShrink.Pinch.not_containsEssentialLoop_of_disjoint_windows Sigma Wfam ?_ ?_ ?_ hcov
  · intro S hS; obtain ⟨k, l, rfl⟩ := hS; exact isWindow_W k l
  · intro S hS; obtain ⟨k, l, rfl⟩ := hS; exact isOpen_W k l
  · exact hdisj

theorem sigma_inessential_drop :
    ¬ (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion
        (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo)
        Work.BoxShrink.PinchOff.RefuteDrop.dropS
        Work.BoxShrink.PinchOff.RefuteDrop.dropC
        Work.BoxShrink.PinchOff.RefuteDrop.dropCyc
        Work.BoxShrink.PinchOff.RefuteDrop.dropU) :=
  sigma_inessential_drop_aux

end
end Work.BoxShrink.PinchOff.RefuteDrop
