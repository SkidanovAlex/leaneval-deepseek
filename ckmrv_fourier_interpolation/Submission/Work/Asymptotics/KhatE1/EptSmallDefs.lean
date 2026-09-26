import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs

/-!
# `IsSmall`: exponential-order bounds with polynomial `scale` loss

`IsSmall f n` says `f = O((scale τ)^N · ‖Ept τ‖^n)` on `{Im τ ≥ 1}`, where
`Ept τ = e^{πiτ}` and `scale τ = 1 + (Im τ)⁻¹ + ‖τ‖`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- `f = O((scale τ)^N · ‖Ept τ‖^n)` for `Im τ ≥ 1`. -/
def IsSmall (f : UpperHalfPlane → ℂ) (n : ℕ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
    ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n

lemma norm_Ept_le_one (τ : UpperHalfPlane) : ‖Work.Residues.Ept τ‖ ≤ 1 :=
  (Work.Residues.norm_Ept_lt_one τ).le

lemma rpow_nonneg' (τ : UpperHalfPlane) (N : ℝ) : 0 ≤ (Work.Kernels.scale τ) ^ N :=
  Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N

lemma ept_pow_nonneg (τ : UpperHalfPlane) (n : ℕ) : 0 ≤ ‖Work.Residues.Ept τ‖ ^ n :=
  pow_nonneg (norm_nonneg _) n

/-- `0 ≤ C * scale^N * ‖Ept‖^n` for `0 ≤ C`. -/
lemma nonneg_Cscale (τ : UpperHalfPlane) (C : ℝ) (N : ℝ) (n : ℕ) (hC : 0 ≤ C) :
    (0:ℝ) ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n :=
  mul_nonneg (mul_nonneg hC (rpow_nonneg' τ N)) (ept_pow_nonneg τ n)

/-- `0 ≤ C * scale^N`. -/
lemma nonneg_Cscale' (τ : UpperHalfPlane) (C : ℝ) (N : ℝ) (hC : 0 ≤ C) :
    (0:ℝ) ≤ C * (Work.Kernels.scale τ) ^ N :=
  mul_nonneg hC (rpow_nonneg' τ N)

lemma IsSmall.mono {f : UpperHalfPlane → ℂ} {m n : ℕ} (h : IsSmall f m) (hmn : n ≤ m) :
    IsSmall f n := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have hle : ‖Work.Residues.Ept τ‖ ^ m ≤ ‖Work.Residues.Ept τ‖ ^ n :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_Ept_le_one τ) hmn
  exact le_trans (hb τ hτ) (mul_le_mul_of_nonneg_left hle (nonneg_Cscale' τ C N hC.le))

lemma IsSmall.add {f g : UpperHalfPlane → ℂ} {m n : ℕ} (hf : IsSmall f m) (hg : IsSmall g n) :
    IsSmall (fun τ => f τ + g τ) (min m n) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hg
  refine ⟨C1 + C2 + 1, max N1 N2, by linarith, le_trans hN1 (le_max_left _ _), fun τ hτ => ?_⟩
  have hN1' : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_left _ _)
  have hN2' : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_right _ _)
  have hm1 : ‖Work.Residues.Ept τ‖ ^ m ≤ ‖Work.Residues.Ept τ‖ ^ min m n :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_Ept_le_one τ) (min_le_left _ _)
  have hn1 : ‖Work.Residues.Ept τ‖ ^ n ≤ ‖Work.Residues.Ept τ‖ ^ min m n :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_Ept_le_one τ) (min_le_right _ _)
  have hb1' : ‖f τ‖ ≤ C1 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n := by
    refine le_trans (hb1 τ hτ) ?_
    calc C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Residues.Ept τ‖ ^ m
        ≤ C1 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN1' hC1.le) (ept_pow_nonneg τ m)
      _ ≤ C1 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n :=
          mul_le_mul_of_nonneg_left hm1 (nonneg_Cscale' τ C1 _ hC1.le)
  have hb2' : ‖g τ‖ ≤ C2 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n := by
    refine le_trans (hb2 τ hτ) ?_
    calc C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Residues.Ept τ‖ ^ n
        ≤ C2 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2' hC2.le) (ept_pow_nonneg τ n)
      _ ≤ C2 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n :=
          mul_le_mul_of_nonneg_left hn1 (nonneg_Cscale' τ C2 _ hC2.le)
  have h0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n :=
    mul_nonneg (rpow_nonneg' τ _) (ept_pow_nonneg τ _)
  have h2 : ‖f τ‖ + ‖g τ‖
      ≤ (C1 + C2) * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n := by
    refine le_trans (add_le_add hb1' hb2') ?_
    rw [show C1 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n
          + C2 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n
        = (C1 + C2) * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n from by ring]
  have h3 : (C1 + C2) * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n
      ≤ (C1 + C2 + 1) * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Residues.Ept τ‖ ^ min m n := by
    nlinarith [h0]
  linarith [norm_add_le (f τ) (g τ), h2, h3]

lemma IsSmall.congr {f g : UpperHalfPlane → ℂ} {n : ℕ} (h : IsSmall f n)
    (hfg : ∀ τ, f τ = g τ) : IsSmall g n := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  exact ⟨C, N, hC, hN, fun τ hτ => by rw [← hfg τ]; exact hb τ hτ⟩

lemma IsSmall.neg {f : UpperHalfPlane → ℂ} {n : ℕ} (hf : IsSmall f n) :
    IsSmall (fun τ => -f τ) n := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ hτ => by simpa using hb τ hτ⟩

lemma IsSmall.sub {f g : UpperHalfPlane → ℂ} {m n : ℕ} (hf : IsSmall f m) (hg : IsSmall g n) :
    IsSmall (fun τ => f τ - g τ) (min m n) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma IsSmall.const_mul (c : ℂ) {f : UpperHalfPlane → ℂ} {n : ℕ} (hf : IsSmall f n) :
    IsSmall (fun τ => c * f τ) n := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  refine ⟨‖c‖ * C + 1, N, by positivity, hN, fun τ hτ => ?_⟩
  have h0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n :=
    mul_nonneg (rpow_nonneg' τ N) (ept_pow_nonneg τ n)
  have h1 : ‖c‖ * ‖f τ‖ ≤ ‖c‖ * (C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n) :=
    mul_le_mul_of_nonneg_left (hb τ hτ) (norm_nonneg _)
  have h2 : ‖c‖ * (C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n)
      = ‖c‖ * C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n := by ring
  have h3 : ‖c‖ * C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n
      ≤ (‖c‖ * C + 1) * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n := by
    have h4 : (0:ℝ) ≤ ‖c‖ * C + 1 := by positivity
    nlinarith [h0, hC, norm_nonneg c, h4]
  rw [norm_mul]
  calc ‖c‖ * ‖f τ‖ ≤ ‖c‖ * (C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n) := h1
    _ = ‖c‖ * C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n := h2
    _ ≤ (‖c‖ * C + 1) * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ n := h3

lemma IsSmall.mul {f g : UpperHalfPlane → ℂ} {m n : ℕ} (hf : IsSmall f m) (hg : IsSmall g n) :
    IsSmall (fun τ => f τ * g τ) (m + n) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hg
  refine ⟨C1 * C2 + 1, N1 + N2, by nlinarith [hC1, hC2], add_nonneg hN1 hN2, fun τ hτ => ?_⟩
  have hsp : (Work.Kernels.scale τ) ^ (N1 + N2)
      = (Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N2 :=
    Real.rpow_add (Work.Kernels.scale_pos τ) N1 N2
  have hmul := mul_le_mul (hb1 τ hτ) (hb2 τ hτ) (norm_nonneg _)
    (nonneg_Cscale τ C1 N1 m hC1.le)
  have hp : ‖Work.Residues.Ept τ‖ ^ (m + n)
      = ‖Work.Residues.Ept τ‖ ^ m * ‖Work.Residues.Ept τ‖ ^ n := pow_add _ _ _
  have hEq : C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Residues.Ept τ‖ ^ m
        * (C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Residues.Ept τ‖ ^ n)
      = C1 * C2 * ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N2)
          * ‖Work.Residues.Ept τ‖ ^ (m + n) := by
    rw [hp]; ring
  have h0' : (0:ℝ) ≤ ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N2)
      * ‖Work.Residues.Ept τ‖ ^ (m + n) :=
    mul_nonneg (mul_nonneg (rpow_nonneg' τ N1) (rpow_nonneg' τ N2)) (ept_pow_nonneg τ _)
  have hfin : C1 * C2 * ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N2)
        * ‖Work.Residues.Ept τ‖ ^ (m + n)
      ≤ (C1 * C2 + 1) * ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N2)
        * ‖Work.Residues.Ept τ‖ ^ (m + n) := by
    nlinarith [h0', hC1, hC2]
  rw [norm_mul, hsp]
  refine le_trans hmul ?_
  rw [hEq]
  exact hfin

/-- `IsSmall` from a plain `scale`-polynomial bound. -/
lemma IsSmall.of_bdd {f : UpperHalfPlane → ℂ} {C N : ℝ} (hC : 0 < C) (hN : 0 ≤ N)
    (hb : ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) :
    IsSmall f 0 := by
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  simpa using hb τ hτ

lemma isSmall_ept : IsSmall Work.Residues.Ept 1 := by
  refine ⟨1, 0, one_pos, le_rfl, fun τ _ => ?_⟩
  simp

lemma ept_sq_apply (τ : UpperHalfPlane) :
    Work.Residues.Ept τ ^ 2 = Work.Kernels.qParamFun τ := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma isSmall_qParam : IsSmall Work.Kernels.qParamFun 2 := by
  have h := isSmall_ept.mul (f := Work.Residues.Ept) (g := Work.Residues.Ept) isSmall_ept
  have hfun : (fun τ : UpperHalfPlane => Work.Residues.Ept τ * Work.Residues.Ept τ)
      = Work.Kernels.qParamFun := by
    funext τ; rw [← sq, ept_sq_apply]
  rwa [hfun] at h

lemma norm_qParamFun_eq (τ : UpperHalfPlane) :
    ‖Work.Kernels.qParamFun τ‖ = ‖Work.Residues.Ept τ‖ ^ 2 := by
  rw [← ept_sq_apply τ, norm_pow]

lemma IsSmall.const (c : ℂ) : IsSmall (fun _ : UpperHalfPlane => c) 0 := by
  refine IsSmall.of_bdd (C := ‖c‖ + 1) (N := 0) (by positivity) le_rfl (fun τ _ => ?_)
  rw [Real.rpow_zero, mul_one]
  linarith [norm_nonneg c]

lemma IsSmall.one : IsSmall (fun _ : UpperHalfPlane => (1:ℂ)) 0 :=
  IsSmall.const 1

lemma IsSmall.zero (n : ℕ) : IsSmall (fun _ : UpperHalfPlane => (0:ℂ)) n := by
  refine ⟨1, 0, one_pos, le_rfl, fun τ _ => ?_⟩
  simp

lemma IsSmall.sum {ι : Type*} (s : Finset ι) {f : ι → UpperHalfPlane → ℂ} {n : ℕ}
    (h : ∀ i ∈ s, IsSmall (f i) n) : IsSmall (fun τ => ∑ i ∈ s, f i τ) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, 0, one_pos, le_rfl, fun τ _ => ?_⟩
      simp
  | insert a s ha ih =>
      have ha' := h a (Finset.mem_insert_self a s)
      have hs' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hh := ha'.add hs'
      have h1 : (fun τ => ∑ i ∈ insert a s, f i τ)
          = fun τ => f a τ + ∑ i ∈ s, f i τ := by
        funext τ; exact Finset.sum_insert ha
      rw [h1]
      exact hh.mono (by simp)

/-- `IsSmall.mono` with the target exponent as an explicit argument. -/
lemma IsSmall.mono_of {f : UpperHalfPlane → ℂ} {m : ℕ} (h : IsSmall f m) (n : ℕ)
    (hn : n ≤ m) : IsSmall f n := h.mono hn

lemma IsSmall.pow {f : UpperHalfPlane → ℂ} {m : ℕ} (hf : IsSmall f m) (k : ℕ) :
    IsSmall (fun τ => f τ ^ k) (m * k) := by
  induction k with
  | zero =>
      refine (IsSmall.one).congr (fun τ => ?_)
      simp
  | succ k ih =>
      have h := ih.mul hf
      have h1 : m * k + m = m * (k + 1) := by ring
      rw [h1] at h
      exact h.congr (fun τ => by rw [pow_succ])

/-- Multiplication by a function bounded by `C (scale τ)^N`. -/
lemma IsSmall.bdd_mul {f g : UpperHalfPlane → ℂ} {n : ℕ} {C N : ℝ} (hC : 0 < C) (hN : 0 ≤ N)
    (hg : ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖g τ‖ ≤ C * (Work.Kernels.scale τ) ^ N)
    (hf : IsSmall f n) : IsSmall (fun τ => f τ * g τ) n := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hf
  refine ⟨(C1 * C + 1), N1 + N, by nlinarith [hC1, hC], add_nonneg hN1 hN, fun τ hτ => ?_⟩
  have hsp : (Work.Kernels.scale τ) ^ (N1 + N)
      = (Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N :=
    Real.rpow_add (Work.Kernels.scale_pos τ) N1 N
  have hmul := mul_le_mul (hb1 τ hτ) (hg τ hτ) (norm_nonneg _) (nonneg_Cscale τ C1 N1 n hC1.le)
  have hEq : C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Residues.Ept τ‖ ^ n
        * (C * (Work.Kernels.scale τ) ^ N)
      = C1 * C * ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N)
          * ‖Work.Residues.Ept τ‖ ^ n := by ring
  have h0' : (0:ℝ) ≤ ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N)
      * ‖Work.Residues.Ept τ‖ ^ n :=
    mul_nonneg (mul_nonneg (rpow_nonneg' τ N1) (rpow_nonneg' τ N)) (ept_pow_nonneg τ n)
  have hfin : C1 * C * ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N)
        * ‖Work.Residues.Ept τ‖ ^ n
      ≤ (C1 * C + 1) * ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N)
        * ‖Work.Residues.Ept τ‖ ^ n := by
    nlinarith [h0', hC1, hC]
  rw [norm_mul, hsp]
  refine le_trans hmul ?_
  rw [hEq]
  exact hfin

end

end Work.Asymptotics.KhatE1
