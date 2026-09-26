import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.E_jdiff_large
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Tile.HalfDev24Defs

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels

noncomputable section

namespace Tile

namespace H24

set_option maxHeartbeats 1000000

/-! ## The sharp divisor lower bound on the contour `z = i t` -/

lemma exp_neg_two_pi_le_half : Real.exp (-(2 * Real.pi)) ≤ 1 / 2 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (2 : ℝ) ≤ (Real.exp 1) ^ 6 := by
    have h3 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 6
    have h4 : (2 : ℝ) ≤ (2.7 : ℝ) ^ 6 := by norm_num
    linarith
  have h5 : (Real.exp 1) ^ 6 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h7 : (2 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have h8 := Real.exp_le_exp.mpr h6
    rw [h5] at h2
    linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h7


lemma one_sub_exp_ge_half {w : UpperHalfPlane} {t : ℝ} (hw : w ∈ Work.Asymptotics.KEpsilon)
    (htle : t ≤ (ModularGroup.S • w).im - 1) :
    (1 : ℝ) / 2 ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I)))‖ := by
  set Z : ℂ := Complex.exp (2 * Real.pi * Complex.I *
    ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I))) with hZdef
  have hnorm : ‖Z‖ = Real.exp (-(2 * Real.pi * ((ModularGroup.S • w).im - t))) := by
    rw [hZdef, Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re]
    norm_num
    try ring
  have hle : ‖Z‖ ≤ Real.exp (-(2 * Real.pi)) := by
    rw [hnorm]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htle])
  have hsub := norm_sub_norm_le (1 : ℂ) Z
  rw [norm_one, hnorm] at hsub
  linarith [exp_neg_two_pi_le_half]

/-! ## The sharp divisor bound at the contour point `z = i t` -/

lemma divisor_lower_sharp :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ Work.Asymptotics.KEpsilon → 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
      c * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t))
        ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
            (Work.Kernels.jInvariantFun w -
              Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
  obtain ⟨c₀, hc₀, hJ⟩ := Work.Asymptotics.E_jdiff_large
  refine ⟨c₀ / 4, by positivity, fun w t ht hw ht1 htle => ?_⟩
  have hΔ : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤
      ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
  have hZ := one_sub_exp_ge_half hw htle
  have hJ' : c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2) ≤
      ‖Work.Kernels.jInvariantFun w -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
    have h := hJ w t ht hw ht1
    have hc : (0 : ℝ) ≤ c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by positivity
    calc c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2)
        ≤ c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) *
            ‖1 - Complex.exp (2 * Real.pi * Complex.I *
              ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I)))‖ :=
          mul_le_mul_of_nonneg_left hZ hc
      _ ≤ ‖Work.Kernels.jInvariantFun w -
            Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := h
  have hprod := mul_le_mul hΔ hJ' (by positivity) (by positivity)
  rw [norm_mul]
  have hexp : (1 / 2 * Real.exp (-(2 * Real.pi * t))) *
        (c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2))
      = c₀ / 4 * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) := by
    have h : Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        = Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← h]; ring
  rw [← hexp]
  exact hprod


/-! ## The `τ`-atom bounds at the cusp-`±1` tiles -/

/-- Upgrade both the constant and the exponent of a bound of the shape `a s^n`. -/
lemma bound_upgrade {a b s : ℝ} {n n' : ℝ} (hs : 1 ≤ s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hnn : n ≤ n') : a * s ^ n ≤ b * s ^ n' := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have h1 : s ^ n ≤ s ^ n' := Real.rpow_le_rpow_of_exponent_le hs hnn
  calc a * s ^ n ≤ b * s ^ n :=
        mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hs0.le n)
    _ ≤ b * s ^ n' := mul_le_mul_of_nonneg_left h1 (le_trans ha hab)

/-- The `τ`-atoms `r0, r1, r2, R0` as `Bdd 0`-functions at the cusp-`±1` tiles. -/
lemma tileAtoms_bdd :
    (∀ (n : ℤ), (n = 1 ∨ n = -1) → EtailE.Bdd 0 (fun w : ℍ => K24F.r0 ((n : ℝ) +ᵥ w))) ∧
    (∀ (n : ℤ), (n = 1 ∨ n = -1) → EtailE.Bdd 0 (fun w : ℍ => K24F.r1 ((n : ℝ) +ᵥ w))) ∧
    (∀ (n : ℤ), (n = 1 ∨ n = -1) → EtailE.Bdd 0 (fun w : ℍ => K24F.r2 ((n : ℝ) +ᵥ w))) ∧
    (∀ (n : ℤ), (n = 1 ∨ n = -1) → EtailE.Bdd 0 (fun w : ℍ => K24F.R0 ((n : ℝ) +ᵥ w))) := by
  have hphi1b : ∀ (n : ℤ), (n = 1 ∨ n = -1) →
      EtailE.Bdd 0 (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ) * E2Fun ((n : ℝ) +ᵥ w)
        - 3 * Complex.I / (Real.pi : ℂ)) :=
    fun n hn => EtailE.Bdd.sub (EtailE.Bdd.mul_zero (Bdd.vadd n hn) (Bdd.vadd_E2 n hn))
      (Bdd.const' (3 * Complex.I / (Real.pi : ℂ)))
  have hphi0 : ∀ (n : ℤ), (n = 1 ∨ n = -1) →
      EtailE.Bdd 0 (fun w : ℍ => Compact.phi1 ((n : ℝ) +ᵥ w)) :=
    fun n hn => EtailE.Bdd.congr (funext fun w => rfl) (hphi1b n hn)
  have hphi2b : ∀ (n : ℤ), (n = 1 ∨ n = -1) →
      EtailE.Bdd 0 (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ)
        * (E2Fun ((n : ℝ) +ᵥ w) * E2Fun ((n : ℝ) +ᵥ w))
        - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun ((n : ℝ) +ᵥ w)) :=
    fun n hn => EtailE.Bdd.sub
      (EtailE.Bdd.mul_zero (Bdd.vadd n hn)
        (EtailE.Bdd.mul_zero (Bdd.vadd_E2 n hn) (Bdd.vadd_E2 n hn)))
      (EtailE.Bdd.mul_zero (Bdd.const' (6 * Complex.I / (Real.pi : ℂ))) (Bdd.vadd_E2 n hn))
  have hphi2 : ∀ (n : ℤ), (n = 1 ∨ n = -1) →
      EtailE.Bdd 0 (fun w : ℍ => Compact.phi2t ((n : ℝ) +ᵥ w)) :=
    fun n hn => EtailE.Bdd.congr (funext fun w => by
      simp only [Compact.phi2t]
      ring) (hphi2b n hn)
  have hR0prod : ∀ (n : ℤ), (n = 1 ∨ n = -1) →
      EtailE.Bdd 0 (fun w : ℍ => Compact.phi1 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
        * E4Fun ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) :=
    fun n hn => EtailE.Bdd.mul_zero (EtailE.Bdd.mul_zero
      (EtailE.Bdd.mul_zero (hphi0 n hn) (Bdd.vadd_E4 n hn)) (Bdd.vadd_E4 n hn))
      (Bdd.vadd_E4 n hn)
  exact ⟨fun n hn => EtailE.Bdd.mul_zero (Bdd.vadd n hn) (Bdd.vadd_E14 n hn),
    fun n hn => EtailE.Bdd.mul_zero (hphi0 n hn) (Bdd.vadd_Delta n hn),
    fun n hn => EtailE.Bdd.mul_zero (hphi2 n hn) (Bdd.vadd_E10 n hn),
    fun n hn => EtailE.Bdd.congr (funext fun w => by
      simp only [K24F.R0]
      ring) (hR0prod n hn)⟩

/-- The atom bounds at the tile `1 +ᵥ w`. -/
theorem tileAtoms24_one : ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧ ∀ w : ℍ, w ∈ KEpsilon →
    TileAtoms24 (((1 : ℤ) : ℝ) +ᵥ w) (K * (scale w) ^ N)
      (K * (scale w) ^ N * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by
  obtain ⟨hA, hB, hC, hD⟩ := tileAtoms_bdd
  obtain ⟨K1, N1, hK1, hN1, b1⟩ := EtailE.Bdd.exists_bound_zero (hA 1 (Or.inl rfl))
  obtain ⟨K2, N2, hK2, hN2, b2⟩ := EtailE.Bdd.exists_bound_zero (hB 1 (Or.inl rfl))
  obtain ⟨K3, N3, hK3, hN3, b3⟩ := EtailE.Bdd.exists_bound_zero (hC 1 (Or.inl rfl))
  obtain ⟨K4, N4, hK4, hN4, b4⟩ := EtailE.Bdd.exists_bound_zero (hD 1 (Or.inl rfl))
  obtain ⟨Cj, Mj, hCj, hMj, bj⟩ :=
    Bdd.shift EtailE.E_bdd_j (fun τ => KernelFacts.jInvariantFun_vadd_one τ) 1 (Or.inl rfl)
  set KS : ℝ := K1 + K2 + K3 + K4 + Cj + 1 with hKS
  set NS : ℝ := N1 + N2 + N3 + N4 + Mj + 1 with hNS
  refine ⟨KS, NS, by rw [hKS]; positivity, by rw [hNS]; positivity, fun w hw => ?_⟩
  have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
  have hτ : (1 : ℝ) ≤ scale (((1 : ℤ) : ℝ) +ᵥ w) := one_le_scale _
  have e1 : K1 * (scale w) ^ N1 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K1) (b := KS) (n := N1) (n' := NS) hs1 hK1.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e2 : K2 * (scale w) ^ N2 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K2) (b := KS) (n := N2) (n' := NS) hs1 hK2.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e3 : K3 * (scale w) ^ N3 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K3) (b := KS) (n := N3) (n' := NS) hs1 hK3.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e4 : K4 * (scale w) ^ N4 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K4) (b := KS) (n := N4) (n' := NS) hs1 hK4.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e5 : Cj * (scale w) ^ Mj ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := Cj) (b := KS) (n := Mj) (n' := NS) hs1 hCj.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have g1 := le_trans (b1 w hw) e1
  have g2 := le_trans (b2 w hw) e2
  have g3 := le_trans (b3 w hw) e3
  have g4 := le_trans (b4 w hw) e4
  have g5 := le_trans (bj w hw) (mul_le_mul_of_nonneg_right e5 (Real.exp_nonneg _))
  exact ⟨le_trans g1 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g2 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g3 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g4 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g5 (le_mul_of_one_le_right (by positivity) hτ)⟩

/-- The atom bounds at the tile `-1 +ᵥ w`. -/
theorem tileAtoms24_neg_one : ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧ ∀ w : ℍ, w ∈ KEpsilon →
    TileAtoms24 (((-1 : ℤ) : ℝ) +ᵥ w) (K * (scale w) ^ N)
      (K * (scale w) ^ N * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by
  obtain ⟨hA, hB, hC, hD⟩ := tileAtoms_bdd
  obtain ⟨K1, N1, hK1, hN1, b1⟩ := EtailE.Bdd.exists_bound_zero (hA (-1) (Or.inr rfl))
  obtain ⟨K2, N2, hK2, hN2, b2⟩ := EtailE.Bdd.exists_bound_zero (hB (-1) (Or.inr rfl))
  obtain ⟨K3, N3, hK3, hN3, b3⟩ := EtailE.Bdd.exists_bound_zero (hC (-1) (Or.inr rfl))
  obtain ⟨K4, N4, hK4, hN4, b4⟩ := EtailE.Bdd.exists_bound_zero (hD (-1) (Or.inr rfl))
  obtain ⟨Cj, Mj, hCj, hMj, bj⟩ :=
    Bdd.shift EtailE.E_bdd_j (fun τ => KernelFacts.jInvariantFun_vadd_one τ) (-1) (Or.inr rfl)
  set KS : ℝ := K1 + K2 + K3 + K4 + Cj + 1 with hKS
  set NS : ℝ := N1 + N2 + N3 + N4 + Mj + 1 with hNS
  refine ⟨KS, NS, by rw [hKS]; positivity, by rw [hNS]; positivity, fun w hw => ?_⟩
  have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
  have hτ : (1 : ℝ) ≤ scale (((-1 : ℤ) : ℝ) +ᵥ w) := one_le_scale _
  have e1 : K1 * (scale w) ^ N1 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K1) (b := KS) (n := N1) (n' := NS) hs1 hK1.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e2 : K2 * (scale w) ^ N2 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K2) (b := KS) (n := N2) (n' := NS) hs1 hK2.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e3 : K3 * (scale w) ^ N3 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K3) (b := KS) (n := N3) (n' := NS) hs1 hK3.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e4 : K4 * (scale w) ^ N4 ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := K4) (b := KS) (n := N4) (n' := NS) hs1 hK4.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have e5 : Cj * (scale w) ^ Mj ≤ KS * (scale w) ^ NS :=
    bound_upgrade (a := Cj) (b := KS) (n := Mj) (n' := NS) hs1 hCj.le
      (by rw [hKS]; linarith) (by rw [hNS]; linarith)
  have g1 := le_trans (b1 w hw) e1
  have g2 := le_trans (b2 w hw) e2
  have g3 := le_trans (b3 w hw) e3
  have g4 := le_trans (b4 w hw) e4
  have g5 := le_trans (bj w hw) (mul_le_mul_of_nonneg_right e5 (Real.exp_nonneg _))
  exact ⟨le_trans g1 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g2 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g3 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g4 (le_mul_of_one_le_right (by positivity) hτ),
    le_trans g5 (le_mul_of_one_le_right (by positivity) hτ)⟩

/-- **The `τ`-atom bounds at `τ = n +ᵥ w`, `w ∈ E`, `n = ±1`.** -/
theorem tileAtoms24_axis : ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧
    ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
      TileAtoms24 ((n : ℝ) +ᵥ w) (K * (scale w) ^ N)
        (K * (scale w) ^ N * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by
  obtain ⟨K1, N1, hK1, hN1, b1⟩ := tileAtoms24_one
  obtain ⟨K2, N2, hK2, hN2, b2⟩ := tileAtoms24_neg_one
  refine ⟨K1 + K2 + 1, max N1 N2, by positivity, le_max_of_le_left hN1, ?_⟩
  intro w n hn hw
  have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
  have hE : (0 : ℝ) ≤ Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := Real.exp_nonneg _
  have hc1 : K1 * (scale w) ^ N1 ≤ (K1 + K2 + 1) * (scale w) ^ (max N1 N2) :=
    bound_upgrade (a := K1) (b := K1 + K2 + 1) (n := N1) (n' := max N1 N2) hs1 hK1.le
      (by linarith) (le_max_left _ _)
  have hc2 : K2 * (scale w) ^ N2 ≤ (K1 + K2 + 1) * (scale w) ^ (max N1 N2) :=
    bound_upgrade (a := K2) (b := K1 + K2 + 1) (n := N2) (n' := max N1 N2) hs1 hK2.le
      (by linarith) (le_max_right _ _)
  rcases hn with h | h
  · subst h
    exact (b1 w hw).mono hc1 (mul_le_mul_of_nonneg_right hc1 hE)
  · subst h
    exact (b2 w hw).mono hc2 (mul_le_mul_of_nonneg_right hc2 hE)

end H24

end Tile

end

end Work.Asymptotics
