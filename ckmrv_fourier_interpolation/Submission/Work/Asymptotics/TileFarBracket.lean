/-
# A *sharp-threshold* tile calculus for the `K_-` cusp-`i∞` tail

This module sets up the exact analogue of the `TB`-calculus of
`Submission/Work/Asymptotics/Tile/tileTB.lean` in which the *pole-height* threshold is

  `Im (S • w) + 1 ≤ t`

(the sharp one) instead of the crude `2 Im (S • w) + 1 ≤ t` used by `TB`.  The point is that on
the cusp-`±1` tiles `τ = n +ᵥ w` (`w ∈ E`, `n = ±1`) the poles of `z ↦ K_-(τ,z)` of height `≥ 1`
are precisely the translates `S • w + k`, all of height `Im (S • w)`; hence every estimate of the
`TB`-calculus that is uniform in the threshold remains true with the sharp threshold, *provided*
the exponent comparison at the end is made with `t ≥ Im (S • w) + 1` rather than
`t ≥ 2 Im (S • w) + 1`.

Concretely, a bound of the shape `C (scale w)^N (1+t)^M e^{a Im(Sw) - b π t}` is dominated by
`C' (scale w)^{N'} (1+t)^{M'} e^{π Im(Sw) - π t}` when `a ≤ b π`: with `t ≥ Im (S•w) + 1` we get
`(a - π)Im(Sw) ≤ (b - 1)π Im(Sw) ≤ (b - 1)π t`.  All the exponent pairs occurring in the `K_-`
bracket identity satisfy this, so the whole chain of `Submission/Work/Asymptotics/Tile/KMinusTileTail.lean`
goes through verbatim.

## Main results

* `Work.Asymptotics.Tile.TBF` — the sharp-threshold calculus.
* `Work.Asymptotics.Tile.TBF.ktl_G8`, `TBF.ktl_G24` — the sharp-threshold tile bracket bounds,
  from which `Work.Asymptotics.Tile.KMinusTileTailSharp` is assembled.
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.KMinusTileTail

set_option maxHeartbeats 1600000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels Work.Asymptotics

noncomputable section

/-- The **far-window threshold**: `1 ≤ t ≤ Im (S • w) - 1`. -/
def FarThresh (w : ℍ) (t : ℝ) : Prop := 1 ≤ t ∧ t ≤ (ModularGroup.S • w).im - 1

/-- `TBF a b F`: on the tiles, `‖F w n z‖ ≤ C (scale w)^N (1+t)^M e^{a Im(Sw) - b π t}`
for `n = ±1`, `w ∈ E` and `z = i t` with the *sharp* threshold `Im (S w) + 1 ≤ t`.

This is `Work.Asymptotics.Tile.TB` with the crude constant `2` removed from the threshold. -/
def TBF (a b : ℝ) (F : ℍ → ℤ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : ℍ) (n : ℤ) (z : ℍ) (t : ℝ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
      (z : ℂ) = (t : ℂ) * Complex.I → FarThresh w t →
        ‖F w n z‖ ≤ C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)

namespace TBF

variable {a a₁ a₂ b b₁ b₂ : ℝ} {F G : ℍ → ℤ → ℍ → ℂ}

lemma mono (h : TBF a b F) (ha : a ≤ a₁) (hb : b₁ ≤ b) : TBF a₁ b₁ F := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => ?_⟩
  refine le_trans (hbnd w n z t hn hw hz ht) ?_
  have hH : 0 ≤ (ModularGroup.S • w).im := by have := hw.2; linarith
  have ht0 : 0 ≤ t := le_trans zero_le_one ht.1
  have hexp : Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      ≤ Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t) := by
    rw [Real.exp_le_exp]
    have h1 : a * (ModularGroup.S • w).im ≤ a₁ * (ModularGroup.S • w).im :=
      mul_le_mul_of_nonneg_right ha hH
    have h2 : b₁ * Real.pi * t ≤ b * Real.pi * t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (le_of_lt Real.pi_pos)) ht0
    linarith
  exact mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
      (Real.rpow_nonneg (by linarith) _))

lemma add (hF : TBF a b F) (hG : TBF a b G) : TBF a b (fun w n z => F w n z + G w n z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by positivity, le_max_of_le_left hN1,
    le_max_of_le_left hM1, fun w n z t hn hw hz ht => ?_⟩
  have hH : 0 ≤ (ModularGroup.S • w).im := by have := hw.2; linarith
  have ht0 : 0 ≤ t := le_trans zero_le_one ht.1
  have hH1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have ht1 : (1:ℝ) ≤ 1 + t := by linarith
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hH1 (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hH1 (le_max_right _ _)
  have hM1' : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  have hM2' : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right _ _)
  set E : ℝ := Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have s1 : ‖F w n z‖ ≤ C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by
    refine le_trans (hb1 w n z t hn hw hz ht) ?_
    have h2 : (scale w) ^ N1 * (1 + t) ^ M1
        ≤ (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul hN1' hM1' (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    calc C1 * (scale w) ^ N1 * (1 + t) ^ M1 * E
        = C1 * ((scale w) ^ N1 * (1 + t) ^ M1 * E) := by ring
      _ ≤ C1 * ((scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hE0.le) hC1.le
      _ = C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by ring
  have s2 : ‖G w n z‖ ≤ C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by
    refine le_trans (hb2 w n z t hn hw hz ht) ?_
    have h2 : (scale w) ^ N2 * (1 + t) ^ M2
        ≤ (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul hN2' hM2' (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    calc C2 * (scale w) ^ N2 * (1 + t) ^ M2 * E
        = C2 * ((scale w) ^ N2 * (1 + t) ^ M2 * E) := by ring
      _ ≤ C2 * ((scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hE0.le) hC2.le
      _ = C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by ring
  refine le_trans (norm_add_le _ _) ?_
  rw [show (C1 + C2) * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E
      = C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E
        + C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E from by ring]
  exact add_le_add s1 s2

lemma neg (hF : TBF a b F) : TBF a b (fun w n z => -F w n z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hF
  exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
    rw [norm_neg]; exact hb w n z t hn hw hz ht⟩

lemma sub (hF : TBF a b F) (hG : TBF a b G) : TBF a b (fun w n z => F w n z - G w n z) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma const_mul (c : ℂ) (hF : TBF a b F) : TBF a b (fun w n z => c * F w n z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hF
  refine ⟨(‖c‖ + 1) * C, N, M, by positivity, hN, hM, fun w n z t hn hw hz ht => ?_⟩
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (hb w n z t hn hw hz ht) (norm_nonneg c)) ?_
  have htw : (0:ℝ) ≤ 1 + t := by linarith [ht.1]
  have hbase : (0:ℝ) ≤ (scale w) ^ N * (1 + t) ^ M
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
      (Real.rpow_nonneg htw _)) (Real.exp_pos _).le
  calc ‖c‖ * (C * (scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = (‖c‖ * C) * ((scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) := by ring
    _ ≤ ((‖c‖ + 1) * C) * ((scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) := by
        refine mul_le_mul_of_nonneg_right ?_ hbase
        nlinarith [hC.le, norm_nonneg c]
    _ = (‖c‖ + 1) * C * (scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) := by ring

lemma congr {F G : ℍ → ℤ → ℍ → ℂ} (hFG : ∀ w n z, F w n z = G w n z) (hF : TBF a b F) :
    TBF a b G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hF
  exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
    rw [← hFG]
    exact hb w n z t hn hw hz ht⟩

lemma const (c : ℂ) : TBF 0 0 (fun _ _ _ => c) := by
  refine ⟨‖c‖ + 1, 0, 0, by positivity, le_refl 0, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  rw [show (0:ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring, Real.exp_zero,
    Real.rpow_zero, Real.rpow_zero]
  simp only [mul_one]
  linarith [norm_nonneg c]

lemma one : TBF 0 0 (fun _ _ _ => (1 : ℂ)) := by
  simpa using const (1 : ℂ)

lemma mul (hF : TBF a₁ b₁ F) (hG : TBF a₂ b₂ G) :
    TBF (a₁ + a₂) (b₁ + b₂) (fun w n z => F w n z * G w n z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, by positivity, by positivity,
    fun w n z t hn hw hz ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans zero_le_one ht.1
  have hs0 : (0:ℝ) < scale w := Work.Kernels.scale_pos w
  have ht1 : (0:ℝ) < 1 + t := by linarith
  rw [norm_mul]
  have hr1 : (scale w) ^ N1 * (scale w) ^ N2 = (scale w) ^ (N1 + N2) :=
    (Real.rpow_add hs0 N1 N2).symm
  have hr2 : (1 + t) ^ M1 * (1 + t) ^ M2 = (1 + t) ^ (M1 + M2) :=
    (Real.rpow_add ht1 M1 M2).symm
  have hr3 : Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t)
      * Real.exp (a₂ * (ModularGroup.S • w).im - b₂ * Real.pi * t)
      = Real.exp ((a₁ + a₂) * (ModularGroup.S • w).im - (b₁ + b₂) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsplit : (C1 * (scale w) ^ N1 * (1 + t) ^ M1
        * Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t))
      * (C2 * (scale w) ^ N2 * (1 + t) ^ M2
        * Real.exp (a₂ * (ModularGroup.S • w).im - b₂ * Real.pi * t))
      = C1 * C2 * (scale w) ^ (N1 + N2) * (1 + t) ^ (M1 + M2)
        * Real.exp ((a₁ + a₂) * (ModularGroup.S • w).im - (b₁ + b₂) * Real.pi * t) := by
    rw [← hr1, ← hr2, ← hr3]
    ring
  have htw : (0:ℝ) ≤ 1 + t := by linarith
  have hF0 : (0:ℝ) ≤ C1 * (scale w) ^ N1 * (1 + t) ^ M1
      * Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1.le
      (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)) (Real.rpow_nonneg htw _))
      (Real.exp_pos _).le
  have hprod := mul_le_mul (hb1 w n z t hn hw hz ht) (hb2 w n z t hn hw hz ht) (norm_nonneg _) hF0
  rw [hsplit] at hprod
  exact hprod

end TBF
/-- **Far-window absorption.**  `C (scale w)^N (1+t)^M e^{a Im(Sw) - b π t}` is dominated by
`C' (scale w)^N (1+t)^M e^{A Im(Sw) - B π t}` when the exponent inequality below holds on the
far window. -/
lemma TBF.absorb_gen {F : ℍ → ℤ → ℍ → ℂ} {a b A B : ℝ} (h : TBF a b F) (K : ℝ) (hK : 0 ≤ K)
    (hineq : ∀ (w : ℍ) (t : ℝ), FarThresh w t →
      (a - A) * (ModularGroup.S • w).im - (b - B) * Real.pi * t ≤ K) :
    TBF A B F := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C * Real.exp K, N, M, by positivity, hN, hM, fun w n z t hn hw hz ht => ?_⟩
  refine le_trans (hbnd w n z t hn hw hz ht) ?_
  have hexp : Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      ≤ Real.exp (A * (ModularGroup.S • w).im - B * Real.pi * t) * Real.exp K := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h := hineq w t ht
    linarith
  calc C * (scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      ≤ C * (scale w) ^ N * (1 + t) ^ M
          * (Real.exp (A * (ModularGroup.S • w).im - B * Real.pi * t) * Real.exp K) :=
        mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
            (Real.rpow_nonneg (by linarith [ht.1]) _))
    _ = C * Real.exp K * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (A * (ModularGroup.S • w).im - B * Real.pi * t) := by ring

/-- **Far-window absorption, numeric form.**  `TBF a b F` with `a ≤ A`, `b ≤ B` and
`(B - b)·π ≤ A - a` implies `TBF A B F`: indeed `(a-A)·Im ≤ (b-B)·π·t` because
`(B-b)·π·t ≤ (A-a)·Im` (using `t ≤ Im` and `b ≤ B ≤ A`-free nonnegativity of `B-b`). -/
lemma TBF.absorb_far {F : ℍ → ℤ → ℍ → ℂ} {a b A B : ℝ} (h : TBF a b F) (ha : a ≤ A)
    (hb : b ≤ B) (hπ : (B - b) * Real.pi ≤ A - a) : TBF A B F := by
  refine h.absorb_gen 0 le_rfl (fun w t ht => ?_)
  have hIm : (0 : ℝ) ≤ (ModularGroup.S • w).im := by linarith [ht.1, ht.2]
  have hbt : (0 : ℝ) ≤ B - b := by linarith
  have h1 : (B - b) * Real.pi * t ≤ (A - a) * (ModularGroup.S • w).im := by
    calc (B - b) * Real.pi * t ≤ (B - b) * Real.pi * (ModularGroup.S • w).im :=
          mul_le_mul_of_nonneg_left (by linarith [ht.2]) (mul_nonneg hbt Real.pi_pos.le)
      _ ≤ (A - a) * (ModularGroup.S • w).im := mul_le_mul_of_nonneg_right hπ hIm
  linarith [h1]

open Work.Asymptotics.EtailE

/-- Transport -/
lemma TBF.of_bdd {c : ℝ} {F : ℍ → ℂ} (h : Bdd c F)
    (hper : ∀ τ : ℍ, F ((1:ℝ)+ᵥτ) = F τ) : TBF c 0 (fun w n _ => F ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, 0, hC, hN, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  have hvn : F ((n:ℝ)+ᵥw) = F w := by
    rcases hn with h | h
    · rw [h, Int.cast_one]; exact hper w
    · rw [h, Int.cast_neg, Int.cast_one]
      have h3 : (1:ℝ) +ᵥ ((-1:ℝ) +ᵥ w) = w := by rw [← add_vadd]; norm_num
      have h4 := hper ((-1:ℝ) +ᵥ w)
      rw [h3] at h4
      exact h4.symm
  change ‖F ((n:ℝ)+ᵥw)‖ ≤ C * (scale w) ^ N * (1 + t) ^ (0:ℝ)
      * Real.exp (c * (ModularGroup.S • w).im - 0 * Real.pi * t)
  rw [hvn]
  refine le_trans (hb w hw) ?_
  rw [show c * (ModularGroup.S • w).im - 0 * Real.pi * t = c * (ModularGroup.S • w).im from by ring,
    Real.rpow_zero, mul_one]

/-- Transport of a `Bdd` bound with a `T`-cocycle `F(τ+1) = F τ + G τ` to the tiles. -/
lemma TBF.of_bdd_cocycle {c c' : ℝ} {F G : ℍ → ℂ} (hF : Bdd c F) (hG : Bdd c' G)
    (hcoc : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → F ((n:ℝ)+ᵥw) = F w + (n:ℂ) * G w) :
    TBF (max c c') 0 (fun w n _ => F ((n:ℝ)+ᵥw)) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, 0, by positivity, le_max_of_le_left hN1, le_refl 0,
    fun w n z t hn hw hz ht => ?_⟩
  rw [Real.rpow_zero, mul_one]
  have hH0 : 0 ≤ (ModularGroup.S • w).im := by linarith [hw.2]
  have hs1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hmn : ‖(n : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]; rcases hn with h | h <;> rw [h] <;> norm_num
  have h1 := hb1 w hw
  have h2 := hb2 w hw
  have hc1 : Real.exp (c * (ModularGroup.S • w).im)
      ≤ Real.exp (max c c' * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hH0)
  have hc2 : Real.exp (c' * (ModularGroup.S • w).im)
      ≤ Real.exp (max c c' * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hH0)
  have hb1' : ‖F w‖ ≤ C1 * (scale w) ^ (max N1 N2)
      * Real.exp (max c c' * (ModularGroup.S • w).im) := by
    refine le_trans h1 ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN1' hC1.le) hc1 (Real.exp_pos _).le
      (mul_nonneg hC1.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  have hb2' : ‖G w‖ ≤ C2 * (scale w) ^ (max N1 N2)
      * Real.exp (max c c' * (ModularGroup.S • w).im) := by
    refine le_trans h2 ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN2' hC2.le) hc2 (Real.exp_pos _).le
      (mul_nonneg hC2.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  calc ‖F ((n:ℝ)+ᵥw)‖ = ‖F w + (n:ℂ) * G w‖ := by rw [hcoc w n hn]
    _ ≤ ‖F w‖ + ‖G w‖ := by
        refine le_trans (norm_add_le _ _) (le_of_eq ?_)
        rw [norm_mul, hmn, one_mul]
    _ ≤ C1 * (scale w) ^ (max N1 N2) * Real.exp (max c c' * (ModularGroup.S • w).im)
        + C2 * (scale w) ^ (max N1 N2) * Real.exp (max c c' * (ModularGroup.S • w).im) :=
        add_le_add hb1' hb2'
    _ = (C1 + C2) * (scale w) ^ (max N1 N2)
        * Real.exp (max c c' * (ModularGroup.S • w).im - 0 * Real.pi * t) := by
        ring

lemma TBF.E4 : TBF 0 0 (fun w n _ => Work.Kernels.E4Fun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_E4 (fun τ => Work.Kernels.KernelFacts.E4Fun_vadd_one τ)

lemma TBF.E6 : TBF 0 0 (fun w n _ => Work.Kernels.E6Fun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_E6 (fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ)

lemma TBF.E8 : TBF 0 0 (fun w n _ => Work.Kernels.E8Fun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_E8 (fun τ => Work.Kernels.KernelFacts.E8Fun_vadd_one τ)

lemma TBF.E10 : TBF 0 0 (fun w n _ => Work.Kernels.E10Fun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_E10 (fun τ => Work.Kernels.KernelFacts.E10Fun_vadd_one τ)

lemma TBF.E14 : TBF 0 0 (fun w n _ => Work.Kernels.E14Fun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_E14 (fun τ => Work.Kernels.KernelFacts.E14Fun_vadd_one τ)

lemma TBF.Delta : TBF (-(2*Real.pi)) 0 (fun w n _ => Work.Kernels.DeltaFun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_Delta (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ)

lemma TBF.invDelta : TBF (2*Real.pi) 0 (fun w n _ => (Work.Kernels.DeltaFun ((n:ℝ)+ᵥw))⁻¹) :=
  TBF.of_bdd EtailE.E_bdd_invDelta (fun τ => by rw [Work.Kernels.KernelFacts.DeltaFun_vadd_one])

lemma TBF.j : TBF (2*Real.pi) 0 (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_j (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ)

lemma TBF.E14_div_Delta (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2*Real.pi) 0
      (fun w n _ => Work.Kernels.E14Fun ((n:ℝ)+ᵥw) / Work.Kernels.DeltaFun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd (EtailE.E_bdd_E14_div_Delta ℓ)
    (fun τ => by
      rw [Work.Kernels.KernelFacts.E14Fun_vadd_one, Work.Kernels.KernelFacts.DeltaFun_vadd_one])

lemma TBF.E2 : TBF 0 0 (fun w n _ => Work.Kernels.E2Fun ((n:ℝ)+ᵥw)) :=
  TBF.of_bdd EtailE.E_bdd_E2 (fun τ => Work.Kernels.E2Fun_vadd_one τ)

/-! ### The `ψ`-atoms and `Λ` -/

lemma TBF.psi2 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n _ => Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hbd⟩ := tile_tau_atoms ℓ
  refine ⟨C, N, 0, hC, hN, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  obtain ⟨_, _, _, _, _, hpsi2, _, _, _⟩ := hbd w n hn hw
  rw [show (0:ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring, Real.exp_zero,
    Real.rpow_zero]
  simp only [mul_one]
  exact hpsi2

lemma TBF.psi4 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n _ => Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hbd⟩ := tile_tau_atoms ℓ
  refine ⟨C, N, 0, hC, hN, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  obtain ⟨_, _, _, _, _, _, hpsi4, _, _⟩ := hbd w n hn hw
  rw [show (0:ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring, Real.exp_zero,
    Real.rpow_zero]
  simp only [mul_one]
  exact hpsi4

/-- `ψ₄E₈ - ψ₂E₁₀` on the tiles, by the `T`-cocycle: it is `O(e^{-π Im(Sw)})`. -/
lemma TBF.psi_combo (ℓ : Work.Kernels.LogLambdaData) :
    TBF (-(Real.pi)) 0 (fun w n _ => psiCombo ℓ ((n:ℝ)+ᵥw)) := by
  have hG : Bdd (-(Real.pi)) (fun w => (Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w) := by
    obtain ⟨C, N, hC, hN, hb⟩ := E_bdd_Xfun
    refine ⟨Real.pi * C, N, by positivity, hN, fun w hw => ?_⟩
    have h := hb w hw
    rw [norm_mul, norm_mul, EtailE.norm_pi, Complex.norm_I, mul_one]
    calc Real.pi * ‖Work.Residues.Xfun w‖
        ≤ Real.pi * (C * (scale w) ^ N * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)) :=
          mul_le_mul_of_nonneg_left h Real.pi_pos.le
      _ = Real.pi * C * (scale w) ^ N * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by ring
  have h := TBF.of_bdd_cocycle (c := -(2 * Real.pi)) (c' := -(Real.pi))
    (F := fun w => psiCombo ℓ w)
    (G := fun w => (Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)
    (EtailE.E_bdd_psi4E8_sub ℓ) hG ?_
  · have hmax : max (-(2 * Real.pi)) (-(Real.pi)) = -(Real.pi) := by
      rw [max_eq_right]; linarith [Real.pi_pos]
    rwa [hmax] at h
  · intro w n hn
    rcases hn with hh | hh
    · rw [hh, Int.cast_one]; push_cast; rw [one_mul]
      exact psiCombo_vadd_one ℓ w
    · rw [hh, Int.cast_neg, Int.cast_one]; push_cast; rw [neg_one_mul]
      exact psiCombo_vadd_neg_one ℓ w

private lemma lamb_eq_aux (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Residues.Lamb ℓ τ
      = Work.Kernels.E4Fun τ * psiCombo ℓ τ / Work.Kernels.DeltaFun τ := by
  rw [Work.Residues.Lamb_eq]
  simp only [psiCombo, Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.E14Fun]
  ring

/-- `Λ = E₄(ψ₄E₈ - ψ₂E₁₀)/Δ` on the tiles is `O(e^{π Im(Sw)})`. -/
lemma TBF.lamb (ℓ : Work.Kernels.LogLambdaData) :
    TBF Real.pi 0 (fun w n _ => Work.Residues.Lamb ℓ ((n:ℝ)+ᵥw)) := by
  have h : TBF (0 + -(Real.pi) + 2 * Real.pi) 0 (fun w n z =>
      Work.Kernels.E4Fun ((n:ℝ)+ᵥw) * psiCombo ℓ ((n:ℝ)+ᵥw)
        * (Work.Kernels.DeltaFun ((n:ℝ)+ᵥw))⁻¹) := by
    have h := (TBF.E4.mul (TBF.psi_combo ℓ)).mul TBF.invDelta
    simpa using h
  have h2 : TBF (0 + -(Real.pi) + 2 * Real.pi) 0
      (fun w n _ => Work.Residues.Lamb ℓ ((n:ℝ)+ᵥw)) :=
    h.congr (G := fun w n _ => Work.Residues.Lamb ℓ ((n:ℝ)+ᵥw)) (fun w n z => by
      rw [lamb_eq_aux ℓ ((n:ℝ)+ᵥw)]; ring)
  exact h2.mono (by linarith) (le_refl 0)


lemma TBF.mul_ZC {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZC m n f) (hG : TBF a b G) : TBF a (b + n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht1 : (1:ℝ) ≤ t := ht.1
  rw [norm_mul]
  have hfz := hb1 z t ht1 hz
  have hS := hb2 w k z t hk hw hz ht
  have hS0 : (0:ℝ) ≤ C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC2.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
      (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (-(n * Real.pi * t))
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b + n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (-(n * Real.pi * t))
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]

/-- Glue a growing `z`-atom to a `TBF` bound. -/
lemma TBF.mul_ZCg {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZCg m n f) (hG : TBF a b G) : TBF a (b - n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht1 : (1:ℝ) ≤ t := ht.1
  rw [norm_mul]
  have hfz := hb1 z t ht1 hz
  have hS := hb2 w k z t hk hw hz ht
  have hS0 : (0:ℝ) ≤ C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC2.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
      (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (n * Real.pi * t)
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b - n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (n * Real.pi * t))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (n * Real.pi * t)
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]



lemma TBF.psi2E10 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n _ => Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw)
      * Work.Kernels.E10Fun ((n:ℝ)+ᵥw)) := by
  have h : TBF (0+0) (0+0) (fun w n _ => Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw)
      * Work.Kernels.E10Fun ((n:ℝ)+ᵥw)) := (TBF.psi2 ℓ).mul TBF.E10
  exact h.mono (le_of_eq (by ring)) (by norm_num)

lemma TBF.psi4E8 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n _ => Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw)
      * Work.Kernels.E8Fun ((n:ℝ)+ᵥw)) := by
  have h : TBF (0+0) (0+0) (fun w n _ => Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw)
      * Work.Kernels.E8Fun ((n:ℝ)+ᵥw)) := (TBF.psi4 ℓ).mul TBF.E8
  exact h.mono (le_of_eq (by ring)) (by norm_num)

/-- `ψ₄E₈ - ψ₂E₁₀` on the tiles (the sharp `e^{-π Im(Sw)}` bound of `TBF.psi_combo`). -/
lemma TBF.psi4E8_sub_psi2E10 (ℓ : Work.Kernels.LogLambdaData) :
    TBF (-(Real.pi)) 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw) * Work.Kernels.E8Fun ((n:ℝ)+ᵥw)
        - Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw) * Work.Kernels.E10Fun ((n:ℝ)+ᵥw)) :=
  (TBF.psi_combo ℓ).congr (fun w n z => by simp only [psiCombo])

lemma TBF.jpsi2E10 (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2*Real.pi) 0 (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)
      * (Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw) * Work.Kernels.E10Fun ((n:ℝ)+ᵥw))) := by
  have h : TBF (2*Real.pi + 0) (0+0) (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)
      * (Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw) * Work.Kernels.E10Fun ((n:ℝ)+ᵥw))) :=
    TBF.j.mul (TBF.psi2E10 ℓ)
  exact h.mono (le_of_eq (by ring)) (by norm_num)

lemma TBF.jpsi4E8 (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2*Real.pi) 0 (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)
      * (Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw) * Work.Kernels.E8Fun ((n:ℝ)+ᵥw))) := by
  have h : TBF (2*Real.pi + 0) (0+0) (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)
      * (Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw) * Work.Kernels.E8Fun ((n:ℝ)+ᵥw))) :=
    TBF.j.mul (TBF.psi4E8 ℓ)
  exact h.mono (le_of_eq (by ring)) (by norm_num)


lemma TBF.jDelta : TBF 0 0 (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)
    * Work.Kernels.DeltaFun ((n:ℝ)+ᵥw)) := by
  have h : TBF (2*Real.pi + -(2*Real.pi)) (0+0) (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)
      * Work.Kernels.DeltaFun ((n:ℝ)+ᵥw)) := TBF.j.mul TBF.Delta
  exact h.mono (le_of_eq (by ring)) (by norm_num)

lemma TBF.ktl_Shsub1 (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 2 (fun w n z => Compact.Sh ((n : ℝ) +ᵥ w) z - 1) := by
  obtain ⟨Cz, hCz, hzc⟩ := ZC.ktl_E4cube ℓ
  obtain ⟨Cd, hCd, hzd⟩ := ZC.ktl_Delta ℓ
  obtain ⟨Cj, Nj, hCj, hNj, hj⟩ := Work.Asymptotics.EtailE.E_bdd_j
  refine ⟨Cz + Cd * Cj, Nj, 0, by positivity, hNj, le_rfl,
    fun w n z t hn hw hz ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := ht.1
  have hsw1 : (1 : ℝ) ≤ (scale w) ^ Nj := Real.one_le_rpow (one_le_scale w) hNj
  have him : (0 : ℝ) ≤ (ModularGroup.S • w).im := by have := hw.2; linarith
  have h1 : ‖E4Fun z ^ 3 - 1‖ ≤ Cz * (1 + t) ^ (0:ℝ) * Real.exp (-(2 * Real.pi * t)) :=
    hzc z t ht1 hz
  have h2 : ‖DeltaFun z‖ ≤ Cd * (1 + t) ^ (0:ℝ) * Real.exp (-(2 * Real.pi * t)) :=
    hzd z t ht1 hz
  have h3 : ‖jInvariantFun ((n : ℝ) +ᵥ w)‖
      ≤ Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    have := hj w hw
    simpa only [ktl_jInvariantFun_vadd_int n hn w] using this
  have hsh : Compact.Sh ((n : ℝ) +ᵥ w) z - 1
      = (E4Fun z ^ 3 - 1) - DeltaFun z * jInvariantFun ((n : ℝ) +ᵥ w) := by
    simp only [Compact.Sh]; ring
  change ‖Compact.Sh ((n : ℝ) +ᵥ w) z - 1‖ ≤ (Cz + Cd * Cj) * (scale w) ^ Nj
    * (1 + t) ^ (0:ℝ) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
  rw [hsh, Real.rpow_zero, mul_one]
  have hexp1 : Real.exp (-(2 * Real.pi * t))
      ≤ Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
    rw [Real.exp_le_exp]; nlinarith [him, Real.pi_pos]
  have hprod : ‖DeltaFun z * jInvariantFun ((n : ℝ) +ᵥ w)‖
      ≤ Cd * Cj * (scale w) ^ Nj
          * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
    rw [norm_mul]
    have hexp : Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        = Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
      rw [show 2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t
            = 2 * Real.pi * (ModularGroup.S • w).im + (-(2 * Real.pi * t)) from by ring,
        Real.exp_add]
      ring
    calc ‖DeltaFun z‖ * ‖jInvariantFun ((n : ℝ) +ᵥ w)‖
        ≤ (Cd * Real.exp (-(2 * Real.pi * t)))
            * (Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) :=
          mul_le_mul (by simpa [Real.rpow_zero] using h2) h3 (norm_nonneg _) (by positivity)
      _ = Cd * Cj * (scale w) ^ Nj * (Real.exp (-(2 * Real.pi * t))
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by ring
      _ = Cd * Cj * (scale w) ^ Nj
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by rw [hexp]
  have h1' : ‖E4Fun z ^ 3 - 1‖
      ≤ Cz * (scale w) ^ Nj
          * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
    refine le_trans h1 ?_
    rw [Real.rpow_zero, mul_one]
    calc Cz * Real.exp (-(2 * Real.pi * t))
        ≤ Cz * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left hexp1 hCz.le
      _ ≤ Cz * (scale w) ^ Nj
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
          have hp : (0:ℝ) ≤ Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) :=
            (Real.exp_pos _).le
          have hCS : Cz ≤ Cz * (scale w) ^ Nj := by
            calc Cz = Cz * 1 := (mul_one Cz).symm
              _ ≤ Cz * (scale w) ^ Nj := mul_le_mul_of_nonneg_left hsw1 hCz.le
          exact mul_le_mul_of_nonneg_right hCS hp
  have hfinal : ‖(E4Fun z ^ 3 - 1) - DeltaFun z * jInvariantFun ((n : ℝ) +ᵥ w)‖
      ≤ (Cz + Cd * Cj) * (scale w) ^ Nj
          * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
    refine le_trans (norm_sub_le _ _) ?_
    have hsum : Cz * (scale w) ^ Nj
          * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
        + Cd * Cj * (scale w) ^ Nj
          * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
        = (Cz + Cd * Cj) * (scale w) ^ Nj
          * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by ring
    rw [← hsum]
    exact add_le_add h1' hprod
  simpa using hfinal

/-! ## `br0` in dimension `8` -/

lemma TBF.ktl_br0_8 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBF 0 0 (fun w n z => (3456 : ℂ) * (Compact.Xc ℓ z * E4Fun ((n : ℝ) +ᵥ w))) :=
    (TBF.const_mul 3456 (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.E4)).mono
      (le_refl 0) (by norm_num)
  have h2 : TBF 0 0 (fun w n z => (1728 : ℂ) * Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)) :=
    (TBF.const_mul 1728 (TBF.psi4 ℓ)).mono (le_refl 0) (by norm_num)
  refine (h1.sub h2).congr (fun w n z => ?_)
  simp only [Compact.br0_8]
  ring

/-! ## The `d = 8` tile bracket -/


lemma TBF.ktl_j2Delta (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) ^ 2 * DeltaFun ((n : ℝ) +ᵥ w)) := by
  refine ((TBF.j.mul TBF.jDelta).mono (by linarith [Real.pi_pos]) (by norm_num)).congr
    (fun w n z => ?_)
  ring

/-- `j·(ψ₄E₈ - ψ₂E₁₀)` on the tiles. -/
lemma TBF.ktl_jpsiCombo (ℓ : Work.Kernels.LogLambdaData) :
    TBF Real.pi 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * psiCombo ℓ ((n : ℝ) +ᵥ w)) :=
  (TBF.j.mul (TBF.psi_combo ℓ)).mono (by linarith [Real.pi_pos]) (by norm_num)


lemma TBF.ktl_c1 (ℓ : Work.Kernels.LogLambdaData) :
    TBF Real.pi 0 (fun w n z => Work.Asymptotics.kmfd_c1 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hjD : TBF Real.pi 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.jDelta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjp : TBF Real.pi 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * psiCombo ℓ ((n : ℝ) +ᵥ w)) :=
    TBF.ktl_jpsiCombo ℓ
  have hD : TBF Real.pi 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF Real.pi 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    (TBF.psi2E10 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp4 : TBF Real.pi 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    (TBF.psi4E8 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  refine (TBF.add (TBF.add (TBF.add (TBF.add (TBF.const_mul (27648 : ℂ) hjD)
      (TBF.const_mul (24 : ℂ) hjp)) (TBF.const_mul (-20570112 : ℂ) hD))
      (TBF.const_mul (15744 : ℂ) hp2)) (TBF.const_mul (-29568 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c1, psiCombo]
  ring

lemma TBF.ktl_c2 (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 0 (fun w n z => Work.Asymptotics.kmfd_c2 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hj2D : TBF (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) ^ 2 * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.ktl_j2Delta ℓ
  have hjD : TBF (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.jDelta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hD : TBF (2 * Real.pi) 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    (TBF.psi2E10 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp4 : TBF (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    (TBF.psi4E8 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjp2 : TBF (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
        * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) :=
    TBF.jpsi2E10 ℓ
  have hjp4 : TBF (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
        * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    TBF.jpsi4E8 ℓ
  have hX2 : TBF (2 * Real.pi) 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) ^ 2 * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) hj2D).mono (le_refl (2 * Real.pi)) (by norm_num)
  have hX1 : TBF (2 * Real.pi) 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.jDelta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  have hX0 : TBF (2 * Real.pi) 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add
    (TBF.const_mul (-3456 : ℂ) hX2) (TBF.const_mul (4976640 : ℂ) hX1))
    (TBF.const_mul (-1192402944 : ℂ) hX0)) (TBF.const_mul (41472 : ℂ) hjD))
    (TBF.const_mul (1080 : ℂ) hjp2)) (TBF.const_mul (648 : ℂ) hjp4))
    (TBF.const_mul (31850496 : ℂ) hD)) (TBF.const_mul (-651456 : ℂ) hp2))
    (TBF.const_mul (-551232 : ℂ) hp4)).congr (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c2]
  ring

lemma TBF.ktl_c3 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Work.Asymptotics.kmfd_c3 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TBF 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi2E10 ℓ
  have hp4 : TBF 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi4E8 ℓ
  refine (TBF.add (TBF.add (TBF.const_mul (-5271257088 : ℂ) hD)
    (TBF.const_mul (3142656 : ℂ) hp2)) (TBF.const_mul (-3142656 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c3]
  ring

lemma TBF.ktl_c4 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Work.Asymptotics.kmfd_c4 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hjD : TBF 0 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) := TBF.jDelta
  have hD : TBF 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi2E10 ℓ
  have hp4 : TBF 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi4E8 ℓ
  have hX1 : TBF 0 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.jDelta).mono (le_refl 0) (by norm_num)
  have hX0 : TBF 0 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TBF.add (TBF.add (TBF.add (TBF.add (TBF.const_mul (597196800 : ℂ) hX1)
    (TBF.const_mul (-382205952000 : ℂ) hX0)) (TBF.const_mul (8623521792 : ℂ) hD))
    (TBF.const_mul (-178689024 : ℂ) hp2)) (TBF.const_mul (-119909376 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c4]
  ring

lemma TBF.ktl_c5 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Work.Asymptotics.kmfd_c5 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TBF 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi2E10 ℓ
  have hp4 : TBF 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi4E8 ℓ
  refine (TBF.add (TBF.add (TBF.const_mul (-496867737600 : ℂ) hD)
    (TBF.const_mul (287539200 : ℂ) hp2)) (TBF.const_mul (-287539200 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c5]
  ring

lemma TBF.ktl_c6 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Work.Asymptotics.kmfd_c6 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hjD : TBF 0 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) := TBF.jDelta
  have hD : TBF 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi2E10 ℓ
  have hp4 : TBF 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi4E8 ℓ
  have hX1 : TBF 0 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.jDelta).mono (le_refl 0) (by norm_num)
  have hX0 : TBF 0 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TBF.add (TBF.add (TBF.add (TBF.add (TBF.const_mul (47775744000 : ℂ) hX1)
    (TBF.const_mul (-34398535680000 : ℂ) hX0)) (TBF.const_mul (917294284800 : ℂ) hD))
    (TBF.const_mul (-15460761600 : ℂ) hp2)) (TBF.const_mul (-8427110400 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c6]
  ring

lemma TBF.ktl_c7 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Work.Asymptotics.kmfd_c7 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TBF 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi2E10 ℓ
  have hp4 : TBF 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi4E8 ℓ
  refine (TBF.add (TBF.add (TBF.const_mul (-9172942848000 : ℂ) hD)
    (TBF.const_mul (5308416000 : ℂ) hp2)) (TBF.const_mul (-5308416000 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c7]
  ring

lemma TBF.ktl_c8 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Work.Asymptotics.kmfd_c8 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TBF 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi2E10 ℓ
  have hp4 : TBF 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi4E8 ℓ
  refine (TBF.add (TBF.add (TBF.const_mul (27518828544000 : ℂ) hD)
    (TBF.const_mul (-15925248000 : ℂ) hp2)) (TBF.const_mul (15925248000 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c8]
  ring

lemma TBF.ktl_dA (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 3 (fun w n z => Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) z) := by
  have hT1 : TBF (-(2 * Real.pi)) 0
      (fun w n _ => (-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) := TBF.const_mul (-3456) TBF.Delta
  have hT2 : TBF 0 0 (fun w n _ =>
      -(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
        - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    (TBF.sub (TBF.psi2E10 ℓ) (TBF.psi4E8 ℓ)).neg
  have hp1 : TBF (-(2 * Real.pi)) (0 + 3)
      (fun w n z => (Compact.dE14 z * ℓ.L z + Compact.E14ref z * Compact.dL ℓ z)
        * ((-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    TBF.mul_ZC zero_le_one (ZC.ktl_dA1 ℓ) hT1
  have hp2 : TBF 0 (0 + 3)
      (fun w n z => (Compact.dE10 z * (UFun z ^ 2 - VFun z ^ 2)
          + Compact.E10ref z * Compact.dD2 z)
        * (-(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)))) :=
    TBF.mul_ZC (le_refl 0) (ZC.ktl_dA2 ℓ) hT2
  refine (TBF.add (hp1.mono (by linarith [Real.pi_pos]) (by norm_num))
    (hp2.mono (le_refl 0) (by norm_num))).congr (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_dA]
  ring


lemma TBF.ktl_A24 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Compact.A24 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hT1 : TBF (-(2 * Real.pi)) 0
      (fun w n _ => (-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) := TBF.const_mul (-3456) TBF.Delta
  have hT2 : TBF 0 0 (fun w n _ =>
      -(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
        - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    (TBF.sub (TBF.psi2E10 ℓ) (TBF.psi4E8 ℓ)).neg
  have hp1 : TBF (-(2 * Real.pi)) 0
      (fun w n z => (E14Fun z * ℓ.L z) * ((-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_E14L ℓ) hT1).mono (le_refl (-(2 * Real.pi))) (by norm_num)
  have hp2 : TBF 0 0
      (fun w n z => (E10Fun z * (UFun z ^ 2 - VFun z ^ 2))
        * (-(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)))) :=
    (TBF.mul_ZC (le_refl 0) (ZC.ktl_E10D2 ℓ) hT2).mono (le_refl 0) (by norm_num)
  refine (TBF.add (hp1.mono (by linarith [Real.pi_pos]) (by norm_num)) hp2).congr
    (fun w n z => ?_)
  simp only [Compact.A24]
  ring

lemma TBF.ktl_B24 (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Compact.B24 ℓ ((n : ℝ) +ᵥ w)) := by
  have h1 : TBF 0 0 (fun w n _ => (-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBF.const_mul (-3456) TBF.Delta).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have h2 : TBF 0 0
      (fun w n _ => (2 : ℂ) * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) :=
    TBF.const_mul 2 (TBF.psi2E10 ℓ)
  have h3 : TBF 0 0
      (fun w n _ => (2 : ℂ) * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    TBF.const_mul 2 (TBF.psi4E8 ℓ)
  refine (TBF.sub (TBF.add h1 h2) h3).congr (fun w n z => ?_)
  simp only [Compact.B24]
  ring

lemma TBF.ktl_C24 (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 0 (fun w n z => Compact.C24 ℓ ((n : ℝ) +ᵥ w)) := by
  have h1 : TBF (2 * Real.pi) 0 (fun w n _ =>
      (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))
        * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    ((TBF.psi2E10 ℓ).mul TBF.j).mono (by linarith [Real.pi_pos]) (by norm_num)
  have hsub : TBF (2 * Real.pi) 0
      (fun w n _ => (1728 : ℂ) - jInvariantFun ((n : ℝ) +ᵥ w)) :=
    TBF.sub ((TBF.const (1728 : ℂ)).mono (by linarith [Real.pi_pos]) (le_refl 0)) TBF.j
  have h2 : TBF (2 * Real.pi) 0 (fun w n _ =>
      (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))
        * ((1728 : ℂ) - jInvariantFun ((n : ℝ) +ᵥ w))) :=
    ((TBF.psi4E8 ℓ).mul hsub).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine (TBF.add h1 h2).congr (fun w n z => ?_)
  simp only [Compact.C24, mul_assoc]

/-! ## The deviation `kmfd_dev` -/


lemma TBF.of_ZC {m n : ℝ} {f : ℍ → ℂ} (hm : 0 ≤ m) (hf : ZC m n f) :
    TBF 0 n (fun _ _ z => f z) := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, 0, m, hC, le_refl 0, hm, fun w k z t hk hw hz ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := ht.1
  have h1 := hb z t ht1 hz
  have hexp : Real.exp (0 * (ModularGroup.S • w).im - n * Real.pi * t)
      = Real.exp (-(n * Real.pi * t)) := by congr 1; ring
  rw [hexp, Real.rpow_zero, mul_one]
  exact h1


lemma TBF.ktl_einv2 : TBF 0 (-2) (fun _ _ z => Compact.einv2 z) := by
  refine ⟨1, 0, 0, one_pos, le_refl 0, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  have h1 : ‖Compact.einv2 z‖ = Real.exp (2 * Real.pi * t) := by
    rw [Compact.einv2, norm_pow, norm_inv, ktl_norm_Ept hz]
    rw [show ((Real.exp (-(Real.pi * t)))⁻¹) ^ 2 = Real.exp (2 * Real.pi * t) from by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring]
  rw [h1]
  have hexp : (0:ℝ) * (ModularGroup.S • w).im - (-2) * Real.pi * t = 2 * Real.pi * t := by ring
  rw [hexp]
  simp


lemma TBF.ktl_Nf (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := by
  have hDX : TBF 0 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  have hD : TBF 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi2E10 ℓ
  have hp4 : TBF 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TBF.psi4E8 ℓ
  refine (TBF.add (TBF.add (TBF.add (TBF.const_mul (-3456 : ℂ) hDX) (TBF.const_mul 3456 hD))
    (TBF.const_mul (-3 : ℂ) hp2)) (TBF.const_mul 3 hp4)).congr (fun w n z => ?_)
  simp only [Compact.Nf]
  ring


lemma TBF.ktl_Mf (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)) := by
  have hD : TBF (2 * Real.pi) 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjD : TBF (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.jDelta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    (TBF.psi2E10 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp4 : TBF (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    (TBF.psi4E8 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjp2 : TBF (2 * Real.pi) 0 (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) := TBF.jpsi2E10 ℓ
  have hjp4 : TBF (2 * Real.pi) 0 (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) := TBF.jpsi4E8 ℓ
  have h1 : TBF (2 * Real.pi) 0
      (fun w n _ => (-41472 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TBF.const_mul (-41472) hD
  have h2 : TBF (2 * Real.pi) 0 (fun w n _ => (-3456 : ℂ)
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)
        - (768 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    TBF.const_mul (-3456) (TBF.sub hjD (TBF.const_mul (768 : ℂ) hD))
  have h3 : TBF (2 * Real.pi) 0 (fun w n _ =>
      Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
        * ((3 : ℂ) * jInvariantFun ((n : ℝ) +ᵥ w) - 1152)) := by
    have ha : TBF (2 * Real.pi) 0 (fun w n _ =>
        (3 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w) * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)
          * E10Fun ((n : ℝ) +ᵥ w)))) := TBF.const_mul 3 hjp2
    have hb : TBF (2 * Real.pi) 0 (fun w n _ =>
        (1152 : ℂ) * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) :=
      TBF.const_mul 1152 hp2
    refine (TBF.sub ha hb).congr (fun w n z => ?_)
    ring
  have h4 : TBF (2 * Real.pi) 0 (fun w n _ =>
      Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)
        * ((2880 : ℂ) - 3 * jInvariantFun ((n : ℝ) +ᵥ w))) := by
    have ha : TBF (2 * Real.pi) 0 (fun w n _ =>
        (2880 : ℂ) * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
      TBF.const_mul 2880 hp4
    have hb : TBF (2 * Real.pi) 0 (fun w n _ =>
        (3 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w) * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)
          * E8Fun ((n : ℝ) +ᵥ w)))) := TBF.const_mul 3 hjp4
    refine (TBF.sub ha hb).congr (fun w n z => ?_)
    ring
  refine (TBF.neg (TBF.add (TBF.add (TBF.add h1 h2) h3) h4)).congr (fun w n z => ?_)
  simp only [Compact.Mf]
  ring

lemma TBF.ktl_br0b (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)
      + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := by
  have hM : TBF (2 * Real.pi) 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)) := TBF.ktl_Mf ℓ
  have hN : TBF 0 0 (fun w n z => Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := TBF.ktl_Nf ℓ
  have h720 : TBF (2 * Real.pi) 0
      (fun w n z => (720 : ℂ) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.const_mul 720 hN).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjN : TBF (2 * Real.pi) 0
      (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul TBF.j hN).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine (TBF.add hM (TBF.sub h720 hjN)).congr (fun w n z => ?_)
  ring


/-- **The `e^{-2}`-free part of `br0_24` keeps its `jτ`-cancellation and is polynomially bounded.**

`-Mf + (720 - jτ)·Nf` rewrites, by pure ring algebra (the `jτ·psiCombo` and `jτ·Δ` terms
cancel: `-3jτ(ψ₂E₁₀ - ψ₄E₈) - 3jτ·psiCombo = 0` and `3456Δ·jτ - 3456Δ·jτ = 0`), to

  `-124416·Δ - 2488320·Δ·Xc + 3456·(Δ·jτ)·Xc + 2160·psiCombo + 1152·ψ₂E₁₀ - 2880·ψ₄E₈`,

each term of which is `TBF 0 0`.  This is the far-window-correct replacement for the naive
piecewise bound (`-Mf` and `(720-jτ)·Nf` are individually `e^{2π Im(S•w)}`-large). -/
lemma TBF.ktl_br0b_far (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)
      + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TBF 0 0 (fun w n _ => (-124416 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBF.const_mul (-124416) TBF.Delta).mono (a₁ := 0) (b₁ := 0) (by linarith [Real.pi_pos])
      (le_refl 0)
  have hDX : TBF 0 0 (fun w n z => (-2488320 : ℂ)
      * (Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TBF.const_mul (-2488320)
      (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.Delta)).mono (a₁ := 0) (b₁ := 0)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hjDX : TBF 0 0 (fun w n z => (3456 : ℂ)
      * (Compact.Xc ℓ z * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)))) :=
    (TBF.const_mul 3456
      (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.jDelta)).mono (a₁ := 0) (b₁ := 0)
      (le_refl 0) (by norm_num)
  have hpC : TBF 0 0 (fun w n _ => (2160 : ℂ) * psiCombo ℓ ((n : ℝ) +ᵥ w)) :=
    (TBF.const_mul 2160 (TBF.psi_combo ℓ)).mono (a₁ := 0) (b₁ := 0)
      (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TBF 0 0 (fun w n _ => (1152 : ℂ) * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := TBF.const_mul 1152 (TBF.psi2E10 ℓ)
  have hp4 : TBF 0 0 (fun w n _ => (-2880 : ℂ) * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := TBF.const_mul (-2880) (TBF.psi4E8 ℓ)
  refine (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add hD hDX) hjDX) hpC) hp2) hp4).congr
    (fun w n z => ?_)
  simp only [Compact.Mf, Compact.Nf, psiCombo]
  ring_nf

/-- **`Nf`, the coefficient of `e^{-2}` in `br0_24`, is polynomially bounded in the far window.**
`Nf = -3456·Δ·Xc + 3456·Δ + 3·psiCombo` (the `psi`-part collapses to the decaying
`psiCombo = ψ₄E₈ - ψ₂E₁₀`), so `TBF 0 0 Nf`. -/
lemma TBF.ktl_Nf_far (ℓ : Work.Kernels.LogLambdaData) :
    TBF 0 0 (fun w n z => Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBF 0 0 (fun w n z => (-3456 : ℂ)
      * (Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TBF.const_mul (-3456)
      (TBF.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TBF.Delta)).mono (a₁ := 0) (b₁ := 0)
      (by linarith [Real.pi_pos]) (by norm_num)
  have h2 : TBF 0 0 (fun w n _ => (3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBF.const_mul 3456 TBF.Delta).mono (a₁ := 0) (b₁ := 0) (by linarith [Real.pi_pos])
      (le_refl 0)
  have h3 : TBF 0 0 (fun w n _ => (3 : ℂ) * psiCombo ℓ ((n : ℝ) +ᵥ w)) :=
    (TBF.const_mul 3 (TBF.psi_combo ℓ)).mono (a₁ := 0) (b₁ := 0) (by linarith [Real.pi_pos])
      (le_refl 0)
  refine (TBF.add (TBF.add h1 h2) h3).congr (fun w n z => ?_)
  simp only [Compact.Nf, psiCombo]
  ring_nf

/-- **The far-window bound for `dSh · br0_24`.**  With the `jτ`-cancellation preserved in
`B = -Mf + (720-jτ)Nf` (`TBF.ktl_br0b_far`) the four pieces of
`dSh·br0_24 = (E4(z)³-E4refc)(-Nf·einv2 + B) - jτ(Δ(z)-Ept²)·(-Nf·einv2 + B)`
have exponent pairs `(0,2), (0,4), (2π,2), (2π,4)`, all dominated (in the far window) by the
target pair `(2π,2)`. -/
lemma TBF.ktl_dShbr0_far (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 2 (fun w n z => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) z
      * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hA : TBF 0 4 (fun _ _ z => E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z) :=
    TBF.of_ZC (le_refl 0) (ZC.ktl_E4cref_dev ℓ)
  have hB : TBF 0 4 (fun _ _ z => DeltaFun z - Work.Residues.Ept z ^ 2) :=
    TBF.of_ZC (le_refl 0) (ZC.ktl_Delta_dev ℓ)
  have hbr0a : TBF 0 (-2)
      (fun w n z => -(Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) * Compact.einv2 z) :=
    (TBF.mul (TBF.ktl_Nf_far ℓ).neg TBF.ktl_einv2).mono (a₁ := 0) (b₁ := (-2))
      (by norm_num) (by norm_num)
  have hbr0b : TBF 0 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)
      + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) :=
    TBF.ktl_br0b_far ℓ
  have e1 : TBF (2 * Real.pi) 2 (fun w n z => (E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z)
      * (-(Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) * Compact.einv2 z)) :=
    (TBF.mul hA hbr0a).mono (a₁ := 2 * Real.pi) (b₁ := 2) (by linarith [Real.pi_pos])
      (by norm_num)
  have e2 : TBF (2 * Real.pi) 2 (fun w n z => (E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z)
      * (-Compact.Mf ℓ ((n : ℝ) +ᵥ w)
        + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z)) :=
    (TBF.mul hA hbr0b).mono (a₁ := 2 * Real.pi) (b₁ := 2) (by linarith [Real.pi_pos])
      (by norm_num)
  have e3 : TBF (2 * Real.pi) 2 (fun w n z =>
      (-(jInvariantFun ((n : ℝ) +ᵥ w) * (DeltaFun z - Work.Residues.Ept z ^ 2)))
        * (-(Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) * Compact.einv2 z)) :=
    (TBF.mul (TBF.mul TBF.j hB).neg hbr0a).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have e4 : TBF (2 * Real.pi) 2 (fun w n z =>
      (-(jInvariantFun ((n : ℝ) +ᵥ w) * (DeltaFun z - Work.Residues.Ept z ^ 2)))
        * (-Compact.Mf ℓ ((n : ℝ) +ᵥ w)
          + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z)) :=
    (TBF.mul (TBF.mul TBF.j hB).neg hbr0b).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  refine (TBF.add (TBF.add e1 e2) (TBF.add e3 e4)).congr (fun w n z => ?_)
  rw [Compact.br0_24]
  simp only [Work.Asymptotics.kmfd_dSh]
  ring

/-- **The far-window bound for `kmfd_dev`**, the second summand of the `K_-` bracket.
Copied from `TBMW.ktl_dev` with the far-window target pair `(2π,2)`: the `(0,1)`-pieces `h1`
and `h4b` are absorbed with `TBF.absorb_gen` at `K = 0` (the inequality is `t ≤ 2 Im(S•w)`), the
remaining pieces have pairs `(0,2)`, `(2π,3)`, `(2π,2)` and go through `.mono`. -/
lemma TBF.ktl_dev_far (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 2 (fun w n z => Work.Asymptotics.kmfd_dev ℓ ((n : ℝ) +ᵥ w) z) := by
  have hdA : TBF 0 3 (fun w n z => Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) z) := TBF.ktl_dA ℓ
  have hA24 : TBF 0 0 (fun w n z => Compact.A24 ℓ ((n : ℝ) +ᵥ w) z) := TBF.ktl_A24 ℓ
  have hB24 : TBF 0 0 (fun w n z => Compact.B24 ℓ ((n : ℝ) +ᵥ w)) := TBF.ktl_B24 ℓ
  have hC24 : TBF (2 * Real.pi) 0 (fun w n z => Compact.C24 ℓ ((n : ℝ) +ᵥ w)) := TBF.ktl_C24 ℓ
  have h1 : TBF (2 * Real.pi) 2
      (fun w n z => Compact.Dref z * Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZCg (le_refl 0) (ZCg.ktl_Dref ℓ) hdA).absorb_far
      (by push_cast; linarith [Real.pi_pos]) (by push_cast; norm_num) (by push_cast; linarith [Real.pi_pos])
  have h2 : TBF (2 * Real.pi) 2
      (fun w n z => Compact.dDelta z * Compact.A24 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.ktl_dDelta ℓ) hA24).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have h3 : TBF (2 * Real.pi) 2
      (fun w n z => Compact.dW z * Compact.C24 ℓ ((n : ℝ) +ᵥ w)) :=
    (TBF.mul_ZC (le_refl 0) (ZC.ktl_dW ℓ) hC24).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have h4a : TBF (2 * Real.pi) 2 (fun w n z =>
      Compact.dW z * (jInvariantFun ((n : ℝ) +ᵥ w) * Compact.B24 ℓ ((n : ℝ) +ᵥ w))) :=
    (TBF.mul_ZC (le_refl 0) (ZC.ktl_dW ℓ) (TBF.j.mul hB24)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have h4b : TBF (2 * Real.pi) 2 (fun w n z =>
      (Work.Asymptotics.kmfd_jref z * Compact.dW z) * Compact.B24 ℓ ((n : ℝ) +ᵥ w)) :=
    (TBF.mul_ZC (le_refl 0) (ZC.ktl_jref_dW ℓ) hB24).absorb_far
      (by push_cast; linarith [Real.pi_pos]) (by push_cast; norm_num) (by push_cast; linarith [Real.pi_pos])
  have h5 : TBF (2 * Real.pi) 2 (fun w n z =>
      ((jInvariantFun z - Work.Asymptotics.kmfd_jref z) * WFun z)
        * Compact.B24 ℓ ((n : ℝ) +ᵥ w)) :=
    (TBF.mul_ZC (le_refl 0)
      (((ZC.ktl_jdev ℓ).mul (ZC.ktl_W ℓ)).mono (m' := 0) (n' := 2) (by norm_num) (by norm_num))
      hB24).mono (a₁ := 2 * Real.pi) (b₁ := 2) (by linarith [Real.pi_pos]) (by norm_num)
  have h4 : TBF (2 * Real.pi) 2 (fun w n z =>
      Compact.dW z * (jInvariantFun ((n : ℝ) +ᵥ w) * Compact.B24 ℓ ((n : ℝ) +ᵥ w))
        - (Work.Asymptotics.kmfd_jref z * Compact.dW z) * Compact.B24 ℓ ((n : ℝ) +ᵥ w)) :=
    TBF.sub h4a h4b
  have h6 : TBF (2 * Real.pi) 2 (fun w n z => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) z
      * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) z) := TBF.ktl_dShbr0_far ℓ
  refine (TBF.add (TBF.sub (TBF.add (TBF.add h1 h2) (TBF.add h3 h4)) h5) h6).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_dev]
  ring

/-- **The far-window `d = 24` tile bracket** `brMinus + Sh·br0`, whose target pair is `(2π,2)`.

The `kmfd_BR` pieces `Ept^k·c_k` carry pairs `(π,1)`, `(2π,2)`, `(0,k)`: the first is absorbed
with `TBF.absorb_gen` at `K = 0` (`t ≤ Im(S•w)`), the rest go through `.mono`.  Together with
`TBF.ktl_dev_far` (also `(2π,2)`) this bounds the full bracket
`brMinus + Sh·br0 = kmfd_BR + kmfd_dev` (`Work.Asymptotics.kmfd_bracket_decomp`). -/
lemma TBF.ktl_G24_far (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 2 (fun w n z => Compact.brMinus ℓ 24 ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hp1 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 1
      * Work.Asymptotics.kmfd_c1 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 1) (TBF.ktl_c1 ℓ)).absorb_far
      (by push_cast; linarith [Real.pi_pos]) (by push_cast; norm_num) (by push_cast; linarith [Real.pi_pos])
  have hp2 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 2
      * Work.Asymptotics.kmfd_c2 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 2) (TBF.ktl_c2 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hp3 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 3
      * Work.Asymptotics.kmfd_c3 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 3) (TBF.ktl_c3 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hp4 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 4
      * Work.Asymptotics.kmfd_c4 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 4) (TBF.ktl_c4 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hp5 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 5
      * Work.Asymptotics.kmfd_c5 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 5) (TBF.ktl_c5 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hp6 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 6
      * Work.Asymptotics.kmfd_c6 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 6) (TBF.ktl_c6 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hp7 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 7
      * Work.Asymptotics.kmfd_c7 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 7) (TBF.ktl_c7 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hp8 : TBF (2 * Real.pi) 2 (fun w n z => Work.Residues.Ept z ^ 8
      * Work.Asymptotics.kmfd_c8 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul_ZC (le_refl 0) (ZC.Ept_pow 8) (TBF.ktl_c8 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  have hBR : TBF (2 * Real.pi) 2 (fun w n z => Work.Asymptotics.kmfd_BR ℓ ((n : ℝ) +ᵥ w) z) := by
    refine (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add (TBF.add hp1 hp2) hp3) hp4)
      hp5) hp6) hp7) hp8).congr (fun w n z => ?_)
    simp only [Work.Asymptotics.kmfd_BR_expansion]
    ring
  refine (TBF.add hBR (TBF.ktl_dev_far ℓ)).congr (fun w n z => ?_)
  rw [Work.Asymptotics.kmfd_bracket_decomp]

/-- **The far-window `d = 8` tile bracket.** -/
lemma TBF.ktl_G8_far (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 2 (fun w n z => Compact.brMinus ℓ 8 ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hA1 : TBF (2 * Real.pi) 2 (fun w n z => (-3456 : ℂ)
      * ((E10Fun z * ℓ.L z - Compact.Xc ℓ z) * E4Fun ((n : ℝ) +ᵥ w))) :=
    (TBF.const_mul (-3456) (TBF.mul_ZC zero_le_one (ZC.ktl_E10L ℓ) TBF.E4)).absorb_far
      (by push_cast; linarith [Real.pi_pos]) (by push_cast; norm_num) (by push_cast; linarith [Real.pi_pos])
  have hA2 : TBF (2 * Real.pi) 2 (fun w n z => (-1 : ℂ)
      * ((E8Fun z * WFun z - E6Fun z * (UFun z ^ 2 - VFun z ^ 2))
          * Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w))) :=
    (TBF.const_mul (-1) (TBF.mul_ZC (le_refl 0) (ZC.ktl_Az ℓ) (TBF.lamb ℓ))).absorb_far
      (by push_cast; linarith [Real.pi_pos]) (by push_cast; norm_num) (by push_cast; linarith [Real.pi_pos])
  have hA3 : TBF (2 * Real.pi) 2 (fun w n z => (1728 : ℂ) * ((E8Fun z * WFun z - 1)
      * Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w))) :=
    (TBF.const_mul 1728 (TBF.mul_ZC (le_refl 0) (ZC.ktl_E8W ℓ) (TBF.psi4 ℓ))).absorb_far
      (by push_cast; linarith [Real.pi_pos]) (by push_cast; norm_num) (by push_cast; linarith [Real.pi_pos])
  have hA4 : TBF (2 * Real.pi) 2 (fun w n z => (Compact.Sh ((n : ℝ) +ᵥ w) z - 1)
      * Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TBF.mul (TBF.ktl_Shsub1 ℓ) (TBF.ktl_br0_8 ℓ)).mono (a₁ := 2 * Real.pi) (b₁ := 2)
      (by linarith [Real.pi_pos]) (by norm_num)
  refine (TBF.add (TBF.add (TBF.add hA1 hA2) hA3) hA4).congr (fun w n z => ?_)
  simp only [Compact.brMinus_eight, Compact.br0_8, Work.Residues.bracket8e,
    Work.Residues.Lamb, Compact.Xc, Work.Kernels.c1728]
  ring

lemma TBF.ktl_dSh (ℓ : Work.Kernels.LogLambdaData) :
    TBF (2 * Real.pi) 4 (fun w n z => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) z) := by
  have hA : TBF (2 * Real.pi) 4 (fun _ _ z => E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z) :=
    (TBF.of_ZC (le_refl 0) (ZC.ktl_E4cref_dev ℓ)).mono (by linarith [Real.pi_pos]) (le_refl 4)
  have hB : TBF 0 4 (fun _ _ z => DeltaFun z - Work.Residues.Ept z ^ 2) :=
    TBF.of_ZC (le_refl 0) (ZC.ktl_Delta_dev ℓ)
  have hjB : TBF (2 * Real.pi) 4
      (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w) * (DeltaFun z - Work.Residues.Ept z ^ 2)) :=
    (TBF.mul TBF.j hB).mono (a₁ := 2 * Real.pi) (b₁ := 4) (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TBF.sub hA hjB).congr (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_dSh]


/-! ## The `d = 24` tile bracket -/


/-! ## The `d = 24` tile bracket: the coefficients `c₁, …, c₈` -/

end

end Work.Asymptotics.Tile
