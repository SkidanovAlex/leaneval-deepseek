import Mathlib
import Submission.Work.Asymptotics.KhatE1.Bracket24Defs
import Submission.Work.Asymptotics.KhatE1.KPlus24SharpStrip
import Submission.Work.Asymptotics.Compact.kminus_tail_core

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-!
# The `Sh`-cleared sharp `d = 24` bracket: definitions and the two-piece reduction

This module holds the definitions shared by `KhatE1/Bracket24ClearedBound.lean` and its two
sub-obligations `KhatE1/Bracket24E2_bound` and `KhatE1/Bracket24Tail_bound`:

* `S0z`, the reference `S0 z = 1 - 6i/(πz)`;
* `Bracket24E2`, the explicit `Ept z²`-coefficient of the `Sh`-cleared `d = 24` bracket
  (see the module docstring of `Bracket24ClearedBound.lean` for its provenance);
* the two predicates `Bracket24E2Bound` and `Bracket24TailBound`;
* the **proved** reduction `Bracket24ClearedBound_of_pieces`.
-/

noncomputable section

/-- The reference `S0 z = 1 - 6i/(πz)`. -/
def S0z (z : UpperHalfPlane) : ℂ := 1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))

/-- **The `Ept z²`-coefficient `B_2` of the `Sh`-cleared `d = 24` bracket.**  Explicit
(verified against the integral-kernel model); see the module docstring. -/
def Bracket24E2 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      9558 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ)
      + -142236 * (Work.Asymptotics.Compact.cuspC ℓ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ)
      + (-4719 / 32) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ)
      + (-6417 / 32) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ)
      + (1 / 3) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + (1 / 6) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + -12 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + 1464 * (Work.Asymptotics.Compact.cuspC ℓ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + -1 * (Work.Asymptotics.Compact.cuspC ℓ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + -142236 * (z : ℂ) * Complex.I * (Work.Kernels.DeltaFun τ)
      + 1464 * (z : ℂ) * Complex.I * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + -1 * (z : ℂ) * Complex.I * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (71 / 48) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (71 / 16) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (1 / 36) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (1 / 6) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ) * (Work.Kernels.jInvariantFun τ)
      + (-71 / 96) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ)
      + (-1351 / 96) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ)
      + (-1351 / 16) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ)
      + -1989 * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ)
      + -5967 * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ)
      + (4 / 3) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.E2Fun τ) * (τ : ℂ)
      + 4 * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * ((Work.Kernels.E4Fun τ)) ^ 3
      + (1 / 4) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (3 / 4) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (-35 / 24) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ)
      + (-1 / 8) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ)
      + (-3 / 4) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ)
      + -8154 * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ)
      + -24462 * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ)
      + (244 / 3) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.E2Fun τ) * (τ : ℂ)
      + 244 * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * ((Work.Kernels.E4Fun τ)) ^ 3
      + (-1 / 18) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.E2Fun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-1 / 6) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.jInvariantFun τ)
      + (1 / 36) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-1 / 16) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-3 / 16) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (-639 / 32) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ)
      + (1 / 32) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ)
      + (3 / 16) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ)
      + 63 * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ)
      + 189 * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ)

/-- **The `E²`-coefficient bound**: `B_2 = O(‖q(τ)‖(scale τ)^N(1+t)^M)` on the funnel strip. -/
def Bracket24E2Bound (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Bracket24E2 ℓ τ z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M

/-- **The tail bound**: `Sh τ z·Bracket24 ℓ τ z - (Ept z)²·B_2` is one power of `q` smaller. -/
def Bracket24TailBound (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z
          - (Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t))

private lemma mono_bound {C : ℝ} (hC : 0 ≤ C) {N N' M M' : ℝ} (hN : N ≤ N') (hM : M ≤ M')
    {τ : UpperHalfPlane} {t : ℝ} (hs : 1 ≤ Work.Kernels.scale τ) (ht : 1 ≤ (1 : ℝ) + t) :
    C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (-(2 * Real.pi * t))
      ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N' * (1 + t) ^ M'
        * Real.exp (-(2 * Real.pi * t)) := by
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs
  have ht0 : (0 : ℝ) ≤ 1 + t := le_trans zero_le_one ht
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hN'' : (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ N' :=
    Real.rpow_le_rpow_of_exponent_le hs hN
  have hM'' : (1 + t) ^ M ≤ (1 + t) ^ M' := Real.rpow_le_rpow_of_exponent_le ht hM
  have h1 : C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N' :=
    mul_le_mul_of_nonneg_left hN'' (mul_nonneg hC hq0)
  have h2 : (1 + t) ^ M * Real.exp (-(2 * Real.pi * t))
      ≤ (1 + t) ^ M' * Real.exp (-(2 * Real.pi * t)) :=
    mul_le_mul_of_nonneg_right hM'' hE0
  calc C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (-(2 * Real.pi * t))
      = (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N)
          * ((1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) := by ring
    _ ≤ (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N')
          * ((1 + t) ^ M' * Real.exp (-(2 * Real.pi * t))) :=
        mul_le_mul h1 h2 (mul_nonneg (Real.rpow_nonneg ht0 _) hE0)
          (mul_nonneg (mul_nonneg hC hq0) (Real.rpow_nonneg hs0 _))
    _ = C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N' * (1 + t) ^ M'
        * Real.exp (-(2 * Real.pi * t)) := by ring

/-- **The target from the two pieces** (triangle inequality, `‖Ept z‖² = exp(-2πt)`). -/
theorem Bracket24ClearedBound_of_pieces (ℓ : Work.Kernels.LogLambdaData)
    (h2 : Bracket24E2Bound ℓ) (htail : Bracket24TailBound ℓ) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := h2
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2'⟩ := htail
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by linarith, le_trans hN1 (le_max_left _ _),
    le_trans hM1 (le_max_left _ _), ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have ht1 : (1 : ℝ) ≤ (1 : ℝ) + t := by have := hF.2; linarith
  have he2 : ‖(Work.Residues.Ept z) ^ 2‖ = Real.exp (-(2 * Real.pi * t)) := by
    rw [norm_pow, Work.Residues.norm_Ept, hzim]
    rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  have h1' := h1 τ z t hF ht hz0 hz1 hzim
  have h2'' := h2' τ z t hF ht hz0 hz1 hzim
  have hA : ‖(Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z‖
      ≤ C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)) := by
    rw [norm_mul, he2]
    calc Real.exp (-(2 * Real.pi * t)) * ‖Bracket24E2 ℓ τ z‖
        ≤ Real.exp (-(2 * Real.pi * t))
            * (C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1
                * (1 + t) ^ M1) :=
          mul_le_mul_of_nonneg_left h1' hE0
      _ = C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
            * Real.exp (-(2 * Real.pi * t)) := by ring
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)) :=
          mono_bound hC1.le (le_max_left _ _) (le_max_left _ _) hs1 ht1
  have hB : ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z
        - (Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z‖
      ≤ C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)) :=
    le_trans h2'' (mono_bound hC2.le (le_max_right _ _) (le_max_right _ _) hs1 ht1)
  have htri : ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z‖
      ≤ ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z
            - (Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z‖
          + ‖(Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z‖ := by
    have h := norm_add_le (Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z
        - (Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z)
      ((Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z)
    have heq : Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z
        - (Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z
        + (Work.Residues.Ept z) ^ 2 * Bracket24E2 ℓ τ z
        = Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z := by ring
    rwa [heq] at h
  refine le_trans (le_trans htri (add_le_add hB hA)) (le_of_eq ?_)
  ring




/-! ## The next coefficients of the tail (for the `k = 3, 4, 5` requirements) -/

def Bracket24E3 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (5634048 / 5) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ)
      + (-4768 / 3) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ)
      + (13360 / 3) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ)
      + (113 / 12) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + (-161 / 12) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + (-35104 / 3) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (1 / 144) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (-1 / 144) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + 8 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2

def Bracket24E4 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      5190880 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ)
      + -69139520 * (Work.Asymptotics.Compact.cuspC ℓ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ)
      + (-1012385 / 18) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ)
      + (-600919 / 18) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ)
      + (-691 / 96) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + (-461 / 96) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + -636 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + 161748 * (Work.Asymptotics.Compact.cuspC ℓ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + 24 * (Work.Asymptotics.Compact.cuspC ℓ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + -69139520 * (z : ℂ) * Complex.I * (Work.Kernels.DeltaFun τ)
      + 161748 * (z : ℂ) * Complex.I * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + 24 * (z : ℂ) * Complex.I * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (71 / 96) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-71 / 48) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (249284 / 81) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-71 / 16) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (249284 / 27) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (7 / 96) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (7 / 16) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ) * (Work.Kernels.jInvariantFun τ)
      + (-85583 / 162) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ)
      + (-885215 / 162) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ)
      + (-885215 / 27) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ)
      + (-11351920 / 9) * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ)
      + (-11351920 / 3) * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ)
      + -988 * ((z : ℂ)) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.E2Fun τ) * (τ : ℂ)
      + -2964 * ((z : ℂ)) ^ 2 * (Real.pi : ℂ) * ((Work.Kernels.E4Fun τ)) ^ 3
      + (1 / 8) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-1 / 4) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (225118 / 27) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-3 / 4) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (225118 / 9) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (1 / 8) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (3 / 4) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ) * (Work.Kernels.jInvariantFun τ)
      + (-2588 / 27) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ)
      + (-2480 / 27) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ)
      + (-4960 / 9) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ)
      + (-36236320 / 9) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ)
      + (-36236320 / 3) * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ)
      + 1084 * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.E2Fun τ) * (τ : ℂ)
      + 3252 * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * ((Work.Kernels.E4Fun τ)) ^ 3
      + (4 / 3) * ((z : ℂ)) ^ 2 * S0z z * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.E2Fun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + 4 * ((z : ℂ)) ^ 2 * S0z z * (Real.pi : ℂ) * ((Work.Kernels.E4Fun τ)) ^ 3 * (Work.Kernels.jInvariantFun τ)
      + (-67 / 96) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-1 / 32) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (-3 / 16) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ) * (Work.Kernels.jInvariantFun τ)
      + (1 / 16) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (-8798 / 81) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ) * (Work.Kernels.jInvariantFun τ)
      + (3 / 16) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (-8798 / 27) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (-803065 / 162) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.E6Fun τ) * (τ : ℂ)
      + (3695 / 162) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * ((Work.Kernels.E2Fun τ)) ^ 2 * (τ : ℂ)
      + (3695 / 27) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.E2Fun τ)
      + (413840 / 9) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * Complex.I * ((Real.pi : ℂ)) ^ 2 * (Work.Kernels.E2Fun τ) * (Work.Kernels.DeltaFun τ) * (τ : ℂ)
      + (413840 / 3) * ((z : ℂ)) ^ 2 * (S0z z) ^ 2 * (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ)

def Bracket24E5 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (3826289664 / 7) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ)
      + -635664 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ)
      + 1352760 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ)
      + (27319 / 24) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + (-25015 / 24) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ) * (Work.Kernels.jInvariantFun τ)
      + -1290832 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * (Work.Kernels.jInvariantFun τ)
      + (-1 / 6) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * ((Work.Kernels.E4Fun τ)) ^ 2 * (Work.Kernels.psi4 ℓ τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + (1 / 6) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) * (Work.Kernels.E6Fun τ) * (Work.Kernels.psi2 ℓ τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2
      + -192 * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.DeltaFun τ) * ((Work.Kernels.jInvariantFun τ)) ^ 2

/-- **The `E³`-coefficient bound**: `‖B_3‖ = O(‖q(τ)‖^{1/2}(scale τ)^N(1+t)^M)`. -/
def Bracket24E3Bound (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Bracket24E3 ℓ τ z‖
        ≤ C * (‖Work.Kernels.qParamFun τ‖) ^ (1 / 2 : ℝ) * (Work.Kernels.scale τ) ^ N
            * (1 + t) ^ M

/-- **The `E⁴`-coefficient bound**: `‖B_4‖ = O((scale τ)^N(1+t)^M)`. -/
def Bracket24E4Bound (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Bracket24E4 ℓ τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M

/-- **The `E⁵`-coefficient bound**: `‖B_5‖ = O(‖q(τ)‖^{-1/2}(scale τ)^N(1+t)^M)`. -/
def Bracket24E5Bound (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Bracket24E5 ℓ τ z‖
        ≤ C * ((‖Work.Kernels.qParamFun τ‖) ^ (1 / 2 : ℝ))⁻¹ * (Work.Kernels.scale τ) ^ N
            * (1 + t) ^ M

end

end Work.Asymptotics.KhatE1
