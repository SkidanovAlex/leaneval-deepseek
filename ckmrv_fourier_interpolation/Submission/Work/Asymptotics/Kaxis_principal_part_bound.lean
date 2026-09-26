/-
# The principal part of the CKMRV kernel at the translate poles on the bad lines

This file proves `Work.Asymptotics.Kaxis_principal_part_bound`: for `s₀ > 0`, `n = ±1` and
`τ` near the "bad line" point `n + i s₀`, the value `K(τ, it)` of the CKMRV kernel on the
imaginary axis differs from its principal part `(n/2π)/(it - (τ - n))` at the translate pole
`z₀ = τ - n` by a bounded amount, uniformly in `τ`, `n` and `t`.

## Structure of the proof

Write `z₀ = τ - n` and `w = S • z₀ = -1/z₀`.  Off the coincidence set
(`j τ ≠ j z`) the master identity `Work.Asymptotics.Kfun_mul_slope_eq_AfunFun` gives

  `K(τ,z) = -M(z) / ((j z - j z₀)(z - z₀))`,

where `M(z) = AfunFun τ z · (z - z₀) + (n/2π)(j z - j z₀)` is holomorphic in `z`.  The value
identity `AfunFun_vadd_int` at the translate pole `z = z₀ = τ - n` shows `M(z₀) = 0`, and the
S-vanishing `AfunFun_S_vadd_zero` shows `M(w) = 0`.

* Off the elliptic point (`s₀ ≠ 1`) the difference quotient of `j` is bounded below near
  `i s₀` (`Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general`), and `M` has a
  double zero at `z₀`; hence `K - (n/2π)/(· - z₀)` is bounded.
* For `s₀ = 1` the two coincidence branches `z₀` and `w` merge at `i` and the lower bound on
  `j` degenerates; the two-branch bound `j_lower_I` and the vanishing of `M` at both `z₀` and
  `w` give the bound instead.  The single degenerate parameter `τ = n + i` (`z₀ = w = i`, where
  `j'(i) = 0`) is handled by a limiting argument along `τ = n + i(1 + 1/k)`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Residues.KPlusClear_TS
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Residues.AfunPlus_neg_one
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.lipschitz_jInvariantFun_local
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Kernels.LogLambda.LambdaLaws

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open Filter
open scoped Topology
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

/-! ## 0. Notation -/

lemma vadd_neg_vadd_cancel (n : ℤ) (τ : ℍ) : ((n : ℝ) +ᵥ ((-(n : ℝ)) +ᵥ τ)) = τ := by
  rw [← add_vadd]
  have h : (n : ℝ) + (-(n : ℝ)) = 0 := by ring
  rw [h, zero_vadd]

lemma coe_neg_vadd (n : ℤ) (τ : ℍ) :
    (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := by
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

lemma jInvariantFun_neg_vadd_int (n : ℤ) (hn : n = 1 ∨ n = -1) (τ : ℍ) :
    jInvariantFun ((-(n : ℝ)) +ᵥ τ) = jInvariantFun τ :=
  jInvariantFun_neg_vadd τ n hn

/-! ## 1. The value identity at the translate pole -/

/-- `AfunFun ℓ d (n + z) z = -(n/2π) j'(z)` for `n = ±1`: the value identity at the translate
pole `z = τ - n` of the kernel. -/
lemma AfunFun_vadd_int_of (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (n : ℤ)
    (hn : n = 1 ∨ n = -1) (z : ℍ) :
    AfunFun ℓ d ((n : ℝ) +ᵥ z) z
      = -((n : ℂ) / (2 * (Real.pi : ℂ))) * Work.Residues.jprime z := by
  rcases hn with rfl | rfl
  · have h : (((1 : ℤ) : ℝ)) = (1 : ℝ) := by norm_num
    rw [h, AfunFun_vadd_one ℓ d hd z]
    norm_num
  · have h2 := AfunFun_neg_vadd ℓ d hd ((-1 : ℝ) +ᵥ z) (-1) (Or.inr rfl)
      (fun w => Work.Residues.AfunPlus_neg_one d hd w)
      (fun w => Work.Residues.AfunMinus_neg_one ℓ d hd w)
    rw [show (-(-1 : ℤ) : ℝ) = (1 : ℝ) by norm_num] at h2
    rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z from by rw [← add_vadd]; norm_num] at h2
    rw [show ((((-1 : ℤ) : ℝ))) = (-1 : ℝ) by norm_num]
    exact h2

/-! ## 2. The S-vanishing of the cleared value function -/

/-- `(T-I)²` kills `τ ↦ K_+^{clear}(τ,z)`. -/
lemma KPlusClear_T2op (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun σ : ℍ => KPlusClear d σ z) = 0 := by
  have hUp : ∀ (σ : ℍ) (i j : Fin 3),
      UpsilonPlusClear d ((1 : ℝ) +ᵥ σ) z i j = UpsilonPlusClear d σ z i j := by
    intro σ i j
    simp only [UpsilonPlusClear]
    split_ifs with h8 h24 <;>
      simp only [Work.Residues.AfunMinusNegOne.PiMatDelta_vadd_one,
        Work.Kernels.KernelFacts.jInvariantFun_vadd_one]
  have hdec : (fun σ : ℍ => KPlusClear d σ z)
      = ∑ i : Fin 3, (fun σ : ℍ => phiVec σ i *
          (∑ j : Fin 3, UpsilonPlusClear d σ z i j * phitVec z j)) := by
    funext σ
    simp only [KPlusClear, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hdec]
  refine T2op_sum Finset.univ (fun i _ => ?_)
  refine T2op_mul_of (KernelFacts.phiVec_T2 i) ?_
  intro σ
  exact Finset.sum_congr rfl (fun j _ => by rw [hUp])

/-- If `(T-I)² N = 0` and `G` is `T`-periodic, then `(T-I)²(N/G) = 0`. -/
lemma T2op_div_of {N G : ℍ → ℂ} (hN : T2op N = 0)
    (hG : ∀ τ : ℍ, G ((1 : ℝ) +ᵥ τ) = G τ) : T2op (fun τ : ℍ => N τ / G τ) = 0 := by
  ext τ
  have h0 := congr_fun hN τ
  have h2 : G ((2 : ℝ) +ᵥ τ) = G τ := by
    rw [vadd_one_add_one, hG ((1 : ℝ) +ᵥ τ), hG τ]
  simp only [T2op, Pi.zero_apply] at h0
  simp only [T2op, Pi.zero_apply, h2, hG τ, div_eq_mul_inv]
  linear_combination (G τ)⁻¹ * h0

/-- `(T-I)²` kills `τ ↦ AfunFun ℓ d τ z`. -/
lemma T2op_AfunFun_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun τ : ℍ => AfunFun ℓ d τ z) = 0 := by
  have hN : T2op (fun τ : ℍ => KPlusClear d τ z + KMinusClear ℓ d τ z) = 0 :=
    T2op_add (KPlusClear_T2op d hd z) (Work.Residues.AfunMinusNegOne.KMinusClear_T2 ℓ d hd z)
  set G : ℍ → ℂ := fun τ => 2 * (DeltaFun τ * DeltaFun z ^ Work.Residues.dpow d) with hGdef
  have hG : ∀ τ : ℍ, G ((1 : ℝ) +ᵥ τ) = G τ := by
    intro τ
    simp only [hGdef, KernelFacts.DeltaFun_vadd_one]
  have h := T2op_div_of hN hG
  have heq : (fun τ : ℍ => AfunFun ℓ d τ z)
      = (fun τ : ℍ => (KPlusClear d τ z + KMinusClear ℓ d τ z) / G τ) := by
    funext τ
    rw [AfunFun, Work.Residues.AfunPlus, Work.Residues.AfunMinus, hGdef]
    ring
  rw [heq]
  exact h

/-- **The S-vanishing.**  For `n = ±1` and `σ ∈ ℍ`, the cleared value function vanishes at the
`S`-translate: `AfunFun ℓ d (n + σ) (S • σ) = 0`. -/
lemma AfunFun_S_vadd_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℤ) (hn : n = 1 ∨ n = -1) (σ : ℍ) :
    AfunFun ℓ d ((n : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
  have hS : ModularGroup.S • (ModularGroup.S • σ) = σ := KL.S_smul_S_smul' σ
  have hplus1 : KPlusClear d ((1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
    have hh := Work.Residues.KPlusClear_TS d hd (ModularGroup.S • σ)
    rwa [hS] at hh
  have hminus1 : KMinusClear ℓ d ((1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
    have hh := Work.Residues.KMinusClear_TS ℓ d hd (ModularGroup.S • σ)
    rwa [hS] at hh
  have hplus0 : KPlusClear d σ (ModularGroup.S • σ) = 0 := by
    have hh := (Work.Asymptotics.KClear_S_vanishing ℓ d hd (ModularGroup.S • σ)).1
    rwa [hS] at hh
  have hminus0 : KMinusClear ℓ d σ (ModularGroup.S • σ) = 0 := by
    have hh := (Work.Asymptotics.KClear_S_vanishing ℓ d hd (ModularGroup.S • σ)).2
    rwa [hS] at hh
  have hA0 : AfunFun ℓ d σ (ModularGroup.S • σ) = 0 := by
    rw [AfunFun, Work.Residues.AfunPlus, Work.Residues.AfunMinus, hplus0, hminus0]
    ring
  have hA1 : AfunFun ℓ d ((1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
    rw [AfunFun, Work.Residues.AfunPlus, Work.Residues.AfunMinus, hplus1, hminus1]
    ring
  have hT2 := congr_fun (T2op_AfunFun_fst ℓ d hd (ModularGroup.S • σ)) ((-1 : ℝ) +ᵥ σ)
  simp only [T2op, Pi.zero_apply] at hT2
  have h1 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ σ) = (1 : ℝ) +ᵥ σ := by
    rw [← add_vadd]; norm_num
  have h2 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ σ) = σ := by
    rw [← add_vadd]; norm_num
  rw [h1, h2, hA1, hA0] at hT2
  have hAneg : AfunFun ℓ d ((-1 : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
    simpa using hT2
  rcases hn with h | h
  · subst h
    rw [show (((1 : ℤ) : ℝ)) = (1 : ℝ) by norm_num]
    exact hA1
  · subst h
    rw [show (((-1 : ℤ) : ℝ)) = (-1 : ℝ) by norm_num]
    exact hAneg

/-! ## 3. Uniform bounds for `AfunFun` near the bad lines -/

/-- `AfunFun` is uniformly bounded on a neighbourhood of the two bad-line points `n + i s₀`
(`n = ±1`): a compactness consequence of its joint continuity. -/
lemma exists_bound_AfunFun_badline (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ 0 ≤ C ∧
      ∀ (τ : ℍ) (n : ℤ) (z : ℍ), (n = 1 ∨ n = -1) →
        |τ.re - (n : ℝ)| < δ → |τ.im - s₀| < δ →
        ‖(z : ℂ) - Complex.I * (s₀ : ℂ)‖ ≤ r → ‖AfunFun ℓ d τ z‖ ≤ C := by
  have hs2 : 0 < s₀ / 2 := by linarith
  have hs4 : 0 < s₀ / 4 := by linarith
  set K : Set ℂ := Metric.closedBall ((1 : ℂ) + Complex.I * (s₀ : ℂ)) (s₀ / 2) ∪
      Metric.closedBall ((-1 : ℂ) + Complex.I * (s₀ : ℂ)) (s₀ / 2) with hKdef
  set Z : Set ℂ := Metric.closedBall (Complex.I * (s₀ : ℂ)) (s₀ / 4) with hZdef
  have hK : IsCompact K := (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
  have hZ : IsCompact Z := isCompact_closedBall _ _
  have himK : ∀ u ∈ K, 0 < u.im := by
    intro u hu
    rcases hu with hu | hu
    · have h1 : ‖u - ((1 : ℂ) + Complex.I * (s₀ : ℂ))‖ ≤ s₀ / 2 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      have h2 : |u.im - s₀| ≤ s₀ / 2 := by
        have h3 : (u - ((1 : ℂ) + Complex.I * (s₀ : ℂ))).im = u.im - s₀ := by simp
        calc |u.im - s₀| = |(u - ((1 : ℂ) + Complex.I * (s₀ : ℂ))).im| := by rw [h3]
          _ ≤ ‖u - ((1 : ℂ) + Complex.I * (s₀ : ℂ))‖ := Complex.abs_im_le_norm _
          _ ≤ s₀ / 2 := h1
      have h4 := (abs_le.mp h2).1
      linarith
    · have h1 : ‖u - ((-1 : ℂ) + Complex.I * (s₀ : ℂ))‖ ≤ s₀ / 2 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      have h2 : |u.im - s₀| ≤ s₀ / 2 := by
        have h3 : (u - ((-1 : ℂ) + Complex.I * (s₀ : ℂ))).im = u.im - s₀ := by simp
        calc |u.im - s₀| = |(u - ((-1 : ℂ) + Complex.I * (s₀ : ℂ))).im| := by rw [h3]
          _ ≤ ‖u - ((-1 : ℂ) + Complex.I * (s₀ : ℂ))‖ := Complex.abs_im_le_norm _
          _ ≤ s₀ / 2 := h1
      have h4 := (abs_le.mp h2).1
      linarith
  have himZ : ∀ u ∈ Z, 0 < u.im := by
    intro u hu
    have h1 : ‖u - Complex.I * (s₀ : ℂ)‖ ≤ s₀ / 4 := by
      rw [hZdef] at hu
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have h2 : |u.im - s₀| ≤ s₀ / 4 := by
      have h3 : (u - Complex.I * (s₀ : ℂ)).im = u.im - s₀ := by simp
      calc |u.im - s₀| = |(u - Complex.I * (s₀ : ℂ)).im| := by rw [h3]
        _ ≤ ‖u - Complex.I * (s₀ : ℂ)‖ := Complex.abs_im_le_norm _
        _ ≤ s₀ / 4 := h1
    have h4 := (abs_le.mp h2).1
    linarith
  have hofK : ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) K :=
    continuousOn_ofComplex_im_pos.mono (fun z hz => himK z hz)
  have hofZ : ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) Z :=
    continuousOn_ofComplex_im_pos.mono (fun z hz => himZ z hz)
  have hpair : ContinuousOn (fun p : ℂ × ℂ =>
      (UpperHalfPlane.ofComplex p.1, UpperHalfPlane.ofComplex p.2)) (K ×ˢ Z) :=
    (hofK.comp continuous_fst.continuousOn (fun p hp => hp.1)).prodMk
      (hofZ.comp continuous_snd.continuousOn (fun p hp => hp.2))
  obtain ⟨C₀, hC₀⟩ := (hK.prod hZ).exists_bound_of_continuousOn
    ((continuous_AfunFun ℓ d).continuousOn.comp hpair (fun p _ => Set.mem_univ _))
  refine ⟨s₀ / 4, s₀ / 4, max C₀ 0, hs4, hs4, le_max_right _ _, ?_⟩
  intro τ n z hn hτre hτim hz
  have hτK : (τ : ℂ) ∈ K := by
    rcases hn with h | h
    · left
      have h5 : |τ.re - (1 : ℝ)| < s₀ / 4 := by
        rw [h] at hτre
        simpa using hτre
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h4 : (τ : ℂ) - ((1 : ℂ) + Complex.I * (s₀ : ℂ))
          = ((τ.re - 1 : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re,
            UpperHalfPlane.coe_im] <;> ring
      rw [h4]
      have h6 := norm_le_re_im (τ.re - 1) (τ.im - s₀)
      linarith
    · right
      have h5 : |τ.re - (-1 : ℝ)| < s₀ / 4 := by
        rw [h] at hτre
        simpa using hτre
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h4 : (τ : ℂ) - ((-1 : ℂ) + Complex.I * (s₀ : ℂ))
          = ((τ.re - (-1) : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re,
            UpperHalfPlane.coe_im] <;> ring
      rw [h4]
      have h6 := norm_le_re_im (τ.re - (-1)) (τ.im - s₀)
      linarith
  have hzZ : (z : ℂ) ∈ Z := by
    rw [hZdef]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hb := hC₀ ((τ : ℂ), (z : ℂ)) ⟨hτK, hzZ⟩
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at hb
  exact le_trans hb (le_max_left _ _)

/-! ## 4. The auxiliary holomorphic function `M` and its vanishing orders -/

/-- The chart version of the auxiliary function
`M(z) = AfunFun τ z · (z - z₀) + (n/2π)(j z - j z₀)` with `z₀ = τ - n`. -/
def Mchart (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (n : ℤ) : ℂ → ℂ :=
  fun u => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) * (u - ((τ : ℂ) - (n : ℂ)))
    + ((n : ℂ) / (2 * (Real.pi : ℂ)))
      * (jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun ((-(n : ℝ)) +ᵥ τ))

lemma Mchart_ofComplex (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (n : ℤ) (z : ℍ) :
    Mchart ℓ d τ n (z : ℂ) = AfunFun ℓ d τ z * ((z : ℂ) - ((τ : ℂ) - (n : ℂ)))
      + ((n : ℂ) / (2 * (Real.pi : ℂ)))
        * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ)) := by
  simp only [Mchart, UpperHalfPlane.ofComplex_apply]

lemma differentiableOn_Mchart (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (n : ℤ) :
    DifferentiableOn ℂ (Mchart ℓ d τ n) {u : ℂ | 0 < u.im} := by
  have hA : DifferentiableOn ℂ (fun u : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := fun w : ℍ => AfunFun ℓ d τ w)).mp
      (mdifferentiable_AfunFun_snd ℓ d hd τ)
  have hJ : DifferentiableOn ℂ (fun u : ℂ => jInvariantFun (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := jInvariantFun)).mp mdifferentiable_jInvariantFun
  refine (hA.mul ?_).add ((hJ.sub (differentiableOn_const _)).const_mul _)
  exact (differentiableOn_id.sub (differentiableOn_const _))

lemma Mchart_self_zero (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (n : ℤ) :
    Mchart ℓ d τ n ((τ : ℂ) - (n : ℂ)) = 0 := by
  have hz : UpperHalfPlane.ofComplex ((τ : ℂ) - (n : ℂ)) = ((-(n : ℝ)) +ᵥ τ) := by
    rw [← coe_neg_vadd n τ]
    exact UpperHalfPlane.ofComplex_apply _
  simp only [Mchart, hz, sub_self, mul_zero, add_zero]

lemma deriv_Mchart_self_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    deriv (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ)) = 0 := by
  set z₀ : ℍ := (-(n : ℝ)) +ᵥ τ with hz₀
  have hz₀c : (z₀ : ℂ) = (τ : ℂ) - (n : ℂ) := by rw [hz₀]; exact coe_neg_vadd n τ
  set zc : ℂ := (τ : ℂ) - (n : ℂ) with hzc
  have hzcim : 0 < zc.im := by
    rw [← hz₀c, UpperHalfPlane.coe_im]; exact z₀.im_pos
  have hopen : {u : ℂ | 0 < u.im} ∈ 𝓝 zc :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzcim
  have hAdiff : DifferentiableAt ℂ (fun u : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u)) zc :=
    ((UpperHalfPlane.mdifferentiable_iff (f := fun w : ℍ => AfunFun ℓ d τ w)).mp
      (mdifferentiable_AfunFun_snd ℓ d hd τ)).differentiableAt hopen
  have hJdiff : DifferentiableAt ℂ (fun u : ℂ => jInvariantFun (UpperHalfPlane.ofComplex u)) zc :=
    ((UpperHalfPlane.mdifferentiable_iff (f := jInvariantFun)).mp
      mdifferentiable_jInvariantFun).differentiableAt hopen
  have h1 : HasDerivAt (fun u : ℂ =>
      AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) * (u - zc))
      (AfunFun ℓ d τ (UpperHalfPlane.ofComplex zc)) zc := by
    have h := hAdiff.hasDerivAt.mul ((hasDerivAt_id zc).sub_const zc)
    simp only [Pi.mul_apply, id_eq] at h
    have hv : deriv (fun u : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u)) zc * (zc - zc)
        + AfunFun ℓ d τ (UpperHalfPlane.ofComplex zc) * 1
        = AfunFun ℓ d τ (UpperHalfPlane.ofComplex zc) := by ring
    rw [hv] at h
    exact h
  have h2 : HasDerivAt (fun u : ℂ => ((n : ℂ) / (2 * (Real.pi : ℂ))) *
      (jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun z₀))
      (((n : ℂ) / (2 * (Real.pi : ℂ))) *
        deriv (fun u : ℂ => jInvariantFun (UpperHalfPlane.ofComplex u)) zc) zc :=
    (hJdiff.hasDerivAt.sub_const _).const_mul _
  have hsum : HasDerivAt (Mchart ℓ d τ n)
      (AfunFun ℓ d τ (UpperHalfPlane.ofComplex zc) + ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        deriv (fun u : ℂ => jInvariantFun (UpperHalfPlane.ofComplex u)) zc) zc := by
    rw [show Mchart ℓ d τ n = fun u : ℂ =>
      AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) * (u - zc)
        + ((n : ℂ) / (2 * (Real.pi : ℂ))) *
          (jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun z₀) from by
      funext u; simp only [Mchart, hzc, hz₀]]
    exact h1.add h2
  rw [hsum.deriv, hzc]
  have hocc : UpperHalfPlane.ofComplex zc = z₀ := by
    rw [← hz₀c]; exact UpperHalfPlane.ofComplex_apply z₀
  rw [hocc]
  have hder : deriv (fun u : ℂ => jInvariantFun (UpperHalfPlane.ofComplex u)) zc
      = Work.Residues.jprime z₀ := by
    rw [← hz₀c]
    exact deriv_jInvariantFun_ofComplex z₀
  rw [hder]
  have hval : AfunFun ℓ d τ z₀ = -((n : ℂ) / (2 * (Real.pi : ℂ))) * Work.Residues.jprime z₀ := by
    have h := AfunFun_vadd_int_of ℓ d hd n hn z₀
    rwa [show ((n : ℝ) +ᵥ z₀) = τ from by rw [hz₀]; exact vadd_neg_vadd_cancel n τ] at h
  rw [hval]
  ring

/-! ## 5. The double-zero bound for `M` -/

/-- **The auxiliary function has a double zero at the pole.**  Near the bad line the bound
`‖M(z)‖ ≤ C ‖z - z₀‖²` holds uniformly in `τ`. -/
lemma M_double_zero_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ 0 ≤ C ∧
      ∀ (τ : ℍ) (n : ℤ) (z : ℍ), (n = 1 ∨ n = -1) →
        |τ.re - (n : ℝ)| < δ → |τ.im - s₀| < δ →
        ‖(z : ℂ) - Complex.I * (s₀ : ℂ)‖ < r →
        ‖AfunFun ℓ d τ z * ((z : ℂ) - ((τ : ℂ) - (n : ℂ)))
            + ((n : ℂ) / (2 * (Real.pi : ℂ)))
              * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ))‖
          ≤ C * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2 := by
  obtain ⟨δ₁, r₁, C₁, hδ₁, hr₁, hC₁, hb₁⟩ := exists_bound_AfunFun_badline ℓ d hd hs₀
  obtain ⟨r_L, L, hr_L, hL, hlip⟩ := lipschitz_jInvariantFun_local (imagAxis s₀ hs₀)
  have hs8 : 0 < s₀ / 8 := by linarith
  set RJ : ℝ := min (min (r₁ / 4) (r_L / 4)) (min 1 (s₀ / 8)) / 8 with hRJ
  have hRJpos : 0 < RJ := by
    rw [hRJ]
    exact div_pos (lt_min (lt_min (by linarith) (by linarith)) (lt_min one_pos hs8)) (by norm_num)
  have hRJ1 : RJ ≤ 1 := by
    rw [hRJ]
    have h := le_trans (min_le_right (min (r₁ / 4) (r_L / 4)) (min 1 (s₀ / 8)))
      (min_le_left 1 (s₀ / 8))
    linarith
  have hRJs : RJ ≤ s₀ / 8 := by
    rw [hRJ]
    have h := le_trans (min_le_right (min (r₁ / 4) (r_L / 4)) (min 1 (s₀ / 8)))
      (min_le_right 1 (s₀ / 8))
    linarith
  have hRJr₁ : RJ ≤ r₁ / 32 := by
    rw [hRJ]
    have h := le_trans (min_le_left (min (r₁ / 4) (r_L / 4)) (min 1 (s₀ / 8)))
      (min_le_left (r₁ / 4) (r_L / 4))
    linarith
  have hRJrL : RJ ≤ r_L / 32 := by
    rw [hRJ]
    have h := le_trans (min_le_left (min (r₁ / 4) (r_L / 4)) (min 1 (s₀ / 8)))
      (min_le_right (r₁ / 4) (r_L / 4))
    linarith
  set R : ℝ := 2 * RJ with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  set δ : ℝ := min δ₁ (RJ / 8) / 8 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (lt_min hδ₁ (by linarith)) (by norm_num)
  have hδle₁ : δ ≤ δ₁ := by
    rw [hδdef]
    have h2 : min δ₁ (RJ / 8) ≤ δ₁ := min_le_left _ _
    linarith
  have hδle : δ ≤ RJ / 64 := by
    rw [hδdef]
    have h2 : min δ₁ (RJ / 8) ≤ RJ / 8 := min_le_right _ _
    linarith
  have hCircle : R + 2 * δ ≤ min r₁ r_L := by
    rw [hRdef]
    have h1 : 2 * RJ ≤ r₁ / 16 := by linarith [hRJr₁]
    have h2 : 2 * RJ ≤ r_L / 16 := by linarith [hRJrL]
    have h3 : 2 * δ ≤ RJ / 32 := by linarith [hδle]
    have h4 : 2 * RJ + 2 * δ ≤ min r₁ r_L := by
      by_cases h : r₁ ≤ r_L
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]; linarith
    linarith
  have hSmall : 4 * RJ + 2 * δ < s₀ := by
    have h1 : 4 * RJ ≤ s₀ / 2 := by linarith [hRJs]
    have h2 : 2 * δ ≤ RJ / 32 := by linarith [hδle]
    linarith
  have hCpos : 0 ≤ (C₁ + L / (2 * Real.pi)) / R := by
    have hL2 : 0 ≤ L / (2 * Real.pi) := div_nonneg hL (by positivity)
    exact div_nonneg (by linarith) hRpos.le
  refine ⟨δ, RJ, (C₁ + L / (2 * Real.pi)) / R, hδpos, hRJpos, hCpos, ?_⟩
  intro τ n z hn hτre hτim hz
  set z₀ : ℍ := (-(n : ℝ)) +ᵥ τ with hz₀
  have hz₀c : (z₀ : ℂ) = (τ : ℂ) - (n : ℂ) := coe_neg_vadd n τ
  have hτim_lo : s₀ - δ < τ.im := by
    have h := (abs_lt.mp hτim).1
    linarith
  have hτcim : ((τ : ℂ) - (n : ℂ)).im = τ.im := by simp
  have hnormτ : ‖((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ)‖ < 2 * δ := by
    have h4 : ((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ)
        = ((τ.re - (n : ℝ) : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
    rw [h4]
    have h5 := norm_le_re_im (τ.re - (n : ℝ)) (τ.im - s₀)
    linarith
  -- holomorphy of `Mchart` on the ball of radius `2 * R`
  have hdiff : DifferentiableOn ℂ (Mchart ℓ d τ n) (Metric.ball ((τ : ℂ) - (n : ℂ)) (2 * R)) := by
    refine (differentiableOn_Mchart ℓ d hd τ n).mono ?_
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : |u.im - ((τ : ℂ) - (n : ℂ)).im| ≤ ‖u - ((τ : ℂ) - (n : ℂ))‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (u - ((τ : ℂ) - (n : ℂ)))
    rw [hτcim] at h1
    have h2 : τ.im - 2 * R ≤ u.im := by
      have h := (abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hu))).1
      linarith
    have h3 : 2 * R = 4 * RJ := by rw [hRdef]; ring
    have h4 : s₀ - δ - 4 * RJ ≤ u.im := by linarith [h2, hτim_lo.le]
    have h5 : 0 < s₀ - δ - 4 * RJ := by linarith [hδle, hRJs, hs₀]
    exact lt_of_lt_of_le h5 h4
  -- the circle bound
  have hcirc : ∀ w : ℂ, ‖w - ((τ : ℂ) - (n : ℂ))‖ = R →
      ‖Mchart ℓ d τ n w‖ ≤ (C₁ + L / (2 * Real.pi)) * R := by
    intro w hw
    have hwim : 0 < w.im := by
      have h1 : |w.im - ((τ : ℂ) - (n : ℂ)).im| ≤ ‖w - ((τ : ℂ) - (n : ℂ))‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - ((τ : ℂ) - (n : ℂ)))
      rw [hτcim, hw] at h1
      have h2 : τ.im - R ≤ w.im := by
        have h := (abs_le.mp h1).1
        linarith
      have h4 : s₀ - δ - R ≤ w.im := by linarith [h2, hτim_lo.le]
      have h5 : 0 < s₀ - δ - R := by linarith [hRdef, hRJs, hδle, hs₀]
      exact lt_of_lt_of_le h5 h4
    have hwC : (UpperHalfPlane.ofComplex w : ℂ) = w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwim, UpperHalfPlane.coe_mk]
    have hAnorm : ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)‖ ≤ C₁ := by
      refine hb₁ τ n (UpperHalfPlane.ofComplex w) hn (lt_of_lt_of_le hτre hδle₁)
        (lt_of_lt_of_le hτim hδle₁) ?_
      rw [hwC]
      have h1 : ‖w - Complex.I * (s₀ : ℂ)‖ ≤ ‖w - ((τ : ℂ) - (n : ℂ))‖ +
          ‖((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ)‖ := by
        calc ‖w - Complex.I * (s₀ : ℂ)‖
            = ‖(w - ((τ : ℂ) - (n : ℂ))) + (((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ))‖ := by
              rw [show w - Complex.I * (s₀ : ℂ)
                  = (w - ((τ : ℂ) - (n : ℂ))) + (((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ))
                  from by ring]
          _ ≤ _ := norm_add_le _ _
      rw [hw] at h1
      have h2 : 2 * δ ≤ r₁ / 64 := by linarith [hδle, hRJr₁]
      linarith [hCircle]
    have hJnorm : ‖jInvariantFun (UpperHalfPlane.ofComplex w) - jInvariantFun z₀‖ ≤ L * R := by
      have hx : ((imagAxis s₀ hs₀ : ℍ) : ℂ) = Complex.I * (s₀ : ℂ) := by
        rw [show Complex.I * (s₀ : ℂ) = (s₀ : ℂ) * Complex.I by ring]; rfl
      have hwx : ‖((UpperHalfPlane.ofComplex w : ℍ) : ℂ) - ((imagAxis s₀ hs₀ : ℍ) : ℂ)‖ < r_L := by
        rw [hwC, hx]
        have h1 : ‖w - Complex.I * (s₀ : ℂ)‖ ≤ R + 2 * δ := by
          have h2 : ‖w - Complex.I * (s₀ : ℂ)‖ ≤ ‖w - ((τ : ℂ) - (n : ℂ))‖ +
              ‖((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ)‖ := by
            calc ‖w - Complex.I * (s₀ : ℂ)‖
                = ‖(w - ((τ : ℂ) - (n : ℂ))) + (((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ))‖ := by
                  rw [show w - Complex.I * (s₀ : ℂ)
                      = (w - ((τ : ℂ) - (n : ℂ))) + (((τ : ℂ) - (n : ℂ)) - Complex.I * (s₀ : ℂ))
                      from by ring]
              _ ≤ _ := norm_add_le _ _
          rw [hw] at h2
          linarith
        linarith [hCircle, min_le_right r₁ r_L]
      have hz₀x : ‖((z₀ : ℍ) : ℂ) - ((imagAxis s₀ hs₀ : ℍ) : ℂ)‖ < r_L := by
        rw [hz₀c, hx]
        linarith [hCircle, min_le_right r₁ r_L]
      have h := hlip (UpperHalfPlane.ofComplex w) z₀ hwx hz₀x
      rw [hwC, hz₀c] at h
      rwa [hw] at h
    have h1 : ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex w) * (w - ((τ : ℂ) - (n : ℂ)))
        + ((n : ℂ) / (2 * (Real.pi : ℂ))) *
          (jInvariantFun (UpperHalfPlane.ofComplex w) - jInvariantFun z₀)‖
        ≤ C₁ * R + (1 / (2 * Real.pi)) * (L * R) := by
      have hn2 : ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
        have hn1 : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
        rw [norm_div, hn1]
        have h2 : ‖((2 : ℂ) * (Real.pi : ℂ))‖ = 2 * Real.pi := by
          rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos]
        rw [h2]
      calc ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex w) * (w - ((τ : ℂ) - (n : ℂ)))
            + ((n : ℂ) / (2 * (Real.pi : ℂ))) *
              (jInvariantFun (UpperHalfPlane.ofComplex w) - jInvariantFun z₀)‖
          ≤ ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)‖ * ‖w - ((τ : ℂ) - (n : ℂ))‖
            + ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖ *
              ‖jInvariantFun (UpperHalfPlane.ofComplex w) - jInvariantFun z₀‖ := by
            calc _ ≤ ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex w) * (w - ((τ : ℂ) - (n : ℂ)))‖
                  + ‖((n : ℂ) / (2 * (Real.pi : ℂ))) *
                    (jInvariantFun (UpperHalfPlane.ofComplex w) - jInvariantFun z₀)‖ :=
                  norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul]
        _ ≤ C₁ * R + (1 / (2 * Real.pi)) * (L * R) := by
            rw [hn2, hw]
            exact add_le_add (mul_le_mul_of_nonneg_right hAnorm hRpos.le)
              (mul_le_mul_of_nonneg_left hJnorm (by positivity))
    rw [Mchart]
    calc _ ≤ C₁ * R + (1 / (2 * Real.pi)) * (L * R) := h1
      _ = (C₁ + L / (2 * Real.pi)) * R := by ring
  have hz' : ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ≤ R := by
    have h1 : ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ≤ ‖(z : ℂ) - Complex.I * (s₀ : ℂ)‖ +
        ‖Complex.I * (s₀ : ℂ) - ((τ : ℂ) - (n : ℂ))‖ := by
      calc ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖
          = ‖((z : ℂ) - Complex.I * (s₀ : ℂ)) + (Complex.I * (s₀ : ℂ) - ((τ : ℂ) - (n : ℂ)))‖ := by
            rw [show (z : ℂ) - ((τ : ℂ) - (n : ℂ))
                = ((z : ℂ) - Complex.I * (s₀ : ℂ)) + (Complex.I * (s₀ : ℂ) - ((τ : ℂ) - (n : ℂ)))
                from by ring]
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖Complex.I * (s₀ : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < 2 * δ := by
      rw [norm_sub_rev]
      exact hnormτ
    rw [hRdef]
    have h3 : RJ + 2 * δ ≤ 2 * RJ := by linarith [hδle]
    linarith
  have hmain := norm_le_of_deriv_eq_zero hRpos hdiff (Mchart_self_zero ℓ d τ n)
    (deriv_Mchart_self_zero ℓ d hd τ n hn) hcirc (z : ℂ) hz'
  rw [Mchart_ofComplex] at hmain
  have h4 : R ^ 2 = 4 * RJ ^ 2 := by rw [hRdef]; ring
  rw [h4] at hmain
  rw [show (C₁ + L / (2 * Real.pi)) * R * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2 / (4 * RJ ^ 2)
      = (C₁ + L / (2 * Real.pi)) / R * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2 from by
    rw [hRdef]; field_simp; ring] at hmain
  exact hmain

/-! ## 6. The two-branch lower bound for `j` near `i` -/

/-- **Two-branch lower bound for `j` near `i`.**  `j u - j v` dominates the product of the two
distances to the coincidence branches `v` and `S • v` of `v`. -/
lemma j_lower_I :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ u v : ℍ,
      ‖(u : ℂ) - Complex.I‖ < ρ → ‖(v : ℂ) - Complex.I‖ < ρ →
      c * ‖(u : ℂ) - (v : ℂ)‖ * ‖(u : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖
        ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
  obtain ⟨ρ₃, hρ₃, c₃, hc₃, hb₃⟩ := MiddleRange.exists_lambdaFun_lipschitz UpperHalfPlane.I
  obtain ⟨ρ₄, hρ₄, c₄, hc₄, hb₄⟩ := MiddleRange.exists_j_sub_lower_lambda_near_I
  set ρ : ℝ := min ρ₄ (min ρ₃ (min (ρ₃ / 4) (1 / 2))) with hρdef
  have hρpos : 0 < ρ :=
    lt_min hρ₄ (lt_min hρ₃ (lt_min (by linarith) (by norm_num)))
  refine ⟨ρ, c₄ * c₃ ^ 2, hρpos, by positivity, fun u v hu hv => ?_⟩
  have huρ₄ : ‖(u : ℂ) - Complex.I‖ < ρ₄ := lt_of_lt_of_le hu (min_le_left _ _)
  have hvρ₄ : ‖(v : ℂ) - Complex.I‖ < ρ₄ := lt_of_lt_of_le hv (min_le_left _ _)
  have huρ₃ : ‖(u : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ₃ := by
    rw [UpperHalfPlane.coe_I]
    exact lt_of_lt_of_le hu (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvρ₃ : ‖(v : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ₃ := by
    rw [UpperHalfPlane.coe_I]
    exact lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hv12 : ‖(v : ℂ) - Complex.I‖ < 1 / 2 :=
    lt_of_lt_of_le hv
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hSv : ‖((ModularGroup.S • v : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ₃ := by
    have h := KL.norm_S_sub_I_le' v hv12
    have hv' : ‖(v : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < ρ₃ / 4 := by
      rw [UpperHalfPlane.coe_I]
      exact lt_of_lt_of_le hv
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    linarith
  have hlam1 : c₃ * ‖(u : ℂ) - (v : ℂ)‖ ≤ ‖lambdaFun u - lambdaFun v‖ :=
    hb₃ u v huρ₃ hvρ₃
  have hlS : c₃ * ‖(u : ℂ) - (((ModularGroup.S • v : ℍ)) : ℂ)‖
      ≤ ‖lambdaFun u - lambdaFun (ModularGroup.S • v)‖ :=
    hb₃ u (ModularGroup.S • v) huρ₃ hSv
  have hlSv : lambdaFun u + lambdaFun v - 1
      = lambdaFun u - lambdaFun (ModularGroup.S • v) := by
    rw [Work.Kernels.LogLambda.lambdaFun_S]
    have h := Work.Rigidity.lambdaFun_add_lambdaSFun v
    linear_combination h
  have hJ' : c₄ * ‖lambdaFun u - lambdaFun v‖ * ‖lambdaFun u + lambdaFun v - 1‖
      ≤ ‖jInvariantFun u - jInvariantFun v‖ := hb₄ u v huρ₄ hvρ₄
  calc c₄ * c₃ ^ 2 * ‖(u : ℂ) - (v : ℂ)‖ * ‖(u : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖
      = c₄ * (c₃ * ‖(u : ℂ) - (v : ℂ)‖) * (c₃ * ‖(u : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖) := by
        ring
    _ ≤ c₄ * ‖lambdaFun u - lambdaFun v‖ * ‖lambdaFun u + lambdaFun v - 1‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlam1 hc₄.le) (by rw [hlSv]; exact hlS)
          (by positivity) (by positivity)
    _ ≤ ‖jInvariantFun u - jInvariantFun v‖ := hJ'



/-! ## 7. The two-zero bound for `M` at `s₀ = 1` -/

/-- **The auxiliary function vanishes at the two coincidence branches.**  For `s₀ = 1` and
`z₀ ≠ S • z₀` the bound `‖M(z)‖ ≤ C ‖z - z₀‖² ‖z - S z₀‖` holds uniformly. -/
lemma M_two_zero_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ 0 ≤ C ∧
      ∀ (τ : ℍ) (n : ℤ) (z : ℍ), (n = 1 ∨ n = -1) →
        |τ.re - (n : ℝ)| < δ → |τ.im - 1| < δ →
        ‖(z : ℂ) - Complex.I‖ < r →
        ((-(n : ℝ)) +ᵥ τ) ≠ ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) →
        ‖AfunFun ℓ d τ z * ((z : ℂ) - ((τ : ℂ) - (n : ℂ)))
            + ((n : ℂ) / (2 * (Real.pi : ℂ)))
              * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ))‖
          ≤ C * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2
              * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ)) : ℍ) : ℂ)‖ := by
  obtain ⟨δ₀, r₀, C₀, hδ₀, hr₀, hC₀, hb₀⟩ := M_double_zero_bound ℓ d hd (s₀ := 1) one_pos
  set rr : ℝ := min (min r₀ δ₀) 1 / 32 with hrrdef
  have hrrpos : 0 < rr := by
    rw [hrrdef]
    exact div_pos (lt_min (lt_min hr₀ hδ₀) one_pos) (by norm_num)
  have hrr1 : rr ≤ 1 / 32 := by
    rw [hrrdef]
    have h : min (min r₀ δ₀) 1 ≤ 1 := min_le_right _ _
    linarith
  have hrrr₀ : rr ≤ r₀ / 32 := by
    rw [hrrdef]
    have h : min (min r₀ δ₀) 1 ≤ r₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hrrδ₀ : rr ≤ δ₀ / 32 := by
    rw [hrrdef]
    have h : min (min r₀ δ₀) 1 ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  set δ : ℝ := min (min δ₀ rr) 1 / 32 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (lt_min (lt_min hδ₀ hrrpos) one_pos) (by norm_num)
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδdef]
    have h : min (min δ₀ rr) 1 ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδrr : δ ≤ rr / 32 := by
    rw [hδdef]
    have h : min (min δ₀ rr) 1 ≤ rr := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hδ1 : δ ≤ 1 / 32 := by
    rw [hδdef]
    have h : min (min δ₀ rr) 1 ≤ 1 := min_le_right _ _
    linarith
  have hCpos : 0 ≤ 4 * C₀ / rr := by positivity
  refine ⟨δ, rr / 8, 4 * C₀ / rr, hδpos, by linarith, hCpos, ?_⟩
  intro τ n z hn hτre hτim hz hne
  set z₀ : ℍ := (-(n : ℝ)) +ᵥ τ with hz₀
  have hz₀c : (z₀ : ℂ) = (τ : ℂ) - (n : ℂ) := coe_neg_vadd n τ
  have hzcim : 0 < ((τ : ℂ) - (n : ℂ)).im := by
    have h2 : ((τ : ℂ) - (n : ℂ)).im = τ.im := by simp
    rw [h2]
    have h : -δ < τ.im - 1 := (abs_lt.mp hτim).1
    linarith [hδ1]
  have hz₀I : ‖(z₀ : ℂ) - Complex.I‖ < 2 * δ := by
    rw [hz₀c]
    have h4 : (τ : ℂ) - (n : ℂ) - Complex.I
        = ((τ.re - (n : ℝ) : ℝ) : ℂ) + ((τ.im - 1 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
    rw [h4]
    have h5 := norm_le_re_im (τ.re - (n : ℝ)) (τ.im - 1)
    linarith
  have hz₀im : 1 / 2 ≤ z₀.im := by
    have h2 : ((z₀ : ℂ)).im = τ.im := by rw [hz₀c]; simp
    have h3 : z₀.im = τ.im := by rw [← UpperHalfPlane.coe_im z₀]; exact h2
    rw [h3]
    have h : -δ < τ.im - 1 := (abs_lt.mp hτim).1
    linarith [hδ1]
  -- distance between the two coincidence branches
  have hwdist : ‖((ModularGroup.S • z₀ : ℍ) : ℂ) - (z₀ : ℂ)‖ ≤ 12 * δ := by
    have hwcoe : ((ModularGroup.S • z₀ : ℍ) : ℂ) = -((z₀ : ℂ))⁻¹ := KL.coe_S_smul' z₀
    have hnorm : ‖(z₀ : ℂ)‖ ≥ 1 / 2 := by
      have h2 : ‖Complex.I‖ ≤ ‖Complex.I - (z₀ : ℂ)‖ + ‖(z₀ : ℂ)‖ := by
        calc ‖Complex.I‖ = ‖(Complex.I - (z₀ : ℂ)) + (z₀ : ℂ)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [norm_sub_rev, Complex.norm_I] at h2
      linarith [hz₀I, hδrr]
    have hne0 : (z₀ : ℂ) ≠ 0 := by
      intro h0
      have h1 : ‖(z₀ : ℂ)‖ = 0 := by rw [h0]; simp
      linarith
    have hfac : (z₀ : ℂ) + ((z₀ : ℂ))⁻¹ = ((z₀ : ℂ) ^ 2 + 1) / (z₀ : ℂ) := by
      field_simp
    have hfac2 : (z₀ : ℂ) ^ 2 + 1 = ((z₀ : ℂ) - Complex.I) * ((z₀ : ℂ) + Complex.I) := by
      rw [show ((z₀ : ℂ) - Complex.I) * ((z₀ : ℂ) + Complex.I)
          = (z₀ : ℂ) ^ 2 - Complex.I ^ 2 by ring, Complex.I_sq]
      ring
    have hnum : ‖(z₀ : ℂ) ^ 2 + 1‖ ≤ 2 * δ * (2 + 2 * δ) := by
      rw [hfac2, norm_mul]
      have h2 : ‖(z₀ : ℂ) + Complex.I‖ ≤ 2 + 2 * δ := by
        have h3 : ‖(z₀ : ℂ) + Complex.I‖ ≤ ‖(z₀ : ℂ) - Complex.I‖ + ‖(2 : ℂ) * Complex.I‖ := by
          calc ‖(z₀ : ℂ) + Complex.I‖ = ‖((z₀ : ℂ) - Complex.I) + 2 * Complex.I‖ := by
                rw [show (z₀ : ℂ) + Complex.I = ((z₀ : ℂ) - Complex.I) + 2 * Complex.I from by ring]
            _ ≤ _ := norm_add_le _ _
        have h4 : ‖(2 : ℂ) * Complex.I‖ = 2 := by
          rw [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
        rw [h4] at h3
        linarith
      exact mul_le_mul (le_of_lt hz₀I) h2 (by positivity) (by positivity)
    have hbound2 : ‖(z₀ : ℂ) ^ 2 + 1‖ / ‖(z₀ : ℂ)‖ ≤ 12 * δ := by
      rw [div_le_iff₀ (by linarith [hnorm] : (0 : ℝ) < ‖(z₀ : ℂ)‖)]
      nlinarith [hnum, hδ1, hδpos, hnorm]
    rw [hwcoe, show -((z₀ : ℂ))⁻¹ - (z₀ : ℂ) = -(((z₀ : ℂ) + ((z₀ : ℂ))⁻¹)) from by ring,
      norm_neg, hfac, norm_div]
    exact hbound2
  -- the function `f = M / (· - z₀)` and its two zeros
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun v : ℍ => dslope (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ)) (v : ℂ)) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have h1 : DifferentiableOn ℂ (fun u : ℂ =>
        dslope (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ)) u) {u : ℂ | 0 < u.im} :=
      (Complex.differentiableOn_dslope (s := {u : ℂ | 0 < u.im})
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzcim)).mpr
        (differentiableOn_Mchart ℓ d hd τ n)
    refine h1.congr ?_
    intro u hu
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hu,
      UpperHalfPlane.coe_mk]
  -- the disc bound for `f`
  have hbound : ∀ v : ℍ, ‖(v : ℂ) - (z₀ : ℂ)‖ ≤ rr →
      ‖dslope (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ)) (v : ℂ)‖ ≤ C₀ * rr := by
    intro v hv
    have hvr : ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ≤ rr := by
      rw [hz₀c] at hv
      exact hv
    by_cases hveq : (v : ℂ) = (τ : ℂ) - (n : ℂ)
    · rw [hveq, dslope_self_eq', deriv_Mchart_self_zero ℓ d hd τ n hn, norm_zero]
      exact mul_nonneg hC₀ hrrpos.le
    · have hvI : ‖(v : ℂ) - Complex.I‖ < r₀ := by
        have h2 : ‖(v : ℂ) - Complex.I‖
            ≤ ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ + ‖((τ : ℂ) - (n : ℂ)) - Complex.I‖ := by
          calc ‖(v : ℂ) - Complex.I‖
              = ‖((v : ℂ) - ((τ : ℂ) - (n : ℂ))) + (((τ : ℂ) - (n : ℂ)) - Complex.I)‖ := by
                rw [show (v : ℂ) - Complex.I
                    = ((v : ℂ) - ((τ : ℂ) - (n : ℂ))) + (((τ : ℂ) - (n : ℂ)) - Complex.I)
                    from by ring]
            _ ≤ _ := norm_add_le _ _
        have h5 : ‖((τ : ℂ) - (n : ℂ)) - Complex.I‖ < 2 * δ := by
          rw [← hz₀c]; exact hz₀I
        linarith [hrrr₀, h5]
      have hM := hb₀ τ n v hn (lt_of_lt_of_le hτre hδδ₀) (lt_of_lt_of_le hτim hδδ₀)
        (by simpa using hvI)
      have hM' : ‖AfunFun ℓ d τ v * ((v : ℂ) - ((τ : ℂ) - (n : ℂ)))
            + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (jInvariantFun v - jInvariantFun z₀)‖
          ≤ C₀ * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2 := hM
      have hpos : 0 < ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hveq)
      rw [dslope_of_ne _ hveq, slope_def_field, Mchart_ofComplex ℓ d τ n v,
        Mchart_self_zero ℓ d τ n, sub_zero, norm_div]
      rw [div_le_iff₀ hpos]
      have h3 : C₀ * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2
          ≤ C₀ * rr * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ := by
        have h5 : ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖
            ≤ rr * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ :=
          mul_le_mul_of_nonneg_right hvr (norm_nonneg _)
        calc C₀ * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2
            = C₀ * (‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖) := by
              ring
          _ ≤ C₀ * (rr * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖) :=
              mul_le_mul_of_nonneg_left h5 hC₀
          _ = C₀ * rr * ‖(v : ℂ) - ((τ : ℂ) - (n : ℂ))‖ := by ring
      linarith [hM', h3]
  have hzero : dslope (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ)) ((z₀ : ℂ)) = 0 := by
    rw [hz₀c, dslope_self_eq']
    exact deriv_Mchart_self_zero ℓ d hd τ n hn
  have hzeroS : dslope (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ))
      (((ModularGroup.S • z₀ : ℍ)) : ℂ) = 0 := by
    have hwne : (((ModularGroup.S • z₀ : ℍ)) : ℂ) ≠ (τ : ℂ) - (n : ℂ) := by
      intro h
      apply hne
      refine UpperHalfPlane.ext ?_
      exact hz₀c.trans h.symm
    rw [dslope_of_ne _ hwne, slope_def_field]
    have hS : AfunFun ℓ d τ (ModularGroup.S • z₀) = 0 := by
      have h := AfunFun_S_vadd_zero ℓ d hd n hn z₀
      rwa [show ((n : ℝ) +ᵥ z₀) = τ from by rw [hz₀]; exact vadd_neg_vadd_cancel n τ] at h
    rw [Mchart_ofComplex, Mchart_self_zero, hS, KernelFacts.jInvariantFun_S_smul, sub_self,
      mul_zero, add_zero, sub_zero, zero_mul, zero_div]
  have hmems : ‖((ModularGroup.S • z₀ : ℍ) : ℂ) - (z₀ : ℂ)‖ < rr / 2 := by
    have h2 : 12 * δ ≤ rr / 2 := by linarith [hδrr]
    linarith [hwdist]
  have hmemz : ‖(z : ℂ) - (z₀ : ℂ)‖ < rr / 2 := by
    have h2 : ‖(z : ℂ) - (z₀ : ℂ)‖ ≤ ‖(z : ℂ) - Complex.I‖ + ‖Complex.I - (z₀ : ℂ)‖ := by
      calc ‖(z : ℂ) - (z₀ : ℂ)‖ = ‖((z : ℂ) - Complex.I) + (Complex.I - (z₀ : ℂ))‖ := by
            rw [show (z : ℂ) - (z₀ : ℂ) = ((z : ℂ) - Complex.I) + (Complex.I - (z₀ : ℂ))
              from by ring]
        _ ≤ _ := norm_add_le _ _
    have h3 : ‖Complex.I - (z₀ : ℂ)‖ = ‖(z₀ : ℂ) - Complex.I‖ := norm_sub_rev _ _
    rw [h3] at h2
    linarith [hz₀I, hδrr]
  have hmemc : ‖(z₀ : ℂ) - (z₀ : ℂ)‖ < rr / 2 := by rw [sub_self, norm_zero]; linarith
  have hmain := KL.two_zero_apply hf (c := z₀) (r := rr) (M := C₀ * rr) hrrpos
    (by linarith [hrr1]) (by positivity) hbound (w₁ := z₀) (w₂ := ModularGroup.S • z₀)
    hmemc hmems hne hzero hzeroS z hmemz
  have hMval : AfunFun ℓ d τ z * ((z : ℂ) - ((τ : ℂ) - (n : ℂ)))
      + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (jInvariantFun z - jInvariantFun z₀)
      = ((z : ℂ) - ((τ : ℂ) - (n : ℂ))) • dslope (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ)) (z : ℂ) := by
    rw [← Mchart_ofComplex ℓ d τ n z]
    by_cases hzeq : (z : ℂ) = (τ : ℂ) - (n : ℂ)
    · rw [hzeq, Mchart_self_zero ℓ d τ n, sub_self, zero_smul]
    · rw [dslope_of_ne _ hzeq, slope_def_field, Mchart_self_zero ℓ d τ n, sub_zero,
        smul_eq_mul]
      field_simp
  rw [hMval, norm_smul]
  have hfin : (4 * (C₀ * rr) / rr ^ 2) = 4 * C₀ / rr := by
    field_simp
  have hzz : ‖(z : ℂ) - (z₀ : ℂ)‖ = ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ := by rw [hz₀c]
  calc ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖
        * ‖dslope (Mchart ℓ d τ n) ((τ : ℂ) - (n : ℂ)) (z : ℂ)‖
      ≤ ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ *
          ((4 * (C₀ * rr) / rr ^ 2) * ‖(z : ℂ) - (z₀ : ℂ)‖
            * ‖(z : ℂ) - (((ModularGroup.S • z₀ : ℍ)) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
    _ = 4 * C₀ / rr * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ^ 2
          * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖ := by
        rw [hfin, hzz]
        ring


/-! ## 8. Auxiliary identities for the main theorem -/

/-- The target's principal-part expression is `(n/2π)·(z - z₀)⁻¹` with `z = it`, `z₀ = τ - n`. -/
lemma principal_part_eq (n : ℤ) (t : ℝ) (ht : 0 < t) (τ : ℍ) :
    (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹
      = ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        (((imagAxis t ht : ℍ) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))⁻¹ := by
  have h1 : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  have h2 : (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  rw [h1, h2]
  have hE : (t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ)
      = -Complex.I * ((t : ℂ) * Complex.I - ((τ : ℂ) - (n : ℂ))) := by
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im] <;> ring
  rw [hE, _root_.mul_inv_rev]
  have hIinv : (-Complex.I)⁻¹ = Complex.I := by
    rw [inv_neg, Complex.inv_I]; ring
  rw [hIinv]
  rw [show (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        (((t : ℂ) * Complex.I - (↑τ - ↑n))⁻¹ * Complex.I)
      = ((-Complex.I) * Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        ((t : ℂ) * Complex.I - (↑τ - ↑n))⁻¹ by ring]
  rw [show (-Complex.I) * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I]; ring]
  ring

/-- The master identity in the form `K = -A/(j z - j z₀)` at the translate pole. -/
lemma Kfun_eq_neg_A_div (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (hne : jInvariantFun z ≠ jInvariantFun ((-(n : ℝ)) +ᵥ τ)) :
    Kfun ℓ d τ z
      = -(AfunFun ℓ d τ z) * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ))⁻¹ := by
  have h := Kfun_mul_slope_eq_AfunFun ℓ d hd τ z (by
    rw [← jInvariantFun_neg_vadd τ n hn]
    exact hne.symm)
  rw [← jInvariantFun_neg_vadd τ n hn] at h
  have hne' : jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ) ≠ 0 := sub_ne_zero.mpr hne
  have h2 : Kfun ℓ d τ z * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ))
      = -(AfunFun ℓ d τ z) := by
    have h3 : jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ)
        = -(jInvariantFun ((-(n : ℝ)) +ᵥ τ) - jInvariantFun z) := by ring
    rw [h3, mul_neg, h]
  rw [← h2]
  rw [mul_assoc, mul_inv_cancel₀ hne', mul_one]

/-- The remainder identity: `K - pp = -M / ((j z - j z₀)(z - z₀))`. -/
lemma remainder_eq (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (hne : jInvariantFun z ≠ jInvariantFun ((-(n : ℝ)) +ᵥ τ)) :
    Kfun ℓ d τ z
        - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)))⁻¹
      = -(AfunFun ℓ d τ z * ((z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))
            + ((n : ℂ) / (2 * (Real.pi : ℂ)))
              * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ)))
          / ((jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ))
              * ((z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))) := by
  rw [Kfun_eq_neg_A_div ℓ d hd τ z n hn hne]
  have hne1 : jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ) ≠ 0 := sub_ne_zero.mpr hne
  have hne2 : (z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) ≠ 0 := by
    intro h
    apply hne
    have h2 : z = (-(n : ℝ)) +ᵥ τ := UpperHalfPlane.ext (sub_eq_zero.mp h)
    rw [h2]
  field_simp
  ring

/-- From the bound on `M` (with the two coincidence branches) and the two-branch lower bound on
`‖j z - j z₀‖`, the remainder at the translate pole is bounded. -/
lemma remainder_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) {CB cI : ℝ} (hCB : 0 ≤ CB) (hcI : 0 < cI)
    (hne : jInvariantFun z ≠ jInvariantFun ((-(n : ℝ)) +ᵥ τ))
    (hM : ‖AfunFun ℓ d τ z * ((z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))
          + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ))‖
        ≤ CB * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ ^ 2
            * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖)
    (hlen : cI * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
        * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖
        ≤ ‖jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖) :
    ‖Kfun ℓ d τ z
        - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)))⁻¹‖ ≤ CB / cI := by
  have hne1 : jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ) ≠ 0 := sub_ne_zero.mpr hne
  have hzz : (z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) ≠ 0 := by
    intro h
    apply hne
    have h2 : z = (-(n : ℝ)) +ᵥ τ := UpperHalfPlane.ext (sub_eq_zero.mp h)
    rw [h2]
  rw [remainder_eq ℓ d hd τ z n hn hne]
  simp only [norm_div, norm_neg, norm_mul]
  rw [div_le_iff₀ (by exact mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hzz))]
  have hden : cI * (‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
      * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖)
      ≤ ‖jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ := by
    simpa only [mul_assoc] using hlen
  calc ‖AfunFun ℓ d τ z * ((z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))
        + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ))‖
      ≤ CB * (‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
          * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖)
        * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
        have h1 : CB * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ ^ 2
              * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖
            = CB * (‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
                * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖)
              * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by ring
        rw [← h1]
        exact hM
    _ = (CB / cI) * (cI * (‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
          * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖))
        * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
        field_simp
    _ ≤ (CB / cI) * ‖jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖
        * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hden (div_nonneg hCB hcI.le)) (norm_nonneg _)
    _ = CB / cI * (‖jInvariantFun z - jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖
        * ‖(z : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖) := by ring

/-- **The main theorem.**  The remainder of the CKMRV kernel at the translate pole is bounded
uniformly along the bad lines. -/
theorem Kaxis_principal_part_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (τ : UpperHalfPlane) (n : ℤ) (t : ℝ) (ht : 0 < t),
        (n = 1 ∨ n = -1) → |τ.re - (n : ℝ)| < δ → |τ.im - s₀| < δ →
        |t - τ.im| < 4 * δ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t -
          (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
            ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹‖ ≤ C := by
  obtain ⟨δA, rA, CA, hδA, hrA, hCA, hbA⟩ := M_double_zero_bound ℓ d hd hs₀
  obtain ⟨δB, rB, CB, hδB, hrB, hCB, hbB⟩ := M_two_zero_bound ℓ d hd
  obtain ⟨ρI, cI, hρI, hcI, hbI⟩ := j_lower_I
  rcases eq_or_ne s₀ 1 with rfl | hs1
  · -- ================= s₀ = 1 =================
    set δ : ℝ := min (min δB (min rB ρI)) 1 / 64 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact div_pos (lt_min (lt_min hδB (lt_min hrB hρI)) one_pos) (by norm_num)
    have hδδB : δ ≤ δB := by
      rw [hδdef]
      have h : min (min δB (min rB ρI)) 1 ≤ δB := le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hδrB : δ ≤ rB / 64 := by
      rw [hδdef]
      have h : min (min δB (min rB ρI)) 1 ≤ rB :=
        le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    have hδρI : δ ≤ ρI / 64 := by
      rw [hδdef]
      have h : min (min δB (min rB ρI)) 1 ≤ ρI :=
        le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
    have hCpos : 0 ≤ CB / cI := div_nonneg hCB hcI.le
    -- the direct bound in the nondegenerate case
    have hdirect : ∀ (σ : ℍ) (m : ℤ) (u : ℝ) (hu : 0 < u), (m = 1 ∨ m = -1) →
        |σ.re - (m : ℝ)| < δ → |σ.im - 1| < δ → |u - σ.im| < 8 * δ →
        ((-(m : ℝ)) +ᵥ σ) ≠ ModularGroup.S • ((-(m : ℝ)) +ᵥ σ) →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis u hu) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ u -
          (-Complex.I) * ((m : ℂ) / (2 * (Real.pi : ℂ))) *
            ((u : ℂ) - (σ.im : ℂ) + Complex.I * (((σ.re - (m : ℝ)) : ℝ) : ℂ))⁻¹‖ ≤ CB / cI := by
      intro σ m u hu hm hσre hσim hu4 hndeg hjne
      have hzcoe : ((Work.Kernels.imagAxis u hu : ℍ) : ℂ) = (u : ℂ) * Complex.I := rfl
      have hz₀coe : (((-(m : ℝ)) +ᵥ σ : ℍ) : ℂ) = (σ : ℂ) - (m : ℂ) := coe_neg_vadd m σ
      have hI1 : ‖((Work.Kernels.imagAxis u hu : ℍ) : ℂ) - Complex.I‖ = |u - 1| := by
        rw [hzcoe]
        have h5 : (u : ℂ) * Complex.I - Complex.I = ((u - 1 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [h5, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hu1 : |u - 1| ≤ |u - σ.im| + |σ.im - 1| := by
        have h3 : u - 1 = (u - σ.im) + (σ.im - 1) := by ring
        calc |u - 1| = |(u - σ.im) + (σ.im - 1)| := by rw [h3]
          _ ≤ _ := abs_add_le _ _
      have hzI : ‖((Work.Kernels.imagAxis u hu : ℍ) : ℂ) - Complex.I‖ < rB := by
        rw [hI1]; linarith [hσim, hu4, hδrB]
      have hzI' : ‖((Work.Kernels.imagAxis u hu : ℍ) : ℂ) - Complex.I‖ < ρI := by
        rw [hI1]; linarith [hσim, hu4, hδρI]
      have hz₀I : ‖(((-(m : ℝ)) +ᵥ σ : ℍ) : ℂ) - Complex.I‖ < ρI := by
        have h2 : ‖(((-(m : ℝ)) +ᵥ σ : ℍ) : ℂ) - Complex.I‖ < 2 * δ := by
          rw [hz₀coe]
          have h4 : (σ : ℂ) - (m : ℂ) - Complex.I
              = ((σ.re - (m : ℝ) : ℝ) : ℂ) + ((σ.im - 1 : ℝ) : ℂ) * Complex.I := by
            apply Complex.ext <;>
              simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
                Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
                Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
          rw [h4]
          have h5 := norm_le_re_im (σ.re - (m : ℝ)) (σ.im - 1)
          linarith
        linarith [hδρI]
      have hjne' : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis u hu)
          ≠ Work.Kernels.jInvariantFun ((-(m : ℝ)) +ᵥ σ) := by
        intro h
        exact hjne (h.trans (jInvariantFun_neg_vadd σ m hm)).symm
      have hM := hbB σ m (Work.Kernels.imagAxis u hu) hm
        (lt_of_lt_of_le hσre hδδB) (lt_of_lt_of_le hσim hδδB) hzI hndeg
      rw [← hz₀coe] at hM
      have hjlow : cI * ‖((Work.Kernels.imagAxis u hu : ℍ) : ℂ)
            - (((-(m : ℝ)) +ᵥ σ : ℍ) : ℂ)‖
          * ‖((Work.Kernels.imagAxis u hu : ℍ) : ℂ)
              - (((ModularGroup.S • ((-(m : ℝ)) +ᵥ σ) : ℍ)) : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis u hu)
              - Work.Kernels.jInvariantFun ((-(m : ℝ)) +ᵥ σ)‖ :=
        hbI (Work.Kernels.imagAxis u hu) ((-(m : ℝ)) +ᵥ σ) hzI' hz₀I
      have htarget : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ u -
          (-Complex.I) * ((m : ℂ) / (2 * (Real.pi : ℂ))) *
            ((u : ℂ) - (σ.im : ℂ) + Complex.I * (((σ.re - (m : ℝ)) : ℝ) : ℂ))⁻¹
          = Kfun ℓ d σ (Work.Kernels.imagAxis u hu)
            - ((m : ℂ) / (2 * (Real.pi : ℂ)))
              * ((((Work.Kernels.imagAxis u hu : ℍ) : ℂ)
                  - (((-(m : ℝ)) +ᵥ σ : ℍ) : ℂ)))⁻¹ := by
        rw [principal_part_eq m u hu σ, Kaxis, dif_pos hu]
      rw [htarget]
      exact remainder_bound ℓ d hd σ (Work.Kernels.imagAxis u hu) m hm hCB hcI hjne' hM hjlow
    -- the degenerate case, where `z₀ = S • z₀ = i`, by a punctured-neighbourhood limit
    have hdegen : ∀ (σ : ℍ) (m : ℤ) (u : ℝ) (hu : 0 < u), (m = 1 ∨ m = -1) →
        |σ.re - (m : ℝ)| < δ → |σ.im - 1| < δ → |u - σ.im| < 4 * δ →
        ((-(m : ℝ)) +ᵥ σ) = ModularGroup.S • ((-(m : ℝ)) +ᵥ σ) →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis u hu) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ u -
          (-Complex.I) * ((m : ℂ) / (2 * (Real.pi : ℂ))) *
            ((u : ℂ) - (σ.im : ℂ) + Complex.I * (((σ.re - (m : ℝ)) : ℝ) : ℂ))⁻¹‖ ≤ CB / cI := by
      intro σ m u hu hm hσre hσim hu4 hdeg hjne
      have hz₀I : ((-(m : ℝ)) +ᵥ σ) = UpperHalfPlane.I := KL.S_fixpoint' hdeg.symm
      have hσ_eq : σ = (m : ℝ) +ᵥ UpperHalfPlane.I := by
        have h := congrArg (fun w => (m : ℝ) +ᵥ w) hz₀I
        simpa only [vadd_neg_vadd_cancel] using h
      have hcoec : (σ : ℂ) = (m : ℂ) + Complex.I := by
        rw [hσ_eq, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_I]
        push_cast
        ring
      have hσre_eq : σ.re = (m : ℝ) := by
        rw [← UpperHalfPlane.coe_re, hcoec]; simp
      have hσim_eq : σ.im = 1 := by
        rw [← UpperHalfPlane.coe_im, hcoec]; simp
      have hu_ne : u ≠ 1 := by
        intro h1
        refine hjne ?_
        rw [hσ_eq, KL.imagAxis_eq_I hu h1]
        rcases hm with hm1 | hm1
        · rw [hm1]
          simpa using (jInvariantFun_neg_vadd UpperHalfPlane.I (-1) (Or.inr rfl))
        · rw [hm1]
          simpa using (jInvariantFun_neg_vadd UpperHalfPlane.I (1) (Or.inl rfl))
      rw [hσim_eq] at hu4
      let Φ : ℍ → ℝ := fun σ' => ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ' u -
          (-Complex.I) * ((m : ℂ) / (2 * (Real.pi : ℂ))) *
            ((u : ℂ) - (σ'.im : ℂ) + Complex.I * (((σ'.re - (m : ℝ)) : ℝ) : ℂ))⁻¹‖
      have hcont : ContinuousAt Φ σ := by
        apply ContinuousAt.norm
        apply ContinuousAt.sub
        · have hfun : (fun σ' : ℍ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ' u)
              = (fun σ' : ℍ => Kfun ℓ d σ' (Work.Kernels.imagAxis u hu)) := by
            funext σ'; simp only [Work.Kernels.Kaxis, dif_pos hu]
          rw [hfun]
          exact (Work.Residues.mdifferentiableAt_Kfun_fst ℓ d hd
            (Work.Kernels.imagAxis u hu) σ hjne).continuousAt
        · have hinner : ContinuousAt (fun σ' : ℍ =>
              (u : ℂ) - (σ'.im : ℂ) + Complex.I * (((σ'.re - (m : ℝ)) : ℝ) : ℂ)) σ := by
            fun_prop
          have hinner_ne : (u : ℂ) - (σ.im : ℂ)
              + Complex.I * (((σ.re - (m : ℝ)) : ℝ) : ℂ) ≠ 0 := by
            rw [hσim_eq, hσre_eq]
            have : (u : ℂ) ≠ 1 := by exact_mod_cast hu_ne
            simpa using (sub_ne_zero.mpr this)
          have hinv : ContinuousAt (fun σ' : ℍ =>
              ((u : ℂ) - (σ'.im : ℂ) + Complex.I * (((σ'.re - (m : ℝ)) : ℝ) : ℂ))⁻¹) σ :=
            hinner.inv₀ hinner_ne
          exact ContinuousAt.const_mul hinv _
      have h1 : ∀ᶠ σ' in 𝓝[≠] σ, |σ'.re - (m : ℝ)| < δ := by
        have hbase : |σ.re - (m : ℝ)| < δ := by rw [hσre_eq]; simpa using hδpos
        have hc : Continuous (fun σ' : ℍ => |σ'.re - (m : ℝ)|) := by fun_prop
        exact (hc.continuousAt.tendsto.eventually
          (IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const) hbase)).filter_mono
            nhdsWithin_le_nhds
      have h2 : ∀ᶠ σ' in 𝓝[≠] σ, |σ'.im - 1| < δ := by
        have hbase : |σ.im - (1 : ℝ)| < δ := by rw [hσim_eq]; simpa using hδpos
        have hc : Continuous (fun σ' : ℍ => |σ'.im - (1 : ℝ)|) := by fun_prop
        exact (hc.continuousAt.tendsto.eventually
          (IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const) hbase)).filter_mono
            nhdsWithin_le_nhds
      have h3 : ∀ᶠ σ' in 𝓝[≠] σ, |u - σ'.im| < 8 * δ := by
        have hbase : |u - σ.im| < 8 * δ := by rw [hσim_eq]; linarith [hu4, hδpos]
        have hc : Continuous (fun σ' : ℍ => |u - σ'.im|) := by fun_prop
        exact (hc.continuousAt.tendsto.eventually
          (IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const) hbase)).filter_mono
            nhdsWithin_le_nhds
      have h4 : ∀ᶠ σ' in 𝓝[≠] σ,
          ((-(m : ℝ)) +ᵥ σ') ≠ ModularGroup.S • ((-(m : ℝ)) +ᵥ σ') := by
        filter_upwards [self_mem_nhdsWithin] with σ' hne
        intro hdeg'
        have hz' : ((-(m : ℝ)) +ᵥ σ') = UpperHalfPlane.I := KL.S_fixpoint' hdeg'.symm
        exact hne (Set.mem_singleton_iff.mpr (by
          have hEq : ((-(m : ℝ)) +ᵥ σ') = ((-(m : ℝ)) +ᵥ σ) := by rw [hz', hz₀I]
          have h := congrArg (fun w => (m : ℝ) +ᵥ w) hEq
          simpa only [vadd_neg_vadd_cancel] using h))
      have h5 : ∀ᶠ σ' in 𝓝[≠] σ, Work.Kernels.jInvariantFun σ'
          ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis u hu) :=
        (Work.Residues.continuous_jInvariantFun.continuousAt.eventually_ne hjne).filter_mono
          nhdsWithin_le_nhds
      have hev : ∀ᶠ σ' in 𝓝[≠] σ, Φ σ' ≤ CB / cI := by
        filter_upwards [h1, h2, h3, h4, h5] with σ' h1' h2' h3' h4' h5'
        exact hdirect σ' m u hu hm h1' h2' h3' h4' h5'
      have hlim : Tendsto Φ (𝓝[≠] σ) (𝓝 (Φ σ)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      show Φ σ ≤ CB / cI
      exact le_of_tendsto hlim hev
    refine ⟨δ, CB / cI, hδpos, hCpos, fun σ m u hu hm hσre hσim hu4 hjne => ?_⟩
    by_cases hdg : ((-(m : ℝ)) +ᵥ σ) = ModularGroup.S • ((-(m : ℝ)) +ᵥ σ)
    · exact hdegen σ m u hu hm hσre hσim hu4 hdg hjne
    · exact hdirect σ m u hu hm hσre hσim (by linarith [hδpos]) hdg hjne
  · -- ================= s₀ ≠ 1 =================
    obtain ⟨ρ₁, hρ₁, c₁, hc₁, hb₁⟩ :=
      MiddleRange.exists_diffQuotient_lower_general hs₀ hs1
    set δ : ℝ := min (min δA (min rA ρ₁)) 1 / 64 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact div_pos (lt_min (lt_min hδA (lt_min hrA hρ₁)) one_pos) (by norm_num)
    have hδδA : δ ≤ δA := by
      rw [hδdef]
      have h : min (min δA (min rA ρ₁)) 1 ≤ δA := le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hδrA : δ ≤ rA / 64 := by
      rw [hδdef]
      have h : min (min δA (min rA ρ₁)) 1 ≤ rA :=
        le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    have hδρ₁ : δ ≤ ρ₁ / 64 := by
      rw [hδdef]
      have h : min (min δA (min rA ρ₁)) 1 ≤ ρ₁ :=
        le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
    have hCpos : 0 ≤ CA / c₁ := div_nonneg hCA hc₁.le
    refine ⟨δ, CA / c₁, hδpos, hCpos, fun τ n t ht hn hτre hτim ht4 hjne => ?_⟩
    have hzcoe : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
    have hz₀coe : (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := coe_neg_vadd n τ
    have hx : ((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ) = (s₀ : ℂ) * Complex.I := rfl
    have hI1 : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ)‖ = |t - s₀| := by
      rw [hzcoe, hx]
      have h5 : (t : ℂ) * Complex.I - (s₀ : ℂ) * Complex.I = ((t - s₀ : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [h5, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hu1 : |t - s₀| ≤ |t - τ.im| + |τ.im - s₀| := by
      have h3 : t - s₀ = (t - τ.im) + (τ.im - s₀) := by ring
      calc |t - s₀| = |(t - τ.im) + (τ.im - s₀)| := by rw [h3]
        _ ≤ _ := abs_add_le _ _
    have hzI : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ)‖ < ρ₁ := by
      rw [hI1]; linarith [ht4, hτim, hδρ₁]
    have hzI' : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - Complex.I * (s₀ : ℂ)‖ < rA := by
      rw [hzcoe]
      have h5 : (t : ℂ) * Complex.I - Complex.I * (s₀ : ℂ) = ((t - s₀ : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [h5, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith [ht4, hτim, hδrA]
    have hz₀I : ‖(((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ)‖ < ρ₁ := by
      rw [hz₀coe, hx]
      have h4 : (τ : ℂ) - (n : ℂ) - (s₀ : ℂ) * Complex.I
          = ((τ.re - (n : ℝ) : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
            Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
            UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
      rw [h4]
      have h5 := norm_le_re_im (τ.re - (n : ℝ)) (τ.im - s₀)
      linarith [hτre, hτim, hδρ₁]
    have hjne' : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        ≠ Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ) := by
      intro h
      exact hjne (h.trans (jInvariantFun_neg_vadd τ n hn)).symm
    have hM := hbA τ n (Work.Kernels.imagAxis t ht) hn
      (lt_of_lt_of_le hτre hδδA) (lt_of_lt_of_le hτim hδδA) hzI'
    rw [← hz₀coe] at hM
    have hjlow : c₁ * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
        ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
            - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ :=
      hb₁ (Work.Kernels.imagAxis t ht) ((-(n : ℝ)) +ᵥ τ) hzI hz₀I
    have hne1 : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ) ≠ 0 := sub_ne_zero.mpr hjne'
    have hzz : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) ≠ 0 :=
      fun h => hjne' (congrArg Work.Kernels.jInvariantFun
        (UpperHalfPlane.ext (sub_eq_zero.mp h)))
    have htarget : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t -
        (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
          ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹
        = Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
          - ((n : ℂ) / (2 * (Real.pi : ℂ)))
            * ((((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)))⁻¹ := by
      rw [principal_part_eq n t ht τ, Kaxis, dif_pos ht]
    rw [htarget]
    rw [remainder_eq ℓ d hd τ (Work.Kernels.imagAxis t ht) n hn hjne']
    simp only [norm_div, norm_neg, norm_mul]
    rw [div_le_iff₀ (by exact mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hzz))]
    have hden : c₁ * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
        ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
            - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ := hjlow
    calc ‖AfunFun ℓ d τ (Work.Kernels.imagAxis t ht) * (((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
          - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))
        + ((n : ℂ) / (2 * (Real.pi : ℂ)))
          * (Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
              - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ))‖
        ≤ CA * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ ^ 2 := hM
      _ = (CA / c₁) * (c₁ * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖)
            * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
          rw [div_eq_mul_inv]; field_simp
      _ ≤ (CA / c₁) * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
              - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖
            * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hden (div_nonneg hCA hc₁.le)) (norm_nonneg _)
      _ = CA / c₁ * (‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
              - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖
            * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖) := by ring

end Work.Asymptotics
