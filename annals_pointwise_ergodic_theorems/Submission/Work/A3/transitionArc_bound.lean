import Mathlib
import Submission.Work.A3.weyl_poly
import Submission.Work.A3.expSum_block_split
import Submission.Work.A3.block_integral_comparison
import Submission.Work.A3.block_variation_bound
import Submission.Work.A3.singInt_le_mArcKernel
import Submission.Work.A3.transitionPhaseLipschitz
import Submission.Work.A3.transition_arith_case_small
import Submission.Work.A3.beta_caseA_bounds

/-!
# The transition-arc bound for polynomial Weyl sums

`Work.A3.transitionArc_bound`: on the *transition* (coherent) arcs
`|θ - a/q| = |β| ≤ N^{-d}(N/q)^{d/(d+1)}/100`, a polynomial Weyl sum of degree `d ≥ 2` satisfies
`‖expSum Q N (a/q + β)‖ ≤ C q^{-δ} mArcKernel N d β`, given the arithmetic input that complete
sums (and their initial segments) mod `q` save a power `q^{-δ}`.

The proof is the classical "block" analysis of the major arcs: `n = r + p q` splits the sum into
`q` blocks, the `a/q`-part of the phase is `q`-periodic and factors out, and each block sum is
compared with the oscillatory integral `∫_0^{N/q} e^{-2πiβQ(qt)}dt = q⁻¹·singInt Q N β`.  The
comparison error is `O(L(N+q))` with `L = 2π|β|A d(N+q)^{d-1}` a Lipschitz constant of the phase;
summed against the partial sums of the periodic weight (summation by parts, using the hypothesis
`hps`) and against the decay of the singular integral it is dominated by `q^{-δ}mArcKernel N d β`
— the exponents cancel exactly because `|β| N^d ≤ (N/q)^{d/(d+1)}/100`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

private lemma transition_arith_large_local (C₁ A : ℝ) (hC₁ : 0 < C₁) (hA : 0 < A)
    (N q d : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (hd : 2 ≤ d) (hqN : q ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {β : ℝ}
    (hreg : (N:ℝ)^(-(d:ℝ)) ≤ |β|)
    (hb : |β| * (N:ℝ)^d ≤ ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) / 100) :
    C₁ * (q:ℝ)^(1-δ) * (3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ)) + 6)
      ≤ (100 * 2^(1/(d:ℝ)) * 100^(1/(d:ℝ)) * (C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 1) + 1))
          * (q:ℝ)^(-δ) * mArcKernel N d β := by
  have hd1 : 1 ≤ d := by omega
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNnn : (0:ℝ) ≤ (N:ℝ) := hNpos.le
  have hqnn : (0:ℝ) ≤ (q:ℝ) := hq0.le
  have hqN' : (q:ℝ) ≤ (N:ℝ) := by exact_mod_cast hqN
  have hbabs : 0 < |β| := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hreg
  set W : ℝ := C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 1) + 1 with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  set Cc : ℝ := 100 * (2:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * W with hCc
  have hCcpos : 0 < Cc := by rw [hCc]; positivity
  have hr1 : (d:ℝ)/((d:ℝ)+1) + 1/((d:ℝ)+1) = 1 := by
    rw [← add_div, div_self (by positivity : ((d:ℝ)+1) ≠ 0)]
  have hqpow : (q:ℝ)^(1-δ) = (q:ℝ) * (q:ℝ)^(-δ) := by
    rw [show (1:ℝ) - δ = 1 + (-δ) by ring, Real.rpow_add hq0, Real.rpow_one]
  have hqdpos : 0 < (q:ℝ)^(-δ) := Real.rpow_pos_of_pos hq0 _
  set X : ℝ := (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1)) with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  -- the key exponent identity `(N/q)^{d/(d+1)} q = X`
  have hiden : ((q:ℝ)^((d:ℝ)/((d:ℝ)+1)))⁻¹ * (q:ℝ) = (q:ℝ)^(1/((d:ℝ)+1)) := by
    rw [← Real.rpow_neg hqnn]
    have hone : (q:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) * (q:ℝ)
        = (q:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) * (q:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
    rw [hone, ← Real.rpow_add hq0]
    congr 1
    linarith [hr1]
  have hNq : ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ) = X := by
    calc ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)
        = (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * ((q:ℝ)^((d:ℝ)/((d:ℝ)+1)))⁻¹ * (q:ℝ) := by
          rw [Real.div_rpow hNnn hqnn, div_eq_mul_inv]
      _ = (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (((q:ℝ)^((d:ℝ)/((d:ℝ)+1)))⁻¹ * (q:ℝ)) := by ring
      _ = (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1)) := by rw [hiden]
  -- `|β| N^d q ≤ X/100`
  have h1 : |β| * (N:ℝ)^d * (q:ℝ) ≤ X / 100 := by
    have h3 : |β| * (N:ℝ)^d * (q:ℝ) ≤ ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ) / 100 := by
      calc |β| * (N:ℝ)^d * (q:ℝ)
          ≤ ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) / 100 * (q:ℝ) :=
            mul_le_mul_of_nonneg_right hb hqnn
        _ = ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ) / 100 := by ring
    calc |β| * (N:ℝ)^d * (q:ℝ)
        ≤ ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ) / 100 := h3
      _ = X / 100 := by rw [hNq]
  -- `q ≤ X`
  have h3 : (q:ℝ) ≤ X := by
    have h4 : (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1)) = (q:ℝ) := by
      rw [← Real.rpow_add hq0, hr1, Real.rpow_one]
    have h5 : (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) ≤ (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) :=
      Real.rpow_le_rpow hqnn hqN' (by positivity)
    rw [hX]
    calc (q:ℝ) = (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1)) := h4.symm
      _ ≤ (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1)) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
  -- `|β| (N+q)^d ≤ 2^d |β| N^d`
  have h4 : |β| * ((N:ℝ)+(q:ℝ))^d ≤ (2:ℝ)^d * (|β| * (N:ℝ)^d) := by
    have h2N : (N:ℝ) + (q:ℝ) ≤ 2 * (N:ℝ) := by linarith
    have h5 : ((N:ℝ)+(q:ℝ))^d ≤ (2 * (N:ℝ))^d := pow_le_pow_left₀ (by positivity) h2N d
    calc |β| * ((N:ℝ)+(q:ℝ))^d ≤ |β| * (2 * (N:ℝ))^d :=
          mul_le_mul_of_nonneg_left h5 (abs_nonneg β)
      _ = (2:ℝ)^d * (|β| * (N:ℝ)^d) := by rw [mul_pow]; ring
  -- the kernel bound
  have h5 : (2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * X
      ≤ mArcKernel N d β := by
    have hb' := beta_caseA_bounds N d q hN hd1 hq hbabs hb
    have hk := (mArcKernel_lower N d hN hd1 β).1 hreg
    refine le_trans ?_ hk
    calc (2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * X
        = (2:ℝ)^(-(1:ℝ)/(d:ℝ)) * ((100:ℝ)^(1/(d:ℝ)) * X) := by ring
      _ ≤ (2:ℝ)^(-(1:ℝ)/(d:ℝ)) * |β|^(-(1:ℝ)/(d:ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa only [hX, mul_assoc] using hb'.2
  -- the exponent step `M^{d-1} M = M^d`
  have hxd : ((N:ℝ)+(q:ℝ))^(d-1) * ((N:ℝ)+(q:ℝ)) = ((N:ℝ)+(q:ℝ))^d := by
    rw [← pow_succ, Nat.sub_add_cancel hd1]
  have hMd : 3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ))
      = 6 * Real.pi * A * (d:ℝ) * (|β| * ((N:ℝ)+(q:ℝ))^d) := by
    have h1 : 3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ))
        = 3 * (2 * Real.pi * |β| * A * (d:ℝ)) * (((N:ℝ)+(q:ℝ))^(d-1) * ((N:ℝ)+(q:ℝ))) := by
      ring
    rw [h1, hxd]; ring
  -- the constant comparison
  have h6 : C₁ * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (1/100) + 6)
      ≤ Cc * ((2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ))) := by
    have hrpow1 : (1:ℝ) ≤ (100:ℝ)^(1/(d:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
    have h2r : (2:ℝ)^(1/(d:ℝ)) * (2:ℝ)^(-(1:ℝ)/(d:ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      have hexp : (1:ℝ)/(d:ℝ) + (-1)/(d:ℝ) = 0 := by rw [← add_div, add_neg_cancel, zero_div]
      rw [hexp, Real.rpow_zero]
    have hCc' : Cc * ((2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)))
        = 100 * (100:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * W := by
      rw [hCc]
      calc 100 * (2:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * W
              * ((2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)))
          = 100 * (100:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * W
              * ((2:ℝ)^(1/(d:ℝ)) * (2:ℝ)^(-(1:ℝ)/(d:ℝ))) := by ring
        _ = 100 * (100:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * W := by rw [h2r, mul_one]
    rw [hCc', hW]
    have h200 : (0:ℝ) ≤ Real.pi * A * (d:ℝ) * (2:ℝ)^d * C₁ := by positivity
    have hg1 : C₁ * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (1/100))
        ≤ 100 * (Real.pi * A * (d:ℝ) * (2:ℝ)^d * C₁) := by nlinarith [h200]
    have hg2 : (6:ℝ) * C₁ ≤ 100 * C₁ + 100 := by nlinarith [hC₁]
    have hbase : C₁ * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (1/100) + 6)
        ≤ 100 * (C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 1) + 1) := by nlinarith [hg1, hg2]
    have hle : (100:ℝ) ≤ 100 * (100:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) := by nlinarith [hrpow1]
    have hnn : (0:ℝ) ≤ C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 1) + 1 := by positivity
    exact hbase.trans (mul_le_mul_of_nonneg_right hle hnn)
  -- the block factor
  have hblk : 3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ)) + 6
      ≤ 6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (|β| * (N:ℝ)^d) + 6 := by
    rw [hMd]
    have hc2 : (0:ℝ) ≤ 6 * Real.pi * A * (d:ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left h4 hc2
    linarith
  calc C₁ * (q:ℝ)^(1-δ) * (3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ)) + 6)
      ≤ C₁ * (q:ℝ)^(1-δ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (|β| * (N:ℝ)^d) + 6) := by
        have hnn : (0:ℝ) ≤ C₁ * (q:ℝ)^(1-δ) := by
          rw [hqpow]; positivity
        exact mul_le_mul_of_nonneg_left hblk hnn
    _ = C₁ * (q:ℝ)^(-δ) * (q:ℝ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (|β| * (N:ℝ)^d) + 6) := by
        rw [hqpow]; ring
    _ = C₁ * (q:ℝ)^(-δ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (|β| * (N:ℝ)^d * (q:ℝ)) + 6 * (q:ℝ)) := by
        ring
    _ ≤ C₁ * (q:ℝ)^(-δ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (X / 100) + 6 * X) := by
        have hc2 : (0:ℝ) ≤ 6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d := by positivity
        have h1' := mul_le_mul_of_nonneg_left h1 hc2
        have h3' := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 6)
        have hmain : 6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (|β| * (N:ℝ)^d * (q:ℝ)) + 6 * (q:ℝ)
            ≤ 6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (X / 100) + 6 * X := by linarith
        exact mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = C₁ * (q:ℝ)^(-δ) * ((6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (1/100) + 6) * X) := by ring
    _ = (C₁ * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d * (1/100) + 6)) * ((q:ℝ)^(-δ) * X) := by ring
    _ ≤ (Cc * ((2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)))) * ((q:ℝ)^(-δ) * X) :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = Cc * (q:ℝ)^(-δ) * ((2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * X) := by ring
    _ ≤ Cc * (q:ℝ)^(-δ) * mArcKernel N d β :=
        mul_le_mul_of_nonneg_left h5 (by positivity)

/-- The transition-arc (coherent arc) bound for polynomial Weyl sums. -/
theorem transitionArc_bound (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {C₁ : ℝ} (hC₁ : 0 < C₁) {δ : ℝ} (hδ : 0 < δ)
    (hcs : ∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
      ‖Work.A3.completeSum Q a q‖ ≤ C₁ * (q : ℝ) ^ (1 - δ))
    (hps : ∀ (q : ℕ) (a : ℤ) (t : ℕ), 1 ≤ q → IsCoprime a (q : ℤ) → t ≤ q →
      ‖∑ r ∈ Finset.range t,
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((a : ℝ) * (((Q.eval (r : ℤ)) : ℤ) : ℝ) / (q : ℝ))))‖
      ≤ C₁ * (q : ℝ) ^ (1 - δ)) :
    ∃ C > 0, ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) →
      |β| * (N : ℝ) ^ Polynomial.natDegree Q
        ≤ ((N : ℝ) / (q : ℝ)) ^ ((Polynomial.natDegree Q : ℝ) / (Polynomial.natDegree Q + 1)) / 100 →
      ‖Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β)‖
        ≤ C * (q : ℝ) ^ (-δ) * Work.A3.mArcKernel N (Polynomial.natDegree Q) β := by
  classical
  obtain ⟨A, hApos, hA⟩ := transitionPhaseLipschitz Q (by omega : 1 ≤ Polynomial.natDegree Q)
  obtain ⟨Cv, hCvpos, hCv⟩ := singInt_le_mArcKernel Q hd
  set d : ℕ := Polynomial.natDegree Q with hddef
  have hd2 : 2 ≤ d := by rw [hddef]; exact hd
  refine ⟨C₁ * Cv + 100 * 2 ^ ((1:ℝ) / (d:ℝ)) * 100 ^ ((1:ℝ) / (d:ℝ)) *
      (C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ) ^ d + 1) + 1), by positivity, ?_⟩
  intro N a q β hN hq hcop hqN hβ
  -- pass to the natural-number modulus
  set qn : ℕ := q.toNat with hqndef
  have hqn_cast : (qn : ℤ) = q := Int.toNat_of_nonneg (by omega)
  have hqn1 : 1 ≤ qn := by omega
  have hqnN : qn ≤ N := by
    have h1 : (qn : ℝ) ≤ (N : ℝ) := by
      rw [← Int.cast_natCast, hqn_cast]; exact hqN
    exact_mod_cast h1
  have hqnR : (qn : ℝ) = (q : ℝ) := by rw [← Int.cast_natCast, hqn_cast]
  have hcop' : IsCoprime a (qn : ℤ) := by rw [hqn_cast]; exact hcop
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hq1 : (1:ℝ) ≤ (qn:ℝ) := by exact_mod_cast hqn1
  have hqpos : (0:ℝ) < (qn:ℝ) := by linarith
  have hβ' : |β| * (N:ℝ) ^ d ≤ ((N:ℝ) / (qn:ℝ)) ^ ((d:ℝ) / ((d:ℝ) + 1)) / 100 := by
    have h := hβ
    rw [← hqnR] at h
    simpa [← hddef, Nat.cast_add] using h
  -- the phase and its Lipschitz constant
  set φ : ℝ → ℂ := fun x => Complex.exp (-(2 * Real.pi * Complex.I * (β * (Qreal Q).eval x)))
    with hφdef
  set M : ℝ := (N:ℝ) + (qn:ℝ) with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith
  have hM2 : M ≤ 2 * (N:ℝ) := by rw [hMdef]; linarith
  have hφcont : Continuous φ := by
    rw [hφdef]
    fun_prop
  set L : ℝ := 2 * Real.pi * |β| * A * (d:ℝ) * M ^ (d - 1) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hlip : ∀ x ∈ Set.Icc (0:ℝ) M, ∀ y ∈ Set.Icc (0:ℝ) M, ‖φ x - φ y‖ ≤ L * |x - y| := by
    intro x hx y hy
    show ‖φ x - φ y‖ ≤ (2 * Real.pi * |β| * A * (d:ℝ) * M ^ (d - 1)) * |x - y|
    rw [hφdef]
    exact (hA β M hM1).1 x hx y hy
  have hnorm : ∀ x ∈ Set.Icc (0:ℝ) M, ‖φ x‖ ≤ 1 := by
    intro x hx
    rw [hφdef]
    exact le_of_eq ((hA β M hM1).2 x)
  -- the periodic weight and the block sums
  set ψ : ℕ → ℂ := fun r => Complex.exp
    (-(2 * Real.pi * Complex.I * (((a:ℝ) / (qn:ℝ)) * (((Q.eval (r:ℤ) : ℤ) : ℝ))))) with hψdef
  set B : ℕ → ℂ := fun r =>
    ∑ p ∈ Finset.range ((N - r) / qn + 1), φ ((r + p * qn : ℕ) : ℝ) with hBdef
  set V : ℂ := ∫ t in (0:ℝ)..((N:ℝ) / (qn:ℝ)), φ ((qn:ℝ) * t) with hVdef
  have hsplit : expSum Q N ((a:ℝ) / (q:ℝ) + β)
      = (∑ r ∈ Finset.range qn, ψ r * B r) - ψ 0 * φ 0 := by
    have h := expSum_block_split Q N qn hqn1 hqnN a β
    have hqa : (a:ℝ) / (q:ℝ) = (a:ℝ) / (qn:ℝ) := by rw [hqnR]
    rw [hqa]
    simpa only [hψdef, hBdef, hφdef, Nat.cast_zero] using h
  -- partial sums of the periodic weight: the hypothesis `hps`
  have hpart : ∀ t ≤ qn, ‖∑ r ∈ Finset.range t, ψ r‖ ≤ C₁ * (qn:ℝ) ^ (1 - δ) := by
    intro t ht
    have h := hps qn a t hqn1 hcop' ht
    have hcongr : (∑ r ∈ Finset.range t, ψ r)
        = ∑ r ∈ Finset.range t, Complex.exp (-(2 * Real.pi * Complex.I *
            ((a : ℝ) * (((Q.eval (r : ℤ)) : ℤ) : ℝ) / (qn : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hψdef]
      congr 1
      ring_nf
    rw [hcongr]
    exact h
  -- the singular integral: `V = q⁻¹ • singInt`
  have hV_eq : V = ((qn:ℂ))⁻¹ * singInt Q N β := by
    rw [hVdef]
    have hqne : (qn:ℝ) ≠ 0 := ne_of_gt hqpos
    have hcomp := intervalIntegral.integral_comp_mul_left (f := φ) (a := (0:ℝ))
      (b := (N:ℝ) / (qn:ℝ)) (c := (qn:ℝ)) hqne
    simp only [mul_zero] at hcomp
    have hqNq : (qn:ℝ) * ((N:ℝ) / (qn:ℝ)) = (N:ℝ) := by field_simp
    rw [hqNq] at hcomp
    have h2 : (∫ t in (0:ℝ)..(N:ℝ), φ t) = singInt Q N β := by
      rw [singInt, hφdef]
    rw [hcomp, Complex.real_smul, h2]
    simp only [Complex.ofReal_natCast, Complex.ofReal_inv]
  -- block comparison with the integral, and the variation of consecutive blocks
  have hcmp : ∀ r < qn, ‖B r - V‖ ≤ 2 * L * M + 1 := by
    intro r hr
    rw [hBdef, hVdef]
    exact block_integral_comparison N qn hqn1 hN φ L hL0 hφcont hlip hnorm r hr
  have hvar : ∑ r ∈ Finset.range (qn - 1), ‖B (r + 1) - B r‖ ≤ L * M + 3 := by
    have h := block_variation_bound N qn hqn1 hN φ L hL0 hlip hnorm
    rw [hBdef]
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro r hr
    rw [norm_sub_rev]
  -- the sequence that is summed by parts
  set bb : ℕ → ℂ := fun r => B r - V - (if r = 0 then φ 0 else 0) with hbbdef
  have hident : expSum Q N ((a:ℝ) / (q:ℝ) + β) - (∑ r ∈ Finset.range qn, ψ r) * V
      = ∑ r ∈ Finset.range qn, ψ r * bb r := by
    rw [hsplit]
    simp only [hbbdef]
    have h1 : ∀ r ∈ Finset.range qn, ψ r * (B r - V - (if r = 0 then φ 0 else 0))
        = ψ r * B r - ψ r * V - (if r = 0 then ψ r * φ 0 else 0) := by
      intro r hr
      by_cases h : r = 0
      · subst h; simp only [if_true]; ring
      · simp only [if_neg h, mul_sub, mul_zero, sub_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', ← Finset.sum_mul]
    have h0 : (0:ℕ) ∈ Finset.range qn := Finset.mem_range.mpr (by omega)
    rw [if_pos h0]
    ring
  -- bounds for `bb`
  have hbb_bd : ∀ r < qn, ‖bb r‖ ≤ 2 * L * M + 2 := by
    intro r hr
    have h1 := hcmp r hr
    have h2 : ‖(if r = 0 then φ 0 else 0)‖ ≤ 1 := by
      by_cases h : r = 0
      · rw [if_pos h]; exact le_of_eq ((hA β M hM1).2 0)
      · rw [if_neg h, norm_zero]; norm_num
    simp only [hbbdef]
    calc ‖B r - V - (if r = 0 then φ 0 else 0)‖
        ≤ ‖B r - V‖ + ‖(if r = 0 then φ 0 else 0)‖ := norm_sub_le _ _
      _ ≤ (2 * L * M + 1) + 1 := by linarith
      _ = 2 * L * M + 2 := by ring
  have hbb_var : ∑ r ∈ Finset.range (qn - 1), ‖bb (r + 1) - bb r‖ ≤ L * M + 4 := by
    have hstep : ∀ r ∈ Finset.range (qn - 1),
        ‖bb (r + 1) - bb r‖
          ≤ ‖B (r + 1) - B r‖ + (if r = 0 then (1:ℝ) else 0) := by
      intro r hr
      have h2 : ‖(if r + 1 = 0 then φ 0 else 0) - (if r = 0 then φ 0 else 0)‖
          ≤ (if r = 0 then (1:ℝ) else 0) := by
        by_cases h : r = 0
        · subst h
          have h3 : (if (0:ℕ) + 1 = 0 then φ 0 else 0) = 0 := by
            rw [if_neg (by norm_num)]
          rw [h3, if_pos rfl, zero_sub, norm_neg, if_pos rfl]
          exact le_of_eq ((hA β M hM1).2 0)
        · rw [if_neg (by omega : ¬ (r + 1 = 0)), if_neg h, sub_zero, norm_zero, if_neg h]
      simp only [hbbdef]
      calc ‖(B (r + 1) - V - (if r + 1 = 0 then φ 0 else 0))
              - (B r - V - (if r = 0 then φ 0 else 0))‖
          = ‖(B (r + 1) - B r)
              - ((if r + 1 = 0 then φ 0 else 0) - (if r = 0 then φ 0 else 0))‖ := by ring_nf
        _ ≤ ‖B (r + 1) - B r‖
              + ‖(if r + 1 = 0 then φ 0 else 0) - (if r = 0 then φ 0 else 0)‖ :=
              norm_sub_le _ _
        _ ≤ ‖B (r + 1) - B r‖ + (if r = 0 then (1:ℝ) else 0) := add_le_add le_rfl h2
    calc ∑ r ∈ Finset.range (qn - 1), ‖bb (r + 1) - bb r‖
        ≤ ∑ r ∈ Finset.range (qn - 1),
            (‖B (r + 1) - B r‖ + (if r = 0 then (1:ℝ) else 0)) := Finset.sum_le_sum hstep
      _ = (∑ r ∈ Finset.range (qn - 1), ‖B (r + 1) - B r‖)
            + ∑ r ∈ Finset.range (qn - 1), (if r = 0 then (1:ℝ) else 0) :=
            Finset.sum_add_distrib
      _ ≤ (L * M + 3) + 1 := by
          refine add_le_add hvar ?_
          rw [Finset.sum_ite_eq']
          split_ifs with h
          · exact le_rfl
          · norm_num
      _ = L * M + 4 := by ring
  -- summation by parts against the hypothesis `hps`
  have habel : ‖∑ r ∈ Finset.range qn, ψ r * bb r‖
      ≤ C₁ * (qn:ℝ) ^ (1 - δ) * (3 * L * M + 6) := by
    set K : ℝ := C₁ * (qn:ℝ) ^ (1 - δ) with hKdef
    have hK0 : 0 ≤ K := by rw [hKdef]; positivity
    have hby := Finset.sum_range_by_parts (R := ℂ) (M := ℂ) bb ψ qn
    simp only [smul_eq_mul] at hby
    have hsum_eq : (∑ i ∈ Finset.range qn, ψ i * bb i)
        = ∑ i ∈ Finset.range qn, bb i * ψ i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum_eq, hby]
    have hKpart : ∀ t ≤ qn, ‖∑ r ∈ Finset.range t, ψ r‖ ≤ K := by
      intro t ht; rw [hKdef]; exact hpart t ht
    have hA1 : ‖bb (qn - 1) * ∑ i ∈ Finset.range qn, ψ i‖ ≤ K * (2 * L * M + 2) := by
      rw [norm_mul]
      calc ‖bb (qn - 1)‖ * ‖∑ i ∈ Finset.range qn, ψ i‖
          ≤ (2 * L * M + 2) * K :=
            mul_le_mul (hbb_bd (qn - 1) (by omega)) (hKpart qn le_rfl) (norm_nonneg _)
              (by positivity)
        _ = K * (2 * L * M + 2) := by ring
    have hA2 : ‖∑ i ∈ Finset.range (qn - 1),
          (bb (i + 1) - bb i) * ∑ j ∈ Finset.range (i + 1), ψ j‖ ≤ K * (L * M + 4) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ i ∈ Finset.range (qn - 1),
            ‖(bb (i + 1) - bb i) * ∑ j ∈ Finset.range (i + 1), ψ j‖
          ≤ ∑ i ∈ Finset.range (qn - 1), ‖bb (i + 1) - bb i‖ * K := by
            apply Finset.sum_le_sum
            intro i hi
            have hi1 : i + 1 ≤ qn := by have := Finset.mem_range.mp hi; omega
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hKpart (i + 1) hi1) (norm_nonneg _)
        _ = (∑ i ∈ Finset.range (qn - 1), ‖bb (i + 1) - bb i‖) * K := by
            rw [Finset.sum_mul]
        _ ≤ (L * M + 4) * K :=
            mul_le_mul_of_nonneg_right hbb_var hK0
        _ = K * (L * M + 4) := by ring
    calc ‖bb (qn - 1) * ∑ i ∈ Finset.range qn, ψ i
            - ∑ i ∈ Finset.range (qn - 1), (bb (i + 1) - bb i) * ∑ j ∈ Finset.range (i + 1), ψ j‖
        ≤ ‖bb (qn - 1) * ∑ i ∈ Finset.range qn, ψ i‖
            + ‖∑ i ∈ Finset.range (qn - 1),
                (bb (i + 1) - bb i) * ∑ j ∈ Finset.range (i + 1), ψ j‖ := norm_sub_le _ _
      _ ≤ K * (2 * L * M + 2) + K * (L * M + 4) := add_le_add hA1 hA2
      _ = K * (3 * L * M + 6) := by ring
  -- the main term
  have hmain : ‖(∑ r ∈ Finset.range qn, ψ r) * V‖
      ≤ C₁ * Cv * (qn:ℝ) ^ (-δ) * mArcKernel N d β := by
    have h1 : ‖∑ r ∈ Finset.range qn, ψ r‖ ≤ C₁ * (qn:ℝ) ^ (1 - δ) := hpart qn le_rfl
    have h2 : ‖V‖ ≤ ((qn:ℝ))⁻¹ * (Cv * mArcKernel N d β) := by
      rw [hV_eq, norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hCv N β) (by positivity)
    calc ‖(∑ r ∈ Finset.range qn, ψ r) * V‖
        = ‖∑ r ∈ Finset.range qn, ψ r‖ * ‖V‖ := norm_mul _ _
      _ ≤ (C₁ * (qn:ℝ) ^ (1 - δ)) * (((qn:ℝ))⁻¹ * (Cv * mArcKernel N d β)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C₁ * Cv * (qn:ℝ) ^ (-δ) * mArcKernel N d β := by
          have hqne : (0:ℝ) < (qn:ℝ) := hqpos
          have hrpow : (qn:ℝ) ^ (1 - δ) * ((qn:ℝ))⁻¹ = (qn:ℝ) ^ (-δ) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hqne]
            congr 1
            ring
          rw [mul_assoc (C₁), ← mul_assoc ((qn:ℝ) ^ (1 - δ)), hrpow]
          ring
  -- assemble
  have hS : ‖expSum Q N ((a:ℝ) / (q:ℝ) + β)‖
      ≤ C₁ * Cv * (qn:ℝ) ^ (-δ) * mArcKernel N d β + C₁ * (qn:ℝ) ^ (1 - δ) * (3 * L * M + 6) := by
    have h1 : expSum Q N ((a:ℝ) / (q:ℝ) + β)
        = (∑ r ∈ Finset.range qn, ψ r) * V + ∑ r ∈ Finset.range qn, ψ r * bb r := by
      have h := sub_eq_iff_eq_add.mp hident
      exact h.trans (add_comm (∑ r ∈ Finset.range qn, ψ r * bb r)
        ((∑ r ∈ Finset.range qn, ψ r) * V))
    rw [h1]
    calc ‖(∑ r ∈ Finset.range qn, ψ r) * V + ∑ r ∈ Finset.range qn, ψ r * bb r‖
        ≤ ‖(∑ r ∈ Finset.range qn, ψ r) * V‖ + ‖∑ r ∈ Finset.range qn, ψ r * bb r‖ :=
          norm_add_le _ _
      _ ≤ C₁ * Cv * (qn:ℝ) ^ (-δ) * mArcKernel N d β
            + C₁ * (qn:ℝ) ^ (1 - δ) * (3 * L * M + 6) := add_le_add hmain habel
  by_cases hreg : (N:ℝ) ^ (-(d:ℝ)) ≤ |β|
  · have harith := transition_arith_large_local C₁ A hC₁ hApos N qn d hN hqn1 hd2 hqnN hδ hreg hβ'
    rw [hLdef, hMdef] at hS
    have hgoal : ‖expSum Q N ((a:ℝ) / (q:ℝ) + β)‖
        ≤ (C₁ * Cv + 100 * 2 ^ ((1:ℝ) / (d:ℝ)) * 100 ^ ((1:ℝ) / (d:ℝ)) *
            (C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ) ^ d + 1) + 1))
            * (qn:ℝ) ^ (-δ) * mArcKernel N d β := by
      linarith [hS, harith]
    rwa [hqnR] at hgoal
  · have hreg' : |β| ≤ (N:ℝ) ^ (-(d:ℝ)) := le_of_lt (not_le.mp hreg)
    have harith := transition_arith_case_small C₁ A hC₁ hApos N qn d hN hqn1 hd2 hqnN hδ hreg'
    rw [hLdef, hMdef] at hS
    have hgoal : ‖expSum Q N ((a:ℝ) / (q:ℝ) + β)‖
        ≤ (C₁ * Cv + 100 * 2 ^ ((1:ℝ) / (d:ℝ)) * 100 ^ ((1:ℝ) / (d:ℝ)) *
            (C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ) ^ d + 1) + 1))
            * (qn:ℝ) ^ (-δ) * mArcKernel N d β := by
      linarith [hS, harith]
    rwa [hqnR] at hgoal

end

end Work.A3
