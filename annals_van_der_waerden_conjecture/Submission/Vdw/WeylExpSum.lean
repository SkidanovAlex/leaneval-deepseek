import Submission.Vdw.WeylBridge
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# The Weyl bound yields the §4 exponential-sum input (power saving `2^{-n}`)

`WeylBridge` reduces the §4 Fourier gate of the development
(`FourierTranslate.ExpSumBound n θ`, hence `MIndexBound` for `θ = 1/2`) to a
power-saving bound for complete polynomial exponential sums over `F_p`.  This
module discharges that input with the **elementary Weyl bound**
(`Commons.Analysis.ExponentialSums.weyl_inequality`), obtaining

    `ExpSumBound n (2^{-n})`.

Consequently the deepest analytic input of the paper's §4 (Weil's bound for
polynomial exponential sums / the Riemann hypothesis for Artin–Schreier curves /
Hasse's theorem for elliptic curves) is **removable**: what it is used for is
only *some* positive saving `θ > 0`, at the price of shrinking the Case-I
threshold `δ` to `δ ≲ θ/n = 2^{-n}/(2n)` (Roadmap Session-152).

Chain: for `Q : (ZMod p)[X]` of degree `k` (`1 ≤ k ≤ n < p`) and
`f = wPoly p Q : ℝ[X]` (leading coefficient `(Q.leadingCoeff).val / p`),
the Weyl inequality at `M = 0`, `N = q = p`, `a = (Q.leadingCoeff).val`, `t = 1`
(with `gcd(a,p) = 1` since `0 < val < p`) gives

    `‖Σ_c χ(Q(c))‖ ≤ C_k·p^{1+ε}·(4/p)^{2^{1-k}}`   (`k ≥ 2`),

because the Weyl bracket is `2/p + 2/p^{k-1} ≤ 4/p`; with `ε := 2^{-n}/2` and
`θ := 2^{-n}` this is `≤ C_k·4^{2^{1-k}}·p^{1-θ}` since `θ + ε ≤ 2^{1-k}` for
`k ≤ n`.  The linear case `k = 1` is a vanishing sum (orthogonality):
`WeylBridge.sum_stdAddChar_eval_natDegree_one`.  The constant is the finite sum
`Σ_{1 ≤ k ≤ n} max (C_k) 1 · 4^{2^{1-k}} + 1`, a function of `n` only.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

open Commons.Analysis.ExponentialSums

theorem expSumBound_weyl (n : ℕ) (hn : 1 ≤ n) : ExpSumBound n ((2:ℝ) ^ (-(n:ℝ))) := by
  set θ : ℝ := (2:ℝ) ^ (-(n:ℝ)) with hθdef
  have h2R : (0:ℝ) < 2 := by norm_num
  have hθpos : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos h2R _
  set ε : ℝ := θ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  classical
  set Cw : ℕ → ℝ := fun k => if hk : 1 ≤ k then
    Classical.choose (weyl_inequality k hk hεpos (t := 1) le_rfl) else 0 with hCwdef
  set Ctot : ℝ := (∑ k ∈ Finset.Icc 1 n,
      max (Cw k) 1 * (4:ℝ) ^ ((2:ℝ)^(1-(k:ℝ)))) + 1 with hCtotdef
  have hCtot_nonneg : 0 ≤ Ctot := by
    rw [hCtotdef]
    have h : (0:ℝ) ≤ ∑ k ∈ Finset.Icc 1 n,
        max (Cw k) 1 * (4:ℝ) ^ ((2:ℝ)^(1-(k:ℝ))) := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (le_trans zero_le_one (le_max_right (Cw k) 1))
        (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) _)
    linarith
  refine ⟨Ctot, hCtot_nonneg, ?_⟩
  intro p _inst hpn Q h1 h2
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le
  have hp0 : (0:ℝ) < (p:ℝ) := lt_of_lt_of_le one_pos hp1
  have hpint : (1:ℤ) ≤ (p:ℤ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le
  have hQne : Q ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
  by_cases hdeg : Q.natDegree = 1
  · rw [sum_stdAddChar_eval_natDegree_one p Q hdeg, norm_zero]
    exact mul_nonneg hCtot_nonneg (Real.rpow_nonneg hp0.le _)
  · have hk2 : 2 ≤ Q.natDegree := by omega
    set k := Q.natDegree with hkdef
    have hk1 : 1 ≤ k := by omega
    have hk_le : k ≤ n := h2
    set s : ℝ := (2:ℝ)^(1-(k:ℝ)) with hsdef
    obtain ⟨hCwpos, hWeyl⟩ :=
      Classical.choose_spec (weyl_inequality k hk1 hεpos (t := 1) le_rfl)
    have hCwk : Cw k = Classical.choose (weyl_inequality k hk1 hεpos (t := 1) le_rfl) := by
      rw [hCwdef]; simp [hk1]
    have hgcd : Int.gcd ((Q.leadingCoeff).val : ℤ) (p:ℤ) = 1 := by
      have hval_lt : (Q.leadingCoeff).val < p := ZMod.val_lt _
      have hval_ne : (Q.leadingCoeff).val ≠ 0 := by
        intro h
        exact Polynomial.leadingCoeff_ne_zero.mpr hQne ((ZMod.val_eq_zero _).mp h)
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast, Nat.gcd_comm]
      exact Nat.Coprime.gcd_eq_one (((Fact.out : Nat.Prime p).coprime_iff_not_dvd).mpr (fun hd =>
        absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hval_ne) hd) (by omega)))
    have hlc : |(wPoly p Q).leadingCoeff - (((Q.leadingCoeff).val : ℤ) : ℝ) / ((p:ℤ) : ℝ)|
        ≤ (1:ℝ) / ((p:ℤ) : ℝ) ^ 2 := by
      have h1' : (wPoly p Q).leadingCoeff
          = (((Q.leadingCoeff).val : ℤ) : ℝ) / ((p:ℤ) : ℝ) := by
        rw [wPoly_leadingCoeff p Q hQne]
        push_cast
        ring
      rw [h1', sub_self, abs_zero]
      positivity
    have hdegf : (wPoly p Q).natDegree = k := by
      rw [wPoly_natDegree p Q hQne, hkdef]
    have hbound := hWeyl 0 p ((Q.leadingCoeff).val : ℤ) (p:ℤ) (wPoly p Q) hpint hgcd hdegf hlc
    rw [← hCwk] at hbound
    have hsum_eq : (∑ c : ZMod p, ZMod.stdAddChar (Q.eval c))
        = ∑ x ∈ Finset.range p,
            Complex.exp (↑(2 * Real.pi * (wPoly p Q).eval ((0:ℝ) + (x:ℝ))) * Complex.I) := by
      rw [sum_zmod_eq_sum_range p (fun c => ZMod.stdAddChar (Q.eval c))]
      exact Finset.sum_congr rfl (fun x _ => stdAddChar_eq_exp_wPoly p Q x)
    rw [hsum_eq]
    simp only [Int.cast_zero, zero_add] at hbound ⊢
    have hk1' : 1 ≤ k - 1 := by omega
    have hpoweq : (p:ℝ) ≤ (p:ℝ) ^ (k-1) := by
      calc (p:ℝ) = (p:ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (p:ℝ) ^ (k-1) := pow_le_pow_right₀ hp1 hk1'
    have hterm1 : (1:ℝ) / ((p:ℤ):ℝ) = 1 / (p:ℝ) := by rw [Int.cast_natCast]
    have hterm3 : (1:ℝ) / (p:ℝ) ^ (k-1) ≤ 1 / (p:ℝ) := by
      have h := one_div_le_one_div_of_le hp0 hpoweq
      simpa using h
    have hterm4 : ((p:ℤ):ℝ) / (p:ℝ)^k ≤ 1 / (p:ℝ) := by
      rw [Int.cast_natCast, div_le_iff₀ (pow_pos hp0 k), one_div, le_inv_mul_iff₀ hp0]
      have hpk : (p:ℝ)^k = (p:ℝ)^(k-1) * (p:ℝ) := by
        conv_lhs => rw [show k = (k-1)+1 by omega]
        rw [pow_add, pow_one]
      rw [hpk]
      exact mul_le_mul_of_nonneg_right hpoweq hp0.le
    have hBnn : (0:ℝ) ≤ (1:ℝ)/((p:ℤ):ℝ) + 1/(p:ℝ) + 1/(p:ℝ)^(k-1) + ((p:ℤ):ℝ)/(p:ℝ)^k := by
      have h1 : (0:ℝ) ≤ (1:ℝ)/((p:ℤ):ℝ) := by positivity
      have h2 : (0:ℝ) ≤ 1/(p:ℝ) := by positivity
      have h3 : (0:ℝ) ≤ 1/(p:ℝ)^(k-1) := by positivity
      have h4 : (0:ℝ) ≤ ((p:ℤ):ℝ)/(p:ℝ)^k := by positivity
      linarith
    have hB : (1:ℝ)/((p:ℤ):ℝ) + 1/(p:ℝ) + 1/(p:ℝ)^(k-1) + ((p:ℤ):ℝ)/(p:ℝ)^k
        ≤ 4 / (p:ℝ) := by
      have ha : (1:ℝ)/((p:ℤ):ℝ) ≤ 1/(p:ℝ) := le_of_eq hterm1
      have hb : (1:ℝ)/(p:ℝ) ≤ 1/(p:ℝ) := le_rfl
      have h4 : (1:ℝ)/(p:ℝ) + 1/(p:ℝ) + 1/(p:ℝ) + 1/(p:ℝ) = 4/(p:ℝ) := by ring
      have h := add_le_add (add_le_add (add_le_add ha hb) hterm3) hterm4
      exact h.trans (le_of_eq h4)
    have hstep1 : Cw k * (p:ℝ)^(1+ε)
          * ((1:ℝ)/((p:ℤ):ℝ) + 1/(p:ℝ) + 1/(p:ℝ)^(k-1) + ((p:ℤ):ℝ)/(p:ℝ)^k)^s
        ≤ Cw k * (p:ℝ)^(1+ε) * ((4:ℝ)/(p:ℝ))^s := by
      have hsnn : (0:ℝ) ≤ s := le_of_lt (Real.rpow_pos_of_pos h2R _)
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hBnn hB hsnn) ?_
      · rw [hCwk]
        exact mul_nonneg (le_of_lt hCwpos) (Real.rpow_nonneg hp0.le _)
    have hstep2 : Cw k * (p:ℝ)^(1+ε) * ((4:ℝ)/(p:ℝ))^s
        = (Cw k * (4:ℝ)^s) * (p:ℝ)^(((1:ℝ)+ε)-s) := by
      rw [Real.div_rpow (by norm_num) hp0.le s, div_eq_mul_inv, ← Real.rpow_neg hp0.le s]
      rw [show Cw k * (p:ℝ)^(1+ε) * ((4:ℝ)^s * (p:ℝ)^(-s))
          = (Cw k * (4:ℝ)^s) * ((p:ℝ)^(1+ε) * (p:ℝ)^(-s)) by ring]
      rw [← Real.rpow_add hp0]
      rw [show ((1:ℝ)+ε) + (-s) = ((1:ℝ)+ε) - s by ring]
    have hexp_le : (1:ℝ) + ε - s ≤ 1 - θ := by
      have hsk : s = 2 * (2:ℝ)^(-((k:ℝ))) := by
        rw [hsdef]
        rw [show (1:ℝ) - (k:ℝ) = 1 + (-((k:ℝ))) by ring, Real.rpow_add h2R]
        norm_num
      have hmono : (2:ℝ)^(-((n:ℝ))) ≤ (2:ℝ)^(-((k:ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk_le
        linarith
      rw [hsk, hεdef, hθdef]
      linarith
    have hstep3 : (Cw k * (4:ℝ)^s) * (p:ℝ)^(((1:ℝ)+ε)-s)
        ≤ (Cw k * (4:ℝ)^s) * (p:ℝ)^(1-θ) := by
      refine mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 hexp_le) ?_
      rw [hCwk]
      exact mul_nonneg (le_of_lt hCwpos) (Real.rpow_nonneg (by norm_num) s)
    have hstep4 : Cw k * (4:ℝ)^s ≤ Ctot := by
      rw [hCtotdef]
      have hmem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hk_le⟩
      have hterm : Cw k * (4:ℝ)^s
          ≤ ∑ j ∈ Finset.Icc 1 n, max (Cw j) 1 * (4:ℝ) ^ ((2:ℝ)^(1-(j:ℝ))) := by
        refine le_trans (mul_le_mul_of_nonneg_right (le_max_left (Cw k) (1:ℝ))
          (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) s)) ?_
        refine Finset.single_le_sum (f := fun j => max (Cw j) 1 * (4:ℝ)^((2:ℝ)^(1-(j:ℝ)))) ?_ hmem
        intro i _
        exact mul_nonneg (le_trans zero_le_one (le_max_right _ _))
          (Real.rpow_nonneg (by norm_num) _)
      linarith
    have hfinal : (Cw k * (4:ℝ)^s) * (p:ℝ)^(1-θ) ≤ Ctot * (p:ℝ)^(1-θ) :=
      mul_le_mul_of_nonneg_right hstep4 (Real.rpow_nonneg hp0.le _)
    refine le_trans hbound ?_
    refine le_trans hstep1 ?_
    rw [hstep2]
    exact le_trans hstep3 hfinal


/-- **Monotonicity of `ExpSumBound` in the saving.**  A saving `θ'` implies any
smaller saving `θ ≤ θ'` (with the same constant). -/
theorem expSumBound_mono (n : ℕ) {θ θ' : ℝ} (h : θ ≤ θ') (hh : ExpSumBound n θ') :
    ExpSumBound n θ := by
  obtain ⟨C, hC, hb⟩ := hh
  refine ⟨C, hC, ?_⟩
  intro p _inst hpn Q h1 h2
  refine (hb p hpn Q h1 h2).trans ?_
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 ?_) hC
  linarith

/-- **The per-prime §4 saving obtained from the Weyl bound**: with
`θ = 2^{-n}`, every nonzero Fourier coefficient of the index-`≥ k` residue set
satisfies `‖ĉ_p(a)‖ ≤ C·p^{n-k-2^{-n}}`. -/
theorem mIndexSaving_weyl (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ), k ≤ n →
      ∀ a : Fin n → ZMod p, a ≠ 0 →
        ‖indexFourierCoeff p n k a‖
          ≤ C * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - (2:ℝ)^(-(n:ℝ))) :=
  mIndexSaving_of_expSumBound n ((2:ℝ)^(-(n:ℝ)))
    (Real.rpow_pos_of_pos (by norm_num) _) (expSumBound_weyl n hn)

end

end Submission.Vdw
