import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.estQ3twoThreeAf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.estQ3twoThreeA` — FS `eq:EstimateQ3Tilde2+3` (`Q₃⁽²⁾ + Q₃⁽³⁾`)

The estimate of FS §10 controlling the second and third pieces of the
Bogoliubov-split cubic word `Q₃⁽²⁾ + Q₃⁽³⁾` by the kinetic reserve
`(𝓁²/2)∫_{P_H^q}𝒟_k b_k†b_k` on the quarter region `P_H^q`:

```
−C·e23A·‖Φ‖²  ≤  ⟨Φ, (Q₃⁽²⁾ + Q₃⁽³⁾ + (𝓁²/2)·dNumOpR P_H^q) Φ⟩   (Φ ∈ NWindow 𝓜).
```

## The two words and the commutator

With `p = -k`, `q = s − k` (for `Q₃⁽²⁾`) and `p = k − s`, `q = k` (for
`Q₃⁽³⁾`), each of the four monomials is of the form

`ã_s† b_p† b_q`  resp.  `b_q† b_p ã_s`,

and moving `ã_s†` (`ã_s`) past `b_p†` (`b_p`) costs a **scalar** commutator
(`taDag_bOpDag_swap`, `bOp_ta_swap`):

`[ã_s†, b_p†] = [b_p, ã_s] = −α_p·ccrX(s,−p) • 1`.

Hence the *pair* `ã_s†b_p†b_q + b_q†b_pã_s` has the quadratic form

`2⟨ã_s(b_pΦ), b_qΦ⟩ + 2σ_{sp}⟨b_qΦ, Φ⟩`,   `σ_{sp} = −α_p·ccrX(s,−p)`,

the first term an off-diagonal pairing of `ã_s(b_pΦ)` with `b_qΦ` (both factors
carrying the low/high momentum split), the second the "constant" part.

## The two absorptions

* The pairing term is bounded by `ε‖ã_s(b_pΦ)‖² + ε⁻¹‖b_qΦ‖²` (`bp_cauchy`).
  Summed over `s` with `ε = (𝓜+1)^{-1/2}` the first half is
  `√(𝓜+1)Σ_q‖b_qΦ‖²` (`NWindow_ta_sum`, the window of `b_pΦ` being `𝓜+1`) and
  the second half costs the *number* `N_f ≤ K₀(K_ℓK_L)³` of modes in the
  support of `f_L` (`Q3KernelFSAll.count_PL`, `k ↦ s−k` injective into `P_H^q`);
  both are absorbed by the reserve, whose weight is `𝒟_q ≥ 1/(64K_H²a²)` on
  `P_H^q` (`kernel_basic`).  This is `absorb_errA`'s first two conjuncts.
* The constant part is dominated by the *sum* `Σ_{k∈P_H}|Ŵ₁(k)α_k|`: by
  `|α_k| ≤ 2ρ|Ŵ₁(k)|/‖k‖²` on `P_H^q` and `sum_W1sq` this is at most
  `2ρK₀aℓ³` (`sum_W1alpha_le`), so the whole constant part is at most
  `C ρ a ℓ³ (K_ℓK_L)³ (|z|/ℓ³)𝓁η` — exactly `e23A` up to the factor `𝓁`
  (`absorb_errA`'s third conjunct).

Everything is asserted with one absolute constant `C` depending only on `K₀`.
-/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace Work.BoseC3QAll
open Work.BoseB7
variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
/-- **The operator core of `estQ3twoThreeA`.**  Everything after the thresholds:
the two splitting identities, the `ε`-Young bounds on the four families of
`(s,k)`-sums, the kinetic reserve and the arithmetic.  The abbreviations
(`Wc`, `Sσ`, `ε`, `Sf`, `Sq`, `Nf`, `Tq`, the coefficients `B2 B3 c2 c3` and the
vectors `u2 v2 u3 v3`) are *parameters* with their defining equations, so that
the elaboration of this argument does not carry the unfolded terms. -/
theorem twoThree_core (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (Φ : F.H)
    (Wc Sσ ε Nf Tq : ℝ) (Sf Sq : Finset Mode)
    (B2 B3 c2 c3 : Mode → Mode → ℝ) (u2 v2 u3 v3 : Mode → Mode → F.H)
    (hWcdef : Wc = 256 * (|E.z| / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille)
    (hSσdef : Sσ = 64 * K₀ ^ 2 * E.lille * eta E)
    (hεdef : ε = (Real.sqrt (E.bigM + 1))⁻¹)
    (hεmul : ε * (E.bigM + 1) = Real.sqrt (E.bigM + 1))
    (hεinv : ε⁻¹ = Real.sqrt (E.bigM + 1))
    (hSfdef : Sf = (excited Mode).filter (fun s => E.fL s ≠ 0))
    (hSqdef : Sq = (excited Mode).filter (F.PHq E.KH E.aScat))
    (hNfdef : Nf = (Sf.card : ℝ))
    (hTqdef : Tq = ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
    (hB2def : ∀ s k : Mode, B2 s k = (E.z / E.ell ^ 3) *
      (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)))
    (hB3def : ∀ s k : Mode, B3 s k = (E.z / E.ell ^ 3) *
      (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)))
    (hc2def : ∀ s k : Mode, c2 s k = -(E.alpha k * T.ccrX s k))
    (hc3def : ∀ s k : Mode, c3 s k = -(E.alpha (s - k) * T.ccrX s (s - k)))
    (hu2def : ∀ s k : Mode, u2 s k = T.ta s (F.bOp E.alpha (-k) Φ))
    (hv2def : ∀ s k : Mode, v2 s k = F.bOp E.alpha (s - k) Φ)
    (hu3def : ∀ s k : Mode, u3 s k = T.ta s (F.bOp E.alpha (k - s) Φ))
    (hv3def : ∀ s k : Mode, v3 s k = F.bOp E.alpha k Φ)
    (hαeven : ∀ k : Mode, E.alpha (-k) = E.alpha k)
    (hPHsub : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i)
    (hsubPHq : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      F.PHq E.KH E.aScat (s - k))
    (hHalf : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hαle : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hDq : ∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 4 ≤ E.D q)
    (hDen4 : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 → E.q3Denom s k ≤ 4)
    (hW1le : ∀ k : Mode, |E.W1 k| ≤ K₀ * E.aScat)
    (hfL0 : ∀ s : Mode, 0 ≤ E.fL s) (hfL1 : ∀ s : Mode, E.fL s ≤ 1)
    (hccr : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E)
    (hcount : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3)
    (hW1sum : ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤ 2 * E.rho * E.aScat * K₀ * E.ell ^ 3)
    (hW1sum_sub : ∀ s : Mode, E.fL s ≠ 0 →
      ∑ k ∈ F.PHset E, |E.W1 k * E.alpha (s - k)| ≤ 5 * E.rho * E.aScat * K₀ * E.ell ^ 3)
    (hbOpWin : ∀ k : Mode, T.NWindow (E.bigM + 1) (F.bOp E.alpha k Φ))
    (hell : 0 < E.ell) (ha : 0 < E.aScat) (hKl : 0 < E.Kl) (hKH : 0 < E.KH)
    (hKL : 0 < E.KL)
    (hmu : 0 < E.mu)
    (hlille_nn : 0 ≤ E.lille) (hη_nn : 0 ≤ eta E) (hK0 : 0 ≤ K₀) (hrho_nn : 0 ≤ E.rho)
    (hbigM : 0 ≤ E.bigM)
    (hzabs : |E.z| = Real.sqrt (E.rho * E.ell ^ 3))
    (hAbs1 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
              Real.sqrt (E.bigM + 1) * (1 + K₀ * (E.Kl * E.KL) ^ 3) *
              (128 * E.KH ^ 2 * E.aScat ^ 2) ≤ (1 / CtwoThree K₀) * E.lille ^ 2)
    (hAbs2 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
              (64 * K₀ ^ 2 * E.lille * eta E) * K₀ * (E.Kl * E.KL) ^ 3 *
              (128 * E.KH ^ 2 * E.aScat ^ 2) ≤ (1 / CtwoThree K₀) * E.lille ^ 2)
    (hAbs3 : 4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
              (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E)
            ≤ (1 / CtwoThree K₀) * e23A E)
 :    -(CtwoThree K₀ * e23A E) * F.normSq Φ ≤
      F.qw Φ (T.Q3twoT E + T.Q3threeT E + (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat))  := by
  classical
  have hCpos : 0 < CtwoThree K₀ := CtwoThree_pos K₀
  have hC2 : (2 : ℝ) ≤ CtwoThree K₀ := CtwoThree_ge_two K₀
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- ===================== basic nonnegativity =====================
  have hSf_sub : Sf ⊆ excited Mode := by
    rw [hSfdef]; exact Finset.filter_subset _ _
  have hSq_sub : Sq ⊆ excited Mode := by
    rw [hSqdef]; exact Finset.filter_subset _ _
  have hNf_nn : 0 ≤ Nf := by rw [hNfdef]; positivity
  have hTq_nn : 0 ≤ Tq := by
    rw [hTqdef]; exact Finset.sum_nonneg fun q _ => F.bp_nonneg _
  have hsqrt_nn : 0 ≤ Real.sqrt (E.bigM + 1) := Real.sqrt_nonneg _
  have hnormsq_nn : 0 ≤ F.normSq Φ := F.bp_nonneg Φ
  have hWc_nn : 0 ≤ Wc := by
    rw [hWcdef]
    have h1 : (0 : ℝ) ≤ |E.z| / E.ell ^ 3 := by positivity
    have h2 : (0 : ℝ) ≤ K₀ ^ 2 := sq_nonneg K₀
    have h3 : (0 : ℝ) ≤ E.aScat := ha.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3) hlille_nn
  have hSσ_nn : 0 ≤ Sσ := by
    rw [hSσdef]
    have h2 : (0 : ℝ) ≤ K₀ ^ 2 := sq_nonneg K₀
    have h1 : (0 : ℝ) ≤ eta E := by
      rw [eta]
      exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKl.le _) hlille_nn) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) hlille_nn) h1
  -- ===================== q3Denom positivity =====================
  have hDpos : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      0 < E.q3Denom s k := by
    intro s k hfL hk hW
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have h1 := hHalf k (hPHsub k hkPH)
    have h2 := hHalf (s - k) (hsubPHq s k hfL hk hW)
    rw [Q3Env.q3Denom]
    have h3 : 0 < (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) := by nlinarith
    exact one_div_pos.mpr h3
  -- ===================== coefficient bounds =====================
  have hA2leG : ∀ s k : Mode, k ∈ F.PHset E → E.W1 k ≠ 0 → |B2 s k| ≤ Wc := by
    intro s k hk hW
    by_cases hfL : E.fL s = 0
    · rw [hB2def]
      simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
      exact hWc_nn
    · have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
      have hkPHq : F.PHq E.KH E.aScat k := hPHsub k hkPH
      have hB : |E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k ≤
          256 * K₀ ^ 2 * E.aScat * E.lille := by
        have hf1 : |E.fL s| ≤ 1 := by
          rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
        have hw : |E.W1 k| ≤ K₀ * E.aScat := hW1le k
        have hal : |E.alpha k| ≤ 64 * K₀ * E.lille := hαle k hkPHq
        have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk hW
        have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk hW).le
        have h01 : (0 : ℝ) ≤ |E.fL s| * |E.W1 k| := by positivity
        have h02 : (0 : ℝ) ≤ |E.alpha k| := abs_nonneg _
        have h03 : (0 : ℝ) ≤ K₀ * E.aScat := mul_nonneg hK0 ha.le
        have h04 : (0 : ℝ) ≤ K₀ ^ 2 * E.aScat * E.lille :=
          mul_nonneg (mul_nonneg (sq_nonneg K₀) ha.le) hlille_nn
        have hstep1 : |E.fL s| * |E.W1 k| ≤ 1 * (K₀ * E.aScat) :=
          mul_le_mul hf1 hw (abs_nonneg _) (by norm_num)
        have hstep2 : |E.fL s| * |E.W1 k| * |E.alpha k| ≤
            (1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille) :=
          mul_le_mul hstep1 hal h02 (mul_nonneg (by norm_num) h03)
        calc |E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k
            ≤ ((1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille)) * 4 :=
              mul_le_mul hstep2 hd hd0 (by positivity)
          _ = 256 * K₀ ^ 2 * E.aScat * E.lille := by ring
      rw [hB2def]
      have habs : |E.z / E.ell ^ 3 * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))|
          = |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k) := by
        simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
          abs_of_nonneg (hDpos s k hfL hk hW).le]
      rw [habs]
      have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
      calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k)
          ≤ |E.z| / E.ell ^ 3 * (256 * K₀ ^ 2 * E.aScat * E.lille) :=
            mul_le_mul_of_nonneg_left hB hz3
        _ = Wc := by rw [hWcdef]; ring
  -- the guard-free wrapper: when `Ŵ₁ k = 0` the coefficient `B2 s k` vanishes
  have hB2_zero : ∀ s k : Mode, E.W1 k = 0 → B2 s k = 0 := by
    intro s k hW
    rw [hB2def]
    simp only [hW, mul_zero, zero_mul, neg_zero]
  have hA2le : ∀ s k : Mode, k ∈ F.PHset E → |B2 s k| ≤ Wc := by
    intro s k hk
    by_cases hW : E.W1 k = 0
    · rw [hB2_zero s k hW, abs_zero]
      exact hWc_nn
    · exact hA2leG s k hk hW
  have hA3leG : ∀ s k : Mode, k ∈ F.PHset E → E.W1 k ≠ 0 → |B3 s k| ≤ Wc := by
    intro s k hk hW
    by_cases hfL : E.fL s = 0
    · rw [hB3def]
      simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
      exact hWc_nn
    · have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
      have hkPHq : F.PHq E.KH E.aScat k := hPHsub k hkPH
      have hskPHq : F.PHq E.KH E.aScat (s - k) := hsubPHq s k hfL hk hW
      have hB : |E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k ≤
          256 * K₀ ^ 2 * E.aScat * E.lille := by
        have hf1 : |E.fL s| ≤ 1 := by
          rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
        have hw : |E.W1 k| ≤ K₀ * E.aScat := hW1le k
        have hal : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαle (s - k) hskPHq
        have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk hW
        have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk hW).le
        have h03 : (0 : ℝ) ≤ K₀ * E.aScat := mul_nonneg hK0 ha.le
        have hstep1 : |E.fL s| * |E.W1 k| ≤ 1 * (K₀ * E.aScat) :=
          mul_le_mul hf1 hw (abs_nonneg _) (by norm_num)
        have hstep2 : |E.fL s| * |E.W1 k| * |E.alpha (s - k)| ≤
            (1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille) :=
          mul_le_mul hstep1 hal (abs_nonneg _) (mul_nonneg (by norm_num) h03)
        calc |E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k
            ≤ ((1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille)) * 4 :=
              mul_le_mul hstep2 hd hd0 (by positivity)
          _ = 256 * K₀ ^ 2 * E.aScat * E.lille := by ring
      rw [hB3def]
      have habs : |E.z / E.ell ^ 3 * (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k))|
          = |E.z| / E.ell ^ 3 *
            (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k) := by
        simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
          abs_of_nonneg (hDpos s k hfL hk hW).le]
      rw [habs]
      have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
      calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k)
          ≤ |E.z| / E.ell ^ 3 * (256 * K₀ ^ 2 * E.aScat * E.lille) :=
            mul_le_mul_of_nonneg_left hB hz3
        _ = Wc := by rw [hWcdef]; ring
  -- again the guard-free wrapper
  have hB3_zero : ∀ s k : Mode, E.W1 k = 0 → B3 s k = 0 := by
    intro s k hW
    rw [hB3def]
    simp only [hW, mul_zero, zero_mul, neg_zero]
  have hA3le : ∀ s k : Mode, k ∈ F.PHset E → |B3 s k| ≤ Wc := by
    intro s k hk
    by_cases hW : E.W1 k = 0
    · rw [hB3_zero s k hW, abs_zero]
      exact hWc_nn
    · exact hA3leG s k hk hW
  have hc2le : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → |c2 s k| ≤ Sσ := by
    intro s k hfL hk
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hkPHq : F.PHq E.KH E.aScat k := hPHsub k hkPH
    have hal : |E.alpha k| ≤ 64 * K₀ * E.lille := hαle k hkPHq
    have hcc : |T.ccrX s k| ≤ K₀ * eta E := hccr s k hfL hkPHq
    rw [hc2def]
    rw [abs_neg, abs_mul]
    have h1 : |E.alpha k| * |T.ccrX s k| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) :=
      mul_le_mul hal hcc (abs_nonneg _) (by positivity)
    calc |E.alpha k| * |T.ccrX s k| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) := h1
      _ = Sσ := by rw [hSσdef]; ring
  have hc3le : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 → |c3 s k| ≤ Sσ := by
    intro s k hfL hk hW
    have hskPHq : F.PHq E.KH E.aScat (s - k) := hsubPHq s k hfL hk hW
    have hal : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαle (s - k) hskPHq
    have hcc : |T.ccrX s (s - k)| ≤ K₀ * eta E := hccr s (s - k) hfL hskPHq
    rw [hc3def]
    rw [abs_neg, abs_mul]
    have h1 : |E.alpha (s - k)| * |T.ccrX s (s - k)| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) :=
      mul_le_mul hal hcc (abs_nonneg _) (by positivity)
    calc |E.alpha (s - k)| * |T.ccrX s (s - k)| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) := h1
      _ = Sσ := by rw [hSσdef]; ring
  -- ===================== the two word identities =====================
  have hQ2 : F.qw Φ (T.Q3twoT E) = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
      B2 s k * (2 * F.bp (u2 s k) (v2 s k) + 2 * c2 s k * F.bp (v2 s k) Φ) := by
    rw [qw_Q3twoT_eq F T E Φ hαeven]
    simp only [hB2def, hc2def, hu2def, hv2def]
    refine (Finset.sum_subset (by rw [hSfdef]; exact Finset.filter_subset _ _) ?_).symm
    intro s hs hns
    have hfL : E.fL s = 0 := by
      by_contra h
      exact hns (by rw [hSfdef]; exact Finset.mem_filter.mpr ⟨hs, h⟩)
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hfL, mul_zero, neg_zero, zero_mul]
  have hQ3 : F.qw Φ (T.Q3threeT E) = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
      B3 s k * (2 * F.bp (u3 s k) (v3 s k) + 2 * c3 s k * F.bp (v3 s k) Φ) := by
    rw [qw_Q3threeT_eq F T E Φ hαeven]
    simp only [hB3def, hc3def, hu3def, hv3def]
    refine (Finset.sum_subset (by rw [hSfdef]; exact Finset.filter_subset _ _) ?_).symm
    intro s hs hns
    have hfL : E.fL s = 0 := by
      by_contra h
      exact hns (by rw [hSfdef]; exact Finset.mem_filter.mpr ⟨hs, h⟩)
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hfL, mul_zero, neg_zero, zero_mul]
  -- ===================== the per-word lower bounds =====================
  have hLB2 : -(∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
        (ε * F.bp (u2 s k) (u2 s k) + ε⁻¹ * F.bp (v2 s k) (v2 s k) +
          |c2 s k| * (F.bp (v2 s k) (v2 s k) + F.normSq Φ))) ≤ F.qw Φ (T.Q3twoT E) := by
    rw [hQ2, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    exact word_bound F Φ (u2 s k) (v2 s k) (B2 s k) (c2 s k) ε hεpos
  have hLB3 : -(∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| *
        (ε * F.bp (u3 s k) (u3 s k) + ε⁻¹ * F.bp (v3 s k) (v3 s k) +
          |c3 s k| * (F.bp (v3 s k) (v3 s k) + F.normSq Φ))) ≤ F.qw Φ (T.Q3threeT E) := by
    rw [hQ3, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    exact word_bound F Φ (u3 s k) (v3 s k) (B3 s k) (c3 s k) ε hεpos
  -- ===================== the region memberships =====================
  have hSq_mem : ∀ x : Mode, x ∈ Sq ↔ x ∈ excited Mode ∧ F.PHq E.KH E.aScat x := by
    intro x
    rw [hSqdef, Finset.mem_filter]
  have hSf_mem : ∀ s : Mode, s ∈ Sf ↔ s ∈ excited Mode ∧ E.fL s ≠ 0 := by
    intro s
    rw [hSfdef, Finset.mem_filter]
  have hmem_ph : ∀ k ∈ F.PHset E, k ∈ Sq := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact hSq_mem k |>.mpr ⟨hk'.1, hPHsub k hk'.2⟩
  have hmem_neg : ∀ k ∈ F.PHset E, -k ∈ Sq := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    refine hSq_mem (-k) |>.mpr ⟨?_, ?_⟩
    · rw [Work.BoseB7.excited, Finset.mem_erase]
      exact ⟨neg_ne_zero.mpr (Finset.mem_erase.mp hk'.1).1, Finset.mem_univ _⟩
    · have h2 : F.PHq E.KH E.aScat k := hPHsub k hk'.2
      simp only [FockData.PHq] at h2 ⊢
      rw [F.kmom_neg k, norm_neg]
      exact h2
  have hmem_sub : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → s - k ∈ Sq := by
    intro s hs k hk hW
    have hs' := (hSf_mem s).mp hs
    have h1 := hsubPHq s k hs'.2 hk hW
    refine hSq_mem (s - k) |>.mpr ⟨?_, h1⟩
    rw [Work.BoseB7.excited, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h0
    have h2 : F.kmom (s - k) = 0 := by rw [h0, kmom_zero]
    have h3 : 0 < ‖F.kmom (s - k)‖ := by
      have h4 : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
      simp only [FockData.PHq] at h1
      linarith [h1]
    rw [h2, norm_zero] at h3
    exact absurd h3 (lt_irrefl 0)
  have hmem_ksub : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → k - s ∈ Sq := by
    intro s hs k hk hW
    have hs' := (hSf_mem s).mp hs
    have h1 := hsubPHq s k hs'.2 hk hW
    have h2 : F.PHq E.KH E.aScat (k - s) := by
      simp only [FockData.PHq] at h1 ⊢
      have he : F.kmom (k - s) = -(F.kmom (s - k)) := by
        rw [show k - s = -(s - k) from by abel, F.kmom_neg]
      rw [he, norm_neg]
      exact h1
    refine hSq_mem (k - s) |>.mpr ⟨?_, h2⟩
    rw [Work.BoseB7.excited, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h0
    have h3 : F.kmom (k - s) = 0 := by rw [h0, kmom_zero]
    have h4 : 0 < ‖F.kmom (k - s)‖ := by
      have h5 : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
      simp only [FockData.PHq] at h2
      linarith [h2]
    rw [h3, norm_zero] at h4
    exact absurd h4 (lt_irrefl 0)
  -- ===================== the coefficient sum =====================
  have hcoefsum : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)
      ≤ Nf * (4 * (|E.z| / E.ell ^ 3) * (2 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
    have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)
        ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := by
      refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => ?_
      have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
      by_cases hW : E.W1 k = 0
      · rw [hB2_zero s k hW, hW]
        simp
      · have h3 : |B2 s k| ≤ 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := by
          rw [hB2def]
          have habs : |E.z / E.ell ^ 3 * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))|
              = |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k) := by
            simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
              abs_of_nonneg (hDpos s k hfL hk hW).le]
          rw [habs]
          have hf1 : |E.fL s| ≤ 1 := by
            rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
          have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk hW
          have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk hW).le
          have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
          calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k)
              ≤ |E.z| / E.ell ^ 3 * (1 * |E.W1 k * E.alpha k| * 4) := by
                refine mul_le_mul_of_nonneg_left ?_ hz3
                have h4 : |E.fL s| * (|E.W1 k| * |E.alpha k|) ≤ 1 * (|E.W1 k| * |E.alpha k|) :=
                  mul_le_mul_of_nonneg_right hf1 (by positivity)
                nlinarith [h4, hd, hd0, abs_nonneg (E.W1 k * E.alpha k),
                  abs_mul (E.W1 k) (E.alpha k)]
            _ = 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := by ring
        exact h3
    have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k|)
        = Nf * (4 * (|E.z| / E.ell ^ 3) * (∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)) := by
      rw [sum_const_mul_sum]
      rw [Finset.sum_const, nsmul_eq_mul, hNfdef]
      ring
    have h3 : (∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|) ≤ 2 * E.rho * E.aScat * K₀ * E.ell ^ 3 :=
      hW1sum
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)
        ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := h1
      _ = Nf * (4 * (|E.z| / E.ell ^ 3) * (∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)) := h2
      _ ≤ Nf * (4 * (|E.z| / E.ell ^ 3) * (2 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNf_nn
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  -- ===================== the eight sum bounds =====================
  exact twoThree_core_mid K₀ F T E Φ Wc Sσ ε Nf Tq Sf Sq B2 B3 c2 c3 u2 v2 u3 v3 hWcdef hSσdef hεdef hεmul hεinv hSfdef hSqdef hNfdef hTqdef hB2def hB3def hc2def hc3def hu2def hv2def hu3def hv3def hαeven hPHsub hsubPHq hHalf hαle hDq hDen4 hW1le hfL0 hfL1 hccr hcount hW1sum hW1sum_sub hbOpWin hell ha hKl hKH hKL hmu hlille_nn hη_nn hK0 hrho_nn hbigM hzabs hAbs1 hAbs2 hAbs3 hCpos hC2 hεpos hSf_sub hSq_sub hNf_nn hTq_nn hsqrt_nn hnormsq_nn hWc_nn hSσ_nn hDpos hA2leG hB2_zero hA2le hA3leG hB3_zero hA3le hc2le hc3le hQ2 hQ3 hLB2 hLB3 hSq_mem hSf_mem hmem_ph hmem_neg hmem_sub hmem_ksub hcoefsum
