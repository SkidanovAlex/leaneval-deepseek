import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.estQ3twoThreeAb
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
/-- Continuation of `twoThree_core` (see the module docstring of
`Submission.Work.BoseC3QAll.estQ3twoThreeAc`): the same statement proved
from item 40 on, with the preceding `have`s as hypotheses. -/
theorem twoThree_core_tail (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
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
    (hCpos : 0 < CtwoThree K₀)
    (hC2 : (2 : ℝ) ≤ CtwoThree K₀)
    (hεpos : 0 < ε)
    (hSf_sub : Sf ⊆ excited Mode)
    (hSq_sub : Sq ⊆ excited Mode)
    (hNf_nn : 0 ≤ Nf)
    (hTq_nn : 0 ≤ Tq)
    (hsqrt_nn : 0 ≤ Real.sqrt (E.bigM + 1))
    (hnormsq_nn : 0 ≤ F.normSq Φ)
    (hWc_nn : 0 ≤ Wc)
    (hSσ_nn : 0 ≤ Sσ)
    (hDpos : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      0 < E.q3Denom s k)
    (hA2leG : ∀ s k : Mode, k ∈ F.PHset E → E.W1 k ≠ 0 → |B2 s k| ≤ Wc)
    (hB2_zero : ∀ s k : Mode, E.W1 k = 0 → B2 s k = 0)
    (hA2le : ∀ s k : Mode, k ∈ F.PHset E → |B2 s k| ≤ Wc)
    (hA3leG : ∀ s k : Mode, k ∈ F.PHset E → E.W1 k ≠ 0 → |B3 s k| ≤ Wc)
    (hB3_zero : ∀ s k : Mode, E.W1 k = 0 → B3 s k = 0)
    (hA3le : ∀ s k : Mode, k ∈ F.PHset E → |B3 s k| ≤ Wc)
    (hc2le : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → |c2 s k| ≤ Sσ)
    (hc3le : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 → |c3 s k| ≤ Sσ)
    (hQ2 : F.qw Φ (T.Q3twoT E) = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
      B2 s k * (2 * F.bp (u2 s k) (v2 s k) + 2 * c2 s k * F.bp (v2 s k) Φ))
    (hQ3 : F.qw Φ (T.Q3threeT E) = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
      B3 s k * (2 * F.bp (u3 s k) (v3 s k) + 2 * c3 s k * F.bp (v3 s k) Φ))
    (hLB2 : -(∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
        (ε * F.bp (u2 s k) (u2 s k) + ε⁻¹ * F.bp (v2 s k) (v2 s k) +
          |c2 s k| * (F.bp (v2 s k) (v2 s k) + F.normSq Φ))) ≤ F.qw Φ (T.Q3twoT E))
    (hLB3 : -(∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| *
        (ε * F.bp (u3 s k) (u3 s k) + ε⁻¹ * F.bp (v3 s k) (v3 s k) +
          |c3 s k| * (F.bp (v3 s k) (v3 s k) + F.normSq Φ))) ≤ F.qw Φ (T.Q3threeT E))
    (hSq_mem : ∀ x : Mode, x ∈ Sq ↔ x ∈ excited Mode ∧ F.PHq E.KH E.aScat x)
    (hSf_mem : ∀ s : Mode, s ∈ Sf ↔ s ∈ excited Mode ∧ E.fL s ≠ 0)
    (hmem_ph : ∀ k ∈ F.PHset E, k ∈ Sq)
    (hmem_neg : ∀ k ∈ F.PHset E, -k ∈ Sq)
    (hmem_sub : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → s - k ∈ Sq)
    (hmem_ksub : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → k - s ∈ Sq)
    (hcoefsum : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)
      ≤ Nf * (4 * (|E.z| / E.ell ^ 3) * (2 * E.rho * E.aScat * K₀ * E.ell ^ 3)))
    (hu2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
      ≤ Wc * (ε * (E.bigM + 1)) * Tq)
    (hu3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε * F.bp (u3 s k) (u3 s k)))
      ≤ Wc * (ε * (E.bigM + 1)) * Tq)
    (hv2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
      ≤ Wc * (ε⁻¹ * Nf) * Tq)
    (hv3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
      ≤ Wc * (ε⁻¹ * Nf) * Tq)
    (hσ2a : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
      ≤ Wc * Sσ * Nf * Tq)
    (hσ3a : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
      ≤ Wc * Sσ * Nf * Tq)
    (hσ2b : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
      ≤ (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ)
    (hσ3b : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
      ≤ (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ)
 :    -(CtwoThree K₀ * e23A E) * F.normSq Φ ≤
      F.qw Φ (T.Q3twoT E + T.Q3threeT E + (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat))  := by
  classical
  have hres : (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq
      ≤ F.qw Φ ((E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) := by
    have hDlb : ∀ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
        1 / (64 * E.KH ^ 2 * E.aScat ^ 2) ≤ E.D q := by
      intro q hq
      have hqPH : F.PHq E.KH E.aScat q := (Finset.mem_filter.mp hq).2
      have h1 : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom q‖ := hqPH
      have h2 : ‖F.kmom q‖ ^ 2 / 4 ≤ E.D q := hDq q hqPH
      have h3 : 1 / (64 * E.KH ^ 2 * E.aScat ^ 2) ≤ ‖F.kmom q‖ ^ 2 / 4 := by
        have h4 : 1 / (64 * E.KH ^ 2 * E.aScat ^ 2)
            = (1 / (4 * E.KH * E.aScat)) ^ 2 * (4 : ℝ)⁻¹ := by
          field_simp
          ring
        rw [h4]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) h1 2) (by norm_num)
      exact h3.trans h2
    rw [qw_smul', qw_dNumOpR_eq F T E Φ, hTqdef, hSqdef]
    have hstep : (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          (1 / (64 * E.KH ^ 2 * E.aScat ^ 2)) * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
        ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) := by
      refine Finset.sum_le_sum fun q hq => ?_
      exact mul_le_mul_of_nonneg_right (hDlb q hq) (F.bp_nonneg _)
    calc (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) *
          (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
        = (E.lille ^ 2 / 2) * ((1 / (64 * E.KH ^ 2 * E.aScat ^ 2)) *
            (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))) := by ring
      _ = (E.lille ^ 2 / 2) * (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            (1 / (64 * E.KH ^ 2 * E.aScat ^ 2)) *
              F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ)) := by
          rw [Finset.mul_sum]
      _ ≤ (E.lille ^ 2 / 2) * (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  -- ===================== the three numeric conditions =====================
  have he23nn : 0 ≤ e23A E := by
    rw [e23A]
    refine mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
    · exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKl.le _) hlille_nn) _
    · positivity
    · exact Real.rpow_nonneg hKl.le _
    · exact Real.rpow_nonneg (mul_nonneg hmu.le (pow_nonneg ha.le 3)) _
  have hIcost : 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf) * Tq
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    have hNf_le : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
      rw [hNfdef]
      have := hcount
      rwa [hSfdef]
    have hWcz : Wc = 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille := by
      rw [hWcdef, hzabs]
    have hpos : 0 < 128 * E.KH ^ 2 * E.aScat ^ 2 := by positivity
    have h1 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          Real.sqrt (E.bigM + 1) * (1 + K₀ * (E.Kl * E.KL) ^ 3) *
          (128 * E.KH ^ 2 * E.aScat ^ 2)
        ≤ (1 / CtwoThree K₀) * E.lille ^ 2 := hAbs1
    have h2 : 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf)
        ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) := by
      rw [show (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))
          = ((1 / CtwoThree K₀) * E.lille ^ 2) / (128 * E.KH ^ 2 * E.aScat ^ 2) from by ring]
      rw [le_div_iff₀ hpos]
      rw [hWcz]
      have hNf2 : 2 * (1 + Nf) ≤ 4 * (1 + K₀ * (E.Kl * E.KL) ^ 3) := by linarith
      have hA0 : 0 ≤ (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          Real.sqrt (E.bigM + 1) * (128 * E.KH ^ 2 * E.aScat ^ 2) := by positivity
      nlinarith [h1, hNf2, hA0, hlille_nn, hNf_nn, hsqrt_nn, hWc_nn]
    calc 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf) * Tq
        = (2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf)) * Tq := by ring
      _ ≤ ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))) * Tq :=
          mul_le_mul_of_nonneg_right h2 hTq_nn
      _ = (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by ring
  have hScost : 2 * Wc * Sσ * Nf * Tq
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    have hNf_le : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
      rw [hNfdef]
      have := hcount
      rwa [hSfdef]
    have hWcz : Wc = 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille := by
      rw [hWcdef, hzabs]
    have hSσz : Sσ = 64 * K₀ ^ 2 * E.lille * eta E := by rw [hSσdef]
    have hpos : 0 < 128 * E.KH ^ 2 * E.aScat ^ 2 := by positivity
    have h1 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          (64 * K₀ ^ 2 * E.lille * eta E) * K₀ * (E.Kl * E.KL) ^ 3 *
          (128 * E.KH ^ 2 * E.aScat ^ 2)
        ≤ (1 / CtwoThree K₀) * E.lille ^ 2 := hAbs2
    have h2 : 2 * Wc * Sσ * Nf
        ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) := by
      rw [show (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))
          = ((1 / CtwoThree K₀) * E.lille ^ 2) / (128 * E.KH ^ 2 * E.aScat ^ 2) from by ring]
      rw [le_div_iff₀ hpos]
      rw [hWcz, hSσz]
      have hNf2 : 2 * Nf ≤ 4 * (K₀ * (E.Kl * E.KL) ^ 3) := by linarith
      have hA0 : 0 ≤ (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          (64 * K₀ ^ 2 * E.lille * eta E) * (128 * E.KH ^ 2 * E.aScat ^ 2) := by positivity
      nlinarith [h1, hNf2, hA0, hlille_nn, hNf_nn, hη_nn, hK0]
    calc 2 * Wc * Sσ * Nf * Tq = (2 * Wc * Sσ * Nf) * Tq := by ring
      _ ≤ ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))) * Tq :=
          mul_le_mul_of_nonneg_right h2 hTq_nn
      _ = (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by ring
  have hEcost :
      (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
        + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
      ≤ CtwoThree K₀ * e23A E * F.normSq Φ := by
    have h28 : (28 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ)
        ≤ CtwoThree K₀ * e23A E := by
      have hNf_le : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
        rw [hNfdef]
        have := hcount
        rwa [hSfdef]
      have hstep1 : (28 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ)
          ≤ 32 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (E.rho * E.aScat * K₀ * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E) := by
        rw [hzabs, hSσdef]
        have hfac : 0 ≤ (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.rho * E.aScat * K₀ *
            E.ell ^ 3 * (64 * K₀ ^ 2 * E.lille * eta E) := by positivity
        have hKL3 : 0 ≤ (E.Kl * E.KL) ^ 3 := by positivity
        nlinarith [hNf_le, hfac, hKL3, hK0, hlille_nn, hη_nn, hNf_nn, ha.le, hrho_nn,
          Real.sqrt_nonneg (E.rho * E.ell ^ 3), sq_nonneg K₀]
      have hstep2 : 32 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (E.rho * E.aScat * K₀ * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E)
          = 4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E) := by ring
      have h3 : (1 / CtwoThree K₀) * e23A E ≤ CtwoThree K₀ * e23A E := by
        have h4 : (1 / CtwoThree K₀) ≤ CtwoThree K₀ := by
          rw [div_le_iff₀ hCpos]
          nlinarith [hC2]
        exact mul_le_mul_of_nonneg_right h4 he23nn
      exact hstep1.trans ((hstep2.symm ▸ hAbs3).trans h3)
    have hcomb : (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
        + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
        = (28 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
            F.normSq Φ := by ring
    rw [hcomb]
    exact mul_le_mul_of_nonneg_right h28 hnormsq_nn
  -- ===================== the final assembly =====================
  have hsplit2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
        (ε * F.bp (u2 s k) (u2 s k) + ε⁻¹ * F.bp (v2 s k) (v2 s k) +
          |c2 s k| * (F.bp (v2 s k) (v2 s k) + F.normSq Φ)))
      = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ)) := by
    rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
          (ε * F.bp (u2 s k) (u2 s k) + ε⁻¹ * F.bp (v2 s k) (v2 s k) +
            |c2 s k| * (F.bp (v2 s k) (v2 s k) + F.normSq Φ)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            ((|B2 s k| * (ε * F.bp (u2 s k) (u2 s k)) +
                |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k))) +
              (|B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)) +
                |B2 s k| * (|c2 s k| * F.normSq Φ))) from by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
    simp only [Finset.sum_add_distrib]
    abel
  have hsplit3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| *
        (ε * F.bp (u3 s k) (u3 s k) + ε⁻¹ * F.bp (v3 s k) (v3 s k) +
          |c3 s k| * (F.bp (v3 s k) (v3 s k) + F.normSq Φ)))
      = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε * F.bp (u3 s k) (u3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ)) := by
    rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| *
          (ε * F.bp (u3 s k) (u3 s k) + ε⁻¹ * F.bp (v3 s k) (v3 s k) +
            |c3 s k| * (F.bp (v3 s k) (v3 s k) + F.normSq Φ)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            ((|B3 s k| * (ε * F.bp (u3 s k) (u3 s k)) +
                |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k))) +
              (|B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)) +
                |B3 s k| * (|c3 s k| * F.normSq Φ))) from by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
    simp only [Finset.sum_add_distrib]
    abel
  have htot8 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε * F.bp (u3 s k) (u3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
      ≤ 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
        + 2 * (Wc * Sσ * Nf * Tq)
        + ((8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
          + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
              F.normSq Φ) := by
    linarith [hu2, hu3, hv2, hv3, hσ2a, hσ3a, hσ2b, hσ3b]
  have hIcost2 : 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    have heq : 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
        = 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf) * Tq := by
      rw [hεmul, hεinv]
      ring
    rw [heq]
    exact hIcost
  have hScost2 : 2 * (Wc * Sσ * Nf * Tq)
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    rw [show 2 * (Wc * Sσ * Nf * Tq) = 2 * Wc * Sσ * Nf * Tq from by ring]
    exact hScost
  have hcinv2 : 2 * (1 / CtwoThree K₀) ≤ 1 := by
    rw [show 2 * (1 / CtwoThree K₀) = 2 / CtwoThree K₀ from by ring, div_le_one hCpos]
    linarith [hC2]
  have hmain : -(CtwoThree K₀ * e23A E * F.normSq Φ)
      ≤ F.qw Φ (T.Q3twoT E + T.Q3threeT E +
          (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) := by
    rw [FockData.qw_add, FockData.qw_add]
    have h2 := hLB2
    have h3 := hLB3
    rw [hsplit2] at h2
    rw [hsplit3] at h3
    have hreslb := hres
    have hnum : 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
        + 2 * (Wc * Sσ * Nf * Tq)
        + ((8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
          + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
              F.normSq Φ)
        ≤ 2 * ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq)
          + CtwoThree K₀ * e23A E * F.normSq Φ := by
      linarith [hIcost2, hScost2, hEcost]
    have hresnn' : 0 ≤ (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq :=
      mul_nonneg (by positivity) hTq_nn
    have h22 : 2 * ((1 / CtwoThree K₀) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq))
        ≤ (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
      have h1 := mul_le_mul_of_nonneg_right hcinv2 hresnn'
      calc 2 * ((1 / CtwoThree K₀) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq))
          = (2 * (1 / CtwoThree K₀)) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq) := by ring
        _ ≤ 1 * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq) := h1
        _ = (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by ring
    have heq : 2 * ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq)
        = 2 * ((1 / CtwoThree K₀) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq)) := by
      ring
    linarith [h2, h3, hreslb, htot8, hnum, hTq_nn, hnormsq_nn, h22, heq]

  rw [show -(CtwoThree K₀ * e23A E) * F.normSq Φ
        = -(CtwoThree K₀ * e23A E * F.normSq Φ) from by ring]
  exact hmain

