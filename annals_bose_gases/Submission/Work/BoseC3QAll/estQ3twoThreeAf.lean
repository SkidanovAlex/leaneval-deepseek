import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseC3QAll.estQ3twoThreeAe
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
from item 32 on, with the preceding `have`s as hypotheses. -/
theorem twoThree_core_mid (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
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
 :    -(CtwoThree K₀ * e23A E) * F.normSq Φ ≤
      F.qw Φ (T.Q3twoT E + T.Q3threeT E + (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat))  := by
  classical
  have hu2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
      ≤ Wc * (ε * (E.bigM + 1)) * Tq := by
    have hR : (∑ k ∈ F.PHset E,
          F.bp (F.bOp E.alpha (-k) Φ) (F.bOp E.alpha (-k) Φ)) ≤ Tq := by
      rw [hTqdef]
      exact sum_le_sum_of_inj (t := F.PHset E) (u := Sq) (φ := fun k => -k)
        (f := fun p => F.bp (F.bOp E.alpha p Φ) (F.bOp E.alpha p Φ))
        (fun i j hij => neg_inj.mp hij) (fun k hk => hmem_neg k hk)
        (fun p => F.bp_nonneg _)
    have h := sum_u_le F T E (M := E.bigM) (by linarith) (ε := ε) (Wc := Wc) hεpos hWc_nn
      (c := B2) (fun s k hk => hA2le s k hk)
      (g := fun k => F.bOp E.alpha (-k) Φ) (fun k => hbOpWin (-k))
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
            (ε * F.bp (T.ta s (F.bOp E.alpha (-k) Φ)) (T.ta s (F.bOp E.alpha (-k) Φ))) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hu2def]
      _ ≤ ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, |B2 s k| *
            (ε * F.bp (T.ta s (F.bOp E.alpha (-k) Φ)) (T.ta s (F.bOp E.alpha (-k) Φ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hSf_sub (fun s _ _ =>
            Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _)
              (mul_nonneg hεpos.le (F.bp_nonneg _)))
      _ ≤ Wc * (ε * (E.bigM + 1)) *
            (∑ k ∈ F.PHset E, F.bp (F.bOp E.alpha (-k) Φ) (F.bOp E.alpha (-k) Φ)) := h
      _ ≤ Wc * (ε * (E.bigM + 1)) * Tq :=
          mul_le_mul_of_nonneg_left hR (by positivity)
  have hu3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε * F.bp (u3 s k) (u3 s k)))
      ≤ Wc * (ε * (E.bigM + 1)) * Tq := by
    have h := sum_u3_le F T E Φ (M := E.bigM) (by linarith) (ε := ε) (Wc := Wc) (Tq := Tq)
      hεpos hWc_nn (Sf := Sf) (Sq := Sq) hSf_sub hTqdef (fun p => hbOpWin p)
      (c := B3) (fun s k hk => hA3le s k hk) (fun s k _ hW => hB3_zero s k hW) hmem_ksub
    simpa only [hu3def] using h
  have hv2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
      ≤ Wc * (ε⁻¹ * Nf) * Tq := by
    have h := sum_bsub_le F T E Φ (Wc := Wc) (Nf := Nf) (Tq := Tq) hWc_nn
      (Sf := Sf) (Sq := Sq) hNfdef hTqdef (c := B2)
      (fun s k hk => hA2le s k hk) (fun s k _ hW => hB2_zero s k hW) hmem_sub
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E, ε⁻¹ * (|B2 s k| * F.bp (v2 s k) (v2 s k)) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, (|B2 s k| * F.bp (v2 s k) (v2 s k)) :=
          sum_const_mul_sum Sf (F.PHset E) ε⁻¹ _
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            (|B2 s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)) := by
          simp only [hv2def]
      _ ≤ ε⁻¹ * (Wc * Nf * Tq) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = Wc * (ε⁻¹ * Nf) * Tq := by ring
  have hv3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
      ≤ Wc * (ε⁻¹ * Nf) * Tq := by
    have h := sum_b_le F T E Φ (Wc := Wc) (Nf := Nf) (Tq := Tq) hWc_nn
      (Sf := Sf) (Sq := Sq) hNfdef hTqdef (c := B3)
      (fun s k hk => hA3le s k hk) hmem_ph
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E, ε⁻¹ * (|B3 s k| * F.bp (v3 s k) (v3 s k)) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, (|B3 s k| * F.bp (v3 s k) (v3 s k)) :=
          sum_const_mul_sum Sf (F.PHset E) ε⁻¹ _
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            (|B3 s k| * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ)) := by
          simp only [hv3def]
      _ ≤ ε⁻¹ * (Wc * Nf * Tq) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = Wc * (ε⁻¹ * Nf) * Tq := by ring
  -- the σ-weighted norms
  have hσ2a : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
      ≤ Wc * Sσ * Nf * Tq := by
    have hc : ∀ s k : Mode, k ∈ F.PHset E → |B2 s k * c2 s k| ≤ Wc * Sσ := by
      intro s k hk
      rw [abs_mul]
      by_cases hfL : E.fL s = 0
      · rw [hB2def]
        simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
        exact mul_nonneg hWc_nn hSσ_nn
      · exact mul_le_mul (hA2le s k hk) (hc2le s k hfL hk) (abs_nonneg _) hWc_nn
    have h := sum_bsub_le F T E Φ (Wc := Wc * Sσ) (Nf := Nf) (Tq := Tq)
      (mul_nonneg hWc_nn hSσ_nn) (Sf := Sf) (Sq := Sq) hNfdef hTqdef
      (c := fun s k => B2 s k * c2 s k) hc
      (fun s k _ hW => by rw [hB2_zero s k hW, zero_mul]) hmem_sub
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            |B2 s k * c2 s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
          rw [abs_mul_abs_mul, hv2def]
      _ ≤ (Wc * Sσ) * Nf * Tq := h
      _ = Wc * Sσ * Nf * Tq := by ring
  have hσ3a : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
      ≤ Wc * Sσ * Nf * Tq := by
    have hc : ∀ s k : Mode, k ∈ F.PHset E → |B3 s k * c3 s k| ≤ Wc * Sσ := by
      intro s k hk
      rw [abs_mul]
      by_cases hfL : E.fL s = 0
      · rw [hB3def]
        simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
        exact mul_nonneg hWc_nn hSσ_nn
      · by_cases hW : E.W1 k = 0
        · rw [hB3def, hW]
          simp only [mul_zero, neg_zero, zero_mul, abs_zero]
          exact mul_nonneg hWc_nn hSσ_nn
        · exact mul_le_mul (hA3leG s k hk hW) (hc3le s k hfL hk hW) (abs_nonneg _) hWc_nn
    have h := sum_b_le F T E Φ (Wc := Wc * Sσ) (Nf := Nf) (Tq := Tq)
      (mul_nonneg hWc_nn hSσ_nn) (Sf := Sf) (Sq := Sq) hNfdef hTqdef
      (c := fun s k => B3 s k * c3 s k) hc hmem_ph
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            |B3 s k * c3 s k| * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
          rw [abs_mul_abs_mul, hv3def]
      _ ≤ (Wc * Sσ) * Nf * Tq := h
      _ = Wc * Sσ * Nf * Tq := by ring
  -- the constants
  have hσ2b : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
      ≤ (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ := by
    have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|) * F.normSq Φ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|)
        ≤ Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|) := by
      have h3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|)
          ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * Sσ := by
        refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => ?_
        have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
        exact mul_le_mul_of_nonneg_left (hc2le s k hfL hk) (abs_nonneg _)
      refine h3.trans ?_
      rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * Sσ)
          = Sσ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring]
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|) * F.normSq Φ := h1
      _ ≤ (Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)) * F.normSq Φ :=
          mul_le_mul_of_nonneg_right h2 hnormsq_nn
      _ ≤ (Sσ * (Nf * (4 * (|E.z| / E.ell ^ 3) * (2 * E.rho * E.aScat * K₀ * E.ell ^ 3)))) *
            F.normSq Φ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoefsum hSσ_nn) hnormsq_nn
      _ = (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
            F.normSq Φ := by ring
  have hσ3b : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
      ≤ (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ := by
    have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|) * F.normSq Φ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|)
        ≤ Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|) := by
      have h3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|)
          ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * Sσ := by
        refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => ?_
        have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
        by_cases hW : E.W1 k = 0
        · rw [hB3def, hW]
          simp
        · exact mul_le_mul_of_nonneg_left (hc3le s k hfL hk hW) (abs_nonneg _)
      refine h3.trans ?_
      rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * Sσ)
          = Sσ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring]
    have hcoefsum3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|)
        ≤ Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
      have h3 : ∀ s ∈ Sf, (∑ k ∈ F.PHset E, |B3 s k|)
          ≤ 4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3) := by
        intro s hs
        have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
        have h4 : (∑ k ∈ F.PHset E, |B3 s k|)
            ≤ ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha (s - k)| := by
          refine Finset.sum_le_sum fun k hk => ?_
          by_cases hW : E.W1 k = 0
          · rw [hB3_zero s k hW, hW]
            simp
          · rw [hB3def]
            have habs : |E.z / E.ell ^ 3 *
                  (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k))|
                = |E.z| / E.ell ^ 3 *
                  (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k) := by
              simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
                abs_of_nonneg (hDpos s k hfL hk hW).le]
            rw [habs]
            have hf1 : |E.fL s| ≤ 1 := by
              rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
            have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk hW
            have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk hW).le
            have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
            calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k)
                ≤ |E.z| / E.ell ^ 3 * (1 * (|E.W1 k| * |E.alpha (s - k)|) * 4) := by
                  refine mul_le_mul_of_nonneg_left ?_ hz3
                  have h5 : |E.fL s| * (|E.W1 k| * |E.alpha (s - k)|) ≤
                      1 * (|E.W1 k| * |E.alpha (s - k)|) :=
                    mul_le_mul_of_nonneg_right hf1 (by positivity)
                  have h6 : 0 ≤ 1 * (|E.W1 k| * |E.alpha (s - k)|) := by positivity
                  have h7 : |E.fL s| * (|E.W1 k| * |E.alpha (s - k)|) * E.q3Denom s k
                      ≤ (1 * (|E.W1 k| * |E.alpha (s - k)|)) * 4 :=
                    mul_le_mul h5 hd hd0 h6
                  nlinarith [h7]
              _ = 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha (s - k)| := by
                  rw [abs_mul]; ring
        refine h4.trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hW1sum_sub s hfL) (by positivity)
      have h2 : (∑ s ∈ Sf, 4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3))
          = Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hNfdef]
      calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|)
          ≤ ∑ s ∈ Sf, 4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3) :=
            Finset.sum_le_sum h3
        _ = Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := h2
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|) * F.normSq Φ := h1
      _ ≤ (Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|)) * F.normSq Φ :=
          mul_le_mul_of_nonneg_right h2 hnormsq_nn
      _ ≤ (Sσ * (Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)))) *
            F.normSq Φ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoefsum3 hSσ_nn) hnormsq_nn
      _ = (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
            F.normSq Φ := by ring
  -- ===================== the reserve =====================
  exact twoThree_core_tail K₀ F T E Φ Wc Sσ ε Nf Tq Sf Sq B2 B3 c2 c3 u2 v2 u3 v3 hWcdef hSσdef hεdef hεmul hεinv hSfdef hSqdef hNfdef hTqdef hB2def hB3def hc2def hc3def hu2def hv2def hu3def hv3def hαeven hPHsub hsubPHq hHalf hαle hDq hDen4 hW1le hfL0 hfL1 hccr hcount hW1sum hW1sum_sub hbOpWin hell ha hKl hKH hKL hmu hlille_nn hη_nn hK0 hrho_nn hbigM hzabs hAbs1 hAbs2 hAbs3 hCpos hC2 hεpos hSf_sub hSq_sub hNf_nn hTq_nn hsqrt_nn hnormsq_nn hWc_nn hSσ_nn hDpos hA2leG hB2_zero hA2le hA3leG hB3_zero hA3le hc2le hc3le hQ2 hQ3 hLB2 hLB3 hSq_mem hSf_mem hmem_ph hmem_neg hmem_sub hmem_ksub hcoefsum hu2 hu3 hv2 hv3 hσ2a hσ3a hσ2b hσ3b
