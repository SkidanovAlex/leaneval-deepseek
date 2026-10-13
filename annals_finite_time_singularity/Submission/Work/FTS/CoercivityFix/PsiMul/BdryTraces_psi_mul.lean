/-
Copyright: work module for the Elgindi finite-time singularity project.

# `BdryTraces α k` is preserved by multiplication with a bounded radial multiplier

`Work.FTS.Nonlin.BdryTraces α k f` records the vanishing of the integration-by-parts boundary
terms of `f`: the *radial* traces `z·(D_z^bD_θ^a f·w)² → 0` at `z → 0⁺` and at `z → ∞`, and the
*angular* traces `sin(2θ)^{1-γ}·(D_z^bD_θ^a f)² → 0` at `θ → 0⁺` and at `θ → (π/2)⁻`.

This module proves that the class is closed under multiplication by a radial factor
`(z,θ) ↦ ψ(z)` which is `C^∞` on `(-1,∞)` and whose `Zop`-iterates `Zop^c ψ = (z∂_z)^c ψ`
(up to order `k`) are bounded by a constant `K`.

ROUTE.  For `z > 0` and `0 < θ < π/2` the mixed derivative of the product expands by
`Work.FTS.CoercivityFix.E2Bound.mixed_zmul`:

  `D_z^bD_θ^a(ψ·g) = ∑_{c ≤ b} C(b,c)·(Zop^c ψ)·(D_z^{b-c}D_θ^a g)`,

so Cauchy–Schwarz in `ℝ` bounds the square of the mixed derivative by

  `(b+1)·∑_{c≤b} (C(b,c)·K)²·(D_z^{b-c}D_θ^a g)²`,

in which every slot carries the same traces as `g`: the pairs `(a, b-c)` satisfy
`a + (b-c) ≤ a + b ≤ k`, so `hbd` applies to each slot.  Each of the four traces of the product
is then a squeeze of the original expression between `0` and the corresponding finite
combination of the traces of `g`, which the four filters `𝓝[>] 0`, `atTop`, `𝓝[>] 0` and
`𝓝[<] (π/2)` push to `0`.

(The restriction `z > 0`, `0 < θ < π/2` of the expansion is harmless: each trace is a limit
along a filter in which these sets are eventually true.)

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.CoercivityFix.E2Bound.mixed_zmul
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.PsiMul

set_option maxHeartbeats 1000000

/-! ## The pointwise bound -/

/-- **Pointwise bound for the mixed derivative of a radial multiple.**  For `z > 0` and
`0 < θ < π/2`, the square of any mixed derivative `D_z^bD_θ^a(ψ·g)`, weighted by an arbitrary
nonnegative factor `ρ`, is bounded by `(b+1)` times the corresponding combination of the mixed
derivatives of `g` (weighted by `ρ`), with coefficients `(C(b,c)·K)²`. -/
private theorem mixed_psi_mul_sq_le {k : ℕ} {ψ : ℝ → ℝ} {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K)
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g)
    (hpsi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => ψ z))
    {a b : ℕ} (hab : a + b ≤ k) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
      ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
        ((b.choose c : ℝ) * K) ^ 2 * (ρ * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    rw [Set.mem_Ioi] at hz ⊢
    linarith
  have hcore : (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
      ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
        ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by
    rw [Work.FTS.CoercivityFix.E2Bound.mixed_zmul b a ψ g hz1 hθ hpsi hg]
    calc (∑ c ∈ Finset.range (b + 1),
            (b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z * Work.Spaces.mixed (b - c) a g z θ)) ^ 2
        ≤ ((Finset.range (b + 1)).card : ℝ) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
              * Work.Spaces.mixed (b - c) a g z θ)) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
              * Work.Spaces.mixed (b - c) a g z θ)) ^ 2 := by
          simp
      _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum fun c hc => ?_
          have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
          have hsq : (Work.Spaces.Zop^[c] ψ z) ^ 2 ≤ K ^ 2 := by
            have h := pow_le_pow_left₀ (abs_nonneg (Work.Spaces.Zop^[c] ψ z))
              (hKb c (by omega) z hz) 2
            rwa [sq_abs] at h
          have e1 : ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
                * Work.Spaces.mixed (b - c) a g z θ)) ^ 2
              = ((b.choose c : ℝ) ^ 2 * (Work.Spaces.Zop^[c] ψ z) ^ 2)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by ring
          have e2 : ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2
              = ((b.choose c : ℝ) ^ 2 * K ^ 2)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (sq_nonneg _)
  calc ρ * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2
      ≤ ρ * (((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcore hρ
    _ = ((b : ℝ) + 1) * (ρ * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by ring
    _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (ρ * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun c _ => by ring

/-! ## The four traces -/

theorem BdryTraces_psi_mul (α : ℝ) (k : ℕ) {ψ : ℝ → ℝ} {K : ℝ}
    (hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioi (-1)))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g)
    (hbd : Work.FTS.Nonlin.BdryTraces α k g) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => ψ z * g z θ) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hKb 0 (Nat.zero_le k) 1 (by norm_num))
  have hpsi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => ψ z) :=
    Work.FTS.CoercivityFix.E2Bound.smoothQuad_of_zOnly hsm
  -- the two angular intervals are eventually true along the two one-sided filters
  have hIoo0 : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (-1) (π / 2), isOpen_Ioo,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      fun x hx => ⟨hx.2, hx.1.2⟩⟩
  have hIooπ : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (π / 4) (π / 2 + 1), isOpen_Ioo,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      fun x hx => ⟨by linarith [hx.1.1, Real.pi_pos], hx.2⟩⟩
  intro a b hab
  refine ⟨?_, ?_⟩
  · intro θ hθ
    refine ⟨?_, ?_⟩
    · -- radial trace at `z → 0⁺`
      refine squeeze_zero'
        (g := fun z => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2)) ?_ ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        have hbnd : (z * (Work.Spaces.w z) ^ 2) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  ((z * (Work.Spaces.w z) ^ 2) * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) :=
          mixed_psi_mul_sq_le hK
            (mul_nonneg (le_of_lt hz) (sq_nonneg (Work.Spaces.w z))) hKb hg hpsi hab hz hθ
        calc z * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ * Work.Spaces.w z) ^ 2
            = (z * (Work.Spaces.w z) ^ 2) *
                (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 := by ring
          _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 * ((z * (Work.Spaces.w z) ^ 2) *
                  (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := hbnd
          _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2) := by
              congr 1
              exact Finset.sum_congr rfl fun c _ => by ring
      · have hsum : Tendsto (fun z => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hbd a (b - c) (by omega)).1 θ hθ).1).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
    · -- radial trace at `z → ∞`
      refine squeeze_zero'
        (g := fun z => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2)) ?_ ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have hbnd : (z * (Work.Spaces.w z) ^ 2) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  ((z * (Work.Spaces.w z) ^ 2) * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) :=
          mixed_psi_mul_sq_le hK
            (mul_nonneg (le_of_lt hz) (sq_nonneg (Work.Spaces.w z))) hKb hg hpsi hab hz hθ
        calc z * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ * Work.Spaces.w z) ^ 2
            = (z * (Work.Spaces.w z) ^ 2) *
                (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 := by ring
          _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 * ((z * (Work.Spaces.w z) ^ 2) *
                  (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := hbnd
          _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2) := by
              congr 1
              exact Finset.sum_congr rfl fun c _ => by ring
      · have hsum : Tendsto (fun z => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2))
            atTop (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hbd a (b - c) (by omega)).1 θ hθ).2).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
  · intro z hz
    refine ⟨?_, ?_⟩
    · -- angular trace at `θ → 0⁺`
      refine squeeze_zero'
        (g := fun θ => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b - c) a g z θ) ^ 2)) ?_ ?_ ?_
      · filter_upwards [hIoo0] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        exact mul_nonneg hsin (sq_nonneg _)
      · filter_upwards [hIoo0] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        have hbnd : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                    * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) :=
          mixed_psi_mul_sq_le hK hsin hKb hg hpsi hab hz hθ
        exact hbnd
      · have hsum : Tendsto (fun θ => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hbd a (b - c) (by omega)).2 z hz).1).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
    · -- angular trace at `θ → (π/2)⁻`
      refine squeeze_zero'
        (g := fun θ => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b - c) a g z θ) ^ 2)) ?_ ?_ ?_
      · filter_upwards [hIooπ] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        exact mul_nonneg hsin (sq_nonneg _)
      · filter_upwards [hIooπ] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        have hbnd : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                    * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) :=
          mixed_psi_mul_sq_le hK hsin hKb hg hpsi hab hz hθ
        exact hbnd
      · have hsum : Tendsto (fun θ => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2))
            (𝓝[<] (π / 2)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hbd a (b - c) (by omega)).2 z hz).2).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)

end Work.FTS.CoercivityFix.PsiMul
