/-
Copyright: work module for the Elgindi finite-time singularity project.

# Multiplication of the `ℋⁿ`-integrand by a function of `z` alone

`Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform` is the pointwise bound

`HkIntegrand α n (fun z θ => φ z * f z θ) z θ ≤ C · (1+K)² · HkIntegrand α n f z θ`

on the open quadrant `z > 0`, `0 < θ < π/2`, where `C` depends only on `n` (never on `α`,
`φ`, `K` or `f`) and where `φ` is a `C^∞` function of `z` alone whose `z`-derivative iterates
`Zop^[b] φ = (z ∂_z)^b φ` are bounded by `K` on `(0,∞)` for `b ≤ n`.  Note that the contraction
constant is *uniform in `z`*: no decay of `φ` at `0` or `∞` is used, only the `Zop`-bounds.

This is the multiplier estimate behind the `D_z`-commutator defect `Ê₂` of the coercivity
fix (`E2hat f = 2·φ·f + 3·φ·D_θf` with `φ(z) = z/(1+z)²`, see
`Submission/Work/FTS/CoercivityFix/E2Bound/E2hat_HkIntegrand_le_uniform.lean`).

## The shape of the argument

`HkIntegrand α n g z θ` is the sum of the squares of the weighted derivatives of `g`:
`∑_{i≤n} (D_z^i g · w/sin(2θ)^{η/2})² + ∑_{1≤i, i+j≤n} (D_z^j D_θ^i g · W)²`.
Both families of operators are derivations of the algebra of `C^∞` functions on the open
quadrant (`Work.FTS.LocData.SmoothQuad`), with Leibniz expansions

* `D_z^i (φ·f) = ∑_{b≤i} binom(i,b)·(Zop^b φ)·(D_z^{i-b} f)`
  (`Work.FTS.LocData.DzIter_mul_smoothQuad`, using `DzIter b (fun z θ => φ z) = Zop^b φ`),
* `D_z^j D_θ^i (φ·f) = ∑_{b≤j} binom(j,b)·(Zop^b φ)·(D_z^{j-b} D_θ^i f)` for `i ≥ 1`
  (`Work.FTS.CoercivityFix.E2Bound.mixed_zmul`).

Hence each summand of `HkIntegrand α n (φ·f)` is a binomial convolution
`∑_b binom · (Zop^b φ) · y_b` with `∑_b y_b² ≤ (k+1)·HkIntegrand α n f`; the numerical
Cauchy–Schwarz step is `Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le` and the extraction of
single summands is `Work.Spaces.sq_le_HkIntegrand_z` / `Work.Spaces.sq_le_HkIntegrand_mixed`.
The two sums are then bounded separately (in the private lemmas `zsum_helper` and
`mixed_helper`) and added.

All constants are explicit but deliberately generous: with `D = 2^n ≥ i.choose b` we use
`C = (n+1)^5 · D² + 1` for each half.  Everything rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.mixed_zmul
import Submission.Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- A function of `z` alone, `C^∞` on `(-1,∞)`, is `SmoothQuad` as a function of `(z,θ)`. -/
private lemma smoothQuad_zonly {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => a z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => a z))
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
  have h : Function.uncurry (fun z _ : ℝ => a z) = fun p : ℝ × ℝ => a p.1 := rfl
  rw [h]
  exact ha.comp contDiffOn_fst (fun p hp => hp.1)

/-- `|i.choose b| ≤ 2^n` in `ℝ` whenever `i ≤ n`. -/
private lemma choose_cast_abs_le (n i b : ℕ) (hbn : i ≤ n) :
    |((i.choose b : ℕ) : ℝ)| ≤ (2 : ℝ) ^ n := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : i.choose b ≤ 2 ^ n :=
    le_trans (Nat.choose_le_two_pow i b) (Nat.pow_le_pow_right (by norm_num) hbn)
  have h2 : ((i.choose b : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := Nat.cast_le.mpr h1
  have h3 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  linarith

/-- Arithmetic of the pure `D_z` sum: `(n+1)` terms each of size
`(((n+1)·2^n)·K)²·((n+1)·H)`. -/
private lemma arith_z (n : ℕ) (K H : ℝ) (hH : 0 ≤ H) :
    ((n : ℝ) + 1) * (((((n : ℝ) + 1) * (2 : ℝ) ^ n) * K) ^ 2 * (((n : ℝ) + 1) * H))
      ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by
  have hq : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hpow : ((n : ℝ) + 1) ^ 4 ≤ ((n : ℝ) + 1) ^ 5 := pow_le_pow_right₀ hq (by norm_num)
  have hle1 : ((n : ℝ) + 1) ^ 4 * ((2 : ℝ) ^ n) ^ 2
      ≤ ((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 :=
    mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  have hle2 : ((n : ℝ) + 1) ^ 4 * ((2 : ℝ) ^ n) ^ 2
      ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) := by linarith
  calc ((n : ℝ) + 1) * (((((n : ℝ) + 1) * (2 : ℝ) ^ n) * K) ^ 2 * (((n : ℝ) + 1) * H))
      = (((n : ℝ) + 1) ^ 4 * ((2 : ℝ) ^ n) ^ 2) * (K ^ 2 * H) := by ring
    _ ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * (K ^ 2 * H) :=
        mul_le_mul_of_nonneg_right hle2 (mul_nonneg (sq_nonneg K) hH)
    _ = (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by ring

/-- Arithmetic of the mixed sum: `(n+1)²` terms each of size
`(((n+1)·2^n)·K)²·((n+1)·H)`. -/
private lemma arith_mixed (n : ℕ) (K H : ℝ) (hH : 0 ≤ H) :
    ((n : ℝ) + 1) * (((n : ℝ) + 1)
        * (((((n : ℝ) + 1) * (2 : ℝ) ^ n) * K) ^ 2 * (((n : ℝ) + 1) * H)))
      ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by
  calc ((n : ℝ) + 1) * (((n : ℝ) + 1)
        * (((((n : ℝ) + 1) * (2 : ℝ) ^ n) * K) ^ 2 * (((n : ℝ) + 1) * H)))
      = (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2) * (K ^ 2 * H) := by ring
    _ ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * (K ^ 2 * H) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg K) hH)
    _ = (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by ring

/-! ## The pure `D_z` sum -/

private lemma zsum_helper (α : ℝ) (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (φ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K) →
      ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => φ z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ C * K ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
  refine ⟨((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1, ?_, ?_⟩
  · have hq0 : (0 : ℝ) < (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    have h1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 5 := pow_pos hq0 5
    have h2 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 2 := by positivity
    nlinarith [mul_pos h1 h2]
  · intro φ K hK hbnd hsm f hf z hz θ hθ
    have hzpos : (0 : ℝ) < z := Set.mem_Ioi.mp hz
    have hzI : z ∈ Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]; exact Set.mem_Ici.mpr (le_of_lt hzpos)
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, hθ.2⟩
    have hfslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' : ℝ => f z' θ)
        (Set.Ioi (-1)) := Work.FTS.LocData.contDiffOn_slice_z hf hθI
    have hHnn : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α n f z θ :=
      Work.Spaces.HkIntegrand_nonneg α n f z θ
    set ρ : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hρ
    set D : ℝ := (2 : ℝ) ^ n with hD
    set B : ℝ := ((n : ℝ) + 1) * D with hB
    set H : ℝ := Work.Spaces.HkIntegrand α n f z θ with hH
    have hDnn : (0 : ℝ) ≤ D := by rw [hD]; positivity
    have hBnn : (0 : ℝ) ≤ B := by rw [hB]; positivity
    have hBnn' : (0 : ℝ) ≤ (B * K) ^ 2 := sq_nonneg _
    have hterm : ∀ i, i ≤ n →
        (Work.Spaces.DzIter i (fun z θ => φ z * f z θ) z θ * ρ) ^ 2
          ≤ (B * K) ^ 2 * (((n : ℝ) + 1) * H) := by
      intro i hi
      have hleib := Work.FTS.LocData.DzIter_mul_smoothQuad i (fun z θ : ℝ => φ z) f hzI hsm hfslice
      have hshift : Work.Spaces.DzIter i (fun z θ => φ z * f z θ) z θ * ρ
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.DzIter (i - b) f z θ * ρ)) := by
        rw [hleib, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b hb => ?_)
        rw [congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z θ : ℝ => φ z) θ) z]
        ring
      have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := i) (D := D) (K := K) hK
        (x := fun b => Work.Spaces.Zop^[b] φ z)
        (y := fun m => Work.Spaces.DzIter m f z θ * ρ)
        (fun b hb => hbnd b (le_trans hb hi) z hz)
        (fun b hb => choose_cast_abs_le n i b hi)
      have hbin' : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.DzIter (i - b) f z θ * ρ))) ^ 2
          ≤ (((i : ℝ) + 1) * D * K) ^ 2
            * ∑ m ∈ Finset.range (i + 1), (Work.Spaces.DzIter m f z θ * ρ) ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hbin
      have hsum : ∑ m ∈ Finset.range (i + 1), (Work.Spaces.DzIter m f z θ * ρ) ^ 2
          ≤ ((i : ℝ) + 1) * H := by
        have h1 : ∑ m ∈ Finset.range (i + 1), (Work.Spaces.DzIter m f z θ * ρ) ^ 2
            ≤ ∑ _m ∈ Finset.range (i + 1), H :=
          Finset.sum_le_sum (fun m hm => Work.Spaces.sq_le_HkIntegrand_z α n f z θ m
            (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hi))
        have h2 : ∑ _m ∈ Finset.range (i + 1), H = ((i : ℝ) + 1) * H := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
        linarith
      have hi1 : ((i : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
        have : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hi
        linarith
      have hC1 : ((i : ℝ) + 1) * D * K ≤ B * K := by
        rw [hB]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi1 hDnn) hK
      have hsq1 : (((i : ℝ) + 1) * D * K) ^ 2 ≤ (B * K) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hC1 2
      have hsq2 : ((i : ℝ) + 1) * H ≤ ((n : ℝ) + 1) * H :=
        mul_le_mul_of_nonneg_right hi1 hHnn
      rw [hshift]
      calc (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.DzIter (i - b) f z θ * ρ))) ^ 2
          ≤ (((i : ℝ) + 1) * D * K) ^ 2
              * ∑ m ∈ Finset.range (i + 1), (Work.Spaces.DzIter m f z θ * ρ) ^ 2 := hbin'
        _ ≤ (((i : ℝ) + 1) * D * K) ^ 2 * (((i : ℝ) + 1) * H) :=
            mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
        _ ≤ (B * K) ^ 2 * (((n : ℝ) + 1) * H) :=
            mul_le_mul hsq1 hsq2 (mul_nonneg (by positivity) hHnn) hBnn'
    have hzsum : (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => φ z * f z θ) z θ * ρ) ^ 2)
        ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by
      have h1 : ∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.DzIter i (fun z θ => φ z * f z θ) z θ * ρ) ^ 2
          ≤ ∑ _i ∈ Finset.range (n + 1), ((B * K) ^ 2 * (((n : ℝ) + 1) * H)) :=
        Finset.sum_le_sum (fun i hm =>
          hterm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
      have h2 : ∑ _i ∈ Finset.range (n + 1), ((B * K) ^ 2 * (((n : ℝ) + 1) * H))
          = ((n : ℝ) + 1) * ((B * K) ^ 2 * (((n : ℝ) + 1) * H)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring
      have h3 : ((n : ℝ) + 1) * ((B * K) ^ 2 * (((n : ℝ) + 1) * H))
          ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by
        rw [hB, hD]
        exact arith_z n K H hHnn
      linarith
    exact hzsum

/-! ## The mixed sum -/

private lemma mixed_helper (α : ℝ) (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (φ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K) →
      ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ C * K ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
  refine ⟨((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1, ?_, ?_⟩
  · have hq0 : (0 : ℝ) < (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    have h1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 5 := pow_pos hq0 5
    have h2 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 2 := by positivity
    nlinarith [mul_pos h1 h2]
  · intro φ K hK hbnd hsm f hf z hz θ hθ
    have hzpos : (0 : ℝ) < z := Set.mem_Ioi.mp hz
    have hzI' : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, hθ.2⟩
    have hφquad : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => φ z) := smoothQuad_zonly hsm
    have hHnn : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α n f z θ :=
      Work.Spaces.HkIntegrand_nonneg α n f z θ
    set D : ℝ := (2 : ℝ) ^ n with hD
    set B : ℝ := ((n : ℝ) + 1) * D with hB
    set H : ℝ := Work.Spaces.HkIntegrand α n f z θ with hH
    have hDnn : (0 : ℝ) ≤ D := by rw [hD]; positivity
    have hBnn' : (0 : ℝ) ≤ (B * K) ^ 2 := sq_nonneg _
    have hconstnn : (0 : ℝ) ≤ (B * K) ^ 2 * (((n : ℝ) + 1) * H) :=
      mul_nonneg hBnn' (mul_nonneg (by positivity) hHnn)
    have hpair : ∀ i j : ℕ,
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ (B * K) ^ 2 * (((n : ℝ) + 1) * H) := by
      intro i j
      by_cases hcond : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hcond]
        obtain ⟨hi1, hij⟩ := hcond
        have hj : j ≤ n := by omega
        have hzm := Work.FTS.CoercivityFix.E2Bound.mixed_zmul j i φ f hzI' hθI hφquad hf
        have hshift : Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
              * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] φ z
                  * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ)) := by
          rw [hzm, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun b hb => by ring)
        have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := j) (D := D) (K := K) hK
          (x := fun b => Work.Spaces.Zop^[b] φ z)
          (y := fun m => Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ)
          (fun b hb => hbnd b (le_trans hb hj) z hz)
          (fun b hb => choose_cast_abs_le n j b hj)
        have hbin' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] φ z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
            ≤ (((j : ℝ) + 1) * D * K) ^ 2
              * ∑ m ∈ Finset.range (j + 1),
                  (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          simpa only [Nat.cast_add, Nat.cast_one] using hbin
        have hsum : ∑ m ∈ Finset.range (j + 1),
              (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ ((j : ℝ) + 1) * H := by
          have h1 : ∑ m ∈ Finset.range (j + 1),
                (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2
              ≤ ∑ _m ∈ Finset.range (j + 1), H :=
            Finset.sum_le_sum (fun m hm =>
              Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i m hi1
                (by have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm); omega))
          have h2 : ∑ _m ∈ Finset.range (j + 1), H = ((j : ℝ) + 1) * H := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast; ring
          linarith
        have hj1 : ((j : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
          have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hj
          linarith
        have hC1 : ((j : ℝ) + 1) * D * K ≤ B * K := by
          rw [hB]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj1 hDnn) hK
        have hsq1 : (((j : ℝ) + 1) * D * K) ^ 2 ≤ (B * K) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hC1 2
        have hsq2 : ((j : ℝ) + 1) * H ≤ ((n : ℝ) + 1) * H :=
          mul_le_mul_of_nonneg_right hj1 hHnn
        rw [hshift]
        calc (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] φ z
                  * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
            ≤ (((j : ℝ) + 1) * D * K) ^ 2
                * ∑ m ∈ Finset.range (j + 1),
                    (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2 := hbin'
          _ ≤ (((j : ℝ) + 1) * D * K) ^ 2 * (((j : ℝ) + 1) * H) :=
              mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
          _ ≤ (B * K) ^ 2 * (((n : ℝ) + 1) * H) :=
              mul_le_mul hsq1 hsq2 (mul_nonneg (by positivity) hHnn) hBnn'
      · rw [if_neg hcond]
        exact hconstnn
    have hmix : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by
      have hinner : ∀ i ∈ Finset.range (n + 1),
          (∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _j ∈ Finset.range (n + 1), ((B * K) ^ 2 * (((n : ℝ) + 1) * H)) :=
        fun i _ => Finset.sum_le_sum (fun j _ => hpair i j)
      have houter : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range (n + 1),
              ∑ _j ∈ Finset.range (n + 1), ((B * K) ^ 2 * (((n : ℝ) + 1) * H)) :=
        Finset.sum_le_sum hinner
      have hval : ∑ _i ∈ Finset.range (n + 1),
            ∑ _j ∈ Finset.range (n + 1), ((B * K) ^ 2 * (((n : ℝ) + 1) * H))
          = ((n : ℝ) + 1)
              * (((n : ℝ) + 1) * ((B * K) ^ 2 * (((n : ℝ) + 1) * H))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        push_cast; ring
      have h3 : ((n : ℝ) + 1) * (((n : ℝ) + 1) * ((B * K) ^ 2 * (((n : ℝ) + 1) * H)))
          ≤ (((n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ n) ^ 2 + 1) * K ^ 2 * H := by
        rw [hB, hD]
        exact arith_mixed n K H hHnn
      linarith
    exact hmix

/-! ## The requested lemma -/

theorem HkIntegrand_zmul_uniform (α : ℝ) (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (φ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K) →
      ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (fun z θ => φ z * f z θ) z θ
          ≤ C * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
  obtain ⟨C₁, hC₁, h₁⟩ := zsum_helper α n
  obtain ⟨C₂, hC₂, h₂⟩ := mixed_helper α n
  refine ⟨C₁ + C₂ + 1, by linarith, ?_⟩
  intro φ K hK hbnd hsm f hf z hz θ hθ
  have hZ := h₁ φ K hK hbnd hsm f hf z hz θ hθ
  have hM := h₂ φ K hK hbnd hsm f hf z hz θ hθ
  have hHnn : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α n f z θ :=
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  have hc : (0 : ℝ) ≤ C₁ + C₂ := by linarith
  have hK2 : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith
  have hstep1 : (C₁ + C₂) * K ^ 2 ≤ (C₁ + C₂) * (1 + K) ^ 2 :=
    mul_le_mul_of_nonneg_left hK2 hc
  have hstep2 : (C₁ + C₂) * (1 + K) ^ 2 ≤ (C₁ + C₂ + 1) * (1 + K) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (1 + K))
  have hstep : (C₁ + C₂) * K ^ 2 * Work.Spaces.HkIntegrand α n f z θ
      ≤ (C₁ + C₂ + 1) * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ :=
    mul_le_mul_of_nonneg_right (le_trans hstep1 hstep2) hHnn
  have he : C₁ * K ^ 2 * Work.Spaces.HkIntegrand α n f z θ
        + C₂ * K ^ 2 * Work.Spaces.HkIntegrand α n f z θ
      = (C₁ + C₂) * K ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by ring
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  linarith [hZ, hM, he, hstep]

end Work.FTS.CoercivityFix.E2Bound.SlotMul
