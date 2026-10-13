/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongLWP/Basic.lean` — the API of the strong-route vocabulary

This module collects the elementary consequences of the definitions of
`Submission/Work/FTS/StrongLWP/Defs.lean` that the S1/S2/S4/S5 arguments use:

* **monotonicity in the order `k`** of `HkIntegrand`, `HkSq`, `HkNorm`: the order-`6` package of a
  strong solution contains its order-`4` package.
* the projections and the derived clauses of `RegPkgMin`, `RegPkgH6` and `LWPSol`;
* `SmoothOpen`-to-`C⁴` and `SmoothQuad`-to-`HQo`, the two conversions the downstream consumers
  (`RegPkgGal`, the IP-based estimates stated on `HQo`) ask for.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongLWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false

/-! ## Monotonicity of the `ℋ^k`-data in `k`

`HkIntegrand α k f` is the sum of the squares of the finitely many weighted derivatives of order
`≤ k` (with the mixed slot switched on for `1 ≤ i ≤ k`), so *increasing* `k` only adds nonnegative
terms: the kernel of this section is the pointwise inequality
`HkIntegrand α k' f z θ ≤ HkIntegrand α k f z θ` for `k' ≤ k`.  The corresponding inequalities for
`HkSq` and `HkNorm` are the reason why an `ℋ⁶`-bound on a solution automatically gives its
`ℋ⁴`-bound, which is what `RegPkgMin.mem4` needs. -/

/-- The two-term `if` comparison behind the monotonicity of the mixed slots. -/
theorem if_le_if_of_imp {a b : Prop} [Decidable a] [Decidable b] (h : a → b) (X : ℝ)
    (hX : 0 ≤ X) : (if a then X else 0) ≤ (if b then X else 0) := by
  by_cases ha : a
  · rw [if_pos ha, if_pos (h ha)]
  · rw [if_neg ha]
    split_ifs with hb
    · exact hX
    · exact le_refl 0

/-- The inner (`j`-)sum of a mixed slot is monotone in the order `k`: the index set grows with `k`
and each summand is switched on for a weaker condition. -/
theorem HkMixedInner_mono (X : ℕ → ℕ → ℝ) (hX : ∀ i j, 0 ≤ X i j) {k k' : ℕ} (hkk : k' ≤ k)
    (i : ℕ) :
    (∑ j ∈ Finset.range (k' + 1), (if 1 ≤ i ∧ i + j ≤ k' then X i j else 0))
      ≤ (∑ j ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then X i j else 0)) := by
  refine le_trans (Finset.sum_le_sum (fun j _ => (if_le_if_of_imp (a := 1 ≤ i ∧ i + j ≤ k')
    (b := 1 ≤ i ∧ i + j ≤ k) (fun h => ⟨h.1, le_trans h.2 hkk⟩) (X i j) (hX i j)))) ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.succ_le_succ hkk)) (fun x _ _ => ?_)
  split_ifs with h
  · exact hX i x
  · exact le_refl 0

/-- **Pointwise monotonicity of the `ℋ^k`-integrand in the order**: `k' ≤ k` ⟹
`HkIntegrand α k' f z θ ≤ HkIntegrand α k f z θ`. -/
theorem HkIntegrand_mono (α : ℝ) (f : Fn) {k k' : ℕ} (hkk : k' ≤ k) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k' f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hrange : Finset.range (k' + 1) ⊆ Finset.range (k + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ hkk)
  rw [Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · exact Finset.sum_le_sum_of_subset_of_nonneg hrange (fun x _ _ => sq_nonneg _)
  · refine le_trans (Finset.sum_le_sum (fun i _ => HkMixedInner_mono
      (fun i j => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (fun i j => sq_nonneg _) hkk i)) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg hrange (fun i _ _ => ?_)
    refine Finset.sum_nonneg (fun j _ => ?_)
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0

/-- **Monotonicity of the `ℋ^k`-square in the order.**  From the `ℋ^k`-membership of `f`
(which makes the outer integrand integrable) and `k' ≤ k`, the order-`k'` norm is bounded by the
order-`k` one. -/
theorem HkSq_mono_of_mem {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (hm : Work.Spaces.HkMem α k f) : Work.Spaces.HkSq α k' f ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hm.2 ?_
  · show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (0 : ℝ) ≤ ∫ (θ : ℝ) in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k' f z θ
    filter_upwards with z
    exact integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α k' f z θ)
  · show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ (θ : ℝ) in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k' f z θ)
        ≤ ∫ (θ : ℝ) in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards with z hz
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α k' f z θ))
      (hm.1 z hz) (Filter.Eventually.of_forall (fun θ => HkIntegrand_mono α f hkk z θ))

/-- **Monotonicity of the `ℋ^k`-norm in the order.** -/
theorem HkNorm_mono_of_mem {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (hm : Work.Spaces.HkMem α k f) : Work.Spaces.HkNorm α k' f ≤ Work.Spaces.HkNorm α k f :=
  Real.sqrt_le_sqrt (HkSq_mono_of_mem hkk hm)

/-! ## The `ℋ⁶`-package contains the `ℋ⁴`-one -/

/-- The `ℋ⁶`-bound of `RegPkgH6` gives the uniform `ℋ⁴`-bound used by `RegPkgGal`
(design §4), as soon as the `ℋ⁶`-membership needed by `HkNorm_mono_of_mem` is available. -/
theorem RegPkgH6.bd4 {α T : ℝ} {g : Fam} (h : RegPkgH6 α T g) :
    ∃ C, ∀ τ, 0 ≤ τ → τ ≤ T → Xn4 α (slice g τ) ≤ C := by
  obtain ⟨C, hC⟩ := h.bd6
  refine ⟨C, fun τ hτ hτT => ?_⟩
  have hm := h.mem6 τ hτ hτT
  exact le_trans (HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hm) (hC τ hτ hτT)

/-- The `ℋ⁴`-membership clause of `RegPkgH6`, through the `ℋ⁴`-field of its `RegPkgMin` (no
monotonicity of `ℋ^k`-membership in the order is needed for this clause: it is a field of the
package). -/
theorem RegPkgH6.mem4 {α T : ℝ} {g : Fam} (h : RegPkgH6 α T g) {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.Spaces.HkMem α 4 (slice g τ) := h.min.mem4 τ hτ

/-! ## `SmoothOpen` and `SmoothQuad` against the consumers

The strong route states its regularity in the *finite* order `4` (`RegPkgMin.c4`), while the frozen
frozen classes are stated with `smoothOrder` (`SmoothOpen`, `SmoothQuad`) or with `HQo`.  The two
directions used below are `SmoothOpen ⟹ C⁴` (the order-`4` clause of a smooth object) and
`SmoothQuad ⟹ SmoothOpen` (so that `RegQ` feeds the estimates that are stated on `HQo`). -/

/-- `SmoothOpen` means `C^∞` on the open quadrant, hence in particular `C⁴`. -/
theorem SmoothOpen.contDiffOn_four {f : Fn} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
  h.of_le (by simp [Work.Stability.smoothOrder])

/-- `SmoothOpen` gives, for each natural order, the honest `C^n`-statement on `Q0` (the form in
which the estimates of `EllipticEst` are stated). -/
theorem SmoothOpen.contDiffOn_nat {f : Fn} (h : Work.FTS.EllipticEst.SmoothOpen f) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0 := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at h
  exact h n

/-- The `C^∞`-class of `EllipticEst` on the open quadrant is contained in the frozen
`smoothOrder`-class of the strong route's `RegPkgMin.c1`/`RegPkgMin.c4`, so the `RegPkgMin`-fields
are *weaker* than the corresponding `SmoothOpen` statements. -/
theorem SmoothOpen.uncurry_contDiffOn_four_uncurried {f : Fn}
    (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Function.uncurry f p) Work.FTS.EllipticEst.Q0 :=
  SmoothOpen.contDiffOn_four h

end Work.FTS.StrongLWP
