/-
Copyright: work module for the Elgindi finite-time singularity project.

# Multiplication of the `ℋᵏ`-integrand by a function of `z` alone, for `SmoothOpen` data

`Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le`: for every `k` there is a constant `C > 0`
(independent of `α`, `φ`, `K` and `g`) such that

`HkIntegrand α k (fun z θ => φ z * g z θ) z θ ≤ C · (1+K)² · HkIntegrand α k g z θ`

* on the **whole closed quadrant** `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`, for `φ : ℝ → ℝ` of class
  `C^∞` on `(-1,∞)` whose `Zop`-iterates `Zop^[b] φ = (z ∂_z)^b φ` are bounded by `K ≥ 0` on
  `(0,∞)` for `b ≤ k`, and for `g` of class `C^∞` on the **open** quadrant
  (`Work.FTS.EllipticEst.SmoothOpen g`) — no smoothness of `g` across `z = 0` is assumed;
* and, as a consequence, `ℋᵏ`-membership and the `ℋᵏ`-norm are preserved:
  `HkMem α k g → HkMem α k (φ·g) ∧ HkSq α k (φ·g) ≤ C · (1+K)² · HkSq α k g`.

## The argument (all pieces are in the two imported modules)

`HkIntegrand α k h z θ` is the sum of the squares of the weighted derivatives of `h`:

`∑_{i≤k} (D_z^i h · w/sin(2θ)^{η/2})² + ∑_{1≤i, i+j≤k} (D_z^j D_θ^i h · W)²`.

* On the interior of the quadrant the two operators satisfy the binomial (Leibniz) rules
  `D_z^i (φ·g) = ∑_{b≤i} binom(i,b)·(Zop^b φ)·(D_z^{i-b} g)` and
  `D_z^jD_θ^i (φ·g) = ∑_{b≤j} binom(j,b)·(Zop^b φ)·(D_z^{j-b}D_θ^i g)` for `i ≥ 1`; because
  `g` is only `C^∞` up to the axis `z = 0`, these are taken in the *finite-order*
  `ContDiffOn` form on the open half-line `(0,∞)`
  (`Work.FTS.FinalClock.DzIter_mul_of_contDiffOn` / `mixed_mul_of_contDiffOn`), applied to the
  `z`-slices of `g` and of its `D_θ`-iterates.  The numerical Cauchy–Schwarz step is
  `Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le`; the resulting `y`-sums are partial sums of
  the two blocks of `HkIntegrand α k g z θ` (`sq_le_HkIntegrand_z` /
  `sq_le_HkIntegrand_mixed`).  This is the algebra of `zmul_pt` (`ZmulCore`) instantiated in
  `zmul_open` (`ZmulBound`).
* The **boundary lines** `z = 0` and `sin(2θ) = 0` of the domain are trivial: there the
  weights `w 0 = 0`, `sin(2θ)^{-η/2} = 0`, `Wt = 0` kill the integrand
  (`HkIntegrand_zero_fst`, `HkIntegrand_eq_zero_of_sin_eq_zero`), while the right-hand side is
  nonnegative (`HkIntegrand_nonneg`); this is `zmul_quad`.
* `hkMem_of_open_dominated` transfers the two honesty requirements of `HkMem` from `g` to
  `φ·g` (continuity of the integrand on the open quadrant, domination on the closed one,
  Fubini for the measurability of the slice-integral).
* Finally the pointwise bound is integrated twice (`integral_mono_of_nonneg` against the
  integrable slices of `g`, then `integral_const_mul`) to compare the `ℋᵏ`-norms.

The constant produced is `zmulConst k = ((k+1)³ + (k+1)⁵)·4ᵏ + 1`.
Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option maxHeartbeats 1600000

theorem HkIntegrand_zmul_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (φ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K) →
      ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)) →
      ∀ g : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen g →
        (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
            ≤ C * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) ∧
        (Work.Spaces.HkMem α k g →
          Work.Spaces.HkMem α k (fun z θ => φ z * g z θ) ∧
          Work.Spaces.HkSq α k (fun z θ => φ z * g z θ)
            ≤ C * (1 + K) ^ 2 * Work.Spaces.HkSq α k g) := by
  refine ⟨zmulConst k, zmulConst_pos k, ?_⟩
  intro α φ K hK hB hsm g hg
  constructor
  · exact zmul_quad α k φ g hK hB hsm hg
  · intro hm
    set c : ℝ := zmulConst k * (1 + K) ^ 2 with hcdef
    have hcnn : 0 ≤ c := by
      rw [hcdef]
      exact mul_nonneg (zmulConst_pos k).le (sq_nonneg _)
    have hF : Work.FTS.EllipticEst.SmoothOpen (fun z θ => φ z * g z θ) :=
      smoothOpen_zmul hsm hg
    have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
          ≤ c * Work.Spaces.HkIntegrand α k g z θ := by
      intro z hz θ hθ
      rw [hcdef]
      exact zmul_quad α k φ g hK hB hsm hg z hz θ hθ
    refine ⟨hkMem_of_open_dominated α k hcnn hF hm hpt, ?_⟩
    -- integrate the pointwise bound, angular variable first
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ)
          ≤ c * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
      intro z hz
      have hle : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
            ≤ c * Work.Spaces.HkIntegrand α k g z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
        exact Filter.Eventually.of_forall fun θ hθ => hpt z hz θ hθ
      have := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α k (fun z θ => φ z * g z θ) z θ)
        ((hm.1 z hz).const_mul c) hle
      rwa [MeasureTheory.integral_const_mul] at this
    have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ)
        ≤ ∫ z in Work.Spaces.Iz,
            c * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ((hm.2).const_mul c) ?_
      · exact Filter.Eventually.of_forall fun z =>
          MeasureTheory.integral_nonneg fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k (fun z θ => φ z * g z θ) z θ
      · exact (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mpr
          (Filter.Eventually.of_forall fun z hz => hinner z hz)
    calc Work.Spaces.HkSq α k (fun z θ => φ z * g z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ := rfl
      _ ≤ ∫ z in Work.Spaces.Iz,
            c * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := houter
      _ = c * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k g z θ := MeasureTheory.integral_const_mul c _
      _ = zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkSq α k g := by
          simp only [hcdef, Work.Spaces.HkSq]

end Work.FTS.StrongPersist.L3Aux
