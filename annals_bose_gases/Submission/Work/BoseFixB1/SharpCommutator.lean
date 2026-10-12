import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
import Submission.Work.SmallBoxD1Integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SharpCommutator` — the SHARP `τ`-commutator bound (FS's `n₀`-weighting)

FS's `lm:appbogolubov` uses the commutator bound `[b_p,b_p†] ≤ n₀|B|⁻¹∫χ_B²` with `n₀` the
**state's flat (condensate) count**.  The corpus's `tau_commutator_le` proves only the lossy
version with `(n+1)·‖Ψ‖²` (the *particle number* times the state norm); the loss
`(n+1)‖Ψ‖² / n₀` is exactly the factor that forces every downstream D1 statement to carry the
particle number instead of the flat count — which is why the honest targets
(`Work.BoseFixB1.lm_appbogolubov_localisedB`, FS `eq:simpleaprioribog` with `n₀`) are not
reachable from the proved D1 chain.

This module proves the sharp bound.  The corpus's proof of `tau_commutator_le` already derives
the EXACT two-mode identity

    ∫(boxOp g 1 Ψ)² − ∫(boxOp 1 g Ψ)²
      = (∫g²)·∫(Ψ·boxOp 1 1 Ψ) − s³·∫(Ψ·boxOp g g Ψ)      (`boxOp_commutator`)

and then (i) bounds `∫(Ψ·boxOp 1 1 Ψ) ≤ s³(n+1)∫Ψ²` (`boxOp_one_one_integral_le`, via
`aP_sq_le`) and (ii) drops the non-negative `∫(Ψ·boxOp g g Ψ)`.  Step (i) is an *equality*:

    ∫(Ψ·boxOp 1 1 Ψ) = s³ · cS1 s Ψ          (`boxOp_one_one_integral_eq`)

(`boxOp 1 1 Ψ = s³ Σ_i P_iΨ` pointwise, and `∫Ψ·P_iΨ = ∫(P_iΨ)²`, `aP_sym_box`/`aP_idem`).
Hence the sharp commutator bound, with the flat count `cS1 s Ψ = Σ_i∫(P_iΨ)²` in place of the
particle number:

    ∫(τ†Ψ)² − ∫(τΨ)² ≤ (∫_{acube s}g²)·cS1 s Ψ          (`tau_commutator_le_sharp`).

The rest of the D1 chain consumes the commutator input *linearly*, so re-running it with `cS1`
in place of `(n+1)‖Ψ‖²` turns D1's mass `(1/2)g0w0Mass·d4MassCoeff (N+1) s` into the sharp
`(1/2)g0w0Mass·((N:ℝ)+2)·cS1 s Φ/s³` — the `n₀`-weighted form of FS's lemma.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The exact `⟨N₀⟩`-identity**: the quadratic form of the constant-mode number operator
`boxOp s 1 1` is `s³` times the flat count `cS1 s Ψ = Σ_i∫(P_iΨ)²`:

    ∫_{abox N s} Ψ·(boxOp s 1 1 Ψ) = s³ · cS1 s Ψ .

(The corpus's `boxOp_one_one_integral_le` proves only `≤ s³(n+1)∫Ψ²`, via `aP_sq_le`.) -/
theorem boxOp_one_one_integral_eq {s : ℝ} (hs : 0 < s) {n : ℕ} {Ψ : X (n + 1) → ℝ}
    (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
      = s ^ 3 * cS1 s Ψ := by
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  have hne : s ≠ 0 := ne_of_gt hs
  have haP : ∀ i : Fin (n + 1), (∫ x in abox (n + 1) s, Ψ x * aP s i Ψ x)
      = ∫ x in abox (n + 1) s, (aP s i Ψ x) ^ 2 := by
    intro i
    have hsym := aP_sym_box hs i (Φ := aP s i Ψ) (Ψ := Ψ) (aP_continuous hs i hΨ) hΨ
    simp only [pow_two]
    rw [← hsym]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [aP_idem hs i hΨ x]
    ring
  have h1 : (∫ x in abox (n + 1) s, Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
      = s ^ 3 * ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, Ψ x * aP s i Ψ x := by
    rw [show (fun x => Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x) = fun x =>
        ∑ i : Fin (n + 1), s ^ 3 * (Ψ x * aP s i Ψ x) by
      funext x
      rw [boxOp_one_one hne Ψ x, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    have hInt : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        Integrable (fun x : X (n + 1) => s ^ 3 * (Ψ x * aP s i Ψ x)) (boxMeas (n + 1) s) := by
      intro i _
      have hbase : Integrable (fun x : X (n + 1) => Ψ x * aP s i Ψ x) (boxMeas (n + 1) s) :=
        ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
          ((hΨ.mul (aP_continuous hs i hΨ)).continuousOn)
      exact (hbase.const_mul (s ^ 3))
    rw [integral_finsetSum _ hInt, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul]
  rw [h1, cS1]
  simp_rw [haP]

/-- **The SHARP `τ`-commutator bound** — FS's `[b_p,b_p†] ≤ n₀|B|⁻¹∫χ_B²` with `n₀` the
state's *flat count* `cS1 s Ψ` (and the box mass `∫g²` in place of `|B|⁻¹∫χ_B²`):

    ∫_{abox N s}(τ†Ψ)² − ∫_{abox N s}(τΨ)² ≤ (∫_{acube s}g²) · cS1 s Ψ .

Compare `tau_commutator_le`, whose right-hand side is `(∫g²)·(n+1)·∫Ψ²`. -/
theorem tau_commutator_le_sharp {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
        - (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
      ≤ (∫ z in acube s, g z * g z) * cS1 s Ψ := by
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  have hs3pos : (0 : ℝ) < s ^ 3 := by positivity
  have htauD : (∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
      = (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2 := by
    rw [show (fun x => (tauDag s g Ψ x) ^ 2) = fun x =>
        (s ^ 3)⁻¹ * (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2 by
      funext x
      rw [tauDag_eq hs g Ψ x, mul_pow, inv_pow, Real.sq_sqrt (le_of_lt hs3pos)]]
    rw [integral_const_mul]
  have htauA : (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
      = (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2 := by
    rw [show (fun x => (tauAnn s g Ψ x) ^ 2) = fun x =>
        (s ^ 3)⁻¹ * (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2 by
      funext x
      rw [tauAnn_eq hs g Ψ x, mul_pow, inv_pow, Real.sq_sqrt (le_of_lt hs3pos)]]
    rw [integral_const_mul]
  have hU : (∫ x in abox (n + 1) s, (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2)
      = ∫ x in abox (n + 1) s,
          Ψ x * boxOp s (fun _ => (1 : ℝ)) g (boxOp s g (fun _ => (1 : ℝ)) Ψ) x := by
    rw [boxOp_adjoint hs continuous_const hg hΨ (continuous_boxOp hs hg continuous_const hΨ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hV : (∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2)
      = ∫ x in abox (n + 1) s,
          Ψ x * boxOp s g (fun _ => (1 : ℝ)) (boxOp s (fun _ => (1 : ℝ)) g Ψ) x := by
    rw [boxOp_adjoint hs hg continuous_const hΨ (continuous_boxOp hs continuous_const hg hΨ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hI1 : Integrable (fun x : X (n + 1) => Ψ x *
      boxOp s (fun _ => (1 : ℝ)) g (boxOp s g (fun _ => (1 : ℝ)) Ψ) x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs continuous_const hg
        (continuous_boxOp hs hg continuous_const hΨ))).continuousOn)
  have hI2 : Integrable (fun x : X (n + 1) => Ψ x *
      boxOp s g (fun _ => (1 : ℝ)) (boxOp s (fun _ => (1 : ℝ)) g Ψ) x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs hg continuous_const
        (continuous_boxOp hs continuous_const hg hΨ))).continuousOn)
  have hIc : Integrable (fun x : X (n + 1) => Ψ x *
      boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs continuous_const continuous_const hΨ)).continuousOn)
  have hIg : Integrable (fun x : X (n + 1) => Ψ x * boxOp s g g Ψ x) (boxMeas (n + 1) s) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      ((hΨ.mul (continuous_boxOp hs hg hg hΨ)).continuousOn)
  have key : (∫ x in abox (n + 1) s, (boxOp s g (fun _ => (1 : ℝ)) Ψ x) ^ 2)
        - (∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2)
      = (∫ z in acube s, g z * g z)
          * (∫ x in abox (n + 1) s, Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        - s ^ 3 * (∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x) := by
    rw [hU, hV, ← integral_sub hI1 hI2]
    rw [show (∫ x in abox (n + 1) s, (Ψ x *
            boxOp s (fun _ => (1 : ℝ)) g (boxOp s g (fun _ => (1 : ℝ)) Ψ) x
          - Ψ x * boxOp s g (fun _ => (1 : ℝ)) (boxOp s (fun _ => (1 : ℝ)) g Ψ) x))
        = ∫ x in abox (n + 1) s, ((∫ z in acube s, g z * g z)
              * (Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
            - s ^ 3 * (Ψ x * boxOp s g g Ψ x)) from
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem (abox_measurable (n + 1) s)] with x hx
        rw [← mul_sub, boxOp_commutator hs hg hΨ hx]
        ring)]
    rw [integral_sub (hIc.const_mul _) (hIg.const_mul _), integral_const_mul, integral_const_mul]
  rw [htauD, htauA, ← mul_sub, key]
  have hcgnn : 0 ≤ ∫ z in acube s, g z * g z := integral_nonneg fun z => mul_self_nonneg _
  have hBnn : 0 ≤ ∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x := boxOp_gg_nonneg hs hg hΨ
  have hA := boxOp_one_one_integral_eq (n := n) hs hΨ
  calc (s ^ 3)⁻¹ * ((∫ z in acube s, g z * g z)
          * (∫ x in abox (n + 1) s,
              Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        - s ^ 3 * (∫ x in abox (n + 1) s, Ψ x * boxOp s g g Ψ x))
      ≤ (s ^ 3)⁻¹ * ((∫ z in acube s, g z * g z)
          * (∫ x in abox (n + 1) s,
              Ψ x * boxOp s (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sub_le_self _ (mul_nonneg (by positivity) hBnn)
    _ = (∫ z in acube s, g z * g z) * cS1 s Ψ := by
        rw [hA]
        field_simp

/-- Sanity check: the sharp bound implies the corpus's `tau_commutator_le` form
(`cS1 s Ψ ≤ (n+1)∫Ψ²`, `aP_sq_le`). -/
theorem tau_commutator_le_sharp_le {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ}
    (hg : Continuous g) {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) :
    (∫ x in abox (n + 1) s, (tauDag s g Ψ x) ^ 2)
        - (∫ x in abox (n + 1) s, (tauAnn s g Ψ x) ^ 2)
      ≤ (∫ z in acube s, g z * g z) * (((n : ℝ) + 1) * ∫ x in abox (n + 1) s, (Ψ x) ^ 2) := by
  haveI : IsFiniteMeasure (boxMeas (n + 1) s) := isFiniteMeasure_boxMeas hs
  have h1 := tau_commutator_le_sharp (n := n) hs hg hΨ
  have h2 : cS1 s Ψ ≤ ((n : ℝ) + 1) * ∫ x in abox (n + 1) s, (Ψ x) ^ 2 := by
    have hsum : cS1 s Ψ ≤ ∑ _i : Fin (n + 1), ∫ x in abox (n + 1) s, (Ψ x) ^ 2 := by
      rw [cS1]
      exact Finset.sum_le_sum (fun i _ => aP_sq_le hs i hΨ)
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsum
  have hcgnn : 0 ≤ ∫ z in acube s, g z * g z := integral_nonneg fun z => mul_self_nonneg _
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hcgnn)

end Work.BoseFixB1
