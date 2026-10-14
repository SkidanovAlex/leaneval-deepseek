import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_ang_v_outer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Iterated derivatives of a `C^N` function on an open set are continuous. -/
private lemma continuousOn_iteratedDeriv_of_contDiffOn {N m : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ N f s) (hm : m ≤ N) :
    ContinuousOn (iteratedDeriv m f) s := by
  have h : ContinuousOn (iteratedDerivWithin m f s) s :=
    ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (𝕜 := ℝ) (n := N) (f := f)
      hs.uniqueDiffOn).mp hf).1 m hm
  exact h.congr fun x hx => ((iteratedDerivWithin_of_isOpen (n := m) hs) hx).symm

/-- `sin(2θ)^e` is nonnegative on `Iθ`. -/
private lemma sinTwo_rpow_nonneg {e θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) e :=
  Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) e

/-- **`AngRHS` is nonnegative**: it is a sum of integrals of a.e. nonnegative integrands, all of
which are in fact nonnegative on `Iθ` (where `sin (2θ) ≥ 0`). -/
private theorem angRHS_nonneg_prv (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    0 ≤ AngRHS k γ u g := by
  have key : ∀ {f : ℝ → ℝ}, (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ) →
      0 ≤ ∫ θ in Work.Spaces.Iθ, f θ := by
    intro f hf
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := (volume : Measure ℝ))
      measurableSet_Icc] with θ hθ
    exact hf θ hθ
  unfold AngRHS
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · exact key fun θ hθ => mul_nonneg (sq_nonneg _) (sinTwo_rpow_nonneg hθ)
  · exact Finset.sum_nonneg fun j _ =>
      key fun θ hθ => mul_nonneg (sq_nonneg _) (sinTwo_rpow_nonneg hθ)
  · exact key fun θ hθ => mul_nonneg (sq_nonneg _) (sinTwo_rpow_nonneg hθ)
  · exact key fun θ _ => sq_nonneg _
  · exact key fun θ _ => sq_nonneg _

/-- **Weighted `v = u / cos θ` bound on the outer window `[0, 3π/8]`.**

For `k ≥ 2`, `γ ∈ [1,5/4]`, `u ∈ C^{k+2}(0,π/2)` continuous on `[0,π/2]` with `u 0 = u (π/2) = 0`
and `g = Lzero1 u`, with the six integrability hypotheses of the target `slice_ang_gen`, one has,
for every `m ≤ k+1`,

`∫_{[0,3π/8]} (∂^m (u/cos))² · sin(2θ)^(2k-γ) ≤ C · AngRHS k γ u g`,

where `AngRHS` is the right-hand side of `slice_ang_gen`
(`Submission/Work/FTS/EllipticEst/remov/slice_ang_reduce.lean`), together with the
integrability of the left-hand integrand.

Route: on `[0,3π/8]` the cosine is bounded below by `cos(3π/8) > 0`, so every iterated derivative
of `1/cos` is bounded there and `(∂^m(u/cos))² ≤ C_k Σ_{j≤m} (u^{(j)})²`; each slot is then
dominated by an integral of `AngRHS` exactly as in the proved `remov/slice_ang_outer`
(`sin(2θ)^(2k-γ) ≤ sin(2θ)^(2j-4-γ)` for `j ≤ k+2`, `≤ sin(2θ)^(-η)` for `j = 2`, `≤ 1` for
`j ≤ 1`). -/
theorem slice_ang_v_outer (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          (Set.Icc 0 (3 * Real.pi / 8)) ∧
        (∫ θ in Set.Icc 0 (3 * Real.pi / 8),
            (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨A, hApos, hAbnd⟩ := invCos_jets_le (k + 2)
  refine ⟨A * ((k : ℝ) + 2), by positivity, ?_⟩
  intro γ u g hγ1 hγ2 hu hcont hu0 hupi hg hInt_k2 hInt_gk hInt_high hInt_2 hInt_1 hInt_0 m hm
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have he_pos : 0 < 2 * (k : ℝ) - γ := by linarith
  have hmk : m ≤ k + 2 := by omega
  -- the dominating density and the left-hand integrand
  set D : ℝ → ℝ := fun θ => ∑ j ∈ Finset.range (m + 1),
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) with hD
  set F : ℝ → ℝ := fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) with hF
  have hsub : Set.Ioo (0 : ℝ) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  -- the slot bounds
  have hslot := angSlot_le_AngRHS k hk γ u g hγ1 hγ2 hu hcont hInt_gk hInt_high hInt_2 hInt_1 hInt_0
  have hslot_int : ∀ j : ℕ, j ≤ k + 1 → IntegrableOn (fun θ => (iteratedDeriv j u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ :=
    fun j hj => (hslot j hj).1
  -- `D` is nonnegative on `Iθ` and integrable there
  have hD_nonneg : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ D θ := by
    intro θ hθ
    rw [hD]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sinTwo_rpow_nonneg hθ)
  have hD_int : IntegrableOn D Work.Spaces.Iθ := by
    rw [hD]
    exact MeasureTheory.integrable_finsetSum _ fun j hj =>
      hslot_int j (by have := Finset.mem_range.mp hj; omega)
  -- the integral of `D` is bounded by `(k+2) * AngRHS`
  have hD_bound : (∫ θ in Work.Spaces.Iθ, D θ) ≤ ((k : ℝ) + 2) * AngRHS k γ u g := by
    have hsum : (∫ θ in Work.Spaces.Iθ, D θ)
        = ∑ j ∈ Finset.range (m + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := by
      rw [hD]
      exact MeasureTheory.integral_finsetSum _ fun j hj =>
        hslot_int j (by have := Finset.mem_range.mp hj; omega)
    rw [hsum]
    calc ∑ j ∈ Finset.range (m + 1), (∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∑ _j ∈ Finset.range (m + 1), AngRHS k γ u g :=
          Finset.sum_le_sum fun j hj =>
            (hslot j (by have := Finset.mem_range.mp hj; omega)).2
      _ = ((m : ℝ) + 1) * AngRHS k γ u g := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((k : ℝ) + 2) * AngRHS k γ u g := by
          refine mul_le_mul_of_nonneg_right ?_ (angRHS_nonneg_prv k γ u g)
          have hle : (m : ℝ) + 1 ≤ (k : ℝ) + 2 := by
            have : m + 1 ≤ k + 2 := by omega
            exact_mod_cast this
          linarith
  -- pointwise domination on the open window
  have hdom : ∀ θ ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8), F θ ≤ A * D θ := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := hsub hθ
    have hσnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := sinTwo_rpow_nonneg hθI
    have hb := hAbnd u hu θ hθ m hmk
    calc F θ = (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := by rw [hF]
      _ ≤ (A * ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2)
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
          mul_le_mul_of_nonneg_right hb hσnn
      _ = A * D θ := by
          change (A * ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2)
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            = A * ∑ j ∈ Finset.range (m + 1),
                (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  -- `F = u/cos`-block is continuous, hence a.e. strongly measurable, on the open window
  have hv : ContDiffOn ℝ (k + 2) (fun t => u t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn fun t ht =>
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hv_cont : ContinuousOn (iteratedDeriv m (fun t => u t / Real.cos t))
      (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
    (continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioo hv hmk).mono fun x hx =>
      ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hσ_cont : ContinuousOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
    ContinuousOn.rpow_const
      (Real.continuous_sin.comp_continuousOn
        ((continuous_const.mul continuous_id).continuousOn))
      (fun θ _ => Or.inr (le_of_lt he_pos))
  have hF_cont : ContinuousOn F (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := by
    rw [hF]
    exact (hv_cont.pow 2).mul hσ_cont
  have hF_aesm : AEStronglyMeasurable F
      (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hF_cont.aestronglyMeasurable measurableSet_Ioo
  have hAD_int : IntegrableOn (fun θ => A * D θ) (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
    Integrable.const_mul (hD_int.mono_set hsub) A
  have hF_int : IntegrableOn F (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := by
    refine Integrable.mono' hAD_int hF_aesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := (volume : Measure ℝ))
      measurableSet_Ioo] with θ hθ
    have hσnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := sinTwo_rpow_nonneg (hsub hθ)
    have hnn : 0 ≤ F θ := by
      rw [hF]
      exact mul_nonneg (sq_nonneg _) hσnn
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hdom θ hθ
  -- the three integral comparisons
  have hint1 : (∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), F θ)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), A * D θ :=
    MeasureTheory.setIntegral_mono_on hF_int hAD_int measurableSet_Ioo hdom
  have hint2 : (∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), A * D θ)
      ≤ ∫ θ in Work.Spaces.Iθ, A * D θ := by
    refine MeasureTheory.setIntegral_mono_set (hD_int.const_mul A) ?_ ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := (volume : Measure ℝ))
        measurableSet_Icc] with θ hθ
      exact mul_nonneg (le_of_lt hApos) (hD_nonneg θ hθ)
    · exact Filter.Eventually.of_forall fun x hx => hsub hx
  have hint3 : (∫ θ in Work.Spaces.Iθ, A * D θ) = A * ∫ θ in Work.Spaces.Iθ, D θ :=
    MeasureTheory.integral_const_mul A D
  have hF_bound : (∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), F θ)
      ≤ (A * ((k : ℝ) + 2)) * AngRHS k γ u g := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), F θ)
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), A * D θ := hint1
      _ ≤ ∫ θ in Work.Spaces.Iθ, A * D θ := hint2
      _ = A * ∫ θ in Work.Spaces.Iθ, D θ := hint3
      _ ≤ A * (((k : ℝ) + 2) * AngRHS k γ u g) :=
          mul_le_mul_of_nonneg_left hD_bound (le_of_lt hApos)
      _ = (A * ((k : ℝ) + 2)) * AngRHS k γ u g := by ring
  refine ⟨?_, ?_⟩
  · change Integrable F (volume.restrict (Set.Icc (0 : ℝ) (3 * Real.pi / 8)))
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc (a := (0 : ℝ)) (b := 3 * Real.pi / 8)]
    exact hF_int
  · change (∫ θ in Set.Icc (0 : ℝ) (3 * Real.pi / 8), F θ)
        ≤ A * ((k : ℝ) + 2) * AngRHS k γ u g
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc (a := (0 : ℝ)) (b := 3 * Real.pi / 8)]
    exact hF_bound

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.sin_hardy_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sin(2θ)`-weighted Hardy inequality (weak hypotheses) on `Iθ = [0,π/2]`

`Work.FTS.H2.Transport3Aux.sin_hardy_weak`: for `0 < β ≤ 1` and `f` continuous on `[0,π/2]`,
differentiable with continuous derivative on the open interval,

`∫_Iθ f² sin(2θ)^{β-1} ≤ (4/β²) ∫_Iθ (f')² sin(2θ)^{1-β} + (4/β) f(π/4)²`.

The two weights are reciprocal; the boundary term at the *interior* point `π/4` is essential
(the inequality is false without it, e.g. for constant `f` as `β → 0`).

Proof: split `Iθ` at `π/4`.  On each half, the sharp power-weighted Hardy inequality with its
boundary term (`Work.FTS.H2.Transport3Aux.hardy_power_weak`, applied with exponent `a = β-1`)
together with Jordan's inequality `(4/π)θ ≤ sin(2θ) ≤ 1` on `[0,π/4]` gives

`∫_0^{π/4} f² sin(2θ)^{β-1} ≤ (4/β²)(π/4)² ∫_0^{π/4}(f')² sin(2θ)^{1-β} + (π/2β) f(π/4)²`,

and the mirror image `θ ↦ π/2 - θ` (under which `sin 2θ` is invariant) gives the same on
`[π/4,π/2]`.  Adding the two halves and using `(π/4)² ≤ 1`, `π ≤ 4` yields the claim.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option maxHeartbeats 1000000

/-- The derivative of the mirror `u ↦ f (π/2 - u)` at an interior point, under the weak
hypotheses of `sin_hardy_weak` (no `C¹`-on-the-closed-interval hypothesis). -/
theorem deriv_mirror_weak {f : ℝ → ℝ}
    (hder : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt f (deriv f θ) θ) :
    ∀ u ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      deriv (fun u : ℝ => f (Real.pi/2 - u)) u = - deriv f (Real.pi/2 - u) := by
  intro u hu
  have hu' : Real.pi/2 - u ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
    ⟨by linarith [hu.2, Real.pi_pos], by linarith [hu.1]⟩
  have h1 : HasDerivAt (fun u : ℝ => Real.pi/2 - u) (-1) u := by
    have h := (hasDerivAt_id u).const_sub (Real.pi/2)
    simpa using h
  have h2 : HasDerivAt (fun u : ℝ => f (Real.pi/2 - u)) (deriv f (Real.pi/2 - u) * (-1)) u := by
    have h := (hder (Real.pi/2 - u) hu').comp u h1
    simpa only [Function.comp_def] using h
  rw [h2.deriv]
  ring

/-- The mirror identity for the `(f')²`-integral, under the weak hypotheses of `sin_hardy_weak`
(`sin 2θ` is invariant under `θ ↦ π/2 - θ`). -/
theorem mirror_deriv_sq_integral_weak {β : ℝ} {f : ℝ → ℝ}
    (hder : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt f (deriv f θ) θ) :
    (∫ u in (0:ℝ)..(Real.pi/4),
        (deriv (fun u : ℝ => f (Real.pi/2 - u)) u)^2 * (Real.sin (2*u))^(1-β))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ)^2 * (Real.sin (2*θ))^(1-β) := by
  rw [← integral_mirror_sub (fun θ : ℝ => (deriv f θ)^2 * (Real.sin (2*θ))^(1-β))]
  refine integral_congr_Ioo (by positivity : (0:ℝ) ≤ Real.pi/4) (fun u hu => ?_)
  rw [deriv_mirror_weak hder u ⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩]
  have hsin : Real.sin (2 * (Real.pi/2 - u)) = Real.sin (2*u) := by
    rw [show 2 * (Real.pi/2 - u) = Real.pi - 2*u by ring, Real.sin_pi_sub]
  rw [hsin]
  ring



end Work.FTS.H2.Transport3Aux
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP26.Bang_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.Nonlinear.Pieces.RNP26

set_option autoImplicit false

/-- **Polynomial bound.**  A polynomial of degree `≤ 5` all of whose coefficients are at most
`10^5` in absolute value is bounded by `6·10^5` on `[0,1]`. -/
private lemma abs_poly6_le (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (a0 a1 a2 a3 a4 a5 : ℝ)
    (h0 : |a0| ≤ 10 ^ 5) (h1 : |a1| ≤ 10 ^ 5) (h2 : |a2| ≤ 10 ^ 5)
    (h3 : |a3| ≤ 10 ^ 5) (h4 : |a4| ≤ 10 ^ 5) (h5 : |a5| ≤ 10 ^ 5) :
    |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5| ≤ 6 * 10 ^ 5 := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hxa : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hp : ∀ k : ℕ, |x ^ k| ≤ 1 := by
    intro k
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hxa
  have e1 : |a1 * x| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a1| * |x| ≤ 10 ^ 5 * 1 := mul_le_mul h1 hxa (abs_nonneg x) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e2 : |a2 * x ^ 2| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a2| * |x ^ 2| ≤ 10 ^ 5 * 1 := mul_le_mul h2 (hp 2) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e3 : |a3 * x ^ 3| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a3| * |x ^ 3| ≤ 10 ^ 5 * 1 := mul_le_mul h3 (hp 3) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e4 : |a4 * x ^ 4| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a4| * |x ^ 4| ≤ 10 ^ 5 * 1 := mul_le_mul h4 (hp 4) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e5 : |a5 * x ^ 5| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a5| * |x ^ 5| ≤ 10 ^ 5 * 1 := mul_le_mul h5 (hp 5) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have s1 := abs_add_le a0 (a1 * x)
  have s2 := abs_add_le (a0 + a1 * x) (a2 * x ^ 2)
  have s3 := abs_add_le (a0 + a1 * x + a2 * x ^ 2) (a3 * x ^ 3)
  have s4 := abs_add_le (a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3) (a4 * x ^ 4)
  have s5 := abs_add_le (a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4) (a5 * x ^ 5)
  have hsplit : |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5|
      ≤ |a0| + |a1 * x| + |a2 * x ^ 2| + |a3 * x ^ 3| + |a4 * x ^ 4| + |a5 * x ^ 5| := by
    linarith
  linarith

/-- The contribution of the `k = 0` part `4x(1-x)·V`: since `4x(1-x) ≥ 0` on `[0,1]`,
`|4x(1-x)V| = 4x(1-x)|V| ≤ 4x(1-x)·6·10^5 ≤ 10^6·4x(1-x)`. -/
private lemma abs_four_mul_le (x V : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hV : |V| ≤ 6 * 10 ^ 5) :
    |4 * x * (1 - x) * V| ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith [hx.1, hx.2]
  rw [abs_mul, abs_of_nonneg h4]
  calc 4 * x * (1 - x) * |V| ≤ 4 * x * (1 - x) * (6 * 10 ^ 5) :=
        mul_le_mul_of_nonneg_left hV h4
    _ ≤ 4 * x * (1 - x) * 10 ^ 6 := mul_le_mul_of_nonneg_left (by norm_num) h4
    _ = 10 ^ 6 * (4 * x * (1 - x)) := by ring

/-- The contribution of one `α`-term: for `0 < α ≤ 1` and `k ≥ 1` one has `(α/3)^k ≤ α/3`,
whence `|(α/3)^k·P| ≤ (α/3)·6·10^5 = 2·10^5·α` whenever `|P| ≤ 6·10^5`. -/
private lemma abs_rpow3_mul_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (hk : 1 ≤ k)
    (P : ℝ) (hP : |P| ≤ 6 * 10 ^ 5) : |(α / 3) ^ k * P| ≤ (α / 3) * (6 * 10 ^ 5) := by
  have ht0 : 0 ≤ α / 3 := by linarith
  have ht1 : α / 3 ≤ 1 := by linarith
  have hpow : (α / 3) ^ k ≤ α / 3 := by
    have := pow_le_pow_of_le_one ht0 ht1 hk
    simpa using this
  rw [abs_mul, abs_pow, abs_of_nonneg ht0]
  exact mul_le_mul hpow hP (abs_nonneg P) ht0

/-- `|a + b + c| ≤ |a| + |b| + |c|`. -/
private lemma abs_sum3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  linarith

/-- `|a + b + c + d| ≤ |a| + |b| + |c| + |d|`. -/
private lemma abs_sum4_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  linarith

/-- `|a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
private lemma abs_sum5_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  linarith

/-- **Bound on the angular polynomials `Bᵢ`.**  For `1 ≤ i ≤ 4`, `x ∈ [0,1]` and
`0 < α ≤ 1`,
  `|Bᵢ(x,α)| ≤ 10^6 (α + 4x(1-x))`.

Proof by the four cases `i = 1,2,3,4`: split `Bang i x α` into its `4x(1-x)·Vᵢ` part and its
(at most four) `(α/3)^k·P_{i,k}` parts, bound the `k = 0` part with `abs_four_mul_le` and each
`α`-part with `abs_rpow3_mul_le` (the polynomial bounds `|Vᵢ|, |P_{i,k}| ≤ 6·10^5` come from
`abs_poly6_le` and `norm_num` on the coefficients), and add up. -/
theorem Bang_bound (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) (x α : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Work.FTS.Nonlinear.Pieces.RNP26.Bang i x α| ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by
  interval_cases i
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_one]
    have hA : |4 * x * (1 - x) * 1| ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(1 : ℝ)| ≤ 6 * 10 ^ 5 := by norm_num
      exact abs_four_mul_le x 1 hx hV
    have hB : |(α / 3) * (-4 + 10 * x - 6 * x ^ 2)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-4 : ℝ) + 10 * x - 6 * x ^ 2| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-4) 10 (-6) 0 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1) ((-4 : ℝ) + 10 * x - 6 * x ^ 2) hP
      rw [pow_one] at hk
      linarith
    calc |4 * x * (1 - x) * 1 + (α / 3) * (-4 + 10 * x - 6 * x ^ 2)|
        ≤ |4 * x * (1 - x) * 1| + |(α / 3) * (-4 + 10 * x - 6 * x ^ 2)| := abs_add_le _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α := add_le_add hA hB
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_two]
    have hA : |4 * x * (1 - x) * (-4 + 8 * x)| ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(-4 : ℝ) + 8 * x| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-4) 8 0 0 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        simpa using h
      exact abs_four_mul_le x (-4 + 8 * x) hx hV
    have hB1 : |(α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-56 : ℝ) * x + 128 * x ^ 2 - 72 * x ^ 3| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-56) 128 (-72) 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1)
        ((-56 : ℝ) * x + 128 * x ^ 2 - 72 * x ^ 3) hP
      rw [pow_one] at hk
      linarith
    have hB2 : |(α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(16 : ℝ) - 64 * x + 84 * x ^ 2 - 36 * x ^ 3| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 16 (-64) 84 (-36) 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 2 (by norm_num)
        ((16 : ℝ) - 64 * x + 84 * x ^ 2 - 36 * x ^ 3) hP
      linarith
    calc |4 * x * (1 - x) * (-4 + 8 * x) + (α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)
            + (α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)|
        ≤ |4 * x * (1 - x) * (-4 + 8 * x)| + |(α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)|
            + |(α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)| := abs_sum3_le _ _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α :=
          add_le_add (add_le_add hA hB1) hB2
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_three]
    have hA : |4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)|
        ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(16 : ℝ) - 96 * x + 96 * x ^ 2| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 16 (-96) 96 0 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      exact abs_four_mul_le x (16 - 96 * x + 96 * x ^ 2) hx hV
    have hB1 : |(α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)|
        ≤ 2 * 10 ^ 5 * α := by
      have hP : |(288 : ℝ) * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4|
          ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 288 (-1536) 2304 (-1056) 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1)
        ((288 : ℝ) * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4) hP
      rw [pow_one] at hk
      linarith
    have hB2 : |(α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)|
        ≤ 2 * 10 ^ 5 * α := by
      have hP : |(480 : ℝ) * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4|
          ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 480 (-1776) 2160 (-864) 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 2 (by norm_num)
        ((480 : ℝ) * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4) hP
      linarith
    have hB3 : |(α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)|
        ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-64 : ℝ) + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4|
          ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-64) 352 (-720) 648 (-216) 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 3 (by norm_num)
        ((-64 : ℝ) + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4) hP
      linarith
    calc |4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)
            + (α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)
            + (α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)
            + (α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)|
        ≤ |4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)|
            + |(α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)|
            + |(α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)|
            + |(α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)| :=
          abs_sum4_le _ _ _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α :=
          add_le_add (add_le_add (add_le_add hA hB1) hB2) hB3
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_four]
    have hA : |4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)|
        ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(-64 : ℝ) + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-64) 896 (-2304) 1536 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      exact abs_four_mul_le x (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3) hx hV
    have hB1 : |(α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
          - 19200 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-1408 : ℝ) * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
          - 19200 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-1408) 15616 (-45696) 50688 (-19200)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1)
        ((-1408 : ℝ) * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4 - 19200 * x ^ 5) hP
      rw [pow_one] at hk
      linarith
    have hB2 : |(α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
          - 20160 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-3072 : ℝ) * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
          - 20160 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-3072) 24000 (-58560) 57792 (-20160)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 2 (by norm_num)
        ((-3072 : ℝ) * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4 - 20160 * x ^ 5) hP
      linarith
    have hB3 : |(α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
          - 8640 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-3328 : ℝ) * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
          - 8640 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-3328) 17152 (-32832) 27648 (-8640)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 3 (by norm_num)
        ((-3328 : ℝ) * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4 - 8640 * x ^ 5) hP
      linarith
    have hB4 : |(α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
          - 1296 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(256 : ℝ) - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
          - 1296 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 256 (-1792) 4992 (-6912) 4752 (-1296)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 4 (by norm_num)
        ((256 : ℝ) - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4 - 1296 * x ^ 5) hP
      linarith
    calc |4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)
            + (α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
                - 19200 * x ^ 5)
            + (α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
                - 20160 * x ^ 5)
            + (α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
                - 8640 * x ^ 5)
            + (α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
                - 1296 * x ^ 5)|
        ≤ |4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)|
            + |(α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
                - 19200 * x ^ 5)|
            + |(α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
                - 20160 * x ^ 5)|
            + |(α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
                - 8640 * x ^ 5)|
            + |(α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
                - 1296 * x ^ 5)| :=
          abs_sum5_le _ _ _ _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α
            + 2 * 10 ^ 5 * α :=
          add_le_add (add_le_add (add_le_add (add_le_add hA hB1) hB2) hB3) hB4
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]

end Work.FTS.Nonlinear.Pieces.RNP26
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.wJet_lip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS_EllLimOK.BoxRegAux (dz dth dir1 prod_dir1_le_one norm_dz_le_one norm_dth_le_one)

theorem wJet_lip {a b K : ℝ} {F : ℝ × ℝ → ℝ} (hab : a < b)
    (hsm : ContDiffOn ℝ 2 F (Work.FTS_EllLimOK.cbox a b))
    (hb : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      ‖iteratedFDerivWithin ℝ 2 F (Work.FTS_EllLimOK.cbox a b) p‖ ≤ K) :
    (∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F p
        - Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F q| ≤ K * ‖p - q‖) ∧
    (∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F p
        - Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F q| ≤ K * ‖p - q‖) := by
  have hs : UniqueDiffOn ℝ (cbox a b) := uniqueDiffOn_cbox hab
  have hconv : Convex ℝ (cbox a b) := by
    rw [cbox]
    exact (convex_Icc a b).prod (convex_Icc 0 (π / 2))
  -- the first within-derivative is differentiable on the box, being `C¹` there
  have hD : DifferentiableOn ℝ (iteratedFDerivWithin ℝ 1 F (cbox a b)) (cbox a b) :=
    hsm.differentiableOn_iteratedFDerivWithin (m := 1) (by norm_num) hs
  -- its within-derivative has operator norm bounded by `K`
  have hbound : ∀ x ∈ cbox a b,
      ‖fderivWithin ℝ (iteratedFDerivWithin ℝ 1 F (cbox a b)) (cbox a b) x‖ ≤ K := by
    intro x hx
    rw [norm_fderivWithin_iteratedFDerivWithin]
    exact hb x hx
  have hmem : (a, 0) ∈ cbox a b := by
    rw [mem_cbox]
    exact ⟨⟨le_rfl, le_of_lt hab⟩, ⟨le_rfl, by positivity⟩⟩
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hb _ hmem)
  -- the componentwise Lipschitz bound for an arbitrary direction of norm `≤ 1`
  have key : ∀ (v : ℝ × ℝ), ‖v‖ ≤ 1 → ∀ p ∈ cbox a b, ∀ q ∈ cbox a b,
      |iteratedFDerivWithin ℝ 1 F (cbox a b) p (dir1 v)
        - iteratedFDerivWithin ℝ 1 F (cbox a b) q (dir1 v)| ≤ K * ‖p - q‖ := by
    intro v hv p hp q hq
    have hM : ‖iteratedFDerivWithin ℝ 1 F (cbox a b) p
        - iteratedFDerivWithin ℝ 1 F (cbox a b) q‖ ≤ K * ‖p - q‖ :=
      hconv.norm_image_sub_le_of_norm_fderivWithin_le hD hbound hq hp
    have h1 : ‖(iteratedFDerivWithin ℝ 1 F (cbox a b) p
        - iteratedFDerivWithin ℝ 1 F (cbox a b) q) (dir1 v)‖
        ≤ ‖iteratedFDerivWithin ℝ 1 F (cbox a b) p
            - iteratedFDerivWithin ℝ 1 F (cbox a b) q‖ * ∏ i : Fin 1, ‖dir1 v i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    have h2 : ∏ i : Fin 1, ‖dir1 v i‖ ≤ 1 := prod_dir1_le_one v hv
    have h4 : (0 : ℝ) ≤ ∏ i : Fin 1, ‖dir1 v i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs] at h1
    calc |iteratedFDerivWithin ℝ 1 F (cbox a b) p (dir1 v)
          - iteratedFDerivWithin ℝ 1 F (cbox a b) q (dir1 v)|
        = |(iteratedFDerivWithin ℝ 1 F (cbox a b) p
            - iteratedFDerivWithin ℝ 1 F (cbox a b) q) (dir1 v)| := rfl
      _ ≤ ‖iteratedFDerivWithin ℝ 1 F (cbox a b) p
            - iteratedFDerivWithin ℝ 1 F (cbox a b) q‖ * ∏ i : Fin 1, ‖dir1 v i‖ := h1
      _ ≤ (K * ‖p - q‖) * ∏ i : Fin 1, ‖dir1 v i‖ :=
          mul_le_mul_of_nonneg_right hM h4
      _ ≤ (K * ‖p - q‖) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 (norm_nonneg _))
      _ = K * ‖p - q‖ := mul_one _
  constructor
  · intro p hp q hq
    rw [wPz]
    exact key dz norm_dz_le_one p hp q hq
  · intro p hp q hq
    rw [wPth]
    exact key dth norm_dth_le_one p hp q hq

end Work.FTS_EllLimOK.BoxDataH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.wJet_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.BoxDataH.wJet_slice` — the slice derivatives of a `C²`-within-the-box function

`WithinVec` defines the six within-partials `wPz`, `wPth`, `wPzz`, `wPtz`, `wPzt`, `wPtt` of a
function `F : ℝ × ℝ → ℝ` on the closed box `cbox a b = [a,b] × [0,π/2]`.  This module shows that
they are the derivatives of the corresponding one-variable slices: for
`F` of class `C²` *within* the box (only!), and every `(z,θ) ∈ cbox a b`,

* `∂_z (z' ↦ F (z',θ)) = wPz F (z,θ)`, `∂_θ (θ' ↦ F (z,θ')) = wPth F (z,θ)`,
* `∂_z (z' ↦ wPz F (z',θ)) = wPzz F (z,θ)`, `∂_θ (θ' ↦ wPz F (z,θ')) = wPtz F (z,θ)`,
* `∂_z (z' ↦ wPth F (z',θ)) = wPzt F (z,θ)`, `∂_θ (θ' ↦ wPth F (z,θ')) = wPtt F (z,θ)`,

where all the derivatives are taken *within* the corresponding closed interval (`Set.Icc a b`,
resp. `Set.Icc 0 (π/2)`); the endpoints are covered.

The proof is the chain rule for within-derivatives
(`HasFDerivWithinAt.comp_hasDerivWithinAt`) applied to the two coordinate curves
`z' ↦ (z',θ)` and `θ' ↦ (z,θ')`, which map the interval into the box, together with the bridges
`wPz_eq_fderivWithin` etc. of `WithinVec` and the `C¹`-regularity of `fderivWithin ℝ F (cbox a b)`
(`ContDiffOn.fderivWithin`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS_EllLimOK.BoxRegAux (dz dth dir1 consD)
open Work.FTS_EllLimOK (cbox mem_cbox)

set_option autoImplicit false

/-! ## The two coordinate curves of the box -/

/-- The `z`-curve `z' ↦ (z',θ)` of the box, as a within-derivative on `[c,d]`. -/
theorem wJetSlice_zCurve {c d : ℝ} (θ z : ℝ) :
    HasDerivWithinAt (fun z' => ((z', θ) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) (Set.Icc c d) z :=
  ((hasDerivAt_id z).prodMk (hasDerivAt_const z θ)).hasDerivWithinAt

/-- The `θ`-curve `θ' ↦ (z,θ')` of the box, as a within-derivative on `[c,d]`. -/
theorem wJetSlice_thCurve {c d : ℝ} (z θ : ℝ) :
    HasDerivWithinAt (fun θ' => ((z, θ') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) (Set.Icc c d) θ :=
  ((hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)).hasDerivWithinAt

/-! ## The slices of a function -/

/-- **The `z`-slice of a function** with a within-derivative `L` on the box: its `z`-derivative
within `[a,b]` is `L dz`. -/
theorem wJetSlice_slice_z {a b : ℝ} {F : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ}
    {z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2))
    (hF : HasFDerivWithinAt F L (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun z' => F (z', θ)) (L dz) (Set.Icc a b) z := by
  have hcurve := wJetSlice_zCurve (c := a) (d := b) θ z
  have hst : MapsTo (fun z' => ((z', θ) : ℝ × ℝ)) (Set.Icc a b) (cbox a b) :=
    fun z' hz => ⟨hz, hθ⟩
  have h := hF.comp_hasDerivWithinAt z hcurve hst
  simpa [Function.comp_def, dz] using h

/-- **The `θ`-slice of a function** with a within-derivative `L` on the box: its `θ`-derivative
within `[0,π/2]` is `L dth`. -/
theorem wJetSlice_slice_th {a b : ℝ} {F : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ}
    {z θ : ℝ} (hz : z ∈ Set.Icc a b)
    (hF : HasFDerivWithinAt F L (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun θ' => F (z, θ')) (L dth) (Set.Icc 0 (π / 2)) θ := by
  have hcurve := wJetSlice_thCurve (c := 0) (d := π / 2) z θ
  have hst : MapsTo (fun θ' => ((z, θ') : ℝ × ℝ)) (Set.Icc 0 (π / 2)) (cbox a b) :=
    fun θ' hθ => ⟨hz, hθ⟩
  have h := hF.comp_hasDerivWithinAt θ hcurve hst
  simpa [Function.comp_def, dth] using h

/-! ## The slices of a continuous-linear-map-valued function -/

/-- **The `z`-slice of a `(ℝ × ℝ) →L[ℝ] ℝ`-valued function**, evaluated at a fixed direction
`v`: its `z`-derivative within `[a,b]` is `(P' dz) v`, where `P'` is the within-derivative of
`P`. -/
theorem wJetSlice_slice_z_clm {a b : ℝ} {P : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)}
    {P' : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)} {z θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) (v : ℝ × ℝ)
    (hP : HasFDerivWithinAt P P' (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun z' => P (z', θ) v) ((P' dz) v) (Set.Icc a b) z := by
  have hcurve := wJetSlice_zCurve (c := a) (d := b) θ z
  have hst : MapsTo (fun z' => ((z', θ) : ℝ × ℝ)) (Set.Icc a b) (cbox a b) :=
    fun z' hz => ⟨hz, hθ⟩
  have hc := hP.comp_hasDerivWithinAt z hcurve hst
  have hu : HasDerivWithinAt (fun _ : ℝ => v) (0 : ℝ × ℝ) (Set.Icc a b) z :=
    (hasDerivAt_const z v).hasDerivWithinAt
  have h := hc.clm_apply hu
  simpa [Function.comp_def, dz] using h

/-- **The `θ`-slice of a `(ℝ × ℝ) →L[ℝ] ℝ`-valued function**, evaluated at a fixed direction
`v`: its `θ`-derivative within `[0,π/2]` is `(P' dth) v`. -/
theorem wJetSlice_slice_th_clm {a b : ℝ} {P : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)}
    {P' : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)} {z θ : ℝ}
    (hz : z ∈ Set.Icc a b) (v : ℝ × ℝ)
    (hP : HasFDerivWithinAt P P' (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun θ' => P (z, θ') v) ((P' dth) v) (Set.Icc 0 (π / 2)) θ := by
  have hcurve := wJetSlice_thCurve (c := 0) (d := π / 2) z θ
  have hst : MapsTo (fun θ' => ((z, θ') : ℝ × ℝ)) (Set.Icc 0 (π / 2)) (cbox a b) :=
    fun θ' hθ => ⟨hz, hθ⟩
  have hc := hP.comp_hasDerivWithinAt θ hcurve hst
  have hu : HasDerivWithinAt (fun _ : ℝ => v) (0 : ℝ × ℝ) (Set.Icc 0 (π / 2)) θ :=
    (hasDerivAt_const θ v).hasDerivWithinAt
  have h := hc.clm_apply hu
  simpa [Function.comp_def, dth] using h

/-! ## The six slice derivatives -/

theorem wJet_slice {a b : ℝ} {F : ℝ × ℝ → ℝ} (hab : a < b)
    (hsm : ContDiffOn ℝ 2 F (Work.FTS_EllLimOK.cbox a b)) :
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => F (z', θ))
        (Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => F (z, θ'))
        (Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc 0 (π / 2)) θ) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F (z', θ))
        (Work.FTS_EllLimOK.BoxDataH.wPzz (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F (z, θ'))
        (Work.FTS_EllLimOK.BoxDataH.wPtz (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc 0 (π / 2)) θ) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F (z', θ))
        (Work.FTS_EllLimOK.BoxDataH.wPzt (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F (z, θ'))
        (Work.FTS_EllLimOK.BoxDataH.wPtt (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc 0 (π / 2)) θ) := by
  have hU : UniqueDiffOn ℝ (cbox a b) := uniqueDiffOn_cbox hab
  have hFd : DifferentiableOn ℝ F (cbox a b) := hsm.differentiableOn (by norm_num)
  have hPsm : ContDiffOn ℝ 1 (fderivWithin ℝ F (cbox a b)) (cbox a b) :=
    hsm.fderivWithin hU (by norm_num)
  have hPd : DifferentiableOn ℝ (fderivWithin ℝ F (cbox a b)) (cbox a b) :=
    hPsm.differentiableOn (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_z hθ ((hFd (z, θ) hp).hasFDerivWithinAt)
    rwa [← wPz_eq_fderivWithin (hU (z, θ) hp)] at h
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_th hz ((hFd (z, θ) hp).hasFDerivWithinAt)
    rwa [← wPth_eq_fderivWithin (hU (z, θ) hp)] at h
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_z_clm hθ dz ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPzz_eq_fderivWithin hU hp] at h
    exact h.congr (fun z' hz' => wPz_eq_fderivWithin (hU (z', θ) ⟨hz', hθ⟩))
      (wPz_eq_fderivWithin (hU (z, θ) hp))
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_th_clm hz dz ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPtz_eq_fderivWithin hU hp] at h
    exact h.congr (fun θ' hθ' => wPz_eq_fderivWithin (hU (z, θ') ⟨hz, hθ'⟩))
      (wPz_eq_fderivWithin (hU (z, θ) hp))
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_z_clm hθ dth ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPzt_eq_fderivWithin hU hp] at h
    exact h.congr (fun z' hz' => wPth_eq_fderivWithin (hU (z', θ) ⟨hz', hθ⟩))
      (wPth_eq_fderivWithin (hU (z, θ) hp))
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_th_clm hz dth ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPtt_eq_fderivWithin hU hp] at h
    exact h.congr (fun θ' hθ' => wPth_eq_fderivWithin (hU (z, θ') ⟨hz, hθ'⟩))
      (wPth_eq_fderivWithin (hU (z, θ) hp))

end Work.FTS_EllLimOK.BoxDataH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.wJet_subseq_extract =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-! ## Two elementary real-analysis tools

The extraction below needs an equicontinuity modulus for a family whose second-order partials are
only **Hölder** of exponent `β > 0` (not Lipschitz).  The two lemmas here supply exactly that:
`x ↦ x ^ β` tends to `0` at `0⁺` for `β > 0`, and consequently `K * δ ^ β` can be made smaller
than any prescribed `ε > 0`. -/

/-- `x ^ β → 0` as `x → 0⁺`, for `β > 0`.  Derived from the negative-exponent limit
`tendsto_rpow_neg_nhdsGT_zero` of Mathlib by taking inverses. -/
theorem tendsto_rpow_nhdsGT_zero_of_pos {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto (fun x : ℝ => x ^ β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-β)) (𝓝[>] (0 : ℝ)) Filter.atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  refine (h1.inv_tendsto_atTop).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  change (x ^ (-β))⁻¹ = x ^ β
  rw [Real.rpow_neg (le_of_lt (show (0 : ℝ) < x from hx)) β, inv_inv]

/-- For `β > 0` and `ε > 0` the quantity `K * δ ^ β` can be made smaller than `ε` by a suitable
positive `δ`, for *every* real `K`. -/
theorem exists_mul_rpow_lt {K β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ K * δ ^ β < ε := by
  by_cases hK : K ≤ 0
  · exact ⟨1, one_pos, by rw [Real.one_rpow, mul_one]; linarith⟩
  · have hKpos : 0 < K := not_le.mp hK
    have hlim : Filter.Tendsto (fun x : ℝ => K * x ^ β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_rpow_nhdsGT_zero_of_pos hβ)
    have hmem : {x : ℝ | K * x ^ β < ε} ∈ 𝓝[>] (0 : ℝ) :=
      hlim.eventually (Iio_mem_nhds (a := ε) (b := 0) hε)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hmem
    have hr2 : (0 : ℝ) < r / 2 := by linarith
    have hmem2 : r / 2 ∈ Metric.ball (0 : ℝ) r ∩ Set.Ioi 0 := by
      refine ⟨?_, hr2⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
      linarith
    exact ⟨r / 2, hr2, hrsub hmem2⟩

/-! ## Uniform convergence transferred across a pointwise equality on the set -/

/-- If `G n` agrees with `F n` on `s` and `F ·` converges uniformly to `f` on `s`, then so does
`G ·`.  (`G` is the *unclamped* jet family and `F` the clamped one.) -/
theorem wJet_tendstoUniformlyOn_congr {ι α : Type*} [PseudoMetricSpace α]
    {F G : ι → α → ℝ} {f : α → ℝ} {l : Filter ι} {s : Set α}
    (h : TendstoUniformlyOn F f l s) (hFG : ∀ n x, x ∈ s → G n x = F n x) :
    TendstoUniformlyOn G f l s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn x hx
  rw [hFG n x hx]
  exact hn x hx

/-! ## The extraction -/

/-- **Subsequence extraction for the six within-partials of a `C²`-Hölder family on a closed
box.**  Given `Hn := Function.uncurry (H n)`, jointly `C²` on `cbox a b`, with

* the operator norms of `iteratedFDerivWithin ℝ k` (`k ≤ 2`) bounded by `K` on the box,
* the order-`2` within-derivatives Hölder of exponent `β > 0` with constant `K`,
* the first-order within-partials `wPz`, `wPth` Lipschitz with constant `K`,

there is a strictly monotone `φ` and a limit `g` of the six components of
`wJet (cbox a b) (uncurry (H (φ n)))` which is uniform on the box and whose limit is continuous
there.  The proof clamps the angle into `[0,π/2]` (the retraction `clampB` of `WithinVec`), which
turns the family into an equicontinuous family of *continuous* functions on the open
neighbourhood `U ⊃ cbox a b`; Arzelà–Ascoli
(`exists_subseq_tendstoLocallyUniformlyOn_fin`) then gives the subsequence, which is restricted
back to the box (where `clampB` is the identity). -/
theorem wJet_subseq_extract {H : ℕ → ℝ → ℝ → ℝ} {a b K β : ℝ} (hab : a < b) (hβ : 0 < β)
    (hsm : ∀ n, ContDiffOn ℝ 2 (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b))
    (hb : ∀ n k : ℕ, k ≤ 2 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      ‖iteratedFDerivWithin ℝ k (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b) p‖ ≤ K)
    (hh : ∀ n, ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b) p
        - iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b) q‖
        ≤ K * ‖p - q‖ ^ β)
    (hlip : ∀ n, ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) p
          - Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) q|
        ≤ K * ‖p - q‖ ∧
      |Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) p
          - Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) q|
        ≤ K * ‖p - q‖) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ × ℝ → (Fin 6 → ℝ),
      (∀ m : Fin 6, TendstoUniformlyOn
        (fun n p => Work.FTS_EllLimOK.BoxDataH.wJet (Work.FTS_EllLimOK.cbox a b)
          (Function.uncurry (H (φ n))) p m)
        (fun p => g p m) Filter.atTop (Work.FTS_EllLimOK.cbox a b)) ∧
      ContinuousOn g (Work.FTS_EllLimOK.cbox a b) := by
  classical
  have hab' : a ≤ b := le_of_lt hab
  -- ## 0. The box is nonempty, hence `0 ≤ K`
  have hK0 : 0 ≤ K := by
    have hmem : (((a, 0) : ℝ × ℝ)) ∈ Work.FTS_EllLimOK.cbox a b :=
      mem_cbox.mpr ⟨⟨le_rfl, hab'⟩, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩
    exact le_trans (norm_nonneg _) (hb 0 0 (by norm_num : (0 : ℕ) ≤ 2) (a, 0) hmem)
  -- ## 1. An open neighbourhood `U` of the box
  set U : Set (ℝ × ℝ) := Set.Ioo (a - 1) (b + 1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) with hUdef
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hboxcpt : IsCompact (Work.FTS_EllLimOK.cbox a b) := isCompact_Icc.prod isCompact_Icc
  have hboxU : Work.FTS_EllLimOK.cbox a b ⊆ U := by
    intro p hp
    rw [mem_cbox] at hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  have hmemB : ∀ p : ℝ × ℝ, clampB a b p ∈ Work.FTS_EllLimOK.cbox a b :=
    fun p => clampB_mem_cbox hab'
  -- ## 2. The clamped jet family
  set F : ℕ → ℝ × ℝ → (Fin 6 → ℝ) := fun n p =>
    wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p) with hFdef
  -- boundedness
  have hFbdd : ∀ n : ℕ, ∀ p : ℝ × ℝ, ‖F n p‖ ≤ K := by
    intro n p
    exact norm_wJet_le (s := Work.FTS_EllLimOK.cbox a b)
      (F := Function.uncurry (H n)) (p := clampB a b p) (hmemB p) (hb n)
  -- ## 3. Equicontinuity of the clamped family
  have heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p : ℝ × ℝ, ∀ q : ℝ × ℝ,
      dist p q < δ → ‖F n p - F n q‖ < ε := by
    intro ε hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_mul_rpow_lt (K := K) (β := β) (ε := ε / 2) hβ (by linarith)
    refine ⟨min (ε / (2 * (K + 1))) δ₂, lt_min (div_pos hε (by linarith)) hδ₂pos, ?_⟩
    intro n p q hpq
    have hpq1 : dist p q < ε / (2 * (K + 1)) := lt_of_lt_of_le hpq (min_le_left _ _)
    have hpq2 : dist p q < δ₂ := lt_of_lt_of_le hpq (min_le_right _ _)
    have hp' := hmemB p
    have hq' := hmemB q
    have hdist : ‖clampB a b p - clampB a b q‖ ≤ dist p q := by
      rw [← dist_eq_norm]
      exact dist_clampB_le a b p q
    -- the `K`-Lipschitz bound for the two first-order components
    have hKstep : K * (ε / (2 * (K + 1))) ≤ ε / 2 := by
      have hK1 : K / (K + 1) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < K + 1)]
        linarith
      calc K * (ε / (2 * (K + 1))) = (ε / 2) * (K / (K + 1)) := by
            field_simp
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hK1 (by linarith)
        _ = ε / 2 := by ring
    have hcomp : ∀ m : Fin 6, |F n p m - F n q m| ≤ ε / 2 := by
      intro m
      fin_cases m
      · -- `m = 0`: the `z`-partial, Lipschitz
        have h := (hlip n (clampB a b p) hp' (clampB a b q) hq').1
        change |wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
            - wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)| ≤ ε / 2
        calc |wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
              - wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)|
            ≤ K * ‖clampB a b p - clampB a b q‖ := h
          _ ≤ K * dist p q := mul_le_mul_of_nonneg_left hdist hK0
          _ ≤ K * (ε / (2 * (K + 1))) :=
              mul_le_mul_of_nonneg_left (le_of_lt hpq1) hK0
          _ ≤ ε / 2 := hKstep
      · -- `m = 1`: the `θ`-partial, Lipschitz
        have h := (hlip n (clampB a b p) hp' (clampB a b q) hq').2
        change |wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
            - wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)| ≤ ε / 2
        calc |wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
              - wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)|
            ≤ K * ‖clampB a b p - clampB a b q‖ := h
          _ ≤ K * dist p q := mul_le_mul_of_nonneg_left hdist hK0
          _ ≤ K * (ε / (2 * (K + 1))) :=
              mul_le_mul_of_nonneg_left (le_of_lt hpq1) hK0
          _ ≤ ε / 2 := hKstep
      · -- `m = 2`: `∂_z∂_z`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (2 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
      · -- `m = 3`: `∂_θ∂_z`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (3 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
      · -- `m = 4`: `∂_z∂_θ`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (4 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
      · -- `m = 5`: `∂_θ∂_θ`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (5 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
    have hnorm : ‖F n p - F n q‖ ≤ ε / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
      intro m
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact hcomp m
    linarith
  -- ## 4. Arzelà–Ascoli
  obtain ⟨φ, hφ, G, hGlim⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin (k := 6) hUopen
      (F := F) (fun _ _ _ => ⟨K, fun n p _ => hFbdd n p⟩)
      (fun _ _ _ ε hε => by
        obtain ⟨δ, hδpos, hδ⟩ := heqc ε hε
        exact ⟨δ, hδpos, fun n p _ q _ hpq => hδ n p q hpq⟩)
  -- ## 5. Continuity of the members, hence of the limit
  have hjetcont : ∀ n : ℕ, ContinuousOn
      (fun q : ℝ × ℝ =>
        wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) q)
      (Work.FTS_EllLimOK.cbox a b) :=
    fun n => continuousOn_pi.mpr (continuousOn_wJet hab (hsm n))
  have hFcont : ∀ n : ℕ, ContinuousOn (F n) (Work.FTS_EllLimOK.cbox a b) := by
    intro n
    refine (hjetcont n).congr (fun p hp => ?_)
    change wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
      = wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) p
    rw [clampB_eq_of_mem_cbox hp]
  -- ## 6. Assembly
  have hunif : TendstoUniformlyOn (fun n p => F (φ n) p) G Filter.atTop
      (Work.FTS_EllLimOK.cbox a b) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).mp hGlim
      (Work.FTS_EllLimOK.cbox a b) hboxU hboxcpt
  have hGcont : ContinuousOn G (Work.FTS_EllLimOK.cbox a b) :=
    hunif.continuousOn (Frequently.of_forall fun n => hFcont (φ n))
  refine ⟨φ, hφ, G, ?_, hGcont⟩
  intro m
  refine wJet_tendstoUniformlyOn_congr
    (F := fun n p => F (φ n) p m) (tendstoUniformlyOn_jetVec_component hunif m) ?_
  intro n p hp
  change wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H (φ n))) p m
    = wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H (φ n))) (clampB a b p) m
  rw [clampB_eq_of_mem_cbox hp]

end Work.FTS_EllLimOK.BoxDataH
end
end
-- ===== merged: Submission.Work.Spaces.BadTermSqBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- The two dominating functions used by the bad term of the `H^4` product rule:

* `badU α f z` is the (constant in `θ`) bound for the `f`-factor, coming from the angular
  Hardy inequality (`bt_f_bound`);
* `badV α g θ` is the (constant in `z`) bound for the `g`-factor, coming from the radial
  Hardy inequality (`bt_g_bound`).

Both are honest integrable functions: `badU` because the squared weighted mixed derivative
`mixed 3 1 f · W` is square-integrable on the product (`bt_prod_integrable`), `badV` for the
same reason with `g` and `mixed 1 1 g`. -/
def badU (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  100 / (gam α - 1) * ∫ s in Iθ, (mixed 3 1 f z s * Wt α z s) ^ 2

def badV (α : ℝ) (g : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z' in Iz, (mixed 1 1 g z' θ * Wt α z' θ) ^ 2




end Work.Spaces
end
end
