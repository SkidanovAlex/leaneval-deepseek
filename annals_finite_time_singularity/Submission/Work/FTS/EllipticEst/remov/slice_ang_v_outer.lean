import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce
import Submission.Work.FTS.EllipticEst.remov.near_pointwise_bound
import Submission.Work.FTS.EllipticEst.remov.mid_pointwise_bound
import Submission.Work.FTS.EllipticEst.remov.slice_ang_outer
import Submission.Work.FTS.EllipticEst.remov.invCos_jets_le
import Submission.Work.FTS.EllipticEst.remov.angSlot_le_AngRHS

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
private theorem angRHS_nonneg (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
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
          refine mul_le_mul_of_nonneg_right ?_ (angRHS_nonneg k γ u g)
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
