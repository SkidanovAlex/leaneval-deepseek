/-
Work module for the Elgindi finite-time singularity project.

# `BSlotTop/SliceAngGenFinal`: the final assembly of the one-dimensional angular estimate

This is the clean-cone copy of `Work.FTS.EllipticEst.remov.slice_ang_gen_final`
(`Submission/Work/FTS/EllipticEst/remov/slice_ang_gen_final.lean`), with its `sorry` filled in.

Given the weighted `v = u/cos θ` slot bounds

  `∫_{Iθ} (v^{(m)})² · sin(2θ)^{2k-γ} ≤ C·AngRHS k γ u g`  (`m ≤ k+1`, with the integrability of
  the integrand) — supplied by `remov.slice_ang_v_outer` and `remov.slice_ang_v_far` — the top
plain slot estimate

  `∫_{Iθ} (u^{(k+2)})² · sin(2θ)^{2k-γ} ≤ C·AngRHS k γ u g`

follows:  `tan θ·u = sin θ·v`, so by Leibniz together with `|sin^{(j)}| ≤ 1`,
`(∂_θ^{k+1}(tan θ·u))² ≤ C_k Σ_{m≤k+1}(v^{(m)})²` a.e. on `Iθ`, while
`∂_θ^{k+1}(tan θ·u) = u^{(k+2)} + 6u^{(k)} + g^{(k)}` (`remov.ang_ode_iterate`); integrating the
resulting pointwise inequality against `sin(2θ)^{2k-γ}` and bounding the `u^{(k)}`-slot by the
`H3(k)`- (or, for `k = 2`, the `H4`-) slot of `AngRHS` and the `g^{(k)}`-slot by
`g_slot_le_angRHS` closes the proof.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.slice_ang_asm
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce
import Submission.Work.FTS.EllipticEst.remov.ang_ode_iterate
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_E_leibniz
import Submission.Work.FTS.EllipticEst.remov.angSlot_le_AngRHS
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.SrcBoundFts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- On `Iθ` the weight `sin(2θ)` is nonnegative. -/
private lemma sin_two_nonneg_Iθ_fts {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin(2θ)` is positive on the open interval. -/
private lemma sin_two_pos_Ioo_fts {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `Ioo 0 (π/2)` is co-null in `volume.restrict Iθ`. -/
private lemma haeIoo_fts :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

private lemma angRHS_nonneg_fts (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    0 ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨hA, hB, hC, hD⟩ := Work.FTS.EllipticEst.remov.angRHS_rest_nonneg k γ u g
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _))
  rw [Work.FTS.EllipticEst.remov.angSlot_AngRHS_unfold]
  linarith

/-- The `H4`-slot of `AngRHS` is bounded by `AngRHS`. -/
private lemma h4slot_le_angRHS_fts (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨hA, hB, hC, hD⟩ := Work.FTS.EllipticEst.remov.angRHS_rest_nonneg k γ u g
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _))
  rw [Work.FTS.EllipticEst.remov.angSlot_AngRHS_unfold]
  linarith

/-- A single `H3`-slot of `AngRHS` is bounded by `AngRHS`. -/
private lemma h3slot_le_angRHS_fts {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} {j : ℕ}
    (hj : j ∈ Finset.Icc 3 (k + 1)) :
    (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨hA, hB, hC, hD⟩ := Work.FTS.EllipticEst.remov.angRHS_rest_nonneg k γ u g
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _))
  have hsingle : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
      ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j' u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
    Finset.single_le_sum (f := fun j' => ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j' u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ))
      (fun j' _ => MeasureTheory.setIntegral_nonneg
        (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _)))
      hj
  rw [Work.FTS.EllipticEst.remov.angSlot_AngRHS_unfold]
  linarith

/-- **The final assembly of the one-dimensional angular estimate.** -/
theorem sliceAngGenFinalFts (k : ℕ) (hk : 2 ≤ k)
    (hV : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.SliceHyp k γ u g → ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
        ∧ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨Cv, hCvpos, hVb⟩ := hV
  set CM : ℝ := ((k : ℝ) + 2) * (2 : ℝ) ^ (2 * (k + 1)) with hCMdef
  have hCMnn : 0 ≤ CM := by rw [hCMdef]; positivity
  refine ⟨3 * (CM * ((k : ℝ) + 2) * Cv + 37), by positivity, ?_⟩
  intro γ u g h
  obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hIk2, hIgk, hIhigh, hI2, hI1, hI0⟩ := h
  set v : ℝ → ℝ := fun t => u t / Real.cos t with hvdef
  have hSlice : Work.FTS.EllipticEst.remov.SliceHyp k γ u g :=
    ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hIk2, hIgk, hIhigh, hI2, hI1, hI0⟩
  have hv_cd : ContDiffOn ℝ (k + 2) v (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hvdef]
    exact Work.FTS.EllipticEst.remov.TopCoreB.contDiffOn_vF hu
  have hv_cdAt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiffAt ℝ (k + 2) v θ := fun θ hθ =>
    hv_cd.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hRnn : 0 ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := angRHS_nonneg_fts k γ u g
  -- ## the `u^{(k)}`-slot majorant
  have hSk : ∃ Sk : ℝ → ℝ, MeasureTheory.IntegrableOn Sk Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, Sk θ) ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g
      ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) ≤ Sk θ := by
    rcases eq_or_lt_of_le hk with hk2 | hk3
    · subst hk2
      refine ⟨fun θ => (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)), hI2, ?_, ?_⟩
      · exact h4slot_le_angRHS_fts 2 γ u g
      · intro θ hθ
        have h2e : iteratedDeriv 2 u θ = deriv (deriv u) θ := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
        rw [h2e]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_Ioo_fts hθ) (Real.sin_le_one _) ?_
        have heta := Work.Spaces.eta_pos
        have hcast : 2 * ((2 : ℕ) : ℝ) = 4 := by norm_num
        rw [hcast]
        have : Work.Spaces.eta ≤ 4 - γ := by
          rw [show Work.Spaces.eta = 99 / 100 from rfl]; linarith
        linarith [heta, this]
    · refine ⟨fun θ => (iteratedDeriv k u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - 4 - γ),
        hIhigh k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), ?_, ?_⟩
      · exact h3slot_le_angRHS_fts (k := k) (γ := γ) (u := u) (g := g)
          (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · intro θ hθ
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_Ioo_fts hθ) (Real.sin_le_one _) ?_
        linarith
  obtain ⟨Sk, hSkint, hSkbd, hSkmaj⟩ := hSk
  -- ## the pointwise Leibniz bound
  have hlevB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2
        ≤ CM * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 := by
    intro θ hθ
    have hev : (fun t => Real.tan t * u t) =ᶠ[𝓝 θ] (Real.sin * v) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      have hct : Real.cos t ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
      simp only [Pi.mul_apply, hvdef]
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have h1 : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        = iteratedDeriv (k + 1) (Real.sin * v) θ :=
      Filter.EventuallyEq.iteratedDeriv_eq _ hev
    rw [h1]
    have hcd_sin : ContDiffAt ℝ (((k + 1 : ℕ)) : WithTop ℕ∞) Real.sin θ :=
      (Real.contDiff_sin (n := (((k + 1 : ℕ)) : WithTop ℕ∞))).contDiffAt
    have hcd_v : ContDiffAt ℝ (((k + 1 : ℕ)) : WithTop ℕ∞) v θ :=
      (hv_cdAt θ hθ).of_le
        (by exact_mod_cast (Nat.le_succ (k + 1) : k + 1 ≤ k + 2))
    have hlev := iteratedDeriv_mul hcd_sin hcd_v
    rw [hlev]
    have habs : |∑ i ∈ Finset.range (k + 2), (((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.sin θ * iteratedDeriv (k + 1 - i) v θ)|
        ≤ ∑ i ∈ Finset.range (k + 2),
            (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro i _
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((k + 1).choose i : ℕ) : ℝ))]
      have hs := Work.FTS.EllipticEst.remov.TopCoreB.abs_iteratedDeriv_sin_le_one i θ
      have hch : (((k + 1).choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
        have := Work.FTS.EllipticEst.remov.TopCoreB.choose_le_two_pow (k + 1) i
        exact_mod_cast this
      calc (((k + 1).choose i : ℕ) : ℝ) * |iteratedDeriv i Real.sin θ|
            * |iteratedDeriv (k + 1 - i) v θ|
          ≤ (2 : ℝ) ^ (k + 1) * 1 * |iteratedDeriv (k + 1 - i) v θ| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact mul_le_mul hch hs (abs_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ| := by ring
    have hstep1 : (∑ i ∈ Finset.range (k + 2), (((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.sin θ * iteratedDeriv (k + 1 - i) v θ)) ^ 2
        ≤ (∑ i ∈ Finset.range (k + 2),
            (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa only [sq_abs] using h
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 2))
      (f := fun i => (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|)
    have hreindex : (∑ i ∈ Finset.range (k + 2),
          ((2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2)
        = (2 : ℝ) ^ (2 * (k + 1)) * ∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2 := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_range_reflect (fun m => (2 : ℝ) ^ (2 * (k + 1))
        * (iteratedDeriv m v θ) ^ 2) (k + 2)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hidx : k + 2 - 1 - i = k + 1 - i := by omega
      rw [hidx]
      have hsq2 : ((2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2
          = (2 : ℝ) ^ (2 * (k + 1)) * (iteratedDeriv (k + 1 - i) v θ) ^ 2 := by
        rw [mul_pow, sq_abs]
        rw [show ((2 : ℝ) ^ (k + 1)) ^ 2 = (2 : ℝ) ^ (2 * (k + 1)) from by
          rw [← pow_mul]; congr 1; ring]
      rw [hsq2]
    calc (∑ i ∈ Finset.range (k + 2), (((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.sin θ * iteratedDeriv (k + 1 - i) v θ)) ^ 2
        ≤ (∑ i ∈ Finset.range (k + 2),
            (2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2 := hstep1
      _ ≤ ((Finset.range (k + 2)).card : ℝ)
            * ∑ i ∈ Finset.range (k + 2),
              ((2 : ℝ) ^ (k + 1) * |iteratedDeriv (k + 1 - i) v θ|) ^ 2 := hsq
      _ = ((k : ℝ) + 2) * ((2 : ℝ) ^ (2 * (k + 1))
            * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) := by
          rw [Finset.card_range, hreindex]; push_cast; ring
      _ = CM * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 := by
          rw [hCMdef]; ring
  -- ## the pointwise bound for the top slot
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ 3 * (CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2)
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + 36 * Sk θ
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
    intro θ hθ
    have hode := Work.FTS.EllipticEst.remov.ang_ode_iterate k hu hg θ hθ
    have hlb := hlevB θ hθ
    have hSkb := hSkmaj θ hθ
    set qθ : ℝ := Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) with hqθdef
    have hqnn : 0 ≤ qθ := by
      rw [hqθdef]; exact Real.rpow_nonneg (le_of_lt (sin_two_pos_Ioo_fts hθ)) _
    have hsq : (iteratedDeriv (k + 2) u θ) ^ 2
        ≤ 3 * ((iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2
            + 36 * (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2) := by
      have h : iteratedDeriv (k + 2) u θ
          = iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
            + (-(6 * iteratedDeriv k u θ)) + (-(iteratedDeriv k g θ)) := by linarith
      have h3 := sq_three_le (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ)
        (-(6 * iteratedDeriv k u θ)) (-(iteratedDeriv k g θ))
      rw [h]
      nlinarith [h3, sq_nonneg (iteratedDeriv k u θ), sq_nonneg (iteratedDeriv k g θ)]
    have hchain : (iteratedDeriv (k + 2) u θ) ^ 2 * qθ
        ≤ 3 * (CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ)
            + 36 * Sk θ
            + (iteratedDeriv k g θ) ^ 2 * qθ) := by
      refine le_trans (mul_le_mul_of_nonneg_right hsq hqnn) ?_
      have hkey : CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ)
          + 36 * ((iteratedDeriv k u θ) ^ 2 * qθ)
          + (iteratedDeriv k g θ) ^ 2 * qθ
          ≤ CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ)
            + 36 * Sk θ
            + (iteratedDeriv k g θ) ^ 2 * qθ := by
        have h4 : 36 * ((iteratedDeriv k u θ) ^ 2 * qθ) ≤ 36 * Sk θ :=
          mul_le_mul_of_nonneg_left hSkb (by norm_num)
        linarith [h4]
      have h1 : (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2 * qθ
          ≤ CM * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) * qθ) := by
        have := mul_le_mul_of_nonneg_right hlb hqnn
        simpa only [mul_assoc] using this
      have hthis : 3 * ((iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2
            + 36 * (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2) * qθ
          = 3 * ((iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ) ^ 2 * qθ
            + 36 * ((iteratedDeriv k u θ) ^ 2 * qθ)
            + (iteratedDeriv k g θ) ^ 2 * qθ) := by ring
      rw [hthis]
      nlinarith [hkey, h1]
    exact hchain
  -- ## the majorant and its integrability
  have hsumInt : MeasureTheory.IntegrableOn (fun θ => (∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      Work.Spaces.Iθ := by
    rw [show (fun θ => (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2)
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        = fun θ => ∑ m ∈ Finset.range (k + 2), ((iteratedDeriv m v θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) from by
      funext θ; rw [Finset.sum_mul]]
    exact MeasureTheory.integrable_finset_sum _ (fun m hm =>
      (hVb γ u g hSlice m (by have := Finset.mem_range.mp hm; omega)).1)
  have hIF1 : MeasureTheory.IntegrableOn (fun θ => CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
      Work.Spaces.Iθ := hsumInt.const_mul CM
  have hIF2 : MeasureTheory.IntegrableOn (fun θ => CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ) Work.Spaces.Iθ := hIF1.add (hSkint.const_mul 36)
  have hIF3 : MeasureTheory.IntegrableOn (fun θ => CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ := hIF2.add hIgk
  have hMajInt : MeasureTheory.IntegrableOn (fun θ => 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) Work.Spaces.Iθ := hIF3.const_mul 3
  have hmain : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
          (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
    MeasureTheory.integral_mono_of_nonneg
      (haeIoo_fts.mono fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos_Ioo_fts hθ)) _))
      hMajInt
      (haeIoo_fts.mono fun θ hθ => hpt θ hθ)
  -- ## evaluating the majorant
  have hsumEval : (∫ θ in Work.Spaces.Iθ, (∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = ∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      rw [Finset.sum_mul])]
    exact MeasureTheory.integral_finsetSum _ (fun m hm =>
      (hVb γ u g hSlice m (by have := Finset.mem_range.mp hm; omega)).1)
  have hsumEval' : (∫ θ in Work.Spaces.Iθ, (∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = ∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := hsumEval
  have hsumBd : (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ ((k : ℝ) + 2) * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
    calc (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∑ _m ∈ Finset.range (k + 2), Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
          Finset.sum_le_sum fun m hm =>
            (hVb γ u g hSlice m (by have := Finset.mem_range.mp hm; omega)).2
      _ = ((Finset.range (k + 2)).card : ℝ)
            * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((k : ℝ) + 2) * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
          rw [Finset.card_range]; push_cast; ring
  have hval : (∫ θ in Work.Spaces.Iθ, 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
      (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
      = 3 * (CM * (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * (∫ θ in Work.Spaces.Iθ, Sk θ)
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (CM * ((∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = (∫ θ in Work.Spaces.Iθ, (CM * ((∑ m ∈ Finset.range (k + 2),
              (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + 36 * Sk θ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
      MeasureTheory.integral_add hIF2 hIgk
    have h2 : (∫ θ in Work.Spaces.Iθ, (CM * ((∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * Sk θ))
        = (∫ θ in Work.Spaces.Iθ, CM * ((∑ m ∈ Finset.range (k + 2),
              (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          + (∫ θ in Work.Spaces.Iθ, 36 * Sk θ) :=
      MeasureTheory.integral_add hIF1 (hSkint.const_mul 36)
    have h3 : (∫ θ in Work.Spaces.Iθ, CM * ((∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = CM * (∫ θ in Work.Spaces.Iθ, (∑ m ∈ Finset.range (k + 2),
            (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
      MeasureTheory.integral_const_mul CM _
    have h4 : (∫ θ in Work.Spaces.Iθ, 36 * Sk θ) = 36 * (∫ θ in Work.Spaces.Iθ, Sk θ) :=
      MeasureTheory.integral_const_mul 36 _
    rw [MeasureTheory.integral_const_mul, h1, h2, h3, h4, hsumEval]
  -- ## the final estimate
  have hgbd : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
    Work.FTS.EllipticEst.remov.g_slot_le_angRHS k γ u g
  calc (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (CM * ((∑ m ∈ Finset.range (k + 2),
          (iteratedDeriv m v θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + 36 * Sk θ + (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := hmain
    _ = 3 * (CM * (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + 36 * (∫ θ in Work.Spaces.Iθ, Sk θ)
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := hval
    _ ≤ 3 * (CM * (((k : ℝ) + 2) * (Cv * Work.FTS.EllipticEst.remov.AngRHS k γ u g))
          + 36 * Work.FTS.EllipticEst.remov.AngRHS k γ u g
          + Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        nlinarith [hsumBd, hSkbd, hgbd, mul_nonneg hCMnn hRnn, hRnn]
    _ = (3 * (CM * ((k : ℝ) + 2) * Cv + 37)) * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
        ring
end Work.FTS.EllipticEst.Prop.BSlotTop
