import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce
import Submission.Work.FTS.EllipticEst.remov.slice_ang_asm
import Submission.Work.FTS.EllipticEst.remov.slice_ang_A_leibniz
import Submission.Work.FTS.EllipticEst.remov.slice_ang_A_cs
import Submission.Work.FTS.EllipticEst.remov.ang_ode_iterate
import Submission.Work.FTS.EllipticEst.remov.angSlot_le_AngRHS
import Submission.Work.FTS.EllipticEst.remov.slice_ang_v_outer
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Prop.Rtilde.SliceGen`: the one-dimensional angular estimate `slice_ang_gen`, from the
weighted `v = u / cos θ` bounds.

This is the final assembly of the paper's §"General `ℋ^k` case" in its `v`-form: the
`(k+2)`-th angular derivative of `u` is controlled through the differentiated slice ODE
`u^{(k+2)} = ∂_θ^{k+1}(tan θ · u) - 6u^{(k)} - g^{(k)}` (`remov.ang_ode_iterate`) and the
Leibniz/Cauchy–Schwarz estimates `remov.slice_ang_A_leibniz`, `remov.slice_ang_A_cs` applied to
`∂_θ^{k+1}(sin θ · v)` with `v = u / cos θ`.  The only geometric input is the weighted `v`-bound
(`VBound`), produced by `remov.slice_ang_v_outer` (proved) and the far-window bound.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Prop.Rtilde

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The weighted `v = u / cos θ` bound hypothesis: for every datum of `SliceHyp k γ u g` and every
`m ≤ k+1`, the `m`-th derivative of `v` is honest against the weight `sin(2θ)^{2k-γ}` on `Iθ` and
its integral is at most `CV · AngRHS k γ u g`. -/
def VBound (k : ℕ) (CV : ℝ) : Prop :=
  0 < CV ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
    ∀ m : ℕ, m ≤ k + 1 →
    MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g

/-- Split a three-term integral. -/
theorem integral_three {s : Set ℝ} {A B C : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hC : MeasureTheory.IntegrableOn C s) :
    (∫ θ in s, (A θ + B θ + C θ)) = (∫ θ in s, A θ) + (∫ θ in s, B θ) + (∫ θ in s, C θ) := by
  rw [MeasureTheory.integral_add (f := fun θ => A θ + B θ) (g := C) (hA.add hB) hC,
    MeasureTheory.integral_add (f := A) (g := B) hA hB]

/-- The differentiated slice ODE, in the `v`-form: on `(0, π/2)`,
`u^{(k+2)} = ∂_θ^{k+1}(sin θ · v) - 6 u^{(k)} - g^{(k)}`. -/
theorem thm_odeV (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 2) u θ
        = iteratedDeriv (k + 1) (fun t => Real.sin t * (u t / Real.cos t)) θ
          - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ := by
  intro θ hθ
  have hode := Work.FTS.EllipticEst.remov.ang_ode_iterate k hu hg θ hθ
  have hev : (fun t => Real.tan t * u t)
      =ᶠ[𝓝 θ] fun t => Real.sin t * (u t / Real.cos t) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hθ] with t ht
    have hc : Real.cos t ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [Filter.EventuallyEq.iteratedDeriv_eq (k + 1) hev] at hode
  linarith

/-- **The pointwise bound of the `v`-slots against the `∂^{k+1}(sin θ v)`-slot.**  On `(0, π/2)`
one has `(∂_θ^{k+1}(sin θ · v))²·Q ≤ (4/3)·B²·(k+2)·Σ_{m ≤ k+1} (v^{(m)})²·Q` with
`B = Σ_{j ≤ k+1} C(k+1,j)`, for `Q ≥ 0`. -/
theorem thm_wBound (k : ℕ) {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ (k + 1) v (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {Q : ℝ} (hQ : 0 ≤ Q) :
    (iteratedDeriv (k + 1) (fun t => Real.sin t * v t) θ) ^ 2 * Q
      ≤ (4 / 3) * (∑ j ∈ Finset.range (k + 2), (((k + 1).choose j : ℕ) : ℝ)) ^ 2
          * ((k : ℝ) + 2)
          * (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 * Q) := by
  set B : ℝ := ∑ j ∈ Finset.range (k + 2), (((k + 1).choose j : ℕ) : ℝ) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hlei := Work.FTS.EllipticEst.remov.slice_ang_A_leibniz k v hv θ hθ
  -- Cauchy–Schwarz in the discrete form `(Σ|aᵢ|)² ≤ n Σ aᵢ²`
  have hCS : (∑ m ∈ Finset.range (k + 2), |iteratedDeriv m v θ|) ^ 2
      ≤ ((k : ℝ) + 2) * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 2))
      (f := fun m => |iteratedDeriv m v θ|) (α := ℝ)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_ofNat, sq_abs] at h
    exact h
  -- the binomial bound
  have hX2 : (iteratedDeriv (k + 1) (fun t => Real.sin t * v t) θ) ^ 2
      ≤ B ^ 2 * (((k : ℝ) + 2) * ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2) := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hlei 2
    rw [sq_abs, mul_pow] at h1
    have h2 := mul_le_mul_of_nonneg_left hCS (by positivity : (0 : ℝ) ≤ B ^ 2)
    linarith [h1, h2]
  have hsum_nn : 0 ≤ ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hmain : (iteratedDeriv (k + 1) (fun t => Real.sin t * v t) θ) ^ 2 * Q
      ≤ B ^ 2 * ((k : ℝ) + 2)
          * (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 * Q) := by
    have h := mul_le_mul_of_nonneg_right hX2 hQ
    rw [← Finset.sum_mul]
    nlinarith [h]
  have hfac : B ^ 2 * ((k : ℝ) + 2) ≤ (4 / 3) * B ^ 2 * ((k : ℝ) + 2) := by
    have h0 : 0 ≤ B ^ 2 * ((k : ℝ) + 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      positivity
    linarith
  have hsumQ_nn : 0 ≤ ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 * Q :=
    Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) hQ
  calc (iteratedDeriv (k + 1) (fun t => Real.sin t * v t) θ) ^ 2 * Q
      ≤ B ^ 2 * ((k : ℝ) + 2)
          * (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 * Q) := hmain
    _ ≤ (4 / 3) * B ^ 2 * ((k : ℝ) + 2)
          * (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 * Q) := by
        apply mul_le_mul_of_nonneg_right _ hsumQ_nn
        linarith [hfac]

/-- **The one-dimensional angular estimate** (the statement of `remov.slice_ang_gen`) from the
weighted `v`-bounds. -/
theorem genFinal (k : ℕ) (hk : 2 ≤ k) {CV : ℝ} (hV : VBound k CV) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  classical
  obtain ⟨hCVpos, hVb⟩ := hV
  set B : ℝ := ∑ j ∈ Finset.range (k + 2), (((k + 1).choose j : ℕ) : ℝ) with hBdef
  refine ⟨3 * ((4 / 3) * B ^ 2 * ((k : ℝ) + 2) * ((k : ℝ) + 2) * CV + 36 + 1) + 1,
    by positivity, ?_⟩
  intro γ u g hsh
  set v : ℝ → ℝ := fun t => u t / Real.cos t with hvdef
  set Q : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) with hQdef
  have hVB := fun m hm => hVb γ u g hsh m hm
  obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hInt_k2, hInt_gk, hInt_high, hInt_2, hInt_1,
    hInt_0⟩ := hsh
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : 0 < 2 * (k : ℝ) - γ := by linarith
  have hk2nn : (0 : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have hQnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Q θ := by
    intro θ hθ
    rw [hQdef]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hQnn' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ Q θ := fun θ hθ =>
    hQnn θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- smoothness of `v` and of `sin · v`
  have hvC : ContDiffOn ℝ (k + 2) v (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hvdef]
    exact hu.div Real.contDiff_cos.contDiffOn fun t ht =>
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hvC1 : ContDiffOn ℝ (k + 1) v (Set.Ioo 0 (Real.pi / 2)) :=
    hvC.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  -- the `v`-integrals
  have hvInt : ∀ m : ℕ, m ∈ Finset.range (k + 2) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m v θ) ^ 2 * Q θ) Work.Spaces.Iθ := by
    intro m hm
    have hm' : m ≤ k + 1 := by have := Finset.mem_range.mp hm; omega
    have h := (hVB m hm').1
    simpa only [hvdef, hQdef] using h
  have hvBnd : ∀ m : ℕ, m ∈ Finset.range (k + 2) →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m v θ) ^ 2 * Q θ)
        ≤ CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
    intro m hm
    have hm' : m ≤ k + 1 := by have := Finset.mem_range.mp hm; omega
    have h := (hVB m hm').2
    simpa only [hvdef, hQdef] using h
  set S : ℝ → ℝ := fun θ => ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m v θ) ^ 2 * Q θ
    with hSdef
  set X : ℝ → ℝ := fun θ => iteratedDeriv (k + 1) (fun t => Real.sin t * v t) θ with hXdef
  set C1 : ℝ := (4 / 3) * B ^ 2 * ((k : ℝ) + 2) with hC1def
  have hC1nn : 0 ≤ C1 := by rw [hC1def]; positivity
  have hS_int : MeasureTheory.IntegrableOn S Work.Spaces.Iθ := by
    rw [hSdef]
    exact MeasureTheory.integrable_finsetSum _ (fun m hm => hvInt m hm)
  -- the pointwise bound for the top slot
  have hpw : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (iteratedDeriv (k + 2) u θ) ^ 2 * Q θ
        ≤ 3 * (C1 * S θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
            + (iteratedDeriv k g θ) ^ 2 * Q θ) := by
    intro θ hθ
    have hQ := hQnn' θ hθ
    have hode := thm_odeV k hu hg θ hθ
    have h1 : (iteratedDeriv (k + 2) u θ) ^ 2 * Q θ
        ≤ 3 * (X θ ^ 2 * Q θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
            + (iteratedDeriv k g θ) ^ 2 * Q θ) := by
      have hbase : (iteratedDeriv (k + 2) u θ) ^ 2
          ≤ 3 * (X θ ^ 2 + 36 * (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2) := by
        rw [hode, hXdef]
        nlinarith [sq_nonneg (iteratedDeriv (k + 1) (fun t => Real.sin t * v t) θ
            + 3 * iteratedDeriv k u θ + iteratedDeriv k g θ / 2),
          sq_nonneg (3 * iteratedDeriv k u θ - iteratedDeriv k g θ / 2)]
      calc (iteratedDeriv (k + 2) u θ) ^ 2 * Q θ
          ≤ (3 * (X θ ^ 2 + 36 * (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2)) * Q θ :=
            mul_le_mul_of_nonneg_right hbase hQ
        _ = 3 * (X θ ^ 2 * Q θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
              + (iteratedDeriv k g θ) ^ 2 * Q θ) := by ring
    have h2 : X θ ^ 2 * Q θ ≤ C1 * S θ := by
      have h := thm_wBound k hvC1 hθ hQ
      rw [hXdef, hC1def, hSdef]
      exact h
    nlinarith [h1, h2]
  -- integrability of the right-hand side of `hpw`
  have hb2int : MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k u θ) ^ 2 * Q θ)
      Work.Spaces.Iθ := by
    obtain ⟨h1, -⟩ := Work.FTS.EllipticEst.remov.angSlot_le_AngRHS k hk γ u g hγ1 hγ2 hu hcont
      hInt_gk hInt_high hInt_2 hInt_1 hInt_0 k (by omega)
    simpa only [hQdef] using h1
  have hc2int : MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2 * Q θ)
      Work.Spaces.Iθ := by simpa only [hQdef] using hInt_gk
  have hR_int : MeasureTheory.IntegrableOn
      (fun θ => 3 * (C1 * S θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
          + (iteratedDeriv k g θ) ^ 2 * Q θ)) Work.Spaces.Iθ :=
    (((hS_int.const_mul C1).add (hb2int.const_mul 36)).add hc2int).const_mul 3
  -- compare the integrals
  have hcmp := MeasureTheory.integral_mono_ae
    (f := fun θ => (iteratedDeriv (k + 2) u θ) ^ 2 * Q θ)
    (g := fun θ => 3 * (C1 * S θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
        + (iteratedDeriv k g θ) ^ 2 * Q θ))
    (by rw [hQdef]; exact hInt_k2) hR_int
    (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (p := fun θ =>
      (iteratedDeriv (k + 2) u θ) ^ 2 * Q θ
        ≤ 3 * (C1 * S θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
            + (iteratedDeriv k g θ) ^ 2 * Q θ)) hpw)
  -- bound the right-hand side
  have hSval : (∫ θ in Work.Spaces.Iθ, S θ)
      = ∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
          (iteratedDeriv m v θ) ^ 2 * Q θ := by
    rw [hSdef]
    exact MeasureTheory.integral_finsetSum _ (fun m hm => hvInt m hm)
  have hSle : (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
        (iteratedDeriv m v θ) ^ 2 * Q θ)
      ≤ ((k : ℝ) + 2) * (CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
    have h1 : (∑ m ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
        (iteratedDeriv m v θ) ^ 2 * Q θ)
        ≤ ∑ _m ∈ Finset.range (k + 2),
            CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
      Finset.sum_le_sum fun m hm => hvBnd m hm
    have h2 : (∑ _m ∈ Finset.range (k + 2),
        CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g)
        = ((k : ℝ) + 2) * (CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    linarith [h1, h2.le]
  have hb2bnd : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2 * Q θ)
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
    obtain ⟨-, h2⟩ := Work.FTS.EllipticEst.remov.angSlot_le_AngRHS k hk γ u g hγ1 hγ2 hu hcont
      hInt_gk hInt_high hInt_2 hInt_1 hInt_0 k (by omega)
    simpa only [hQdef] using h2
  have hc2bnd : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2 * Q θ)
      ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
    have := Work.FTS.EllipticEst.remov.g_slot_le_angRHS k γ u g
    simpa only [hQdef] using this
  have hRnn : 0 ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
    Work.FTS.EllipticEst.remov.angRHS_nonneg k γ u g
  -- the value of the right-hand side integral
  have hRval : (∫ θ in Work.Spaces.Iθ, 3 * (C1 * S θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
        + (iteratedDeriv k g θ) ^ 2 * Q θ))
      = 3 * (C1 * (∫ θ in Work.Spaces.Iθ, S θ)
          + 36 * (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2 * Q θ)
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2 * Q θ)) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [integral_three (A := fun θ => C1 * S θ)
      (B := fun θ => 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ))
      (C := fun θ => (iteratedDeriv k g θ) ^ 2 * Q θ)
      (hS_int.const_mul C1) (hb2int.const_mul 36) hc2int,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the arithmetic
  have hRHSle : (∫ θ in Work.Spaces.Iθ, 3 * (C1 * S θ + 36 * ((iteratedDeriv k u θ) ^ 2 * Q θ)
        + (iteratedDeriv k g θ) ^ 2 * Q θ))
      ≤ 3 * (((4 / 3) * B ^ 2 * ((k : ℝ) + 2) * ((k : ℝ) + 2) * CV) + 36 + 1)
          * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
    rw [hRval]
    have hA : C1 * (∫ θ in Work.Spaces.Iθ, S θ)
        ≤ C1 * (((k : ℝ) + 2) * (CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g)) :=
      mul_le_mul_of_nonneg_left (by rw [hSval]; exact hSle) hC1nn
    have hB : 36 * (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2 * Q θ)
        ≤ 36 * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by linarith [hb2bnd]
    have hCc : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2 * Q θ)
        ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := hc2bnd
    have hAc : C1 * (((k : ℝ) + 2) * (CV * Work.FTS.EllipticEst.remov.AngRHS k γ u g))
        = ((4 / 3) * B ^ 2 * ((k : ℝ) + 2) * ((k : ℝ) + 2) * CV)
            * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
      rw [hC1def]; ring
    nlinarith [hA, hAc, hB, hCc, hRnn]
  have hfinal : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2 * Q θ)
      ≤ 3 * (((4 / 3) * B ^ 2 * ((k : ℝ) + 2) * ((k : ℝ) + 2) * CV) + 36 + 1)
          * Work.FTS.EllipticEst.remov.AngRHS k γ u g := le_trans hcmp hRHSle
  calc (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2 * Q θ) := by rw [hQdef]
    _ ≤ 3 * (((4 / 3) * B ^ 2 * ((k : ℝ) + 2) * ((k : ℝ) + 2) * CV) + 36 + 1)
          * Work.FTS.EllipticEst.remov.AngRHS k γ u g := hfinal
    _ ≤ (3 * ((4 / 3) * B ^ 2 * ((k : ℝ) + 2) * ((k : ℝ) + 2) * CV + 36 + 1) + 1)
          * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
        apply mul_le_mul_of_nonneg_right _ hRnn
        linarith

end Work.FTS.EllipticEst.Prop.Rtilde
