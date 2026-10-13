/-
# Helpers for the level-six `T1` slot term (`t1SlotTermZ`)

This module collects the elementary slot facts used by
`Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ`:

* `canonW_le_int` — monotonicity of the canonical weight `canonW q = w² sin(2·)^{-q}` in the
  exponent `q`, on the *open* angular interval (so that it also covers `q = 0`, where the
  endpoint values of `sin(2·)^{-q}` are junk);
* `canonW_mul_z_le_int`, `canonW_mul_mixed_le_int` — the pointwise domination of a
  `canonW q`-weighted slot square by the `ℋ⁶`-integrand, on the open angular interval and
  for `0 ≤ q ≤ η` (pure `D_z`-slots) resp. `q ≤ γ` (mixed slots);
* `canonW_abs_mul_le_sqrt_pair` — the AM–GM pairing of two such slots;
* `slotTriple_iterated` — the wrapper that converts a pointwise bound
  `canonW q · |X| · |Y| · |Z| ≤ M √(HkIntegrand h₁) √(HkIntegrand h₂)` (one sup-bounded factor
  and two slots) into the iterated-integral statement, together with the integrability of the
  radial marginal.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SlotZ

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_eta_eq canonW_gam_eq
  canonW_mono)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## An a.e.-conversion for the angular interval -/

/-- A property holding at every interior angle holds a.e. on `Iθ`. -/
theorem ae_Iθ_of_forall_Ioo {P : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), P θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), P θ := by
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-! ## Monotonicity of `canonW` in the exponent, on the open interval -/

theorem canonW_le_int {q q' z θ : ℝ} (hqq : q ≤ q')
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    canonW q z θ ≤ canonW q' z θ := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h : Real.sin (2 * θ) ^ (-q) ≤ Real.sin (2 * θ) ^ (-q') :=
    Real.rpow_le_rpow_of_exponent_ge (y := -q) (z := -q') hσ hσ1 (by linarith)
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-! ## The pointwise slot dominations on the open interval -/

theorem canonW_mul_z_le_int {α q : ℝ} {h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hq : q ≤ Work.Spaces.eta) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (j : ℕ) (hj : j ≤ 6) :
    canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have h1 : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθI]
    exact canonW_le_int hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (Work.Spaces.DzIter j h z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 h z θ j hj

theorem canonW_mul_mixed_le_int {α q : ℝ} {h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hqγ : q ≤ Work.Spaces.gam α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 6) :
    canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have h1 : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθI]
    exact canonW_le_int hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 h z θ i j hi hij

/-! ## The AM–GM pairing of two slots -/

theorem canonW_abs_mul_le_sqrt_pair {α q : ℝ} {X Y h₁ h₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hX : canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₁ z θ)
    (hY : canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₂ z θ) :
    canonW q z θ * |X z θ| * |Y z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 6 h₁ z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 h₂ z θ) := by
  have hc : 0 ≤ canonW q z θ := canonW_nonneg ⟨hθ.1.le, hθ.2.le⟩
  have hre : (Real.sqrt (canonW q z θ) * |X z θ|) * (Real.sqrt (canonW q z θ) * |Y z θ|)
      = (Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ)) * (|X z θ| * |Y z θ|) := by
    ring
  calc canonW q z θ * |X z θ| * |Y z θ|
      = (Real.sqrt (canonW q z θ) * |X z θ|) * (Real.sqrt (canonW q z θ) * |Y z θ|) := by
        rw [hre, Real.mul_self_sqrt hc]
        ring
    _ = Real.sqrt (canonW q z θ * (X z θ) ^ 2)
          * Real.sqrt (canonW q z θ * (Y z θ) ^ 2) := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 6 h₁ z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 h₂ z θ) :=
        mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## The three-factor slot bound: sup-bounded factor times two slots -/

/-- **The three-factor slot bound.**  If `X` is bounded pointwise by `M` on the open quadrant
and the `canonW q`-weighted squares of `Y`, `Z` are dominated pointwise by the `ℋ⁶`-integrands
of `h₁`, `h₂`, then the iterated integral of `canonW q |X||Y||Z|` converges and is at most
`M √(HkSq α 6 h₁) √(HkSq α 6 h₂)`.

The proof runs through the product measure `pm`: the pointwise majorant
`M √(HkIntegrand h₁) √(HkIntegrand h₂)` with `M` pulled out is integrated by Hölder
(`SixAux.integrable_of_pointwise_sqrt`), and the product integral is converted back to the
iterated one by Fubini. -/
theorem slotTriple_core {α q M : ℝ} (hM : 0 ≤ M)
    {X Y Z h₁ h₂ : ℝ → ℝ → ℝ}
    (hs1 : Work.FTS.EllipticEst.SmoothOpen h₁) (hs2 : Work.FTS.EllipticEst.SmoothOpen h₂)
    (hm1 : Work.Spaces.HkMem α 6 h₁) (hm2 : Work.Spaces.HkMem α 6 h₂)
    (hae : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |X p.1 p.2| * |Y p.1 p.2| * |Z p.1 p.2|)
      Work.FTS.StrongPersist.N6Trans.SixAux.pm)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
        ≤ M * (Real.sqrt (Work.Spaces.HkIntegrand α 6 h₁ z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 h₂ z θ))) :
    MeasureTheory.IntegrableOn (fun z =>
        ∫ θ in Work.Spaces.Iθ, canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|)
      ≤ M * (Real.sqrt (Work.Spaces.HkSq α 6 h₁) * Real.sqrt (Work.Spaces.HkSq α 6 h₂)) := by
  obtain ⟨hInt, hle⟩ := Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise_sqrt
    (F := fun z θ => canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|) hs1 hs2 hm1 hm2 hM hae
    (fun z θ hz hθ hθ2 => by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (canonW_nonneg ⟨hθ.le, hθ2.le⟩) (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _))]
      exact hpt z θ hz hθ hθ2)
  let S : ℝ → ℝ → ℝ := fun z θ => canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
  have hInt' : MeasureTheory.Integrable (fun p : ℝ × ℝ => S p.1 p.2)
      Work.FTS.StrongPersist.N6Trans.SixAux.pm := hInt
  have hmarg : (fun z : ℝ => ∫ θ, ‖S z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = fun z : ℝ => ∫ θ, S z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    funext z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_Iθ_of_forall_Ioo
      (P := fun θ => 0 ≤ canonW q z θ) (fun θ hθ => canonW_nonneg ⟨hθ.1.le, hθ.2.le⟩)] with θ hθ
    have : S z θ = canonW q z θ * |X z θ| * |Y z θ| * |Z z θ| := rfl
    rw [this, Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hθ (abs_nonneg _))
      (abs_nonneg _)) (abs_nonneg _))]
  constructor
  · have hfub := (MeasureTheory.integrable_prod_iff hae).mp hInt'
    rw [hmarg] at hfub
    exact hfub.2
  · have hfub2 : (∫ z, ∫ θ, S z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = ∫ p, S p.1 p.2 ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      MeasureTheory.integral_integral hInt'
    change (∫ z, ∫ θ, S z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) ≤ _
    rw [hfub2]
    exact hle

/-! ## The three-factor slot bound with a sup-bounded factor -/

/-- **The three-factor slot bound, `sup` on the first factor.**  `X` is bounded pointwise by
`M` and the `canonW q`-weighted squares of `Y`, `Z` are dominated by the `ℋ⁶`-integrands of
`h₁`, `h₂`; then the iterated integral of `canonW q |X||Y||Z|` converges and is at most
`M √(HkSq α 6 h₁) √(HkSq α 6 h₂)`. -/
theorem slotTripleFirst {α q M : ℝ} (hM : 0 ≤ M)
    {X Y Z h₁ h₂ : ℝ → ℝ → ℝ}
    (hs1 : Work.FTS.EllipticEst.SmoothOpen h₁) (hs2 : Work.FTS.EllipticEst.SmoothOpen h₂)
    (hm1 : Work.Spaces.HkMem α 6 h₁) (hm2 : Work.Spaces.HkMem α 6 h₂)
    (hae : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |X p.1 p.2| * |Y p.1 p.2| * |Z p.1 p.2|)
      Work.FTS.StrongPersist.N6Trans.SixAux.pm)
    (hsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |X z θ| ≤ M)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₁ z θ)
    (hZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Z z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₂ z θ) :
    MeasureTheory.IntegrableOn (fun z =>
        ∫ θ in Work.Spaces.Iθ, canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|)
      ≤ M * (Real.sqrt (Work.Spaces.HkSq α 6 h₁) * Real.sqrt (Work.Spaces.HkSq α 6 h₂)) := by
  refine slotTriple_core (α := α) (q := q) (M := M) hM hs1 hs2 hm1 hm2 hae
    (fun z θ hz hθ hθ2 => ?_)
  have hpair := canonW_abs_mul_le_sqrt_pair (α := α) (q := q) (X := Y) (Y := Z)
    (h₁ := h₁) (h₂ := h₂) ⟨hθ, hθ2⟩ (hY z θ hz hθ hθ2) (hZ z θ hz hθ hθ2)
  calc canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
      = (canonW q z θ * |Y z θ| * |Z z θ|) * |X z θ| := by ring
    _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 h₁ z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 h₂ z θ)) * M :=
        mul_le_mul hpair (hsup z θ hz hθ hθ2) (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = M * (Real.sqrt (Work.Spaces.HkIntegrand α 6 h₁ z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 h₂ z θ)) := by ring

/-- **The three-factor slot bound, `sup` on the middle factor.**  Same as `slotTripleFirst`
with the sup hypothesis on `Y` and the slot dominations on `X`, `Z`. -/
theorem slotTripleMid {α q M : ℝ} (hM : 0 ≤ M)
    {X Y Z h₁ h₂ : ℝ → ℝ → ℝ}
    (hs1 : Work.FTS.EllipticEst.SmoothOpen h₁) (hs2 : Work.FTS.EllipticEst.SmoothOpen h₂)
    (hm1 : Work.Spaces.HkMem α 6 h₁) (hm2 : Work.Spaces.HkMem α 6 h₂)
    (hae : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |X p.1 p.2| * |Y p.1 p.2| * |Z p.1 p.2|)
      Work.FTS.StrongPersist.N6Trans.SixAux.pm)
    (hsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Y z θ| ≤ M)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₁ z θ)
    (hZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Z z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₂ z θ) :
    MeasureTheory.IntegrableOn (fun z =>
        ∫ θ in Work.Spaces.Iθ, canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|)
      ≤ M * (Real.sqrt (Work.Spaces.HkSq α 6 h₁) * Real.sqrt (Work.Spaces.HkSq α 6 h₂)) := by
  refine slotTriple_core (α := α) (q := q) (M := M) hM hs1 hs2 hm1 hm2 hae
    (fun z θ hz hθ hθ2 => ?_)
  have hpair := canonW_abs_mul_le_sqrt_pair (α := α) (q := q) (X := X) (Y := Z)
    (h₁ := h₁) (h₂ := h₂) ⟨hθ, hθ2⟩ (hX z θ hz hθ hθ2) (hZ z θ hz hθ hθ2)
  calc canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
      = (canonW q z θ * |X z θ| * |Z z θ|) * |Y z θ| := by ring
    _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 h₁ z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 h₂ z θ)) * M :=
        mul_le_mul hpair (hsup z θ hz hθ hθ2) (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = M * (Real.sqrt (Work.Spaces.HkIntegrand α 6 h₁ z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 h₂ z θ)) := by ring

end Work.FTS.StrongPersist.N6Trans.T1SlotZ
