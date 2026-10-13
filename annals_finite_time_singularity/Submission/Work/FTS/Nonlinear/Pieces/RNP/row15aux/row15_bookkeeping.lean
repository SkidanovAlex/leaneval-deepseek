import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.HkIntegrand_le_of_mixed_bound
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gwt_integrableOn_and_integral_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.rlog_sq_integrableOn_and_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 15: the `H⁴`-bookkeeping for `N₂^{ss}`

The pointwise information available for `f = N₂^{ss}(α, Φ_s)` — a bound on
`|D_z^j D_θ^i f · w|` at those `z > 0` where the angular derivatives of the stream
function `U(Φ̃_s)` tend to `0` at `θ → 0⁺` — is integrated here to give the `H⁴`-bound

`HkSq α 4 f ≤ (10⁶ K (Cs+1))² α⁴`.

The two complementary hypotheses are used as follows.  For `z > 0` where the θ-slice
`HkIntegrand α 4 f z ·` is **integrable** on `Iθ`, the contrapositive of `hbad` supplies
the vanishing of the angular derivatives, hence `hU` gives the pointwise bound and
`HkIntegrand_le_of_mixed_bound` turns it into `HkIntegrand α 4 f z θ ≤ C rlog(z)² Gwt α θ`,
whose θ-integral is `≤ 2000 C rlog(z)²/α` (`Gwt_integrableOn_and_integral_le`).  At the
`z` where the slice is **not** integrable, the slice integral is `0` by Mathlib's
convention for the Bochner integral of a non-integrable function, so the bound holds
there too.  Integrating in `z` with `∫_0^∞ rlog² ≤ 100`
(`rlog_sq_integrableOn_and_integral_le`) gives `HkSq ≤ 2·10⁵ K²(Cs+1)²α⁵`, and
`α ≤ 1` upgrades this to `10¹²K²(Cs+1)²α⁴`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

theorem row15_bookkeeping {α Cs K : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 < K) (hCs : 0 ≤ Cs)
    (hU : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
        ∀ θ ∈ Work.Spaces.Iθ, ∀ i j : ℕ, i + j ≤ 4 →
          |Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z θ * Work.Spaces.w z|
            ≤ K * α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ * ((1 + Real.log (1 + z)) / (1 + z)))
    (hbad : ∀ z ∈ Set.Ioi (0 : ℝ),
        ¬(∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
        ¬MeasureTheory.IntegrableOn
          (fun θ => Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ)
          Work.Spaces.Iθ) :
    Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N2ss α Φs)
      ≤ (1000000 * K * (Cs + 1)) ^ 2 * α ^ 4 := by
  obtain ⟨hGwtInt, hGwtVal⟩ := Gwt_integrableOn_and_integral_le (α := α) hα hα1
  obtain ⟨hrlogInt, hrlogVal⟩ := rlog_sq_integrableOn_and_integral_le
  set f : ℝ → ℝ → ℝ := Work.FTS.Nonlin.N2ss α Φs with hf
  have hα0 : 0 ≤ α := le_of_lt hα
  -- the constant `P` of the pointwise bound
  set P : ℝ := K * α ^ 3 * (Cs + 1) with hP
  have hP2 : 0 ≤ P ^ 2 := sq_nonneg _
  have h2000 : 0 ≤ 2000 / α := by positivity
  -- ## Step 1: the θ-slice bound, for every `z ∈ [0,∞)`
  have hkey : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ P ^ 2 * (rlog z) ^ 2 * (2000 / α) := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases lt_or_eq_of_le hz' with hzpos | hz0
    · by_cases hInt : MeasureTheory.IntegrableOn
          (fun θ => Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iθ
      · -- the slice is integrable: `hbad` gives the good `z`, `hU` the pointwise bound
        have hgood : ∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
          by_contra hb
          exact hbad z hzpos hb hInt
        have hpt := hU z hzpos hgood
        have hpt' : ∀ θ ∈ Work.Spaces.Iθ, ∀ i j : ℕ, i + j ≤ 4 →
            |Work.Spaces.mixed j i f z θ * Work.Spaces.w z|
              ≤ K * α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ * rlog z :=
          fun θ hθ i j hij => hpt θ hθ i j hij
        have hptwise : ∀ θ ∈ Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 f z θ ≤ (P ^ 2 * (rlog z) ^ 2) * Gwt α θ :=
          fun θ hθ => HkIntegrand_le_of_mixed_bound (f := f) hα hK hCs hzpos hpt' θ hθ
        have hIntMaj : MeasureTheory.Integrable
            (fun θ => (P ^ 2 * (rlog z) ^ 2) * Gwt α θ)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          hGwtInt.const_mul _
        have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
            (fun θ => Work.Spaces.HkIntegrand α 4 f z θ) :=
          Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
        have hle_ae : (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
            ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
            (fun θ => (P ^ 2 * (rlog z) ^ 2) * Gwt α θ) := by
          filter_upwards [MeasureTheory.ae_restrict_mem
            (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
          exact hptwise θ hθ
        calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            ≤ ∫ θ in Work.Spaces.Iθ, (P ^ 2 * (rlog z) ^ 2) * Gwt α θ :=
              MeasureTheory.integral_mono_of_nonneg hnn hIntMaj hle_ae
          _ = (P ^ 2 * (rlog z) ^ 2) * ∫ θ in Work.Spaces.Iθ, Gwt α θ :=
              MeasureTheory.integral_const_mul _ _
          _ ≤ (P ^ 2 * (rlog z) ^ 2) * (2000 / α) :=
              mul_le_mul_of_nonneg_left hGwtVal (mul_nonneg hP2 (sq_nonneg _))
          _ = P ^ 2 * (rlog z) ^ 2 * (2000 / α) := by ring
      · -- the slice is not integrable: the slice integral is `0` by convention
        have hInt' : ¬ MeasureTheory.Integrable
            (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hInt
        rw [MeasureTheory.integral_undef hInt']
        exact mul_nonneg (mul_nonneg hP2 (sq_nonneg _)) h2000
    · -- `z = 0`: the weight `w 0 = 0` kills every term of the integrand
      rw [← hz0]
      have hzero : ∀ θ : ℝ, Work.Spaces.HkIntegrand α 4 f 0 θ = 0 := by
        intro θ
        simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
      simp only [hzero, integral_zero]
      exact mul_nonneg (mul_nonneg hP2 (sq_nonneg _)) h2000
  -- ## Step 2: integrate the slice bound over `z`
  have hIntA : MeasureTheory.Integrable
      (fun z => (P ^ 2 * (2000 / α)) * (rlog z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hrlogInt.const_mul _
  have hnn2 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
    Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hle2 : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (P ^ 2 * (2000 / α)) * (rlog z) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ P ^ 2 * (rlog z) ^ 2 * (2000 / α) := hkey z hz
      _ = (P ^ 2 * (2000 / α)) * (rlog z) ^ 2 := by ring
  have hmain := MeasureTheory.integral_mono_of_nonneg hnn2 hIntA hle2
  have hval2 : ∫ z in Work.Spaces.Iz, (P ^ 2 * (2000 / α)) * (rlog z) ^ 2
      = (P ^ 2 * (2000 / α)) * ∫ z in Work.Spaces.Iz, (rlog z) ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      ≤ (1000000 * K * (Cs + 1)) ^ 2 * α ^ 4
  refine le_trans hmain ?_
  rw [hval2]
  refine le_trans (mul_le_mul_of_nonneg_left hrlogVal (mul_nonneg hP2 h2000)) ?_
  -- ## Step 3: the arithmetic
  have hpow : α ^ 5 ≤ α ^ 4 := by
    rw [show α ^ 5 = α ^ 4 * α by ring]
    exact mul_le_of_le_one_right (pow_nonneg hα0 4) hα1
  have key : (P ^ 2 * (2000 / α)) * 100 = 200000 * (K * (Cs + 1)) ^ 2 * α ^ 5 := by
    rw [hP]
    field_simp
    ring
  have key2 : (1000000 * K * (Cs + 1)) ^ 2 * α ^ 4
      = 1000000000000 * (K * (Cs + 1)) ^ 2 * α ^ 4 := by ring
  rw [key, key2]
  have hX : 0 ≤ (K * (Cs + 1)) ^ 2 := sq_nonneg _
  have hstep : (K * (Cs + 1)) ^ 2 * α ^ 5 ≤ (K * (Cs + 1)) ^ 2 * α ^ 4 :=
    mul_le_mul_of_nonneg_left hpow hX
  nlinarith [hstep, hX, hα0, mul_nonneg hX (pow_nonneg hα0 4)]

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
