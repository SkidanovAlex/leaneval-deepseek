import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal ContDiff FourierTransform

namespace Work.BoseBox

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The crude a.e. bound `wScaled s (g₀) ≤ 2·g₀`** in the dilute regime
`R ≤ s·chiR0`: only the elementary bound `(χ⋆χ) ≥ 1/2` on `ball 0 R` is used
(`KernelMean.wScaled_abs_le_two`), not the Taylor expansion. -/
private lemma wScaled_g0_le_two_ae {v : ℝ³ → ℝ} {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (h : Work.UBB.ScatSol v)
    (hsR : R ≤ s * Submission.BoseGases.chiR0) :
    ∀ᵐ x : ℝ³, Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x ≤
      (1 + 1) * Submission.BoseGases.g0 v h x := by
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  filter_upwards [Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h] with x hx
  have h2 := Submission.BoseGases.wScaled_abs_le_two hs (le_of_lt hR) hsR hgsupp x
  have h3 : |Submission.BoseGases.g0 v h x| = Submission.BoseGases.g0 v h x := abs_of_nonneg hx
  calc Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x
      ≤ |Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x| := le_abs_self _
    _ ≤ 2 * |Submission.BoseGases.g0 v h x| := h2
    _ = (1 + 1) * Submission.BoseGases.g0 v h x := by rw [h3]; ring

/-- **The Newton-identity data of the chosen scattering solution.**

For the corpus's scattering solution `w₀ = Classical.choose h` and `g₀ = v(1−w₀)` (so
`−Δw₀ = g₀/2` weakly and `w₀ → 0` at ∞), the renormalised kernel `wScaled s (g₀) = g₀/convScale s`
satisfies, uniformly for all `s > 0` with `R ≤ s·chiR0`, the x-space finiteness and FS's
Newton/mass bound (his `eq:WSestimate`, the `M1` input of `lm:appbogolubov`):

  `(2π)⁻³∫_q |𝓕(wScaled s (g₀))((2π)⁻¹•q)|²/‖q‖² dq ≤ 2(1+6·Ct·(R/s)²)·g0w0Mass h`

for a fixed `Ct ≥ 0` (the `C²`-bound of `χ⋆χ − 1` near 0), together with the integrability of
`(x,y) ↦ W₁(x)W₁(y)/‖x−y‖` (the `hWfin` field of `diagW_lm_appbogolubov_explicitC`).  The pure
`g₀` case is the Newton identity `(2π)⁻³∫|ĝ₀(q)|²/‖q‖²dq = 2·∫g₀w₀ = 2·g0w0Mass` (equivalent to
`∫∫g₀(x)g₀(y)/|x−y| = 8π∫g₀w₀`, from `−Δw₀ = g₀/2` and `w₀(x) = (8π)⁻¹∫g₀(y)/|x−y|dy`), and the
`convScale` factor is `1 + O(Ct‖z/s‖²)` on `supp g₀ ⊆ ball 0 R` with `R ≤ s·chiR0` (so
`1/convScale ≤ 2` there).  Local inputs: the Newton representation `NewtonRep`,
`chiR0_half`, and the `conv3` Taylor bound near 0. -/
theorem q3NewtonData {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ s : ℝ, 0 < s → R ≤ s * Submission.BoseGases.chiR0 →
      MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
          Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) q.1 *
            Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) q.2 * (‖q.1 - q.2‖)⁻¹)
      ∧ (1 / (2 * Real.pi) ^ 3) * ∫ q : ℝ³,
          ((FourierTransform.fourier (fun x : ℝ³ =>
              (Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x : ℂ))
            ((1 / (2 * Real.pi)) • q)).re) ^ 2 / ‖q‖ ^ 2
        ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * Submission.BoseGases.g0w0Mass (v := v) h := by
  -- the second-order Taylor data of `χ⋆χ` at the origin
  obtain ⟨C₀, hC₀0, r₁, hr₁, hT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  refine ⟨max C₀ (1 / (2 * r₁ ^ 2)), le_trans hC₀0 (le_max_left _ _), ?_⟩
  intro s hs hsR
  have hG0 : ∀ᵐ x : ℝ³, 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hGsupp : ∀ x : ℝ³, R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
    fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  have hmass : 0 ≤ Submission.BoseGases.g0w0Mass (v := v) h :=
    Submission.BoseGases.g0w0Mass_nonneg hR hv_nonneg hvrad hv_supp h
  have hD0 : (0 : ℝ) ≤ ∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z := by
    simpa [Submission.BoseGases.g0w0Mass] using hmass
  -- the x-space pair kernel of `g₀` is integrable (Newton representation + Tonelli)
  have hGjoint : MeasureTheory.Integrable (fun p : ℝ³ × ℝ³ =>
      Submission.BoseGases.g0 v h p.1 * Submission.BoseGases.g0 v h p.2 *
        (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    Work.MGroupInput.newtonianSharp_integrable_double_coulPot hR
      (Submission.BoseGases.g0_integrable hR hv_supp h) hG0 hGsupp
      (Work.MGroupInput.newtonianSharp_g0_coulPot_integrable hR hv_nonneg hvrad hv_supp h)
  -- the target's momentum integral, written with `pairW`
  have hLHS : ∀ W : ℝ³ → ℝ,
      (1 / (2 * Real.pi) ^ 3) * ∫ q : ℝ³,
          ((FourierTransform.fourier (fun x : ℝ³ => (W x : ℂ))
            ((1 / (2 * Real.pi)) • q)).re) ^ 2 / ‖q‖ ^ 2
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2 := by
    intro W
    have hfun : (fun q : ℝ³ =>
          ((FourierTransform.fourier (fun x : ℝ³ => (W x : ℂ))
            ((1 / (2 * Real.pi)) • q)).re) ^ 2 / ‖q‖ ^ 2)
        = fun q : ℝ³ => (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2 := by
      funext q
      rw [Submission.BoseGases.pairW_eq_cfourier_re]
      simp only [one_div, Submission.BoseGases.cfourier]
    rw [hfun, one_div]
  have hW0 : ∀ᵐ x : ℝ³, 0 ≤ Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x := by
    filter_upwards [hG0] with x hx
    rw [Submission.BoseGases.wScaled]
    exact div_nonneg hx (Submission.BoseGases.convScale_nonneg s x)
  by_cases hcase : R / s ≤ r₁ ∧ C₀ * (R / s) ^ 2 ≤ 1 / 2
  · -- **the refined branch**: the Taylor sandwich gives `W₁ ≤ (1+δ)g₀` with `δ = 2C₀(R/s)²`
    obtain ⟨hreg, hcond⟩ := hcase
    have hδ0 : 0 ≤ 2 * C₀ * (R / s) ^ 2 := by positivity
    have hsharp : ∀ᵐ x : ℝ³,
        Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x ≤
          (1 + 2 * C₀ * (R / s) ^ 2) * Submission.BoseGases.g0 v h x := by
      have hb := Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R) (ℓ := s)
        (r₁ := r₁) (C := C₀) hR hv_nonneg hvrad hv_supp h hC₀0 hr₁ hT hs hreg hcond
      filter_upwards [hb] with x hx
      calc Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x
          ≤ Submission.BoseGases.g0 v h x +
              2 * C₀ * (R / s) ^ 2 * Submission.BoseGases.g0 v h x := by linarith [hx.2]
        _ = (1 + 2 * C₀ * (R / s) ^ 2) * Submission.BoseGases.g0 v h x := by ring
    have hWint : MeasureTheory.Integrable
        (Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h)) :=
      Work.MGroupInput.integrable_wScaled_g0_of_sharp hs hR hv_nonneg hvrad hv_supp h hδ0 hsharp
    refine ⟨Work.MGroupInput.newtonianSharp_integrable_double_of_sharp hδ0 hWint hW0 hsharp
      hGjoint, ?_⟩
    have hns := Work.MGroupInput.newtonianSharp (s := s) (δ := 2 * C₀ * (R / s) ^ 2) hs hδ0
      hR hv_nonneg hvrad hv_supp h hsharp
    have hcoef : 2 * (1 + 2 * C₀ * (R / s) ^ 2) ^ 2
        ≤ 2 * (1 + 6 * max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) := by
      have hδle : 2 * C₀ * (R / s) ^ 2 ≤ 1 := by linarith
      have hδsq : (2 * C₀ * (R / s) ^ 2) ^ 2 ≤ 2 * C₀ * (R / s) ^ 2 := by
        nlinarith [hδ0, hδle]
      have hmono : C₀ * (R / s) ^ 2 ≤ max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      linarith
    have hgoal : 2 * (1 + 2 * C₀ * (R / s) ^ 2) ^ 2 *
          (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z)
        ≤ 2 * (1 + 6 * max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) *
            Submission.BoseGases.g0w0Mass (v := v) h := by
      have h := mul_le_mul_of_nonneg_right hcoef hD0
      simpa [Submission.BoseGases.g0w0Mass] using h
    rw [hLHS]
    calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          (Submission.BoseGases.pairW
            (Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h)) q) ^ 2 / ‖q‖ ^ 2
        ≤ 2 * (1 + 2 * C₀ * (R / s) ^ 2) ^ 2 *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z) := hns.2
      _ ≤ 2 * (1 + 6 * max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) *
            Submission.BoseGases.g0w0Mass (v := v) h := hgoal
  · -- **the crude branch**: only `W₁ ≤ 2g₀` is available
    have hδ0 : (0 : ℝ) ≤ 1 := zero_le_one
    have hsharp : ∀ᵐ x : ℝ³,
        Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x ≤
          (1 + 1) * Submission.BoseGases.g0 v h x :=
      wScaled_g0_le_two_ae hR hs hv_nonneg hvrad hv_supp h hsR
    have hWint : MeasureTheory.Integrable
        (Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h)) :=
      Work.MGroupInput.integrable_wScaled_g0_of_sharp hs hR hv_nonneg hvrad hv_supp h hδ0 hsharp
    refine ⟨Work.MGroupInput.newtonianSharp_integrable_double_of_sharp hδ0 hWint hW0 hsharp
      hGjoint, ?_⟩
    have hns := Work.MGroupInput.newtonianSharp (s := s) (δ := 1) hs hδ0
      hR hv_nonneg hvrad hv_supp h hsharp
    -- in this branch `Ct·(R/s)² ≥ 1/2`
    have hkey : (1 : ℝ) / 2 ≤ max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2 := by
      by_cases hlt : r₁ < R / s
      · have h1 : (1 / (2 * r₁ ^ 2)) * r₁ ^ 2 ≤ max C₀ (1 / (2 * r₁ ^ 2)) * r₁ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg r₁)
        have h2 : (1 / (2 * r₁ ^ 2)) * r₁ ^ 2 = 1 / 2 := by
          field_simp
        have h3 : r₁ ^ 2 ≤ (R / s) ^ 2 := by nlinarith [hr₁, hlt]
        have h4 : max C₀ (1 / (2 * r₁ ^ 2)) * r₁ ^ 2
            ≤ max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (le_trans hC₀0 (le_max_left _ _))
        linarith
      · have hle : R / s ≤ r₁ := le_of_not_gt hlt
        have hsecond : 1 / 2 < C₀ * (R / s) ^ 2 := by
          by_contra hc
          exact hcase ⟨hle, le_of_not_gt hc⟩
        exact le_trans (le_of_lt hsecond)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    have harith : (8 : ℝ) * (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z)
        ≤ 2 * (1 + 6 * max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) *
            Submission.BoseGases.g0w0Mass (v := v) h := by
      have h4 : (4 : ℝ) ≤ 1 + 6 * (max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) := by
        linarith [hkey]
      have hstep : (4 : ℝ) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z)
          ≤ (1 + 6 * (max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2)) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z) :=
        mul_le_mul_of_nonneg_right h4 hD0
      have htwo : (2 : ℝ) * ((4 : ℝ) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z))
          ≤ 2 * ((1 + 6 * (max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2)) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z)) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
      have hrew : 2 * ((1 + 6 * (max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2)) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z))
          = 2 * (1 + 6 * max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z) := by ring
      rw [hrew] at htwo
      have hmain : (8 : ℝ) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z)
          ≤ 2 * (1 + 6 * max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z) := by
        nlinarith [htwo]
      simpa [Submission.BoseGases.g0w0Mass] using hmain
    rw [hLHS]
    calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          (Submission.BoseGases.pairW
            (Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h)) q) ^ 2 / ‖q‖ ^ 2
        ≤ 2 * (1 + 1) ^ 2 *
            (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z) := hns.2
      _ = 8 * (∫ z : ℝ³, Submission.BoseGases.g0 v h z * Classical.choose h z) := by ring
      _ ≤ 2 * (1 + 6 * max C₀ (1 / (2 * r₁ ^ 2)) * (R / s) ^ 2) *
            Submission.BoseGases.g0w0Mass (v := v) h := harith

end Work.BoseBox
