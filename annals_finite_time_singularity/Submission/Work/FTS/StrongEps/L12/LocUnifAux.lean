/-
# `L12_tendsto_locUnif` — the auxiliary estimates

Auxiliary objects and elementary estimates for the proof of
`Work.FTS.StrongEps.L12.L12_tendsto_locUnif`:

* `radMarg α D = ∫_θ HkIntegrand α 0 D · θ` — the radial marginal of the `ℋ⁰`-integrand (with
  `HkSq α 0 D = ∫_s radMarg α D s` definitionally);
* `angKSw = ∫_θ K θ · Sw θ` and `angEnd ε = ∫_{Iθ ∖ Icc ε (π/2-ε)} (K θ Sw θ)²` — the two angular
  constants of the split bound;
* `integrableOn_Wlam_sq`, `integrableOn_Wlam_mul_sqrt` — the radial integrability facts;
* `exists_delta_small`, `exists_R_large`, `exists_eps_small` — the three "choose the parameter
  small/large" lemmas used in the final `ε`-argument (the existence of a small `δ`, a large `R` and
  a small angular cut `ε`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.L12AbsLe
import Submission.Work.FTS.StrongEps.L12.L12_z_lipschitz
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Auxiliary objects -/

/-- The radial marginal `s ↦ ∫_θ HkIntegrand α 0 D s θ` of the `ℋ⁰`-integrand. -/
def radMarg (α : ℝ) (D : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 D s θ

lemma radMarg_nonneg (α : ℝ) (D : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ radMarg α D s :=
  integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 D s θ

lemma HkSq_zero_eq (α : ℝ) (D : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 D = ∫ s in Work.Spaces.Iz, radMarg α D s := by
  simp only [Work.Spaces.HkSq, radMarg]

/-- `∫_{θ ∈ Iθ} K θ · Sw θ`. -/
def angKSw : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ

/-- `∫_{θ ∈ Iθ ∖ Icc ε (π/2-ε)} (K θ · Sw θ)²`. -/
def angEnd (ε : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ \ Set.Icc ε (Real.pi / 2 - ε),
    (Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ) ^ 2

lemma angKSw_nonneg : 0 ≤ angKSw := by
  rw [angKSw]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ)
      (Work.FTS.GalBasis.cc.Sw_nonneg_of_mem_Iθ hθ))

lemma angEnd_nonneg (ε : ℝ) : 0 ≤ angEnd ε := by
  rw [angEnd]
  exact MeasureTheory.setIntegral_nonneg (measurableSet_Icc.diff measurableSet_Icc)
    (fun θ _ => sq_nonneg _)

/-! ## Elementary estimates for `Wlam` -/

lemma continuousOn_Wlam : ContinuousOn (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s) (Set.Ioi 0) := by
  rw [show Work.FTS.GalBasis.cc.Wlam = fun s : ℝ => s / (1 + s) ^ 2 from rfl]
  refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
  intro s hs
  have hs' : (0 : ℝ) < s := hs
  exact pow_ne_zero 2 (by linarith)

lemma integrableOn_Wlam_sq :
    MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi 0) := by
  have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_one_add_sq_inv 0 le_rfl
  refine h1.mono' ?_ ?_
  · exact (continuousOn_Wlam.pow 2).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Wlam_sq_le_inv_sq s (le_of_lt hs)

lemma integrableOn_Wlam_mul_sqrt {H : ℝ → ℝ} (hHnn : ∀ s, 0 ≤ H s)
    (hHint : MeasureTheory.IntegrableOn H (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s))
      (Set.Ioi 0) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun s => (Work.FTS.GalBasis.cc.Wlam s ^ 2 + H s) / 2) (Set.Ioi 0) :=
    (integrableOn_Wlam_sq.add hHint).div_const 2
  refine hmaj.mono' ?_ ?_
  · exact ((continuousOn_Wlam.aestronglyMeasurable (μ := volume) measurableSet_Ioi).mul
      (hHint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable)
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hWnn : 0 ≤ Work.FTS.GalBasis.cc.Wlam s := Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt hs)
    have hH0 : 0 ≤ Real.sqrt (H s) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hWnn hH0)]
    nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - Real.sqrt (H s)),
      Real.sq_sqrt (hHnn s), hWnn, hH0]

/-! ## The choice lemmas -/

lemma exists_delta_small {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ K * Real.sqrt δ < η := by
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨(min 1 (η / (K + 1))) ^ 2, by positivity, ?_, ?_⟩
  · have h0 : 0 ≤ min 1 (η / (K + 1)) := le_of_lt (lt_min one_pos (by positivity))
    have h1 : min 1 (η / (K + 1)) ≤ 1 := min_le_left _ _
    nlinarith
  · have h0 : 0 ≤ min 1 (η / (K + 1)) := le_of_lt (lt_min one_pos (by positivity))
    have hsq : Real.sqrt ((min 1 (η / (K + 1))) ^ 2) = min 1 (η / (K + 1)) :=
      Real.sqrt_sq h0
    have h2 : min 1 (η / (K + 1)) ≤ η / (K + 1) := min_le_right _ _
    have h3 : K * (η / (K + 1)) < η := by
      have h4 : K / (K + 1) < 1 := by
        rw [div_lt_one hK1]
        linarith
      calc K * (η / (K + 1)) = (K / (K + 1)) * η := by ring
        _ < 1 * η := mul_lt_mul_of_pos_right h4 hη
        _ = η := one_mul η
    rw [hsq]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 hK) h3

lemma exists_R_large {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ K * Real.sqrt (1 / (1 + R)) < η := by
  rcases eq_or_lt_of_le hK with h | hKpos
  · refine ⟨1, le_rfl, ?_⟩
    rw [← h, zero_mul]
    exact hη
  · refine ⟨max 1 (K ^ 2 / η ^ 2 + 1), le_max_left _ _, ?_⟩
    have hlt : K ^ 2 / η ^ 2 < 1 + max 1 (K ^ 2 / η ^ 2 + 1) := by
      have := le_max_right (1 : ℝ) (K ^ 2 / η ^ 2 + 1)
      linarith
    have hpos : (0 : ℝ) < K ^ 2 / η ^ 2 := by positivity
    have h1 : 1 / (1 + max 1 (K ^ 2 / η ^ 2 + 1)) < 1 / (K ^ 2 / η ^ 2) :=
      one_div_lt_one_div_of_lt hpos hlt
    have h2 : 1 / (K ^ 2 / η ^ 2) = (η / K) ^ 2 := by
      rw [div_pow]
      field_simp
    have h3 : Real.sqrt (1 / (1 + max 1 (K ^ 2 / η ^ 2 + 1))) < η / K := by
      rw [Real.sqrt_lt' (by positivity)]
      rw [h2] at h1
      exact h1
    calc K * Real.sqrt (1 / (1 + max 1 (K ^ 2 / η ^ 2 + 1))) < K * (η / K) :=
          mul_lt_mul_of_pos_left h3 hKpos
      _ = η := by field_simp

lemma exists_eps_small {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi / 4 ∧ K * Real.sqrt ε < η := by
  obtain ⟨δ, hδ0, hδ1, hδsmall⟩ := exists_delta_small hK hη
  refine ⟨min δ (Real.pi / 8), lt_min hδ0 (by positivity), ?_, ?_⟩
  · have h : min δ (Real.pi / 8) ≤ Real.pi / 8 := min_le_right _ _
    linarith [Real.pi_pos]
  · have hle : Real.sqrt (min δ (Real.pi / 8)) ≤ Real.sqrt δ :=
      Real.sqrt_le_sqrt (min_le_left _ _)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hK) hδsmall

end Work.FTS.StrongEps.L12
