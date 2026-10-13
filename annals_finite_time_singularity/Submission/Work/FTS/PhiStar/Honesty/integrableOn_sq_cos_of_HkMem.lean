import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the `cos θ`-weighted `θ`-slice of `HkMem α 0 F`

At level `0` the `H^k`-integrand collapses to a single square,

    `HkIntegrand α 0 F z θ = (F z θ · w z / sin(2θ)^{η/2})²`,

whose `θ`-integral is honest at every `z ∈ [0,∞)` by `HkMem α 0 F`.  On `Iθ` and away from
the two endpoints `θ = 0, π/2` this square is `(F z θ)² · w z² · sin(2θ)^{-η}`, and
`cos θ · sin(2θ)^{η}` is bounded by `1` there.  Hence

    `(F z θ)² · cos θ = HkIntegrand α 0 F z θ · (cos θ · sin(2θ)^η / w z²)`

holds almost everywhere on `Iθ` for `z > 0`, with a multiplier bounded by the constant
`1 / w z²`; multiplying an integrable function by such a multiplier preserves integrability.

The two endpoints `{0, π/2}` (where `sin(2θ) = 0` and the identity above fails) are a null set,
which is the only source of the "almost everywhere" caveat.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

theorem integrableOn_sq_cos_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ := by
  classical
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  -- The `H^k`-slice at `z` is honest (this is the only content of `HkMem α 0 F` that is used).
  have hB : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 F z θ) Work.Spaces.Iθ :=
    hF.1 z hzIz
  -- The bounded multiplier `cos θ · sin(2θ)^η / w z²`.
  set c : ℝ → ℝ := fun θ => Real.cos θ * (Real.sin (2 * θ)) ^ Work.Spaces.eta
      / (Work.Spaces.w z) ^ 2 with hcdef
  have hcont_c : Continuous c := by
    rw [hcdef]
    have h1 : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun _ => Or.inr Work.Spaces.eta_nonneg)
    exact (Real.continuous_cos.mul h1).div_const _
  have hc_aesm : AEStronglyMeasurable c (volume.restrict Work.Spaces.Iθ) :=
    hcont_c.aestronglyMeasurable
  -- **Pointwise identity** on `Iθ` away from the endpoints.
  have key : ∀ θ, θ ∈ Work.Spaces.Iθ → Real.sin (2 * θ) ≠ 0 →
      (F z θ) ^ 2 * Real.cos θ = Work.Spaces.HkIntegrand α 0 F z θ * c θ := by
    intro θ hθI hsinθ
    have hsp : 0 < Real.sin (2 * θ) :=
      lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
        (by linarith [hθI.2, Real.pi_pos])) (Ne.symm hsinθ)
    rw [hcdef]
    rw [show Work.Spaces.HkIntegrand α 0 F z θ
        = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
          simp [Work.Spaces.HkIntegrand]]
    -- `(sin(2θ)^{η/2})² = sin(2θ)^η`
    have hqssq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add hsp]
      congr 1
      rw [Work.Spaces.eta]; ring
    rw [mul_pow, div_pow, hqssq]
    have hse : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hsp _)
    have hwne : Work.Spaces.w z ≠ 0 := ne_of_gt hwpos
    field_simp
  -- The endpoint set where `sin(2θ)` vanishes is contained in `{0, π/2}`.
  have hsub : {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0} ⊆
      ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    obtain ⟨hθI, hθ0⟩ := hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h0, hpi⟩ := hcon
    have hθpos : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm h0)
    have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 hpi
    have h1 : 0 < 2 * θ := by linarith
    have h2 : 2 * θ < Real.pi := by linarith [Real.pi_pos]
    have h3 := Real.sin_pos_of_pos_of_lt_pi h1 h2
    rw [hθ0] at h3
    exact lt_irrefl 0 h3
  have hnull : volume {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0} = 0 := by
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  -- Hence `sin(2θ) ≠ 0` almost everywhere on `Iθ`.
  have hsin : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), Real.sin (2 * θ) ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : ℝ | ¬ Real.sin (2 * a) ≠ 0} = {a : ℝ | Real.sin (2 * a) = 0} := by
      ext a; simp
    rw [hset]
    rw [MeasureTheory.Measure.restrict_apply
      (by measurability : MeasurableSet {a : ℝ | Real.sin (2 * a) = 0})]
    refine measure_mono_null ?_ hnull
    intro θ hθ
    exact ⟨hθ.2, hθ.1⟩
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) ≠ 0 :=
    (ae_restrict_mem hIθ).and hsin
  -- The two functions agree almost everywhere on `Iθ`.
  have hfun : (fun θ : ℝ => (F z θ) ^ 2 * Real.cos θ) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 0 F z θ * c θ) := by
    filter_upwards [hae] with θ hθ
    exact key θ hθ.1 hθ.2
  -- `HkIntegrand · c` is integrable: `|c|` is bounded by the constant `(w z²)⁻¹` on `Iθ`.
  have hInt : Integrable (fun θ => Work.Spaces.HkIntegrand α 0 F z θ * c θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.mono' ((hB.norm).const_mul (((Work.Spaces.w z) ^ 2)⁻¹)) ?_ ?_
    · exact hB.aestronglyMeasurable.mul hc_aesm
    · filter_upwards [hae] with θ hθ
      obtain ⟨hθI, hsinθ⟩ := hθ
      have hsp : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
          (by linarith [hθI.2, Real.pi_pos])) (Ne.symm hsinθ)
      rw [norm_mul]
      have hcn : ‖c θ‖ ≤ ((Work.Spaces.w z) ^ 2)⁻¹ := by
        rw [hcdef]
        simp only
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hwpos 2)]
        rw [div_le_iff₀ (pow_pos hwpos 2), inv_mul_cancel₀ (ne_of_gt (pow_pos hwpos 2))]
        rw [abs_mul]
        have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
        have h2 : |(Real.sin (2 * θ)) ^ Work.Spaces.eta| ≤ 1 := by
          rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsp) _)]
          exact Real.rpow_le_one (le_of_lt hsp) (Real.sin_le_one _) Work.Spaces.eta_nonneg
        simpa using mul_le_mul h1 h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      calc ‖Work.Spaces.HkIntegrand α 0 F z θ‖ * ‖c θ‖
          ≤ ‖Work.Spaces.HkIntegrand α 0 F z θ‖ * ((Work.Spaces.w z) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hcn (norm_nonneg _)
        _ = ((Work.Spaces.w z) ^ 2)⁻¹ * ‖Work.Spaces.HkIntegrand α 0 F z θ‖ := by ring
  exact hInt.congr hfun.symm

end Work.FTS.PhiStar.Honesty
