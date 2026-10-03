import Mathlib
import Submission.Work.L62.lowcyl
import Submission.Work.Horn.pushdown_lower_end_linear_growth
import Submission.Work.Horn.pushdown_differentiableOn_punctured
import Submission.Work.Repel.pushdown_holo

namespace Work.L62

open MandelDim Set Filter Topology Metric
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Elementary facts about `pushdown` and `τ₀`

These are the small algebraic/analytic inputs of the main computation:
`pushdown E` vanishes exactly at `0` (so the `τ₀` on the outside is applied at a non-zero point),
`τ₀ z = -1/z` never vanishes off `0` and is holomorphic there, `π(-z) = (π z)⁻¹`, and `τ₀ → ∞`
(i.e. to the cobounded filter) as `z → 0` with `z ≠ 0`. -/

/-- `pushdown E` vanishes exactly at `0`. -/
private lemma pushdown_eq_zero_iff (E : ℂ → ℂ) (x : ℂ) :
    MandelDim.pushdown E x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [Work.Horn.MandelDim.pushdown_of_ne E hx] at h
    exact Work.Horn.MandelDim.piExp_ne_zero _ h
  · rintro rfl
    exact Work.Horn.MandelDim.pushdown_zero E

/-- `τ₀ z = -1/z` is non-zero at every non-zero point. -/
private lemma tau0_ne_zero' {z : ℂ} (hz : z ≠ 0) : MandelDim.tau0 z ≠ 0 := by
  simp only [MandelDim.tau0]
  exact div_ne_zero (by norm_num) hz

/-- `τ₀ z = -1/z` is holomorphic at every non-zero point. -/
private lemma differentiableAt_tau0' {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ MandelDim.tau0 z := by
  have h1 : MandelDim.tau0 = fun z : ℂ => (-1 : ℂ) / z := rfl
  rw [h1]
  exact (differentiableAt_const (c := (-1 : ℂ))).div differentiableAt_id (by simpa using hz)

/-- `π(-z) = (π z)⁻¹`. -/
private lemma piExp_neg' (z : ℂ) : MandelDim.piExp (-z) = (MandelDim.piExp z)⁻¹ := by
  rw [MandelDim.piExp, MandelDim.piExp,
    show 2 * ↑Real.pi * Complex.I * -z = -(2 * ↑Real.pi * Complex.I * z) by ring,
    Complex.exp_neg]

/-! ## The two limit computations -/

/-- `τ₀` sends the puncture `0` (with the point removed) to the lower end `Im → -∞`, i.e. to the
cobounded filter of the lift. -/
private lemma tendsto_tau0_cobounded :
    Tendsto MandelDim.tau0 (𝓝[≠] (0 : ℂ)) (Bornology.cobounded ℂ) := by
  rw [Filter.hasBasis_cobounded_norm.tendsto_right_iff]
  intro R _
  by_cases hR : R ≤ 0
  · filter_upwards with x
    rw [Work.L62.norm_tau0]
    have : (0 : ℝ) ≤ 1 / ‖x‖ := by positivity
    linarith
  · push Not at hR
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨R⁻¹, inv_pos.mpr hR, fun x hx hxne => ?_⟩
    change R ≤ ‖MandelDim.tau0 x‖
    rw [Work.L62.norm_tau0, le_div_iff₀ (norm_pos_iff.mpr (by simpa using hxne))]
    have h1 : ‖x‖ * R < 1 := (lt_div_iff₀ hR).mp (by simpa [dist_eq_norm] using hx)
    linarith [h1]

/-- **Linear growth of `pushdown Ẽ` at the lower end, in quotient form.**
`pushdown d.E x / x → π cl` as `‖x‖ → ∞`: this is
`Work.Horn.pushdown_lower_end_linear_growth` (`‖P x - π cl · x‖ ≤ ε‖x‖`) divided by `‖x‖`. -/
private lemma pushdown_div_tendsto {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    {cl : ℂ} (hcl : Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl)) :
    Tendsto (fun x : ℂ => MandelDim.pushdown d.E x / x) (Bornology.cobounded ℂ)
      (nhds (MandelDim.piExp cl)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ε', hε'pos, hε'lt⟩ : ∃ ε' > 0, ε' < ε := ⟨ε / 2, by linarith, by linarith⟩
  obtain ⟨R, hR⟩ := Work.Horn.pushdown_lower_end_linear_growth d hcl ε' hε'pos
  refine Filter.mem_of_superset (show {x : ℂ | max R 1 ≤ ‖x‖} ∈ Bornology.cobounded ℂ from ?_)
    (show {x : ℂ | max R 1 ≤ ‖x‖} ⊆
      {x : ℂ | dist (MandelDim.pushdown d.E x / x) (MandelDim.piExp cl) < ε} from ?_)
  · exact Filter.hasBasis_cobounded_norm.mem_iff.mpr ⟨max R 1, trivial, subset_rfl⟩
  · intro x hx
    change dist (MandelDim.pushdown d.E x / x) (MandelDim.piExp cl) < ε
    have hx1 : (1 : ℝ) ≤ ‖x‖ := le_trans (le_max_right R 1) hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx1
    have hxne : x ≠ 0 := norm_pos_iff.mp hxpos
    have hbound : ‖MandelDim.pushdown d.E x - MandelDim.piExp cl * x‖ ≤ ε' * ‖x‖ :=
      hR x (le_trans (le_max_left R 1) hx)
    have hEq : MandelDim.pushdown d.E x / x - MandelDim.piExp cl
        = (MandelDim.pushdown d.E x - MandelDim.piExp cl * x) / x := by field_simp
    rw [dist_eq_norm, hEq, norm_div, div_lt_iff₀ hxpos]
    exact lt_of_le_of_lt hbound (mul_lt_mul_of_pos_right hε'lt hxpos)

/-- **The `τ₀`-conjugate of the pushed-down horn map is holomorphic on `lowOmega` with derivative `π (-cl)` at the puncture.**  With `P := pushdown d.E` and `τ₀ z = -1/z`, the function `G ζ = τ₀ (P (τ₀ ζ))` is holomorphic on the lower cylinder neighbourhood `Work.L62.lowOmega d hd`, and `G'(0) = π(-cl)`, where `cl` is the lower-end limit of `d.E - id` (`ParabData.E_lower`, taken here as the hypothesis `hcl`).

This is the analytic core of the lower-end model: `G` is (away from `0`) the composition of the holomorphic `τ₀` on `ℂ \ {0}`, the holomorphic `P` on `π '' hd.Bl` (`Work.Repel.pushdown_holo` + `hd.Bl_T` + `Work.L62.E_add_one_Bl`), and `τ₀` again; at `0` one uses the lower-end linear growth of `P` (`Work.Horn.pushdown_lower_end_linear_growth`: `‖P x - π cl · x‖ ≤ ε‖x‖` for `‖x‖ ≥ R`), which gives `ζ⁻¹ G ζ = 1/(π cl - ζ·e(ζ)) → (π cl)⁻¹ = π(-cl)`. -/
theorem tau0_pushdown_holo_deriv {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl)) :
    HasDerivAt (fun ζ : ℂ => MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 ζ)))
      (MandelDim.piExp (-cl)) 0 ∧
    DifferentiableOn ℂ (fun ζ : ℂ => MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 ζ)))
      (Work.L62.lowOmega d hd) := by
  set F : ℂ → ℂ := fun ζ => MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 ζ)) with hF
  have hF0 : F 0 = 0 := by simp [hF, MandelDim.tau0, Work.Horn.MandelDim.pushdown_zero]
  -- ### 1. the derivative at the puncture: `ζ⁻¹ G ζ → π(-cl)`
  have hderiv : HasDerivAt F (MandelDim.piExp (-cl)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hmain : Tendsto (fun ζ : ℂ => MandelDim.tau0 ζ / MandelDim.pushdown d.E (MandelDim.tau0 ζ))
        (𝓝[≠] (0 : ℂ)) (𝓝 (MandelDim.piExp (-cl))) := by
      -- substitute `x = τ₀ ζ = -1/ζ`, which escapes to `∞`
      have h1 : Tendsto (fun ζ : ℂ => MandelDim.pushdown d.E (MandelDim.tau0 ζ) / MandelDim.tau0 ζ)
          (𝓝[≠] 0) (𝓝 (MandelDim.piExp cl)) :=
        (pushdown_div_tendsto d hcl).comp tendsto_tau0_cobounded
      have h2 : Tendsto
          (fun ζ : ℂ => (MandelDim.pushdown d.E (MandelDim.tau0 ζ) / MandelDim.tau0 ζ)⁻¹)
          (𝓝[≠] 0) (𝓝 ((MandelDim.piExp cl)⁻¹)) :=
        h1.inv₀ (Work.Horn.MandelDim.piExp_ne_zero cl)
      rw [← piExp_neg' cl] at h2
      exact h2.congr (fun ζ => inv_div _ _)
    have hsl : slope F 0 = fun ζ : ℂ => ζ⁻¹ * F ζ := by
      funext ζ; simp only [slope, hF0, vsub_eq_sub, sub_zero, smul_eq_mul]
    rw [hsl]
    refine hmain.congr (fun ζ => ?_)
    simp only [hF, MandelDim.tau0]
    ring
  -- ### 2. holomorphy on `lowOmega = {0} ∪ τ₀(π '' Bl)`
  have holo : DifferentiableOn ℂ F (Work.L62.lowOmega d hd) := by
    intro ζ hζ
    rw [Work.L62.lowOmega] at hζ
    rcases hζ with h | h
    · subst h
      exact hderiv.differentiableAt.differentiableWithinAt
    · obtain ⟨x, hxmem, hxζ⟩ := h
      obtain ⟨w, hw, hwx⟩ := hxmem
      have hx0 : x ≠ 0 := by rw [← hwx]; exact Work.Horn.MandelDim.piExp_ne_zero w
      have hζ0 : ζ ≠ 0 := by rw [← hxζ]; exact tau0_ne_zero' hx0
      have hτ : MandelDim.tau0 ζ = x := by rw [← hxζ, Work.L62.tau0_tau0]
      -- `pushdown d.E` is holomorphic at `τ₀ ζ = x ∈ π '' Bl`, by `g_holo` and openness of `π '' Bl`
      have hP : DifferentiableAt ℂ (MandelDim.pushdown d.E) (MandelDim.tau0 ζ) := by
        rw [hτ]
        refine (hd.g_holo.differentiableAt (x := x) ?_)
        refine Filter.mem_of_superset
          ((Work.L62.isOpen_piExp_image hd.Bl_open).mem_nhds ⟨w, hw, hwx⟩) ?_
        rintro y ⟨w', hw', rfl⟩
        exact Or.inr ⟨w', Or.inr hw', rfl⟩
      have hne : MandelDim.pushdown d.E (MandelDim.tau0 ζ) ≠ 0 := by
        rw [hτ]
        exact fun hz => hx0 ((pushdown_eq_zero_iff d.E x).mp hz)
      exact ((differentiableAt_tau0' hne).comp ζ
        (hP.comp ζ (differentiableAt_tau0' hζ0))).differentiableWithinAt
  exact ⟨hderiv, holo⟩

end

end Work.L62
