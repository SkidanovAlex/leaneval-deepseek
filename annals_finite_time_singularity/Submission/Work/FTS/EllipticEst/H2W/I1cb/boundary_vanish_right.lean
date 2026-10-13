import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.I1cb

/-! ## Vanishing of a boundary value at `θ = π/2`

If `|F θ| ≤ C sin(2θ) |G θ|` on `(d, π/2)` and `G` is integrable there, then `F → 0` at `π/2`.
The mechanism is that any nonzero limit `c` of `F` forces `|G θ| ≥ c' / sin(2θ)` on a
one-sided neighbourhood of `π/2`, and `1 / sin(2θ)` is not integrable there (it behaves like
`1/(2(π/2 - θ))`, a logarithmic divergence).  The non-integrability is obtained from Mathlib's
criterion `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` applied to the
primitive `θ ↦ log (tan θ)`, whose derivative is `2 / sin(2θ)` and which tends to `+∞` as
`θ → (π/2)⁻`. -/

open MeasureTheory Set Filter
open scoped Topology

/-- The derivative of the primitive of `1/sin(2θ)` on `(0, π/2)`. -/
lemma bvr_deriv_log_tan_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    deriv (fun θ => Real.log (Real.tan θ)) θ = 2 * (Real.sin (2*θ))⁻¹ := by
  have hcos : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).ne'
  have htan : Real.tan θ ≠ 0 :=
    (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2).ne'
  have hsin : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).ne'
  rw [(Real.hasDerivAt_tan hcos).log htan |>.deriv, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  field_simp

/-- `1 / sin(2θ)` is not integrable on any `(t, π/2)`, `t < π/2`: the logarithmic divergence
at `π/2`. -/
lemma bvr_not_integrableOn_inv_sin_two {t : ℝ} (ht : t < Real.pi/2) :
    ¬ IntegrableOn (fun θ => (Real.sin (2*θ))⁻¹) (Set.Ioo t (Real.pi/2)) := by
  have hpi2 : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hmem : Set.Ioo 0 (Real.pi/2) ∈ 𝓝[<] (Real.pi/2) :=
    (nhdsLT_basis (Real.pi/2)).mem_iff.2 ⟨0, hpi2, subset_rfl⟩
  refine not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter (l := 𝓝[<] (Real.pi/2))
    (E := ℝ) (F := ℝ) (f := fun θ => Real.log (Real.tan θ))
    ((nhdsLT_basis (Real.pi/2)).mem_iff.2 ⟨t, ht, subset_rfl⟩) ?_ ?_ ?_
  · filter_upwards [hmem] with x hx
    exact ((Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩).ne').log
      (Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2).ne').differentiableAt
  · have h1 : Tendsto (fun x => Real.log (Real.tan x)) (𝓝[<] (Real.pi/2)) atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_tan_pi_div_two
    have hev : (fun x => ‖Real.log (Real.tan x)‖) =ᶠ[𝓝[<] (Real.pi/2)]
        (fun x => Real.log (Real.tan x)) := by
      filter_upwards [Real.tendsto_tan_pi_div_two.eventually (eventually_ge_atTop 1)] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx)]
    exact h1.congr' hev.symm
  · refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [hmem] with x hx
    rw [bvr_deriv_log_tan_Ioo hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- A function dominating a positive multiple of `1/sin(2θ)` on `(t, π/2)`, `0 ≤ t < π/2`,
is not integrable there. -/
lemma bvr_not_integrableOn_of_ge_inv_sin_two {G : ℝ → ℝ} {c t : ℝ} (hc : 0 < c)
    (ht : 0 ≤ t) (ht2 : t < Real.pi/2)
    (h : ∀ θ ∈ Set.Ioo t (Real.pi/2), c * (Real.sin (2*θ))⁻¹ ≤ G θ) :
    ¬ IntegrableOn G (Set.Ioo t (Real.pi/2)) := by
  intro hG
  have habs : IntegrableOn (fun θ => |G θ|) (Set.Ioo t (Real.pi/2)) := hG.abs
  have hkey : IntegrableOn (fun θ => c * (Real.sin (2*θ))⁻¹) (Set.Ioo t (Real.pi/2)) := by
    refine Integrable.mono' habs ?_ ?_
    · exact (measurable_const.mul ((Real.continuous_sin.measurable.comp
        (measurable_const.mul measurable_id)).inv)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs : 0 < Real.sin (2*θ) := by
        refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, ht]) ?_
        linarith [hθ.2]
      have hinv : 0 < (Real.sin (2*θ))⁻¹ := inv_pos.2 hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hc, abs_of_pos hinv]
      exact le_trans (h θ hθ) (le_abs_self _)
  have hsin_int : IntegrableOn (fun θ => (Real.sin (2*θ))⁻¹) (Set.Ioo t (Real.pi/2)) := by
    have h2 : IntegrableOn (fun θ => c⁻¹ * (c * (Real.sin (2*θ))⁻¹))
        (Set.Ioo t (Real.pi/2)) := hkey.const_mul c⁻¹
    refine h2.congr ?_
    filter_upwards with θ
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact bvr_not_integrableOn_inv_sin_two ht2 hsin_int

theorem boundary_vanish_right {F G : ℝ → ℝ} {c d C : ℝ} (hd : d < Real.pi/2) (hC : 0 ≤ C)
    (hlim : Filter.Tendsto F (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds c))
    (hbd : ∀ θ ∈ Set.Ioo d (Real.pi/2), |F θ| ≤ C * Real.sin (2*θ) * |G θ|)
    (hint : MeasureTheory.IntegrableOn G (Set.Ioo d (Real.pi/2))) : c = 0 := by
  by_contra hc
  have hpi2 : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcpos : 0 < |c| := abs_pos.2 hc
  -- `|F| ≥ |c|/2` on a one-sided neighbourhood `(δ, π/2)` of `π/2`
  obtain ⟨δ, hδlt, hδsub⟩ := (nhdsLT_basis (Real.pi/2)).mem_iff.1
    (hlim.abs.eventually (eventually_ge_nhds (by linarith : |c|/2 < |c|)))
  -- shrink to a subinterval `(t, π/2)` contained in `(d, π/2)` and in `(δ, π/2)`, with `t ≥ 0`
  set t := max (max d δ) 0
  have ht2 : t < Real.pi / 2 := max_lt (max_lt hd hδlt) hpi2
  have ht0 : 0 ≤ t := le_max_right _ _
  have htd : d ≤ t := le_trans (le_max_left d δ) (le_max_left _ 0)
  have htδ : δ ≤ t := le_trans (le_max_right d δ) (le_max_left _ 0)
  have hraw : ∀ θ ∈ Set.Ioo t (Real.pi/2), |c|/2 ≤ C * Real.sin (2*θ) * |G θ| := by
    intro θ hθ
    exact le_trans (hδsub ⟨lt_of_le_of_lt htδ hθ.1, hθ.2⟩)
      (hbd θ ⟨lt_of_le_of_lt htd hθ.1, hθ.2⟩)
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- `C = 0` makes the bound `|F| ≤ 0` on `(t, π/2)`
    subst hC0
    obtain ⟨θ, hθ⟩ : (Set.Ioo t (Real.pi/2)).Nonempty :=
      ⟨(t + Real.pi/2)/2, by constructor <;> linarith⟩
    have hh := hraw θ hθ
    rw [zero_mul, zero_mul] at hh
    linarith
  · -- the lower bound `|c|/(2C) · 1/sin(2θ) ≤ |G θ|` contradicts integrability of `G`
    have hkey : ∀ θ ∈ Set.Ioo t (Real.pi/2),
        |c|/(2*C) * (Real.sin (2*θ))⁻¹ ≤ |G θ| := by
      intro θ hθ
      have hs : 0 < Real.sin (2*θ) := by
        refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, ht0]) ?_
        linarith [hθ.2]
      have h1 : |c| / (2 * C) ≤ Real.sin (2*θ) * |G θ| := by
        rw [div_le_iff₀ (by positivity)]
        linarith [hraw θ hθ]
      have h2 : |c|/(2*C) * (Real.sin (2*θ))⁻¹ * Real.sin (2*θ)
          ≤ |G θ| * Real.sin (2*θ) := by
        rw [mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
        exact h1.trans (le_of_eq (mul_comm _ _))
      exact (mul_le_mul_iff_of_pos_right hs).1 h2
    exact (bvr_not_integrableOn_of_ge_inv_sin_two (G := fun θ => |G θ|) (c := |c|/(2*C))
      (div_pos hcpos (by positivity)) ht0 ht2 hkey)
      (IntegrableOn.mono_set (hint.abs) (fun _ hθ => ⟨lt_of_le_of_lt htd hθ.1, hθ.2⟩))

end Work.FTS.EllipticEst.H2W.I1cb
