/-
# `Fallback` — self-contained proofs of the two `Linv` ingredients

Under `Work.FTS.PhiStar.Linv23Aux.Fallback` this file re-proves, without depending on the
delegated files, the two ingredients of the target `linv23_smooth`:

* `hasDerivAt_LinvPhi` — the fundamental theorem of calculus for the regularised primitive
  `LinvPhi h θ = ∫_0^θ sin t cos²t h t / 2`, requiring only *local* boundedness of `h` at `0⁺`;
* `linvPhi_smooth` — `LinvPhi h` is `C^∞` on `(0, π/2)` when `h` is;
* `linv_bounded` — `|Linv h θ| ≤ M / (2 cos³ t)` for `θ ∈ (0, t)`, `t < π/2`, where `M` bounds
  `|h|` on `(0, t)`: the `θ⁻²` blow-up of the weight `(sin²θ cos³θ)⁻¹` is cancelled by the `θ²`
  vanishing of the primitive, because `(1 - cos θ)/sin²θ = 1/(1 + cos θ) ≤ 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.Linv23Aux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Linv23Aux.Fallback

set_option autoImplicit false

/-- **FTC for the regularised primitive.**  If `h` is continuous on `(0, π/2)` and locally
bounded at `0⁺` then `LinvPhi h` has derivative `LinvPhiInt h θ` at every `θ ∈ (0, π/2)`. -/
theorem hasDerivAt_LinvPhi {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |h θ| ≤ M)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (LinvPhi h) (LinvPhiInt h θ) θ := by
  obtain ⟨t₁, hθt₁, ht₁π⟩ : ∃ t₁ : ℝ, θ < t₁ ∧ t₁ < Real.pi / 2 :=
    ⟨(θ + Real.pi / 2) / 2, by linarith [hθ.2], by linarith [hθ.2]⟩
  obtain ⟨M, hM⟩ := hbdd t₁ (by linarith [hθ.1]) ht₁π
  have hcontOn : ContinuousOn (LinvPhiInt h) (Set.Ioo 0 (Real.pi / 2)) := by
    unfold LinvPhiInt
    exact ((Real.continuous_sin.continuousOn.mul
      ((Real.continuous_cos.pow 2).continuousOn)).div_const 2).mul hcont
  have hsub : Set.Ioc (0 : ℝ) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 (lt_trans hθt₁ ht₁π)⟩
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Ioc (0 : ℝ) θ), ‖LinvPhiInt h x‖ ≤ M / 2 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hxmem : x ∈ Set.Ioo 0 t₁ := ⟨hx.1, lt_of_le_of_lt hx.2 hθt₁⟩
    have h1 : |Real.sin x * Real.cos x ^ 2 / 2| ≤ 1 / 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (sq_nonneg (Real.cos x))]
      have hc : Real.cos x ^ 2 ≤ 1 := Real.cos_sq_le_one x
      have hs : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hprod : |Real.sin x| * Real.cos x ^ 2 ≤ 1 * 1 :=
        mul_le_mul hs hc (sq_nonneg _) (by norm_num)
      linarith
    have h2 : |h x| ≤ M := hM x hxmem
    rw [Real.norm_eq_abs, LinvPhiInt, abs_mul]
    calc |Real.sin x * Real.cos x ^ 2 / 2| * |h x| ≤ 1 / 2 * M :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = M / 2 := by ring
  have hfin : volume (Set.Ioc (0 : ℝ) θ) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hint : IntervalIntegrable (LinvPhiInt h) volume (0 : ℝ) θ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hθ.1.le]
    exact IntegrableOn.of_bound hfin
      ((hcontOn.mono hsub).aestronglyMeasurable measurableSet_Ioc) (M / 2) hbound
  have hct : ContinuousAt (LinvPhiInt h) θ := hcontOn.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have hsm : StronglyMeasurableAtFilter (LinvPhiInt h) (𝓝 θ) volume :=
    hcontOn.stronglyMeasurableAtFilter isOpen_Ioo θ hθ
  exact intervalIntegral.integral_hasDerivAt_right hint hsm hct

/-- The primitive of a `C^∞` function that is locally bounded at `0⁺` is `C^∞` on `(0, π/2)`. -/
theorem linvPhi_smooth {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |h θ| ≤ M) :
    ContDiffOn ℝ Work.Stability.smoothOrder (LinvPhi h) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)) := hsm.continuousOn
  have hInt : ContDiffOn ℝ Work.Stability.smoothOrder (LinvPhiInt h)
      (Set.Ioo 0 (Real.pi / 2)) := by
    unfold LinvPhiInt
    exact (((Real.contDiff_sin.contDiffOn).mul
      (((Real.contDiff_cos).contDiffOn).pow 2)).div_const 2).mul hsm
  have hderiv : ContDiffOn ℝ Work.Stability.smoothOrder (deriv (LinvPhi h))
      (Set.Ioo 0 (Real.pi / 2)) :=
    ContDiffOn.congr hInt fun x hx => (hasDerivAt_LinvPhi hcont hbdd hx).deriv
  rw [show Work.Stability.smoothOrder = (∞ : ℕ∞ω) from rfl,
    contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
  exact ⟨fun x hx => (hasDerivAt_LinvPhi hcont hbdd hx).differentiableAt.differentiableWithinAt,
    hderiv⟩

/-- The local bound for `Linv`: if `|h| ≤ M` on `(0, t)`, `t < π/2`, then
`|Linv h θ| ≤ M / (2 cos³ t)` for every `θ ∈ (0, t)`. -/
theorem linv_bounded_aux {h : ℝ → ℝ} {M t : ℝ}
    (hM : ∀ θ ∈ Set.Ioo 0 t, |h θ| ≤ M) (ht0 : 0 < t) (htp : t < Real.pi / 2) :
    ∀ θ ∈ Set.Ioo 0 t, |Linv h θ| ≤ M / (2 * Real.cos t ^ 3) := by
  have hM0 : 0 ≤ M := by
    have hmem : t / 2 ∈ Set.Ioo 0 t := ⟨by linarith, by linarith⟩
    exact le_trans (abs_nonneg _) (hM (t / 2) hmem)
  have hcost : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht0, Real.pi_pos], htp⟩
  have hcost3 : 0 < Real.cos t ^ 3 := pow_pos hcost 3
  intro θ hθ
  have hθπ : θ < Real.pi / 2 := lt_trans hθ.2 htp
  have hsinθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (lt_trans hθπ (by linarith [Real.pi_pos]))
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθπ⟩
  have hcosθ3 : 0 < Real.cos θ ^ 3 := pow_pos hcosθ 3
  -- Step 1: the primitive is `O(θ²)`, i.e. `|LinvPhi h θ| ≤ M/2 * (1 - cos θ)`.
  have hΦ : |LinvPhi h θ| ≤ M / 2 * (1 - Real.cos θ) := by
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0 : ℝ) θ →
        ‖LinvPhiInt h x‖ ≤ M / 2 * Real.sin x := by
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hxmem : x ∈ Set.Ioo 0 t := ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      have hxtπ : x < Real.pi / 2 := lt_of_le_of_lt hx.2 hθπ
      have hsinx : 0 ≤ Real.sin x :=
        le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx.1
          (lt_trans hxtπ (by linarith [Real.pi_pos])))
      have h1 : |Real.sin x * Real.cos x ^ 2 / 2| ≤ Real.sin x / 2 := by
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg hsinx, abs_of_nonneg (sq_nonneg (Real.cos x))]
        have hc : Real.cos x ^ 2 ≤ 1 := Real.cos_sq_le_one x
        have h3 : Real.sin x * Real.cos x ^ 2 ≤ Real.sin x * 1 :=
          mul_le_mul_of_nonneg_left hc hsinx
        linarith
      rw [Real.norm_eq_abs, LinvPhiInt, abs_mul]
      calc |Real.sin x * Real.cos x ^ 2 / 2| * |h x| ≤ Real.sin x / 2 * M :=
            mul_le_mul h1 (hM x hxmem) (abs_nonneg _) (by linarith [hsinx])
        _ = M / 2 * Real.sin x := by ring
    have hIntg : IntervalIntegrable (fun x : ℝ => M / 2 * Real.sin x) volume (0 : ℝ) θ :=
      (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _
    have hval : (∫ x in (0 : ℝ)..θ, M / 2 * Real.sin x) = M / 2 * (1 - Real.cos θ) := by
      rw [intervalIntegral.integral_const_mul, integral_sin, Real.cos_zero]
    have hmain := intervalIntegral.norm_integral_le_of_norm_le (le_of_lt hθ.1) hae hIntg
    rw [Real.norm_eq_abs, hval] at hmain
    exact hmain
  -- Step 2: `(sin²θ cos³θ)⁻¹ (1 - cos θ) ≤ 1/cos³t`, via `(1 - cos θ)/sin²θ = 1/(1 + cos θ)`.
  have hsin_sq : Real.sin θ ^ 2 = (1 - Real.cos θ) * (1 + Real.cos θ) := by
    rw [Real.sin_sq]; ring
  have hlt1 : Real.cos θ < 1 := by
    have hpos : 0 < (1 - Real.cos θ) * (1 + Real.cos θ) := by
      rw [← hsin_sq]; exact pow_pos hsinθ 2
    have h2 : 0 < 1 + Real.cos θ := by linarith [hcosθ]
    nlinarith [hpos, h2]
  have hone : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 - Real.cos θ)
      = ((1 + Real.cos θ) * Real.cos θ ^ 3)⁻¹ := by
    rw [hsin_sq]
    have h1 : (1 - Real.cos θ) ≠ 0 := by intro h; linarith
    have h2 : (1 + Real.cos θ) ≠ 0 := by intro h; linarith [hcosθ]
    have h3 : Real.cos θ ≠ 0 := ne_of_gt hcosθ
    field_simp
  have hb1 : ((1 + Real.cos θ) * Real.cos θ ^ 3)⁻¹ ≤ (Real.cos θ ^ 3)⁻¹ := by
    refine (inv_le_inv₀ (mul_pos (by linarith [hcosθ]) hcosθ3) hcosθ3).mpr ?_
    have hle : (1 : ℝ) ≤ 1 + Real.cos θ := by linarith [hcosθ]
    calc Real.cos θ ^ 3 = 1 * Real.cos θ ^ 3 := (one_mul _).symm
      _ ≤ (1 + Real.cos θ) * Real.cos θ ^ 3 :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hcosθ3)
  have hcub : Real.cos t ^ 3 ≤ Real.cos θ ^ 3 :=
    pow_le_pow_left₀ (le_of_lt hcost)
      (Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1)
        (by linarith [htp, Real.pi_pos]) (le_of_lt hθ.2)) 3
  have hb2 : (Real.cos θ ^ 3)⁻¹ ≤ (Real.cos t ^ 3)⁻¹ :=
    (inv_le_inv₀ hcosθ3 hcost3).mpr hcub
  have hchain : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 - Real.cos θ)
      ≤ (Real.cos t ^ 3)⁻¹ := by
    rw [hone]; exact le_trans hb1 hb2
  have hmu : 0 < Real.sin θ ^ 2 * Real.cos θ ^ 3 := mul_pos (pow_pos hsinθ 2) hcosθ3
  have hhalf : 0 ≤ M / 2 := div_nonneg hM0 (by norm_num)
  rw [Linv_eq_phi h θ, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hmu)]
  calc (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * |LinvPhi h θ|
      ≤ (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (M / 2 * (1 - Real.cos θ)) :=
        mul_le_mul_of_nonneg_left hΦ (le_of_lt (inv_pos.mpr hmu))
    _ = M / 2 * ((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 - Real.cos θ)) := by ring
    _ ≤ M / 2 * (Real.cos t ^ 3)⁻¹ := mul_le_mul_of_nonneg_left hchain hhalf
    _ = M / (2 * Real.cos t ^ 3) := by ring

/-- The local bound for `Linv` in the exact form of the target statement. -/
theorem linv_bounded {h : ℝ → ℝ}
    (hbdd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |h θ| ≤ M) :
    ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |Linv h θ| ≤ M := by
  intro t ht0 htp
  obtain ⟨M, hM⟩ := hbdd t ht0 htp
  exact ⟨M / (2 * Real.cos t ^ 3), linv_bounded_aux hM ht0 htp⟩

/-- The local bound for the primitive `LinvI h = ∫_0^θ Linv h`: a bound `M` for `|Linv h|` on
`(0, t)` gives `|LinvI h θ| ≤ max M |Linv h 0| * t` on `(0, t)`.  (The value at `0` has to be
accounted for separately since `uIcc 0 θ` contains it.) -/
theorem linvI_bounded {h : ℝ → ℝ}
    (hbdd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |Linv h θ| ≤ M) :
    ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |LinvI h θ| ≤ M := by
  intro t ht0 htp
  obtain ⟨M, hM⟩ := hbdd t ht0 htp
  refine ⟨max M |Linv h 0| * t, fun θ hθ => ?_⟩
  have hC0 : 0 ≤ max M |Linv h 0| := le_trans (abs_nonneg _) (le_max_right _ _)
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0 : ℝ) θ →
      ‖Linv h x‖ ≤ max M |Linv h 0| := by
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs]
    rcases eq_or_lt_of_le (le_of_lt hx.1) with hx0 | hx0
    · rw [← hx0]; exact le_max_right _ _
    · exact le_trans (hM x ⟨hx0, lt_of_le_of_lt hx.2 hθ.2⟩) (le_max_left _ _)
  have hInt : IntervalIntegrable (fun _ : ℝ => max M |Linv h 0|) volume (0 : ℝ) θ :=
    continuous_const.intervalIntegrable _ _
  have hmain := intervalIntegral.norm_integral_le_of_norm_le (le_of_lt hθ.1) hae hInt
  have hval : (∫ x in (0 : ℝ)..θ, max M |Linv h 0|) = max M |Linv h 0| * θ := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  rw [Real.norm_eq_abs, hval] at hmain
  exact le_trans hmain (mul_le_mul_of_nonneg_left hθ.2.le hC0)

end Work.FTS.PhiStar.Linv23Aux.Fallback
