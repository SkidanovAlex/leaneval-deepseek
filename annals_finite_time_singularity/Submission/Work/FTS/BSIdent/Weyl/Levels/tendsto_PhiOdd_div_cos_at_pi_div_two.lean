import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_slice_quotient

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

/-!
# The boundary value `Φ̂/cos` at `θ = π/2`

Near `θ = π/2` the stream function `Φ` vanishes (`Φ w (π/2) τ = 0`), so the quotient
`Φ̂(w,θ,τ)/cos θ` has a finite limit there, namely `-∂_θ Φ(w₀,π/2,τ)`: indeed, writing
`θ = π/2 - δ` with `δ → 0⁺`, `cos θ = sin δ` and `Φ(w,θ) = -δ ∂_θΦ(w,π/2) + o(δ)`.

The proof is the product rule for limits applied to the two factors
`Φ(w,θ)/(θ - π/2) → ∂_θΦ(w₀,π/2)` (the slice difference quotient, `tendsto_slice_quotient`)
and `(θ - π/2)/cos θ → 1/∂_θ(cos)(π/2) = -1`, combined with `Φ̂ = Φ` on the sector
`{p.2 > 0}`.
-/

/-- Near `(w₀, π/2)`, the sector `{0 < p.1 ∧ 0 < p.2 ∧ p.2 < π/2}` is contained in the box
`{|p.1 - w₀| < δ} ∩ {|p.2 - π/2| < δ}` (and there `p.2 ≠ π/2`).  This is the filter transfer
that lets the slice-quotient lemmas be applied on the sector. -/
private lemma sector_le_box (w₀ δ : ℝ) (hδ : 0 < δ) :
    𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2) ≤
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ ∧ p.2 ≠ Real.pi / 2}]
        (w₀, Real.pi / 2) := by
  set T : Set (ℝ × ℝ) := {p | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ} with hT
  have hTmem : T ∈ 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}]
      (w₀, Real.pi / 2) :=
    nhdsWithin_le_nhds (Filter.mem_of_superset (Metric.ball_mem_nhds (w₀, Real.pi / 2) hδ)
      (by
        intro p hp
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
        exact hp))
  calc 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2)
      = 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2} ∩ T] (w₀, Real.pi / 2) :=
        (nhdsWithin_inter_of_mem' hTmem).symm
    _ ≤ 𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - Real.pi / 2| < δ ∧ p.2 ≠ Real.pi / 2}]
          (w₀, Real.pi / 2) :=
        nhdsWithin_mono _ fun p hp => ⟨hp.2.1, hp.2.2, ne_of_lt hp.1.2.2⟩

theorem tendsto_PhiOdd_div_cos_at_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-(deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2)))) := by
  -- a positive radius, small enough that the box stays in `w > -1` and in `w > 0`
  obtain ⟨δ, hδpos, hδ1, hδw⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ w₀ :=
    ⟨min 1 w₀, lt_min one_pos hw₀, min_le_left _ _, min_le_right _ _⟩
  -- the `C²` hypothesis and the vanishing, on the box of half-width `δ`
  have hsm' : ∀ w θ : ℝ, |w - w₀| < δ → |θ - Real.pi / 2| < δ →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) := by
    intro w θ hw hθ
    rw [abs_lt] at hw hθ
    exact hsm w θ (by linarith [hw.1, hδw])
      (by linarith [hθ.1, hδ1, Real.pi_pos]) (by linarith [hθ.2, hδ1])
  have hz' : ∀ w : ℝ, |w - w₀| < δ → Φ w (Real.pi / 2) τ = 0 := by
    intro w hw
    rw [abs_lt] at hw
    exact hπ w (by linarith [hw.1, hδw])
  -- (1) the `θ`-difference quotient of `Φ` tends to `∂_θΦ (w₀, π/2)`
  have hslope : Filter.Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ / (p.2 - Real.pi / 2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) :=
    (tendsto_slice_quotient (f := fun w θ : ℝ => Φ w θ τ) (w₀ := w₀) (θ₀ := Real.pi / 2)
      (δ := δ) hδpos hsm' hz').mono_left (sector_le_box w₀ δ hδpos)
  -- (2) the quotient `(θ - π/2) / cos θ` tends to `-1`
  have hcosq : Filter.Tendsto (fun p : ℝ × ℝ => (p.2 - Real.pi / 2) / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-1)) := by
    have hsmc : ∀ w θ : ℝ, |w - w₀| < Real.pi / 2 + 1 → |θ - Real.pi / 2| < Real.pi / 2 + 1 →
        ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) (w, θ) :=
      fun _ _ _ _ => ContDiffAt.cos contDiffAt_snd
    have hzc : ∀ w : ℝ, |w - w₀| < Real.pi / 2 + 1 → Real.cos (Real.pi / 2) = 0 :=
      fun _ _ => Real.cos_pi_div_two
    have h1 : Filter.Tendsto (fun p : ℝ × ℝ => Real.cos p.2 / (p.2 - Real.pi / 2))
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
        (𝓝 (-1)) := by
      have h0 := (tendsto_slice_quotient (f := fun _ θ : ℝ => Real.cos θ) (w₀ := w₀)
        (θ₀ := Real.pi / 2) (δ := Real.pi / 2 + 1) (by linarith [Real.pi_pos]) hsmc
        hzc).mono_left (sector_le_box w₀ (Real.pi / 2 + 1) (by linarith [Real.pi_pos]))
      simpa [Real.deriv_cos, Real.sin_pi_div_two] using h0
    have h2 : Filter.Tendsto (fun p : ℝ × ℝ => (Real.cos p.2 / (p.2 - Real.pi / 2))⁻¹)
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
        (𝓝 (-1)) := by
      have h0 := h1.inv₀ (by norm_num : (-1 : ℝ) ≠ 0)
      simpa using h0
    exact h2.congr' (Eventually.of_forall fun p => inv_div _ _)
  -- (3) the product is the quotient of the statement
  have hprod : Filter.Tendsto
      (fun p : ℝ × ℝ =>
        (Φ p.1 p.2 τ / (p.2 - Real.pi / 2)) * ((p.2 - Real.pi / 2) / Real.cos p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) * (-1))) :=
    hslope.mul hcosq
  have key : Filter.Tendsto
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) * (-1))) :=
    hprod.congr' (by
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [Work.FTS.BSIdent.PhiOdd_of_nonneg (Φ := Φ) (z := p.1) (θ := p.2) (τ := τ)
        (le_of_lt hp.2.1)]
      have h1 : p.2 - Real.pi / 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp.2.2)
      have h2 : Real.cos p.2 ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hp.2.2⟩)
      have h3 : p.2 * 2 - Real.pi ≠ 0 := fun hcon => h1 (by linarith)
      field_simp)
  simpa [mul_neg, mul_one] using key

end Work.FTS.BSIdent.Weyl.Levels
