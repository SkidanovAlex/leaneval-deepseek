import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `MuHDens` — the angular dominated-convergence step for the `L₁₂`-density

`l12dens_tendsto_of_slot`: a pointwise domination of a family of profiles by `C/sin(2θ)` on the
open quadrant, together with the pointwise convergence of the profiles there and the a.e.
measurability of the angular slices, gives the convergence of the `L₁₂`-densities at every
`s > 0`.

This is `dens_tendsto_of_slot_tendsto` (`E5Aux.dens_tendsto_of_slot_tendsto`) with the two
hypotheses about the *limit* (`hmeasl`, `hdoml`) removed: the dominated-convergence theorem for
the `θ`-integral needs measurability and domination only for the *sequence*.

(The earlier draft of this file contained its own `K_nonneg_of_mem_Iθ` and `K_eq`; the first is
already in `E5Aux2.AbsL12densLe` under exactly that name, and the second is renamed here to
`K_eq_sin_two_mul`.)
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-- `K θ = (3/2)·sin(2θ)·cos θ`. -/
theorem K_eq_sin_two_mul (θ : ℝ) : Work.Spaces.K θ = 3 / 2 * Real.sin (2 * θ) * Real.cos θ := by
  rw [Work.Spaces.K, Real.sin_two_mul]; ring

/-- `K θ = 0` at both endpoints of `Iθ`. -/
theorem K_at_endpoints : Work.Spaces.K 0 = 0 ∧ Work.Spaces.K (Real.pi / 2) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Work.Spaces.K]; simp
  · rw [Work.Spaces.K, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring

/-- The angular density of the family converges, from a domination by `C/sin(2θ)` on the open
quadrant and the pointwise convergence of the profiles there.  Only the *sequence* needs to be
measurable and dominated. -/
theorem l12dens_tendsto_of_slot {Yk : ℕ → ℝ → ℝ → ℝ} {Y : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k : ℕ, ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Yk k s θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hdom : ∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Yk k z θ| ≤ C / Real.sin (2 * θ))
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun k : ℕ => Yk k z θ) Filter.atTop (nhds (Y z θ))) :
    ∀ s ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun k : ℕ => Work.FM.L12dens Work.Spaces.K (Yk k) s)
      Filter.atTop (nhds (Work.FM.L12dens Work.Spaces.K Y s)) := by
  intro s hs
  -- the dominating function `(3C/2)·cos θ`
  have hb : MeasureTheory.Integrable (fun θ : ℝ => 3 * C / 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (continuous_const.mul Real.continuous_cos).continuousOn.integrableOn_compact isCompact_Icc
  -- the pointwise domination of every slice
  have hbound : ∀ k : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * Yk k s θ‖ ≤ 3 * C / 2 * Real.cos θ := by
    intro k
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h2 | h2
      · have hKnn : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem_Iθ hθ
        have hs2 : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        have hkey : Work.Spaces.K θ * (C / Real.sin (2 * θ)) = 3 * C / 2 * Real.cos θ := by
          rw [K_eq_sin_two_mul]; field_simp
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKnn]
        calc Work.Spaces.K θ * |Yk k s θ|
            ≤ Work.Spaces.K θ * (C / Real.sin (2 * θ)) :=
              mul_le_mul_of_nonneg_left (hdom k s θ ⟨hs, h0, h2⟩) hKnn
          _ = 3 * C / 2 * Real.cos θ := hkey
      · subst h2
        rw [Real.norm_eq_abs, K_at_endpoints.2, zero_mul, abs_zero, Real.cos_pi_div_two, mul_zero]
    · subst h0
      rw [Real.norm_eq_abs, K_at_endpoints.1, zero_mul, abs_zero, Real.cos_zero, mul_one]
      linarith [hC]
  -- the a.e. convergence of the slices
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun k : ℕ => Work.Spaces.K θ * Yk k s θ) Filter.atTop
        (nhds (Work.Spaces.K θ * Y s θ)) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h2 | h2
      · exact (hconv s θ ⟨hs, h0, h2⟩).const_mul _
      · subst h2
        have h1 : (fun k : ℕ => Work.Spaces.K (Real.pi / 2) * Yk k s (Real.pi / 2))
            = fun _ : ℕ => (0 : ℝ) := by
          funext k; rw [K_at_endpoints.2, zero_mul]
        have h2' : Work.Spaces.K (Real.pi / 2) * Y s (Real.pi / 2) = 0 := by
          rw [K_at_endpoints.2, zero_mul]
        rw [h1, h2']; exact tendsto_const_nhds
    · subst h0
      have h1 : (fun k : ℕ => Work.Spaces.K 0 * Yk k s 0) = fun _ : ℕ => (0 : ℝ) := by
        funext k; rw [K_at_endpoints.1, zero_mul]
      have h2' : Work.Spaces.K 0 * Y s 0 = 0 := by rw [K_at_endpoints.1, zero_mul]
      rw [h1, h2']; exact tendsto_const_nhds
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun (k : ℕ) (θ : ℝ) => Work.Spaces.K θ * Yk k s θ)
    (f := fun θ : ℝ => Work.Spaces.K θ * Y s θ)
    (bound := fun θ : ℝ => 3 * C / 2 * Real.cos θ)
    (fun k => hmeas k s hs) hb hbound hlim
  simpa only [Work.FM.L12dens, Work.Spaces.Iθ, MeasureTheory.integral_div] using h.div_const s

end Work.FTS.StrongEps.E5Aux2
