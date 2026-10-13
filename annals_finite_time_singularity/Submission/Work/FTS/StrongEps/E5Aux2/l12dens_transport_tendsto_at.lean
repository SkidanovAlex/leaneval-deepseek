import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.StrongEps.E5Aux2.AbsL12densLe
import Submission.Work.FTS.StrongEps.E5Aux2.abs_Transport_slotMaj_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise convergence of the `L₁₂`-density of the transport block

Along the `ε`-scheme (`ε n → 0`), the angular density of the *transport* block of the projected
`J_ε`-slices converges at every `z > 0`:

  `L12dens K (Transport (slice (JfamP ρ (ε n) (G n)) s)) z ⟶ L12dens K (Transport (slice g s)) z`.

The mathematics is a single dominated-convergence theorem in the angular variable:

* the `θ`-integrand is `θ ↦ K θ · Transport f z θ / z = K θ · 3 D_θ f z θ/((1+z)z)`, and
  `D_θ f = mixed 0 1 f` definitionally, so the *slot* convergence
  `mixed 0 1 (JfamP-slice) z θ → mixed 0 1 g z θ` on the open quadrant (`mixed_JfamP_tendsto`, at
  `(j,i) = (0,1)`) gives the pointwise convergence of the integrand at every interior `θ`; at the
  two endpoints `θ = 0, π/2` the factor `K θ` vanishes, so there is nothing to prove;
* the domination is supplied by the `SlotMaj 1` clause of `EpsDecay`, which bounds
  `|D_θ (slice (JfamP ρ (ε n) (G n)) s) z θ|` by `Maj z` for *every* `θ`, whence
  `|K θ · Transport · / z| ≤ K θ · (3 Maj z/(1+z))/z` (the slot-to-transport step is the shared
  lemma `E5Aux2.abs_Transport_slotMaj_le`), a continuous (hence integrable) function
  of `θ` on the compact `Iθ`;
* the a.e. strong measurability of the integrands is the joint continuity hypothesis `hcont`,
  through `MuHGlue.aesm_slice_K_of_contOn` (which only needs continuity on the open quadrant,
  because the two angular endpoints are null in `Iθ`).

This is the `θ`-step feeding the `z`-dominated convergence of the radial functional
`L₁₂(Transport ·)(0)` (`E5Aux2.l12Transport_JfamP_tendsto`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

/-- The transport block in *slot* form: `Transport f z θ = 3 D_θ f z θ/(1+z)` with
`D_θ f = mixed 0 1 f` holds definitionally; the right-hand side is written in the `mixed`-form
used by the slot bounds of `EpsDecay`. -/
private theorem Transport_eq_slot (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.Transport f z θ = 3 * Work.Spaces.mixed 0 1 f z θ / (1 + z) := rfl

theorem l12dens_transport_tendsto_at {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (Work.Coercivity.Transport
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)))
      Work.FTS.EllipticEst.Q0)
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.FM.L12dens Work.Spaces.K
        (Work.Coercivity.Transport
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z)
      Filter.atTop
      (nhds (Work.FM.L12dens Work.Spaces.K
        (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s)) z)) := by
  -- the hypothesis `hsm` in the shape demanded by `mixed_JfamP_tendsto`
  have hsm' : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (Work.FTS.Galerkin.slice (G n) s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n k => by simpa only [Work.FTS.StrongEps.Quad] using hsm n k
  -- **The dominated convergence theorem for the angular integral.**
  have hmain : Filter.Tendsto (fun n : ℕ => ∫ θ,
      Work.Spaces.K θ * Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ / z
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      Filter.atTop (nhds (∫ θ,
        Work.Spaces.K θ * Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s) z θ / z
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (F := fun (n : ℕ) (θ : ℝ) => Work.Spaces.K θ * Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ / z)
      (f := fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice g s) z θ / z)
      (bound := fun θ : ℝ => Work.Spaces.K θ * (3 * Maj z / (1 + z)) / z)
      ?_ ?_ ?_ ?_
    · -- a.e. strong measurability of the integrands, from joint continuity on the open quadrant
      intro n
      have h1 := aesm_slice_K_of_contOn (hcont n) hz
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun θ => (1 / z) * (Work.Spaces.K θ * Work.Coercivity.Transport
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := h1.const_mul (1 / z)
      exact h2.congr (Filter.Eventually.of_forall fun θ => by ring)
    · -- integrability of the majorant (`K` is continuous and `Iθ` is compact)
      exact (((Work.FTS.StrongEps.E5Aux2.continuous_K.mul continuous_const).div_const z)
        |>.continuousOn).integrableOn_compact isCompact_Icc
    · -- the pointwise domination, from the `SlotMaj 1` clause of `EpsDecay`
      intro n
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      have hKnn : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem_Iθ hθ
      have hb : |Work.Coercivity.Transport (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ| ≤ 3 * Maj z / (1 + z) :=
        abs_Transport_slotMaj_le hz
          (fun θ' => (hDec n).2.2.2.1 z hz θ' 0 1 (by norm_num)) θ
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hKnn, abs_of_pos hz]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKnn) hz.le
    · -- a.e. convergence of the integrands (`K` vanishes at the two angular endpoints)
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · have hθ0 : θ = 0 := h0.symm
        rw [hθ0]
        have hK0 : Work.Spaces.K 0 = 0 := by simp [Work.Spaces.K]
        simp only [hK0, zero_mul, zero_div]
        exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · have hθ2 : θ = Real.pi / 2 := h2
          rw [hθ2]
          have hKp : Work.Spaces.K (Real.pi / 2) = 0 := by
            simp [Work.Spaces.K, Real.cos_pi_div_two]
          simp only [hKp, zero_mul, zero_div]
          exact tendsto_const_nhds
        · -- interior: the slot convergence at `(j,i) = (0,1)`
          have hp : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, h0, h2⟩
          have hX := Work.FTS.StrongEps.mixed_JfamP_tendsto hρ hsm' hconv
            (fun n => (hε n).1) hε0 hl12 hp (j := 0) (i := 1) (by norm_num)
          have hT : Filter.Tendsto (fun n : ℕ => Work.Coercivity.Transport
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
              Filter.atTop (nhds (Work.Coercivity.Transport
                (Work.FTS.Galerkin.slice g s) z θ)) := by
            simpa only [Transport_eq_slot] using (hX.const_mul 3).div_const (1 + z)
          simpa only [mul_assoc, mul_div_assoc] using
            ((hT.const_mul (Work.Spaces.K θ)).div_const z)
  simpa only [Work.FM.L12dens, Work.Spaces.Iθ] using hmain

end Work.FTS.StrongEps.E5Aux2
