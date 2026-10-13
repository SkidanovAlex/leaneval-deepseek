import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.integral_mixed_mul_adjMixed_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weak (test-function) convergence of a slot family

The target `weak_slots_tendsto_open` produces, for a sequence `V n` which is `C^∞` on the open
quadrant, converges pointwise on `Q0` to `R` and is locally uniformly bounded, a limit for the
pairings `∫_{Q0} (mixed j i (V n)) φ` against a test function `φ ∈ C_c^∞(Q0)`.

The slot derivatives of `V n` need not converge (no equi-continuity is assumed), so the argument
moves the derivatives onto the test function: by the formal adjointness
`integral_mixed_mul_adjMixed_open` the pairing equals `∫_{Q0} (V n) · adjMixed (j,i) φ`, and
`adjMixed (j,i) φ` is a *fixed* test function, so the dominated convergence theorem applies on its
(compact) support.

The measure-theoretic step is isolated first, in the reusable form
`tendsto_setIntegral_mul_of_pointwise_of_bound`. -/

/-- **Pairing a pointwise convergent, locally bounded family against a test function.**
If `W n` is continuous on the open quadrant `Q0` and converges pointwise to `L` there, and if the
family is bounded on every compact subset of `Q0`, then for every `ψ` which is continuous on `Q0`
with closed support contained in `Q0` the pairings `∫_{Q0} (W n) ψ` converge.

The proof is the dominated convergence theorem on the compact set `tsupport ψ`: off that set `ψ`
vanishes, so all the integrands vanish there; on it the family is bounded by a constant and
converges pointwise. -/
theorem tendsto_setIntegral_mul_of_pointwise_of_bound
    {W : ℕ → ℝ → ℝ → ℝ} {L ψ : ℝ → ℝ → ℝ}
    (hW : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => W n p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hψc : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hKc : IsCompact (tsupport (Function.uncurry ψ)))
    (hψsub : tsupport (Function.uncurry ψ) ⊆ Work.FTS.EllipticEst.Q0)
    (hconv : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => W n q.1 q.2) Filter.atTop (nhds (L q.1 q.2)))
    (hbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ n : ℕ, ∀ q ∈ K, |W n q.1 q.2| ≤ C) :
    Filter.Tendsto (fun n => ∫ p in Work.FTS.EllipticEst.Q0, W n p.1 p.2 * ψ p.1 p.2)
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0, L p.1 p.2 * ψ p.1 p.2)) := by
  classical
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry ψ) with hKdef
  have hKmeas : MeasurableSet K := hKc.measurableSet
  have hQ0meas : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  obtain ⟨C, hCb⟩ := hbnd K hKc hψsub
  set C' : ℝ := max C 0 with hC'def
  -- `ψ` vanishes off its closed support
  have hvan : ∀ p : ℝ × ℝ, p ∉ K → ψ p.1 p.2 = 0 := by
    intro p hp
    by_contra h
    exact hp (subset_tsupport (Function.uncurry ψ)
      (by show Function.uncurry ψ p ≠ 0; exact h))
  -- the dominated convergence theorem, on the measure `volume.restrict K`
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun p : ℝ × ℝ => W n p.1 p.2 * ψ p.1 p.2)
        ((volume : Measure (ℝ × ℝ)).restrict K) := by
    intro n
    exact (((hW n).mul hψc).mono hψsub).aestronglyMeasurable_of_isCompact hKc hKmeas
  have hbndint : Integrable (fun p : ℝ × ℝ => C' * ‖ψ p.1 p.2‖)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖ψ p.1 p.2‖) K := (hψc.mono hψsub).norm
    exact (ContinuousOn.integrableOn_compact hKc hcont).integrable.const_mul C'
  have hbnd' : ∀ n : ℕ, ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict K),
      ‖W n p.1 p.2 * ψ p.1 p.2‖ ≤ C' * ‖ψ p.1 p.2‖ := by
    intro n
    filter_upwards [ae_restrict_mem hKmeas] with p hp
    have hb : |W n p.1 p.2| ≤ C' := le_trans (hCb n p hp) (le_max_left C 0)
    calc ‖W n p.1 p.2 * ψ p.1 p.2‖ = |W n p.1 p.2| * |ψ p.1 p.2| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ C' * |ψ p.1 p.2| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = C' * ‖ψ p.1 p.2‖ := by rw [Real.norm_eq_abs]
  have hlim' : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict K),
      Filter.Tendsto (fun n => W n p.1 p.2 * ψ p.1 p.2) Filter.atTop
        (nhds (L p.1 p.2 * ψ p.1 p.2)) := by
    filter_upwards [ae_restrict_mem hKmeas] with p hp
    exact (hconv p (hψsub hp)).mul_const (ψ p.1 p.2)
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure (ℝ × ℝ)).restrict K)
    (F := fun n (p : ℝ × ℝ) => W n p.1 p.2 * ψ p.1 p.2)
    (f := fun p : ℝ × ℝ => L p.1 p.2 * ψ p.1 p.2)
    (fun p : ℝ × ℝ => C' * ‖ψ p.1 p.2‖) hmeas hbndint hbnd' hlim'
  -- transfer the integrals from the compact support `K` back to the quadrant `Q0`
  have hQK : ∀ (Φ : ℝ × ℝ → ℝ), (∀ p, p ∉ K → Φ p = 0) →
      (∫ p in Work.FTS.EllipticEst.Q0, Φ p) = ∫ p in K, Φ p := by
    intro Φ hΦ
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0meas hψsub
      (fun p hp => hΦ p hp.2)
  have h1 : (fun n => ∫ p in Work.FTS.EllipticEst.Q0, W n p.1 p.2 * ψ p.1 p.2)
      = fun n => ∫ p in K, W n p.1 p.2 * ψ p.1 p.2 :=
    funext (fun n => hQK _ (fun p hp => by rw [hvan p hp, mul_zero]))
  have h2 : (∫ p in Work.FTS.EllipticEst.Q0, L p.1 p.2 * ψ p.1 p.2)
      = ∫ p in K, L p.1 p.2 * ψ p.1 p.2 :=
    hQK _ (fun p hp => by rw [hvan p hp, mul_zero])
  rw [h1, h2]
  exact hDCT

theorem weak_slots_tendsto_open {V : ℕ → Work.FTS.Galerkin.Fn} {R : Work.FTS.Galerkin.Fn} (j i : ℕ)
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hconv : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => V n q.1 q.2) Filter.atTop (nhds (R q.1 q.2)))
    (hR : ContinuousOn (Function.uncurry R) Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ n : ℕ, ∀ q ∈ K, |V n q.1 q.2| ≤ C) :
    ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => ∫ q in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) q.1 q.2 * φ q.1 q.2) Filter.atTop (nhds L) := by
  intro φ hφ hcs hts
  -- the adjoint `ψ = (D_z^j D_θ^i)^* φ` of the slot, a fixed test function
  set ψ : ℝ → ℝ → ℝ := Work.FTS.Apriori.Limit.adjMixed (j, i) φ with hψdef
  have hTestφ : Work.FTS.Apriori.Limit.TestQ φ := by
    refine ⟨?_, hcs, hts⟩
    exact contDiffOn_iff_forall_nat_le.mpr (fun n _ => (hφ n).contDiffOn)
  have hTestψ : Work.FTS.Apriori.Limit.TestQ ψ := by
    rw [hψdef]
    exact (Work.FTS.Apriori.Limit.TestQ_mul_adjMixed hTestφ).2 j i
  -- the adjointness of the slot, applied to each member of the family
  have hIBP : (fun n => ∫ q in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) q.1 q.2 * φ q.1 q.2)
      = fun n => ∫ q in Work.FTS.EllipticEst.Q0, V n q.1 q.2 * ψ q.1 q.2 := by
    funext n
    have h := integral_mixed_mul_adjMixed_open (g := V n) (ψ := φ) (hsm n) hφ hcs hts j i
    rw [hψdef]
    exact h
  refine ⟨∫ q in Work.FTS.EllipticEst.Q0, R q.1 q.2 * ψ q.1 q.2, ?_⟩
  rw [hIBP]
  exact tendsto_setIntegral_mul_of_pointwise_of_bound
    (W := fun n => V n) (L := R) (ψ := ψ)
    (fun n => (hsm n).continuousOn) hTestψ.1.continuousOn hTestψ.2.1.isCompact hTestψ.2.2
    hconv hbnd

end Work.FTS.StrongEps.E5G
