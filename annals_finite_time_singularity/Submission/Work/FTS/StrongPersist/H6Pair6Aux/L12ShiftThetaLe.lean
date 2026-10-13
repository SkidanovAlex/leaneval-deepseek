import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaIbp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaEnd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

/- Bound for the `k = 0` term of the `L₁₂·D_θ` slot expansion.

Context: `Work.FTS.TransportS.slotPairing ρ a b u v = ∫_z∫_θ ρ·(D_z^bD_θ^a u)·(D_z^bD_θ^a v)`;
`IsLeafW α a ρ` says `ρ` is one of the three leaf weights `w(z)²sin(2θ)^{-η}`, `w(z)²`,
`w(z)²sin(2θ)^{-γ}` (the last only for `a ≥ 1`); `HkNorm α k f = √(HkSq α k f)` and `HkSq α k`
is the weighted ℋ^k energy of the paper.

The Leibniz expansion of `slotPairing ρ a b (fun z θ => L₁₂ f z * D_θ f z θ)` (with `L₁₂ f`
radial) produces one term per `k ≤ b`, of which the `k = 0` one is
`∫_z L₁₂ f z·(∫_θ ρ z θ·(D_z^bD_θ^{a+1}f)·(D_z^bD_θ^a f))`; the claim below is that its
absolute value is `≤ C·|f|_{ℋ⁴}·|f|²_{ℋ⁶}`.

Planned route: `ρ = w(z)²·sin(2θ)^{-q}` for `q = η`, `0` or `γ`.  Put
`h := fun z θ => D_z^bD_θ^a f z θ` (`SmoothOpen`, since `f` is) and `Φ z := L₁₂ f z·(w z)²`;
on the open quadrant `D_θ h = D_z^bD_θ^{a+1}f` (commutation of `D_θ` with `D_z^b`, e.g.
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen` for `Q0`), so the
double integral is exactly `Work.Coercivity.wip (fun z θ => Φ z·sin(2θ)^{-q}) (D_θ h) h`, to
which `Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp` applies, giving
`(q-1)·∫_z Φ z·(∫_θ cos(2θ)sin(2θ)^{-q}h²)`.  Since `|q-1| ≤ 1` and `|L₁₂ f z| ≤ C₄|f|_{ℋ⁴}`
for `z > 0` (`L12Sup4` at `k = 0`) while `∫_z w²∫_θ sin(2θ)^{-q}h² = ∫∫ρh² ≤ HkSq α 6 f`
(`leaf_slot_le6`), this is `≤ C₄|f|_{ℋ⁴}·HkSq α 6 f`.  The three `IntegrableOn (Iz×ˢIθ)`
hypotheses of `wip_Dth_ibp` are dominated by `C|f|_{ℋ⁴}·HkIntegrand α 7 f` (resp.
`HkIntegrand α 6 f`), jointly integrable by
`Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen`; the `z = 0` slice is killed by `w 0 = 0`. -/
theorem L12ShiftThetaLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f := by
  -- The constant is the one of `L12Sup4`, the uniform bound `|L₁₂ f z| ≤ C₄|f|_{ℋ⁴}`.
  obtain ⟨C₄, hC₄pos, hC₄⟩ := L12Sup4
  refine ⟨C₄, hC₄pos, ?_⟩
  intro α hαIoc f a b ρ hO hmem6 hmem7 h0 hab hρ
  obtain ⟨hα, hα1⟩ := hαIoc
  -- `z > 0` almost everywhere on `Iz` (only `z = 0` is excluded).
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hEq : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hEq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- The pointwise bound on `L₁₂ f`, valid on all of `Iz` (`z = 0` uses `L₁₂ f 0 = 0`).
  have hCbound : ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 f z| ≤ C₄ * Work.Spaces.HkNorm α 4 f := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · rw [← h, h0, abs_zero]
      exact mul_nonneg (le_of_lt hC₄pos) (Work.Spaces.HkNorm_nonneg α 4 f)
    · have hh := hC₄ α f hα hα1 hO hmem6 h0 0 (by norm_num) z h
      simpa using hh
  -- The core estimate for an exponent `q` with `σ^{-q}` dominated by the leaf blocks.
  have main : ∀ (q : ℝ) (ρ : ℝ → ℝ → ℝ),
      |q - 1| ≤ 1 → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      ρ = (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ C₄ * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f := by
    intro q ρ hqabs hqle hq0 hρq hρlem
    subst hρq
    -- The three integrability hypotheses of the angular integration by parts.
    obtain ⟨hi0, hi1, hi2, _hprod, hout, hslice⟩ :=
      Work.FTS.StrongPersist.H6Pair6Aux.ibp_integrable_fts hα hα1 hO hmem6 hmem7 h0 hab hqle hq0
    -- Step A: pull the radial weight `(w z)²` out of the angular integral.
    have hAint : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ := by
      intro z
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    have hA : (∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show Work.Construction.L12 f z *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      rw [hAint z]
      ring
    -- Step B: replace `D_z^bD_θ^{a+1}f` by `D_θ(D_z^bD_θ^a f)` inside the angular integral.
    have hB : (∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hzpos] with z hz
      have hinner : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
        have h2 := Work.FTS.StrongPersist.H6Pair6Aux.dth_mixed_eqOn_Q0 (f := f) hO a b
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ.1, hθ.2⟩)
        have h1 : Work.Spaces.mixed b (a + 1) f z θ
            = Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ := h2.symm
        rw [h1]
      show (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
      rw [hinner]
    -- Step C: identify the iterated integral with the `ρ`-weighted pairing `wip`.
    have hC : (∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ))
        = Work.Coercivity.wip
            (fun z θ => (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-q))
            (Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ))
            (fun z θ => Work.Spaces.mixed b a f z θ) := by
      rw [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
          = ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * ((Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
                * (Real.sin (2 * θ)) ^ (-q))
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    -- The angular integration by parts.
    have hIBP := Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
        (h := fun z θ => Work.Spaces.mixed b a f z θ)
        (Φ := fun z => Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) (q := q)
        (hO.mixed b a) hi0 hi1 hi2
    rw [hA, hB, hC, hIBP]
    -- The remaining one-dimensional estimate.
    exact Work.FTS.StrongPersist.H6Pair6Aux.end_bound_fts (f := f) (a := a) (b := b)
      (q := q) (C₄ := C₄) hα hmem6 hab hqabs hCbound hρlem hout hslice
  -- The three leaf weights.
  rcases hρ with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = w²σ^{-η}`
    subst hρ
    exact main Work.Spaces.eta Work.FTS.TransportS.leafEta
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta, Work.Spaces.gam]; linarith) (fun _ => le_rfl) rfl (Or.inl rfl)
  · -- `ρ = w²`
    subst hρ
    refine main 0 Work.FTS.TransportS.leafOne ?_ (by rw [Work.Spaces.gam]; linarith)
      (fun _ => by rw [Work.Spaces.eta]; norm_num) ?_ (Or.inr (Or.inl rfl))
    · rw [zero_sub, abs_neg, abs_one]
    · funext z θ
      simp [Work.FTS.TransportS.leafOne, Real.rpow_zero]
  · -- `ρ = w²σ^{-γ}` (only for `a ≥ 1`)
    subst hρ
    refine main (Work.Spaces.gam α) (Work.FTS.TransportS.leafGam α) ?_ le_rfl ?_ rfl
      (Or.inr (Or.inr ⟨ha1, rfl⟩))
    · rw [Work.Spaces.gam_sub_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ α / 10)]
      linarith
    · intro ha0; omega

end Work.FTS.StrongPersist.H6Pair6Aux
