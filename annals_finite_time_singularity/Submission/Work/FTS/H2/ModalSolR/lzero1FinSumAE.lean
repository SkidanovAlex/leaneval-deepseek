import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.EllipticEst.ModalSolution.PTB.finSum_lzero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open MeasureTheory Set Filter
open scoped Real Topology BigOperators

/-!
# `ModalSolR/lzero1FinSumAE` — the angular operator on a finite mode sum, almost everywhere

For a finite set `s` of modes and coefficients `a : ℕ → ℝ`, put

  `v θ = ∑_{m ∈ s} a m · eFam m θ`

(`eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is the `m`-th Dirichlet eigenfunction of the
angular operator `Lzero1 = -∂_θθ + ∂_θ(tan θ ·) - 6`).  The two statements proved here are

* **almost everywhere** the operator acts diagonally on the finite sum,
  `Lzero1 v θ = ∑_{m ∈ s} lam m · a m · eFam m θ`,  `lam m = 2m(2m+5)`;
* the `cos θ`-weighted product `Lzero1 v · v · cos θ` is integrable on `Iθ = [0, π/2]`.

The pointwise identity is a finite-sum linearity statement: it holds at every `θ` with
`cos θ ≠ 0`, i.e. at every `θ ∈ Iθ` except the endpoint `π/2` (which is a null set).  The
linearity input is `Work.EllipticEst.ModalSolution.PTB.finSum_lzero`, transported to `Lzero1`
along the definitional bridge `Lzero1_eq_Lzero`; the per-mode eigenvalue relation is
`Gegenbauer.eFam_Lzero`.  Integrability follows because the integrand agrees a.e. on `Iθ` with
the continuous function `(∑ lam m · a m · eFam m) · (∑ a m · eFam m) · cos`, and `Iθ` is
compact.
-/

/-- `θ ≠ π/2` holds almost everywhere on the line (a singleton is null). -/
private lemma ae_ne_pi_half : ∀ᵐ θ ∂(MeasureTheory.volume : Measure ℝ), θ ≠ Real.pi / 2 := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬x ≠ Real.pi / 2} = {Real.pi / 2} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, ne_eq, not_not]
  rw [hset]
  exact measure_singleton _

/-- On `Iθ = [0, π/2]` the only zero of `cos` is the right endpoint: for `θ ∈ Iθ`, `θ ≠ π/2`
one has `cos θ ≠ 0`. -/
private lemma cos_ne_zero_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hne : θ ≠ Real.pi / 2) : Real.cos θ ≠ 0 := by
  rw [Work.Spaces.Iθ] at hθ
  have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hne
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩)

/-- **`Lzero1` on a finite sum of eigenmodes.**  For any finite set `s` of modes, any
coefficients `a`, and any `θ` with `cos θ ≠ 0`, the operator acts mode-wise with the
eigenvalues `lam m = 2m(2m+5)`. -/
private lemma lzero1_finSum_eFam (a : ℕ → ℝ) (s : Finset ℕ) {θ : ℝ}
    (hcos : Real.cos θ ≠ 0) :
    Work.FTS.EllipticEst.Lzero1
        (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      = ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  rw [show Work.FTS.EllipticEst.Lzero1
        (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      = Work.Elliptic.Lzero
          (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0 θ from
    congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero
      (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0) θ]
  exact Work.EllipticEst.ModalSolution.PTB.finSum_lzero a s 0 θ hcos

theorem lzero1FinSumAE (a : ℕ → ℝ) (s : Finset ℕ) :
    (∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ∈ Work.Spaces.Iθ →
      Work.FTS.EllipticEst.Lzero1
          (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        = ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    ∧ MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1
            (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
          * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
        Work.Spaces.Iθ := by
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ∈ Work.Spaces.Iθ →
      Work.FTS.EllipticEst.Lzero1
          (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        = ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    filter_upwards [ae_ne_pi_half] with θ hne hθ
    exact lzero1_finSum_eFam a s (cos_ne_zero_of_mem_Iθ hθ hne)
  refine ⟨hae, ?_⟩
  -- the pointwise identity, as an a.e. equality on the restricted measure
  have hid : (fun θ => Work.FTS.EllipticEst.Lzero1
        (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        θ ∈ Work.Spaces.Iθ :=
      MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
    have hne : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ≠ Real.pi / 2 :=
      MeasureTheory.ae_restrict_of_ae ae_ne_pi_half
    filter_upwards [hmem, hne] with θ h1 h2
    exact lzero1_finSum_eFam a s (cos_ne_zero_of_mem_Iθ h1 h2)
  -- the comparison integrand is continuous, hence integrable on the compact `Iθ`
  have hcont1 : Continuous fun θ : ℝ => ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ :=
    continuous_finsetSum _ (fun m _ =>
      (Work.FTS.PhiStar.Series.continuous_eFam m).const_mul
        (Work.FTS.PhiStar.Gegenbauer.lam m * a m))
  have hcont2 : Continuous fun θ : ℝ => ∑ m ∈ s, a m
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ :=
    continuous_finsetSum _ (fun m _ =>
      (Work.FTS.PhiStar.Series.continuous_eFam m).const_mul (a m))
  have hS : MeasureTheory.Integrable
      (fun θ : ℝ => (∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hcont1.mul hcont2).mul Real.continuous_cos).continuousOn
  -- the two integrands agree a.e. on `Iθ`
  have hcongr : (fun θ : ℝ => (∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.FTS.EllipticEst.Lzero1
          (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ) := by
    filter_upwards [hid] with θ h
    rw [h]
  exact hS.congr hcongr

end Work.FTS.H2.ModalSolR
