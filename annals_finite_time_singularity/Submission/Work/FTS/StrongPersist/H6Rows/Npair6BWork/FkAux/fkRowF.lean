import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowsAux
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.radialMatchedMajorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaEnd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkArith
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- **The generic row bound** for the radial-coefficient pieces `(FK f)·X` at a slot with
`b ≤ 5`: the `D_z`-iterates of `FK f` up to order `5` are bounded by `fkDzdIterSqLe`, and the
`AM–GM`/Cauchy–Schwarz reduction `mixed_radial_mul_le` of the radial Leibniz expansion together
with the pointwise slot pricing `domLeaf_all` gives the estimate. -/
theorem fkRowF : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (X : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → b ≤ 5 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed b a (fun z θ => Work.Construction.FK f z * X z θ) z θ
          = ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)
              * (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
                  * Work.Spaces.mixed (b - b₁) a f z θ)) →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.FK f z * X z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cdzd, hCdzdpos, hdzd⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  refine ⟨(7 * (7 * 4096) * Cdzd + 1) * 2, by positivity, ?_⟩
  intro α hαmem f M a b ρ X hdd hab hb5 hleaf hLeib
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hdd.sm
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdd.bdd
  have hmem : ∀ m ≤ 6, Work.Spaces.HkMem α m f := fun m hm =>
    Work.FTS.OpenPkg.HkMem_mono_open hsm m hm hdd.h6
  have hleaf' : Work.FTS.TransportS.IsLeafW α a ρ := hleaf
  -- the a.e. bounds on the `D_z`-iterates of `FK f`
  have hb₁all : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), ∀ b₁ ∈ Finset.range (b + 1),
      (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        ≤ Cdzd * Work.Spaces.HkSq α (b₁ + 1) f := by
    rw [Finset.eventually_all]
    intro b₁ hb₁
    filter_upwards [hdzd (α := α) (f := f) hαmem.1 hsm hdd.h6 hdd.h7 b₁
      (by have := Finset.mem_range.mp hb₁; omega)] with z hz
    rwa [Work.Elliptic.DzIter_rad] at hz
  -- the pointwise dominated integrand
  have hpt : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed b a (fun z θ => Work.Construction.FK f z * X z θ) z θ|
        * |Work.Spaces.mixed b a f z θ|
      ≤ ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
            * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
            * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ) / 2
        + Work.Spaces.HkIntegrand α 6 f z θ / 2 := by
    filter_upwards [hb₁all] with z hz
    intro hz0 θ hθ0 hθ1
    have hρ : 0 ≤ ρ z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z ⟨hθ0.le, hθ1.le⟩
    have hA := mixed_radial_mul_le (r := fun z => Work.Construction.FK f z) (X := X)
      (X' := f) (V := fun z θ => Work.Spaces.mixed b a f z θ) (a := a) (A := a)
      (b := b) (ρ := ρ) (z := z) (θ := θ) hρ
      (hDz := hLeib z θ hz0 hθ0 hθ1)
      (hCb := fun b₁ hb₁ => hz b₁ hb₁)
    refine le_trans hA ?_
    have hsum : (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
          * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
          * (ρ z θ * (Work.Spaces.mixed (b - b₁) a f z θ) ^ 2))
        ≤ ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
            * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
            * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ := by
      refine Finset.sum_le_sum fun b₁ hb₁ => ?_
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (sq_nonneg _) (mul_nonneg hCdzdpos.le
          (Work.Spaces.HkSq_nonneg α (b₁ + 1) f)))
      exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hleaf' ⟨hθ0, hθ1⟩ (by omega)
    have hV : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hleaf ⟨hθ0, hθ1⟩ (by omega)
    have hnn : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
    linarith [mul_le_mul_of_nonneg_left hsum hnn, hV]
  -- the θ-slice integrability of the dominator
  have hθInt : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.Integrable
      (fun θ => ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
            * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
            * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ) / 2
        + Work.Spaces.HkIntegrand α 6 f z θ / 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ => ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
            * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
            * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrable_finsetSum _ fun b₁ hb₁ =>
        ((hmem ((b - b₁) + a) (by have := Finset.mem_range.mp hb₁; omega)).1 z hz).const_mul _
    have h2 : MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 6 f z θ / 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hmem 6 le_rfl).1 z hz).div_const 2
    exact ((h1.const_mul _).div_const 2).add h2
  -- the value of the θ-integral of the dominator
  -- the value of the θ-integral of the dominator
  have hθVal : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1),
              (b.choose b₁ : ℝ) ^ 2 * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
              * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ) / 2
          + Work.Spaces.HkIntegrand α 6 f z θ / 2))
        = ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
              * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
              * (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ)) / 2
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) / 2 := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ => ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
            * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
            * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrable_finsetSum _ fun b₁ hb₁ =>
        ((hmem ((b - b₁) + a) (by have := Finset.mem_range.mp hb₁; omega)).1 z hz).const_mul _
    have h2 : MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 6 f z θ / 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hmem 6 le_rfl).1 z hz).div_const 2
    have hgi : MeasureTheory.Integrable
        (fun θ => ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1),
            (b.choose b₁ : ℝ) ^ 2 * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
            * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ) / 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (h1.const_mul ((b : ℝ) + 1)).div_const 2
    rw [MeasureTheory.integral_add hgi h2, MeasureTheory.integral_div, MeasureTheory.integral_div]
    have hA : (∫ θ in Work.Spaces.Iθ, ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1),
          (b.choose b₁ : ℝ) ^ 2 * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
          * Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ))
        = ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2
            * (Cdzd * Work.Spaces.HkSq α (b₁ + 1) f)
            * (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α ((b - b₁) + a) f z θ)) := by
      rw [MeasureTheory.integral_const_mul ((b : ℝ) + 1)]
      congr 1
      rw [MeasureTheory.integral_finset_sum _ fun b₁ hb₁ =>
        ((hmem ((b - b₁) + a)
          (by have := Finset.mem_range.mp hb₁; omega)).1 z hz).const_mul _]
      exact Finset.sum_congr rfl fun b₁ _ => MeasureTheory.integral_const_mul _ _
    rw [hA]
  -- TODO (route in Npair6BWork/NOTES_fkRowsC6_ROUTE2.md §2): the two monotone-integration
  -- steps (`hmain`), the evaluation of the double integral (`hval`), and the finite arithmetic.
  -- The pieces above (`hpt`, `hθInt`, `hθVal`) are the analytic core; see the delegated
  -- sibling `FkAux/fkRowDth` and `FkAux/fkRowF6` for the completed shapes.
  sorry

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
