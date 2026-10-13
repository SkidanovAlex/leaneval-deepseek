import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.contDiffOn6_FK
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.radialMatchedMajorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.topSlotZLe
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMulHkSqSliceLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPsi6TermBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 3200000

/-! ## The dominating function on the radial line

`G z = Σ_{b ≤ 6} (D_z^b (FK f)(z))² · ∫_θ HkIntegrand α (6-b) f (z,θ)`: the matched
(releveled) majorant of the level-six integrand of the product `(FK f) · f`, integrated over
the angle.  The three analytic inputs of the crux are

* `fkMulHkSqSliceLe` — the pointwise-in-`θ` matched majorant of `radialMatchedMajorant`,
  integrated over `θ` (a.e. in `z`);
* `fkPsi6TermBound` — integrability of each summand and the level-table bound
  `∫_z (D_z^b (FK f)(z))² · ∫_θ HkIntegrand α (6-b) f ≤ C M² |f|²_{ℋ⁶}`;
* `hkMem_fk_mul` — `(FK f) · f ∈ ℋ⁶` (honesty of the left-hand side).
-/

/-- **The `ℋ⁶`-energy of `(FK f) · f`** is bounded by `C · M² · |f|²_{ℋ⁶}`.

This is the crux of the leaf bound: the level-six integrand of the product is dominated
(summand by summand, with the *matched* level `6 - b` on the datum) by
`(D_z^b (FK f))² · HkIntegrand α (6-b) f`, and each of the seven matched slots is priced by the
table
`b ≤ 3 : |D_z^b(FK f)|² ≤ HkSq α (b+1) f ≤ M²`, `∫ HkIntegrand α (6-b) f ≤ |f|²_{ℋ⁶}`,
`b = 4 : ≤ |f|²_{ℋ⁶} · M²`, `b = 5 : ≤ |f|²_{ℋ⁶} · M²`,
`b = 6 : ∫ (D_z^6(FK f))² ≤ C |f|²_{ℋ⁶}` against `sup_z ∫_θ sin(2θ)^{-η} f² ≤ C M²`. -/
theorem fkMulHkSqLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z * f z θ)
        ≤ C * M ^ 2 * Work.Spaces.HkSq α 6 f := by
  have hA := fkMulHkSqSliceLe
  have hB := fkPsi6TermBound
  obtain ⟨Ca, hCapos, hA⟩ := hA
  obtain ⟨Cb, hCbpos, hB⟩ := hB
  refine ⟨Ca * (7 * Cb) + 1, by positivity, ?_⟩
  intro α hα f M hD
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hα
  have hmem : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * f z θ) :=
    (Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul α hα f M hD).1
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  -- the dominating function and its integrability
  set G : ℝ → ℝ := fun z => ∑ b ∈ Finset.range 7,
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) with hGdef
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hGdef]
    refine MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => ?_)
    exact (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).1
  -- the a.e. slice bound
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => Work.Construction.FK f z * f z θ) z θ) ≤ Ca * G z := by
    filter_upwards [hA α hα f M hD] with z hz
    rw [hGdef]
    exact hz
  -- the monotone `z`-integration
  have hmono : Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, Ca * G z := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) (hGint.const_mul Ca) hslice
  -- the value of the dominating integral
  have hval : (∫ z in Work.Spaces.Iz, Ca * G z)
      = Ca * ∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
    rw [hGdef, MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
    · exact fun b hb =>
        (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).1
  -- the level table
  have hterms : (∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)))
      ≤ ∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) := by
    refine Finset.sum_le_sum fun b hb => ?_
    exact (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).2
  have hsumval : (∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f))
      = 7 * (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, Ca * G z := hmono
    _ = Ca * ∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) := hval
    _ ≤ Ca * ∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hterms (le_of_lt hCapos)
    _ = Ca * (7 * (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f)) := by rw [hsumval]
    _ ≤ (Ca * (7 * Cb) + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by
        nlinarith [hCapos, hCbpos, hSnn, hM2, sq_nonneg M, mul_nonneg hM2 hSnn]

theorem fkLeafSqFKf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (b' a' : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      b' + a' ≤ 6 →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.leafEta z θ
            * (Work.Spaces.mixed b' a' (fun z θ => Work.Construction.FK f z * f z θ) z θ) ^ 2)
        ≤ C * M ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := fkMulHkSqLe
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  intro α hα f M b' a' hD hab
  have hmem : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * f z θ) :=
    (Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul α hα f M hD).1
  have hslot := hC₁ (α := α) (f := fun z θ => Work.Construction.FK f z * f z θ) 6 hα.1 hmem
    a' b' Work.FTS.TransportS.leafEta (by omega) (Or.inl rfl)
  have hprod := hC₀ α hα f M hD
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.leafEta z θ
          * (Work.Spaces.mixed b' a' (fun z θ => Work.Construction.FK f z * f z θ) z θ) ^ 2)
      ≤ C₁ * Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z * f z θ) := hslot
    _ ≤ C₁ * (C₀ * M ^ 2 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hprod (le_of_lt hC₁pos)
    _ = (C₀ * C₁) * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
