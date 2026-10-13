import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.radialMatchedMajorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMulHkSqSliceLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPsi6TermBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkLeafSqFKf
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinPow
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinSqLeibniz
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinSqMulSliceLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- **The level-six `ℋ⁶`-energy of the piece `sin²θ·(FK f)·f`**: for a datum
`DatData α f M` (so `√(HkSq α 4 f) ≤ M`) and `α ∈ (0,1]`,

  `HkSq α 6 (fun z θ => sin²θ · FK f z · f z θ) ≤ C · M² · HkSq α 6 f`.

Route (two of the three steps have proved templates in the tree):

1. **Pointwise σ²-multiplier comparison**: for every `m ≤ 6`, `SmoothOpen g` and `(z,θ)`,
   `HkIntegrand α m (fun z θ => sin²θ · g z θ) z θ ≤ Cloc m · HkIntegrand α m g z θ`.
   Proof: `fkSinSqLeibniz` expands the mixed slots as
   `mixed j i (σ²·g) = Σ_{r ≤ i} C(i,r) · DthIter r σ² · mixed j (i-r) g` on the open quadrant
   (`SmoothOpen σ²` is `fkSinSqLeibniz_sinSq_smoothOpen`), and `fkSinPow` gives
   `|DthIter r σ²| ≤ Ksin r · σ²` for `r ≥ 1` (while `DthIter 0 σ² = σ² ≤ 1`). The factor `σ²`
   is *absorbed by the weight*: with slot weights `Wt α = w·σ^{-γ/2}` and `w·σ^{-η/2}` one has
   `σ²·Wt α ≤ w·σ^{-η/2}` and `σ²·wσ^{-η/2} ≤ wσ^{-η/2}`, because `γ ≤ 2 + η`
   (`γ = 1 + α/10 ≤ 1.1`, `η = 99/100`), so each summand is dominated by a slot of
   `HkIntegrand α m g`. The `D_z`-slots are immediate since `σ²` is `θ`-only
   (`DzIter j (σ²·g) = σ²·DzIter j g`).
2. **θ-integrated matched majorant** (analogue of `FkAux.fkMulHkSqSliceLe` with `g := σ²·f`):
   for a.e. `z ∈ Iz`,
   `∫_θ HkIntegrand α 6 (fun z θ => FK f z · (sin²θ · f z θ)) z θ
      ≤ C · Σ_{b ≤ 6} (DzIter b (FK f) z 0)² · (∫_θ HkIntegrand α (6-b) f z θ)`.
   Proof: `radialMatchedMajorant` with `r := fun z => FK f z`, `g := fun z θ => sin²θ · f z θ`
   (Leibniz hypotheses `leibniz_rad_Dz_cd6`/`leibniz_rad_mixed_cd6`; `FK f` is `C⁶` by
   `contDiffOn6_FK`, `σ²·f` is `C⁶` on `Q0` since `f` is), integrated in `θ` as in
   `fkMulHkSqSliceLe`, using step 1 and `HkMem α (6-b) f` for the slice integrability.
3. **Assembly** (analogue of `FkAux.fkMulHkSqLe`): integrate step 2 in `z`; each term of the
   dominating sum is integrable and `≤ Cb · M² · HkSq α 6 f` by `FkAux.fkPsi6TermBound`.
`HkMem α 6 (fun z θ => sin²θ · FK f z · f z θ)` is conjunct 5 of `Npair6BWork.hkMem_fk_mul`. -/
theorem fkSinSqHkSq : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
        ≤ C * M ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Ca, hCapos, hA⟩ := fkSinSqMulSliceLe
  obtain ⟨Cb, hCbpos, hB⟩ := fkPsi6TermBound
  refine ⟨Ca * (7 * Cb) + 1, by positivity, ?_⟩
  intro α hα f M hD
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hα
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  set G : ℝ → ℝ := fun z => ∑ b ∈ Finset.range 7,
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) with hGdef
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hGdef]
    refine MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => ?_)
    exact (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).1
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) z θ) ≤ Ca * G z := by
    filter_upwards [hA α hα f M hD] with z hz
    rw [hGdef]
    exact hz
  have hmono : Work.Spaces.HkSq α 6
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, Ca * G z := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) (hGint.const_mul Ca) hslice
  have hval : (∫ z in Work.Spaces.Iz, Ca * G z)
      = Ca * ∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
    rw [hGdef, MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
    · exact fun b hb =>
        (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).1
  have hterms : (∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)))
      ≤ ∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) := by
    refine Finset.sum_le_sum fun b hb => ?_
    exact (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).2
  have hsumval : (∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f))
      = 7 * (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, Ca * G z := hmono
    _ = Ca * ∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) := hval
    _ ≤ Ca * ∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hterms (le_of_lt hCapos)
    _ = Ca * (7 * (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f)) := by rw [hsumval]
    _ ≤ (Ca * (7 * Cb) + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by
        nlinarith [hCapos, hCbpos, hSnn, hM2, sq_nonneg M, mul_nonneg hM2 hSnn]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
