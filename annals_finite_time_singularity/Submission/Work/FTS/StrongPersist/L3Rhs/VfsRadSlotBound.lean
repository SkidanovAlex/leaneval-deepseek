import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Aux.L12f_slot_le
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.sum_sq_binom_le
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

/-
Intended namespace: `Work.FTS.StrongPersist.L3Rhs`.
The weighted slot bound for the radial product `z ↦ L₁₂(f)(z) · B(z)` (with `B` an arbitrary
radial factor that is `C⁴` on `(0,∞)` with `Zop`-jets of order `≤ 3` bounded by `24000`):
`∑_{q ≤ 3} (D_z^q (L₁₂ f · B))² w²` is integrable on `Iz` and its integral is bounded by
`C · HkSq α 4 f`.
Route: the Leibniz expansion `DzIter q (fun z _ => L₁₂ f z * B z) z 0
= Σ_{b ≤ q} C(q,b) · (Zop^[b] (L₁₂ f) z) · (Zop^[q-b] B z)` (all `z > 0`), which is
`Work.FTS.FinalClock.DzIter_mul_of_contDiffOn` with the multiplier `fun z => L₁₂ f z` (`C⁴`
on `(0,∞)` by `UopHk.contDiffOn_L12_k` at `k = 4`) and the second factor `fun z => B z`;
then `(D_z^q (L₁₂ f · B) z)² w z ² ≤ C · Σ_{b ≤ 3} (Zop^[b] (L₁₂ f) z)² w z ²`, and each
slot is integrable with integral `≤ C' · HkSq α 4 f` by
`Work.FTS.StrongPersist.L3Aux.L12f_slot_le` (needs `SmoothOpen f`, `HkMem α 4 f`,
`L12 f 0 = 0`, `α ≤ 1`, and slot order `≤ 4`).  `Work.Spaces.Zop_slice` identifies
`Zop^[b] (fun z => φ z)` with `DzIter b (fun z _ => φ z) · 0`.
-/
theorem VfsRadSlotBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (B : ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 → ContDiffOn ℝ 4 B (Set.Ioi (0 : ℝ)) →
    (∀ b ≤ 3, ∀ z ∈ Work.Spaces.Iz, |Work.Spaces.Zop^[b] B z| ≤ 24000) →
    MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Aux.L12f_slot_le
  refine ⟨1024 * 24000 ^ 2 * (4 * C₁) + 1, by positivity, ?_⟩
  intro α f B hα hα1 hsm hmem h0 hB4 hBbound
  have hL4 : ContDiffOn ℝ 4 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem (by norm_num)
  have hLq : ∀ q : ℕ, q ≤ 4 →
      ContDiffOn ℝ (q : ℕ∞) (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
    fun q hq => hL4.of_le (by simp [hq])
  have hBq : ∀ q : ℕ, q ≤ 4 → ContDiffOn ℝ (q : ℕ∞) B (Set.Ioi (0 : ℝ)) :=
    fun q hq => hB4.of_le (by simp [hq])
  have hslot := hC₁ α hα hα1 f hsm hmem h0
  -- ## the Leibniz expansion
  have hexp : ∀ q ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.Zop^[q - b] B z) := by
    intro q hq z hz
    have h1 : Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.DzIter (q - b) (fun z _ => B z) z 0) :=
      Work.FTS.FinalClock.DzIter_mul_of_contDiffOn q (fun z => Work.Construction.L12 f z)
        (fun z _ => B z) isOpen_Ioi (hLq q (by omega)) (hBq q (by omega)) z hz
    rw [h1]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [congrFun (Work.Spaces.Zop_slice (q - b) (fun z _ => B z) 0) z]
  -- ## the pointwise Cauchy–Schwarz bound
  have hpt : ∀ (X Y : ℕ → ℝ) (z : ℝ), z ∈ Set.Ioi (0 : ℝ) → (∀ j ≤ 3, |Y j| ≤ 24000) →
      (∀ q ≤ 3, Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (X b * Y (q - b))) →
      (∑ q ∈ Finset.range 4,
          (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ 1024 * 24000 ^ 2
            * ∑ b ∈ Finset.range 4, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro X Y z _ hY hex
    have hsq : ∀ q ≤ 3,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          ≤ 256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
      intro q hq
      rw [hex q hq]
      exact Work.FTS.StrongPersist.L3Rhs.VfsRadAux.sum_sq_binom_le q hq X Y hY
    have hsum : (∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2)
        ≤ 1024 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
      calc (∑ q ∈ Finset.range 4,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2)
          ≤ ∑ _q ∈ Finset.range 4,
              (256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2) :=
            Finset.sum_le_sum (fun q hq => hsq q (by rw [Finset.mem_range] at hq; omega))
        _ = 4 * (256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = 1024 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by ring
    calc (∑ q ∈ Finset.range 4,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = (∑ q ∈ Finset.range 4,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2)
              * (Work.Spaces.w z) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (1024 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2) * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
      _ = 1024 * 24000 ^ 2
            * ∑ b ∈ Finset.range 4, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          rw [← Finset.sum_mul]; ring
  -- ## abbreviations
  let X : ℕ → ℝ → ℝ := fun b z => Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
  let Y : ℕ → ℝ → ℝ := fun j z => Work.Spaces.Zop^[j] B z
  let G : ℝ → ℝ := fun z => ∑ b ∈ Finset.range 4, (X b z) ^ 2 * (Work.Spaces.w z) ^ 2
  let A : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 4,
      (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2
  have hAnn : ∀ z, 0 ≤ A z := fun z =>
    Finset.sum_nonneg (fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hApt : ∀ z ∈ Set.Ioi (0 : ℝ), A z ≤ 1024 * 24000 ^ 2 * G z := by
    intro z hz
    exact hpt (fun b => X b z) (fun j => Y j z) z hz
      (fun j hj => hBbound j hj z (Set.mem_Ici.mpr (le_of_lt hz)))
      (fun q hq => hexp q hq z hz)
  -- ## integrability of the majorant
  have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum (Finset.range 4)
      (f := fun b z => (X b z) ^ 2 * (Work.Spaces.w z) ^ 2) (fun b hb => ?_)
    have hb4 : b ≤ 4 := by rw [Finset.mem_range] at hb; omega
    refine MeasureTheory.IntegrableOn.congr_fun (hslot b hb4).1 (fun z _ => ?_) measurableSet_Ici
    show (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
    rw [← congrFun (Work.Spaces.Zop_slice b (fun z _ => Work.Construction.L12 f z) 0) z]
  -- ## the value of the majorant integral
  have hGval : (∫ z in Work.Spaces.Iz, G z) ≤ 4 * (C₁ * Work.Spaces.HkSq α 4 f) := by
    have hfun : G = fun z => ∑ b ∈ Finset.range 4,
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
      funext z
      show (∑ b ∈ Finset.range 4,
            (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
          = ∑ b ∈ Finset.range 4,
              (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
                * (Work.Spaces.w z) ^ 2
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← congrFun (Work.Spaces.Zop_slice b (fun z _ => Work.Construction.L12 f z) 0) z]
    rw [hfun]
    calc (∫ z in Work.Spaces.Iz, ∑ b ∈ Finset.range 4,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = ∑ b ∈ Finset.range 4,
            (∫ z in Work.Spaces.Iz,
              (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
                * (Work.Spaces.w z) ^ 2) :=
          MeasureTheory.integral_finsetSum (Finset.range 4)
            (fun b hb => (hslot b (by rw [Finset.mem_range] at hb; omega)).1)
      _ ≤ ∑ _b ∈ Finset.range 4, (C₁ * Work.Spaces.HkSq α 4 f) :=
          Finset.sum_le_sum (fun b hb =>
            (hslot b (by rw [Finset.mem_range] at hb; omega)).2)
      _ = 4 * (C₁ * Work.Spaces.HkSq α 4 f) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  -- ## the a.e. statements
  have hIzcongr : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
  have hae_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      A z ≤ 1024 * 24000 ^ 2 * G z := by
    rw [hIzcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hApt z hz)
  have hae_norm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖A z‖ ≤ 1024 * 24000 ^ 2 * G z := by
    rw [hIzcongr]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnn z)]
    exact hApt z hz
  have hAesm : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum hL4 hB4
  have hAint : MeasureTheory.IntegrableOn A Work.Spaces.Iz :=
    MeasureTheory.Integrable.mono' (hGint.const_mul (1024 * 24000 ^ 2)) hAesm hae_norm
  have hAle : (∫ z in Work.Spaces.Iz, A z)
      ≤ 1024 * 24000 ^ 2 * (∫ z in Work.Spaces.Iz, G z) := by
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (g := fun z => 1024 * 24000 ^ 2 * G z)
      (Filter.Eventually.of_forall hAnn) (hGint.const_mul (1024 * 24000 ^ 2)) hae_le
    rwa [MeasureTheory.integral_const_mul] at hmono
  refine ⟨hAint, ?_⟩
  have hS := Work.Spaces.HkSq_nonneg α 4 f
  calc (∫ z in Work.Spaces.Iz, A z)
      ≤ 1024 * 24000 ^ 2 * (∫ z in Work.Spaces.Iz, G z) := hAle
    _ ≤ 1024 * 24000 ^ 2 * (4 * (C₁ * Work.Spaces.HkSq α 4 f)) :=
        mul_le_mul_of_nonneg_left hGval (by positivity)
    _ = (1024 * 24000 ^ 2 * (4 * C₁)) * Work.Spaces.HkSq α 4 f := by ring
    _ ≤ (1024 * 24000 ^ 2 * (4 * C₁) + 1) * Work.Spaces.HkSq α 4 f := by nlinarith [hS]

end Work.FTS.StrongPersist.L3Rhs
