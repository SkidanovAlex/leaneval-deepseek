/-
# `SlotSumRadAOpen` — the radial slot sum of `radA α f` under the weak (open) hypotheses

`Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_radA_le'` proves

  `∫_z SlotSum (radA α f) ≤ C·HkSq α 6 f`

for data in the class `H6Adm α f`, i.e. assuming `HQo α 6 f` **and** the vanishing on the
angular boundary lines (`VanishTheta f`) and at the axis (`f 0 θ = pz f 0 θ = 0`).  The three
extra fields are *unused* by that argument: the only things the proof consumes from `H6Adm` are
`hf.reg.1 : SmoothOpen f` and `hf.l12 : L12 f 0 = 0`.  This file re-runs the assembly with the
honest hypotheses `SmoothOpen f`, `HkMem α 7 f`, `L12 f 0 = 0`, which is the form the class-`C`
(`EpsZero`) chapter needs.

The ingredients (all imported, all `sorry`-free):

* `H6Aux.Alt_SlotSum_radA_ptwise` — the pointwise split
  `SlotSum (radA α f) z ≤ 2·S1 z + 2·(L₁₂(Transport f)(0))²·S2 z`, where `S1` is the slot sum of
  `ampA·L₁₂f` and `S2` the slot sum of `ampB/c`;
* `ZopSlotMul_le` — `S1 ≤ Czop(1+KA)²·Su`, `Su` the slot sum of `L₁₂f`;
* `L12SlotSum6` — `∫ Su ≤ C₁·HkSq α 6 f` (needs only `SmoothOpen`, `HkMem α 6`, `L12 f 0 = 0`);
* `Alt_slotSum_ampB_div_le` — `∫ S2 ≤ Cb`, uniformly in `α`;
* `WeakC0_sq_le_HkSq6` (proved below) — `(L₁₂(Transport f)(0))² ≤ Cc0·HkSq α 6 f`, the
  `H6Adm`-free form of `H6Aux.Alt_C0_sq_le_HkSq6`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.StrongPersist.H6Aux.ZopSlotMul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

open Work.Spaces (HkMem HkSq HkNorm)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The projector constant at level six, without the `H6Adm` package.**
`C₀f = L₁₂(Transport f)(0) = L12f (Transport f) 0` is bounded by `HkNorm α 4 f`
(`L3Aux.Transport_L12_zero_le`, which needs only `HkMem α 4 f` — no smoothness, no vanishing),
hence by `HkSq α 6 f` for data with order-seven honesty.  This is
`H6Aux.Alt_C0_sq_le_HkSq6` with the `H6Adm` hypothesis replaced by its `SmoothOpen` field, which
is the only part of `H6Adm` that that proof uses. -/
theorem WeakC0_sq_le_HkSq6 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₀, _hC₀, hb⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  refine ⟨C₀ ^ 2, by positivity, ?_⟩
  intro α hαIoc f hsm hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have habs : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0|
      ≤ C₀ * Work.Spaces.HkNorm α 4 f := hb α f hα hα1 hmem4
  have hmono : Work.Spaces.HkSq α 4 f ≤ Work.Spaces.HkSq α 6 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6
  have h4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      = |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ^ 2 := by rw [sq_abs]
    _ ≤ (C₀ * Work.Spaces.HkNorm α 4 f) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = C₀ ^ 2 * Work.Spaces.HkSq α 4 f := by
        rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt h4]
    _ ≤ C₀ ^ 2 * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

theorem SlotSumRadAOpen :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Construction.L12 f 0 = 0 →
        MeasureTheory.IntegrableOn
          (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
          Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Czop, hCzop, hzopb⟩ := Work.FTS.StrongPersist.H6Aux.ZopSlotMul_le
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := Work.FTS.StrongPersist.L6Aux.L12SlotSum6
  obtain ⟨Cc0, hCc0pos, hC0b⟩ := WeakC0_sq_le_HkSq6
  obtain ⟨Cb, hCbpos, hBb⟩ := Work.FTS.StrongPersist.H6Aux.Alt_slotSum_ampB_div_le
  obtain ⟨KA, hKA, hKAb⟩ := Work.FTS.StrongPersist.H6Aux.Alt_ampA_dzdIter_bound6
  refine ⟨2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb), ?_, ?_⟩
  · have h1 : 0 < Czop * (1 + KA) ^ 2 * C₁ := by
      have hK1 : 0 < 1 + KA := by linarith
      exact mul_pos (mul_pos hCzop (pow_pos hK1 2)) hC₁pos
    have h2 : 0 < Cc0 * Cb := mul_pos hCc0pos hCbpos
    linarith
  intro α hαIoc f hsm hmem7 hl12
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hu6 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z' => Work.Coercivity.L12f f z')
        = fun z' => Work.Construction.L12 f z' := rfl
    rw [hfun]
    exact h
  have hA6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1).mul hu6
  -- abbreviations
  set u : ℝ → ℝ := fun z' => Work.Coercivity.L12f f z' with hu
  set C0 : ℝ := Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 with hC0
  set S1 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z' * u z') z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS1
  set S2 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS2
  set Su : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2 with hSu
  set S3 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS3
  -- `L₁₂f`-slots: integrability and bound
  have hL12i := hC₁b α hα hα1 f hsm hmem6 hl12
  have hExp_eq : (fun z => ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2) = Su := by
    rw [hSu, hu]
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
    rfl
  have hIzIoi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hIoiIz : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz :=
    MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))
  have hUint : MeasureTheory.IntegrableOn Su (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := hL12i.1
    rw [hExp_eq] at h2
    exact h2.congr_set_ae hIoiIz
  have hUbd : (∫ z in Set.Ioi (0 : ℝ), Su z) ≤ C₁ * Work.Spaces.HkSq α 6 f := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C₁ * Work.Spaces.HkSq α 6 f := hL12i.2
    rw [hExp_eq] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the z-multiplier bound
  have hZp : ∀ z ∈ Set.Ioi (0 : ℝ), S1 z ≤ Czop * (1 + KA) ^ 2 * Su z := by
    intro z hz
    have h := hzopb (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z') u KA hKA
      (fun j hj z' hz' => hKAb α hαIoc j hj z' hz')
      (Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1) hu6 z hz
    rwa [hS1, hSu]
  have hS1nn : ∀ z, 0 ≤ S1 z := by
    intro z
    rw [hS1]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS2nn : ∀ z, 0 ≤ S2 z := by
    intro z
    rw [hS2]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS3nn : ∀ z, 0 ≤ S3 z := by
    intro z
    rw [hS3]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS1int : MeasureTheory.IntegrableOn S1 (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (hUint.const_mul (Czop * (1 + KA) ^ 2)) ?_ ?_
    · rw [hS1]
      exact (Work.FTS.StrongPersist.H6Aux.Alt_continuousOn_slotSum (n := 6)
        hA6).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hS1nn z)]
      exact hZp z hz
  have hS1bd : (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ (Czop * (1 + KA) ^ 2) * (∫ z in Set.Ioi (0 : ℝ), Su z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall hS1nn) (hUint.const_mul (Czop * (1 + KA) ^ 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hZp)
    rwa [MeasureTheory.integral_const_mul] at h
  have hS2int : MeasureTheory.IntegrableOn S2 (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := (hBb α hαIoc).1
    rw [← hS2] at h2
    exact h2.congr_set_ae hIoiIz
  have hS2bd : (∫ z in Set.Ioi (0 : ℝ), S2 z) ≤ Cb := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ Cb := (hBb α hαIoc).2
    rw [← hS2] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the pointwise majorant
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), S3 z ≤ 2 * S1 z + (2 * C0 ^ 2) * S2 z := by
    intro z hz
    rw [hS3, hS1, hS2, hC0]
    simp only
    rw [← Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_eq
      (Work.FTS.CoercivityFix.Transfer.radA α f) z]
    exact Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_radA_ptwise hα hα1 f hsm hmem7 hz
  have hMono : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hS3nn)
      ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  have hSplit : (∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z))
      = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
        + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := by
    rw [MeasureTheory.integral_add (hS1int.const_mul 2) (hS2int.const_mul (2 * C0 ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hC0sq : C0 ^ 2 ≤ Cc0 * Work.Spaces.HkSq α 6 f := by
    rw [hC0]
    exact hC0b α hαIoc f hsm hmem7
  have hCz : 0 ≤ Czop * (1 + KA) ^ 2 := mul_nonneg hCzop.le (sq_nonneg _)
  have hS2nnint : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), S2 z := integral_nonneg hS2nn
  have hstep1 : 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact hS1bd.trans (mul_le_mul_of_nonneg_left hUbd hCz)
  have hstep2 : (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z)
      ≤ (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := by
    have hb0 : 0 ≤ 2 * (Cc0 * Work.Spaces.HkSq α 6 f) :=
      le_trans (by positivity)
        (mul_le_mul_of_nonneg_left hC0sq (by norm_num))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hC0sq (by norm_num)) hS2bd
      hS2nnint hb0
  have hchain : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
    calc (∫ z in Set.Ioi (0 : ℝ), S3 z)
        ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) := hMono
      _ = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
            + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := hSplit
      _ ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f))
            + (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := add_le_add hstep1 hstep2
      _ = (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
          ring
  have hS3_eq : Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f)
      = S3 := by
    rw [hS3]
    funext z
    exact Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_eq _ z
  refine ⟨?_, ?_⟩
  · have h2 : MeasureTheory.IntegrableOn S3 (Set.Ioi (0 : ℝ)) := by
      refine Integrable.mono' ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2))) ?_ ?_
      · rw [hS3]
        exact (Work.FTS.StrongPersist.H6Aux.Alt_continuousOn_slotSum (n := 6)
          (Work.FTS.StrongPersist.H6Aux.contDiffOn_six_radA hα hα1 hsm hmem7)
          ).aestronglyMeasurable measurableSet_Ioi
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hS3nn z)]
        exact hpt z hz
    have h3 : MeasureTheory.IntegrableOn S3 Work.Spaces.Iz := h2.congr_set_ae hIzIoi
    rwa [← hS3_eq] at h3
  · have h2 : (∫ z in Work.Spaces.Iz, S3 z)
        ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
      rw [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm]
      exact hchain
    rwa [← hS3_eq] at h2

end Work.FTS.StrongEps.EpsZero.ClassCHk
