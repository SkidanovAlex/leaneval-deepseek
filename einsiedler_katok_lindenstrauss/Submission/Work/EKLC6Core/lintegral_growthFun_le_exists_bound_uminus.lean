import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.shapeAvg_lintegral_eq
import Submission.Work.EKLC6Core.HcondSigFree.HcondSig_le_lintegral_atomInfo_mp
import Submission.Work.EKLC6Core.growth_le_HcondSig_mp
import Submission.Work.EKLC6Core.negMulLog_le_sum_mul_negLog
import Submission.Work.EKLC6Core.lintegral_ofReal_shift_sub_le_ae
import Submission.Work.EKLC6Core.AtomInfoSetup
import Submission.Work.EKLC6Core.HcondSig_aux
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.haar_uminus_data_right_scaling_ge_one
import Submission.Work.EKLC6Core.shape_mass_le_leafwise_piece
import Submission.Work.EKLC6Core.Wsh_smul_eq_general
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.integrable_growthFun_uminus_of_plaque
import Submission.Work.EKLC6Core.aemeasurable_atomInfo
import Submission.Work.EKLC6Core.measurableSet_shapeGraph
import Submission.Work.EKLC6Core.measurable_apply_section
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `EKLC6Core.lintegral_growthFun_le_exists_bound_uminus`

The uniform finiteness of the entropy contribution of the stable horospherical subgroup
`U = Uminus t` of `aDiag t` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`: there is a constant `C < ⊤`, depending only
on `t`, such that for every `aDiag t`-invariant probability `μ`, every leaf-wise system `ν` for
`Uminus t`, and every `aDiag t`-descending plaque algebra `A` carried on a `μ`-conull set,

`∫⁻ x, ofReal (growthFun (Uminus t) ν t x) ≤ C`.

## The argument

Let `A` be a `T`-decreasing plaque algebra (`T x = aDiag t • x`) with `μ Zᶜ = 0`, and `ν` a
leaf-wise system for `U = Uminus t`.  Write `B = comap T A` and
`atomInfo A U ν t x = -log (ν x (shape A U x) / ν x (shape B U x)) ≥ 0`.

1. `∫⁻ ofReal (atomInfo A U ν t) ≤ HcondSig μ A B` (`lintegral_atomInfo_le_nocov`, Pisa 7.34/7.35).
2. `HcondSig μ A B ≤ ofReal (log c)`, where `c ≥ 1` is the scaling constant of the Haar measure
   `m` of `Uminus t` under conjugation by `aDiag (-t)` (`hcondSig_le_ofReal_log_scaling` below).
   This is Pisa 7.9/7.55 (the convexity bound `h_μ(a,U) ≤ J`), proved here by the Gibbs
   inequality for the finite partitions defining `HcondSig`: for a.e. `x` the conditional
   probabilities `σ k = ν x (Dpart k x) / ν x (Wsh x)` of the `B`-atom are dominated by the Haar
   weights `τ k = m (Dpart k x) / m (Wsh x)`, and the `ν x`-average of the Haar surprisal
   `hsurpU` integrates back to `∫ (J + hPhiU ∘ T - hPhiU) ≤ J` by the one-sided coboundary
   estimate (`lintegral_ofReal_shift_sub_le_ae`).
3. `∫⁻ ofReal (growthFun U ν t) ≤ ∫⁻ ofReal (atomInfo A U ν t)`
   (`lintegral_growthFun_le_lintegral_atomInfo_horo_ae`, Pisa 7.18/7.34).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The Haar surprisal of an `A`-atom -/

/-- `log` of the Haar mass of the shape of the `A`-atom at `x`. -/
def hPhiU (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3) (A : MeasurableSpace X3) (x : X3) : ℝ :=
  Real.log ((mU (shape A (Uminus t) x)).toReal)

@[simp] theorem hPhiU_def (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3)
    (A : MeasurableSpace X3) (x : X3) :
    hPhiU t mU A x = Real.log ((mU (shape A (Uminus t) x)).toReal) := rfl

/-- `-log (m (shape A U x) / m (shape (comap T A) U x))`, the Haar analogue of the pointwise
surprisal of the `A`-atom inside the `comap T A`-atom. -/
def hsurpU (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3) (A : MeasurableSpace X3)
    (x : X3) : ℝ :=
  Real.log ((mU (Wsh t ⟨A⟩ (Uminus t) x)).toReal) - hPhiU t mU A x

@[simp] theorem hsurpU_def (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3)
    (A : MeasurableSpace X3) (x : X3) :
    hsurpU t mU A x = Real.log ((mU (Wsh t ⟨A⟩ (Uminus t) x)).toReal) - hPhiU t mU A x := rfl

/-- The conditional probability of the `k`-th part of a finite partition with respect to the
pull-back algebra `betaAlg t S`. -/
def ceOfU (t : Fin 3 → ℝ) (μ : MeasureTheory.Measure X3) (S : Work.EKLRelCross.MSAlg)
    (P : @Work.EKLContract.FinPart X3 instMeasurableSpaceX3) (x : X3) (k : Fin P.n) : ℝ :=
  MeasureTheory.condExp (betaAlg t S) μ ((P.parts k).indicator (fun _ => (1 : ℝ))) x

/-- Measurability of `x ↦ mU (shape A U x)` for a measure finite on compacta, a closed subgroup
`U` and a countably generated `A ≤ borel`; the σ-algebra of the domain is kept explicit. -/
theorem measurable_shape_mass_const_lin {U : Subgroup SL3}
    (hUc : IsClosed (U : Set SL3))
    (mU : MeasureTheory.Measure SL3)
    (hfin : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    {A : MeasurableSpace X3}
    (hcount : ∃ b : Set (Set X3), b.Countable ∧ A = MeasurableSpace.generateFrom b)
    (hAb : A ≤ borel X3) :
    @Measurable X3 ENNReal instMeasurableSpaceX3 ENNReal.measurableSpace
      (fun x : X3 => mU (shape A U x)) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  obtain ⟨E, hEmeas, hAgen⟩ := exists_generating_sequence hAb hcount
  have hSmeas : MeasurableSet {p : X3 × SL3 | p.2 ∈ shape A U p.1} := by
    have h := measurableSet_shapeGraph (U := U) (E := E) hUc hEmeas
    rw [← hAgen] at h
    exact h
  have hSect : ∀ x : X3,
      Prod.mk x ⁻¹' {p : X3 × SL3 | p.2 ∈ shape A U p.1} = shape A U x := by
    intro x
    ext u
    simp
  have hfinU : MeasureTheory.IsFiniteMeasureOnCompacts mU := by
    refine ⟨?_⟩
    intro K hK
    exact lt_top_iff_ne_top.mpr (hfin K hK)
  have hmeasU : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable fun _ : X3 => ∫ g, f g ∂(mU) := fun _ => measurable_const
  have hmain := measurable_apply_section (κ := fun _ : X3 => mU) hmeasU (fun _ => hfinU) hSmeas
  have heq : (fun x : X3 => mU (Prod.mk x ⁻¹' {p : X3 × SL3 | p.2 ∈ shape A U p.1}))
      = fun x => mU (shape A U x) := by
    funext x
    rw [hSect x]
  rwa [heq] at hmain

/-! ## The Haar mass of the shapes -/

/-- The Haar mass of the pull-back shape, by the conjugation scaling. -/
theorem mass_WshU_eq (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3) (c : ENNReal)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hscale : ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU (conjBy (-t) s) = c * mU s)
    {x : X3} (hTxZ : aDiag t • x ∈ Z) :
    mU (Wsh t ⟨A⟩ (Uminus t) x) = c * mU (shape A (Uminus t) (aDiag t • x)) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hshape : Wsh t ⟨A⟩ (Uminus t) x = conjBy (-t) (shape A (Uminus t) (aDiag t • x)) := by
    rw [Wsh_def]
    exact hcsg_shape_comap_eq hU A t x
  rw [hshape]
  exact hscale _ (fun u hu => hu.1) (measurableSet_shape hU hplq hTxZ)

/-- The Haar mass of the shape of the `A`-atom at a point of the base set is positive. -/
theorem hPhiU_pos_of_mem (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hposm : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧
      s = o ∩ (Uminus t : Set SL3)) → s.Nonempty → 0 < mU s)
    (hcar : mU ((Uminus t : Set SL3))ᶜ = 0)
    {y : X3} (hyZ : y ∈ Z) : 0 < mU (shape A (Uminus t) y) := by
  obtain ⟨O, hOopen, hOeq⟩ := (hplq.2.2.2 y hyZ).2.2.1
  have hyatom : y ∈ atom A y := by
    rw [Work.EKLContract.atom, Set.mem_sInter]
    rintro s ⟨-, hs⟩
    exact hs
  have h1shape : (1 : SL3) ∈ shape A (Uminus t) y :=
    ⟨(Uminus t).one_mem, by rw [one_smul]; exact hyatom⟩
  have h1O : (1 : SL3) ∈ O := by rw [hOeq] at h1shape; exact h1shape.1
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hUc : MeasurableSet ((Uminus t : Set SL3)) := hU.1.measurableSet
  have hsplit : mU (O ∩ (Uminus t : Set SL3)) + mU (O \ (Uminus t : Set SL3)) = mU O :=
    measure_inter_add_sdiff O hUc
  have hcompl : mU (O \ (Uminus t : Set SL3)) = 0 :=
    measure_mono_null (fun z hz => hz.2) hcar
  have hval : mU O = mU (O ∩ (Uminus t : Set SL3)) := by
    rw [← hsplit, hcompl, add_zero]
  rw [hOeq]
  exact hposm (O ∩ (Uminus t : Set SL3)) ⟨O, hOopen, rfl⟩
    ⟨(1 : SL3), ⟨h1O, (Uminus t).one_mem⟩⟩

/-- The Haar mass of the shape of the `A`-atom at a point of the base set is finite
(the shape is entrywise bounded). -/
theorem hPhiU_lt_top_of_mem (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hfinm : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    {y : X3} (hyZ : y ∈ Z) : mU (shape A (Uminus t) y) < ⊤ := by
  obtain ⟨C, hC⟩ := (hplq.2.2.2 y hyZ).2.2.2
  refine lt_of_le_of_lt (measure_mono ?_)
    (lt_top_iff_ne_top.mpr
      (hfinm _ (Work.EKLProd.sl3EntryBox_compact (fun _ _ => -C) (fun _ _ => C))))
  intro u hu i j
  have h := hC u hu i j
  exact ⟨neg_le_of_abs_le h, le_of_abs_le h⟩

/-- The Haar scaling identity in logarithmic form. -/
theorem log_mass_WshU (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3) (c : ENNReal)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hposm : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧
      s = o ∩ (Uminus t : Set SL3)) → s.Nonempty → 0 < mU s)
    (hcar : mU ((Uminus t : Set SL3))ᶜ = 0)
    (hfinm : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    (hscale : ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU (conjBy (-t) s) = c * mU s)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    {x : X3} (hTxZ : aDiag t • x ∈ Z) :
    Real.log ((mU (Wsh t ⟨A⟩ (Uminus t) x)).toReal)
      = Real.log c.toReal + hPhiU t mU A (aDiag t • x) := by
  rw [mass_WshU_eq t mU c hplq hscale hTxZ, ENNReal.toReal_mul]
  have hVpos : mU (shape A (Uminus t) (aDiag t • x)) ≠ 0 :=
    ne_of_gt (hPhiU_pos_of_mem t mU hplq hposm hcar hTxZ)
  have hVtop : mU (shape A (Uminus t) (aDiag t • x)) ≠ ⊤ :=
    ne_of_lt (hPhiU_lt_top_of_mem t mU hplq hfinm hTxZ)
  have hct : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hctop⟩
  have hVt : (mU (shape A (Uminus t) (aDiag t • x))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hVpos, hVtop⟩
  rw [Real.log_mul hct hVt]
  rfl

/-- **Monotonicity of the Haar surprisal along the diagonal flow.** -/
theorem hPhiU_le (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3) (c : ENNReal)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hposm : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧
      s = o ∩ (Uminus t : Set SL3)) → s.Nonempty → 0 < mU s)
    (hcar : mU ((Uminus t : Set SL3))ᶜ = 0)
    (hfinm : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    (hscale : ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU (conjBy (-t) s) = c * mU s)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hdec : MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A)
    {x : X3} (hxZ : x ∈ Z) (hTxZ : aDiag t • x ∈ Z) :
    hPhiU t mU A x ≤ Real.log c.toReal + hPhiU t mU A (aDiag t • x) := by
  have hsub : shape A (Uminus t) x ⊆ Wsh t ⟨A⟩ (Uminus t) x :=
    fun u hu => ⟨hu.1, hcsg_atom_mono hdec x hu.2⟩
  have hle : mU (shape A (Uminus t) x) ≤ mU (Wsh t ⟨A⟩ (Uminus t) x) := measure_mono hsub
  have hpos : 0 < (mU (shape A (Uminus t) x)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (hPhiU_pos_of_mem t mU hplq hposm hcar hxZ))
      (ne_of_lt (hPhiU_lt_top_of_mem t mU hplq hfinm hxZ))
  have htop : mU (Wsh t ⟨A⟩ (Uminus t) x) ≠ ⊤ := by
    rw [mass_WshU_eq t mU c hplq hscale hTxZ]
    exact ne_of_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hctop)
      (hPhiU_lt_top_of_mem t mU hplq hfinm hTxZ))
  have hle' : (mU (shape A (Uminus t) x)).toReal
      ≤ (mU (Wsh t ⟨A⟩ (Uminus t) x)).toReal := ENNReal.toReal_mono htop hle
  calc hPhiU t mU A x = Real.log ((mU (shape A (Uminus t) x)).toReal) := rfl
    _ ≤ Real.log ((mU (Wsh t ⟨A⟩ (Uminus t) x)).toReal) := Real.log_le_log hpos hle'
    _ = Real.log c.toReal + hPhiU t mU A (aDiag t • x) :=
        log_mass_WshU t mU c hplq hposm hcar hfinm hscale hc0 hctop hTxZ


/-! ## The Haar mass along the leaf, and the pointwise comparison -/

/-- The Haar mass of the pull-back shape is unchanged along the leaf. -/
theorem m_Wsh_of_mem (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hri : ∀ u ∈ Uminus t, ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU ((fun g : SL3 => g * u) '' s) = mU s)
    {x : X3} (hTxZ : aDiag t • x ∈ Z) {u : SL3}
    (hu : u ∈ Wsh t ⟨A⟩ (Uminus t) x) :
    mU (Wsh t ⟨A⟩ (Uminus t) (u • x)) = mU (Wsh t ⟨A⟩ (Uminus t) x) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hmeas : MeasurableSet (Wsh t ⟨A⟩ (Uminus t) x) := by
    rw [Wsh_def]
    exact measurableSet_shape hU (isPlaqueAlgebra_betaAlg hU hplq t) hTxZ
  rw [Wsh_smul_eq_general t hu]
  exact hri u⁻¹ ((Uminus t).inv_mem hu.1) _
    (fun v hv => hv.1) hmeas

/-- The Haar surprisal along the leaf, written in terms of the mass of the pull-back shape. -/
theorem hsurpU_of_mem_Wsh (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hri : ∀ u ∈ Uminus t, ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU ((fun g : SL3 => g * u) '' s) = mU s)
    {x : X3} (hTxZ : aDiag t • x ∈ Z) {u : SL3}
    (hu : u ∈ Wsh t ⟨A⟩ (Uminus t) x) :
    hsurpU t mU A (u • x)
      = Real.log ((mU (Wsh t ⟨A⟩ (Uminus t) x)).toReal) - hPhiU t mU A (u • x) := by
  simp only [hsurpU_def, hPhiU_def]
  rw [m_Wsh_of_mem t mU hplq hri hTxZ hu]

/-- **The main pointwise comparison**: the Haar surprisal dominates `-log τ` on the piece of the
pull-back shape over the partition element containing `u • x`. -/
theorem negLog_tau_le_hsurpU (t : Fin 3 → ℝ) (mU : MeasureTheory.Measure SL3) (c : ENNReal)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hposm : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧
      s = o ∩ (Uminus t : Set SL3)) → s.Nonempty → 0 < mU s)
    (hcar : mU ((Uminus t : Set SL3))ᶜ = 0)
    (hfinm : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    (hri : ∀ u ∈ Uminus t, ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU ((fun g : SL3 => g * u) '' s) = mU s)
    (hscale : ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU (conjBy (-t) s) = c * mU s)
    (hc1 : 1 ≤ c) (hctop : c ≠ ⊤)
    (hdec : MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A)
    {x : X3} (hTxZ : aDiag t • x ∈ Z) {u : SL3} (huZ : u • x ∈ Z)
    (hu : u ∈ Wsh t ⟨A⟩ (Uminus t) x)
    {C : Set X3} (hC : MeasurableSet[A] C) (huC : u • x ∈ C) :
    - Real.log ((mU (Wsh t ⟨A⟩ (Uminus t) x ∩ {v : SL3 | v • x ∈ C})).toReal
        / (mU (Wsh t ⟨A⟩ (Uminus t) x)).toReal) ≤ hsurpU t mU A (u • x) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  set W : Set SL3 := Wsh t ⟨A⟩ (Uminus t) x with hWdef
  set a : ENNReal := mU (W ∩ {v : SL3 | v • x ∈ C}) with hadef
  set b : ENNReal := mU W with hbdef
  have hle : mU (shape A (Uminus t) (u • x)) ≤ a := by
    have hmem : u • x ∈ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) x := by
      have h1 : u ∈ Wsh t ⟨A⟩ (Uminus t) x := by rw [← hWdef]; exact hu
      rw [Wsh_def, betaAlg_def] at h1
      exact h1.2
    have hsub : atom A (u • x) ⊆ C := hcsg_atom_subset_of_mem hC huC
    have h1 := shape_mass_le_leafwise_piece hU hri hplq t hdec hTxZ huZ hmem
    have h2 : mU (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) (Uminus t) x
          ∩ {v : SL3 | v • x ∈ atom A (u • x)})
        ≤ mU (W ∩ {v : SL3 | v • x ∈ C}) := by
      refine measure_mono ?_
      rintro v ⟨hvW, hvA⟩
      exact ⟨hvW, hsub hvA⟩
    rw [hadef]
    exact le_trans h1 h2
  have hposV : 0 < mU (shape A (Uminus t) (u • x)) :=
    hPhiU_pos_of_mem t mU hplq hposm hcar huZ
  have hltV : mU (shape A (Uminus t) (u • x)) < ⊤ :=
    hPhiU_lt_top_of_mem t mU hplq hfinm huZ
  have hb1 : b = c * mU (shape A (Uminus t) (aDiag t • x)) := by
    rw [hbdef, hWdef]
    exact mass_WshU_eq t mU c hplq hscale hTxZ
  have hposb : 0 < b := by
    rw [hb1]
    exact ENNReal.mul_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hc1))
      (ne_of_gt (hPhiU_pos_of_mem t mU hplq hposm hcar hTxZ))
  have hltb : b < ⊤ := by
    rw [hb1]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hctop)
      (hPhiU_lt_top_of_mem t mU hplq hfinm hTxZ)
  have hposa : 0 < a := lt_of_lt_of_le hposV hle
  have hlta : a < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hltb
  have hlog : Real.log ((mU (shape A (Uminus t) (u • x))).toReal) ≤ Real.log a.toReal :=
    Real.log_le_log (ENNReal.toReal_pos (ne_of_gt hposV) (ne_of_lt hltV))
      (ENNReal.toReal_mono (ne_of_lt hlta) hle)
  have hsurp_eq : hsurpU t mU A (u • x)
      = Real.log b.toReal - Real.log ((mU (shape A (Uminus t) (u • x))).toReal) := by
    rw [hsurpU_of_mem_Wsh t mU hplq hri hTxZ hu]
    simp only [hbdef, hWdef, hPhiU_def]
  have hlogdiv : - Real.log (a.toReal / b.toReal) = Real.log b.toReal - Real.log a.toReal := by
    rw [Real.log_div (ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposa) (ne_of_lt hlta)))
      (ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposb) (ne_of_lt hltb)))]
    ring
  rw [hsurp_eq, hlogdiv]
  linarith [hlog]

/-- For a finite measurable partition of a set of finite `ν`-measure, the normalized masses sum
to `1`. -/
private lemma sum_mass_div_eq_one_lin {α : Type*} [MeasurableSpace α] {ρ : Measure α} {ι : Type*}
    [Fintype ι] {W : Set α} {D : ι → Set α} (hD : ∀ i, MeasurableSet (D i))
    (hd : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (hcov : Set.iUnion D = W)
    (hW0 : ρ W ≠ 0) (hWtop : ρ W ≠ ⊤) :
    ∑ i, (ρ (D i)).toReal / (ρ W).toReal = 1 := by
  have hle : ∀ i, ρ (D i) ≤ ρ W := fun i => by
    rw [← hcov]; exact measure_mono (Set.subset_iUnion D i)
  have hfin : ∀ i, ρ (D i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hWtop (hle i)
  have hsum : ∑ i, ρ (D i) = ρ W := by
    have h := measure_biUnion_finset (μ := ρ) (s := Finset.univ) (f := D)
      (fun i _ j _ hij => hd i j hij) (fun i _ => hD i)
    have hunion : (⋃ b ∈ (Finset.univ : Finset ι), D b) = Set.iUnion D := by
      ext u; simp
    rw [hunion, hcov] at h
    exact h.symm
  have hsumR : ∑ i, (ρ (D i)).toReal = (ρ W).toReal := by
    rw [← ENNReal.toReal_sum (fun i _ => hfin i), hsum]
  have hne : (ρ W).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hW0 hWtop)
  rw [← Finset.sum_div, hsumR, div_self hne]

/-- **The pointwise entropy bound.**  For a.e. `x`, the Shannon entropy of the finite partition `P`
inside its `B`-atom (`B = comap (aDiag t ·) A`) is at most the `ν x`-average of the Haar
surprisal `hsurpU` over the pull-back shape. -/
theorem hsurpU_shapeAvg_bound (t : Fin 3 → ℝ)
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {Z : Set X3} (S : Work.EKLRelCross.MSAlg) (hplq : IsPlaqueAlgebra (Uminus t) Z S.m)
    (hdec : betaAlg t S ≤ S.m)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ (Uminus t) ν X')
    (hmp : MeasurePreserving (fun z : X3 => aDiag t • z) μ μ) (hZ : μ Zᶜ = 0)
    (P : @FinPart X3 instMeasurableSpaceX3) (hP : partSigma P ≤ S.m)
    {mU : Measure SL3} {c : ENNReal}
    (hposm : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧
      s = o ∩ (Uminus t : Set SL3)) → s.Nonempty → 0 < mU s)
    (hcar : mU ((Uminus t : Set SL3))ᶜ = 0)
    (hfinm : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    (hri : ∀ u ∈ Uminus t, ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU ((fun g : SL3 => g * u) '' s) = mU s)
    (hscale : ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU (conjBy (-t) s) = c * mU s)
    (hc1 : 1 ≤ c) (hctop : c ≠ ⊤) :
    ∀ᵐ x ∂μ, ENNReal.ofReal (∑ k : Fin P.n, Real.negMulLog (ceOfU t μ S P x k))
      ≤ shapeAvg t S (Uminus t) ν (fun y => ENNReal.ofReal (hsurpU t mU S.m y)) x := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hX'ae : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hZ
  have hTZmeas : MeasurableSet Z := hplq.1 Z hplq.2.2.1
  have hTZ : μ ((fun z : X3 => aDiag t • z) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hTZmeas.compl.nullMeasurableSet, hZ]
  have hTZae : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hTZ
  have hratio : ∀ᵐ x ∂μ, ∀ k : Fin P.n, ceOfU t μ S P x k
      = (ν x (Wsh t S (Uminus t) x ∩ {u : SL3 | u • x ∈ P.parts k})).toReal
        / (ν x (Wsh t S (Uminus t) x)).toReal := by
    rw [Filter.eventually_all]
    intro k
    have h := hcsg_ae_condExp_eq_shape_ratio hU hL hmp (P.measurable k) hplq hZ
    filter_upwards [h] with x hx
    simpa only [ceOfU, Wsh_def, betaAlg_def] using hx
  have hleaf : ∀ᵐ x ∂μ, ∀ᵐ u ∂(ν x), u ∈ Wsh t S (Uminus t) x → u • x ∈ Z := by
    have h := ae_Wsh_mem_of_null hU hL t hmp hTZmeas.compl hZ hplq hZ
    filter_upwards [h] with x hx
    filter_upwards [hx] with u hu
    intro huW
    exact Set.notMem_compl_iff.mp (hu huW)
  filter_upwards [hX'ae, hZae, hTZae, hratio, hleaf] with x hxX' hxZ hxTZ hxr hxleaf
  set W : Set SL3 := Wsh t S (Uminus t) x with hWdef
  set D : Fin P.n → Set SL3 := fun k => W ∩ {u : SL3 | u • x ∈ P.parts k} with hDdef
  have hDsub : ∀ k, D k ⊆ Wsh t S (Uminus t) x := fun k u hu => by
    simp only [hDdef, hWdef] at hu
    exact hu.1
  have hWmass_pos : 0 < ν x W := (mass_Wsh (S := S) hU hL hplq t hxX' hxTZ).1
  have hWmass_top : ν x W < ⊤ := (mass_Wsh (S := S) hU hL hplq t hxX' hxTZ).2
  have hWmU_pos : 0 < mU W := by
    rw [hWdef, mass_WshU_eq t mU c hplq hscale hxTZ]
    exact ENNReal.mul_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hc1))
      (ne_of_gt (hPhiU_pos_of_mem t mU hplq hposm hcar hxTZ))
  have hWmU_top : mU W < ⊤ := by
    rw [hWdef, mass_WshU_eq t mU c hplq hscale hxTZ]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hctop)
      (hPhiU_lt_top_of_mem t mU hplq hfinm hxTZ)
  have hWmeas : MeasurableSet W := by
    rw [hWdef, Wsh_def]
    exact measurableSet_shape hU (isPlaqueAlgebra_betaAlg hU hplq t) hxTZ
  have hDmeas : ∀ k, MeasurableSet (D k) := fun k => by
    rw [hDdef]
    exact hWmeas.inter
      ((P.measurable k).preimage (continuous_id.smul continuous_const).measurable)
  have hDdisj : ∀ k l : Fin P.n, k ≠ l → Disjoint (D k) (D l) := fun k l hkl => by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    simp only [hDdef] at hu1 hu2
    exact (Set.disjoint_left.mp (P.disjoint hkl)) hu1.2 hu2.2
  have hDcov : Set.iUnion D = W := by
    ext u
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hu⟩
      simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq] at hu
      exact hu.1
    · intro hu
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (by rw [P.cover]; exact Set.mem_univ (u • x))
      exact ⟨k, by simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq]; exact ⟨hu, hk⟩⟩
  have hsum_sigma : ∑ k, ceOfU t μ S P x k = 1 := by
    rw [Finset.sum_congr rfl (fun k _ => hxr k)]
    exact sum_mass_div_eq_one_lin hDmeas hDdisj hDcov (ne_of_gt hWmass_pos) (ne_of_lt hWmass_top)
  have hsum_tau : ∑ k, (mU (D k)).toReal / (mU W).toReal ≤ 1 := by
    rw [sum_mass_div_eq_one_lin hDmeas hDdisj hDcov (ne_of_gt hWmU_pos) (ne_of_lt hWmU_top)]
  have hsigma_nn : ∀ k, 0 ≤ ceOfU t μ S P x k := fun k => by rw [hxr k]; positivity
  have htau_nn : ∀ k, 0 ≤ (mU (D k)).toReal / (mU W).toReal := fun k => by positivity
  have hDleW : ∀ k, mU (D k) ≤ mU W := fun k => by
    simp only [hDdef, hWdef]
    exact measure_mono Set.inter_subset_left
  have hDltW : ∀ k, mU (D k) < ⊤ := fun k => lt_of_le_of_lt (hDleW k) hWmU_top
  have htau_pos : ∀ k, ceOfU t μ S P x k ≠ 0 →
      (mU (D k)).toReal / (mU W).toReal ≠ 0 := by
    intro k hk
    have h1 : (ν x (D k)).toReal / (ν x W).toReal ≠ 0 := by rw [← hxr k]; exact hk
    have h2 : ν x (D k) ≠ 0 := by
      intro h0
      refine h1 ?_
      rw [h0]
      simp
    have hS0 : ν x {u : SL3 | u ∈ Wsh t S (Uminus t) x ∧ u • x ∉ Z} = 0 := by
      have h := MeasureTheory.ae_iff.mp hxleaf
      have hset : {u : SL3 | ¬ (u ∈ Wsh t S (Uminus t) x → u • x ∈ Z)}
          = {u : SL3 | u ∈ Wsh t S (Uminus t) x ∧ u • x ∉ Z} := by
        ext u; simp only [Set.mem_ofPred_eq, Classical.not_imp, Set.mem_setOf_eq]
      rw [← hset]
      exact h
    have h3 : ∃ u ∈ D k, u • x ∈ Z := by
      by_contra hc
      have hc' : ∀ u, u ∈ D k → u • x ∉ Z := by
        intro u hu hux
        exact hc ⟨u, hu, hux⟩
      have hsub : D k ⊆ {u : SL3 | u ∈ Wsh t S (Uminus t) x ∧ u • x ∉ Z} :=
        fun u hu => ⟨hDsub k hu, hc' u hu⟩
      exact h2 (measure_mono_null hsub hS0)
    obtain ⟨u, huD, huZ⟩ := h3
    have huW : u ∈ Wsh t S (Uminus t) x := hDsub k huD
    have huC : u • x ∈ P.parts k := by
      simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq] at huD
      exact huD.2
    have hC : MeasurableSet[S.m] (P.parts k) := hP _ (hcsg_partSigma_mem P k)
    have hmem : u • x ∈ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) S.m) x := by
      rw [Wsh_def, betaAlg_def] at huW
      exact huW.2
    have hsub2 : atom S.m (u • x) ⊆ P.parts k := hcsg_atom_subset_of_mem hC huC
    have h1b := shape_mass_le_leafwise_piece hU hri hplq t hdec hxTZ huZ hmem
    have h2b : mU (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) S.m)
          (Uminus t) x ∩ {v : SL3 | v • x ∈ atom S.m (u • x)}) ≤ mU (D k) := by
      rw [hDdef, hWdef]
      refine measure_mono ?_
      rintro v ⟨hvW, hvA⟩
      exact ⟨hvW, hsub2 hvA⟩
    have hbnd : mU (shape S.m (Uminus t) (u • x)) ≤ mU (D k) := le_trans h1b h2b
    have hposD : mU (D k) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (hPhiU_pos_of_mem t mU hplq hposm hcar huZ) hbnd)
    exact div_ne_zero (ne_of_gt (ENNReal.toReal_pos hposD (ne_of_lt (hDltW k))))
      (ne_of_gt (ENNReal.toReal_pos (ne_of_gt hWmU_pos) (ne_of_lt hWmU_top)))
  have htau_le_one : ∀ k, (mU (D k)).toReal / (mU W).toReal ≤ 1 := by
    intro k
    have hle : mU (D k) ≤ mU W := by
      rw [hDdef]
      exact measure_mono Set.inter_subset_left
    have htop : mU W ≠ ⊤ := ne_of_lt hWmU_top
    have h1 : (mU (D k)).toReal ≤ (mU W).toReal := ENNReal.toReal_mono htop hle
    exact (div_le_one (ENNReal.toReal_pos (ne_of_gt hWmU_pos) (ne_of_lt hWmU_top))).mpr h1
  have htau_log_nn : ∀ k, 0 ≤ - Real.log ((mU (D k)).toReal / (mU W).toReal) :=
    fun k => neg_nonneg.mpr (Real.log_nonpos (by positivity) (htau_le_one k))
  have hgibbs : ∑ k, Real.negMulLog (ceOfU t μ S P x k)
      ≤ ∑ k, ceOfU t μ S P x k
        * (- Real.log ((mU (D k)).toReal / (mU W).toReal)) :=
    negMulLog_le_sum_mul_negLog _ _ hsigma_nn hsum_sigma htau_nn hsum_tau htau_pos
  have hofReal_ce : ∀ k, ENNReal.ofReal (ceOfU t μ S P x k)
      = ν x (D k) / (ν x W) := by
    intro k
    rw [hxr k]
    have hDk : D k = W ∩ {u : SL3 | u • x ∈ P.parts k} := by simp only [hDdef]
    rw [hDk]
    exact ofReal_toReal_div_eq
      (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hWmass_top))
      (ne_of_gt hWmass_pos) (ne_of_lt hWmass_top)
  have hterm : ∀ k : Fin P.n, ENNReal.ofReal (ceOfU t μ S P x k
        * (- Real.log ((mU (D k)).toReal / (mU W).toReal)))
      ≤ (∫⁻ u in D k, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x)) / (ν x W) := by
    intro k
    have hkey : ν x (D k) * ENNReal.ofReal
        (- Real.log ((mU (D k)).toReal / (mU W).toReal))
        ≤ ∫⁻ u in D k, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x) := by
      have hpt : ∀ᵐ u ∂((ν x).restrict (D k)), ENNReal.ofReal
          (- Real.log ((mU (D k)).toReal / (mU W).toReal))
          ≤ ENNReal.ofReal (hsurpU t mU S.m (u • x)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (hDmeas k),
          MeasureTheory.ae_restrict_of_ae hxleaf] with u huD huWZ
        have huW : u ∈ Wsh t S (Uminus t) x := hDsub k huD
        have huC : u • x ∈ P.parts k := by
          simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq] at huD
          exact huD.2
        have hDk : D k = Wsh t S (Uminus t) x ∩ {v : SL3 | v • x ∈ P.parts k} := by
          simp only [hDdef, hWdef]
        rw [hDk]
        exact ENNReal.ofReal_le_ofReal
          (negLog_tau_le_hsurpU t mU c hplq hposm hcar hfinm hri hscale hc1 hctop hdec
            hxTZ (huWZ huW) huW (hP _ (hcsg_partSigma_mem P k)) huC)
      calc ν x (D k) * ENNReal.ofReal
              (- Real.log ((mU (D k)).toReal / (mU W).toReal))
          = ENNReal.ofReal (- Real.log ((mU (D k)).toReal / (mU W).toReal))
              * ν x (D k) := mul_comm _ _
        _ = ∫⁻ u in D k, ENNReal.ofReal
              (- Real.log ((mU (D k)).toReal / (mU W).toReal)) ∂(ν x) :=
            (MeasureTheory.setLIntegral_const _ _).symm
        _ ≤ ∫⁻ u in D k, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x) :=
            MeasureTheory.lintegral_mono_ae hpt
    calc ENNReal.ofReal (ceOfU t μ S P x k
          * (- Real.log ((mU (D k)).toReal / (mU W).toReal)))
        = (ν x (D k) / (ν x W)) * ENNReal.ofReal
            (- Real.log ((mU (D k)).toReal / (mU W).toReal)) := by
          rw [ENNReal.ofReal_mul (hsigma_nn k), hofReal_ce k]
      _ = (ν x (D k) * ENNReal.ofReal
            (- Real.log ((mU (D k)).toReal / (mU W).toReal))) / (ν x W) := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
      _ ≤ (∫⁻ u in D k, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x)) / (ν x W) :=
          ENNReal.div_le_div_right hkey _
  have hfibre : ENNReal.ofReal (∑ k, ceOfU t μ S P x k
        * (- Real.log ((mU (D k)).toReal / (mU W).toReal)))
      ≤ shapeAvg t S (Uminus t) ν (fun y => ENNReal.ofReal (hsurpU t mU S.m y)) x := by
    rw [shapeAvg_def, ← hWdef]
    have hsum : ∑ k, ∫⁻ u in D k, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x)
        = ∫⁻ u in W, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x) := by
      rw [← hDcov,
        MeasureTheory.lintegral_iUnion (fun k => hDmeas k) (fun i j hij' => hDdisj i j hij')
          (fun u => ENNReal.ofReal (hsurpU t mU S.m (u • x))), tsum_fintype]
    calc ENNReal.ofReal (∑ k, ceOfU t μ S P x k
            * (- Real.log ((mU (D k)).toReal / (mU W).toReal)))
        = ∑ k, ENNReal.ofReal (ceOfU t μ S P x k
            * (- Real.log ((mU (D k)).toReal / (mU W).toReal))) :=
          ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hsigma_nn k) (htau_log_nn k))
      _ ≤ ∑ k, (∫⁻ u in D k, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x)) / (ν x W) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (∑ k, ∫⁻ u in D k, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x)) / (ν x W) := by
          conv_rhs => rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => ENNReal.div_eq_inv_mul)
      _ = (∫⁻ u in W, ENNReal.ofReal (hsurpU t mU S.m (u • x)) ∂(ν x)) / (ν x W) := by
          rw [hsum]
  calc ENNReal.ofReal (∑ k, Real.negMulLog (ceOfU t μ S P x k))
      ≤ ENNReal.ofReal (∑ k, ceOfU t μ S P x k
          * (- Real.log ((mU (D k)).toReal / (mU W).toReal))) :=
        ENNReal.ofReal_le_ofReal hgibbs
    _ ≤ shapeAvg t S (Uminus t) ν (fun y => ENNReal.ofReal (hsurpU t mU S.m y)) x := hfibre

/-! ## The conditional entropy bound and the target -/

/-- **Pisa 7.9/7.55 for `U = Uminus t`**: the σ-algebra conditional entropy of a `T`-decreasing
plaque algebra is at most the logarithm of the Haar scaling constant of `conjBy (-t)`. -/
theorem hcondSig_le_ofReal_log_scaling
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ (Uminus t) ν X')
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A)
    {mU : Measure SL3} {c : ENNReal}
    (hposm : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧
      s = o ∩ (Uminus t : Set SL3)) → s.Nonempty → 0 < mU s)
    (hcar : mU ((Uminus t : Set SL3))ᶜ = 0)
    (hfinm : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    (hri : ∀ u ∈ Uminus t, ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU ((fun g : SL3 => g * u) '' s) = mU s)
    (hscale : ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU (conjBy (-t) s) = c * mU s)
    (hc1 : 1 ≤ c) (hctop : c ≠ ⊤) :
    @HcondSig X3 instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A)
      ≤ ENNReal.ofReal (Real.log c.toReal) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hc0 : c ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hc1)
  have hJ : 0 ≤ Real.log c.toReal := by
    have h1 : (1 : ENNReal).toReal ≤ c.toReal := ENNReal.toReal_mono hctop (by simpa using hc1)
    have h2 : (1 : ℝ) ≤ c.toReal := by simpa using h1
    exact Real.log_nonneg h2
  have hmeasPhi : Measurable (fun x : X3 => mU (shape A (Uminus t) x)) :=
    measurable_shape_mass_const_lin hU.1 mU hfinm hplq.2.1 hplq.1
  have hmeasW : Measurable (fun x : X3 => mU (Wsh t ⟨A⟩ (Uminus t) x)) := by
    have hA' : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ borel X3 :=
      comap_le_borel_of_le hplq.1 t
    have hcount' : ∃ b' : Set (Set X3), b'.Countable ∧
        MeasurableSpace.comap (fun y : X3 => aDiag t • y) A
          = MeasurableSpace.generateFrom b' := by
      obtain ⟨b, hbc, hbA⟩ := hplq.2.1
      exact ⟨Set.preimage (fun y : X3 => aDiag t • y) '' b, hbc.image _, by
        rw [hbA, MeasurableSpace.comap_generateFrom]⟩
    have h := measurable_shape_mass_const_lin hU.1 mU hfinm hcount' hA'
    simpa only [Wsh_def, betaAlg_def] using h
  have hPhi_ae : AEMeasurable (hPhiU t mU A) μ :=
    (Real.measurable_log.comp hmeasPhi.ennreal_toReal).aemeasurable
  have hsurp_meas : Measurable (hsurpU t mU A) :=
    (Real.measurable_log.comp hmeasW.ennreal_toReal).sub
      (Real.measurable_log.comp hmeasPhi.ennreal_toReal)
  have hTZmeas : MeasurableSet Z := hplq.1 Z hplq.2.2.1
  have hTZ : μ ((fun z : X3 => aDiag t • z) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hTZmeas.compl.nullMeasurableSet, hZ]
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hZ
  have hTZae : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hTZ
  have hle_ae : ∀ᵐ x ∂μ, hPhiU t mU A x
      ≤ Real.log c.toReal + hPhiU t mU A (aDiag t • x) := by
    filter_upwards [hZae, hTZae] with x hxZ hxTZ
    exact hPhiU_le t mU c hplq hposm hcar hfinm hscale hc0 hctop hdec hxZ hxTZ
  rw [HcondSig]
  refine iSup_le ?_
  rintro ⟨P, hP⟩
  have hb := hsurpU_shapeAvg_bound t ⟨A⟩ hplq hdec hL hmp hZ P hP
    hposm hcar hfinm hri hscale hc1 hctop
  change ENNReal.ofReal (@Hcond X3 instMeasurableSpaceX3 μ P
      (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A))
      ≤ ENNReal.ofReal (Real.log c.toReal)
  calc ENNReal.ofReal (@Hcond X3 instMeasurableSpaceX3 μ P
        (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A))
      = ENNReal.ofReal (∫ x, ∑ k : Fin P.n,
          Real.negMulLog (ceOfU t μ ⟨A⟩ P x k) ∂μ) := by
        rw [Hcond]; rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal (∑ k : Fin P.n,
          Real.negMulLog (ceOfU t μ ⟨A⟩ P x k)) ∂μ :=
        ofReal_integral_le_lintegral_ofReal' _
    _ ≤ ∫⁻ x, shapeAvg t ⟨A⟩ (Uminus t) ν
          (fun y => ENNReal.ofReal (hsurpU t mU A y)) x ∂μ :=
        lintegral_mono_ae hb
    _ = ∫⁻ x, ENNReal.ofReal (hsurpU t mU A x) ∂μ :=
        shapeAvg_lintegral_eq hU hL t hmp (S := ⟨A⟩) hplq hZ _
          hsurp_meas.ennreal_ofReal
    _ = ∫⁻ x, ENNReal.ofReal ((Real.log c.toReal) + hPhiU t mU A (aDiag t • x)
          - hPhiU t mU A x) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hZae, hTZae] with x _ hxTZ
        rw [hsurpU_def, log_mass_WshU t mU c hplq hposm hcar hfinm hscale hc0 hctop hxTZ]
    _ ≤ ENNReal.ofReal (Real.log c.toReal) :=
        lintegral_ofReal_shift_sub_le_ae hmp hPhi_ae hJ hle_ae

/-- The pointwise information of the `A`-atom inside its `B`-atom is bounded by the logarithm of
the Haar scaling constant. -/
theorem lintegral_atomInfo_le_ofReal_log_scaling
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ (Uminus t) ν X')
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A)
    {mU : Measure SL3} {c : ENNReal}
    (hposm : ∀ s : Set SL3, (∃ o : Set SL3, IsOpen o ∧
      s = o ∩ (Uminus t : Set SL3)) → s.Nonempty → 0 < mU s)
    (hcar : mU ((Uminus t : Set SL3))ᶜ = 0)
    (hfinm : ∀ K : Set SL3, IsCompact K → mU K ≠ ⊤)
    (hri : ∀ u ∈ Uminus t, ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU ((fun g : SL3 => g * u) '' s) = mU s)
    (hscale : ∀ s : Set SL3, s ⊆ (Uminus t : Set SL3) → MeasurableSet s →
      mU (conjBy (-t) s) = c * mU s)
    (hc1 : 1 ≤ c) (hctop : c ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (atomInfo A (Uminus t) ν t x) ∂μ
      ≤ ENNReal.ofReal (Real.log c.toReal) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  exact le_trans (lintegral_atomInfo_le_nocov (μ := μ) (U := Uminus t) (ν := ν) (X' := X')
      t hL hU hmp (A := A) (Z := Z) hplq hdec hZ)
    (hcondSig_le_ofReal_log_scaling t hmp hL hplq hZ hdec hposm hcar hfinm hri hscale hc1 hctop)

/-! ## The target -/

theorem lintegral_growthFun_le_exists_bound_uminus (t : Fin 3 → ℝ) :
    ∃ C : ENNReal, C < ⊤ ∧
      (∀ (μ : MeasureTheory.Measure Work.EKLContract.X3),
        MeasureTheory.IsProbabilityMeasure μ →
        MeasureTheory.MeasurePreserving
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ →
        ∀ {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
          {X' : Set Work.EKLContract.X3},
          Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X' →
        ∀ {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3},
          Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A →
          μ Zᶜ = 0 →
          MeasurableSpace.comap
            (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A →
          Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) →
          @MeasureTheory.lintegral Work.EKLContract.X3
            Work.EKLContract.instMeasurableSpaceX3 μ
            (fun x => ENNReal.ofReal
              (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x)) ≤ C) := by
  obtain ⟨mU, c, hc1, hctop, hcar, hposm, hfinm, hri, hscale⟩ :=
    haar_uminus_data_right_scaling_ge_one t
  refine ⟨ENNReal.ofReal (Real.log c.toReal), ENNReal.ofReal_lt_top, ?_⟩
  intro μ hprob hmp ν X' hL A Z hplq hZ hdec hmeas
  haveI : MeasureTheory.IsProbabilityMeasure μ := hprob
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    (uminus_isHoro t).2
  have hA1 : ∫⁻ x, ENNReal.ofReal (atomInfo A (Uminus t) ν t x) ∂μ
      ≤ ENNReal.ofReal (Real.log c.toReal) :=
    lintegral_atomInfo_le_ofReal_log_scaling t hmp hL hplq hZ hdec
      hposm hcar hfinm hri hscale hc1 hctop
  have hfinA : ∫⁻ x, ENNReal.ofReal (atomInfo A (Uminus t) ν t x) ∂μ ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hA1 ENNReal.ofReal_lt_top)
  exact le_trans
    (lintegral_growthFun_le_lintegral_atomInfo_horo_ae (μ := μ) (U := Uminus t)
      (ν := ν) (X' := X') t hU hcontr hmp hL hplq hdec hZ hfinA) hA1

end Work.EKLC6Core
