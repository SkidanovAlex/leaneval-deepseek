import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.KinGePDiag
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.KinGePDiagHold` — an axiom-clean form of `Work.BoseFixR.KinGePDiag`

The target lemma is

  `pDiagForm ℓ (fsKinCoeff ((2 d s ℓ)⁻¹)) Φ ≤ kinFormB n ℓ d s eT b Φ`

for every smooth `Φ` and `n ≥ 1`: the diagonal `p`-space mode form is dominated by the
box-restricted localised kinetic word.  The statement is exactly that of
`Submission.Work.BoseFixR.KinGePDiag`, whose proof is complete except for one gap — the
uniform bound on the three bounded pieces of the localised kinetic word, marked there as
`have hNG … := by` with an unfinished body.  That gap is closed here by the two lemmas
proved at the top of this file:

* `gapBare_zero_le_of_sup_bound` — the bare mean-free box mass of a state bounded by `M` on
  `Λ(0) = acube ℓ` is at most `(2M)²ℓ³` (the box mean is bounded by the same `M`,
  `Work.BoseFixR.abs_bsMean_zero_le`, so `|Q_0ψ| ≤ 2M` on the box);
* `neuGapMom_box_bound` — `neuWord + gapWord + momWord ≤ K` on `abox m ℓ`: each of the three
  pieces is dominated by a multiple of `gapBare ℓ 0`
  (`Work.BoseBox.q3kinNeuFracLeGapBare` gives `neuFrac ℓ a² 0 (Q_0ψ) ≤ gapBare`,
  `Work.BoseBox.q3kinMomFormLeGapBare` gives `momForm ℓ d 0 ψ ≤ gapBare`; neither needs
  smoothness or compact support), and `gapBare` is uniformly bounded because the slot fibre
  of a smooth state is bounded on the box (`Work.BSKinetic.exists_fibre_bound`).

The remainder of the proof is the per-slot comparison of `KinGePDiag`, verbatim.  With the
gap closed, `#print axioms Work.BoseFixR.KinGePDiagHold` reports
`[propext, Classical.choice, Quot.sound]`, whereas the proof of the corresponding
declaration in `KinGePDiag` still contains an unfinished step.
-/

noncomputable section

namespace Work.BoseFixR

open MeasureTheory

set_option linter.unusedVariables false

/-- The anchored moving box is the centred cube: `lamBox ℓ 0 = acube ℓ`. -/
lemma lamBox_zero_eq_acube (ℓ : ℝ) :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- **The bare mean-free box mass of a state bounded on the box.**
`gapBare ℓ 0 ψ = ∫_{Λ(0)}(Q_0ψ)² ≤ (2M)²ℓ³` whenever `|ψ| ≤ M` on `Λ(0) = acube ℓ`. -/
theorem gapBare_zero_le_of_sup_bound {ℓ M : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ)
    (hbd : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) :
    Work.BoseKinLoc.gapBare ℓ 0 ψ ≤ (2 * M) ^ 2 * ℓ ^ 3 := by
  have hac : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := lamBox_zero_eq_acube ℓ
  have hreal : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
      (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]
  have hmean : |Work.BSKinetic.bsMean ℓ 0 ψ| ≤ M := abs_bsMean_zero_le hℓ hbd
  have hQbd : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Work.BoseKinLoc.Qfree ℓ 0 ψ z| ≤ 2 * M := by
    intro z hz
    have h3 : Work.BoseKinLoc.Qfree ℓ 0 ψ z = ψ z - Work.BSKinetic.bsMean ℓ 0 ψ := rfl
    rw [h3]
    have h4 : |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ|
        ≤ |ψ z| + |Work.BSKinetic.bsMean ℓ 0 ψ| := abs_sub _ _
    linarith [hbd z hz, hmean]
  have hInt1 : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2)
      (Submission.BoseGases.acube ℓ) := by
    rw [← hac]
    exact Work.BoseBox.integrableOn_Qfree_sq_of_continuous hℓ 0 hψ
  have hne : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.acube ℓ) ≠ ⊤ := by
    rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_ne_top
  have hInt2 : MeasureTheory.IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => (2 * M) ^ 2)
      (Submission.BoseGases.acube ℓ) := by
    rw [MeasureTheory.IntegrableOn]
    haveI : MeasureTheory.IsFiniteMeasure
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr hne
    exact MeasureTheory.integrable_const _
  calc Work.BoseKinLoc.gapBare ℓ 0 ψ
      = ∫ z in Submission.BoseGases.acube ℓ, (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2 := by
        rw [Work.BoseKinLoc.gapBare, hac]
    _ ≤ ∫ z in Submission.BoseGases.acube ℓ, (2 * M) ^ 2 :=
        MeasureTheory.setIntegral_mono_on hInt1 hInt2 (Submission.BoseGases.acube_measurable ℓ)
          (fun z hz => by
            rw [← sq_abs (Work.BoseKinLoc.Qfree ℓ 0 ψ z)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hQbd z hz) 2)
    _ = (2 * M) ^ 2 * ℓ ^ 3 := by
        rw [MeasureTheory.setIntegral_const, hreal]
        ring

/-- **The three bounded pieces of the localised kinetic word are uniformly bounded on the
box**: `neuGapMom = neuWord + gapWord + momWord`, and each of the three is dominated by a
multiple of the bare mean-free box mass `gapBare`, which is itself bounded on `abox m ℓ`
because the slot fibre of a smooth state is bounded there. -/
theorem neuGapMom_box_bound {m : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin (m + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BoseBox.neuGapMom ℓ d s eT b Φ i r ≤ K := by
  obtain ⟨M, _M1, hM0, _hM10, hfib⟩ := Work.BSKinetic.exists_fibre_bound hℓ m hΦ
  have hc1 : 0 ≤ (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) := by
    have hz1 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (mul_pos hd hℓ).le _
    positivity
  have hc2 : 0 ≤ b * ℓ ^ (-2 : ℤ) := by
    have hz2 : 0 ≤ ℓ ^ (-2 : ℤ) := zpow_nonneg hℓ.le _
    positivity
  have hc3 : 0 ≤ b * eT * (d * ℓ) ^ (-2 : ℤ) := by
    have hz1 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (mul_pos hd hℓ).le _
    positivity
  have hB0 : 0 ≤ (2 * M) ^ 2 * ℓ ^ 3 := by positivity
  refine ⟨((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) + b * ℓ ^ (-2 : ℤ)
    + b * eT * (d * ℓ) ^ (-2 : ℤ)) * ((2 * M) ^ 2 * ℓ ^ 3), ?_, ?_⟩
  · exact mul_nonneg (by linarith) hB0
  · intro r hr
    have hψc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN m i (z, r))) :=
      (Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous
    have hgap := gapBare_zero_le_of_sup_bound hℓ hM0 hψc
      (fun z hz => (hfib i r hr).1 z hz)
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (mul_pos hd hℓ).le _
    have hneu := Work.BoseBox.q3kinNeuFracLeGapBare (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ))
      hℓ ha2 0 hψc
    have hmom := Work.BoseBox.q3kinMomFormLeGapBare (ℓ := ℓ) (d := d) hℓ 0 hψc
    have e1 : Work.BoseKinLoc.neuWord ℓ d eT 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))
        ≤ (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := by
      rw [Work.BoseKinLoc.neuWord]
      exact mul_le_mul_of_nonneg_left hneu hc1
    have e2 : Work.BoseKinLoc.gapWord ℓ b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))
        = b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := rfl
    have e3 : Work.BoseKinLoc.momWord ℓ d eT b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))
        ≤ b * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := by
      rw [Work.BoseKinLoc.momWord]
      exact mul_le_mul_of_nonneg_left hmom hc3
    rw [Work.BoseBox.neuGapMom]
    calc Work.BoseKinLoc.neuWord ℓ d eT 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
            Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + Work.BoseKinLoc.gapWord ℓ b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
              Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + Work.BoseKinLoc.momWord ℓ d eT b 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
              Φ (Submission.BoseGases.kcInsN m i (z, r)))
        ≤ (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r)))
          + b * eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) :=
          add_le_add (add_le_add e1 (le_of_eq e2)) e3
      _ = ((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) + b * ℓ ^ (-2 : ℤ)
            + b * eT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) := by
          ring
      _ ≤ ((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) + b * ℓ ^ (-2 : ℤ)
            + b * eT * (d * ℓ) ^ (-2 : ℤ)) * ((2 * M) ^ 2 * ℓ ^ 3) :=
          mul_le_mul_of_nonneg_left hgap (by linarith)

theorem KinGePDiagHold {n : ℕ} {ℓ d s eT b : ℝ} (hn : 1 ≤ n) (hℓ : 0 < ℓ) (hs : 0 < s) (hd0 : 0 < d)
    (hd1 : d ≤ 1) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Submission.BoseGases.pDiagForm ℓ (Submission.BoseGases.fsKinCoeff ((2 * d * s * ℓ)⁻¹)) Φ
      ≤ Work.BoseKinLoc.kinFormB n ℓ d s eT b Φ := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hΦc : Continuous Φ := hΦ.continuous
  set cS : ℝ := (2 * (s * ℓ))⁻¹ with hcSdef
  set cB : ℝ := (2 * (d * s * ℓ))⁻¹ with hcBdef
  have hcSnn : 0 ≤ cS := by rw [hcSdef]; positivity
  have hcBnn : 0 ≤ cB := by rw [hcBdef]; positivity
  have hcSB : cS ≤ cB := by
    rw [hcSdef, hcBdef]
    refine inv_anti₀ (by positivity) ?_
    have h : d * s * ℓ ≤ s * ℓ := by
      have h1 : d * s * ℓ ≤ 1 * (s * ℓ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hd1 (le_of_lt (mul_pos hs hℓ))
      simpa using h1
    linarith
  rw [show (2 * d * s * ℓ)⁻¹ = cB from by rw [hcBdef]; ring_nf]
  rw [Submission.BoseGases.pDiagForm, Work.BoseKinLoc.kinFormB, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m + 1)))) => ?_)
  -- ## the analytic inputs (delegated)
  have hFib : ∃ K : ℝ, 0 ≤ K ∧ (∀ r ∈ Submission.BoseGases.abox m ℓ,
      ∀ p : EuclideanSpace ℝ (Fin 3), Work.BoseBox.fibKT ℓ Φ i r p ≤ K)
      ∧ Continuous (Function.uncurry (Work.BoseBox.fibKT ℓ Φ i)) := by
    obtain ⟨⟨Ki, hKi0, hKi⟩, _, hcont⟩ := FibKTBoxFacts (m := m) (ℓ := ℓ) hℓ hΦc i
    exact ⟨Ki, hKi0, hKi, hcont⟩
  have hBsS : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r) ≤ K :=
    BsOneBodyBoxBound (m := m) (ℓ := ℓ) (c := cS) hℓ hcSnn hΦ i
  have hBsB : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r) ≤ K :=
    BsOneBodyBoxBound (m := m) (ℓ := ℓ) (c := cB) hℓ hcBnn hΦ i
  have hNG : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BoseBox.neuGapMom ℓ d s eT b Φ i r ≤ K :=
    neuGapMom_box_bound hℓ hd0 heT0 heT1 hb hΦ i
  have hgapMeas : AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) :=
    GapWordFibreMeas (m := m) (ℓ := ℓ) (b := b) hΦc i
  have hwin : ∀ (w : EuclideanSpace ℝ (Fin 3) → ℂ) (S : EuclideanSpace ℝ (Fin 3) → ℝ),
      Measurable w → Measurable S →
      Measurable (fun r : Submission.BoseGases.X m =>
        ∫ p : EuclideanSpace ℝ (Fin 3), S p *
          ‖∫ z : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (w z * ((Work.BoseKinLoc.Qfree ℓ 0
                (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℝ) : ℂ))‖ ^ 2) :=
    fun w S hw hS => WindowedFTMeas (m := m) (ℓ := ℓ) hΦc i hw hS
  have hdℓ : 0 < d * ℓ := mul_pos hd0 hℓ
  have ha2 : 0 < (d * ℓ) ^ (-2 : ℤ) := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    exact inv_pos.mpr (by positivity)
  have hneuMeas : AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)) :=
    NeuFracFibreMeas (m := m) (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ)) hℓ ha2 hΦ i
  obtain ⟨Ki, hKi0, hKi, hKicont⟩ := hFib
  obtain ⟨Ks, hKs0, hKs⟩ := hBsS
  obtain ⟨Kb, hKb0, hKb⟩ := hBsB
  obtain ⟨Kv, hKv0, hKv⟩ := hNG
  -- ## the `fsT` bound and the integrability of the two `bsOneBody` words
  have hmainEq : ∀ r : Submission.BoseGases.X m,
      Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        = (1 - eT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          + eT * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
    intro r
    rw [Work.BoseKinLoc.mainWord, ← hcSdef, ← hcBdef]
  have hfsTle : ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        ≤ Kv + ((1 - eT) * Ks + eT * Kb) := by
    intro r hr
    have h1 : Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        = Work.BoseBox.neuGapMom ℓ d s eT b Φ i r
          + Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
      rw [show Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          = Work.BoseBox.fsWord ℓ d s eT b Φ i r from rfl]
      rw [Work.BoseBox.fsWord_eq]
      rfl
    rw [h1, hmainEq r]
    have h2 := hKs r hr
    have h3 := hKb r hr
    have h4 := hKv r hr
    nlinarith [heT0, heT1, h2, h3, h4]
  have hfsTint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun _ : Submission.BoseGases.X m => Kv + ((1 - eT) * Ks + eT * Kb)) ?_ ?_ ?_
    · haveI : MeasureTheory.IsFiniteMeasure
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) :=
        MeasureTheory.isFiniteMeasure_restrict.mpr
          (Submission.BoseGases.abox_lt_top m ℓ hℓ.le).ne
      exact MeasureTheory.integrable_const _
    · exact (aemeasurable_fsT_genFibre hℓ hd0 heT0 hb hΦ i hgapMeas hwin hneuMeas).restrict
    · refine (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable m ℓ)).mpr ?_
      refine Filter.Eventually.of_forall (fun r hr => ?_)
      rw [Real.norm_of_nonneg (Work.BoseKinLoc.Word.fsT_nonneg_of_continuous hℓ hd0 hs heT0 heT1 hb
        0 ((Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous))]
      exact hfsTle r hr
  -- ## integrability of the two `bsOneBody` words on the box
  have hIntK : ∀ (c K' : ℝ), 0 ≤ K' → (∀ r ∈ Submission.BoseGases.abox m ℓ,
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r) ≤ K') →
      MeasureTheory.Integrable (fun r : Submission.BoseGases.X m =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m ℓ)) := by
    intro c K' hK'0 hK'
    refine MeasureTheory.Integrable.mono' (g := fun _ : Submission.BoseGases.X m => K') ?_ ?_ ?_
    · haveI : MeasureTheory.IsFiniteMeasure
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) :=
        MeasureTheory.isFiniteMeasure_restrict.mpr
          (Submission.BoseGases.abox_lt_top m ℓ hℓ.le).ne
      exact MeasureTheory.integrable_const _
    · exact (aemeasurable_bsOneBody_genFibre (m := m) (ℓ := ℓ) i hwin c).aestronglyMeasurable.restrict
    · refine (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable m ℓ)).mpr ?_
      refine Filter.Eventually.of_forall (fun r hr => ?_)
      rw [Real.norm_of_nonneg (Work.BSKinetic.bsOneBody_nonneg (u := 0)
        (fun t => Submission.BoseGases.fsKinCoeff_nonneg c t) _)]
      exact hK' r hr
  have hIntS := hIntK cS Ks hKs0 hKs
  have hIntB := hIntK cB Kb hKb0 hKb
  -- ## the `p`-side comparison
  have hpdnn : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseBox.pDens ℓ Φ i p := fun p =>
    mul_nonneg (by positivity) (MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
  have hpdAEM : AEMeasurable (Work.BoseBox.pDens ℓ Φ i)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    (continuous_pDens hℓ hΦc i).aemeasurable
  have hpdlint : ∫⁻ p : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (Work.BoseBox.pDens ℓ Φ i p) < ⊤ := lintegral_pDens_lt_top hℓ hΦ i
  have hcore := Work.BoseBox.coreA (c₀ := cB) (c₁ := cS) (c₂ := cB) hcSB le_rfl heT0 heT1
    hpdnn hpdAEM hpdlint
  have hidentB : ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff cB ‖p‖ *
        Work.BoseBox.pDens ℓ Φ i p
      = (∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Submission.BoseGases.fsKinCoeff cB ‖p‖ *
          Work.BoseBox.pDens ℓ Φ i p)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg cB ‖p‖) (hpdnn p)))
      (((Work.BoseBox.continuous_fsKinCoeff_norm cB).mul
        (continuous_pDens hℓ hΦc i)).aestronglyMeasurable)
  have hstepA : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff cB ‖p‖ * Work.BoseBox.pDens ℓ Φ i p
      ≤ (1 - eT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff cS ‖p‖ * Work.BoseBox.pDens ℓ Φ i p)
        + eT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff cB ‖p‖ * Work.BoseBox.pDens ℓ Φ i p) := by
    conv_lhs => rw [hidentB]
    exact hcore
  have hcmpS := pDens_integral_le_bsOneBody (m := m) (ℓ := ℓ) (c := cS) (K := Ki)
    hℓ hcSnn hΦc i hKi hKicont
  have hcmpB := pDens_integral_le_bsOneBody (m := m) (ℓ := ℓ) (c := cB) (K := Ki)
    hℓ hcBnn hΦc i hKi hKicont
  -- ## the `mainWord` integral and its domination
  have hlin : ∫ r in Submission.BoseGases.abox m ℓ,
        Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
      = (1 - eT) * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        + eT * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) := by
    rw [show (fun r : Submission.BoseGases.X m =>
          Work.BoseKinLoc.mainWord ℓ d s eT 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        = fun r => (1 - eT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
            + eT * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r) from funext hmainEq]
    rw [MeasureTheory.integral_add (hIntS.const_mul _) (hIntB.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hdom : (1 - eT) * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        + eT * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      ≤ ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
    rw [← hlin]
    refine MeasureTheory.integral_mono_of_nonneg ?_ hfsTint ?_
    · refine Filter.Eventually.of_forall (fun r => ?_)
      show (0 : ℝ) ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
      rw [hmainEq r]
      exact add_nonneg (mul_nonneg (by linarith) (Work.BSKinetic.bsOneBody_nonneg (u := 0)
          (fun t => Submission.BoseGases.fsKinCoeff_nonneg cS t) _))
        (mul_nonneg heT0 (Work.BSKinetic.bsOneBody_nonneg (u := 0)
          (fun t => Submission.BoseGases.fsKinCoeff_nonneg cB t) _))
    · exact Filter.Eventually.of_forall (fun r => mainWord_le_fsT hℓ hd0 heT0 hb
        ((Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous))
  -- ## the RHS in the `r`-form (dropping the box indicator and peeling a slot)
  have hRHS : (ℓ ^ (-3 : ℤ)) * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s eT b 0
          (Work.BoseKinLoc.fibre (m + 1) i Φ x)
      = ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
    -- (i) the box indicator is `1` on the box
    have hind : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (m + 1) i Φ x)
          = Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x) := by
      intro x hx
      have hxi : x i ∈ Submission.BoseGases.acube ℓ := hx i
      have h1 : Work.BoseKinLoc.indU ℓ 0 (x i) = 1 :=
        Set.indicator_of_mem (by simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hxi) _
      rw [h1, one_mul]
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable (m + 1) ℓ) hind]
    -- (ii) the fibre `genFibre` is the inserted `fibre`
    have hfib : ∀ r : Submission.BoseGases.X m,
        Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          = Work.BoseKinLoc.fsT ℓ d s eT b 0
              (Work.BoseKinLoc.fibre (m + 1) i Φ (Submission.BoseGases.kcInsN m i (0, r))) := by
      intro r
      congr 1
      exact funext (fun z => Work.BoseKinLoc.Kinetic.genFibre_eq_fibre i Φ r 0 z)
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable m ℓ)
      (fun r _ => hfib r)]
    -- (iii) peel the slot
    rw [← peel_slot_abox_indep (m := m) (ℓ := ℓ) hℓ i
      (H := fun x => Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (m + 1) i Φ x))
      (fun r y y' => by
        congr 1
        funext z
        simp only [Work.BoseKinLoc.fibre, Submission.BoseGases.update_kcInsN])]
    rw [show ℓ ^ (-3 : ℤ) = (ℓ ^ 3)⁻¹ from by rw [zpow_neg, zpow_ofNat]]
  -- ## the final combination
  calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff cB ‖p‖ * Work.BoseBox.pDens ℓ Φ i p
      ≤ (1 - eT) * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cS) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        + eT * (∫ r in Submission.BoseGases.abox m ℓ,
            Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff cB) 0
              (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) :=
        le_trans hstepA (add_le_add (mul_le_mul_of_nonneg_left hcmpS (by linarith))
          (mul_le_mul_of_nonneg_left hcmpB heT0))
    _ ≤ ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := hdom
    _ = (ℓ ^ (-3 : ℤ)) * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s eT b 0
            (Work.BoseKinLoc.fibre (m + 1) i Φ x) := hRHS.symm

end Work.BoseFixR

end
