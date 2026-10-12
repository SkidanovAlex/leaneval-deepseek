import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Sector.fsT_translate
import Submission.Work.BoseKinLoc.Sector.potWordU_shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.word_translate` — translation covariance of the localised box word

FS `eq:Def_HB`'s localised box Hamiltonian is the moving-box family
`H_{Λ,u}(μ)_N`, `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³`.  This module proves that the family is **exactly**
the anchored member `u = 0` conjugated by the translation `x ↦ x + ℓu` of the configuration
space — so the whole moving-box family of quadratic forms is unitarily equivalent to the single
anchored form, which is what the C3 sector decomposition needs:

    `boxForm N v g ℓ μ d s εT b u Φ
       = boxForm N v g ℓ μ d s εT b 0 (fun z => Φ (fun i => ℓ•u + z i))`.

## Proof

Write `c := fun _ : Fin N => ℓ • u` for the constant configuration shift and
`S Φ := fun z => Φ (c + z)` for the translated `N`-body state.  `boxForm` is a sum of two
pieces, and each is handled by a change of variables in the measure-preserving translation
`x ↦ x ± c` of `X N = (ℝ³)^N`:

* **kinetic.** `slotForm N q ℓ u i Φ = ℓ⁻³ ∫_x indU ℓ u (x i) · q(fibre N i Φ x)`; the fibre of
  the translated state is the translate of the fibre,
  `fibre N i (SΦ) x = T_u (fibre N i Φ (x + c))` (`wt_fibre_shift`), and the one-body word is
  translation covariant, `fsT u ψ = fsT 0 (T_u ψ)` (`Sector.fsT_translate`).  The indicator
  `indU` transports by `indU ℓ 0 (z − ℓ•u) = indU ℓ u z` (`wt_indU_shift`), and the shift of the
  integration variable is measure preserving (`wt_integral_shiftN`).  Summing over the slots
  gives `wt_kinForm_shift`.

* **potential.** `potWordU` is a sum of the localised kernels `wLoc`, which transport by
  `wLoc ℓ h u x y = wLoc ℓ h 0 (x − ℓ•u) (y − ℓ•u)` in both slots and in the integrated variable
  (`Sector.potWordU_shift`), while `SΦ (z − c) = Φ z`.  The change of variables
  `wt_integral_shiftN_sub` gives `wt_potInt_shift`.

No hypothesis on the potentials `v, g` or the kinetic parameters is used: every step is either a
pointwise function identity or a change of variables for a measure-preserving map, hence valid
for arbitrary (possibly non-integrable, junk-valued) integrands.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option maxHeartbeats 1000000

/-! ## 1. The indicator of the moving box -/

/-- The indicator `θ_u = 1_{Λ(u)}` of the moving box, transported to the anchored box:
`indU ℓ u z = indU ℓ 0 (z − ℓ•u)`. -/
lemma wt_indU_shift (ℓ : ℝ) (u z : ℝ³) :
    Work.BoseKinLoc.indU ℓ u z = Work.BoseKinLoc.indU ℓ 0 (z - ℓ • u) := by
  rw [Work.BoseKinLoc.indU, Work.BoseKinLoc.indU]
  by_cases h : z ∈ Work.BoseKinLoc.lamBox ℓ u
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, sub_eq_add_neg] using h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, sub_eq_add_neg] using h

/-! ## 2. Translation of the slot fibres -/

/-- The slot-`i` fibre of the translated `N`-body state is the translate of the fibre of the
original state at the translated configuration:
`fibre N i (SΦ) x = T_u (fibre N i Φ (x + c))`, i.e. pointwise
`z ↦ fibre N i Φ (x + c) (ℓ•u + z)` with `c = fun _ => ℓ•u`. -/
lemma wt_fibre_shift {N : ℕ} (ℓ : ℝ) (u : ℝ³) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N i (fun z : Submission.BoseGases.X N => Φ (fun k => ℓ • u + z k)) x
      = fun z : ℝ³ => Work.BoseKinLoc.fibre N i Φ (fun k => ℓ • u + x k) (ℓ • u + z) := by
  funext z
  simp only [Work.BoseKinLoc.fibre]
  congr 1
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk : k = i
  · simp [hk]
  · simp [hk]

/-! ## 3. Change of variables for the translations of `X N = (ℝ³)^N` -/

/-- The translation `x ↦ (k ↦ ℓ•u + x k)` of the configuration space is measure preserving,
hence may be substituted in an integral. -/
lemma wt_integral_shiftN {N : ℕ} (ℓ : ℝ) (u : ℝ³) (F : Submission.BoseGases.X N → ℝ) :
    (∫ x : Submission.BoseGases.X N, F (fun k => ℓ • u + x k))
      = ∫ x : Submission.BoseGases.X N, F x := by
  let e : Submission.BoseGases.X N ≃ᵐ Submission.BoseGases.X N :=
    MeasurableEquiv.addLeft (fun _ : Fin N => ℓ • u)
  have hmp : MeasurePreserving (⇑e) volume volume := by
    change MeasurePreserving
      (fun x : Submission.BoseGases.X N => (fun _ : Fin N => ℓ • u) + x) volume volume
    exact measurePreserving_add_left volume _
  exact hmp.integral_comp' (f := e) (g := F)

/-- The inverse translation `x ↦ (k ↦ x k − ℓ•u)` of the configuration space is measure
preserving, hence may be substituted in an integral. -/
lemma wt_integral_shiftN_sub {N : ℕ} (ℓ : ℝ) (u : ℝ³) (F : Submission.BoseGases.X N → ℝ) :
    (∫ x : Submission.BoseGases.X N, F (fun k => x k - ℓ • u))
      = ∫ x : Submission.BoseGases.X N, F x := by
  let e : Submission.BoseGases.X N ≃ᵐ Submission.BoseGases.X N :=
    MeasurableEquiv.addLeft (-(fun _ : Fin N => ℓ • u))
  have hmp : MeasurePreserving (⇑e) volume volume := by
    change MeasurePreserving
      (fun x : Submission.BoseGases.X N => (-(fun _ : Fin N => ℓ • u)) + x) volume volume
    exact measurePreserving_add_left volume _
  have h := hmp.integral_comp' (f := e) (g := F)
  have hL : (∫ x : Submission.BoseGases.X N, F ((⇑e) x))
      = ∫ x : Submission.BoseGases.X N, F (fun k => x k - ℓ • u) := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    funext k
    simp [e, Pi.add_apply, sub_eq_add_neg, add_comm]
  rw [hL] at h
  exact h

/-! ## 4. Translation of a kinetic slot and of the whole kinetic word -/

/-- One slot of the kinetic word is translation covariant. -/
lemma wt_slotForm_shift {N : ℕ} (ℓ d s εT b : ℝ) (u : ℝ³) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseKinLoc.slotForm N (Work.BoseKinLoc.fsT ℓ d s εT b 0) ℓ 0 i
        (fun z : Submission.BoseGases.X N => Φ (fun k => ℓ • u + z k))
      = Work.BoseKinLoc.slotForm N (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ := by
  unfold Work.BoseKinLoc.slotForm
  congr 1
  have h1 : (∫ x : Submission.BoseGases.X N, Work.BoseKinLoc.indU ℓ 0 (x i)
        * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre N i (fun z : Submission.BoseGases.X N =>
            Φ (fun k => ℓ • u + z k)) x))
      = ∫ x : Submission.BoseGases.X N, Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.fsT ℓ d s εT b u
            (Work.BoseKinLoc.fibre N i Φ (fun k => ℓ • u + x k)) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [wt_fibre_shift]
    rw [← fsT_translate ℓ d s εT b u (Work.BoseKinLoc.fibre N i Φ (fun k => ℓ • u + x k))]
  have h2 : (∫ x : Submission.BoseGases.X N, Work.BoseKinLoc.indU ℓ 0 (x i)
        * Work.BoseKinLoc.fsT ℓ d s εT b u
          (Work.BoseKinLoc.fibre N i Φ (fun k => ℓ • u + x k)))
      = ∫ y : Submission.BoseGases.X N, Work.BoseKinLoc.indU ℓ u (y i)
          * Work.BoseKinLoc.fsT ℓ d s εT b u (Work.BoseKinLoc.fibre N i Φ y) := by
    have h := wt_integral_shiftN (N := N) ℓ u (F := fun y : Submission.BoseGases.X N =>
      Work.BoseKinLoc.indU ℓ 0 (y i - ℓ • u) * Work.BoseKinLoc.fsT ℓ d s εT b u
        (Work.BoseKinLoc.fibre N i Φ y))
    have hL : (∫ x : Submission.BoseGases.X N, (fun y : Submission.BoseGases.X N =>
          Work.BoseKinLoc.indU ℓ 0 (y i - ℓ • u) * Work.BoseKinLoc.fsT ℓ d s εT b u
            (Work.BoseKinLoc.fibre N i Φ y)) (fun k => ℓ • u + x k))
        = ∫ x : Submission.BoseGases.X N, Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.fsT ℓ d s εT b u
              (Work.BoseKinLoc.fibre N i Φ (fun k => ℓ • u + x k)) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [add_sub_cancel_left]
    rw [hL] at h
    rw [h]
    apply integral_congr_ae
    filter_upwards with y
    have hh : Work.BoseKinLoc.indU ℓ 0 (y i - ℓ • u) = Work.BoseKinLoc.indU ℓ u (y i) :=
      (wt_indU_shift ℓ u (y i)).symm
    rw [hh]
  rw [h1, h2]

/-- The kinetic word `Σᵢ𝒯_u^{(i)}` is translation covariant. -/
lemma wt_kinForm_shift {N : ℕ} (ℓ d s εT b : ℝ) (u : ℝ³)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ
      = Work.BoseKinLoc.kinForm N ℓ d s εT b 0
          (fun z : Submission.BoseGases.X N => Φ (fun i : Fin N => ℓ • u + z i)) := by
  unfold Work.BoseKinLoc.kinForm
  exact Finset.sum_congr rfl (fun i _ => (wt_slotForm_shift ℓ d s εT b u i Φ).symm)

/-! ## 5. Translation of the potential term -/

/-- The potential part of the box word is translation covariant. -/
lemma wt_potInt_shift {N : ℕ} (v g : ℝ³ → ℝ) (ℓ μ : ℝ) (hℓ : 0 < ℓ) (u : ℝ³)
    (Φ : Submission.BoseGases.X N → ℝ) :
    (∫ x : Submission.BoseGases.X N,
        ((fun z : Submission.BoseGases.X N => Φ (fun k => ℓ • u + z k)) x) ^ 2
          * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x)
      = ∫ x : Submission.BoseGases.X N, (Φ x) ^ 2
          * Work.BoseKinLoc.potWordU N v g ℓ μ u x := by
  have h := wt_integral_shiftN_sub (N := N) ℓ u (F := fun y : Submission.BoseGases.X N =>
      ((fun z : Submission.BoseGases.X N => Φ (fun k => ℓ • u + z k)) y) ^ 2
        * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y)
  have hL : (∫ y : Submission.BoseGases.X N, (fun y : Submission.BoseGases.X N =>
        ((fun z : Submission.BoseGases.X N => Φ (fun k => ℓ • u + z k)) y) ^ 2
          * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) (fun k : Fin N => y k - ℓ • u))
      = ∫ y : Submission.BoseGases.X N, (Φ y) ^ 2
          * Work.BoseKinLoc.potWordU N v g ℓ μ u y := by
    apply integral_congr_ae
    filter_upwards with y
    have h1 : Φ (fun k : Fin N => ℓ • u + (y k - ℓ • u)) = Φ y := by
      congr 1
      funext k
      abel
    rw [h1]
    rw [potWordU_shift v g ℓ μ hℓ u y]
  exact h.symm.trans hL

/-! ## 6. The box word is translation covariant -/

theorem word_translate {N : ℕ} (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) (u : ℝ³) (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b u Φ
      = Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b 0
          (fun z : Submission.BoseGases.X N => Φ (fun i : Fin N => ℓ • u + z i)) := by
  simp only [Work.BoseKinLoc.boxForm]
  rw [wt_kinForm_shift]
  congr 1
  exact (wt_potInt_shift v g ℓ μ hℓ u Φ).symm

end Work.BoseKinLoc.Sector
