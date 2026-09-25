import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.HonestAux
import Submission.Work.NN.Core.dbarSolverHonest
import Submission.Work.NN.Core.schauderIterateGen
import Submission.Work.NN.Ratio.Setup

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

/-- The intermediate radii used in the assembly: with `ρ' < ρ` componentwise we interpolate
```
ρ' < ρo < rA < rB < ρs < ρ .
```
The honest core (`Work.NN.Core.dbarSolverHonest`) solves on `polydisc 0 ρs`, and the localised
datum `polydiscCut rA rB · f` (which agrees with `f` on `polydisc 0 rA`) is fed to
`Work.NN.Core.schauderIterateGen` with equation polydisc `ρo`, data polydisc `rA` and output
polydisc `ρ'`. -/
theorem dbarHonestOne {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T1 : (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ)) (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ f, (∀ j, ContDiffOn ℝ 1 (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        ∀ j (z : Fin n → ℂ), z ∈ Work.CR.Flat.polydisc 0 ρ' →
          Work.CR.Flat.dbarCoord j (T1 f) z = f j z) ∧
      (∀ (k : ℕ) (f : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiffOn ℝ (k + 1) (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        Work.CR.Flat.holderNorm (k + 1) α (T1 f) (Work.CR.Flat.polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) *
              ∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc 0 ρ)) ∧
      (∀ f, (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        ContDiffOn ℝ (⊤ : ℕ∞) (T1 f) (Work.CR.Flat.polydisc 0 ρ')) := by
  classical
  -- ## the intermediate radii
  let ρo : Fin n → ℝ := fun j => ρ' j + (ρ j - ρ' j) / 8
  let rA : Fin n → ℝ := fun j => ρ' j + (ρ j - ρ' j) / 4
  let rB : Fin n → ℝ := fun j => ρ' j + 3 * (ρ j - ρ' j) / 8
  let ρs : Fin n → ℝ := fun j => ρ' j + (ρ j - ρ' j) / 2
  have hρ'ρo : ∀ j, ρ' j < ρo j := fun j => by
    have h : ρo j = ρ' j + (ρ j - ρ' j) / 8 := rfl
    rw [h]; linarith [hlt j]
  have hρorA : ∀ j, ρo j < rA j := fun j => by
    have h1 : ρo j = ρ' j + (ρ j - ρ' j) / 8 := rfl
    have h2 : rA j = ρ' j + (ρ j - ρ' j) / 4 := rfl
    rw [h1, h2]; linarith [hlt j]
  have hrArB : ∀ j, rA j < rB j := fun j => by
    have h1 : rA j = ρ' j + (ρ j - ρ' j) / 4 := rfl
    have h2 : rB j = ρ' j + 3 * (ρ j - ρ' j) / 8 := rfl
    rw [h1, h2]; linarith [hlt j]
  have hrBρs : ∀ j, rB j < ρs j := fun j => by
    have h1 : rB j = ρ' j + 3 * (ρ j - ρ' j) / 8 := rfl
    have h2 : ρs j = ρ' j + (ρ j - ρ' j) / 2 := rfl
    rw [h1, h2]; linarith [hlt j]
  have hρoρs : ∀ j, ρo j < ρs j := fun j => lt_trans (hρorA j) (lt_trans (hrArB j) (hrBρs j))
  have hρsρ : ∀ j, ρs j < ρ j := fun j => by
    have h : ρs j = ρ' j + (ρ j - ρ' j) / 2 := rfl
    rw [h]; linarith [hlt j]
  have hρ'ρs : ∀ j, ρ' j < ρs j := fun j => lt_trans (hρ'ρo j) (hρoρs j)
  have hρoρ : ∀ j, ρo j < ρ j := fun j => lt_trans (hρoρs j) (hρsρ j)
  have hρs_pos : ∀ j, 0 < ρs j := fun j => lt_trans (hρ' j) (hρ'ρs j)
  have hrA_pos : ∀ j, 0 < rA j := fun j => lt_trans (hρ' j) (lt_trans (hρ'ρo j) (hρorA j))
  have hrAρ : ∀ j, rA j < ρ j := fun j =>
    lt_trans (hrArB j) (lt_trans (hrBρs j) (hρsρ j))
  -- ## the honest core, with solution polydisc `ρs`
  obtain ⟨T, C0, hC0pos, hEq, hEst, hSm, hSmInf⟩ :=
    dbarSolverHonest (n := n) hn hα hα1 hρ hρs_pos hρsρ
  -- ## the generalised Schauder iterate
  choose Citer hCiter using fun k => schauderIterateGen (n := n) hn (c := 0)
    (r0 := ρ') (ρmax := ρo) (r := rA) hρ' hρ'ρo hρorA hα hα1 k
  refine ⟨T, fun k => Citer k * (2 + C0) + 1, ?_, ?_, ?_, ?_⟩
  · intro k
    have h1 := hCiter k
    have h2 : (0 : ℝ) < 2 + C0 := by linarith
    nlinarith [mul_pos h1.1 h2]
  · -- ## the equation
    intro f hf hfcl j z hz
    exact hEq f hf hfcl j z (fun l => lt_trans (hz l) (hρ'ρs l))
  · -- ## the higher order estimate
    intro k f hf hfcl
    -- smoothness of the datum that the core is applied to
    have hf1 : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ) := fun j =>
      (hf j).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ (↑k + 1))
    -- the localised datum and the localised solution
    have hchi_sm : ContDiff ℝ (↑(⊤ : ℕ∞))
        (Work.NN.Ratio.polydiscCut rA rB) := Work.NN.Ratio.contDiff_polydiscCut _ _
    have hsupp : tsupport (Work.NN.Ratio.polydiscCut rA rB) ⊆ polydisc 0 ρs := by
      intro z hz l
      have h1 : ‖z l‖ ≤ rB l := Work.NN.Ratio.tsupport_polydiscCut_subset
        (fun i => le_of_lt (hrA_pos i)) hrArB hz l
      simp only [Pi.zero_apply, sub_zero]
      exact lt_of_le_of_lt h1 (hrBρs l)
    have hU : ContDiff ℝ (↑(k + 1)) (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z) :=
      Work.NN.Ratio.contDiff_mul_of_tsupport_subset (m := k + 1) hchi_sm (isOpen_polydisc 0 ρs)
        hsupp (hSm k f hf)
    have hF : ∀ j, ContDiff ℝ (↑(k + 1))
        (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z) := fun j =>
      Work.NN.Ratio.contDiff_mul_of_tsupport_subset (m := k + 1) hchi_sm (isOpen_polydisc 0 ρs)
        hsupp ((hf j).mono (polydisc_mono (fun i => (hρsρ i).le)))
    have hclosedness : ∀ j l z, z ∈ polydisc 0 ρo →
        dbarCoord j (fun z => Work.NN.Ratio.polydiscCut rA rB z * f l z) z
          = dbarCoord l (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z) z := by
      intro j l z hz
      have hzA : z ∈ polydisc 0 rA := fun m => lt_trans (hz m) (hρorA m)
      rw [dbarCoord_polydiscCut_mul_eq (fun i => le_of_lt (hrA_pos i)) hrArB hzA j,
        dbarCoord_polydiscCut_mul_eq (fun i => le_of_lt (hrA_pos i)) hrArB hzA l]
      exact hfcl j l z (fun m => lt_trans (hz m) (hρoρ m))
    have hequation : ∀ j z, z ∈ polydisc 0 ρo →
        dbarCoord j (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z) z
          = Work.NN.Ratio.polydiscCut rA rB z * f j z := by
      intro j z hz
      have hzA : z ∈ polydisc 0 rA := fun m => lt_trans (hz m) (hρorA m)
      rw [dbarCoord_polydiscCut_mul_eq (fun i => le_of_lt (hrA_pos i)) hrArB hzA j,
        hEq f hf1 hfcl j z (fun m => lt_trans (hz m) (hρoρs m))]
      exact (polydiscCut_mul_eqOn (g := f j) (fun i => le_of_lt (hrA_pos i)) hrArB z hzA).symm
    have hiter := (hCiter k).2 (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z)
      (fun j z => Work.NN.Ratio.polydiscCut rA rB z * f j z) hU hF hclosedness hequation
    -- ## bookkeeping of the norms
    have hcongrT : holderNorm (k + 1) α (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z)
          (polydisc 0 ρ')
        = holderNorm (k + 1) α (T f) (polydisc 0 ρ') :=
      holderNorm_congr_gen (Ω := polydisc 0 ρ') (f := fun z =>
          Work.NN.Ratio.polydiscCut rA rB z * T f z) (g := T f) (fun z hz =>
        polydiscCut_mul_eqOn (g := T f) (fun i => le_of_lt (hrA_pos i)) hrArB z
          (fun m => lt_trans (hz m) (lt_trans (hρ'ρo m) (hρorA m))))
    have hsum1 : (∑ j, holderNorm k α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
          (polydisc 0 rA)) ≤ ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [holderNorm_congr_gen (Ω := polydisc 0 rA) (f := fun z =>
          Work.NN.Ratio.polydiscCut rA rB z * f j z) (g := f j) (fun z hz =>
        polydiscCut_mul_eqOn (g := f j) (fun i => le_of_lt (hrA_pos i)) hrArB z hz)]
      exact holderNorm_mono_set (isOpen_polydisc 0 ρ) (isOpen_polydisc 0 rA)
        (fun z hz l => lt_trans (hz l) (hrAρ l)) k α (f j)
    have hsum2 : (∑ j, holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
          (polydisc 0 rA)) ≤ ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
      refine (Finset.sum_le_sum fun j _ => ?_).trans (Finset.sum_le_sum fun j _ =>
        holderNorm_mono_k (Nat.zero_le k) α (f j) (polydisc 0 ρ))
      rw [holderNorm_congr_gen (Ω := polydisc 0 rA) (f := fun z =>
          Work.NN.Ratio.polydiscCut rA rB z * f j z) (g := f j) (fun z hz =>
        polydiscCut_mul_eqOn (g := f j) (fun i => le_of_lt (hrA_pos i)) hrArB z hz)]
      exact holderNorm_mono_set (isOpen_polydisc 0 ρ) (isOpen_polydisc 0 rA)
        (fun z hz l => lt_trans (hz l) (hrAρ l)) 0 α (f j)
    have hsum3 : holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z)
          (polydisc 0 ρo)
        ≤ ENNReal.ofReal C0 * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
      have hcongr : holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z)
            (polydisc 0 ρo)
          = holderNorm 0 α (T f) (polydisc 0 ρo) :=
        holderNorm_congr_gen (Ω := polydisc 0 ρo) (f := fun z =>
            Work.NN.Ratio.polydiscCut rA rB z * T f z) (g := T f) (fun z hz =>
          polydiscCut_mul_eqOn (g := T f) (fun i => le_of_lt (hrA_pos i)) hrArB z
            (fun m => lt_trans (hz m) (hρorA m)))
      rw [hcongr]
      exact (holderNorm_mono_set (isOpen_polydisc 0 ρs) (isOpen_polydisc 0 ρo)
          (fun z hz l => lt_trans (hz l) (hρoρs l)) 0 α (T f)).trans
        ((hEst f hf1).trans (mul_le_mul' le_rfl
          (Finset.sum_le_sum fun j _ => holderNorm_mono_k (Nat.zero_le k) α (f j) (polydisc 0 ρ))))
    have hbound : (∑ j, holderNorm k α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
              (polydisc 0 rA))
            + (∑ j, holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
              (polydisc 0 rA))
            + holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z) (polydisc 0 ρo)
          ≤ ENNReal.ofReal (2 + C0) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
      set S : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (polydisc 0 ρ) with hS
      calc (∑ j, holderNorm k α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
                (polydisc 0 rA))
              + (∑ j, holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
                (polydisc 0 rA))
              + holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z) (polydisc 0 ρo)
          ≤ S + S + ENNReal.ofReal C0 * S := by
            refine add_le_add (add_le_add ?_ ?_) ?_
            · simpa only [hS] using hsum1
            · simpa only [hS] using hsum2
            · simpa only [hS] using hsum3
        _ = (2 + ENNReal.ofReal C0) * S := by ring
        _ = (ENNReal.ofReal 2 + ENNReal.ofReal C0) * S := by
              rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        _ = ENNReal.ofReal (2 + C0) * S := by
              rw [← ENNReal.ofReal_add (by norm_num) (le_of_lt hC0pos)]
        _ = ENNReal.ofReal (2 + C0) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by rw [hS]
    calc holderNorm (k + 1) α (T f) (polydisc 0 ρ')
        = holderNorm (k + 1) α (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z)
            (polydisc 0 ρ') := hcongrT.symm
      _ ≤ ENNReal.ofReal (Citer k) *
            ((∑ j, holderNorm k α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
                (polydisc 0 rA))
              + (∑ j, holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * f j z)
                (polydisc 0 rA))
              + holderNorm 0 α (fun z => Work.NN.Ratio.polydiscCut rA rB z * T f z)
                (polydisc 0 ρo)) := hiter
      _ ≤ ENNReal.ofReal (Citer k) * (ENNReal.ofReal (2 + C0)
            * ∑ j, holderNorm k α (f j) (polydisc 0 ρ)) := mul_le_mul' le_rfl hbound
      _ = ENNReal.ofReal (Citer k * (2 + C0)) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (hCiter k).1)]
      _ ≤ ENNReal.ofReal (Citer k * (2 + C0) + 1) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have h1 := (hCiter k).1
            have h2 : (0 : ℝ) < 2 + C0 := by linarith
            nlinarith [mul_pos h1 h2]
  · -- ## smoothness
    intro f hf hfcl
    exact (hSmInf f hf).mono (polydisc_mono (fun j => (hρ'ρs j).le))

end Work.NN.Core
