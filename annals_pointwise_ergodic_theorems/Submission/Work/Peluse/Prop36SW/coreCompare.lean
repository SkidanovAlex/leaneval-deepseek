import Mathlib
import Submission.Work.Peluse.Prop36SW.signBridge
import Submission.Work.Peluse.Prop36SW.boxNorm_le_arithIcc_succ
import Submission.Work.Peluse.Prop36SW.average_piIcc_eq_average_paramBox

/-!
# Comparing the level-`H` signed box average with the level-`(H+1)` absolute box average

The `§5` chain of Peluse's Proposition 3.6 produces a family average of level-`H` box norms with the
*signed* slot coefficients `p s a`, while the ladder (`Prop36SW.PeluseLadderAG`) consumes a family
average of *positive* coefficients and, at the top of the chain, of window `H+1`.  This module
supplies that comparison: the level-`H` signed average over the closed box `∏_i [-H,H]` is bounded
by `(4^t)^{2^{-t}}` times the level-`(H+1)` average with the absolute coefficients over the ladder's
parameter box `paramBox (H+1)`, where `t` is the level of the box norm.

Three ingredients, all proved elsewhere:

* `average_piIcc_eq_average_paramBox` — the average over `∏_i [-H,H]` is the average over
  `paramBox (H+1) = ∏_{Slot ι 1} Ioo (-(H+1)) (H+1)` (`Ioo (-(H+1)) (H+1) = Icc (-H) H` in `ℤ`);
* `sum_paramBox_boxNorm_abs` (the *sign bridge*) — the box average of any function of the direction
  family is unchanged under `p ↦ |p|`;
* `boxNorm_le_arithIcc_succ` — enlarging the direction windows from `H` to `H+1` costs at most the
  constant `(4^t)^{2^{-t}}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- The level of the family index type of the chain (encoded in the `coreCompare` statement as the
cardinality of `FamIdx` at slot multiplicity one and family multiplicity one). -/
private abbrev coreLevel (ι : Type) [Fintype ι] : ℕ :=
  Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))

/-- **The `H → H+1` step with absolute coefficients.**  Enlarging the direction windows of the
`|p|`-family from `H` to `H+1` costs at most `(4^t)^{2^{-t}}`; the direction family is
`j ↦ arithIcc (∑_{s ∈ ω_j} |p s.1 a| · b s) M` read through the `Fin`-normalisation
`(Fintype.equivFin (FamIdx _)).symm`. -/
private lemma boxNorm_pDirFamG_le_succ {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (p : ι → P → ℤ) (H : ℕ) (hH : 1 ≤ H) (a : P) (b : Slot ι (fun _ => 1) → ℤ)
    (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f)
    (ht : 2 ≤ coreLevel ι) :
    Work.Peluse.boxNorm (coreLevel ι)
      (fun j => pDirFamG (k := fun _ : ι => 1) (kω := fun _ => 1)
        (p := fun (s : ι) (_ : P) => |p s a|) H a b
        ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f
      ≤ (((4 : ℝ) ^ (coreLevel ι)) ^ (1 / (2 : ℝ) ^ (coreLevel ι)))
        * Work.Peluse.boxNorm (coreLevel ι)
          (fun j => pDirFamG (k := fun _ : ι => 1) (kω := fun _ => 1)
            (p := fun (s : ι) (a' : P) => |p s a'|) (H + 1) a b
            ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f := by
  exact Work.Peluse.Prop36SW.boxNorm_le_arithIcc_succ
    (t := Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))) ht
    (fun j => ∑ s ∈ (((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1)
        (fun _ => 1))).symm j).1).1, |p s.1 a| * b s) hH S hf

/-- **The summed comparison.**  The `paramBox (H+1)`-average-ready form of `coreCompare`: the sum of
the level-`H` box norms with the signed coefficients is dominated by `(4^t)^{2^{-t}}` times the sum
of the level-`(H+1)` box norms with the absolute coefficients. -/
private lemma coreCompare_sum_le {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (p : ι → P → ℤ) (H : ℕ) (hH : 1 ≤ H) (a : P) (S : Finset ℤ) {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) (ht : 2 ≤ coreLevel ι) :
    (∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1),
        Work.Peluse.boxNorm (coreLevel ι)
        (fun j => Work.Peluse.UControl.pDirFam (k := fun _ : ι => 1) (kω := fun _ => 1)
          (p := fun (s : ι) (_ : Fin 0 → ℤ) => p s a) H (fun _ => (0 : ℤ)) b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f)
      ≤ (((4 : ℝ) ^ (coreLevel ι)) ^ (1 / (2 : ℝ) ^ (coreLevel ι)))
        * (∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1),
        Work.Peluse.boxNorm (coreLevel ι)
        (fun j => pDirFamG (k := fun _ : ι => 1) (kω := fun _ => 1)
          (p := fun (s : ι) (a' : P) => |p s a'|) (H + 1) a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f) := by
  -- the signed `pDirFam` family is the `pDirFamG` family of the general-parameter-type form
  have h1 : (∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1),
        Work.Peluse.boxNorm (coreLevel ι)
        (fun j => Work.Peluse.UControl.pDirFam (k := fun _ : ι => 1) (kω := fun _ => 1)
          (p := fun (s : ι) (_ : Fin 0 → ℤ) => p s a) H (fun _ => (0 : ℤ)) b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f)
      = (∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1),
        Work.Peluse.boxNorm (coreLevel ι)
        (fun j => pDirFamG (k := fun _ : ι => 1) (kω := fun _ => 1)
          (p := fun (s : ι) (_ : P) => p s a) H a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f) := by
    congr 1
  -- the sign bridge: the box average is unchanged under `p ↦ |p|`
  have hsign := Work.Peluse.Prop36SW.sum_paramBox_boxNorm_abs (kω := fun _ => 1)
      (p := fun (s : ι) (_ : P) => p s a) H (H + 1) a S f
  -- the `H → H+1` step, summed
  have hstep : (∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1),
        Work.Peluse.boxNorm (coreLevel ι)
        (fun j => pDirFamG (k := fun _ : ι => 1) (kω := fun _ => 1)
          (p := fun (s : ι) (_ : P) => |p s a|) H a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f)
      ≤ (((4 : ℝ) ^ (coreLevel ι)) ^ (1 / (2 : ℝ) ^ (coreLevel ι)))
        * (∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1),
        Work.Peluse.boxNorm (coreLevel ι)
        (fun j => pDirFamG (k := fun _ : ι => 1) (kω := fun _ => 1)
          (p := fun (s : ι) (a' : P) => |p s a'|) (H + 1) a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j)) S f) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => boxNorm_pDirFamG_le_succ p H hH a b S hf ht)
  exact (h1.trans hsign).trans_le hstep

theorem coreCompare {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (p : ι → P → ℤ) (H : ℕ) (hH : 1 ≤ H) (a : P) (S : Finset ℤ) {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f)
    (ht : 2 ≤ Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))) :
    ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ))).card : ℝ)⁻¹ *
        ∑ s ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ)),
          Work.Peluse.boxNorm
            (Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1)))
            (fun j => Work.Peluse.UControl.pDirFam
              (p := fun (s : ι) (_ : Fin 0 → ℤ) => p s a) H (fun _ => (0 : ℤ))
              (fun k => s k.1)
              ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1)
                (fun _ => 1))).symm j)) S f
      ≤ (((4 : ℝ) ^ (Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1)
              (fun _ => 1)))) ^
          (1 / (2 : ℝ) ^ (Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1)
            (fun _ => 1)))))
        * (((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1)).card : ℝ)⁻¹ *
          ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1),
            Work.Peluse.boxNorm
              (Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1)))
              (fun j => Work.Peluse.Prop36SW.pDirFamG
                (p := fun (s : ι) (a' : P) => |p s a'|) (H + 1) a b
                ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1)
                  (fun _ => 1))).symm j)) S f) := by
  classical
  -- replace the average over the closed box `∏_i [-H,H]` by the average over `paramBox (H+1)`
  rw [Work.Peluse.Prop36SW.average_piIcc_eq_average_paramBox (ι := ι) H
        (fun b => Work.Peluse.boxNorm
          (Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1)))
          (fun j => Work.Peluse.UControl.pDirFam
            (p := fun (s : ι) (_ : Fin 0 → ℤ) => p s a) H (fun _ => (0 : ℤ)) b
            ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : ι => 1) (fun _ => 1))).symm j))
          S f)]
  -- the positive prefactor `|paramBox (H+1)|⁻¹`
  have hkey := coreCompare_sum_le (ι := ι) p H hH a S hf ht
  exact le_trans (mul_le_mul_of_nonneg_left hkey (by positivity)) (le_of_eq (by ring))

end

end Work.Peluse.Prop36SW
