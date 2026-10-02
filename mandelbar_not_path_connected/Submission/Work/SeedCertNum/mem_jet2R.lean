/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Soundness of the *rounded* second-order jet recursion `jet2IterR` (item A3)

`Work.SeedCert.jet2IterR K Ctyp Xz n` is `jet2Iter Ctyp Xz n` with an outward rounding to the grid
`2^-K` inserted after every step (`Work.SeedCert.DJet2.roundOut`, `Work.SeedCert.CBox.mem_roundOut`
in `Submission/Work/SeedCertNum/Round.lean`).  The present file proves the soundness
`mem_jet2R`: for `c ∈ Ctyp`, `z ∈ Xz` and every `n`,

* `(Tsq c)^[n] z` lies in the `v`-box,
* `deriv ((Tsq c)^[n]) z` lies in the `d1`-box,
* `deriv (deriv ((Tsq c)^[n])) z` lies in the `d2`-box

of the rounded recursion.  The proof is the induction of `Submission/Work/SeedCertNum/mem_jet2.lean`
(`jet2_step`) redone with `jet2IterR` in place of `jet2Iter`; the only new ingredient is that each
step of the recursion is followed by `roundOut K`, whose soundness `CBox.mem_roundOut` supplies the
last inclusion.
-/
import Mathlib
import Submission.Work.SeedCertNum.Round
import Submission.Work.SeedCertNum.mem_jet2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

noncomputable section

/-! ## The induction step of the rounded recursion -/

/-- One step of the rounded jet recursion: the three box inclusions for `n + 1` follow from those
for `n`.  Mirror of `Work.SeedCertNum.jet2_step`, with the `roundOut K` of each box in the
conclusion supplied by `Work.SeedCert.CBox.mem_roundOut`. -/
theorem jet2_stepR {c : ℂ} {Ctyp Xz : CBox} (hc : c ∈ Ctyp.toSet) (K n : ℕ) {z : ℂ}
    (ih : ((Work.Landing.Tsq c)^[n] z ∈ (jet2IterR K Ctyp Xz n).v.toSet) ∧
          (deriv ((Work.Landing.Tsq c)^[n]) z ∈ (jet2IterR K Ctyp Xz n).d1.toSet) ∧
          (deriv (deriv ((Work.Landing.Tsq c)^[n])) z ∈ (jet2IterR K Ctyp Xz n).d2.toSet)) :
    ((Work.Landing.Tsq c)^[n+1] z ∈ (jet2IterR K Ctyp Xz (n+1)).v.toSet) ∧
    (deriv ((Work.Landing.Tsq c)^[n+1]) z ∈ (jet2IterR K Ctyp Xz (n+1)).d1.toSet) ∧
    (deriv (deriv ((Work.Landing.Tsq c)^[n+1])) z ∈ (jet2IterR K Ctyp Xz (n+1)).d2.toSet) := by
  obtain ⟨hv, hd1, hd2⟩ := ih
  -- `conj c` lies in the conjugated parameter box
  have hsc : star c ∈ Ctyp.conj.toSet := CBox.mem_conj hc
  -- `4 w` lies in `v.mulScalar 4`
  have h4 : (4 : ℂ) * ((Work.Landing.Tsq c)^[n] z)
      ∈ ((jet2IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).toSet := by
    have := CBox.mem_mulScalar (B := (jet2IterR K Ctyp Xz n).v) hv (a := Dya.ofInt 4)
    simpa using this
  -- `w^2 + conj c` lies in the intermediate box `v.sq + conj Ctyp`
  have hu : ((Work.Landing.Tsq c)^[n] z) ^ 2 + star c
      ∈ (((jet2IterR K Ctyp Xz n).v.sq).add Ctyp.conj).toSet :=
    CBox.mem_add (CBox.mem_sq hv) hsc
  -- `G'(w) = 4 w (w^2 + conj c)` lies in `dG`
  have hdG : deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
      ∈ (((jet2IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).mul
         (((jet2IterR K Ctyp Xz n).v.sq).add Ctyp.conj)).toSet := by
    rw [deriv_Tsq_apply]
    exact CBox_mem_mul h4 hu
  refine ⟨?_, ?_, ?_⟩
  · -- value: `G w = (w^2 + conj c)^2 + c`
    rw [Function.iterate_succ_apply']
    simp only [jet2IterR, DJet2.roundOut, jet2Step]
    exact CBox.mem_roundOut
      (CBox.mem_add (CBox.mem_sq (CBox.mem_add (CBox.mem_sq hv) hsc)) hc)
  · -- first derivative: chain rule
    have hdiffG : DifferentiableAt ℂ (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z) :=
      ((contDiff_Tsq c).contDiffAt).differentiableAt (by norm_num)
    have hdiffH : DifferentiableAt ℂ ((Work.Landing.Tsq c)^[n]) z :=
      ((contDiff_Tsq_iter c n).contDiffAt).differentiableAt (by norm_num)
    have hcomp := deriv_comp z hdiffG hdiffH
    rw [Function.iterate_succ', hcomp]
    have hprod := CBox_mem_mul hdG hd1
    simpa only [jet2IterR, DJet2.roundOut, jet2Step] using CBox.mem_roundOut hprod
  · -- second derivative: order-two Faà di Bruno
    have hcomp2 := deriv_deriv_comp_two (G := Work.Landing.Tsq c)
      (H := (Work.Landing.Tsq c)^[n]) (z := z)
      ((contDiff_Tsq c).contDiffAt) ((contDiff_Tsq_iter c n).contDiffAt)
    rw [Function.iterate_succ', hcomp2]
    have h12 : (12 : ℂ) * ((Work.Landing.Tsq c)^[n] z) ^ 2
        ∈ ((jet2IterR K Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).toSet := by
      have := CBox.mem_mulScalar (B := (jet2IterR K Ctyp Xz n).v.sq)
        (CBox.mem_sq hv) (a := Dya.ofInt 12)
      simpa using this
    have h4c : (4 : ℂ) * star c ∈ (Ctyp.conj.mulScalar (Dya.ofInt 4)).toSet := by
      have := CBox.mem_mulScalar (B := Ctyp.conj) hsc (a := Dya.ofInt 4)
      simpa using this
    have hd2G : deriv (deriv (Work.Landing.Tsq c)) ((Work.Landing.Tsq c)^[n] z)
        ∈ (((jet2IterR K Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).add
           (Ctyp.conj.mulScalar (Dya.ofInt 4))).toSet := by
      rw [deriv_deriv_Tsq_apply]
      exact CBox.mem_add h12 h4c
    have hA := CBox_mem_mul hd2G (CBox.mem_sq hd1)
    have hB := CBox_mem_mul hdG hd2
    have hsum := CBox.mem_add hA hB
    simpa only [jet2IterR, DJet2.roundOut, jet2Step] using CBox.mem_roundOut hsum

/-! ## Soundness of the rounded recursion -/

/-- **Soundness of `jet2IterR`.**  For `c` in the parameter box `Ctyp` and `z` in `Xz`, the `n`-th
iterate of `Tsq c` at `z`, together with its first two derivatives, lies in the corresponding
rounded boxes of the recursion. -/
theorem mem_jet2R_of_mem {c : ℂ} {Ctyp Xz : CBox} (hc : c ∈ Ctyp.toSet)
    (K n : ℕ) {z : ℂ} (hz : z ∈ Xz.toSet) :
    ((Work.Landing.Tsq c)^[n] z ∈ (jet2IterR K Ctyp Xz n).v.toSet) ∧
      (deriv ((Work.Landing.Tsq c)^[n]) z ∈ (jet2IterR K Ctyp Xz n).d1.toSet) ∧
      (deriv (deriv ((Work.Landing.Tsq c)^[n])) z ∈ (jet2IterR K Ctyp Xz n).d2.toSet) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [Function.iterate_zero_apply]
      simp only [jet2IterR]
      exact CBox.mem_roundOut hz
    · have hd : deriv ((Work.Landing.Tsq c)^[0]) z = 1 := by
        rw [Function.iterate_zero]
        exact deriv_id z
      rw [hd]
      simp only [jet2IterR]
      refine CBox.mem_roundOut ?_
      simp [oneBox, Dya.toReal_one, Dya.toReal_zero]
    · have hd : deriv (deriv ((Work.Landing.Tsq c)^[0])) z = 0 := by
        rw [Function.iterate_zero]
        rw [show deriv (id : ℂ → ℂ) = fun _ => 1 from funext (fun x => deriv_id x)]
        exact deriv_const z 1
      rw [hd]
      simp only [jet2IterR]
      refine CBox.mem_roundOut ?_
      simp [Dya.toReal_zero]
  | succ n ih => exact jet2_stepR hc K n ih

/-! ## The requested lemma -/

theorem mem_jet2R {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV} {Xz : Work.SeedCert.CBox}
    (K n : ℕ) {z : ℂ} {t : ℝ} (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n] z
        ∈ (Work.SeedCert.jet2IterR K (Work.SeedCert.pbox x₀ Xt) Xz n).v.toSet) ∧
      (deriv ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n]) z
        ∈ (Work.SeedCert.jet2IterR K (Work.SeedCert.pbox x₀ Xt) Xz n).d1.toSet) ∧
      (deriv (deriv ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n])) z
        ∈ (Work.SeedCert.jet2IterR K (Work.SeedCert.pbox x₀ Xt) Xz n).d2.toSet) :=
  mem_jet2R_of_mem (Ctyp := Work.SeedCert.pbox x₀ Xt) (Work.SeedCert.mem_pbox ht) K n hz

end

end Work.SeedCertNum
