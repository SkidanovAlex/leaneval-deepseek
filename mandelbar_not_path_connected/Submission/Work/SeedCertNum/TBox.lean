/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Interval evaluation of `T_c` and of its iterates over complex boxes

`TBox c B` is a computable box containing `T_c z = z̄² + c` for every `z ∈ B` and every `c` in the
parameter box `Ctyp`; `FTBox` is its 10-fold iteration, i.e. an enclosure of
`F c = (Tsq c)^[5] = (T_c)^[10]`.  These are the enclosures the petal/Taylor model
(`NOTES_LEAD_mandelbar_noncusp.md` §2.5) and the jet arithmetic of item A3 evaluate on the boxes of
their certificates.

## Main results

* `CBox.mem_sq` — `CBox.sq` is sound (from `Work.SeedCertNum.CBox_mem_mul`);
* `TBox`, `TBox_step`, `mem_TBox`;
* `FTBox`, `FTBox_apply`, `mem_FTBox`.
-/
import ChallengeDeps
import Submission.Work.SeedCertNum.CBox_mem_mul
import Submission.Work.SeedCertNum.Box

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

/-- The square of a box is sound. -/
theorem CBox.mem_sq {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) : z ^ 2 ∈ (B.sq).toSet := by
  rw [CBox.sq, pow_two]
  exact Work.SeedCertNum.CBox_mem_mul hz hz

/-- A box containing `T_c z` for `z ∈ B` and `c ∈ Ctyp`: `(conj B)² + Ctyp`. -/
def TBox (Ctyp B : CBox) : CBox := ((B.conj).sq).add Ctyp

theorem mem_TBox {Ctyp B : CBox} {c z : ℂ} (hc : c ∈ Ctyp.toSet) (hz : z ∈ B.toSet) :
    Tantibar c z ∈ (TBox Ctyp B).toSet := by
  have h1 : (star z : ℂ) ∈ B.conj.toSet := CBox.mem_conj hz
  have h2 : (star z : ℂ) ^ 2 ∈ (B.conj).sq.toSet := CBox.mem_sq h1
  have h3 := CBox.mem_add h2 hc
  simpa [TBox, Tantibar, CBox.add, CBox.sq] using h3

/-- The `n`-fold iterate of the `T_c`-enclosure step (associated so that the induction on `n`
composes boxes). -/
def TBoxIter (Ctyp : CBox) : ℕ → CBox → CBox
  | 0, B => B
  | n + 1, B => TBoxIter Ctyp n (TBox Ctyp B)

theorem mem_TBoxIter {Ctyp : CBox} (n : ℕ) {B : CBox} {c z : ℂ} (hc : c ∈ Ctyp.toSet)
    (hz : z ∈ B.toSet) : (Tantibar c)^[n] z ∈ (TBoxIter Ctyp n B).toSet := by
  induction n generalizing B z with
  | zero => simpa [TBoxIter] using hz
  | succ n ih =>
    have h1 : Tantibar c z ∈ (TBox Ctyp B).toSet := mem_TBox hc hz
    have h2 := ih (B := TBox Ctyp B) (z := Tantibar c z) h1
    show (Tantibar c)^[n] (Tantibar c z) ∈ (TBoxIter Ctyp n (TBox Ctyp B)).toSet
    exact h2

/-- An enclosure of `F c = (T_c)^[10]` over the boxes `Ctyp` (parameters) and `B` (points). -/
def FTBox (Ctyp B : CBox) : CBox := TBoxIter Ctyp 10 B

theorem mem_FTBox {Ctyp B : CBox} {c z : ℂ} (hc : c ∈ Ctyp.toSet) (hz : z ∈ B.toSet) :
    (Tantibar c)^[10] z ∈ (FTBox Ctyp B).toSet :=
  mem_TBoxIter 10 hc hz

end Work.SeedCert
