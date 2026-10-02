/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Item A3: the parabolic point is *simple*

`F''(z₁) ≠ 0`, where `F c = (Tsq c)^[5] = (T_c)^[10]` (`Work.FSeed.F`), together with the
enclosure of the quadratic coefficient `A = F''(z₁)/2`.  The proof is the 2-jet propagation
`mem_jet2` (`Submission/Work/SeedCertNum/Jet2.lean`) evaluated on the degenerate-free box
`Xz × Xt` of the certified point, plus the `decide`-checked statement that the resulting box
`d2box` does not contain `0`.

Pilot values: `F''(z₁) ≈ 755.368 + 1136.032 i`, so `|A| ≈ 682.12`; the box `Abox` here encloses
`A` with `681² ≤ ‖A‖² ≤ 683²`.

## Main results

* `krawData_d2_avoids` — `decide`-checked exclusion of `0` from `d2box`;
* `iteratedDeriv2_ne_zero` — `iteratedDeriv 2 (Work.FSeed.F cb) z1 ≠ 0`;
* `Aquad_mem`, `Aquad_ne_zero`, `Aquad_normsq_bounds`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1
import Submission.Work.SeedCertNum.Round
import Submission.Work.SeedCertNum.mem_jet2R
import Submission.Work.SeedCertNum.deriv2_Tsq
import Submission.Work.FSeed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxRecDepth 8000

/-- The box containing `F''(z₁) = iteratedDeriv 2 (F c_b) z₁`.  The recursion is run with
outward rounding to the grid `2^-400` (`jet2IterR`), which keeps the exponents of the endpoints —
and hence the kernel cost of the `decide` checks below — bounded by `O(400)` instead of the `4^5`
growth of the exact recursion (`Submission/Work/SeedCertNum/Round.lean`). -/
def d2box : CBox := (jet2IterR 400 (pbox krawData.x₀ krawData.Xt) krawData.Xz 5).d2

/-- The quadratic coefficient `A = F''(z₁)/2` of the parabolic point. -/
def Aquad : ℂ := iteratedDeriv 2 (Work.FSeed.F cb) z1 / 2

/-- The box containing `A`. -/
def Abox : CBox := d2box.mulScalar (Dya.half Dya.one)

/-- `681²`, as a dyadic. -/
def sq681 : Dya := Dya.mul (Dya.ofInt 681) (Dya.ofInt 681)

/-- `683²`, as a dyadic. -/
def sq683 : Dya := Dya.mul (Dya.ofInt 683) (Dya.ofInt 683)

theorem krawData_d2_avoids : d2box.avoidsZero = true := by decide

theorem krawData_A_lo : Dya.le sq681 (Abox.normSq).lo = true := by decide

theorem krawData_A_hi : Dya.le (Abox.normSq).hi sq683 = true := by decide

theorem d2_mem : iteratedDeriv 2 (Work.FSeed.F cb) z1 ∈ d2box.toSet := by
  have h := Work.SeedCertNum.mem_jet2R (x₀ := krawData.x₀) (Xt := krawData.Xt) (Xz := krawData.Xz)
    400 5 (z := z1) (t := krawU.2.2) krawU_z_mem krawU_t_mem
  have hd := h.2.2
  have key : iteratedDeriv 2 (Work.FSeed.F cb) =
      deriv (deriv ((Work.Landing.Tsq cb)^[5])) := by
    rw [Work.FSeed.F_apply]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [key]
  exact hd

theorem Aquad_mem : Aquad ∈ Abox.toSet := by
  have h := d2_mem
  have hm := CBox.mem_mulScalar (B := d2box) h (a := Dya.half Dya.one)
  rw [show (Dya.half Dya.one).toReal = 1 / 2 by
        simp [Dya.toReal_half, Dya.toReal_one]] at hm
  simpa [Abox, Aquad, div_eq_mul_inv, mul_comm] using hm

theorem Aquad_normsq_bounds : (681 : ℝ) * 681 ≤ ‖Aquad‖ ^ 2 ∧ ‖Aquad‖ ^ 2 ≤ (683 : ℝ) * 683 := by
  have h := CBox.mem_normSq Aquad_mem
  have h1 : (sq681).toReal ≤ (Abox.normSq).lo.toReal :=
    (Dya.toReal_le_iff _ _).mp krawData_A_lo
  have h2 : (Abox.normSq).hi.toReal ≤ (sq683).toReal :=
    (Dya.toReal_le_iff _ _).mp krawData_A_hi
  simp only [sq681, sq683, Dya.toReal_mul, Dya.toReal_ofInt] at h1 h2
  exact ⟨le_trans h1 h.1, le_trans h.2 h2⟩

theorem Aquad_ne_zero : Aquad ≠ 0 := by
  intro h
  have hb := Aquad_normsq_bounds.1
  rw [h] at hb
  norm_num at hb

theorem iteratedDeriv2_eq : iteratedDeriv 2 (Work.FSeed.F cb) z1 = 2 * Aquad := by
  rw [Aquad]
  ring

theorem iteratedDeriv2_ne_zero : iteratedDeriv 2 (Work.FSeed.F cb) z1 ≠ 0 := by
  rw [iteratedDeriv2_eq]
  exact mul_ne_zero two_ne_zero Aquad_ne_zero

end

end Work.SeedCert
