import Mathlib
import Submission.Work.PTCert.rowHelp

namespace Work.PTCert

/-
Goal: identify the stored stabiliser list `stabL r` with the kernel scan of row `r`
(`1 ≤ r < 18`; row `0` has `stabL 0 = []` and is excluded).

For each `r = 1,…,17` the already-proved theorem `Submission.PTCert.C.stabtab…`/`C.scan_ok r`
states, with `x0 = cG rowT r` and `(a,b) = (x0/128, x0%128)`,
  `eqL (scanRow cmT rowIdxT a b x0 pcL) stabLr = true`
(`Checks/R r.lean`), and `stabL r = stabLs.getD r [] = stabLr` is definitional.
The row codes are (the values of `Submission.PTCert.D.cG rowT r`, `r = 1..17`):
  1, 129, 131, 132, 133, 135, 145, 146, 147, 148, 149, 151, 161, 162, 165, 166, 169
with `(a,b) = (0,1), (1,1), (1,3), (1,4), (1,5), (1,7), (1,17), (1,18), (1,19), (1,20), (1,21),
(1,23), (1,33), (1,34), (1,37), (1,38), (1,41)`.
Use `Work.PTCert.eqL_eq_true` (rowHelp) to turn `eqL … = true` into an equality, `Work.PTCert.x0c_val`
for `cG rowT r = x0cL.getD r 0`, and split `r` into the 17 cases (`interval_cases`). Each case is a
tiny `decide +kernel` computation (`cG rowT 5 = 133`, `133/128 = 1`, …); do NOT run `decide` on
`scanRow` itself.
-/
open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stabLScan : ∀ r < 18, 1 ≤ r →
    stabL r = scanRow cmT rowIdxT (cG rowT r / 128) (cG rowT r % 128) (cG rowT r) pcL := by
  intro r hr hr1
  interval_cases r
  · have h := (eqL_eq_true _ _).mp C.scan_ok1
    have hx : cG rowT 1 = 1 := by rw [x0c_val 1 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 1 = stabL1 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok2
    have hx : cG rowT 2 = 129 := by rw [x0c_val 2 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 2 = stabL2 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok3
    have hx : cG rowT 3 = 131 := by rw [x0c_val 3 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 3 = stabL3 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok4
    have hx : cG rowT 4 = 132 := by rw [x0c_val 4 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 4 = stabL4 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok5
    have hx : cG rowT 5 = 133 := by rw [x0c_val 5 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 5 = stabL5 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok6
    have hx : cG rowT 6 = 135 := by rw [x0c_val 6 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 6 = stabL6 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok7
    have hx : cG rowT 7 = 145 := by rw [x0c_val 7 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 7 = stabL7 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok8
    have hx : cG rowT 8 = 146 := by rw [x0c_val 8 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 8 = stabL8 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok9
    have hx : cG rowT 9 = 147 := by rw [x0c_val 9 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 9 = stabL9 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok10
    have hx : cG rowT 10 = 148 := by rw [x0c_val 10 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 10 = stabL10 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok11
    have hx : cG rowT 11 = 149 := by rw [x0c_val 11 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 11 = stabL11 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok12
    have hx : cG rowT 12 = 151 := by rw [x0c_val 12 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 12 = stabL12 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok13
    have hx : cG rowT 13 = 161 := by rw [x0c_val 13 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 13 = stabL13 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok14
    have hx : cG rowT 14 = 162 := by rw [x0c_val 14 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 14 = stabL14 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok15
    have hx : cG rowT 15 = 165 := by rw [x0c_val 15 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 15 = stabL15 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok16
    have hx : cG rowT 16 = 166 := by rw [x0c_val 16 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 16 = stabL16 from rfl).trans h.symm
  · have h := (eqL_eq_true _ _).mp C.scan_ok17
    have hx : cG rowT 17 = 169 := by rw [x0c_val 17 (by norm_num)]; decide
    rw [hx]; norm_num
    exact (show stabL 17 = stabL17 from rfl).trans h.symm

end Work.PTCert
