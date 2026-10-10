import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Expanded matrix entries of the AS Galois-coordinate matrices

`asM w i j = (w+i)^j` and `asN w k j = (w+2k)^j` for `i, j, k : Fin 5`; the lemmas below record
the twenty-five expanded forms of each.  They are the *simp normal form* used by the transport
certificates of `Work.MotAS.ASTransport`: without them `ring` expands products of the powers
`(w+i)^j` directly, which blows up the computation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

variable {R : Type*} [CommRing R]

theorem asM_0_0 (w : R) : asM w 0 0 = 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_0_1 (w : R) : asM w 0 1 = w := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_0_2 (w : R) : asM w 0 2 = w^2 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_0_3 (w : R) : asM w 0 3 = w^3 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_0_4 (w : R) : asM w 0 4 = w^4 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_1_0 (w : R) : asM w 1 0 = 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_1_1 (w : R) : asM w 1 1 = w + 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_1_2 (w : R) : asM w 1 2 = w^2 + 2*w + 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_1_3 (w : R) : asM w 1 3 = w^3 + 3*w^2 + 3*w + 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_1_4 (w : R) : asM w 1 4 = w^4 + 4*w^3 + 6*w^2 + 4*w + 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_2_0 (w : R) : asM w 2 0 = 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_2_1 (w : R) : asM w 2 1 = w + 2 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_2_2 (w : R) : asM w 2 2 = w^2 + 4*w + 4 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_2_3 (w : R) : asM w 2 3 = w^3 + 6*w^2 + 12*w + 8 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_2_4 (w : R) : asM w 2 4 = w^4 + 8*w^3 + 24*w^2 + 32*w + 16 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_3_0 (w : R) : asM w 3 0 = 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_3_1 (w : R) : asM w 3 1 = w + 3 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_3_2 (w : R) : asM w 3 2 = w^2 + 6*w + 9 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_3_3 (w : R) : asM w 3 3 = w^3 + 9*w^2 + 27*w + 27 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_3_4 (w : R) : asM w 3 4 = w^4 + 12*w^3 + 54*w^2 + 108*w + 81 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_4_0 (w : R) : asM w 4 0 = 1 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_4_1 (w : R) : asM w 4 1 = w + 4 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_4_2 (w : R) : asM w 4 2 = w^2 + 8*w + 16 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_4_3 (w : R) : asM w 4 3 = w^3 + 12*w^2 + 48*w + 64 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asM_4_4 (w : R) : asM w 4 4 = w^4 + 16*w^3 + 96*w^2 + 256*w + 256 := by
  simp only [asM, Matrix.of_apply]
  norm_num
  try ring

theorem asN_0_0 (w : R) : asN w 0 0 = 1 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_0_1 (w : R) : asN w 0 1 = w := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_0_2 (w : R) : asN w 0 2 = w^2 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_0_3 (w : R) : asN w 0 3 = w^3 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_0_4 (w : R) : asN w 0 4 = w^4 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_1_0 (w : R) : asN w 1 0 = 1 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_1_1 (w : R) : asN w 1 1 = w + 2 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_1_2 (w : R) : asN w 1 2 = w^2 + 4*w + 4 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_1_3 (w : R) : asN w 1 3 = w^3 + 6*w^2 + 12*w + 8 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_1_4 (w : R) : asN w 1 4 = w^4 + 8*w^3 + 24*w^2 + 32*w + 16 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_2_0 (w : R) : asN w 2 0 = 1 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_2_1 (w : R) : asN w 2 1 = w + 4 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_2_2 (w : R) : asN w 2 2 = w^2 + 8*w + 16 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_2_3 (w : R) : asN w 2 3 = w^3 + 12*w^2 + 48*w + 64 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_2_4 (w : R) : asN w 2 4 = w^4 + 16*w^3 + 96*w^2 + 256*w + 256 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_3_0 (w : R) : asN w 3 0 = 1 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_3_1 (w : R) : asN w 3 1 = w + 6 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_3_2 (w : R) : asN w 3 2 = w^2 + 12*w + 36 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_3_3 (w : R) : asN w 3 3 = w^3 + 18*w^2 + 108*w + 216 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_3_4 (w : R) : asN w 3 4 = w^4 + 24*w^3 + 216*w^2 + 864*w + 1296 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_4_0 (w : R) : asN w 4 0 = 1 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_4_1 (w : R) : asN w 4 1 = w + 8 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_4_2 (w : R) : asN w 4 2 = w^2 + 16*w + 64 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_4_3 (w : R) : asN w 4 3 = w^3 + 24*w^2 + 192*w + 512 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

theorem asN_4_4 (w : R) : asN w 4 4 = w^4 + 32*w^3 + 384*w^2 + 2048*w + 4096 := by
  simp only [asN, Matrix.of_apply]
  norm_num
  try ring

end Work.MotAS
