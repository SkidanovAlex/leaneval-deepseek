import Mathlib.Analysis.Real.Sqrt
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5/6 — the two-mode Bogoliubov algebra (c-number core of FS eq:BogIdentity / eq:BogIneq)

Fournais--Solovej final_v2.tex (thm:bogolubov-complete, eq:BogIdentity, eq:BogIneq):
for CCR operators `a₊, a₋` and `A > 0`, `B ∈ ℝ` with `|B| ≤ A`, setting
`s := √(A²−B²)`, `D := (A+s)/2`, `α := B/(A+s)`,

    A(u²+v²) + 2Buv = D·((u+αv)² + (v+αu)²)            (the c-number core),
    A − s = B²/(A+s) ≤ B²/A,                            (Taylor control)
    min over shifts:  A(u²+v²)+2Buv+2L(u+v) ≥ −2L²/(A+B)   (eq:BogIneq's κ-term).

The true quantum zero-point constant `−(A−√(A²−B²))` of eq:BogIneq comes from
the CCR commutators `[a,a†]=1`; the c-number facts here are the finite-rank
algebra on which any mode/Fock replay of thm:BogHamDiag rests.
-/

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology

/-- `s := √(A²−B²)`, the spectral-gap constant of the 2×2 Bogoliubov matrix. -/
noncomputable def bogS (A B : ℝ) : ℝ := Real.sqrt (A ^ 2 - B ^ 2)

/-- `D := (A + s)/2`, the "positive part" coefficient in the Bogoliubov diagonalization. -/
noncomputable def bogD (A B : ℝ) : ℝ := (A + bogS A B) / 2

/-- `α := B/(A+s)`, the squeezing parameter (`|α| < 1` in the strict regime). -/
noncomputable def bogAlpha (A B : ℝ) : ℝ := B / (A + bogS A B)

lemma bogS_nonneg (A B : ℝ) : 0 ≤ bogS A B := by
  exact Real.sqrt_nonneg (A ^ 2 - B ^ 2)

lemma bogS_sq {A B : ℝ} (hB : |B| ≤ A) : bogS A B ^ 2 = A ^ 2 - B ^ 2 := by
  have hb2le : B ^ 2 ≤ A ^ 2 := by
    exact sq_le_sq' (abs_le.mp hB).1 (abs_le.mp hB).2
  unfold bogS
  rw [Real.sq_sqrt (by nlinarith [hb2le])]

lemma bogS_sq_le {A B : ℝ} (hA : 0 ≤ A) (hB : |B| ≤ A) : bogS A B ≤ A := by
  unfold bogS
  calc
    Real.sqrt (A ^ 2 - B ^ 2) ≤ Real.sqrt (A ^ 2) := by
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg B])
    _ = A := by rw [Real.sqrt_sq hA]

lemma bog_denom_ne_zero {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) : A + bogS A B ≠ 0 := by
  have hs : 0 ≤ bogS A B := bogS_nonneg A B
  nlinarith

lemma bog_A_sub_s_eq {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    A - bogS A B = B ^ 2 / (A + bogS A B) := by
  have hneq : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hsq : bogS A B ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  field_simp [hneq]
  nlinarith

lemma bogD_def {A B : ℝ} : bogD A B = (A + bogS A B) / 2 := by
  rfl

lemma bogD_pos {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) : 0 < bogD A B := by
  unfold bogD
  have hs : 0 ≤ bogS A B := bogS_nonneg A B
  nlinarith

lemma bog_alpha_mul_D {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    bogAlpha A B * bogD A B = B / 2 := by
  unfold bogAlpha bogD
  field_simp [bog_denom_ne_zero hA hB]

lemma bog_D_mul_one_add_alpha_sq {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    bogD A B * (1 + bogAlpha A B ^ 2) = A := by
  have hneq : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hsq : bogS A B ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  unfold bogAlpha bogD
  field_simp [hneq]
  nlinarith [hsq]

/-- The c-number core of eq:BogIdentity: the 2-mode quadratic form is a perfect
square after the Bogoliubov (squeezing) rotation `(u,v) ↦ (u+αv, v+αu)`. -/
lemma bog_two_mode_identity {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (u v : ℝ) :
    A * (u ^ 2 + v ^ 2) + 2 * B * u * v =
      bogD A B * ((u + bogAlpha A B * v) ^ 2 + (v + bogAlpha A B * u) ^ 2) := by
  have hDA : bogD A B * (1 + bogAlpha A B ^ 2) = A := bog_D_mul_one_add_alpha_sq hA hB
  have hαD : bogAlpha A B * bogD A B = B / 2 := bog_alpha_mul_D hA hB
  have h2 : 4 * bogD A B * bogAlpha A B = 2 * B := by
    calc
      4 * bogD A B * bogAlpha A B = 4 * (bogAlpha A B * bogD A B) := by ring
      _ = 4 * (B / 2) := by rw [hαD]
      _ = 2 * B := by ring
  symm
  calc
    bogD A B * ((u + bogAlpha A B * v) ^ 2 + (v + bogAlpha A B * u) ^ 2)
        = bogD A B * ((1 + bogAlpha A B ^ 2) * (u ^ 2 + v ^ 2) +
            4 * bogAlpha A B * u * v) := by ring
    _ = (bogD A B * (1 + bogAlpha A B ^ 2)) * (u ^ 2 + v ^ 2) +
          (4 * bogD A B * bogAlpha A B) * (u * v) := by ring
    _ = A * (u ^ 2 + v ^ 2) + 2 * B * u * v := by
      rw [hDA, h2]
      ring

/-- The 2-mode Bogoliubov matrix `[[A,B],[B,A]]` is positive semidefinite when
`0 ≤ A` and `|B| ≤ A`. -/
lemma bog_two_mode_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : |B| ≤ A) (u v : ℝ) :
    0 ≤ A * (u ^ 2 + v ^ 2) + 2 * B * u * v := by
  have hBA : -A ≤ B := (abs_le.mp hB).1
  have hBleA : B ≤ A := (abs_le.mp hB).2
  have hApB : 0 ≤ A + B := by linarith
  have hAmB : 0 ≤ A - B := by linarith
  calc
    A * (u ^ 2 + v ^ 2) + 2 * B * u * v
        = (A + B) / 2 * (u + v) ^ 2 + (A - B) / 2 * (u - v) ^ 2 := by ring
    _ ≥ 0 := by
      have h1 : 0 ≤ (A + B) / 2 * (u + v) ^ 2 :=
        mul_nonneg (div_nonneg hApB (by norm_num)) (sq_nonneg (u + v))
      have h2 : 0 ≤ (A - B) / 2 * (u - v) ^ 2 :=
        mul_nonneg (div_nonneg hAmB (by norm_num)) (sq_nonneg (u - v))
      linarith

/-- eq:BogIneq's linear-shift (κ-term) bound in c-number form:
`A(u²+v²)+2Buv+2L(u+v) ≥ −2L²/(A+B)` whenever `A+B > 0` and `|B| ≤ A`. -/
lemma bog_linear_shift {A B L : ℝ} (hAB : 0 < A + B) (hB : |B| ≤ A) (u v : ℝ) :
    0 ≤ A * (u ^ 2 + v ^ 2) + 2 * B * u * v + 2 * L * (u + v) +
      2 * L ^ 2 / (A + B) := by
  have hBleA : B ≤ A := (abs_le.mp hB).2
  have hAmB : 0 ≤ A - B := by linarith
  have hApB_ne : A + B ≠ 0 := ne_of_gt hAB
  have hsquare :
      A * (u ^ 2 + v ^ 2) + 2 * B * u * v + 2 * L * (u + v) + 2 * L ^ 2 / (A + B)
        = (A - B) / 2 * (u - v) ^ 2 + (A + B) / 2 * (u + v + 2 * L / (A + B)) ^ 2 := by
    field_simp [hApB_ne]
    ring
  rw [hsquare]
  have h1 : 0 ≤ (A - B) / 2 * (u - v) ^ 2 :=
    mul_nonneg (div_nonneg hAmB (by norm_num)) (sq_nonneg (u - v))
  have h2 : 0 ≤ (A + B) / 2 * (u + v + 2 * L / (A + B)) ^ 2 := by
    exact mul_nonneg (div_nonneg (le_of_lt hAB) (by norm_num)) (sq_nonneg _)
  linarith

/-- `A − √(A²−B²) = B²/(A + √(A²−B²)) ≤ B²/A` — the Taylor control used in
eq:Rough2 (`−(A−√) ≥ −(1/2+Cε)|B|²/A` follows by scaling). -/
lemma bog_A_sub_s_le {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    A - bogS A B ≤ B ^ 2 / A := by
  rw [bog_A_sub_s_eq hA hB]
  exact div_le_div_of_nonneg_left (sq_nonneg B) hA (by
    have hs : 0 ≤ bogS A B := bogS_nonneg A B
    nlinarith)

end BoseGases
end Submission
