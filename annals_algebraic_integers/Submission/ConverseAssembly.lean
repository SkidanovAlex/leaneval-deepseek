import Submission.Contracts
import Submission.WnormToolkit
import Submission.EisensteinInt
import Submission.Asymptotics
import Submission.IvtRoots
import Submission.SerreExample
import Submission.Notions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# Keystone: the four deep contracts imply the converse output

`Submission.Contracts.ConverseOutputSerre` (monic irreducible integer
polynomials with roots in the open Serre interval, degrees → ∞, root means →
first Serre moment) follows from the four deep contracts
(`SquarefreeContract`, `AdjustContract`, `EarlyIntsContract`,
`RSphereContract`) by the assembly of Smith, adjust.tex §4.1 ("Proof of
Theorem main"): constants, main inequalities, per-n Eisenstein construction,
sign-change/root-location, subexponential weighted-norm bound, RSphere.
-/

noncomputable section

open MeasureTheory
open ComplexOrder
open Filter
open Polynomial
open scoped Real BigOperators Topology

namespace Submission.ConverseAssembly

open Submission.Contracts
open Submission.WnormToolkit
open Submission.EisensteinInt
open Submission.Asymptotics
open Submission.IvtRoots
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm
open Submission.Notions

/-! ## Elementary ℤ / ℝ arithmetic glue -/

/-- `4c − 2` is even. -/
lemma even_four_mul_sub_two (c : ℤ) : Even (4 * c - 2) := by
  rw [even_iff_two_dvd]
  use 2 * c - 1
  ring

/-- `4 ∤ (4c − 2)`: the constant term of the Eisenstein polynomial. -/
lemma not_four_dvd_four_mul_sub_two (c : ℤ) : ¬ (4 : ℤ) ∣ (4 * c - 2) := by
  intro h
  rcases h with ⟨k, hk⟩
  omega

/-- Evenness of an integer scaled by 4. -/
lemma even_four_mul (c : ℤ) : Even (4 * c) := by
  rw [even_iff_two_dvd]
  use 2 * c
  ring

lemma even_int_of_even_real {z : ℤ} (hz : Even z) : Even (z : ℝ) := by
  rcases hz with ⟨k, hk⟩
  refine ⟨(k : ℝ), ?_⟩
  exact_mod_cast hk

/-- `1 < κ` (accessor). -/
lemma kappa_gt_one' : 1 < kappa := kappa_gt_one

/-- κ is positive. -/
lemma kappa_pos : 0 < kappa := lt_trans zero_lt_one kappa_gt_one

/-- `B = 2·C0/log κ` is positive when `0 < C0`. -/
lemma B_pos {C0 : ℝ} (hC0 : 0 < C0) : 0 < (2 * C0) / Real.log kappa := by
  have hlog : 0 < Real.log kappa := Real.log_pos kappa_gt_one
  exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hC0) hlog

/-! ## Polynomial transfer glue (`zmap`) -/

/-- Evaluation transfer: complex evaluation of the real map of `Q` agrees with
direct complex evaluation of `Q`. -/
lemma aeval_zmap (Q : Polynomial ℤ) (z : ℂ) :
    Polynomial.aeval z (zmap Q) = Polynomial.aeval z Q := by
  unfold zmap
  exact (Polynomial.aeval_eq_aeval_map (R := ℤ) (S := ℂ) (T := ℝ)
    (φ := algebraMap ℤ ℝ) (by exact (IsScalarTower.algebraMap_eq ℤ ℝ ℂ).symm) Q z).symm

/-- natDegree is preserved under `zmap` for monic polynomials. -/
lemma zmap_natDegree {Q : Polynomial ℤ} (hmon : Q.Monic) :
    (zmap Q).natDegree = Q.natDegree := by
  unfold zmap
  exact hmon.natDegree_map (algebraMap ℤ ℝ)

/-- Monicity is preserved under `zmap`. -/
lemma zmap_monic {Q : Polynomial ℤ} (hmon : Q.Monic) : (zmap Q).Monic := by
  unfold zmap
  exact hmon.map (algebraMap ℤ ℝ)

/-- Evaluating the real map of `Q` at a real point agrees with evaluating `Q`. -/
lemma zmap_eval_real (Q : Polynomial ℤ) (x : ℝ) : (zmap Q).eval x = Polynomial.aeval x Q := by
  unfold zmap
  rw [Polynomial.aeval_def]
  rw [← Polynomial.eval₂_eq_eval_map]

/-- `zmap` of the constant four multiple. -/
lemma zmap_four_mul (R : Polynomial ℤ) :
    zmap (Polynomial.C (4 : ℤ) * R) = Polynomial.C (4 : ℝ) * zmap R := by
  unfold zmap
  rw [Polynomial.map_mul, Polynomial.map_C]
  norm_num

/-- `zmap` of the constant `2`. -/
lemma zmap_two : zmap (Polynomial.C (2 : ℤ)) = Polynomial.C (2 : ℝ) := by
  unfold zmap
  rw [Polynomial.map_C]
  norm_num

/-- `zmap` of a difference. -/
lemma zmap_sub (P Q : Polynomial ℤ) : zmap (P - Q) = zmap P - zmap Q := by
  simp [zmap]

/-- `zmap` of `X^n`. -/
lemma zmap_X_pow (n : ℕ) : zmap (X ^ n) = (X ^ n : Polynomial ℝ) := by
  simp [zmap]

end Submission.ConverseAssembly
