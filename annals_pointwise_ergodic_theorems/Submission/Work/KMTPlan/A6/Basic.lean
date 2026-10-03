/-
# Elementary tools for the high–high case of Area A6

This module collects the elementary (purely formal) tools used by the high–high case
(`Work.KMTPlan.A6.highHigh`) of the contract's Area A6:

* `variationalNorm_le_three_tsum_enorm` — the pointwise bound
  `V^r(u) ≤ 3 ∑'_n ‖u n‖` for `r ≥ 1` (via `Submission.VarCoeff.variationalNorm_mul_le`);
* `eLpNorm_variationalNorm_one_le_tsum` — its `ℓ¹` form, which is what replaces the finite-sum
  bound `Work.Analysis.SingleScale.eLpNorm_variationalNorm_le_sum` when the index set of scales is
  infinite (as it is for the paraproduct columns `varpCol` when the height parameters are small);
* `logN_pos` — `1 ≤ logN N`;
* `eLpNorm_varpPiece_le` — the single-scale (anf) bound for the contract's columns: on the index
  set, the clamped column is the unclamped one, and its `ℓ¹` norm is at most
  `‖F‖_{ℓ²} ‖G‖_{ℓ²}`.
-/
import Submission.Work.KMTPlan.Model
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## The variational norm of a series -/

/-- **`V^r(u) ≤ 3 ∑'_n ‖u n‖`.**  For `r ≥ 1`, the `V^r`-norm of a sequence is at most three
times the sum of the (pointwise) norms of its entries; this is the "counted with multiplicity"
form of the variational norm, and it is the form in which the summation over an arbitrary set of
scales is performed in the high–high case.  (Compare
`Work.Analysis.SingleScale.variationalNorm_le_sum_enorm`, which is the finitely supported
version.) -/
lemma variationalNorm_le_three_tsum_enorm {r : ℝ≥0} (hr : 1 ≤ r) (u : ℕ → ℂ) :
    variationalNorm r u ≤ 3 * ∑' n, ‖u n‖ₑ := by
  have h := Submission.PointwiseErgodicTheorems.variationalNorm_mul_le (r := r) hr
    (m := fun _ : ℕ => 1) (d := fun (_ : ℕ) (_ : ℕ) => (1 : ℂ))
    (b := fun k n => if k = n then u n else 0)
    (fun k n => by simp)
    (fun n => ⟨n + 1, fun k hk => by
      have hkn : k ≠ n := by omega
      simp [hkn]⟩)
  have h1 : (fun n : ℕ => ∑' k, (1 : ℂ) * (if k = n then u n else (0 : ℂ))) = u := by
    funext n
    rw [tsum_eq_single n]
    · simp
    · intro k hk
      simp [hk]
  have h3 : ∀ n : ℕ, (↑(1 : ℕ) : ℝ≥0∞)⁻¹ * (∑' k, ‖(if k = n then u n else (0 : ℂ))‖ₑ)
      = ‖u n‖ₑ := by
    intro n
    rw [tsum_eq_single n]
    · simp
    · intro k hk
      simp [hk]
  rw [h1] at h
  calc variationalNorm r u
      ≤ 3 * ∑' n, (↑(1 : ℕ) : ℝ≥0∞)⁻¹
          * (∑' k, ‖(if k = n then u n else (0 : ℂ))‖ₑ) := h
    _ = 3 * ∑' n, ‖u n‖ₑ := by rw [tsum_congr h3]

/-- **The `ℓ¹` form of `V^r(u) ≤ 3 ∑'_n ‖u n‖`.**  For a family `u : ℕ → ℤ → ℂ`,
`‖ V^r_n u_n ‖_{ℓ¹(ℤ)} ≤ 3 ∑'_n ‖ u n ‖_{ℓ¹(ℤ)}`. -/
lemma eLpNorm_variationalNorm_one_le_tsum {r : ℝ≥0} (hr : 1 ≤ r) (u : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x)) 1 Measure.count
      ≤ 3 * ∑' n, eLpNorm (fun x : ℤ => u n x) 1 Measure.count := by
  rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  have step1 : (∫⁻ x : ℤ, ‖variationalNorm r (fun n : ℕ => u n x)‖ₑ ∂Measure.count)
      ≤ ∫⁻ x : ℤ, (3 : ℝ≥0∞) * ∑' n, ‖u n x‖ₑ ∂Measure.count :=
    lintegral_mono (fun x => by
      rw [enorm_eq_self]
      exact variationalNorm_le_three_tsum_enorm hr (fun n => u n x))
  refine step1.trans ?_
  have hlin : (fun x : ℤ => (3 : ℝ≥0∞) * ∑' n, ‖u n x‖ₑ)
      = fun x : ℤ => ∑' n, (3 : ℝ≥0∞) * ‖u n x‖ₑ := by
    funext x
    rw [ENNReal.tsum_mul_left]
  rw [hlin]
  rw [MeasureTheory.lintegral_tsum
    (fun n => (measurable_of_countable (fun x : ℤ => (3 : ℝ≥0∞) * ‖u n x‖ₑ)).aemeasurable)]
  have hfac : (fun i : ℕ => ∫⁻ a : ℤ, (3 : ℝ≥0∞) * ‖u i a‖ₑ ∂Measure.count)
      = fun i : ℕ => 3 * eLpNorm (fun x : ℤ => u i x) 1 Measure.count := by
    funext i
    rw [MeasureTheory.lintegral_const_mul' 3 _ (by norm_num), eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  rw [hfac, ENNReal.tsum_mul_left]

/-! ## The logarithmic scale -/

/-- `1 ≤ logN N`. -/
lemma logN_pos (N : ℕ) : 1 ≤ logN N := by
  have h : 0 < Nat.log 2 (max N 2) := Nat.log_pos (by norm_num) (le_max_right N 2)
  simp only [logN]
  omega

/-! ## The single-scale bound for the columns -/

/-- On the index set the clamped column `varpCol` is the unclamped piece `varpPiece`. -/
lemma varpCol_eq_piece_of_indexSet {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {a : ℕ → ℝ≥0}
    {f g : ℤ → ℂ} {l₁ l₂ k₁ k₂ : ℕ} {n : ℕ}
    (h : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))) :
    varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n
      = varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ := by
  have h' : l₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧ l₂ ≤ heightScale C₀ (Nat.floor (a n)) ∧
      k₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧ k₂ ≤ heightScale C₀ (Nat.floor (a n)) := by
    simpa only [inIndexSet_iff_le] using h
  funext x
  exact varpCol_eq_piece (Pj := kmtPj ρ) (P := P) (d := P.natDegree) (C₀ := C₀) (a := a)
    (f := f) (g := g) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (n := n) (x := x)
    (by simpa only [inIndexSet_iff_le] using h')

/-- **(anf) at the columns.**  On the index set, the `ℓ¹` norm of a clamped column is at most
`‖f‖_{ℓ²} ‖g‖_{ℓ²}` (the single-scale Hölder bound of the paper, `SingleScale.eLpNorm_AhalfR_le`
at `q = 1`, `q₁ = q₂ = 2`). -/
lemma eLpNorm_varpCol_le {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {a : ℕ → ℝ≥0} {f g : ℤ → ℂ}
    {l₁ l₂ k₁ k₂ n : ℕ}
    (h : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)))
    (hf : MemLp (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count)
    (hg : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g)
      2 Measure.count) :
    eLpNorm (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
        1 Measure.count
      ≤ eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
        * eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g)
            2 Measure.count := by
  rw [varpCol_eq_piece_of_indexSet (P := P) h]
  refine eLpNorm_AhalfR_le TZ measurePreserving_TZ (a n) X P
    (q := 1) (q₁ := 2) (q₂ := 2) ?_ le_rfl hf hg
  rw [ENNReal.inv_two_add_inv_two, inv_one]

end

end Work.KMTPlan.A6
