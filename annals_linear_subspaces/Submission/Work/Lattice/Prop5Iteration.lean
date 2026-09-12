import Mathlib
import Submission.Work.Lattice.BatchExtraction
import Submission.Work.Lattice.MaxPhiFlag
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank
import Submission.Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq

/-!
# Prop 5: the iteration step (I) — dominated lattice families in orthonormal form

The paper's Prop 5 constructs the family `v_1, …, v_ℓ` by induction; at each step it replaces the
vectors already produced by an orthonormal basis of their span (the `π₊`-dominance is a property of
the *plane*, not of the basis) and then extends that orthonormal family inside the next flag
member.

This module records the first, basis-free ingredient: **the `π₊`-dominance ratio
`‖π₊(⋀^m v)‖ / ‖⋀^m v‖` depends only on the plane `span ℝ v`**, so a dominated lattice family can
be replaced by an orthonormal family with the same dominance:

* `exists_orthonormal_dominated` — given `v` `ℝ`-independent with
  `c‖⋀^m v‖ ≤ ‖blockElem (⋀^m v) 0‖`, there is an orthonormal `e` with
  `c‖⋀^m e‖ ≤ ‖blockElem (⋀^m e) 0‖`.

Module `Submission.Work.Lattice.Prop5Iteration`, namespace `Submission.Prop5Iteration`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.Prop5Iteration

open Submission.GraysonData
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm

variable {d : ℕ}

/-- **The dominance ratio is a plane invariant.**  A dominated `ℝ`-independent family can be
replaced by an orthonormal family with the same `π₊`-dominance. -/
theorem exists_orthonormal_dominated {m ℓ : ℕ} (hm : 0 < m) {v : Fin m → E d}
    (hvli : LinearIndependent ℝ v) {c : ℝ}
    (hdom : c * ‖exteriorPower.ιMulti ℝ m v‖ ≤
      ‖blockElem (d := d) (k := m) (ℓ := ℓ) (exteriorPower.ιMulti ℝ m v) 0‖) :
    ∃ e : Fin m → E d, Orthonormal ℝ e ∧
      c * ‖exteriorPower.ιMulti ℝ m e‖ ≤
        ‖blockElem (d := d) (k := m) (ℓ := ℓ) (exteriorPower.ιMulti ℝ m e) 0‖ := by
  classical
  set W : Submodule ℝ (E d) := Submodule.span ℝ (Set.range v) with hW
  have hfin : Module.finrank ℝ W = m := by
    rw [hW, finrank_span_eq_card hvli, Fintype.card_fin]
  obtain ⟨e, heON, -, hespan⟩ :=
    Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank W hfin
  have hspan : Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range v) := by
    rw [hespan, hW]
  obtain ⟨a, ha0, ha⟩ :=
    Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq e v
      heON.linearIndependent hvli hspan
  have hnormE : ‖exteriorPower.ιMulti ℝ m e‖ = 1 :=
    Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e heON hm
  have hv : exteriorPower.ιMulti ℝ m v = a⁻¹ • exteriorPower.ιMulti ℝ m e := by
    rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have hblk : ‖blockElem (d := d) (k := m) (ℓ := ℓ) (exteriorPower.ιMulti ℝ m v) 0‖ =
      |a|⁻¹ * ‖blockElem (d := d) (k := m) (ℓ := ℓ) (exteriorPower.ιMulti ℝ m e) 0‖ := by
    rw [hv, blockElem_smul, norm_smul, Real.norm_eq_abs, abs_inv]
  have hnormV : ‖exteriorPower.ιMulti ℝ m v‖ = |a|⁻¹ := by
    rw [hv, norm_smul, hnormE, mul_one, Real.norm_eq_abs, abs_inv]
  rw [hnormV, hblk] at hdom
  refine ⟨e, heON, ?_⟩
  rw [hnormE, mul_one]
  rw [mul_comm c] at hdom
  exact le_of_mul_le_mul_left hdom (inv_pos.mpr (abs_pos.mpr ha0))


/-! ## The `ε`-parameter sequence of the orthonormal extension

`Lemma5Extension.exists_orthonormal_cone_family` needs a positive non-increasing sequence `εseq`
with `εseq (s+1) = εseq s · γ s` and `2^i (γ s)^{i-s} < εseq s`.  A constant `γ` cannot work for
`i − m ≥ 2` (at `s = i−1` the constraints force `2^i < 1`), so the pair is defined by *recursion*:
`γ s := (εseq s / 2^{i+1})^{1/(i-s)}`, which satisfies the key inequality with room to spare. -/

/-- The recursively defined `ε`-sequence: `f 0 = e₀`,
`f (k+1) = f k · (f k / 2^{i+1})^{1/(i-m-k)}`. -/
noncomputable def epsSeq (i m : ℕ) (e₀ : ℝ) : ℕ → ℝ :=
  fun k => Nat.rec e₀ (fun k ih => ih * (ih / (2 : ℝ) ^ (i + 1)) ^ ((1 : ℝ) / ((i - m - k : ℕ) : ℝ))) k

lemma epsSeq_zero (i m : ℕ) (e₀ : ℝ) : epsSeq i m e₀ 0 = e₀ := rfl

lemma epsSeq_succ (i m : ℕ) (e₀ : ℝ) (k : ℕ) :
    epsSeq i m e₀ (k + 1) = epsSeq i m e₀ k *
      (epsSeq i m e₀ k / (2 : ℝ) ^ (i + 1)) ^ ((1 : ℝ) / ((i - m - k : ℕ) : ℝ)) := rfl

/-- The recursive sequence is positive when `e₀ > 0`. -/
lemma epsSeq_pos {i m : ℕ} {e₀ : ℝ} (he₀ : 0 < e₀) : ∀ k, 0 < epsSeq i m e₀ k := by
  intro k
  induction k with
  | zero => exact he₀
  | succ k ih =>
      rw [epsSeq_succ]
      exact mul_pos ih (Real.rpow_pos_of_pos (div_pos ih (by positivity)) _)

/-- The recursive sequence stays below `e₀` when `0 < e₀ ≤ 1`. -/
lemma epsSeq_le_zero {i m : ℕ} {e₀ : ℝ} (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) :
    ∀ k, epsSeq i m e₀ k ≤ e₀ := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      have hpos := epsSeq_pos (i := i) (m := m) he₀ k
      rw [epsSeq_succ]
      have hb : epsSeq i m e₀ k / (2 : ℝ) ^ (i + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact le_trans ih (le_trans he₁ (one_le_pow₀ (by norm_num)))
      calc epsSeq i m e₀ k *
            (epsSeq i m e₀ k / (2 : ℝ) ^ (i + 1)) ^ ((1 : ℝ) / ((i - m - k : ℕ) : ℝ))
          ≤ epsSeq i m e₀ k * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ hpos.le
            exact Real.rpow_le_one (div_nonneg hpos.le (by positivity)) hb (by positivity)
        _ ≤ e₀ := by rw [mul_one]; exact ih

/-- The recursive sequence is non-increasing when `0 < e₀ ≤ 1`. -/
lemma epsSeq_anti {i m : ℕ} {e₀ : ℝ} (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) :
    ∀ k, epsSeq i m e₀ (k + 1) ≤ epsSeq i m e₀ k := by
  intro k
  have hpos := epsSeq_pos (i := i) (m := m) he₀ k
  rw [epsSeq_succ]
  have hb : epsSeq i m e₀ k / (2 : ℝ) ^ (i + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact le_trans (epsSeq_le_zero (i := i) (m := m) he₀ he₁ k)
      (le_trans he₁ (one_le_pow₀ (by norm_num)))
  calc epsSeq i m e₀ k *
        (epsSeq i m e₀ k / (2 : ℝ) ^ (i + 1)) ^ ((1 : ℝ) / ((i - m - k : ℕ) : ℝ))
      ≤ epsSeq i m e₀ k * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        exact Real.rpow_le_one (div_nonneg hpos.le (by positivity)) hb (by positivity)
    _ = epsSeq i m e₀ k := mul_one _

/-- **The `ε`-sequence exists.**  For `m < i` and `0 < e₀ ≤ 1` there are positive sequences
`εseq` (non-increasing, `εseq m = e₀`) and `γ` (`0 < γ ≤ 1`) with
`2^i (γ s)^{i-s} < εseq s` and `εseq (s+1) = εseq s · γ s` for `m ≤ s < i`. -/
theorem exists_epsSeq {i m : ℕ} (_hmi : m < i) {e₀ : ℝ} (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) :
    ∃ (εseq γ : ℕ → ℝ), (∀ s, 0 < εseq s) ∧ (∀ s, εseq s ≤ εseq m) ∧ εseq m = e₀ ∧
      (∀ s, 0 < γ s) ∧ (∀ s, γ s ≤ 1) ∧
      (∀ s, m ≤ s → s < i →
        (2 : ℝ) ^ i * (γ s) ^ (i - s) < εseq s ∧ εseq (s + 1) = εseq s * γ s) := by
  classical
  let εseq : ℕ → ℝ := fun s => if s ≤ m then e₀ else epsSeq i m e₀ (s - m)
  let γ : ℕ → ℝ := fun s =>
    if m ≤ s ∧ s < i then
      (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^ ((1 : ℝ) / ((i - s : ℕ) : ℝ))
    else 1
  refine ⟨εseq, γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simp only [εseq]
    by_cases h : s ≤ m
    · rw [if_pos h]; exact he₀
    · rw [if_neg h]; exact epsSeq_pos (i := i) (m := m) he₀ (s - m)
  · intro s
    have hm : εseq m = e₀ := by simp only [εseq]; rw [if_pos le_rfl]
    rw [hm]
    simp only [εseq]
    by_cases h : s ≤ m
    · rw [if_pos h]
    · rw [if_neg h]
      exact epsSeq_le_zero (i := i) (m := m) he₀ he₁ (s - m)
  · simp only [εseq]; rw [if_pos le_rfl]
  · intro s
    simp only [γ]
    by_cases h : m ≤ s ∧ s < i
    · rw [if_pos h]
      exact Real.rpow_pos_of_pos (div_pos (epsSeq_pos (i := i) (m := m) he₀ (s - m)) (by positivity)) _
    · rw [if_neg h]; norm_num
  · intro s
    simp only [γ]
    by_cases h : m ≤ s ∧ s < i
    · rw [if_pos h]
      refine Real.rpow_le_one (div_nonneg (epsSeq_pos (i := i) (m := m) he₀ _).le (by positivity)) ?_ (by positivity)
      rw [div_le_one (by positivity)]
      exact le_trans (epsSeq_le_zero (i := i) (m := m) he₀ he₁ (s - m))
        (le_trans he₁ (one_le_pow₀ (by norm_num)))
    · rw [if_neg h]
  · intro s hms hsi
    have hcond : m ≤ s ∧ s < i := ⟨hms, hsi⟩
    have hε : εseq s = epsSeq i m e₀ (s - m) := by
      simp only [εseq]
      by_cases hs : s ≤ m
      · rw [if_pos hs]
        have hsm : s = m := le_antisymm hs hms
        rw [hsm, Nat.sub_self, epsSeq_zero]
      · rw [if_neg hs]
    constructor
    · rw [show γ s = (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^
          ((1 : ℝ) / ((i - s : ℕ) : ℝ)) from by simp only [γ]; rw [if_pos hcond], hε]
      have hne : ((i - s : ℕ) : ℝ) ≠ 0 := by
        have : 0 < i - s := Nat.sub_pos_of_lt hsi
        exact_mod_cast Nat.pos_iff_ne_zero.mp this
      have hpow : ((epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^
          ((1 : ℝ) / ((i - s : ℕ) : ℝ))) ^ (i - s) =
          epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (div_nonneg (epsSeq_pos (i := i) (m := m) he₀ _).le (by positivity))]
        rw [one_div, inv_mul_cancel₀ hne, Real.rpow_one]
      have hpos := epsSeq_pos (i := i) (m := m) he₀ (s - m)
      have h2 : (2 : ℝ) ^ i * (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) =
          epsSeq i m e₀ (s - m) / 2 := by
        rw [mul_div_assoc', pow_succ]
        field_simp
      rw [hpow, h2]
      linarith [hpos]
    · have hs1 : ¬ (s + 1 ≤ m) := by omega
      have hγ : γ s = (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^
          ((1 : ℝ) / ((i - s : ℕ) : ℝ)) := by
        simp only [γ]; rw [if_pos hcond]
      have hsub : s + 1 - m = (s - m) + 1 := by omega
      have hexp : i - m - (s - m) = i - s := by omega
      rw [show εseq (s + 1) = epsSeq i m e₀ (s + 1 - m) from by
            simp only [εseq]; rw [if_neg hs1], hsub, epsSeq_succ, hε, hγ, hexp]

theorem exists_epsSeq_expl {i m : ℕ} (hmi : m < i) {e₀ : ℝ} (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) :
    ∃ (εseq γ : ℕ → ℝ), (∀ s, 0 < εseq s) ∧ (∀ s, εseq s ≤ εseq m) ∧ εseq m = e₀ ∧
      (∀ s, 0 < γ s) ∧ (∀ s, γ s ≤ 1) ∧
      (∀ s, m ≤ s → s < i →
        (2 : ℝ) ^ i * (γ s) ^ (i - s) < εseq s ∧ εseq (s + 1) = εseq s * γ s) ∧
      εseq i = epsSeq i m e₀ (i - m) := by
  classical
  let εseq : ℕ → ℝ := fun s => if s ≤ m then e₀ else epsSeq i m e₀ (s - m)
  let γ : ℕ → ℝ := fun s =>
    if m ≤ s ∧ s < i then
      (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^ ((1 : ℝ) / ((i - s : ℕ) : ℝ))
    else 1
  refine ⟨εseq, γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simp only [εseq]
    by_cases h : s ≤ m
    · rw [if_pos h]; exact he₀
    · rw [if_neg h]; exact epsSeq_pos (i := i) (m := m) he₀ (s - m)
  · intro s
    have hm : εseq m = e₀ := by simp only [εseq]; rw [if_pos le_rfl]
    rw [hm]
    simp only [εseq]
    by_cases h : s ≤ m
    · rw [if_pos h]
    · rw [if_neg h]
      exact epsSeq_le_zero (i := i) (m := m) he₀ he₁ (s - m)
  · simp only [εseq]; rw [if_pos le_rfl]
  · intro s
    simp only [γ]
    by_cases h : m ≤ s ∧ s < i
    · rw [if_pos h]
      exact Real.rpow_pos_of_pos (div_pos (epsSeq_pos (i := i) (m := m) he₀ (s - m)) (by positivity)) _
    · rw [if_neg h]; norm_num
  · intro s
    simp only [γ]
    by_cases h : m ≤ s ∧ s < i
    · rw [if_pos h]
      refine Real.rpow_le_one (div_nonneg (epsSeq_pos (i := i) (m := m) he₀ _).le (by positivity)) ?_ (by positivity)
      rw [div_le_one (by positivity)]
      exact le_trans (epsSeq_le_zero (i := i) (m := m) he₀ he₁ (s - m))
        (le_trans he₁ (one_le_pow₀ (by norm_num)))
    · rw [if_neg h]
  · intro s hms hsi
    have hcond : m ≤ s ∧ s < i := ⟨hms, hsi⟩
    have hε : εseq s = epsSeq i m e₀ (s - m) := by
      simp only [εseq]
      by_cases hs : s ≤ m
      · rw [if_pos hs]
        have hsm : s = m := le_antisymm hs hms
        rw [hsm, Nat.sub_self, epsSeq_zero]
      · rw [if_neg hs]
    constructor
    · rw [show γ s = (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^
          ((1 : ℝ) / ((i - s : ℕ) : ℝ)) from by simp only [γ]; rw [if_pos hcond], hε]
      have hne : ((i - s : ℕ) : ℝ) ≠ 0 := by
        have : 0 < i - s := Nat.sub_pos_of_lt hsi
        exact_mod_cast Nat.pos_iff_ne_zero.mp this
      have hpow : ((epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^
          ((1 : ℝ) / ((i - s : ℕ) : ℝ))) ^ (i - s) =
          epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (div_nonneg (epsSeq_pos (i := i) (m := m) he₀ _).le (by positivity))]
        rw [one_div, inv_mul_cancel₀ hne, Real.rpow_one]
      have hpos := epsSeq_pos (i := i) (m := m) he₀ (s - m)
      have h2 : (2 : ℝ) ^ i * (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) =
          epsSeq i m e₀ (s - m) / 2 := by
        rw [mul_div_assoc', pow_succ]
        field_simp
      rw [hpow, h2]
      linarith [hpos]
    · have hs1 : ¬ (s + 1 ≤ m) := by omega
      have hγ : γ s = (epsSeq i m e₀ (s - m) / (2 : ℝ) ^ (i + 1)) ^
          ((1 : ℝ) / ((i - s : ℕ) : ℝ)) := by
        simp only [γ]; rw [if_pos hcond]
      have hsub : s + 1 - m = (s - m) + 1 := by omega
      have hexp : i - m - (s - m) = i - s := by omega
      rw [show εseq (s + 1) = epsSeq i m e₀ (s + 1 - m) from by
            simp only [εseq]; rw [if_neg hs1], hsub, epsSeq_succ, hε, hγ, hexp]
  · simp only [εseq]
    rw [if_neg (by omega : ¬ (i ≤ m))]


end Submission.Prop5Iteration

end
