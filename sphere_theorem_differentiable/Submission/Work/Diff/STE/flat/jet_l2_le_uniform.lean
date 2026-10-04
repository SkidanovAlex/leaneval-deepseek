/-
# `Work.Diff.STE.flat.jet_l2_le_uniform`

The `L²` bounds for the jets of a box-supported Fourier series, with a constant that is *uniform
in the order* `m ≤ s` (and in the box level `N` and the coefficient family `c`).  This is
`Work.Diff.STE.flat.jet_l2_le` with `∃ C` moved outside the quantifiers over `m`, `N`, `c`.

Proof: `jet_l2_le`'s argument shows that the constant for a single order `m` is
`(2π)^{2m} · C(s)`, and `(2π)^{2m} ≤ (2π)^{2s}` for `m ≤ s`.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators
open Work.Diff.STE.Flat

/-- `CSq` is monotone in the level. -/
lemma csq_mono_level {n : ℕ} {k m : ℕ} (hkm : k ≤ m) (d : (Fin n → ℤ) → ℂ)
    (h : Summable (fun a : Fin n → ℤ => (wt a) ^ m * ‖d a‖ ^ 2)) : CSq k d ≤ CSq m d := by
  rw [CSq, CSq]
  refine Summable.tsum_le_tsum (fun a => ?_) ?_ h
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (wt_one_le a) hkm) (sq_nonneg _)
  · exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg (pow_nonneg (le_of_lt (wt_pos a)) k) (sq_nonneg _))
      (fun a => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (wt_one_le a) hkm)
        (sq_nonneg _)) h

theorem jet_l2_le_uniform {n s : ℕ} (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (hm : m ≤ s) (N : ℕ)
      (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      ∀ (l : Fin m → Fin n) (i j : Fin n),
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖Work.Diff.STE.pdVec m l (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) x‖ ^ 2
          ≤ C * Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) := by
  classical
  -- the constant only comes from `CSq s cᵢⱼ ≤ Cq * ENormSqFull s u`: it is uniform in `c`
  obtain ⟨Cq, hCqnn, hCq⟩ := CSq_le_ENormSq_seriesFun (ι := Fin n) s
  refine ⟨(2 * Real.pi) ^ (2 * s) * Cq, mul_nonneg (by positivity) hCqnn, ?_⟩
  intro m hm N c hc l i j
  -- all the polynomial moments of the (finitely supported) entry family are summable
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  -- the entry series and its iterated derivative
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext y; rw [seriesFunM_apply]
  have hpd : pdVec m l (fun y => seriesFunM c y i j)
      = seriesFun (dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j)) := by
    rw [pdVec, hfun]
    exact funext (fun x => pdList_seriesFun (List.ofFn l)
      (fun k : Fin n → ℤ => c k i j) hmom x)
  -- Parseval turns the `L²` norm of the differentiated series into an `ℓ²` sum
  have hL2 : (∫ x in unitCube (ι := Fin n),
        ‖seriesFun (dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j)) x‖ ^ 2)
      = ∑' k : Fin n → ℤ, ‖dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j) k‖ ^ 2 :=
    ens_integral_normSq_seriesFun (dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j))
      (by simpa using summable_dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j) hmom 0)
  rw [hpd, hL2]
  have h1 : (∑' k : Fin n → ℤ, ‖dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j) k‖ ^ 2)
      ≤ (2 * Real.pi) ^ (2 * m) * CSq m (fun k : Fin n → ℤ => c k i j) := by
    have h := tsum_normSq_dmulV_le (List.ofFn l) (fun k : Fin n → ℤ => c k i j) hmom
    rw [List.length_ofFn, ← pow_mul] at h
    exact h
  have h2 : (2 * Real.pi) ^ (2 * m) ≤ (2 * Real.pi) ^ (2 * s) :=
    pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) (by omega)
  have h3 : CSq m (fun k : Fin n → ℤ => c k i j) ≤ CSq s (fun k : Fin n → ℤ => c k i j) :=
    csq_mono_level hm _ (summable_wt_pow_mul_norm_sq (fun k : Fin n → ℤ => c k i j) hmom s)
  have h4 : CSq s (fun k : Fin n → ℤ => c k i j)
      ≤ Cq * ENormSqFull s (seriesFunM c) := by
    refine (hCq (fun k : Fin n → ℤ => c k i j) hmom).trans ?_
    rw [ENormSqFull]
    refine mul_le_mul_of_nonneg_left ?_ hCqnn
    have hEs : ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM s (seriesFunM c) := by
      rw [← hfun]
      exact ENormSq_le_ENormSqM (seriesFunM c) i j
    have hE0 : ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      rw [← hfun]
      exact ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
    exact add_le_add hEs hE0
  calc (∑' k : Fin n → ℤ, ‖dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j) k‖ ^ 2)
      ≤ (2 * Real.pi) ^ (2 * m) * CSq m (fun k : Fin n → ℤ => c k i j) := h1
    _ ≤ (2 * Real.pi) ^ (2 * s) * CSq s (fun k : Fin n → ℤ => c k i j) :=
        mul_le_mul h2 h3 (CSq_nonneg' m (fun k : Fin n → ℤ => c k i j)) (by positivity)
    _ ≤ (2 * Real.pi) ^ (2 * s) * (Cq * ENormSqFull s (seriesFunM c)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (2 * Real.pi) ^ (2 * s) * Cq * ENormSqFull s (seriesFunM c) := by ring

end Work.Diff.STE.flat
