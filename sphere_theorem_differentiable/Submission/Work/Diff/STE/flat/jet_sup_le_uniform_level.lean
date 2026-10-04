import Mathlib
import Submission.Work.Diff.STE.flat.level_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The uniform level-`s` sup bound for the jets of a box-supported coefficient family

`Work.Diff.STE.flat.level_step` needs the sup norms of the spatial derivatives of `seriesFunM c`
(up to order `s - sob n`) to be bounded *uniformly in the box size `N`, in the coefficient family
`c` and in the order `m`* of the derivative, by a constant times
`1 + √(ENormSqFull s (seriesFunM c))`.

`Work.Diff.STE.flat.jet_sup_le` (in `level_aux`) gives this bound for a fixed `N`, `c` and `m`, but
its constant is produced *inside* the quantifiers over `N`, `c`, `m`, so it is not immediately
usable.  The proof of `jet_sup_le`, however, exhibits the constant explicitly: it is
`C₀ * (2π)^m * √C₂` with
* `C₀` from `norm_seriesFun_le` at level `sob n` (`n < 2 * sob n`) and
* `C₂` from `CSq_le_ENormSq_seriesFun` at level `s`,

neither of which depends on `N`, `c` or `m`.  Since `m + sob n ≤ s` forces `m ≤ s`, the factor
`(2π)^m` is dominated by `(2π)^s`, and the single constant `C := C₀ * (2π)^s * √C₂` works for all
`m`, all `N` and all box-supported `c`.
-/

set_option maxHeartbeats 1000000

open MeasureTheory BigOperators

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

/-- **Uniform sup bounds for the jets.**  There is a constant `C ≥ 0`, depending only on `n` and
`s`, such that for every `m` with `m + sob n ≤ s`, every box size `N`, every coefficient family `c`
supported in `box n N`, every multi-index `l : Fin m → Fin n`, every matrix entry `(i,j)` and every
`x`,

`‖∂^l (seriesFunM c · i j) x‖ ≤ C * (1 + √(ENormSqFull s (seriesFunM c)))`. -/
theorem jet_sup_le_uniform_level {n s : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (hm : m + Work.Diff.STE.flat.sob n ≤ s)
      (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      ∀ (l : Fin m → Fin n) (i j : Fin n) (x : Fin n → ℝ),
        ‖Work.Diff.STE.pdVec m l (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) x‖
          ≤ C * (1 + Real.sqrt (Work.Diff.STE.Flat.ENormSqFull s
              (Work.Diff.STE.Flat.seriesFunM c))) := by
  obtain ⟨C0, hC0, h0⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (sob n)
    (by simpa using n_lt_two_sob n)
  obtain ⟨C2, hC2, h2⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) s
  refine ⟨C0 * (2 * Real.pi) ^ s * Real.sqrt C2, by positivity, ?_⟩
  intro m hm N c hc l i j x
  have hmle : m ≤ s := by omega
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext y; rw [seriesFunM_apply]
  have hpd : pdVec m l (fun y => seriesFunM c y i j) x
      = seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x := by
    rw [hfun]
    exact pdList_seriesFun (List.ofFn l) (fun k => c k i j) hmom x
  rw [hpd]
  have hstep := h0 (dmulV (List.ofFn l) (fun k => c k i j))
    (summable_wt_pow_mul_norm_sq _ (fun M => summable_dmulV _ _ hmom M) (sob n)) x
  have hCSq : CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))
      ≤ ((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j) := by
    have h := CSq_dmulV_le (sob n) (List.ofFn l) (fun k => c k i j) hmom
    simpa [List.length_ofFn] using h
  have hlev : sob n + m ≤ s := by omega
  have hmono : CSq (sob n + m) (fun k : Fin n → ℤ => c k i j)
      ≤ CSq s (fun k => c k i j) := by
    rw [CSq, CSq]
    refine Summable.tsum_le_tsum (fun k => ?_)
      (summable_wt_pow_mul_norm_sq _ hmom (sob n + m))
      (summable_wt_pow_mul_norm_sq _ hmom s)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (wt_one_le k) hlev) (sq_nonneg _)
  have h4 : CSq s (fun k : Fin n → ℤ => c k i j) ≤ C2 * ENormSqFull s (seriesFunM c) := by
    have h := h2 (fun k => c k i j) hmom
    have hEs : ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM s (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := s) (seriesFunM c) i j
      rwa [hfun] at hh
    have hE0 : ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
      rwa [hfun] at hh
    refine h.trans ?_
    rw [ENormSqFull]
    exact mul_le_mul_of_nonneg_left (add_le_add hEs hE0) hC2
  have hconst : C0 * (2 * Real.pi) ^ m * Real.sqrt C2
      ≤ C0 * (2 * Real.pi) ^ s * Real.sqrt C2 := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg C2)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hmle) hC0
  have hnonneg : 0 ≤ 1 + Real.sqrt (ENormSqFull s (seriesFunM c)) := by
    linarith [Real.sqrt_nonneg (ENormSqFull s (seriesFunM c))]
  calc ‖seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x‖
      ≤ C0 * Real.sqrt (CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))) := hstep
    _ ≤ C0 * Real.sqrt (((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j)) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCSq) hC0
    _ = C0 * ((2 * Real.pi) ^ m * Real.sqrt (CSq (sob n + m) (fun k => c k i j))) := by
        have hsq : ((2 * Real.pi) ^ 2) ^ m = ((2 * Real.pi) ^ m) ^ 2 := by
          rw [← pow_mul]; ring_nf
        rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ C0 * ((2 * Real.pi) ^ m * Real.sqrt (C2 * ENormSqFull s (seriesFunM c))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
        exact hmono.trans h4
    _ = C0 * ((2 * Real.pi) ^ m
          * (Real.sqrt C2 * Real.sqrt (ENormSqFull s (seriesFunM c)))) := by
        rw [Real.sqrt_mul hC2]
    _ ≤ C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg C2)
    _ = C0 * (2 * Real.pi) ^ m * Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := by ring
    _ ≤ C0 * (2 * Real.pi) ^ s * Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) :=
        mul_le_mul_of_nonneg_right hconst hnonneg

end

end Work.Diff.STE.flat
