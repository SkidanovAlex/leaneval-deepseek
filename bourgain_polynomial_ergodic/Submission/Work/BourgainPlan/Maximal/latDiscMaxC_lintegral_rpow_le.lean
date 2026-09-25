/-
# The centred two-sided discrete Hardy--Littlewood maximal inequality on `ℤ`

This file proves `Work.BourgainPlan.Maximal.latDiscMaxC_lintegral_rpow_le`: the centred
two-sided discrete maximal operator

`latDiscMaxC a x = sup_{N ≥ 1} N⁻¹ Σ_{j ∈ [x-N, x+N]} a j`

maps `ℓᵖ(ℤ)` to `ℓᵖ(ℤ)` for every `1 < p < ∞` (for `ℝ≥0∞`-valued `a`), *given* the same
bound for the one-sided ("forward") maximal operator

`fwd a x = sup_{n ≥ 1} n⁻¹ Σ_{k<n} a (x+k)`.

The reduction is elementary: the centred interval `[x-N, x+N]` splits into `[x-N, x]` and
`[x+1, x+N]`; the first half is a *backward* average of length `N+1` at `x`, the second half is
dominated by a *forward* average of length `N+1` at `x`.  Since `N+1 ≤ 2N` for `N ≥ 1`, both
halves are controlled by `2 · fwd` applied to `a` and to the reflection `y ↦ a (-y)`.  The
reflection is an involution preserving the counting measure, which is where the change of
variables in the integral comes from.
-/
import Mathlib
import Submission.Work.BourgainPlan.Maximal.subtwoLatDefs

open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- The one-sided ("forward") discrete maximal function on `ℤ`, in the exact shape in which it
occurs as the hypothesis `h1` of the main theorem. -/
private def fwd (a : ℤ → ENNReal) (x : ℤ) : ENNReal :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), ((n : ENNReal))⁻¹ * ∑ k ∈ Finset.range n, a (x + (k : ℤ))

/-- The image of `range (n+1)` under `k ↦ x - k` is the interval `[x-n, x]`. -/
private lemma image_range_int_sub (x : ℤ) (n : ℕ) :
    (Finset.range (n+1)).image (fun k : ℕ => x - (k:ℤ)) = Finset.Icc (x - (n:ℤ)) x := by
  ext j
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    constructor <;> omega
  · intro hk
    refine ⟨(x - j).toNat, ?_, ?_⟩
    · rw [Int.toNat_lt (by omega : (0:ℤ) ≤ x - j)]
      omega
    · rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ x - j)]
      ring

/-- The image of `range (n+1)` under `k ↦ x + k` is the interval `[x, x+n]`. -/
private lemma image_range_int_add (x : ℤ) (n : ℕ) :
    (Finset.range (n+1)).image (fun k : ℕ => x + (k:ℤ)) = Finset.Icc x (x + (n:ℤ)) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    constructor <;> omega
  · intro hk
    refine ⟨(j - x).toNat, ?_, ?_⟩
    · rw [Int.toNat_lt (by omega : (0:ℤ) ≤ j - x)]
      omega
    · rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ j - x)]
      ring

private lemma inj_sub (x : ℤ) : Function.Injective (fun k : ℕ => x - (k:ℤ)) := by
  intro p q hpq
  change x - (p:ℤ) = x - (q:ℤ) at hpq
  have : (p:ℤ) = (q:ℤ) := by omega
  exact_mod_cast this

private lemma inj_add (x : ℤ) : Function.Injective (fun k : ℕ => x + (k:ℤ)) := by
  intro p q hpq
  change x + (p:ℤ) = x + (q:ℤ) at hpq
  have : (p:ℤ) = (q:ℤ) := by omega
  exact_mod_cast this

/-- `N⁻¹ (N+1) ≤ 2` for `N ≥ 1`, in `ℝ≥0∞`. -/
private lemma inv_mul_succ_le_two {N : ℕ} (hN : 1 ≤ N) :
    ((N : ENNReal))⁻¹ * (((N + 1 : ℕ) : ENNReal)) ≤ 2 := by
  have hN0 : (N : ENNReal) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNtop : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hcast : (((N + 1 : ℕ)) : ENNReal) = (N : ENNReal) + 1 := by push_cast; ring
  rw [hcast, mul_add, mul_one, ENNReal.inv_mul_cancel hN0 hNtop]
  have hle : (N : ENNReal)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]; exact_mod_cast hN
  calc (1 : ENNReal) + (N:ENNReal)⁻¹ ≤ 1 + 1 := add_le_add_right hle 1
    _ = 2 := one_add_one_eq_two

private lemma add_le_two_mul_max (u v : ENNReal) : u + v ≤ 2 * max u v := by
  calc u + v ≤ max u v + max u v := add_le_add (le_max_left u v) (le_max_right u v)
    _ = 2 * max u v := by rw [two_mul]

/-- The centred two-sided discrete maximal function is dominated by twice the sum of the forward
maximal function of `a` and of its reflection. -/
private lemma latDiscMaxC_le_two_mul_fwd (a : ℤ → ENNReal) (x : ℤ) :
    latDiscMaxC a x ≤ 2 * (fwd a x + fwd (fun y : ℤ => a (-y)) (-x)) := by
  set b : ℤ → ENNReal := fun y => a (-y) with hb
  rw [latDiscMaxC]
  refine iSup_le fun N => iSup_le fun hN => ?_
  have hN1 : 1 ≤ N := hN
  set SL : ENNReal := ∑ k ∈ Finset.range (N+1), b (-x + (k:ℤ)) with hSL
  set SR : ENNReal := ∑ k ∈ Finset.range (N+1), a (x + (k:ℤ)) with hSR
  have h0 : (((N + 1 : ℕ)) : ENNReal) ≠ 0 := by simp
  have htop : (((N + 1 : ℕ)) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top (N+1)
  have hSL_le : ((N+1 : ℕ) : ENNReal)⁻¹ * SL ≤ fwd b (-x) := by
    rw [fwd]
    exact le_iSup_of_le (N+1) (le_iSup_of_le (Nat.succ_pos N) le_rfl)
  have hSR_le : ((N+1 : ℕ) : ENNReal)⁻¹ * SR ≤ fwd a x := by
    rw [fwd]
    exact le_iSup_of_le (N+1) (le_iSup_of_le (Nat.succ_pos N) le_rfl)
  have hSL_bound : SL ≤ ((N+1 : ℕ) : ENNReal) * fwd b (-x) := by
    have heq : SL = ((N+1 : ℕ) : ENNReal) * (((N+1 : ℕ) : ENNReal)⁻¹ * SL) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]
    rw [heq]
    exact mul_le_mul_right hSL_le _
  have hSR_bound : SR ≤ ((N+1 : ℕ) : ENNReal) * fwd a x := by
    have heq : SR = ((N+1 : ℕ) : ENNReal) * (((N+1 : ℕ) : ENNReal)⁻¹ * SR) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]
    rw [heq]
    exact mul_le_mul_right hSR_le _
  have hsplit : Finset.Icc (x - (N:ℤ)) (x + (N:ℤ))
      = Finset.Icc (x - (N:ℤ)) x ∪ Finset.Icc (x+1) (x + (N:ℤ)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc (x - (N:ℤ)) x) (Finset.Icc (x+1) (x + (N:ℤ))) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_Icc] at hj1 hj2
    omega
  have hleft : ∑ j ∈ Finset.Icc (x - (N:ℤ)) x, a j = SL := by
    rw [hSL, ← image_range_int_sub x N, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      show a (x - (k:ℤ)) = a (-(-x + (k:ℤ)))
      congr 1
      ring
    · intro p hp q hq hpq
      exact inj_sub x hpq
  have hmid : ∑ j ∈ Finset.Icc x (x + (N:ℤ)), a j = SR := by
    rw [hSR, ← image_range_int_add x N, Finset.sum_image]
    intro p hp q hq hpq
    exact inj_add x hpq
  have hright : ∑ j ∈ Finset.Icc (x + 1) (x + (N:ℤ)), a j ≤ SR := by
    rw [← hmid]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj1 hj2; exact zero_le
  have hS : ∑ j ∈ Finset.Icc (x - (N:ℤ)) (x + (N:ℤ)), a j ≤ SL + SR := by
    rw [hsplit, Finset.sum_union hdisj, hleft]
    exact add_le_add_right hright SL
  calc ((N : ENNReal))⁻¹ * ∑ j ∈ Finset.Icc (x - (N:ℤ)) (x + (N:ℤ)), a j
      ≤ (N : ENNReal)⁻¹ * (SL + SR) := mul_le_mul_right hS _
    _ = (N : ENNReal)⁻¹ * SL + (N : ENNReal)⁻¹ * SR := mul_add _ _ _
    _ ≤ 2 * fwd b (-x) + 2 * fwd a x := by
        apply add_le_add
        · have h1 : (N : ENNReal)⁻¹ * SL ≤ (N : ENNReal)⁻¹ * (((N+1 : ℕ) : ENNReal) * fwd b (-x)) :=
            mul_le_mul_right hSL_bound _
          rw [← mul_assoc] at h1
          exact h1.trans (mul_le_mul_left (inv_mul_succ_le_two hN1) _)
        · have h1 : (N : ENNReal)⁻¹ * SR ≤ (N : ENNReal)⁻¹ * (((N+1 : ℕ) : ENNReal) * fwd a x) :=
            mul_le_mul_right hSR_bound _
          rw [← mul_assoc] at h1
          exact h1.trans (mul_le_mul_left (inv_mul_succ_le_two hN1) _)
    _ = 2 * (fwd a x + fwd b (-x)) := by ring

/-- The counting measure on `ℤ` is invariant under the reflection `x ↦ -x`. -/
private lemma lintegral_neg_comp_count (g : ℤ → ENNReal) :
    ∫⁻ x : ℤ, g (-x) ∂Measure.count = ∫⁻ x : ℤ, g x ∂Measure.count := by
  rw [lintegral_count, lintegral_count]
  exact Equiv.tsum_eq (Equiv.neg ℤ) g

theorem latDiscMaxC_lintegral_rpow_le {p : ℝ} (hp : 1 < p)
    (h1 : ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ → ENNReal),
      ∫⁻ x : ℤ, (⨆ n : ℕ, ⨆ (_ : 0 < n), ((n : ENNReal))⁻¹ * ∑ k ∈ Finset.range n, a (x + (k : ℤ))) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * ∫⁻ x : ℤ, (a x) ^ p ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ → ENNReal),
      ∫⁻ x : ℤ, (Work.BourgainPlan.Maximal.latDiscMaxC a x) ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * ∫⁻ x : ℤ, (a x) ^ p ∂MeasureTheory.Measure.count := by
  obtain ⟨C0, hC0pos, hC0⟩ := h1
  have hp0 : 0 ≤ p := by linarith
  have hC0' : ∀ a : ℤ → ENNReal,
      ∫⁻ x : ℤ, (fwd a x)^p ∂Measure.count ≤
        ENNReal.ofReal C0 * ∫⁻ x : ℤ, (a x)^p ∂Measure.count := by
    intro a
    simpa only [fwd] using hC0 a
  refine ⟨4^p * C0 * 2,
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) p) hC0pos) (by norm_num), fun a => ?_⟩
  set b : ℤ → ENNReal := fun y => a (-y) with hb
  set I : ENNReal := ∫⁻ x : ℤ, (a x)^p ∂Measure.count with hI
  have hpt : ∀ x : ℤ, (latDiscMaxC a x)^p ≤ (4:ENNReal)^p * ((fwd a x)^p + (fwd b (-x))^p) := by
    intro x
    have h0 : latDiscMaxC a x ≤ 2 * (fwd a x + fwd b (-x)) := latDiscMaxC_le_two_mul_fwd a x
    have hs1 : (latDiscMaxC a x)^p ≤ (2 * (fwd a x + fwd b (-x)))^p :=
      ENNReal.rpow_le_rpow h0 hp0
    have hs2 : (2 * (fwd a x + fwd b (-x)))^p ≤ (4 * max (fwd a x) (fwd b (-x)))^p := by
      apply ENNReal.rpow_le_rpow _ hp0
      calc 2 * (fwd a x + fwd b (-x)) ≤ 2 * (2 * max (fwd a x) (fwd b (-x))) :=
            mul_le_mul_right (add_le_two_mul_max _ _) 2
        _ = 4 * max (fwd a x) (fwd b (-x)) := by ring
    have hs3 : (4 * max (fwd a x) (fwd b (-x)))^p
        = (4:ENNReal)^p * (max (fwd a x) (fwd b (-x)))^p := ENNReal.mul_rpow_of_nonneg _ _ hp0
    have hs4 : (4:ENNReal)^p * (max (fwd a x) (fwd b (-x)))^p
        ≤ (4:ENNReal)^p * ((fwd a x)^p + (fwd b (-x))^p) := by
      apply mul_le_mul_right
      rw [ENNReal.max_rpow hp0]
      exact max_le (le_add_of_nonneg_right (zero_le : (0:ENNReal) ≤ (fwd b (-x))^p))
                   (le_add_of_nonneg_left (zero_le : (0:ENNReal) ≤ (fwd a x)^p))
    exact hs1.trans (hs2.trans (hs3.trans_le hs4))
  have hmono : ∫⁻ x : ℤ, (latDiscMaxC a x)^p ∂Measure.count
      ≤ ∫⁻ x : ℤ, (4:ENNReal)^p * ((fwd a x)^p + (fwd b (-x))^p) ∂Measure.count :=
    lintegral_mono hpt
  have hcm : ∫⁻ x : ℤ, (4:ENNReal)^p * ((fwd a x)^p + (fwd b (-x))^p) ∂Measure.count
      = (4:ENNReal)^p * ∫⁻ x : ℤ, ((fwd a x)^p + (fwd b (-x))^p) ∂Measure.count :=
    lintegral_const_mul _ (measurable_of_countable _)
  have hadd : ∫⁻ x : ℤ, ((fwd a x)^p + (fwd b (-x))^p) ∂Measure.count
      = ∫⁻ x : ℤ, (fwd a x)^p ∂Measure.count + ∫⁻ x : ℤ, (fwd b (-x))^p ∂Measure.count :=
    lintegral_add_left (measurable_of_countable _) _
  have hFa : ∫⁻ x : ℤ, (fwd a x)^p ∂Measure.count ≤ ENNReal.ofReal C0 * I := hC0' a
  have hGb : ∫⁻ x : ℤ, (fwd b (-x))^p ∂Measure.count ≤ ENNReal.ofReal C0 * I := by
    rw [lintegral_neg_comp_count (fun y : ℤ => (fwd b y)^p)]
    calc ∫⁻ y : ℤ, (fwd b y)^p ∂Measure.count
        ≤ ENNReal.ofReal C0 * ∫⁻ y : ℤ, (b y)^p ∂Measure.count := hC0' b
      _ = ENNReal.ofReal C0 * I := by
          have hbb : ∫⁻ y : ℤ, (b y)^p ∂Measure.count =
              ∫⁻ y : ℤ, (a y)^p ∂Measure.count := by
            simp only [hb]
            exact lintegral_neg_comp_count (fun y : ℤ => (a y)^p)
          rw [hbb]
  have hI2 : ∫⁻ x : ℤ, ((fwd a x)^p + (fwd b (-x))^p) ∂Measure.count
      ≤ 2 * (ENNReal.ofReal C0 * I) := by
    rw [hadd]
    calc ∫⁻ x : ℤ, (fwd a x)^p ∂Measure.count + ∫⁻ x : ℤ, (fwd b (-x))^p ∂Measure.count
        ≤ ENNReal.ofReal C0 * I + ENNReal.ofReal C0 * I := add_le_add hFa hGb
      _ = 2 * (ENNReal.ofReal C0 * I) := by rw [two_mul]
  have hconst : (4:ENNReal)^p * (2 * (ENNReal.ofReal C0 * I))
      = ENNReal.ofReal (4^p * C0 * 2) * I := by
    have key : (4:ENNReal)^p * (2 * ENNReal.ofReal C0) = ENNReal.ofReal (4^p * C0 * 2) := by
      have h4 : (4:ENNReal)^p = ENNReal.ofReal (4^p) := by
        have h44 : (4:ENNReal) = ENNReal.ofReal (4:ℝ) := (ENNReal.ofReal_ofNat 4).symm
        rw [h44]
        exact ENNReal.ofReal_rpow_of_pos (x := (4:ℝ)) (p := p) (by norm_num)
      have h2 : (2:ENNReal) = ENNReal.ofReal (2:ℝ) := (ENNReal.ofReal_natCast 2).symm
      calc (4:ENNReal)^p * (2 * ENNReal.ofReal C0)
          = ENNReal.ofReal (4^p) * (ENNReal.ofReal (2:ℝ) * ENNReal.ofReal C0) := by rw [h4, h2]
        _ = ENNReal.ofReal (4^p) * ENNReal.ofReal ((2:ℝ) * C0) := by
              rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        _ = ENNReal.ofReal (4^p * ((2:ℝ) * C0)) := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) p)]
        _ = ENNReal.ofReal (4^p * C0 * 2) := by congr 1; ring
    rw [← key]
    ring
  calc ∫⁻ x : ℤ, (latDiscMaxC a x)^p ∂Measure.count
      ≤ (4:ENNReal)^p * ∫⁻ x : ℤ, ((fwd a x)^p + (fwd b (-x))^p) ∂Measure.count :=
        hmono.trans (le_of_eq hcm)
    _ ≤ (4:ENNReal)^p * (2 * (ENNReal.ofReal C0 * I)) := mul_le_mul_right hI2 _
    _ = ENNReal.ofReal (4^p * C0 * 2) * I := hconst

end

end Work.BourgainPlan.Maximal
