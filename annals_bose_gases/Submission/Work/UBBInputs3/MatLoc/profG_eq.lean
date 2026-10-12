import Mathlib.Computability.Reduce
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.profG_eq` — the first-difference energy of the profile

`Work.UBBInputs3.profG p = Σ_s (prof p (s+1) - prof p s)²` is the first-difference
energy `G` of the normalised triangle profile `prof p = tri p / √(triMass p)`.

This file computes it exactly:

* `triMass p = Σ_s tri(p,s)² = (p+1)(2p²+4p+3)/3` (the profile is the tent
  `p+1, p, …, 1` over `[-p,p]`, so the squares sum to `(p+1)² + 2Σ_{k=1}^p k²`);
* `Σ_s (tri(p,s+1) - tri(p,s))² = 2(p+1)`  (the tent rises with slope `+1` from
  `tri(p,-p-1) = 0` to `tri(p,0) = p+1` and falls with slope `-1` back to
  `tri(p,p+1) = 0`, so each nonzero first difference has absolute value `1`);

whence `profG p = 2(p+1) / triMass p = 6/(2p²+4p+3)`, the statement proved below.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-! ## 1. Reindexing a `ℤ`-interval sum as a sum over `Finset.range` -/

private lemma sum_Icc_eq_sum_range_int {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a b : ℤ) :
    ∑ s ∈ Finset.Icc a b, f s = ∑ j ∈ Finset.range (b + 1 - a).toNat, f (a + (j : ℤ)) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  rfl

/-! ## 2. Pointwise values of the triangle profile -/

/-- On `s ≤ 0` the tent is `p+1+s` (clipped at `0`). -/
private lemma tri_eq_max_of_nonpos {p : ℕ} {s : ℤ} (h2 : s ≤ 0) :
    Work.UBBInputs3.tri p s = max 0 ((s : ℝ) + (p : ℝ) + 1) := by
  have h2' : (s : ℝ) ≤ 0 := by exact_mod_cast h2
  rw [Work.UBBInputs3.tri, abs_of_nonpos h2']
  congr 1
  ring

/-- On `s ≥ 0` the tent is `p+1-s` (clipped at `0`). -/
private lemma tri_eq_max_of_nonneg {p : ℕ} {s : ℤ} (h : 0 ≤ s) :
    Work.UBBInputs3.tri p s = max 0 ((p : ℝ) + 1 - (s : ℝ)) := by
  have h' : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h
  rw [Work.UBBInputs3.tri, abs_of_nonneg h']

private lemma tri_eq_of_nonneg {p : ℕ} {s : ℤ} (h1 : 0 ≤ s) (h2 : s ≤ (p : ℤ)) :
    Work.UBBInputs3.tri p s = (p : ℝ) + 1 - (s : ℝ) := by
  rw [tri_eq_max_of_nonneg (p := p) h1]
  exact max_eq_right (by
    have h2' : (s : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    linarith)

private lemma tri_eq_of_nonpos {p : ℕ} {s : ℤ} (h1 : -(p : ℤ) ≤ s) (h2 : s ≤ 0) :
    Work.UBBInputs3.tri p s = (s : ℝ) + (p : ℝ) + 1 := by
  rw [tri_eq_max_of_nonpos (p := p) h2]
  exact max_eq_right (by
    have h1' : -(p : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1
    linarith)

private lemma tri_eq_zero_of_le {p : ℕ} {s : ℤ} (h : s ≤ -(p : ℤ) - 1) :
    Work.UBBInputs3.tri p s = 0 := by
  have h' : (s : ℝ) ≤ -(p : ℝ) - 1 := by exact_mod_cast h
  have h2 : (s : ℝ) ≤ 0 := by linarith
  rw [Work.UBBInputs3.tri, abs_of_nonpos h2, max_eq_left]
  linarith

private lemma tri_eq_zero_of_ge {p : ℕ} {s : ℤ} (h : (p : ℤ) + 1 ≤ s) :
    Work.UBBInputs3.tri p s = 0 := by
  have h' : (p : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast h
  have hp : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (s : ℝ) := by linarith
  rw [Work.UBBInputs3.tri, abs_of_nonneg h2, max_eq_left]
  linarith

/-! ## 3. The auxiliary power sums -/

private lemma sum_range_one_add_sq (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ 2
      = (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-! ## 4. The squared mass of the triangle profile -/

private lemma triMass_value (p : ℕ) :
    Work.UBBInputs3.triMass p
      = ((p : ℝ) + 1) * (2 * (p : ℝ) ^ 2 + 4 * (p : ℝ) + 3) / 3 := by
  have harg : ((p : ℤ) + 1 - -(p : ℤ)).toNat = 2 * p + 1 := by
    have hcast : ((p : ℤ) + 1 - -(p : ℤ)) = ((2 * p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  have hre : Work.UBBInputs3.triMass p
      = ∑ j ∈ Finset.range (2 * p + 1),
          (Work.UBBInputs3.tri p (-(p : ℤ) + (j : ℤ))) ^ 2 := by
    unfold Work.UBBInputs3.triMass
    rw [sum_Icc_eq_sum_range_int (fun s => (Work.UBBInputs3.tri p s) ^ 2) (-(p : ℤ)) (p : ℤ),
      harg]
  have h1 : ∑ j ∈ Finset.range (p + 1), (Work.UBBInputs3.tri p (-(p : ℤ) + (j : ℤ))) ^ 2
      = ∑ j ∈ Finset.range (p + 1), ((j : ℝ) + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ p := by rw [Finset.mem_range] at hj; omega
    have h0 : -(p : ℤ) ≤ -(p : ℤ) + (j : ℤ) := by omega
    have h2 : -(p : ℤ) + (j : ℤ) ≤ 0 := by omega
    rw [tri_eq_of_nonpos h0 h2]
    push_cast
    ring
  have h2 : ∑ k ∈ Finset.range p, (Work.UBBInputs3.tri p (-(p : ℤ) + (((p + 1 + k : ℕ)) : ℤ))) ^ 2
      = ∑ k ∈ Finset.range p, ((p : ℝ) - (k : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < p := Finset.mem_range.mp hk
    have hidx : -(p : ℤ) + (((p + 1 + k : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [hidx]
    have h0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by omega
    have h2 : (k : ℤ) + 1 ≤ (p : ℤ) := by omega
    rw [tri_eq_of_nonneg h0 h2]
    push_cast
    ring
  have h3 : ∑ k ∈ Finset.range p, ((p : ℝ) - (k : ℝ)) ^ 2
      = ∑ k ∈ Finset.range p, ((k : ℝ) + 1) ^ 2 := by
    rw [← Finset.sum_range_reflect (fun i : ℕ => ((i : ℝ) + 1) ^ 2) p]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < p := Finset.mem_range.mp hk
    have hk1 : 1 ≤ p := by omega
    have hcast : ((p - 1 - k : ℕ) : ℝ) + 1 = (p : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub (by omega : k ≤ p - 1), Nat.cast_sub hk1]
      push_cast
      ring
    rw [hcast]
  rw [hre, show 2 * p + 1 = (p + 1) + p by omega, Finset.sum_range_add, h1, h2, h3,
    sum_range_one_add_sq (p + 1), sum_range_one_add_sq p]
  push_cast
  ring

private lemma triMass_pos_of_value (p : ℕ) : 0 < Work.UBBInputs3.triMass p := by
  rw [triMass_value p]
  positivity

/-! ## 5. The sum of squared first differences of the triangle profile -/

private lemma profG_num_eq (p : ℕ) :
    ∑ s ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1),
        (Work.UBBInputs3.tri p (s + 1) - Work.UBBInputs3.tri p s) ^ 2
      = 2 * ((p : ℝ) + 1) := by
  -- the last index `s = p+1` of the interval contributes nothing
  have hzero : ∀ t : ℤ, t ∉ Finset.Icc (-(p : ℤ) - 1) (p : ℤ) →
      (Work.UBBInputs3.tri p (t + 1) - Work.UBBInputs3.tri p t) ^ 2 = 0 := by
    intro t ht
    simp only [Finset.mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [tri_eq_zero_of_le (p := p) (by omega : t + 1 ≤ -(p : ℤ) - 1),
        tri_eq_zero_of_le (p := p) (by omega : t ≤ -(p : ℤ) - 1)]
      ring
    · rw [tri_eq_zero_of_ge (p := p) (by omega : (p : ℤ) + 1 ≤ t + 1),
        tri_eq_zero_of_ge (p := p) (by omega : (p : ℤ) + 1 ≤ t)]
      ring
  have hsub := Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside
    (fun t : ℤ => (Work.UBBInputs3.tri p (t + 1) - Work.UBBInputs3.tri p t) ^ 2)
    (le_refl (-(p : ℤ) - 1)) (by omega : (p : ℤ) ≤ (p : ℤ) + 1) hzero
  rw [hsub]
  have harg : ((p : ℤ) + 1 - (-(p : ℤ) - 1)).toNat = 2 * p + 2 := by
    have hcast : ((p : ℤ) + 1 - (-(p : ℤ) - 1)) = ((2 * p + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  rw [sum_Icc_eq_sum_range_int
    (fun s => (Work.UBBInputs3.tri p (s + 1) - Work.UBBInputs3.tri p s) ^ 2)
    (-(p : ℤ) - 1) (p : ℤ), harg]
  -- rising edge: `j ↦ -(p+1)+j` for `j ≤ p` gives first difference `+1`
  have h1 : ∑ j ∈ Finset.range (p + 1),
        (Work.UBBInputs3.tri p ((-(p : ℤ) - 1 + (j : ℤ)) + 1)
          - Work.UBBInputs3.tri p (-(p : ℤ) - 1 + (j : ℤ))) ^ 2
      = ∑ j ∈ Finset.range (p + 1), (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ p := by rw [Finset.mem_range] at hj; omega
    have hA : Work.UBBInputs3.tri p (-(p : ℤ) - 1 + (j : ℤ)) = (j : ℝ) := by
      rw [tri_eq_max_of_nonpos (p := p) (by omega : -(p : ℤ) - 1 + (j : ℤ) ≤ 0)]
      have hc : ((-(p : ℤ) - 1 + (j : ℤ) : ℤ) : ℝ) + (p : ℝ) + 1 = (j : ℝ) := by
        push_cast; ring
      rw [hc, max_eq_right (by positivity)]
    have hB : Work.UBBInputs3.tri p ((-(p : ℤ) - 1 + (j : ℤ)) + 1) = (j : ℝ) + 1 := by
      have hidx : (-(p : ℤ) - 1 + (j : ℤ)) + 1 = -(p : ℤ) + (j : ℤ) := by ring
      rw [hidx, tri_eq_max_of_nonpos (p := p) (by omega : -(p : ℤ) + (j : ℤ) ≤ 0)]
      have hc : ((-(p : ℤ) + (j : ℤ) : ℤ) : ℝ) + (p : ℝ) + 1 = (j : ℝ) + 1 := by
        push_cast; ring
      rw [hc, max_eq_right (by positivity)]
    rw [hA, hB]
    norm_num
  -- falling edge: `k ↦ k` for `k ≤ p` gives first difference `-1`
  have h2 : ∑ k ∈ Finset.range (p + 1),
        (Work.UBBInputs3.tri p ((-(p : ℤ) - 1 + (((p + 1) + k : ℕ) : ℤ)) + 1)
          - Work.UBBInputs3.tri p (-(p : ℤ) - 1 + (((p + 1) + k : ℕ) : ℤ))) ^ 2
      = ∑ k ∈ Finset.range (p + 1), (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ p := by rw [Finset.mem_range] at hk; omega
    have hidx : -(p : ℤ) - 1 + (((p + 1) + k : ℕ) : ℤ) = (k : ℤ) := by push_cast; ring
    rw [hidx]
    have hA : Work.UBBInputs3.tri p (k : ℤ) = (p : ℝ) + 1 - (k : ℝ) := by
      rw [tri_eq_max_of_nonneg (p := p) (by omega : (0 : ℤ) ≤ (k : ℤ))]
      push_cast
      exact max_eq_right (by
        have hkR : (k : ℝ) ≤ (p : ℝ) := by exact_mod_cast hk'
        linarith)
    have hB : Work.UBBInputs3.tri p ((k : ℤ) + 1) = (p : ℝ) - (k : ℝ) := by
      rw [tri_eq_max_of_nonneg (p := p) (by omega : (0 : ℤ) ≤ (k : ℤ) + 1)]
      push_cast
      rw [max_eq_right (by
        have hkR : (k : ℝ) ≤ (p : ℝ) := by exact_mod_cast hk'
        linarith)]
      ring
    rw [hA, hB]
    ring
  rw [show 2 * p + 2 = (p + 1) + (p + 1) by omega, Finset.sum_range_add, h1, h2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-! ## 6. The first-difference energy of the normalised profile -/

theorem profG_eq (p : ℕ) :
    Work.UBBInputs3.profG p = 6 / (2 * (p : ℝ) ^ 2 + 4 * (p : ℝ) + 3) := by
  have hnum := profG_num_eq p
  have htm := triMass_value p
  have hpos : 0 < Work.UBBInputs3.triMass p := triMass_pos_of_value p
  have hsqrt : Real.sqrt (Work.UBBInputs3.triMass p) ^ 2 = Work.UBBInputs3.triMass p :=
    Real.sq_sqrt hpos.le
  -- each summand of `profG` is the corresponding summand of `profG_num_eq` divided by `triMass`
  have hterm : ∀ s : ℤ, (Work.UBBInputs3.prof p (s + 1) - Work.UBBInputs3.prof p s) ^ 2
      = (Work.UBBInputs3.tri p (s + 1) - Work.UBBInputs3.tri p s) ^ 2
        / Work.UBBInputs3.triMass p := by
    intro s
    unfold Work.UBBInputs3.prof
    rw [div_sub_div_same, div_pow, hsqrt]
  unfold Work.UBBInputs3.profG
  rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.sum_div, hnum, htm]
  have h1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (p : ℝ) ^ 2 + 4 * (p : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

end Work.UBBInputs3.MatLoc
