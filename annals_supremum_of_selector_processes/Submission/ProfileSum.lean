import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Deep

/-!
PROVE: `Submission.ProfileSum.profile_sum_bound` (the profile-sum bound in Lemma ML,
Park--Pham 2024 §2.2).  This is a PURE analytic/combinatorial statement: prove it only from
`Sel.Deep.Sys.LegalEntry`/`legalLower`/`IsQPower` (import Submission.Deep; q = 100).  Do NOT
import any other Submission file; work in namespace Submission.ProfileSum.

## Meaning
ζ ∈ [0, 10^{-9}].  A "key" k = (b, s) ∈ ℕ × (ℕ → ℕ) encodes a partial legal profile
(s_0, …, s_b) of LEVEL COUNTS: s j is the (natural) count at level j, for j ≤ b, and
`Sys.LegalEntry (s j) j` holds (0 or a power of 100 with bounds), while `s b ≠ 0`
(top level is genuinely b).  We must bound the sum over any finite family K of such keys of
ζ^(s_0 + ⋯ + s_b) (this is ζ^{n_b} in the paper).  The claimed bound is ≤ 1/10 (huge slack:
ζ ≤ 10^{-9} makes everything astronomically small).

## Definitions you should introduce
```
noncomputable def legalVals (j : ℕ) : Finset ℕ :=
  (Finset.range (2 * Sel.Deep.q ^ j)).filter (fun v : ℕ => Sys.LegalEntry v j)
noncomputable def u (ζ : ℝ) (j : ℕ) : ℝ := ∑ v ∈ legalVals j, ζ ^ v - 1
```
(`legalVals j` = all legal values at level j including 0; `Sys.LegalEntry v j` means
`v = 0 ∨ (IsQPower v ∧ (legalLower j : ℝ) ≤ v ∧ v < 2·100^j)`; hence `legalVals j` =
{v : ℕ | Sys.LegalEntry v j} since the filter bound `v < 2 * q^j` is automatic.  Verify
`mem_legalVals : v ∈ legalVals j ↔ Sys.LegalEntry v j`; `zero_mem_legalVals : 0 ∈ legalVals j`;
`sum_legalVals : (∑ v ∈ legalVals j, ζ ^ v) = 1 + u ζ j`.)

## Recommended proof structure (each bullet may be its own lemma)

1. **legality ⇒ value bounds.**  For v ∈ legalVals j, v ≠ 0:
   - v ≥ 1 (trivial).
   - v ≥ 2^{j-4} when j ≥ 5.  [Show: v ≥ legalLower j = 100^{j-4}/(j+1)^2
     (for j ≥ 5 the max(1,·) is the second argument, since 100^{j-4}/(j+1)^2 ≥ 1 —
     prove by induction that 100^{j-4} ≥ (j+1)^2 for j ≥ 5, or 50^{j-4} ≥ (j+1)^2,
     base j=5: 100 ≥ 36; step multiplies by 50 while (j+2)^2/(j+1)^2 ≤ 4).]
   - Also prove 100^{j-4}/(j+1)^2 ≥ 2^{j-4} for j ≥ 5 (equivalently 50^{j-4} ≥ (j+1)^2).
   - v < 2 * q^j (from LegalEntry).
2. **counting legal values.**  # {v ∈ legalVals j | v ≠ 0} ≤ j + 1.
   [Every nonzero legal value is a power of 100: v = q^k, and v < 2·q^j ≤ q^{j+1} gives
   k ≤ j (use `pow_lt_pow_iff_right₀` with q > 1, or a direct argument); distinct k give
   distinct v (powers of 100 strictly increase).  Hence a Finset of at most j+1 values.]
   Consequently `u ζ j ≤ (j+1)·ζ^m` where m = 1 for j ≤ 4 and m = 2^{j-4} for j ≥ 5
   (each term ζ^v ≤ ζ^m because v ≥ m and 0 ≤ ζ ≤ 1 — use `pow_le_pow_of_le_one`).
3. **partial-sum bound.**  `∀ τ, ∑ j ∈ Finset.range (τ+1), u ζ j ≤ 15·ζ + 12·ζ²`
   [Split: j ≤ 4 gives Σ_{j≤4}(j+1)ζ^1 = 15ζ.  For j ≥ 5: u ζ j ≤ (j+1)·ζ^{2^{j-4}}.
   Prove by induction on m that (5+m+1)·ζ^{2^{m+1}} ≤ 6ζ²·(1/2)^m (ratio between successive
   terms ≤ 1/2 because (j+2)/(j+1) ≤ 2 and ζ^{2^{j-4}} ≤ ζ² ≤ 1/4 for j ≥ 5, ζ ≤ 1/2), then
   ∑ over j ∈ [5, τ] ≤ 6ζ²·∑_{m}(1/2)^m ≤ 12ζ² (`geom_sum` style: finite geometric sum
   (1/2)-tail ≤ 2).]
4. **product bound.**  For nonnegative reals (u_j): if (∑_{j ≤ τ} u_j) ≤ 1/2 then
   `∏ j ∈ range(τ+1), (1 + u j) ≤ 1 + 2·(∑ j ∈ range(τ+1), u j)` — induction over τ; each step
   uses (1+a)(1+2S) ≤ 1+2(S+a) when 2S ≤ 1 and a ≥ 0.  (You may also use 1+a ≤ exp a + known
   exp bounds, but the elementary induction is easiest.)
5. **the key-sum ≤ profile-product.**  Let `K : Finset (ℕ × (ℕ → ℕ))` with the hypotheses of
   the theorem.  Show
   `∑ k ∈ K, ζ^(∑ j ∈ range (k.1 + 1), k.2 j) ≤ ∏ j ∈ range (τ+1), (1 + u ζ j) - 1`.
   [Map each key (b,s) to the zero-padded profile function p : ℕ → ℕ, p j = if j ≤ b then
   s j else 0.  This map is injective on K (s b ≠ 0 makes b the top level of p) and
   Σ_{j ≤ b} s j = Σ_{j ∈ range(τ+1)} p j.  Then prove the "profiles" bound: for any Finset
   P of functions p : ℕ → ℕ with p j ∈ legalVals j for j ≤ τ and p j = 0 for j > τ:
   `∑ p ∈ P, ζ^(∑ j ∈ range(τ+1), p j) ≤ ∏ j ∈ range(τ+1), (1 + u ζ j)`
   by induction on τ: split P by the value v := p τ (finite fibers, images ⊆ legalVals τ),
   factor ζ^v, apply the induction hypothesis to the projected fibers (restrict p to levels
   < τ, zero above; injective because P-profiles are zero above τ), and sum the geometric
   factor: ∑_{v ∈ image} ζ^v ≤ ∑_{v ∈ legalVals τ} ζ^v = 1 + u ζ τ.]
   Conclude Σ over K ∪ {0-profile} ≤ Π (the 0-profile contributes 1), so Σ over K ≤ Π − 1.
6. **final.**  Combine 3,4,5: Σ over K ≤ Π − 1 ≤ 2·Σu ≤ 2·(15ζ + 12ζ²) ≤ 1/10
   [for ζ ≤ 10^{-9}: 30ζ ≤ 30·10^{-9} < 1/10, 24ζ² tiny; verify by hand with coarse
   inequalities and `nlinarith`/`norm_num` at the end — avoid norm_num on 10^9-sized
   naturals, work symbolically with (10^9)⁻¹ etc.]

Note: `Sel.Deep.q = 100`; `Sel.Deep.q_pos : 0 < (q:ℝ)`; `Sys.legalLower j = max 1
(q^j/(q^4·(j+1)^2))`; `Sys.IsQPower m = ∃ k, m = q^k`.  Real exponentiation in this file is
only with NATURAL exponents (ζ ^ n).  All sums are finite Finset sums.  Work in namespace
`Submission.ProfileSum`; the theorem below must keep its exact name and statement.
-/

set_option autoImplicit false
open Classical
open Finset
open scoped BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace ProfileSum

open Sel
open Sel.Deep
open Sel.Deep.Sys


/-! # Profile sum bound: development

We build the proof of `profile_sum_bound` from scratch.  We keep the original
statement at the end of the file. -/

open Sel
open Sel.Deep
open Sel.Deep.Sys

/-- legal values at level `j` (including 0) -/
noncomputable def legalVals (j : ℕ) : Finset ℕ :=
  (Finset.range (2 * q ^ j)).filter (fun v : ℕ => Sys.LegalEntry v j)

/-- total weight of all legal values at level `j` -/
noncomputable def profSum (ζ : ℝ) (j : ℕ) : ℝ := ∑ v ∈ legalVals j, ζ ^ v

/-- surplus of legal values at level `j` over the empty profile -/
noncomputable def u (ζ : ℝ) (j : ℕ) : ℝ := profSum ζ j - 1

lemma profSum_eq_one_add_u (ζ : ℝ) (j : ℕ) : profSum ζ j = 1 + u ζ j := by
  unfold u profSum
  ring

lemma u_eq_profSum_sub_one (ζ : ℝ) (j : ℕ) : u ζ j = profSum ζ j - 1 := rfl

lemma q_pow_pos (j : ℕ) : 0 < q ^ j := by positivity

lemma two_mul_q_pow_pos (j : ℕ) : 0 < 2 * q ^ j := by positivity

lemma q_pow_ge_one (j : ℕ) : 1 ≤ q ^ j := by
  have := q_pow_pos j
  omega

lemma legalEntry_lt_two_mul_q_pow (j v : ℕ) (hL : Sys.LegalEntry v j) :
    v < 2 * q ^ j := by
  rcases hL with hz | hpow
  · rw [hz]
    exact two_mul_q_pow_pos j
  · exact_mod_cast hpow.2.2

/-- `legalVals j` collects exactly the legal entries at level `j`. -/
lemma mem_legalVals (j v : ℕ) : v ∈ legalVals j ↔ Sys.LegalEntry v j := by
  unfold legalVals
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro hL
    exact ⟨legalEntry_lt_two_mul_q_pow j v hL, hL⟩

lemma zero_mem_legalVals (j : ℕ) : 0 ∈ legalVals j := by
  rw [mem_legalVals]
  exact Or.inl rfl

/-- a nonzero legal entry is a power of q, at least the legal lower bound, and below `2*q^j` -/
lemma legalEntry_nonzero {j v : ℕ} (hL : Sys.LegalEntry v j) (hv : v ≠ 0) :
    ∃ k : ℕ, v = q ^ k ∧ (legalLower j : ℝ) ≤ (v : ℝ) ∧ v < 2 * q ^ j := by
  rcases hL with hz | hpow
  · contradiction
  · rcases hpow with ⟨⟨k, hk⟩, hl, hu⟩
    refine ⟨k, hk, hl, ?_⟩
    exact_mod_cast hu

/-! ## Part B: growth of `50^m` and lower bound on legal values -/

/-- `(m+5)^2 ≤ 50^m` for `1 ≤ m` -/
lemma fifty_sq_le (m : ℕ) (hm : 1 ≤ m) : (m + 5) ^ 2 ≤ 50 ^ m := by
  refine Nat.le_induction ?base ?step m hm
  · norm_num
  · intro n hn ih
    calc
      ((n + 1) + 5) ^ 2 = (n + 6) ^ 2 := by congr 1 <;> omega
      _ ≤ 50 * (n + 5) ^ 2 := by nlinarith
      _ ≤ 50 * 50 ^ n := by exact Nat.mul_le_mul_left 50 ih
      _ = 50 ^ (n + 1) := by rw [pow_succ]; ring

/-- real version of `fifty_sq_le` -/
lemma fifty_sq_le_real (m : ℕ) (hm : 1 ≤ m) : ((m + 5 : ℕ) : ℝ) ^ 2 ≤ (50 : ℝ) ^ m := by
  exact_mod_cast fifty_sq_le m hm

lemma two_pow_ge_self (m : ℕ) : m ≤ 2 ^ m := by
  have P : ∀ m : ℕ, m + 1 ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        calc
          (m + 1) + 1 ≤ 2 * (m + 1) := by omega
          _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (m + 1) := by rw [pow_succ]; ring
  exact le_trans (Nat.le_succ m) (P m)

/-- `legalLower` at level `m + 4` is at least `2^m` (real). -/
lemma legalLower_m_ge (m : ℕ) (hm : 1 ≤ m) : (2 : ℝ) ^ m ≤ legalLower (m + 4) := by
  unfold legalLower
  let den : ℝ := (((m + 4 : ℕ) : ℝ) + 1) ^ 2
  have hden_eq : den = ((m + 5 : ℕ) : ℝ) ^ 2 := by
    dsimp [den]
    congr 1
    norm_num
    ring
  have hfifty := fifty_sq_le_real m hm
  have hmain : (2 : ℝ) ^ m * den ≤ (q : ℝ) ^ m := by
    calc
      (2 : ℝ) ^ m * den ≤ (2 : ℝ) ^ m * (50 : ℝ) ^ m := by
        rw [hden_eq]
        exact mul_le_mul_of_nonneg_left hfifty (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) m)
      _ = (q : ℝ) ^ m := by
        rw [← mul_pow]
        norm_num
  have hc : 0 < (q : ℝ) ^ 4 * den := by positivity
  have hfrac : (2 : ℝ) ^ m ≤ (q : ℝ) ^ (m + 4) / ((q : ℝ) ^ 4 * den) := by
    rw [le_div_iff₀ hc]
    rw [pow_add]
    have hq4 : 0 ≤ (q : ℝ) ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hmain hq4
    nlinarith
  change (2 : ℝ) ^ m ≤ max 1 ((q : ℝ) ^ (m + 4) / ((q : ℝ) ^ 4 * den))
  exact le_trans hfrac (le_max_right (1 : ℝ) ((q : ℝ) ^ (m + 4) / ((q : ℝ) ^ 4 * den)))

/-- at level `j ≥ 5`, the lower bound is at least `2^(j-4)` (real). -/
lemma legalLower_ge_two_pow (j : ℕ) (hj : 5 ≤ j) : (2 : ℝ) ^ (j - 4) ≤ legalLower j := by
  have hm1 : 1 ≤ j - 4 := by omega
  have h := legalLower_m_ge (j - 4) hm1
  have hsub : (j - 4) + 4 = j := Nat.sub_add_cancel (by omega)
  simpa [hsub] using h

/-- a nonzero legal value at level `j ≥ 5` is at least `2^(j-4)` -/
lemma legal_v_ge_two_pow (j : ℕ) (hj : 5 ≤ j) {v : ℕ} (hL : Sys.LegalEntry v j) (hv : v ≠ 0) :
    2 ^ (j - 4) ≤ v := by
  rcases legalEntry_nonzero hL hv with ⟨k, hk, hl, hu⟩
  have hreal : (2 : ℝ) ^ (j - 4) ≤ (v : ℝ) := le_trans (legalLower_ge_two_pow j hj) hl
  exact_mod_cast hreal

/-- a nonzero legal value at level `j ≥ 5` is at least `j - 4` -/
lemma legal_v_ge_level (j : ℕ) (hj : 5 ≤ j) {v : ℕ} (hL : Sys.LegalEntry v j) (hv : v ≠ 0) :
    j - 4 ≤ v := by
  exact le_trans (two_pow_ge_self (j - 4)) (legal_v_ge_two_pow j hj hL hv)

/-! ## Part C: counting legal values and bounding `u` -/

/-- every nonzero legal value at level `j` is a power `q^k` with `k ≤ j` -/
lemma legal_nonzero_mem_pow_image (j : ℕ) {v : ℕ} (hvne : v ≠ 0) (hv : v ∈ legalVals j) :
    v ∈ (Finset.range (j + 1)).image (fun k : ℕ => q ^ k) := by
  have hL : Sys.LegalEntry v j := (mem_legalVals j v).1 hv
  have hvlt : v < 2 * q ^ j := legalEntry_lt_two_mul_q_pow j v hL
  rcases hL with hz | hpow
  · exact False.elim (hvne hz)
  · rcases hpow with ⟨⟨k, hk⟩, hl, hu⟩
    have hqk : q ^ k < q ^ (j + 1) := by
      calc
        q ^ k = v := hk.symm
        _ < 2 * q ^ j := hvlt
        _ ≤ q ^ (j + 1) := by
          have hq2 : 2 ≤ q := by norm_num
          calc
            2 * q ^ j ≤ q * q ^ j := Nat.mul_le_mul_right (q ^ j) hq2
            _ = q ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]
    have hklt : k < j + 1 := (pow_lt_pow_iff_right₀ (by norm_num : 1 < q)).1 hqk
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hklt, hk.symm⟩

/-- nonzero legal values form a subset of `{q^k : k ≤ j}` -/
lemma nonzero_legalVals_subset_powers (j : ℕ) :
    (legalVals j).filter (fun v => v ≠ 0) ⊆ (Finset.range (j + 1)).image (fun k : ℕ => q ^ k) := by
  intro v hv
  exact legal_nonzero_mem_pow_image j (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hv).1

/-- there are at most `j + 1` nonzero legal values at level `j` -/
lemma card_nonzero_legalVals_le (j : ℕ) :
    ((legalVals j).filter (fun v => v ≠ 0)).card ≤ j + 1 := by
  calc
    ((legalVals j).filter (fun v => v ≠ 0)).card
        ≤ ((Finset.range (j + 1)).image (fun k : ℕ => q ^ k)).card :=
          Finset.card_le_card (nonzero_legalVals_subset_powers j)
    _ ≤ (Finset.range (j + 1)).card := Finset.card_image_le
    _ = j + 1 := by simp

/-- splitting a sum over `s` according to a predicate -/
lemma sum_filter_partition (s : Finset ℕ) (f : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ x ∈ s.filter p, f x) + (∑ x ∈ s.filter (fun x => ¬ p x), f x) = ∑ x ∈ s, f x := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ x ∈ s, if p x then f x else 0) + (∑ x ∈ s, if ¬ p x then f x else 0)
        = ∑ x ∈ s, ((if p x then f x else 0) + (if ¬ p x then f x else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ x ∈ s, f x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          by_cases hp : p x <;> simp [hp]

/-- `u ζ j` equals the sum of `ζ^v` over the nonzero legal values at level `j` -/
lemma u_eq_nonzero_sum (ζ : ℝ) (j : ℕ) : u ζ j = ∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v := by
  classical
  unfold u profSum
  have hf0 : (legalVals j).filter (fun v : ℕ => v = 0) = ({0} : Finset ℕ) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact h.2
    · intro h
      subst v
      exact ⟨zero_mem_legalVals j, rfl⟩
  have hpart : (∑ v ∈ legalVals j, ζ ^ v) =
      (∑ v ∈ (legalVals j).filter (fun v : ℕ => v = 0), ζ ^ v) +
        (∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v) := by
    rw [sum_filter_partition]
  calc
    u ζ j = (∑ v ∈ legalVals j, ζ ^ v) - 1 := rfl
    _ = ((∑ v ∈ (legalVals j).filter (fun v : ℕ => v = 0), ζ ^ v) +
        (∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v)) - 1 := by rw [hpart]
    _ = ∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v := by
        rw [hf0]
        simp

lemma u_nonneg (ζ : ℝ) (hζ0 : 0 ≤ ζ) (j : ℕ) : 0 ≤ u ζ j := by
  rw [u_eq_nonzero_sum]
  exact Finset.sum_nonneg (fun v _ => pow_nonneg hζ0 v)

/-- for levels `j ≤ 4`, `u ζ j ≤ (j+1)ζ` -/
lemma u_le_level_small (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) {j : ℕ} (hj : j ≤ 4) :
    u ζ j ≤ ((j + 1 : ℕ) : ℝ) * ζ := by
  rw [u_eq_nonzero_sum]
  have hterm : ∀ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v ≤ ζ := by
    intro v hv
    have hvne : v ≠ 0 := (Finset.mem_filter.mp hv).2
    have hv1 : 1 ≤ v := by omega
    simpa [pow_one] using pow_le_pow_of_le_one hζ0 hζ1 hv1
  calc
    (∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v)
        ≤ (∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ) := Finset.sum_le_sum hterm
    _ = ((legalVals j).filter (fun v => v ≠ 0)).card * ζ := by simp
    _ ≤ ((j + 1 : ℕ) : ℝ) * ζ := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_nonzero_legalVals_le j) hζ0

/-- for levels `j ≥ 5`, `u ζ j ≤ (j+1)ζ^(j-4)` -/
lemma u_le_level_big (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) {j : ℕ} (hj : 5 ≤ j) :
    u ζ j ≤ ((j + 1 : ℕ) : ℝ) * ζ ^ (j - 4) := by
  rw [u_eq_nonzero_sum]
  have hterm : ∀ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v ≤ ζ ^ (j - 4) := by
    intro v hv
    have hvmem : v ∈ legalVals j := (Finset.mem_filter.mp hv).1
    have hvne : v ≠ 0 := (Finset.mem_filter.mp hv).2
    have hL : Sys.LegalEntry v j := (mem_legalVals j v).1 hvmem
    have hvge : j - 4 ≤ v := legal_v_ge_level j hj hL hvne
    exact pow_le_pow_of_le_one hζ0 hζ1 hvge
  calc
    (∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ v)
        ≤ (∑ v ∈ (legalVals j).filter (fun v => v ≠ 0), ζ ^ (j - 4)) := Finset.sum_le_sum hterm
    _ = ((legalVals j).filter (fun v => v ≠ 0)).card * ζ ^ (j - 4) := by simp
    _ ≤ ((j + 1 : ℕ) : ℝ) * ζ ^ (j - 4) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_nonzero_legalVals_le j)
          (pow_nonneg hζ0 (j - 4))

/-! ## Part D: partial sums of `u` over levels -/

/-- exact partial geometric sum: `∑_{m<n+1} (1/2)^m = 2 - (1/2)^n` -/
lemma sum_half_range (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), ((1 / 2 : ℝ) ^ m)) = 2 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : (1 / 2 : ℝ) ^ n = 2 * (1 / 2 : ℝ) ^ (n + 1) := by
        rw [pow_succ]
        norm_num
        ring
      nlinarith

/-- `∑_{m<n} (1/2)^m ≤ 2` -/
lemma sum_half_le_two (n : ℕ) : (∑ m ∈ Finset.range n, ((1 / 2 : ℝ) ^ m)) ≤ 2 := by
  calc
    (∑ m ∈ Finset.range n, ((1 / 2 : ℝ) ^ m))
        ≤ ∑ m ∈ Finset.range (n + 1), ((1 / 2 : ℝ) ^ m) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
            (fun m _ _ => pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) m)
    _ = 2 - (1 / 2 : ℝ) ^ n := sum_half_range n
    _ ≤ 2 := by nlinarith [pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) n]

/-- decay of the tail terms: `(m+6)ζ^(m+1) ≤ 6ζ(1/2)^m` when `ζ ≤ 1/4` -/
lemma tail_decay (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ4 : ζ ≤ (1 / 4 : ℝ)) :
    ∀ m : ℕ, ((m + 6 : ℕ) : ℝ) * ζ ^ (m + 1) ≤ 6 * ζ * (1 / 2 : ℝ) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hb : 2 * ((m : ℝ) + 7) * ζ ≤ (m : ℝ) + 6 := by
        have h1 : 2 * ((m : ℝ) + 7) * ζ ≤ 2 * ((m : ℝ) + 7) * (1 / 4 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hζ4 (by positivity)
        have hlin : (m : ℝ) + 7 ≤ 2 * ((m : ℝ) + 6) := by nlinarith
        have h2 : 2 * ((m : ℝ) + 7) * (1 / 4 : ℝ) ≤ (m : ℝ) + 6 := by nlinarith [hlin]
        exact le_trans h1 h2
      have hzpow : 0 ≤ ζ ^ (m + 1) := pow_nonneg hζ0 (m + 1)
      have hb' : 2 * (((m : ℝ) + 7) * ζ ^ (m + 1) * ζ) ≤ ((m : ℝ) + 6) * ζ ^ (m + 1) := by
        have hmm := mul_le_mul_of_nonneg_right hb hzpow
        nlinarith
      calc
        (((m + 1 + 6 : ℕ) : ℝ) * ζ ^ ((m + 1) + 1)) ≤ (1 / 2) * (((m : ℝ) + 6) * ζ ^ (m + 1)) := by
          have hcast : ((m + 1 + 6 : ℕ) : ℝ) = (m : ℝ) + 7 := by
            rw [Nat.cast_add]
            norm_num [Nat.cast_add]
            ring
          rw [hcast]
          rw [pow_succ]
          nlinarith [hb']
        _ ≤ (1 / 2) * (6 * ζ * (1 / 2 : ℝ) ^ m) := by
          have ihn : ((m : ℝ) + 6) * ζ ^ (m + 1) ≤ 6 * ζ * (1 / 2 : ℝ) ^ m := by
            have hc : ((m + 6 : ℕ) : ℝ) = (m : ℝ) + 6 := by
              rw [Nat.cast_add]
              ring
            rwa [hc] at ih
          exact mul_le_mul_of_nonneg_left ihn (by norm_num : 0 ≤ (1 / 2 : ℝ))
        _ = 6 * ζ * (1 / 2 : ℝ) ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- the sum of the tail terms (in `m`) is at most `12ζ` -/
lemma tail_sum_le (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ4 : ζ ≤ (1 / 4 : ℝ)) (N : ℕ) :
    (∑ m ∈ Finset.range N, (((m + 6 : ℕ) : ℝ) * ζ ^ (m + 1))) ≤ 12 * ζ := by
  calc
    (∑ m ∈ Finset.range N, (((m + 6 : ℕ) : ℝ) * ζ ^ (m + 1)))
        ≤ ∑ m ∈ Finset.range N, (6 * ζ * (1 / 2 : ℝ) ^ m) := by
          exact Finset.sum_le_sum (fun m hm => tail_decay ζ hζ0 hζ4 m)
    _ = 6 * ζ * (∑ m ∈ Finset.range N, ((1 / 2 : ℝ) ^ m)) := by
          rw [← Finset.mul_sum]
    _ ≤ 6 * ζ * 2 := by
          exact mul_le_mul_of_nonneg_left (sum_half_le_two N) (by positivity)
    _ = 12 * ζ := by ring

/-- reindex a filtered range-sum by subtracting `c` -/
lemma sum_range_filter_shift {N c : ℕ} (f : ℕ → ℝ) :
    (∑ j ∈ (Finset.range N).filter (fun j : ℕ => c ≤ j), f j)
      = ∑ m ∈ Finset.range (N - c), f (m + c) := by
  classical
  refine Finset.sum_bij (fun a ha => a - c) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range]
    have h1 := (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    have h2 := (Finset.mem_filter.mp ha).2
    have hlt : a + 1 ≤ N := Nat.succ_le_of_lt h1
    have hsub : (a + 1) - c ≤ N - c := Nat.sub_le_sub_right hlt c
    have hrew : (a + 1) - c = (a - c) + 1 := by omega
    rwa [hrew] at hsub
  · intro a₁ ha₁ a₂ ha₂ h
    have hc1 : c ≤ a₁ := (Finset.mem_filter.mp ha₁).2
    have hc2 : c ≤ a₂ := (Finset.mem_filter.mp ha₂).2
    calc
      a₁ = (a₁ - c) + c := (Nat.sub_add_cancel hc1).symm
      _ = (a₂ - c) + c := by rw [h]
      _ = a₂ := Nat.sub_add_cancel hc2
  · intro b hb
    have hb' : b < N - c := (Finset.mem_range.mp hb)
    refine ⟨b + c, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · by_cases hc : c ≤ N
        · have hsum : (N - c) + c = N := Nat.sub_add_cancel hc
          have hbc : b + c < (N - c) + c := Nat.add_lt_add_right hb' c
          simpa [hsum] using hbc
        · have hNc : N - c = 0 := by omega
          omega
      · omega
    · omega
  · intro a ha
    have h2 : c ≤ a := (Finset.mem_filter.mp ha).2
    congr 1
    exact (Nat.sub_add_cancel h2).symm

/-- `∑_{j ≤ τ} u ζ j ≤ 37ζ` for `ζ ≤ 10⁻⁹` -/
lemma partial_sum_u_le (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ9 : ζ ≤ ((10 : ℝ) ^ 9)⁻¹) (τ : ℕ) :
    (∑ j ∈ Finset.range (τ + 1), u ζ j) ≤ 37 * ζ := by
  have hζ1 : ζ ≤ 1 := by
    have h01 : ((10 : ℝ) ^ 9)⁻¹ ≤ 1 := by norm_num
    exact le_trans hζ9 h01
  have hζ4 : ζ ≤ (1 / 4 : ℝ) := by
    have h04 : ((10 : ℝ) ^ 9)⁻¹ ≤ (1 / 4 : ℝ) := by norm_num
    exact le_trans hζ9 h04
  classical
  have hA : (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => j ≤ 4), u ζ j) ≤ 25 * ζ := by
    have hA1 : (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => j ≤ 4), u ζ j)
        ≤ ∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => j ≤ 4), (((j + 1 : ℕ) : ℝ) * ζ) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact u_le_level_small ζ hζ0 hζ1 ((Finset.mem_filter.mp hj).2)
    have hsub : (Finset.range (τ + 1)).filter (fun j : ℕ => j ≤ 4) ⊆ Finset.range 5 := by
      intro j hj
      rw [Finset.mem_range]
      have hj' := (Finset.mem_filter.mp hj).2
      omega
    have hA2 : (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => j ≤ 4), (((j + 1 : ℕ) : ℝ) * ζ))
        ≤ ∑ j ∈ Finset.range 5, (((j + 1 : ℕ) : ℝ) * ζ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro j hj hjn
      positivity
    have hA3 : (∑ j ∈ Finset.range 5, (((j + 1 : ℕ) : ℝ) * ζ)) ≤ 25 * ζ := by
      have hterm : ∀ j ∈ Finset.range 5, (((j + 1 : ℕ) : ℝ) * ζ) ≤ 5 * ζ := by
        intro j hj
        have hj' : j < 5 := (Finset.mem_range.mp hj)
        have hj'' : (j + 1 : ℕ) ≤ 5 := by omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj'') hζ0
      calc
        (∑ j ∈ Finset.range 5, (((j + 1 : ℕ) : ℝ) * ζ)) ≤ ∑ j ∈ Finset.range 5, (5 * ζ) :=
          Finset.sum_le_sum hterm
        _ = 25 * ζ := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ]
          simp
          ring
    exact le_trans (le_trans hA1 hA2) hA3
  have hB : (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), u ζ j) ≤ 12 * ζ := by
    have hB1 : (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), u ζ j)
        ≤ ∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), (((j + 1 : ℕ) : ℝ) * ζ ^ (j - 4)) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact u_le_level_big ζ hζ0 hζ1 ((Finset.mem_filter.mp hj).2)
    have hBeq : (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), (((j + 1 : ℕ) : ℝ) * ζ ^ (j - 4)))
        = ∑ m ∈ Finset.range (τ + 1 - 5), ((((m + 6 : ℕ) : ℝ) * ζ ^ (m + 1))) := by
      calc
        (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), (((j + 1 : ℕ) : ℝ) * ζ ^ (j - 4)))
            = ∑ m ∈ Finset.range (τ + 1 - 5), ((((m + 5 + 1 : ℕ) : ℝ) * ζ ^ (m + 5 - 4))) := by
              rw [sum_range_filter_shift]
        _ = ∑ m ∈ Finset.range (τ + 1 - 5), ((((m + 6 : ℕ) : ℝ) * ζ ^ (m + 1))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hnat' : m + 5 + 1 = m + 6 := by omega
              have he : m + 5 - 4 = m + 1 := by omega
              rw [hnat', he]
    calc
      (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), u ζ j)
          ≤ ∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), (((j + 1 : ℕ) : ℝ) * ζ ^ (j - 4)) := hB1
      _ = ∑ m ∈ Finset.range (τ + 1 - 5), ((((m + 6 : ℕ) : ℝ) * ζ ^ (m + 1))) := hBeq
      _ ≤ 12 * ζ := tail_sum_le ζ hζ0 hζ4 (τ + 1 - 5)
  have hpart : (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => j ≤ 4), u ζ j) +
      (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), u ζ j)
      = ∑ j ∈ Finset.range (τ + 1), u ζ j := by
    have hnot : (Finset.range (τ + 1)).filter (fun j : ℕ => ¬ j ≤ 4) =
        (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j) := by
      ext j
      simp only [Finset.mem_filter]
      constructor <;> intro h <;> exact ⟨h.1, by omega⟩
    have h := sum_filter_partition (Finset.range (τ + 1)) (fun j => u ζ j) (fun j : ℕ => j ≤ 4)
    rw [hnot] at h
    exact h
  calc
    (∑ j ∈ Finset.range (τ + 1), u ζ j) = (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => j ≤ 4), u ζ j) +
        (∑ j ∈ (Finset.range (τ + 1)).filter (fun j : ℕ => 5 ≤ j), u ζ j) := hpart.symm
    _ ≤ 25 * ζ + 12 * ζ := add_le_add hA hB
    _ = 37 * ζ := by ring

/-! ## Part E: product bound -/

/-- `∏_{j≤τ} (1+u_j) ≤ 1 + 2·Σ_{j≤τ} u_j` when `0 ≤ Σu ≤ 1/2` -/
lemma prod_one_add_u_le (ζ : ℝ) (hζ0 : 0 ≤ ζ) (τ : ℕ)
    (hS : (∑ j ∈ Finset.range (τ + 1), u ζ j) ≤ (1 / 2 : ℝ)) :
    (∏ j ∈ Finset.range (τ + 1), (1 + u ζ j)) ≤ 1 + 2 * (∑ j ∈ Finset.range (τ + 1), u ζ j) := by
  induction τ with
  | zero =>
      have hu : 0 ≤ u ζ 0 := u_nonneg ζ hζ0 0
      simp
      nlinarith
  | succ τ ih =>
      let S : ℝ := ∑ j ∈ Finset.range (τ + 1), u ζ j
      let a : ℝ := u ζ (τ + 1)
      have huτ : 0 ≤ u ζ (τ + 1) := u_nonneg ζ hζ0 (τ + 1)
      have hS' : S ≤ (1 / 2 : ℝ) := by
        dsimp [S]
        calc
          (∑ j ∈ Finset.range (τ + 1), u ζ j) ≤ ∑ j ∈ Finset.range ((τ + 1) + 1), u ζ j := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
            intro j hj hjn
            exact u_nonneg ζ hζ0 j
          _ ≤ (1 / 2 : ℝ) := hS
      have ih' := ih hS'
      have h2S : 2 * S ≤ 1 := by nlinarith [hS']
      have hrel : (1 + 2 * S) * (1 + a) ≤ 1 + 2 * (S + a) := by
        have hnonpos : 2 * S - 1 ≤ 0 := by nlinarith [h2S]
        have hprod : (2 * S - 1) * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hnonpos huτ
        nlinarith [hprod]
      calc
        (∏ j ∈ Finset.range (τ + 2), (1 + u ζ j))
            = (∏ j ∈ Finset.range (τ + 1), (1 + u ζ j)) * (1 + u ζ (τ + 1)) := by
              rw [Finset.prod_range_succ]
        _ ≤ (1 + 2 * S) * (1 + a) := by
              dsimp [a]
              exact mul_le_mul_of_nonneg_right ih' (by positivity)
        _ ≤ 1 + 2 * (S + a) := hrel
        _ = 1 + 2 * (∑ j ∈ Finset.range (τ + 2), u ζ j) := by
              dsimp [S, a]
              congr 2
              conv_rhs =>
                rw [Finset.sum_range_succ, Finset.sum_range_succ]
              rw [Finset.sum_range_succ]

/-! ## Part F: profiles and the profile-sum bound -/

/-- the zero profile -/
noncomputable def zeroProf : ℕ → ℕ := fun _ => 0

/-- weight of a profile over the first `n` levels -/
noncomputable def wsum (p : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, p j

/-- zero-padding of a partial profile `s` with top level `b` -/
noncomputable def pad (b : ℕ) (s : ℕ → ℕ) : ℕ → ℕ := fun j => if j ≤ b then s j else 0

/-- profile valid on levels `0..n-1`, zero at levels `≥ n` -/
def IsProf (n : ℕ) (p : ℕ → ℕ) : Prop :=
  (∀ j : ℕ, j < n → p j ∈ legalVals j) ∧ (∀ j : ℕ, n ≤ j → p j = 0)

lemma zeroProf_mem_IsProf (n : ℕ) : IsProf n zeroProf := by
  constructor
  · intro j hj
    simp [zeroProf, zero_mem_legalVals]
  · intro j hj
    rfl

/-- weights of a profile over `n+1` levels split off the top value -/
lemma wsum_succ (p : ℕ → ℕ) (n : ℕ) : wsum p (n + 1) = wsum p n + p n := by
  unfold wsum
  rw [Finset.sum_range_succ]

/-- the restriction of a profile to the first `n` levels -/
noncomputable def restrictProf (n : ℕ) (p : ℕ → ℕ) : ℕ → ℕ :=
  fun j => if j < n then p j else 0

lemma wsum_restrictProf (p : ℕ → ℕ) (n : ℕ) : wsum p n = wsum (restrictProf n p) n := by
  unfold wsum restrictProf
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj' : j < n := (Finset.mem_range.mp hj)
  simp [hj']

/-- value of the restricted profile -/
lemma restrictProf_eq_of_le (p : ℕ → ℕ) (n : ℕ) :
    ∀ j, (restrictProf (n + 1) p) j = if j ≤ n then p j else 0 := by
  intro j
  unfold restrictProf
  by_cases h1 : j < n + 1
  · have hle : j ≤ n := by omega
    simp [h1, hle]
  · have hle : ¬ j ≤ n := by omega
    simp [h1, hle]

/-- the main profile bound: sum over any set of legal profiles is bounded by the total product -/
lemma profile_bound (ζ : ℝ) (hζ0 : 0 ≤ ζ) (n : ℕ) (P : Finset (ℕ → ℕ))
    (hP : ∀ p ∈ P, IsProf (n + 1) p) :
    (∑ p ∈ P, ζ ^ wsum p (n + 1)) ≤ ∏ j ∈ Finset.range (n + 1), profSum ζ j := by
  classical
  revert hP
  revert P
  induction n with
  | zero =>
      intro P hP
      -- profiles of width 1: value at level 0
      have hmap : ∀ p ∈ P, p 0 ∈ legalVals 0 := by
        intro p hp
        exact (hP p hp).1 0 (by norm_num)
      have hinj : Set.InjOn (fun p : ℕ → ℕ => p 0) (P : Set (ℕ → ℕ)) := by
        intro p hp q hq hpq
        funext j
        by_cases hj : j = 0
        · simpa [hj] using hpq
        · have hj1 : 1 ≤ j := by omega
          have hz1 : p j = 0 := (hP p hp).2 j hj1
          have hz2 : q j = 0 := (hP q hq).2 j hj1
          simp [hz1, hz2]
      calc
        (∑ p ∈ P, ζ ^ wsum p (0 + 1)) = ∑ p ∈ P, ζ ^ (p 0) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          simp [wsum]
        _ = ∑ v ∈ P.image (fun p : ℕ → ℕ => p 0), ζ ^ v := by
          exact (Finset.sum_image (f := fun v : ℕ => ζ ^ v) (g := fun p : ℕ → ℕ => p 0) hinj).symm
        _ ≤ ∑ v ∈ legalVals 0, ζ ^ v := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro v hv
            rcases (Finset.mem_image.mp hv) with ⟨p, hp, hpeq⟩
            rw [← hpeq]
            exact hmap p hp
          · intro v hv hvn
            exact pow_nonneg hζ0 v
        _ = ∏ j ∈ Finset.range (0 + 1), profSum ζ j := by
          simp [profSum]
  | succ n ih =>
      intro P hP
      -- profiles of width n+2
      have hfib : (∑ p ∈ P, ζ ^ wsum p ((n + 1) + 1)) =
          ∑ v ∈ legalVals (n + 1),
            ∑ p ∈ P.filter (fun p : ℕ → ℕ => p (n + 1) = v), ζ ^ wsum p ((n + 1) + 1) := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro p hp
        exact (hP p hp).1 (n + 1) (by omega)
      have hstep : ∀ v ∈ legalVals (n + 1),
          (∑ p ∈ P.filter (fun p : ℕ → ℕ => p (n + 1) = v), ζ ^ wsum p ((n + 1) + 1))
            ≤ ζ ^ v * (∏ j ∈ Finset.range (n + 1), profSum ζ j) := by
        intro v hv
        let Pv : Finset (ℕ → ℕ) := P.filter (fun p : ℕ → ℕ => p (n + 1) = v)
        let Q : Finset (ℕ → ℕ) := Pv.image (fun p : ℕ → ℕ => restrictProf (n + 1) p)
        have hQ : ∀ q ∈ Q, IsProf (n + 1) q := by
          intro q hq
          rcases (Finset.mem_image.mp hq) with ⟨p, hp, hpeq⟩
          have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
          rw [← hpeq]
          constructor
          · intro j hj
            have hjle : j ≤ n := by omega
            rw [restrictProf_eq_of_le p n j, if_pos hjle]
            exact (hP p hpP).1 j (by omega)
          · intro j hj
            rw [restrictProf_eq_of_le p n j]
            have hneg : ¬ j ≤ n := by omega
            rw [if_neg hneg]
        have hinj : Set.InjOn (fun p : ℕ → ℕ => restrictProf (n + 1) p) (Pv : Set (ℕ → ℕ)) := by
          intro p hp q hq hpq
          funext j
          by_cases hj1 : j ≤ n
          · have hc : restrictProf (n + 1) p j = restrictProf (n + 1) q j := by
              simpa using congr_fun hpq j
            have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
            have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
            rw [restrictProf_eq_of_le p n j, restrictProf_eq_of_le q n j, if_pos hj1, if_pos hj1] at hc
            exact hc
          · by_cases hj2 : j = n + 1
            · have hpv := (Finset.mem_filter.mp hp).2
              have hqv := (Finset.mem_filter.mp hq).2
              calc
                p j = p (n + 1) := by rw [hj2]
                _ = q (n + 1) := hpv.trans hqv.symm
                _ = q j := by rw [hj2]
            · have hgt : n + 1 + 1 ≤ j := by omega
              have hz1 : p j = 0 := (hP p (Finset.mem_filter.mp hp).1).2 j hgt
              have hz2 : q j = 0 := (hP q (Finset.mem_filter.mp hq).1).2 j hgt
              simp [hz1, hz2]
        have hQIH : (∑ q ∈ Q, ζ ^ wsum q (n + 1)) ≤ ∏ j ∈ Finset.range (n + 1), profSum ζ j := by
          exact ih Q hQ
        calc
          (∑ p ∈ Pv, ζ ^ wsum p ((n + 1) + 1))
              = ∑ p ∈ Pv, ζ ^ (wsum p (n + 1) + p (n + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                rw [wsum_succ p (n + 1)]
          _ = ∑ p ∈ Pv, (ζ ^ (wsum (restrictProf (n + 1) p) (n + 1))) * ζ ^ (p (n + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                rw [pow_add, wsum_restrictProf p (n + 1)]
          _ = ∑ p ∈ Pv, (ζ ^ (wsum (restrictProf (n + 1) p) (n + 1))) * ζ ^ v := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                rw [(Finset.mem_filter.mp hp).2]
          _ = ζ ^ v * ∑ p ∈ Pv, ζ ^ (wsum (restrictProf (n + 1) p) (n + 1)) := by
                rw [mul_comm (ζ ^ v), Finset.sum_mul]
          _ = ζ ^ v * ∑ q ∈ Q, ζ ^ wsum q (n + 1) := by
                congr 1
                exact (Finset.sum_image (f := fun q : ℕ → ℕ => ζ ^ wsum q (n + 1))
                  (g := fun p : ℕ → ℕ => restrictProf (n + 1) p) hinj).symm
          _ ≤ ζ ^ v * (∏ j ∈ Finset.range (n + 1), profSum ζ j) := by
                exact mul_le_mul_of_nonneg_left hQIH (pow_nonneg hζ0 v)
      calc
        (∑ p ∈ P, ζ ^ wsum p ((n + 1) + 1))
            = ∑ v ∈ legalVals (n + 1),
              ∑ p ∈ P.filter (fun p : ℕ → ℕ => p (n + 1) = v), ζ ^ wsum p ((n + 1) + 1) := hfib
        _ ≤ ∑ v ∈ legalVals (n + 1), (ζ ^ v * (∏ j ∈ Finset.range (n + 1), profSum ζ j)) := by
              refine Finset.sum_le_sum ?_
              intro v hv
              exact hstep v hv
        _ = (∏ j ∈ Finset.range (n + 1), profSum ζ j) * ∑ v ∈ legalVals (n + 1), ζ ^ v := by
              rw [mul_comm (∏ j ∈ Finset.range (n + 1), profSum ζ j), Finset.sum_mul]
        _ = ∏ j ∈ Finset.range ((n + 1) + 1), profSum ζ j := by
              conv_rhs => rw [Finset.prod_range_succ]
              rfl

/-- profiles of positive weight: the sum is the total minus the empty profile's contribution -/
lemma profile_bound_sub_one (ζ : ℝ) (hζ0 : 0 ≤ ζ) (n : ℕ) (P : Finset (ℕ → ℕ))
    (hP : ∀ p ∈ P, IsProf (n + 1) p)
    (hP1 : ∀ p ∈ P, 1 ≤ wsum p (n + 1)) :
    (∑ p ∈ P, ζ ^ wsum p (n + 1)) ≤ (∏ j ∈ Finset.range (n + 1), profSum ζ j) - 1 := by
  classical
  have hz0 : zeroProf ∉ P := by
    intro hz
    have hw := hP1 zeroProf hz
    have hw' : wsum zeroProf (n + 1) = 0 := by
      simp [wsum, zeroProf]
    rw [hw'] at hw
    omega
  have hQ : ∀ q ∈ (insert zeroProf P : Finset (ℕ → ℕ)), IsProf (n + 1) q := by
    intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact zeroProf_mem_IsProf (n + 1)
    · exact hP q hq
  have hb := profile_bound ζ hζ0 n (insert zeroProf P) hQ
  have hQsum : (∑ q ∈ (insert zeroProf P : Finset (ℕ → ℕ)), ζ ^ wsum q (n + 1))
      = (∑ p ∈ P, ζ ^ wsum p (n + 1)) + 1 := by
    rw [Finset.sum_insert hz0]
    have hw0 : wsum zeroProf (n + 1) = 0 := by
      simp [wsum, zeroProf]
    simp [hw0]
    ring
  have hsumP : (∑ p ∈ P, ζ ^ wsum p (n + 1)) + 1 ≤ ∏ j ∈ Finset.range (n + 1), profSum ζ j := by
    simpa [hQsum] using hb
  nlinarith

/-- the weight of a padded profile over `τ+1` levels is the partial sum -/
lemma wsum_pad (τ : ℕ) (b : ℕ) (hb : b ≤ τ) (s : ℕ → ℕ) :
    wsum (pad b s) (τ + 1) = ∑ j ∈ Finset.range (b + 1), s j := by
  unfold wsum pad
  calc
    (∑ j ∈ Finset.range (τ + 1), if j ≤ b then s j else 0)
        = ∑ j ∈ Finset.range (b + 1), if j ≤ b then s j else 0 := by
          refine (Finset.sum_subset (s₁ := Finset.range (b + 1)) (s₂ := Finset.range (τ + 1)) ?_ ?_).symm
          · intro j hj
            rw [Finset.mem_range]
            exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hb)
          · intro j hj hjn
            rw [Finset.mem_range] at hj
            have hnle : ¬ j ≤ b := by
              intro hle
              have : j < b + 1 := Nat.lt_succ_of_le hle
              exact hjn (Finset.mem_range.mpr this)
            simp [hnle]
    _ = ∑ j ∈ Finset.range (b + 1), s j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj' : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          simp [hj']

/-- a padded legal partial profile is a legal profile at level `τ+1` -/
lemma IsProf_pad (τ : ℕ) {b : ℕ} (hb : b ≤ τ) {s : ℕ → ℕ}
    (hleg : ∀ j, j ≤ b → s j ∈ legalVals j) :
    IsProf (τ + 1) (pad b s) := by
  constructor
  · intro j hj
    by_cases hle : j ≤ b
    · unfold pad
      simp [hle]
      exact hleg j hle
    · unfold pad
      simp [hle]
      exact zero_mem_legalVals j
  · intro j hj
    unfold pad
    have hnle : ¬ j ≤ b := by omega
    simp [hnle]

/-- comparing two pads when the first top level is at most the second -/
lemma pad_eq_of_le {b b' : ℕ} {s s' : ℕ → ℕ} (hbb : b ≤ b')
    (hp : pad b s = pad b' s') (hstop : s' b' ≠ 0)
    (hsz : ∀ j, b < j → s j = 0) (hsz' : ∀ j, b' < j → s' j = 0) :
    b = b' ∧ ∀ j, s j = s' j := by
  have htop' : pad b' s' b' ≠ 0 := by
    simp [pad, hstop]
  have htop : pad b s b' ≠ 0 := by
    rwa [hp]
  have hb'b : b' ≤ b := by
    by_contra h
    have : pad b s b' = 0 := by
      unfold pad
      simp [h]
    exact htop this
  have hb : b = b' := by omega
  constructor
  · exact hb
  · intro j
    by_cases hj : j ≤ b
    · calc
        s j = pad b s j := by simp [pad, hj]
        _ = pad b' s' j := by rw [hp]
        _ = s' j := by
          have hj' : j ≤ b' := by omega
          simp [pad, hj']
    · have hgt : b < j := by omega
      have hgt' : b' < j := by omega
      rw [hsz j hgt, hsz' j hgt']

/-- `pad` is injective on a set of keys with nonzero top level -/
lemma pad_injective_on {τ : ℕ} {K : Finset (ℕ × (ℕ → ℕ))}
    (hKb : ∀ k ∈ K, k.1 ≤ τ) (hKtop : ∀ k ∈ K, k.2 k.1 ≠ 0)
    (hKzero : ∀ k ∈ K, ∀ j, k.1 < j → k.2 j = 0) :
    Set.InjOn (fun k : ℕ × (ℕ → ℕ) => pad k.1 k.2) (K : Set (ℕ × (ℕ → ℕ))) := by
  intro k hk k' hk' h
  rcases k with ⟨b, s⟩
  rcases k' with ⟨b', s'⟩
  rcases le_total b b' with hbb' | hb'b
  · have hmain := pad_eq_of_le hbb' h (hKtop ⟨b', s'⟩ hk')
        (fun j hj => hKzero ⟨b, s⟩ hk j hj) (fun j hj => hKzero ⟨b', s'⟩ hk' j hj)
    rcases hmain with ⟨hb, hs⟩
    exact Prod.ext hb (funext hs)
  · have hmain := pad_eq_of_le hb'b h.symm (hKtop ⟨b, s⟩ hk)
        (fun j hj => hKzero ⟨b', s'⟩ hk' j hj) (fun j hj => hKzero ⟨b, s⟩ hk j hj)
    rcases hmain with ⟨hb', hs'⟩
    exact Prod.ext hb'.symm (funext fun j => (hs' j).symm)

/-- the key sum is bounded by the total profile product minus one -/
lemma key_sum_le_total (ζ : ℝ) (hζ0 : 0 ≤ ζ) (τ : ℕ) (K : Finset (ℕ × (ℕ → ℕ)))
    (hKb : ∀ k ∈ K, k.1 ≤ τ)
    (hKleg : ∀ k ∈ K, ∀ j : ℕ, j ≤ k.1 → Sys.LegalEntry (k.2 j) j)
    (hKtop : ∀ k ∈ K, k.2 k.1 ≠ 0)
    (hKzero : ∀ k ∈ K, ∀ j : ℕ, k.1 < j → k.2 j = 0) :
    (∑ k ∈ K, ζ ^ (∑ j ∈ Finset.range (k.1 + 1), k.2 j))
      ≤ (∏ j ∈ Finset.range (τ + 1), profSum ζ j) - 1 := by
  classical
  let P : Finset (ℕ → ℕ) := K.image (fun k : ℕ × (ℕ → ℕ) => pad k.1 k.2)
  have hP : ∀ p ∈ P, IsProf (τ + 1) p := by
    intro p hp
    rcases (Finset.mem_image.mp hp) with ⟨k, hk, hpeq⟩
    rw [← hpeq]
    exact IsProf_pad τ (hKb k hk) (fun j hle => (mem_legalVals j (k.2 j)).2 (hKleg k hk j hle))
  have hP1 : ∀ p ∈ P, 1 ≤ wsum p (τ + 1) := by
    intro p hp
    rcases (Finset.mem_image.mp hp) with ⟨k, hk, hpeq⟩
    rw [← hpeq]
    have hmem : k.1 ∈ Finset.range (k.1 + 1) := by
      simp
    have hs1 : 1 ≤ ∑ j ∈ Finset.range (k.1 + 1), k.2 j := by
      have hterm : k.2 k.1 ≤ ∑ j ∈ Finset.range (k.1 + 1), k.2 j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le (k.2 j)) hmem
      have hnz : 1 ≤ k.2 k.1 := by
        have hz : k.2 k.1 ≠ 0 := hKtop k hk
        omega
      omega
    calc
      1 ≤ ∑ j ∈ Finset.range (k.1 + 1), k.2 j := hs1
      _ = wsum (pad k.1 k.2) (τ + 1) := (wsum_pad τ k.1 (hKb k hk) (k.2)).symm
  have hb := profile_bound_sub_one ζ hζ0 τ P hP hP1
  have hkeysum : (∑ k ∈ K, ζ ^ (∑ j ∈ Finset.range (k.1 + 1), k.2 j))
      = ∑ p ∈ P, ζ ^ wsum p (τ + 1) := by
    calc
      (∑ k ∈ K, ζ ^ (∑ j ∈ Finset.range (k.1 + 1), k.2 j))
          = ∑ k ∈ K, ζ ^ wsum (pad k.1 k.2) (τ + 1) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            congr 1
            exact (wsum_pad τ k.1 (hKb k hk) (k.2)).symm
      _ = ∑ p ∈ P, ζ ^ wsum p (τ + 1) := by
            dsimp [P]
            exact (Finset.sum_image (f := fun p : ℕ → ℕ => ζ ^ wsum p (τ + 1))
              (g := fun k : ℕ × (ℕ → ℕ) => pad k.1 k.2)
              (pad_injective_on hKb hKtop hKzero)).symm
  rw [hkeysum]
  exact hb

/-- the total product can be rewritten in terms of `u` -/
lemma total_prod_eq (ζ : ℝ) (τ : ℕ) :
    (∏ j ∈ Finset.range (τ + 1), profSum ζ j) = ∏ j ∈ Finset.range (τ + 1), (1 + u ζ j) := by
  refine Finset.prod_congr rfl ?_
  intro j hj
  exact profSum_eq_one_add_u ζ j

/-- profile-sum bound: over any finite family of legal partial profiles the total weight is `≤ 1/10`. -/
theorem profile_sum_bound (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ9 : ζ ≤ ((10 : ℝ) ^ 9)⁻¹)
    (τ : ℕ) (K : Finset (ℕ × (ℕ → ℕ)))
    (hKb : ∀ k ∈ K, k.1 ≤ τ)
    (hKleg : ∀ k ∈ K, ∀ j : ℕ, j ≤ k.1 → Sys.LegalEntry (k.2 j) j)
    (hKtop : ∀ k ∈ K, k.2 k.1 ≠ 0)
    (hKzero : ∀ k ∈ K, ∀ j : ℕ, k.1 < j → k.2 j = 0) :
    (∑ k ∈ K, ζ ^ (∑ j ∈ Finset.range (k.1 + 1), k.2 j)) ≤ (10 : ℝ)⁻¹ := by
  classical
  have hkey := key_sum_le_total ζ hζ0 τ K hKb hKleg hKtop hKzero
  have htotal : (∏ j ∈ Finset.range (τ + 1), profSum ζ j) =
      ∏ j ∈ Finset.range (τ + 1), (1 + u ζ j) := total_prod_eq ζ τ
  have hsumu := partial_sum_u_le ζ hζ0 hζ9 τ
  have h12 : (∑ j ∈ Finset.range (τ + 1), u ζ j) ≤ (1 / 2 : ℝ) := by
    have hm : 37 * ζ ≤ 37 * ((10 : ℝ) ^ 9)⁻¹ :=
      mul_le_mul_of_nonneg_left hζ9 (by norm_num)
    have hbig : 37 * ((10 : ℝ) ^ 9)⁻¹ ≤ (1 / 2 : ℝ) := by norm_num
    exact le_trans hsumu (le_trans hm hbig)
  have hprod := prod_one_add_u_le ζ hζ0 τ h12
  calc
    (∑ k ∈ K, ζ ^ (∑ j ∈ Finset.range (k.1 + 1), k.2 j))
        ≤ (∏ j ∈ Finset.range (τ + 1), profSum ζ j) - 1 := hkey
    _ = (∏ j ∈ Finset.range (τ + 1), (1 + u ζ j)) - 1 := by rw [htotal]
    _ ≤ (1 + 2 * (∑ j ∈ Finset.range (τ + 1), u ζ j)) - 1 := by
        linarith [hprod]
    _ = 2 * (∑ j ∈ Finset.range (τ + 1), u ζ j) := by ring
    _ ≤ 2 * (37 * ζ) := by
        exact mul_le_mul_of_nonneg_left hsumu (by norm_num : 0 ≤ (2 : ℝ))
    _ = 74 * ζ := by ring
    _ ≤ (10 : ℝ)⁻¹ := by
        have hm : 74 * ζ ≤ 74 * ((10 : ℝ) ^ 9)⁻¹ :=
          mul_le_mul_of_nonneg_left hζ9 (by norm_num)
        have hbig : 74 * ((10 : ℝ) ^ 9)⁻¹ ≤ (10 : ℝ)⁻¹ := by norm_num
        exact le_trans hm hbig

end ProfileSum
end Submission
