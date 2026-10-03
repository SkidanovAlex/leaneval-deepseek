import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs

namespace Work.A7

/-!
# Decomposition of a sum over an interval into residue classes mod `q`

This file proves `Work.A7.sum_class_decomp`: a sum over `(K, N]` of a `q`-periodic weight times
a test function splits into the sums over the residue classes `a ∈ [0,q)`, each of which is
indexed by `m ∈ Icc (mFirst q K a) (mLast q N a)` via `n = a + q m`.

The proof is a reindexing: `Finset.sum_fiberwise_of_maps_to` for the map `n ↦ n % q` reduces to
the fibre sums, and each fibre is identified with `Icc (mFirst q K a) (mLast q N a)` by the
bijection `n ↦ n / q` (`Finset.sum_bij'`), inverse `m ↦ (a + q m).toNat`.
-/

open Finset

/-! ## Elementary periodicity and index arithmetic -/

/-- Iteration of the periodicity hypothesis `hc`: `c (x + q * m) = c x` for every `m : ℕ`. -/
lemma periodicity_mul (q : ℕ) (c : ℤ → ℂ) (hc : ∀ n : ℤ, c (n + q) = c n) :
    ∀ (m : ℕ) (x : ℤ), c (x + (q:ℤ) * m) = c x := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have h : x + (q:ℤ) * ((k+1 : ℕ) : ℤ) = (x + (q:ℤ)*((k:ℕ):ℤ)) + q := by push_cast; ring
    rw [h]
    rw [hc]
    exact ih x

/-- The division algorithm: if `n % q = a` then `n = a + q * (n / q)`. -/
lemma eq_add_mul_div {q a n : ℕ} (h : n % q = a) : n = a + q * (n / q) := by
  have := Nat.mod_add_div n q
  rw [h] at this
  exact this.symm

/-- The `ℤ`-valued form of `eq_add_mul_div`. -/
lemma cast_eq_add_mul_div {q a n : ℕ} (h : n % q = a) :
    (n:ℤ) = (a:ℤ) + (q:ℤ)*((n/q:ℕ):ℤ) := by
  have h1 : a + q*(n/q) = n := (eq_add_mul_div h).symm
  have h2 : ((a + q*(n/q) : ℕ) : ℤ) = (a:ℤ) + (q:ℤ)*((n/q:ℕ):ℤ) := by push_cast; ring
  rw [h1] at h2
  exact h2

/-- `mFirst` is always non-negative. -/
lemma mFirst_nonneg (q K a : ℕ) : 0 ≤ mFirst q K a := by
  unfold mFirst
  split_ifs with h
  · push_cast; positivity
  · norm_num

/-- `(a + q m).toNat = a + q * m.toNat` for `m ≥ 0`. -/
lemma toNat_add_mul (q a : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    ((a : ℤ) + (q : ℤ) * m).toNat = a + q * m.toNat := by
  have hle : (0:ℤ) ≤ (a:ℤ) + (q:ℤ)*m := by
    have h1 : (0:ℤ) ≤ (q:ℤ)*m := mul_nonneg (by positivity) hm
    have h2 : (0:ℤ) ≤ (a:ℤ) := by positivity
    linarith
  apply (Nat.cast_inj (R := ℤ)).mp
  rw [Int.toNat_of_nonneg hle]
  push_cast
  rw [Int.toNat_of_nonneg hm]

/-! ## The two inclusions of the index bijection -/

/-- If `m ≥ mFirst q K a` then `a + q m > K`. -/
lemma lt_toNat_of_mFirst_le (q : ℕ) (hq : 0 < q) (K a : ℕ) {m : ℤ}
    (hm : mFirst q K a ≤ m) : K < (a + (q:ℤ)*m).toNat := by
  have hm0 : 0 ≤ m := le_trans (mFirst_nonneg q K a) hm
  rw [toNat_add_mul q a hm0]
  rw [mFirst] at hm
  split_ifs at hm with hK
  · have h1 : (K - a)/q + 1 ≤ m.toNat := by
      rw [Int.le_toNat hm0]
      push_cast
      exact hm
    have h2 : q * ((K-a)/q + 1) ≤ q * m.toNat := Nat.mul_le_mul_left q h1
    have h3 : K - a < q * ((K-a)/q + 1) := by
      rw [mul_comm]
      exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
    have h4 : K - a < q * m.toNat := lt_of_lt_of_le h3 h2
    calc K = a + (K - a) := (Nat.add_sub_of_le hK).symm
      _ < a + q * m.toNat := Nat.add_lt_add_left h4 a
  · have hK' : K < a := lt_of_not_ge hK
    exact lt_of_lt_of_le hK' (Nat.le_add_right a _)

/-- If `m ≤ mLast q N a` and `m ≥ 0` then `a + q m ≤ N`. -/
lemma toNat_le_of_le_mLast (q : ℕ) (_hq : 0 < q) (N a : ℕ) {m : ℤ}
    (hm0 : 0 ≤ m) (hm : m ≤ mLast q N a) : (a + (q:ℤ)*m).toNat ≤ N := by
  rw [toNat_add_mul q a hm0]
  rw [mLast] at hm
  split_ifs at hm with hN
  · have h1 : m.toNat ≤ (N - a)/q := by
      rw [Int.toNat_le]
      exact hm
    have h2 : q * m.toNat ≤ q * ((N-a)/q) := Nat.mul_le_mul_left q h1
    have h3 : q * ((N-a)/q) ≤ N - a := Nat.mul_div_le (N-a) q
    have h4 : q * m.toNat ≤ N - a := le_trans h2 h3
    calc a + q * m.toNat ≤ a + (N - a) := Nat.add_le_add_left h4 a
      _ = N := Nat.add_sub_of_le hN
  · exfalso; omega

/-- If `m ≥ mFirst q K a` and `a < q` then `a + q m ≡ a (mod q)`. -/
lemma toNat_mod_of_mFirst_le (q : ℕ) (K a : ℕ) (ha : a < q) {m : ℤ}
    (hm : mFirst q K a ≤ m) : (a + (q:ℤ)*m).toNat % q = a := by
  have hm0 : 0 ≤ m := le_trans (mFirst_nonneg q K a) hm
  rw [toNat_add_mul q a hm0]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

/-- If `n > K` and `n % q = a` then `n / q ≥ mFirst q K a`. -/
lemma mFirst_le_div (q : ℕ) (hq : 0 < q) {a : ℕ} (_ha : a < q) {K n : ℕ}
    (h : n % q = a) (hn : K < n) :
    mFirst q K a ≤ ((n / q : ℕ) : ℤ) := by
  have hna : n = a + q * (n/q) := eq_add_mul_div h
  rw [mFirst]
  split_ifs with hK
  · have hKa : K = a + (K - a) := (Nat.add_sub_of_le hK).symm
    have hlt : K - a < q * (n/q) := by
      have : a + (K - a) < a + q*(n/q) := by rw [← hKa, ← hna]; exact hn
      exact (Nat.add_lt_add_iff_left).mp this
    have hlt2 : (K - a)/q < n/q := by
      rw [Nat.div_lt_iff_lt_mul hq, mul_comm]
      exact hlt
    have hle : (K-a)/q + 1 ≤ n/q := Nat.succ_le_of_lt hlt2
    push_cast
    exact_mod_cast hle
  · push_cast
    exact Int.natCast_nonneg _

/-- If `n ≤ N` and `n % q = a` then `n / q ≤ mLast q N a`. -/
lemma div_le_mLast (q : ℕ) (hq : 0 < q) {a : ℕ} (_ha : a < q) {N n : ℕ}
    (h : n % q = a) (hn : n ≤ N) :
    ((n / q : ℕ) : ℤ) ≤ mLast q N a := by
  have hna : n = a + q*(n/q) := eq_add_mul_div h
  have haN : a ≤ N := by
    have : a ≤ n := by rw [← h]; exact Nat.mod_le n q
    omega
  rw [mLast, if_pos haN]
  have h1 : q * (n/q) ≤ N - a := by
    have h2 : a + q*(n/q) ≤ N := by rw [← hna]; exact hn
    exact Nat.le_sub_of_add_le (by rw [add_comm]; exact h2)
  have h3 : n/q ≤ (N-a)/q := by
    rw [Nat.le_div_iff_mul_le hq, mul_comm]
    exact h1
  exact_mod_cast h3

/-! ## The fibre sum over one residue class -/

/-- **One residue class.**  For `a < q`, the sum of `F` over the `n ∈ (K, N]` with `n ≡ a (mod q)`
equals the sum of `F` over `m ∈ Icc (mFirst q K a) (mLast q N a)` evaluated at `a + q m`. -/
lemma sum_filter_mod_eq_sum_Icc (q : ℕ) (hq : 0 < q) (a : ℕ) (ha : a < q) (K N : ℕ)
    (F : ℤ → ℂ) :
    ∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), F (n : ℤ)
      = ∑ m ∈ Finset.Icc (mFirst q K a) (mLast q N a), F ((a : ℤ) + (q : ℤ) * m) := by
  refine Finset.sum_bij' (fun n _ => ((n/q:ℕ):ℤ)) (fun m _ => (a + (q:ℤ)*m).toNat)
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc]
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact ⟨mFirst_le_div q hq ha hn.2 hn.1.1, div_le_mLast q hq ha hn.2 hn.1.2⟩
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc]
    rw [Finset.mem_Icc] at hm
    exact ⟨⟨lt_toNat_of_mFirst_le q hq K a hm.1,
            toNat_le_of_le_mLast q hq N a (le_trans (mFirst_nonneg q K a) hm.1) hm.2⟩,
           toNat_mod_of_mFirst_le q K a ha hm.1⟩
  · intro n hn
    rw [Finset.mem_filter] at hn
    show (a + (q:ℤ) * (((n/q:ℕ):ℤ))).toNat = n
    rw [toNat_add_mul q a (Int.natCast_nonneg _), Int.toNat_natCast]
    exact (eq_add_mul_div hn.2).symm
  · intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : 0 ≤ m := le_trans (mFirst_nonneg q K a) hm.1
    show ((((a + (q:ℤ)*m).toNat) / q : ℕ) : ℤ) = m
    rw [toNat_add_mul q a hm0]
    rw [show a + q * m.toNat = a + m.toNat * q from by rw [mul_comm]]
    rw [Nat.add_mul_div_right a m.toNat hq, Nat.div_eq_of_lt ha, Nat.zero_add]
    exact Int.toNat_of_nonneg hm0
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact congrArg F (cast_eq_add_mul_div hn.2)

/-! ## The decomposition -/

/-- **Decomposition of a sum over `(K, N]` into the residue classes mod `q`**, for a `q`-periodic
weight `c`.  For every `a ∈ [0,q)` the integers `n ≤ N` with `n ≡ a (mod q)` and `n > K` are exactly
`a + q m` with `mFirst q K a ≤ m ≤ mLast q N a` (as defined in
`Submission/Work/A7/ModelApproxCore_M0_defs.lean`).
Proof: `Finset.sum_fiberwise_of_maps_to` with `g n = n % q` plus the reindexing
`n = a + q m` (`Nat.div_add_mod`) and the periodicity of `c` (iteration of `hc`). -/
theorem sum_class_decomp (q : ℕ) (hq : 0 < q) (K N : ℕ) (c F : ℤ → ℂ)
    (hc : ∀ n : ℤ, c (n + q) = c n) :
    ∑ n ∈ Finset.Ioc K N, c (n : ℤ) * F (n : ℤ)
      = ∑ a ∈ Finset.range q, c (a : ℤ) *
          ∑ m ∈ Finset.Icc (Work.A7.mFirst q K a) (Work.A7.mLast q N a),
            F ((a : ℤ) + (q : ℤ) * m) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.Ioc K N) (t := Finset.range q)
        (g := fun n : ℕ => n % q) (f := fun n : ℕ => c (n:ℤ) * F (n:ℤ))
        (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hq))]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a < q := Finset.mem_range.mp ha
  rw [Finset.mul_sum]
  trans c (a:ℤ) * ∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), F (n:ℤ)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_filter] at hn
    have hcn : c (n:ℤ) = c (a:ℤ) := by
      rw [cast_eq_add_mul_div hn.2]
      exact periodicity_mul q c hc (n/q) (a:ℤ)
    rw [hcn]
  · rw [sum_filter_mod_eq_sum_Icc q hq a ha' K N F, Finset.mul_sum]

end Work.A7
