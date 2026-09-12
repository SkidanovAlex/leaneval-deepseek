import Mathlib


/-!
# GOAL (Dimitrov's "squarerad" integrality, coefficient form)

If `G = U² + 4V` is an integer power series with `U(0) = 1` and
`G(0) = 1`, then the square root `f` of `G` with `f(0) = 1` (over ℚ) has
integer coefficients.

Formalized with sequences: `g k`, `u k`, `v k` are the coefficients of
`G, U, V`; the hypothesis is the convolution identity
`g k = (U*U coeff k) + 4 v k`, i.e.
`g k = (∑ i ∈ range (k+1), u i * u (k - i)) + 4 * v k`,
and `b k` are the coefficients of the square root (over ℚ):
`b 0 = 1` and `conv(b) k = g k` for all `k`
(`(∑ i ∈ range (k+1), b i * b (k - i)) = (g k : ℚ)`).
Prove: every `b k` is an integer.

## Proof summary (parity induction)

Split the convolution sums at the ends:
`conv a k = 2 * a k + mid a k` where `mid` collects the middle pairs
`(i+1, k-1-i)`, `i ∈ range (k-1)`.

Induction hypothesis: for every `j < k`, `b j` is an integer
(`(B j : ℚ) = b j` with `B j : ℤ`) and `b j ≡ u j (mod 2)`
(`B j = u j + 2 * C j`).  Then the middle product difference
`mid b k - mid u k` is divisible by 4 (expand `B = U + 2C` in the product
difference; the two asymmetric cross terms cancel by reflection
`i ↦ k - 1 - (i+1)`, implemented in `cross_refl`/`mid4`).

Combining with the convolution equation yields
`2 (b k - u k) = 4 * (integer)`, hence `b k = u k + 2 * c` for an integer
`c`, finishing the induction.
-/

noncomputable section

open scoped BigOperators

namespace Submission.SqrtInt

/-- Convolution sum `Σ_{i=0}^k a i * a (k - i)` (over ℚ). -/
def conv (a : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (k + 1), a i * a (k - i)

/-- Middle product sum: pairs `(j, k-j)` with `1 ≤ j ≤ k-1`, indexed by
  `i ↦ (i+1, k-1-i)`, `i ∈ range (k-1)`. -/
def mid (a : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (k - 1), a (i + 1) * a (k - 1 - i)

/-- Integer version of `mid`. -/
def midZ (A : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k - 1), A (i + 1) * A (k - 1 - i)

/-- Isolate the two end terms of the convolution (which contribute `2 * a k`,
  since `a 0 = 1`). -/
lemma split_conv (a : ℕ → ℚ) (ha0 : a 0 = 1) {k : ℕ} (hk : 0 < k) :
    conv a k = 2 * a k + mid a k := by
  unfold conv mid
  rw [Finset.sum_range_succ]
  have hk1 : (k - 1) + 1 = k := by omega
  have hR : Finset.range k = Finset.range ((k - 1) + 1) := by rw [hk1]
  rw [hR]
  rw [Finset.sum_range_succ' (fun i => a i * a (k - i)) (k - 1)]
  have hsum : (∑ i ∈ Finset.range (k - 1), a (i + 1) * a (k - (i + 1))) =
      ∑ i ∈ Finset.range (k - 1), a (i + 1) * a (k - 1 - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have h : k - (i + 1) = k - 1 - i := by omega
    simp [h]
  rw [hsum]
  simp [ha0]
  ring

/-- Reflection symmetry of the middle index set: `i ↦ k-1-(i+1)` runs over
  `range (k-1)` and swaps the two factors. -/
lemma cross_refl (P Q : ℕ → ℤ) (k : ℕ) :
    (∑ i ∈ Finset.range (k - 1), P (i + 1) * Q (k - 1 - i)) =
      ∑ i ∈ Finset.range (k - 1), Q (i + 1) * P (k - 1 - i) := by
  apply Finset.sum_bij (fun i _ => k - 1 - (i + 1))
  · intro i hi
    have hi' : i < k - 1 := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb h
    have ha' : a < k - 1 := Finset.mem_range.mp ha
    have hb' : b < k - 1 := Finset.mem_range.mp hb
    omega
  · intro b hb
    have hb' : b < k - 1 := Finset.mem_range.mp hb
    refine ⟨k - 1 - (b + 1), ?_, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · have h1 : k - 1 - (b + 1) + 1 = k - 1 - b := by omega
      have h2 : k - 1 - (k - 1 - b) = b := by
        exact Nat.sub_sub_self (by omega : b ≤ k - 1)
      rw [h1, h2]
  · intro a ha
    have ha' : a < k - 1 := Finset.mem_range.mp ha
    have h1 : k - 1 - (a + 1) + 1 = k - 1 - a := by omega
    have h2 : k - 1 - (k - 1 - (a + 1)) = a + 1 := by
      exact Nat.sub_sub_self (by omega : a + 1 ≤ k - 1)
    rw [h1, h2]
    ring

/-- If `B ≡ U (mod 2)` termwise on the middle indices (say `B = U + 2 C`),
  then the middle-product difference is divisible by 4. -/
lemma mid4 (B U C : ℕ → ℤ) (k : ℕ)
    (h : ∀ j, j ≤ k - 1 → B j = U j + 2 * C j) :
    (4 : ℤ) ∣ midZ B k - midZ U k := by
  unfold midZ
  rw [← Finset.sum_sub_distrib]
  refine ⟨∑ i ∈ Finset.range (k - 1), (U (i + 1) * C (k - 1 - i) + C (i + 1) * C (k - 1 - i)), ?_⟩
  have hrewrite :
      (∑ i ∈ Finset.range (k - 1), (B (i + 1) * B (k - 1 - i) - U (i + 1) * U (k - 1 - i))) =
        ∑ i ∈ Finset.range (k - 1),
          (2 * (U (i + 1) * C (k - 1 - i)) + 2 * (C (i + 1) * U (k - 1 - i)) +
            4 * (C (i + 1) * C (k - 1 - i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i < k - 1 := Finset.mem_range.mp hi
    have hbi : B (i + 1) = U (i + 1) + 2 * C (i + 1) := h (i + 1) (by omega)
    have hbk : B (k - 1 - i) = U (k - 1 - i) + 2 * C (k - 1 - i) := h (k - 1 - i) (by omega)
    rw [hbi, hbk]
    ring
  rw [hrewrite]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  rw [mul_add]
  rw [← cross_refl U C k]
  ring

/-- Casting an integer middle-product sum into ℚ gives the rational one. -/
lemma midZ_cast (A : ℕ → ℤ) (k : ℕ) : ((midZ A k : ℤ) : ℚ) = mid (fun j => (A j : ℚ)) k := by
  unfold midZ mid
  norm_num

/-- Rational form of `mid4`: under the same hypotheses (with `B` the integer
  value of `b` on the middle indices), `mid b k - mid u k = 4 * q`. -/
lemma mid4_Q (b : ℕ → ℚ) (u : ℕ → ℤ) (B C : ℕ → ℤ) (k : ℕ)
    (hB : ∀ j, j ≤ k - 1 → (B j : ℚ) = b j)
    (h : ∀ j, j ≤ k - 1 → B j = u j + 2 * C j) :
    ∃ q0 : ℤ, mid b k - mid (fun j => (u j : ℚ)) k = 4 * (q0 : ℚ) := by
  obtain ⟨q, hq⟩ := mid4 B u C k h
  have h1 := midZ_cast B k
  have h2 := midZ_cast u k
  have hBmid : mid (fun j => (B j : ℚ)) k = mid b k := by
    unfold mid
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < k - 1 := Finset.mem_range.mp hi
    have hb1 := hB (i + 1) (by omega)
    have hb2 := hB (k - 1 - i) (by omega)
    simp [hb1, hb2]
  refine ⟨q, ?_⟩
  calc
    mid b k - mid (fun j => (u j : ℚ)) k
        = mid (fun j => (B j : ℚ)) k - mid (fun j => (u j : ℚ)) k := by rw [hBmid]
    _ = ((midZ B k : ℤ) : ℚ) - ((midZ u k : ℤ) : ℚ) := by rw [h1, h2]
    _ = ((midZ B k - midZ u k : ℤ) : ℚ) := by rw [Int.cast_sub]
    _ = ((4 * q : ℤ) : ℚ) := by rw [hq]
    _ = 4 * (q : ℚ) := by norm_num

/-- Pure rational step: from the convolution equality
  `conv b n = conv u n + 4 * v n` and the mod-4 middle congruence, the next
  coefficient satisfies `b n = u n + 2 * c` for an integer `c`. -/
lemma core_step (b u : ℕ → ℚ) (zv q0 : ℤ) {n : ℕ} (hn : 0 < n)
    (hb0 : b 0 = 1) (hu0 : u 0 = 1)
    (hconv1 : conv b n = conv u n + 4 * ((zv : ℤ) : ℚ))
    (hmid : mid b n - mid u n = 4 * ((q0 : ℤ) : ℚ)) :
    ∃ c : ℤ, b n = u n + 2 * ((c : ℤ) : ℚ) := by
  have hsplit1 := split_conv b hb0 hn
  have hsplit2 := split_conv u hu0 hn
  have htwo : 2 * (b n - u n) = 4 * (((zv - q0) : ℤ) : ℚ) := by
    calc
      2 * (b n - u n) = (conv b n - conv u n) - (mid b n - mid u n) := by
        rw [hsplit1, hsplit2]
        ring
      _ = 4 * ((zv : ℤ) : ℚ) - 4 * ((q0 : ℤ) : ℚ) := by
        rw [hconv1, hmid]
        ring
      _ = 4 * (((zv - q0) : ℤ) : ℚ) := by
        rw [Int.cast_sub]
        ring
  have hdiv : b n - u n = 2 * (((zv - q0) : ℤ) : ℚ) := by
    linarith
  refine ⟨zv - q0, ?_⟩
  linarith

/-- Square-root integrality (squarerad), coefficient form over ℤ/ℚ. -/
theorem sqrt_integral (g : ℕ → ℤ) (u : ℕ → ℤ) (v : ℕ → ℤ)
    (hu0 : u 0 = 1)
    (hconv : ∀ k : ℕ,
      g k = (∑ i ∈ Finset.range (k + 1), u i * u (k - i)) + 4 * v k)
    (b : ℕ → ℚ) (hb0 : b 0 = 1)
    (hbsq : ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), b i * b (k - i)) = (g k : ℚ)) :
    ∀ k : ℕ, ∃ z : ℤ, (z : ℚ) = b k := by
  let P : ℕ → Prop := fun k =>
    (∃ z : ℤ, (z : ℚ) = b k) ∧ ∃ c : ℤ, (b k : ℚ) = (u k : ℚ) + 2 * ((c : ℤ) : ℚ)
  have hmain : ∀ k, P k := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ihn
    by_cases hn0 : n = 0
    · subst n
      refine ⟨⟨1, ?_⟩, ⟨0, ?_⟩⟩
      · simp [hb0]
      · simp [hb0, hu0]
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      let B : ℕ → ℤ := fun j => if hj : j < n then Classical.choose (ihn j hj).1 else 0
      let C : ℕ → ℤ := fun j => if hj : j < n then Classical.choose (ihn j hj).2 else 0
      have hB : ∀ j, j < n → (B j : ℚ) = b j := by
        intro j hj
        simp [B, hj]
        exact Classical.choose_spec (ihn j hj).1
      have hC : ∀ j, j < n → (b j : ℚ) = (u j : ℚ) + 2 * ((C j : ℤ) : ℚ) := by
        intro j hj
        simp [C, hj]
        exact Classical.choose_spec (ihn j hj).2
      have hBUC : ∀ j, j ≤ n - 1 → B j = u j + 2 * C j := by
        intro j hj
        have hjlt : j < n := by omega
        have hcast1 : ((B j : ℤ) : ℚ) = ((u j + 2 * C j : ℤ) : ℚ) := by
          rw [hB j hjlt]
          rw [hC j hjlt]
          norm_num
        exact_mod_cast hcast1
      obtain ⟨q0, hmid⟩ := mid4_Q b u B C n (fun j hj => hB j (by omega)) hBUC
      have hconv1 : conv b n = conv (fun j : ℕ => (u j : ℚ)) n + 4 * ((v n : ℤ) : ℚ) := by
        have hgQ : ((g n : ℤ) : ℚ) = conv (fun j : ℕ => (u j : ℚ)) n + 4 * ((v n : ℤ) : ℚ) := by
          have hc := congrArg (fun x : ℤ => (x : ℚ)) (hconv n)
          simpa [conv] using hc
        exact (hbsq n).trans hgQ
      have huQ0 : (fun j : ℕ => (u j : ℚ)) 0 = 1 := by simp [hu0]
      obtain ⟨c, hc⟩ := core_step b (fun j : ℕ => (u j : ℚ)) (v n) q0 hn hb0 huQ0 hconv1 hmid
      refine ⟨⟨u n + 2 * c, ?_⟩, ⟨c, ?_⟩⟩
      · rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
        exact hc.symm
      · exact hc
  intro k
  exact (hmain k).1

end Submission.SqrtInt
