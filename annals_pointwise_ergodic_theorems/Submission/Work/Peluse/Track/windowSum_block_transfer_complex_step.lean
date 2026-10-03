import Mathlib
import Submission.Work.Peluse.Peel.windowSum_block_transfer

/-!
# Block transfer for the `d`-stepped window sums: the complex step

`Work.Peluse.Track.windowSum_block_transfer_complex_step` compares the squared `M`-window sums of
a bounded complex function `ψ` supported in `symIcc N = [-N,N]` with its squared `L`-window sums,
`1 ≤ L ≤ M`, for a general step `d : ℤ`:

```
∑_{x ∈ [-N,N]} |∑_{y ∈ [1,M]} ψ (x + d y)|²
    ≤ 2 (M/L)² ∑_{x ∈ [-N,N+L|d|]} |∑_{y ∈ [1,L]} ψ (x + d y)|² + 2 L² #[-N,N] .
```

The mechanism is the exact block decomposition of the `M`-window: writing `K = M / L` (so
`K L ≤ M`), the interval `[1, K L]` is the disjoint union of the `K` blocks `[kL+1, (k+1)L]`,
`k < K`, so with `W_L(z) = ∑_{i ∈ [1,L]} ψ (z + d i)`,

`∑_{y ∈ [1,M]} ψ (x + d y) = ∑_{k<K} W_L (x + d k L) + ∑_{y ∈ [KL+1,M]} ψ (x + d y)`,

the second sum having at most `L` terms.  Cauchy–Schwarz over the `K` blocks gives
`|∑_{k<K} W_L(x+dkL)|² ≤ K ∑_{k<K} |W_L(x+dkL)|²`; summing over `x ∈ [-N,N]`, exchanging the order
of summation and re-indexing each inner sum by the *injective* shift `x ↦ x + d k L` loses nothing,
because `W_L` vanishes off `[-N-L|d|, N+L|d|]` (`ψ` is supported in `[-N,N]`), so that the image of
`[-N,N]` under the shift is, on the support of `W_L`, a sub-sum of `∑_{z ∈ [-N-L|d|,N+L|d|]} |W_L z|²`.
Finally each term of the excess has norm at most `1`, so the excess contributes `≤ L²` per `x`.

## Reference

B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Ann. of Math. **195** (2022), §5.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Peluse.Track

/-- `z ∈ symIcc A = [-A,A]` iff `|z| ≤ A`. -/
lemma mem_symIcc_iff_natAbs {A : ℕ} {z : ℤ} : z ∈ Work.Peluse.symIcc A ↔ z.natAbs ≤ A := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |z| ≤ (A : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro hz
    have h : (z.natAbs : ℤ) ≤ (A : ℤ) := by exact_mod_cast hz
    rw [Int.natCast_natAbs] at h
    exact abs_le.mp h

/-- **Shifting the summation index loses nothing**, for a nonnegative summand `a` that vanishes
outside `symIcc Q`: for any shift `c : ℤ`,

`∑_{x ∈ symIcc N} a (x + c) ≤ ∑_{z ∈ symIcc Q} a z`.

Indeed the terms of the left-hand sum whose shifted index leaves `symIcc Q` vanish, and the
remaining indices, being the image of an injective shift, form a sub-sum of the right-hand one. -/
lemma sum_symIcc_shift_le {N Q : ℕ} {a : ℤ → ℝ} (ha : ∀ z, 0 ≤ a z)
    (h0 : ∀ z : ℤ, z ∉ Work.Peluse.symIcc Q → a z = 0) (c : ℤ) :
    (∑ x ∈ Work.Peluse.symIcc N, a (x + c)) ≤ ∑ z ∈ Work.Peluse.symIcc Q, a z := by
  classical
  have hinj : Set.InjOn (fun x : ℤ => x + c) ↑(Work.Peluse.symIcc N) :=
    fun x _ y _ h => by simpa using add_right_cancel h
  rw [← Finset.sum_image (f := a) hinj]
  have hfil : (∑ z ∈ (Work.Peluse.symIcc N).image (fun x : ℤ => x + c), a z)
      = ∑ z ∈ ((Work.Peluse.symIcc N).image (fun x : ℤ => x + c)).filter
          (fun z => z ∈ Work.Peluse.symIcc Q), a z := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases h : z ∈ Work.Peluse.symIcc Q
    · simp [h]
    · simp [h, h0 z h]
  rw [hfil]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun z hz => (Finset.mem_filter.mp hz).2) (fun z _ _ => ha z)

/-- If `z + d·i ∈ symIcc N` and `i ≤ L` then `z ∈ symIcc (N + L·|d|)`: indeed
`|z| ≤ |z + d i| + |d| i ≤ N + |d| L`. -/
lemma mem_symIcc_of_add_mul_mem {N L : ℕ} {d z : ℤ} {i : ℕ} (hi : i ≤ L)
    (h : z + d * (i : ℤ) ∈ Work.Peluse.symIcc N) :
    z ∈ Work.Peluse.symIcc (N + L * d.natAbs) := by
  rw [mem_symIcc_iff_natAbs] at h ⊢
  have hcast : ((N + L * d.natAbs : ℕ) : ℤ) = (N : ℤ) + (L : ℤ) * |d| := by
    rw [Nat.cast_add, Nat.cast_mul, Int.natCast_natAbs]
  have h2 : |z + d * (i : ℤ)| ≤ (N : ℤ) := by
    rw [← Int.natCast_natAbs (z + d * (i : ℤ))]
    exact_mod_cast h
  have h3 : |d * (i : ℤ)| = |d| * (i : ℤ) := by
    rw [abs_mul]
    exact congrArg (fun t => |d| * t) (abs_of_nonneg (Int.natCast_nonneg i))
  have h4 : (i : ℤ) ≤ (L : ℤ) := by exact_mod_cast hi
  have h5 : |d| * (i : ℤ) ≤ |d| * (L : ℤ) := mul_le_mul_of_nonneg_left h4 (abs_nonneg d)
  have h1 : |z| ≤ (N : ℤ) + (L : ℤ) * |d| := by
    calc |z| = |(z + d * (i : ℤ)) - d * (i : ℤ)| := by ring_nf
      _ ≤ |z + d * (i : ℤ)| + |d * (i : ℤ)| := abs_sub _ _
      _ ≤ (N : ℤ) + |d| * (L : ℤ) := by linarith
      _ = (N : ℤ) + (L : ℤ) * |d| := by ring
  have h6 : ((z.natAbs : ℤ)) ≤ ((N + L * d.natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, hcast]
    exact h1
  exact_mod_cast h6

theorem windowSum_block_transfer_complex_step {N M L : ℕ} (hL : 1 ≤ L) (hLM : L ≤ M) (d : ℤ)
    (ψ : ℤ → ℂ) (hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → ψ x = 0)
    (hbd : ∀ x : ℤ, ‖ψ x‖ ≤ 1) :
    (∑ x ∈ Work.Peluse.symIcc N, ‖∑ y ∈ Finset.Icc 1 M, ψ (x + d * (y : ℤ))‖ ^ 2)
      ≤ 2 * (((M / L : ℕ) : ℝ)) ^ 2
          * (∑ x ∈ Work.Peluse.symIcc (N + L * d.natAbs),
              ‖∑ y ∈ Finset.Icc 1 L, ψ (x + d * (y : ℤ))‖ ^ 2)
        + 2 * (L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
  classical
  set K : ℕ := M / L with hK
  set Q : ℕ := N + L * d.natAbs with hQ
  set W : ℤ → ℂ := fun z => ∑ i ∈ Finset.Icc 1 L, ψ (z + d * (i : ℤ)) with hW
  set B : ℤ → ℂ := fun x => ∑ k ∈ Finset.range K, W (x + d * ((k * L : ℕ) : ℤ)) with hB
  set E : ℤ → ℂ := fun x => ∑ y ∈ Finset.Icc (K * L + 1) M, ψ (x + d * (y : ℤ)) with hE
  set S : ℤ → ℂ := fun x => ∑ y ∈ Finset.Icc 1 M, ψ (x + d * (y : ℤ)) with hS
  -- `K L ≤ M`
  have hKL : K * L ≤ M := by rw [hK]; exact Nat.div_mul_le_self M L
  -- the `L`-window sum vanishes off `symIcc Q`
  have hWvan : ∀ z : ℤ, z ∉ Work.Peluse.symIcc Q → W z = 0 := by
    intro z hz
    simp only [hW]
    refine Finset.sum_eq_zero (fun i hi => hsup _ ?_)
    intro hmem
    exact hz (mem_symIcc_of_add_mul_mem (d := d) (z := z) (Finset.mem_Icc.mp hi).2 hmem)
  -- the split of the `M`-window sum at `K*L`, and the block decomposition
  have hsplit : ∀ x : ℤ, S x
      = (∑ y ∈ Finset.Icc 1 (K * L), ψ (x + d * (y : ℤ))) + E x := by
    intro x
    simp only [hS, hE]
    rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) (K * L),
      ← Finset.Ico_add_one_right_eq_Icc (K * L + 1) M,
      ← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) M]
    exact (Finset.sum_Ico_consecutive (fun z : ℕ => ψ (x + d * (z : ℤ)))
      (by omega) (by omega)).symm
  have hblocks : ∀ x : ℤ, (∑ y ∈ Finset.Icc 1 (K * L), ψ (x + d * (y : ℤ))) = B x := by
    intro x
    simp only [hB]
    rw [← Work.Peluse.Peel.sum_range_Icc_blocks K L (fun z : ℕ => ψ (x + d * (z : ℤ)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hW]
    rw [← Work.Peluse.Peel.sum_Icc_add_const (fun z : ℕ => ψ (x + d * (z : ℤ))) (j * L) 1 L]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    push_cast
    ring
  have hSB : ∀ x : ℤ, S x = B x + E x := fun x => by rw [hsplit x, hblocks x]
  -- pointwise two-term reduction
  have hpoint : ∀ x : ℤ, ‖S x‖ ^ 2 ≤ 2 * ‖B x‖ ^ 2 + 2 * ‖E x‖ ^ 2 := by
    intro x
    have h1 : ‖S x‖ ≤ ‖B x‖ + ‖E x‖ := by
      rw [hSB x]
      exact norm_add_le _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [h2, sq_nonneg (‖B x‖ - ‖E x‖), norm_nonneg (B x), norm_nonneg (E x)]
  -- the main term: Cauchy–Schwarz over the blocks
  have hB1 : ∀ x : ℤ, ‖B x‖ ^ 2
      ≤ (K : ℝ) * ∑ k ∈ Finset.range K, ‖W (x + d * ((k * L : ℕ) : ℤ))‖ ^ 2 := by
    intro x
    have := Work.Peluse.Peel.norm_sum_sq_le_card_mul_sq (Finset.range K)
      (fun k => W (x + d * ((k * L : ℕ) : ℤ)))
    simpa [hB, Finset.card_range] using this
  have hB2 : (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
      ≤ (K : ℝ) * ∑ k ∈ Finset.range K,
          ∑ x ∈ Work.Peluse.symIcc N, ‖W (x + d * ((k * L : ℕ) : ℤ))‖ ^ 2 := by
    calc (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
        ≤ ∑ x ∈ Work.Peluse.symIcc N,
            (K : ℝ) * ∑ k ∈ Finset.range K,
              ‖W (x + d * ((k * L : ℕ) : ℤ))‖ ^ 2 :=
          Finset.sum_le_sum (fun x _ => hB1 x)
      _ = (K : ℝ) * ∑ x ∈ Work.Peluse.symIcc N,
            ∑ k ∈ Finset.range K, ‖W (x + d * ((k * L : ℕ) : ℤ))‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (K : ℝ) * ∑ k ∈ Finset.range K,
            ∑ x ∈ Work.Peluse.symIcc N, ‖W (x + d * ((k * L : ℕ) : ℤ))‖ ^ 2 := by
          rw [Finset.sum_comm]
  have hshift : ∀ k : ℕ, (∑ x ∈ Work.Peluse.symIcc N,
        ‖W (x + d * ((k * L : ℕ) : ℤ))‖ ^ 2) ≤ ∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2 := by
    intro k
    exact sum_symIcc_shift_le (a := fun z => ‖W z‖ ^ 2) (fun z => sq_nonneg _)
      (fun z hz => by rw [hWvan z hz]; simp) (d * ((k * L : ℕ) : ℤ))
  have hB3 : (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
      ≤ (K : ℝ) ^ 2 * ∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2 := by
    calc (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
        ≤ (K : ℝ) * ∑ k ∈ Finset.range K,
            ∑ x ∈ Work.Peluse.symIcc N, ‖W (x + d * ((k * L : ℕ) : ℤ))‖ ^ 2 := hB2
      _ ≤ (K : ℝ) * ∑ k ∈ Finset.range K, ∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun k _ => hshift k)
      _ = (K : ℝ) * ((K : ℝ) * ∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (K : ℝ) ^ 2 * ∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2 := by ring
  -- the excess: at most `L` terms of norm at most `1`
  have hcard : (Finset.Icc (K * L + 1) M).card ≤ L := by
    have hMlt : M < K * L + L := by
      have hmod := Nat.mod_lt M (by omega : 0 < L)
      have hdecomp : L * K + M % L = M := by
        rw [hK]; exact Nat.div_add_mod M L
      calc M = L * K + M % L := hdecomp.symm
        _ = K * L + M % L := by ring
        _ < K * L + L := Nat.add_lt_add_left hmod _
    rw [Nat.card_Icc]
    omega
  have hEbound : (∑ x ∈ Work.Peluse.symIcc N, ‖E x‖ ^ 2)
      ≤ (L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
    have hstep : ∀ x ∈ Work.Peluse.symIcc N, ‖E x‖ ^ 2 ≤ (L : ℝ) ^ 2 := by
      intro x _
      have h1 : ‖E x‖ ≤ (L : ℝ) := by
        have h1a : ‖E x‖ ≤ ∑ y ∈ Finset.Icc (K * L + 1) M, ‖ψ (x + d * (y : ℤ))‖ := by
          rw [hE]
          exact norm_sum_le _ _
        refine le_trans h1a ?_
        calc (∑ y ∈ Finset.Icc (K * L + 1) M, ‖ψ (x + d * (y : ℤ))‖)
            ≤ ∑ y ∈ Finset.Icc (K * L + 1) M, (1 : ℝ) := Finset.sum_le_sum (fun y _ => hbd _)
          _ = ((Finset.Icc (K * L + 1) M).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ (L : ℝ) := by exact_mod_cast hcard
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc (∑ x ∈ Work.Peluse.symIcc N, ‖E x‖ ^ 2)
        ≤ ∑ x ∈ Work.Peluse.symIcc N, (L : ℝ) ^ 2 := Finset.sum_le_sum hstep
      _ = (L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- assembly
  have hLHS : (∑ x ∈ Work.Peluse.symIcc N, ‖S x‖ ^ 2)
      ≤ 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
        + 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖E x‖ ^ 2) := by
    calc (∑ x ∈ Work.Peluse.symIcc N, ‖S x‖ ^ 2)
        ≤ ∑ x ∈ Work.Peluse.symIcc N, (2 * ‖B x‖ ^ 2 + 2 * ‖E x‖ ^ 2) :=
          Finset.sum_le_sum (fun x _ => hpoint x)
      _ = 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
            + 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖E x‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1' : 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
      ≤ 2 * (K : ℝ) ^ 2 * (∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2) := by
    calc 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖B x‖ ^ 2)
        ≤ 2 * ((K : ℝ) ^ 2 * ∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hB3 (by norm_num)
      _ = 2 * (K : ℝ) ^ 2 * (∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2) := by ring
  have h2' : 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖E x‖ ^ 2)
      ≤ 2 * (L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
    calc 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖E x‖ ^ 2)
        ≤ 2 * ((L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hEbound (by norm_num)
      _ = 2 * (L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by ring
  have hfinal : (∑ x ∈ Work.Peluse.symIcc N, ‖S x‖ ^ 2)
      ≤ 2 * (K : ℝ) ^ 2 * (∑ z ∈ Work.Peluse.symIcc Q, ‖W z‖ ^ 2)
        + 2 * (L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) :=
    le_trans hLHS (add_le_add h1' h2')
  simpa only [hK, hQ, hW, hS] using hfinal

end Work.Peluse.Track
