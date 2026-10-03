import Mathlib
import Submission.Work.Analysis.Hilbert.lattice_exp_defs

/-!
# The `τ`-averaging identity: the shifted lattice conditional expectations average to the
triangular smoothing

This file proves `lattice_exp_average`: for `k ≤ K`, `g : ℤ → ℂ` and `n : ℤ`,

`∑_{τ ∈ [0, 2^K)} latticeExp k τ g n = 2^K · triConv k g n`,

i.e. *the average of the `τ`-shifted dyadic conditional expectations `E_k^τ g` over a complete
residue system of shifts is the triangular (Fejér) smoothing of `g`*.

Since for fixed `τ` the family `(latticeExp k τ g)_k` is a reverse martingale (the σ-algebras
`latticeSpan k τ` are *decreasing* in `k`, so the reversed family is a conditional-expectation
martingale), and `varPathC` is convex, this identity is exactly what is needed to write the walk
`k ↦ triConv k g` as a convex combination of martingale walks, to which Lépingle's inequality
applies.

## Structure of the proof

The key ingredient is the **cyclic sum**, `sum_Ico_emod_cycle`: for any `m > 0`, summing
`Φ (x % m)` over any `m` consecutive integers gives the same as summing over `[0, m)` (the sum is
invariant under `n ↦ n+1`, and at `n = 0` it is the obvious sum).  Its dyadic version
`sum_Ico_emod_pow` says that over a block of `2^{k+d}` consecutive integers, `x % 2^k` runs
through `2^d` complete cycles.

This reduces the left-hand side to the elementary double sum
`∑_{j < 2^k} ∑_{e < 2^k} g (n-j+e)`, and the latter is `2^{2k} · triConv k g n` — which is
exactly the content of the (already proved) `shiftExp_average`, since substituting `d = e - τ` in
`shiftExp` turns it into the same double sum.
-/

open Finset
open scoped BigOperators ENNReal

namespace Work.Analysis.Hilbert

noncomputable section

/-! ## The cyclic sum over a full period -/

/-- **The cyclic sum**: summing `Φ (x % m)` over any `m` consecutive integers `[n, n+m)` gives the
same as summing over `[0, m)`. -/
lemma sum_Ico_emod_cycle (m : ℕ) (Φ : ℤ → ℂ) (n : ℤ) :
    ∑ x ∈ Finset.Ico n (n + (m:ℤ)), Φ (x % (m:ℤ)) = ∑ j ∈ Finset.range m, Φ (j:ℤ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hmz : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
    have hstep : ∀ n : ℤ,
        ∑ x ∈ Finset.Ico (n+1) (n+1 + (m:ℤ)), Φ (x % (m:ℤ))
          = ∑ x ∈ Finset.Ico n (n + (m:ℤ)), Φ (x % (m:ℤ)) := by
      intro n
      have hsplit1 : Finset.Ico n (n + (m:ℤ))
          = insert n (Finset.Ico (n+1) (n + (m:ℤ))) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hsplit2 : Finset.Ico (n+1) (n+1 + (m:ℤ))
          = insert (n + (m:ℤ)) (Finset.Ico (n+1) (n + (m:ℤ))) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnot1 : n ∉ Finset.Ico (n+1) (n + (m:ℤ)) := by simp [Finset.mem_Ico]
      have hnot2 : (n + (m:ℤ)) ∉ Finset.Ico (n+1) (n + (m:ℤ)) := by simp [Finset.mem_Ico]
      rw [hsplit1, hsplit2, Finset.sum_insert hnot2, Finset.sum_insert hnot1]
      have hmod : (n + (m:ℤ)) % (m:ℤ) = n % (m:ℤ) := by
        rw [Int.add_emod, Int.emod_self, add_zero]
        exact Int.emod_eq_of_lt (Int.emod_nonneg n (ne_of_gt hmz)) (Int.emod_lt_of_pos n hmz)
      rw [hmod]
    have hbase : ∑ x ∈ Finset.Ico (0:ℤ) ((0:ℤ) + (m:ℤ)), Φ (x % (m:ℤ))
        = ∑ j ∈ Finset.range m, Φ (j:ℤ) := by
      rw [zero_add]
      refine (Finset.sum_nbij' (fun j : ℕ => (j:ℤ)) (fun b : ℤ => b.toNat) ?_ ?_ ?_ ?_ ?_).symm
      · intro j hj
        exact Finset.mem_Ico.mpr ⟨by positivity, by exact_mod_cast (Finset.mem_range.mp hj)⟩
      · intro b hb
        exact Finset.mem_range.mpr (by
          have := (Finset.mem_Ico.mp hb).2
          omega)
      · intro j hj
        exact Nat.cast_injective (Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ (j:ℤ)))
      · intro b hb
        exact Int.toNat_of_nonneg (Finset.mem_Ico.mp hb).1
      · intro j hj
        rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (Finset.mem_range.mp hj))]
    rcases lt_or_ge n 0 with hn | hn
    · refine Int.leInductionDown (motive := fun n _ =>
        ∑ x ∈ Finset.Ico n (n + (m:ℤ)), Φ (x % (m:ℤ)) = ∑ j ∈ Finset.range m, Φ (j:ℤ)) hbase ?_
        n (le_of_lt hn)
      intro n _ ih
      have hs := hstep (n - 1)
      rw [show n - 1 + 1 = n by ring] at hs
      exact hs.symm.trans ih
    · refine Int.leInduction (motive := fun n _ =>
        ∑ x ∈ Finset.Ico n (n + (m:ℤ)), Φ (x % (m:ℤ)) = ∑ j ∈ Finset.range m, Φ (j:ℤ)) hbase
        (fun n _ ih => (hstep n).trans ih) n hn

/-- **The cyclic sum over a dyadic block**: for a block of `2^{k+d}` consecutive integers, `x % 2^k`
runs through exactly `2^d` complete residue systems. -/
lemma sum_Ico_emod_pow (k : ℕ) (Φ : ℤ → ℂ) :
    ∀ (d : ℕ) (n : ℤ), ∑ x ∈ Finset.Ico n (n + (2:ℤ)^(k+d)), Φ (x % (2:ℤ)^k)
      = ((2:ℂ)^d) * ∑ j ∈ Finset.range (2^k), Φ (j:ℤ) := by
  intro d
  induction d with
  | zero =>
      intro n
      simp only [Nat.add_zero, pow_zero, one_mul]
      exact sum_Ico_emod_cycle (2^k) Φ n
  | succ d ih =>
      intro n
      have h2 : (2:ℤ)^(k+(d+1)) = (2:ℤ)^(k+d) + (2:ℤ)^(k+d) := by
        rw [show k + (d+1) = (k+d)+1 by ring, pow_succ]; ring
      have hcons : Finset.Ico n (n + (2:ℤ)^(k+(d+1)))
          = Finset.Ico n (n + (2:ℤ)^(k+d))
            ∪ Finset.Ico (n + (2:ℤ)^(k+d)) (n + ((2:ℤ)^(k+d) + (2:ℤ)^(k+d))) := by
        rw [h2, Finset.Ico_union_Ico_eq_Ico] <;>
          linarith [pow_nonneg (by norm_num : (0:ℤ) ≤ 2) (k+d)]
      rw [hcons, Finset.sum_union]
      · rw [ih n, ← add_assoc, ih (n + (2:ℤ)^(k+d))]
        have : ((2:ℂ)^(d+1)) = ((2:ℂ)^d) + ((2:ℂ)^d) := by rw [pow_succ]; ring
        rw [this]; ring
      · refine Finset.disjoint_left.mpr fun x hx1 hx2 => ?_
        rw [Finset.mem_Ico] at hx1 hx2
        omega


/-! ## Converting `range` sums into `Ico` sums on `ℤ` -/

lemma sum_range_eq_sum_Ico {M : Type*} [AddCommMonoid M] (m : ℕ) (ψ : ℤ → M) :
    ∑ j ∈ Finset.range m, ψ (j:ℤ) = ∑ j ∈ Finset.Ico (0:ℤ) (m:ℤ), ψ j := by
  refine Finset.sum_nbij' (fun j : ℕ => (j:ℤ)) (fun b : ℤ => b.toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_Ico.mpr ⟨by positivity, by exact_mod_cast (Finset.mem_range.mp hj)⟩
  · intro b hb
    obtain ⟨h0, h1⟩ := Finset.mem_Ico.mp hb
    exact Finset.mem_range.mpr ((Int.toNat_lt h0).mpr h1)
  · intro j hj
    exact Nat.cast_injective (Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ (j:ℤ)))
  · intro b hb
    exact Int.toNat_of_nonneg (Finset.mem_Ico.mp hb).1
  · intro j hj
    rfl

/-! ## The double sum is `2^{2k}` times the triangular smoothing -/

/-- The `τ`-shifted conditional expectation as a sum over the *canonical* interval `[0, 2^k)`:
`shiftExp k τ g n = 2^{-k} ∑_{e ∈ [0,2^k)} g (n - e + τ)`. -/
lemma shiftExp_eq_Ico_sum (k : ℕ) (τ : ℤ) (g : ℤ → ℂ) (n : ℤ) :
    shiftExp k τ g n
      = ((2:ℂ)^k)⁻¹ * ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - e + τ) := by
  rw [shiftExp]
  refine congrArg (((2:ℂ)^k)⁻¹ * ·) ?_
  have key := Finset.sum_Ico_add' (fun d => g (n - d)) (0:ℤ) ((2:ℤ)^k) (-τ)
  simp only [zero_add] at key
  rw [show -τ + (2:ℤ)^k = ((2:ℤ)^k + -τ) by ring]
  rw [← key]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  ring

/-- **The double sum equals `2^{2k}` times the triangular smoothing**, via the already proved
`shiftExp_average`. -/
lemma sum_Ico_Ico_eq_triConv (k : ℕ) (g : ℤ → ℂ) (n : ℤ) :
    ∑ j ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - j + e)
      = ((2:ℂ)^k) * (((2:ℂ)^k) * triConv k g n) := by
  have h1 : ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftExp k τ g n
      = ((2:ℂ)^k) * triConv k g n := by
    simpa only [triConv] using shiftExp_average k g n
  have h2 : ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftExp k τ g n
      = ((2:ℂ)^k)⁻¹ * ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k),
          ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - e + τ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => shiftExp_eq_Ico_sum k τ g n
  have hk : ((2:ℂ)^k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hX : ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - e + τ)
      = ((2:ℂ)^k) * (((2:ℂ)^k) * triConv k g n) := by
    have h4 : ((2:ℂ)^k) * (((2:ℂ)^k)⁻¹ * (∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k),
          ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - e + τ)))
        = ((2:ℂ)^k) * (((2:ℂ)^k) * triConv k g n) := by
      rw [← h2]
      exact congrArg (((2:ℂ)^k) * ·) h1
    have h5 : ((2:ℂ)^k) * (((2:ℂ)^k)⁻¹ * (∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k),
          ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - e + τ)))
        = ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k),
            g (n - e + τ) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]
    exact h5.symm.trans h4
  calc ∑ j ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - j + e)
      = ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), ∑ e ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), g (n - e + τ) := by
        conv_lhs => rw [Finset.sum_comm]
    _ = ((2:ℂ)^k) * (((2:ℂ)^k) * triConv k g n) := hX

/-! ## The `τ`-averaging identity -/

/-- **The `τ`-averaging identity**: averaging the shifted lattice conditional expectations over a
complete residue system of shifts is the triangular smoothing. -/
theorem lattice_exp_average {k K : ℕ} (h : k ≤ K) (g : ℤ → ℂ) (n : ℤ) :
    ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^K), latticeExp k τ g n
      = ((2:ℂ)^K) * triConv k g n := by
  obtain ⟨d, rfl⟩ : ∃ d, K = k + d := ⟨K - k, by omega⟩
  have hstep1 : ∀ τ : ℤ, latticeExp k τ g n
      = ((2:ℂ)^k)⁻¹ * ∑ e ∈ Finset.range (2^k), g (n - (n + τ) % (2:ℤ)^k + (e:ℤ)) := by
    intro τ
    rw [latticeExp]
    refine congrArg (((2:ℂ)^k)⁻¹ * ·) ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    have hb := sub_latticeBase k τ n
    omega
  have hconv : ∑ e ∈ Finset.range (2^k), ∑ j ∈ Finset.range (2^k),
        g (n - (j:ℤ) + (e:ℤ)) = ((2:ℂ)^k) * (((2:ℂ)^k) * triConv k g n) := by
    rw [sum_range_eq_sum_Ico (2^k) (fun e => ∑ j ∈ Finset.range (2^k), g (n - j + e))]
    rw [Finset.sum_congr rfl (fun e _ => sum_range_eq_sum_Ico (2^k) (fun j => g (n - j + e)))]
    push_cast
    rw [Finset.sum_comm]
    exact sum_Ico_Ico_eq_triConv k g n
  have hkr : ((2:ℂ)^k) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^(k+d)), latticeExp k τ g n
      = ((2:ℂ)^k)⁻¹ * ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^(k+d)),
          ∑ e ∈ Finset.range (2^k), g (n - (n + τ) % (2:ℤ)^k + (e:ℤ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => hstep1 τ
    _ = ((2:ℂ)^k)⁻¹ * ∑ e ∈ Finset.range (2^k),
          ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^(k+d)),
            g (n - (n + τ) % (2:ℤ)^k + (e:ℤ)) := by
        rw [Finset.sum_comm]
    _ = ((2:ℂ)^k)⁻¹ * ∑ e ∈ Finset.range (2^k),
          ∑ x ∈ Finset.Ico n (n + (2:ℤ)^(k+d)), g (n - x % (2:ℤ)^k + (e:ℤ)) := by
        congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        have hsub := Finset.sum_Ico_add' (fun x : ℤ => g (n - x % (2:ℤ)^k + (e:ℤ)))
          (0:ℤ) ((2:ℤ)^(k+d)) n
        simpa only [zero_add, add_zero, add_comm] using hsub
    _ = ((2:ℂ)^k)⁻¹ * ∑ e ∈ Finset.range (2^k),
          ((2:ℂ)^d * ∑ j ∈ Finset.range (2^k), g (n - (j:ℤ) + (e:ℤ))) := by
        congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        exact sum_Ico_emod_pow k (fun y => g (n - y + (e:ℤ))) d n
    _ = ((2:ℂ)^k)⁻¹ * ((2:ℂ)^d) * ∑ e ∈ Finset.range (2^k),
          ∑ j ∈ Finset.range (2^k), g (n - (j:ℤ) + (e:ℤ)) := by
        rw [← Finset.mul_sum]
        ring
    _ = ((2:ℂ)^(k+d)) * triConv k g n := by
        rw [hconv, pow_add]
        field_simp <;> ring_nf

end

end Work.Analysis.Hilbert
