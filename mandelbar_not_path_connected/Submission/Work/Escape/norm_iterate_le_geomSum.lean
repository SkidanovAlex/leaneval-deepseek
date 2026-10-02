import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Geometric-sum bound for the iterates of a monic-growth map

For a map `f` with `MonicGrowth f d A` (i.e. `‖z‖^d - A ≤ ‖f z‖ ≤ ‖z‖^d + A`), degree `d ≥ 2`,
and a radius `B ≥ 2` with `A ≤ B`, the orbit of every `z` with `‖z‖ ≤ B` stays below
`B ^ (1 + d + d^2 + ⋯ + d^n)`.

This is the "everything stays finite" half of the escape dichotomy: it is the crude a priori
bound that makes `K_f` (and hence the filled tricorn) a bounded set, and it is the input used to
show that the partial Green functions are uniformly bounded on compacts.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-- The geometric sum `1 + d + ⋯ + d^{n+1}` satisfies the recursion
`S (n+1) = d * S n + 1`. -/
theorem geomSum_succ (d n : ℕ) :
    (∑ i ∈ Finset.range (n + 2), d ^ i) = d * (∑ i ∈ Finset.range (n + 1), d ^ i) + 1 := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have : (∑ k ∈ Finset.range (n + 1), d ^ (k + 1))
      = d * ∑ k ∈ Finset.range (n + 1), d ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_succ']
  rw [this]

theorem norm_iterate_le_geomSum (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {B : ℝ} (hB : 2 ≤ B) {z : ℂ} (hz : ‖z‖ ≤ B) (hAB : A ≤ B) (n : ℕ) :
    ‖(f^[n]) z‖ ≤ B ^ (∑ i ∈ Finset.range (n + 1), d ^ i) := by
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hd1 : 1 ≤ d := by omega
  induction n with
  | zero =>
      have h0 : ∑ i ∈ Finset.range (0 + 1), d ^ i = 1 := by simp
      rw [h0, pow_one]
      simpa using hz
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      -- the exponent produced by the induction step
      have hE1 : 1 ≤ ∑ i ∈ Finset.range (k + 1), d ^ i := by
        have hmem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
        have := Finset.single_le_sum (s := Finset.range (k + 1)) (f := fun i => d ^ i)
            (fun i _ => Nat.zero_le _) hmem
        simpa using this
      have hk : 1 ≤ (∑ i ∈ Finset.range (k + 1), d ^ i) * d := by
        simpa using Nat.mul_le_mul hE1 hd1
      have hBEd : B ≤ B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) := by
        calc B = B ^ 1 := (pow_one B).symm
          _ ≤ B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) := pow_le_pow_right₀ hB1 hk
      have hBm1 : (1 : ℝ) ≤ B - 1 := by linarith
      have hPnn : (0 : ℝ) ≤ B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) := pow_nonneg hB0 _
      -- `B ≤ (B ^ E) * (B - 1)`; this is the slack that absorbs the additive constant `A`
      have h1 : B ≤ B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) * (B - 1) := by
        calc B = B * 1 := (mul_one B).symm
          _ ≤ B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) * (B - 1) :=
                mul_le_mul hBEd hBm1 zero_le_one hPnn
      have hsucc : ∑ i ∈ Finset.range (k + 1 + 1), d ^ i
          = d * (∑ i ∈ Finset.range (k + 1), d ^ i) + 1 := geomSum_succ d k
      calc ‖f ((f^[k]) z)‖
          ≤ ‖(f^[k]) z‖ ^ d + A := h.norm_le _
        _ ≤ (B ^ (∑ i ∈ Finset.range (k + 1), d ^ i)) ^ d + A :=
              add_le_add_left (pow_le_pow_left₀ (norm_nonneg _) ih d) A
        _ = B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) + A := by rw [pow_mul]
        _ ≤ B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) * B := by
              have hA' : A ≤ B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) * (B - 1) :=
                hAB.trans h1
              have hPB : B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) * B
                  = B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) * (B - 1)
                    + B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d) := by ring
              linarith [hA', hPB]
        _ = B ^ ((∑ i ∈ Finset.range (k + 1), d ^ i) * d + 1) := by rw [pow_succ]
        _ = B ^ (∑ i ∈ Finset.range (k + 1 + 1), d ^ i) := by
              rw [hsucc]; congr 1; ring

end Work.Escape
