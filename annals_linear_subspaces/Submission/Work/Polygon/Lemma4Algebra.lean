import Mathlib
import Submission.Work.Polygon.DiscreteConvex

/-!
# Lemma 4 of de Saxcé §3 — the block algebra (first connection)

The paper's Lemma 4 reads
`⟨ċ_t, c_t⟩ = −(1/ℓ + 1/(d−ℓ)) · Σ_{s=0}^{r} (ℓ_{s+1} − ℓ_s) · Λ_{j_s+1}`
where `c_t` is the Grayson polygon of the flow lattice `a_t s_x ℤᵈ`, `0 = j₀ < … < j_{r+1} = d`
its angular points (slopes `Λ_i = c(i) − c(i−1)` constant on each block `(j_s, j_{s+1}]`),
and `ℓ_s = dim(V_{j_s} ∩ L)` counts how many of the `j_s` flag directions are contracted.

Its proof has three moves, of which the FIRST and the THIRD are pure block algebra over
the discrete functions involved, and are independent of the flow/polygon machinery:

1. **Regroup** (`block_regroup`): for *any* functions `u, c : ℕ → ℝ` and any breakpoint
   sequence `0 = j₀ ≤ … ≤ j_{r+1} = d` on which `c` has constant slopes `Λ s`,
   `Σ_{i<d} (u(i+1)−u(i))·(c(i+1)−c(i)) = Σ_{s ≤ r} (u(j_{s+1}) − u(j_s))·Λ s`.
   (This is the identity `⟨ċ,c⟩ = Σ_s (ċ(j_{s+1})−ċ(j_s))Λ_{j_s+1}` with `u := ċ_t`,
   `c := c_t`; it needs no convexity and no differentiability — only the block structure.)
2. Substitute the flow-derivative formula `u(j_{s+1}) − u(j_s) = (j_{s+1}−j_s)·A − (ℓ_{s+1}−ℓ_s)·B`
   and separate the sums (`lemma4_algebraic`).
3. **Slope-total of the polygon** (`block_sum_weighted`): `Σ_s (j_{s+1}−j_s)·Λ s =
   c(d) − c(0)`, which is `0` when `c(0) = c(d) = 0` — this is `grayson_slopes_sum_zero`
   of `DiscreteConvex`, made concrete on the block side (each block contributes
   `(j_{s+1}−j_s)` slopes, all equal to `Λ s`).

The result (`lemma4_algebraic`): for any `A, B : ℝ`,
`⟨u,c⟩ = (c d − c 0)·A − B·Σ_s (ℓ_{s+1}−ℓ_s)·Λ s`, so with `c 0 = c d = 0` the first
term vanishes and one obtains the shape of Lemma 4's conclusion; instantiating
`u := ċ_t`, `c := c_t`, `A := 1/(d−ℓ₀)`, `B := 1/ℓ₀ + 1/(d−ℓ₀)` and `ℓ_s` from the flag
is the remaining (flow-level) instantiation, to be done once the flow-lattice polygon
and its derivative exist.

All declarations are Mathlib-only apart from the `DiscreteConvex` import.
-/

open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace Submission.Polygon

/-- Telescope of the slopes over an interval `[p, q)`: `Σ_{i∈Ico p q} dslope u i = u q − u p`. -/
lemma sum_Ico_dslope_eq_sub (u : ℕ → ℝ) {p q : ℕ} (hpq : p ≤ q) :
    (∑ i ∈ Finset.Ico p q, dslope u i) = u q - u p := by
  rw [Finset.sum_Ico_eq_sub (fun i : ℕ => dslope u i) hpq]
  rw [telescope u q, telescope u p]
  ring

/-- **Atomic block contribution** (`Lemma 4, move 1, per block`): if `c` has constant
slope `Λ` on `[p, q)` then the inner product of `u` and `c` restricted to the block is
`(u q − u p)·Λ`. -/
lemma block_inner (u c : ℕ → ℝ) {p q : ℕ} (hpq : p ≤ q) (Λ : ℝ)
    (hΛ : ∀ i : ℕ, p ≤ i → i < q → dslope c i = Λ) :
    (∑ i ∈ Finset.Ico p q, dslope u i * dslope c i) = (u q - u p) * Λ := by
  calc
    (∑ i ∈ Finset.Ico p q, dslope u i * dslope c i)
        = (∑ i ∈ Finset.Ico p q, dslope u i * Λ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hΛ i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2]
    _ = (∑ i ∈ Finset.Ico p q, dslope u i) * Λ := by
            rw [← Finset.sum_mul]
    _ = (u q - u p) * Λ := by
            rw [sum_Ico_dslope_eq_sub u hpq]

/-- A consecutive block partition `[j₀, j₁) ∪ … ∪ [j_r, j_{r+1})` of `[0, j_{r+1})`
splits the sum over the range accordingly. -/
lemma sum_Ico_consecutive {r : ℕ} (j : ℕ → ℕ) (f : ℕ → ℝ)
    (hj0 : j 0 = 0) (hmono : ∀ s : ℕ, s ≤ r → j s ≤ j (s + 1)) :
    (∑ i ∈ Finset.range (j (r + 1)), f i) =
      ∑ s ∈ Finset.range (r + 1), ∑ i ∈ Finset.Ico (j s) (j (s + 1)), f i := by
  let T : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (j k), f i
  have hblocks : ∀ s : ℕ, s ≤ r →
      (∑ i ∈ Finset.Ico (j s) (j (s + 1)), f i) = T (s + 1) - T s := by
    intro s hs
    dsimp [T]
    exact Finset.sum_Ico_eq_sub f (hmono s hs)
  calc
    (∑ i ∈ Finset.range (j (r + 1)), f i) = T (r + 1) := by dsimp [T]
    _ = T (r + 1) - T 0 := by
          have hT0 : T 0 = 0 := by
            dsimp [T]
            rw [hj0]
            simp
          rw [hT0]
          ring
    _ = ∑ s ∈ Finset.range (r + 1), (T (s + 1) - T s) := by
          exact (Finset.sum_range_sub (f := T) (n := r + 1)).symm
    _ = ∑ s ∈ Finset.range (r + 1), ∑ i ∈ Finset.Ico (j s) (j (s + 1)), f i := by
          apply Finset.sum_congr rfl
          intro s hs
          exact (hblocks s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))).symm

/-- **Regroup over the blocks** (`Lemma 4, move 1`): if `c` has constant slope `Λ s` on
each block `(j_s, j_{s+1}]` of the partition `0 = j₀ ≤ … ≤ j_{r+1} = d`, then
`Σ_{i<d} dslope u i · dslope c i = Σ_{s ≤ r} (u(j_{s+1}) − u(j_s))·Λ s`
(with `u := ċ_t`, `c := c_t` this is the first displayed identity of Lemma 4's proof). -/
lemma block_regroup {d r : ℕ} (u c : ℕ → ℝ) (j : ℕ → ℕ) (Λ : ℕ → ℝ)
    (hj0 : j 0 = 0) (hjd : j (r + 1) = d)
    (hmono : ∀ s : ℕ, s ≤ r → j s ≤ j (s + 1))
    (hΛ : ∀ s : ℕ, s ≤ r → ∀ i : ℕ, j s ≤ i → i < j (s + 1) → dslope c i = Λ s) :
    (∑ i ∈ Finset.range d, dslope u i * dslope c i) =
      ∑ s ∈ Finset.range (r + 1), (u (j (s + 1)) - u (j s)) * Λ s := by
  have hpart : (∑ i ∈ Finset.range (j (r + 1)), dslope u i * dslope c i) =
      ∑ s ∈ Finset.range (r + 1),
        ∑ i ∈ Finset.Ico (j s) (j (s + 1)), dslope u i * dslope c i :=
    sum_Ico_consecutive j (fun i => dslope u i * dslope c i) hj0 hmono
  rw [hjd] at hpart
  rw [hpart]
  apply Finset.sum_congr rfl
  intro s hs
  have hs_le : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  exact block_inner u c (hmono s hs_le) (Λ s) (hΛ s hs_le)

/-- **Slope-total blockwise** (`Lemma 4, move 3`): with the block structure of `block_regroup`,
`Σ_s (j_{s+1} − j_s)·Λ s = c d − c 0` (each block contributes `j_{s+1} − j_s` slopes, all
equal to `Λ s`).  For the Grayson polygon `c(0) = c(d) = 0` (the `g 0 = g d = 0` data case of
`grayson_slopes_sum_zero`), this total is `0`. -/
lemma block_sum_weighted {d r : ℕ} (c : ℕ → ℝ) (j : ℕ → ℕ) (Λ : ℕ → ℝ)
    (hj0 : j 0 = 0) (hjd : j (r + 1) = d)
    (hmono : ∀ s : ℕ, s ≤ r → j s ≤ j (s + 1))
    (hΛ : ∀ s : ℕ, s ≤ r → ∀ i : ℕ, j s ≤ i → i < j (s + 1) → dslope c i = Λ s) :
    (∑ s ∈ Finset.range (r + 1), ((j (s + 1) - j s : ℕ) : ℝ) * Λ s) = c d - c 0 := by
  have hreg := block_regroup (u := fun i : ℕ => (i : ℝ)) (c := c) j Λ hj0 hjd hmono hΛ
  have hL : (∑ i ∈ Finset.range d, dslope (fun i : ℕ => (i : ℝ)) i * dslope c i) = c d - c 0 := by
    calc
      (∑ i ∈ Finset.range d, dslope (fun i : ℕ => (i : ℝ)) i * dslope c i)
          = ∑ i ∈ Finset.range d, dslope c i := by
              apply Finset.sum_congr rfl
              intro i hi
              have hd : dslope (fun j : ℕ => (j : ℝ)) i = 1 := by
                dsimp [dslope]
                rw [Nat.cast_add]
                ring
              rw [hd]
              ring
      _ = c d - c 0 := telescope c d
  have hR : (∑ s ∈ Finset.range (r + 1), ((j (s + 1) : ℝ) - (j s : ℝ)) * Λ s) =
      ∑ s ∈ Finset.range (r + 1), (((j (s + 1) - j s : ℕ) : ℝ)) * Λ s := by
    apply Finset.sum_congr rfl
    intro s hs
    have hs_le : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    congr 1
    exact (Nat.cast_sub (hmono s hs_le)).symm
  calc
    (∑ s ∈ Finset.range (r + 1), ((j (s + 1) - j s : ℕ) : ℝ) * Λ s)
        = ∑ s ∈ Finset.range (r + 1), ((j (s + 1) : ℝ) - (j s : ℝ)) * Λ s := hR.symm
    _ = ∑ i ∈ Finset.range d, dslope (fun i : ℕ => (i : ℝ)) i * dslope c i := hreg.symm
    _ = c d - c 0 := hL

/-- **Algebraic core of Lemma 4**: given the flow-derivative shape
`u(j_{s+1}) − u(j_s) = (j_{s+1} − j_s)·A − (ℓ_{s+1} − ℓ_s)·B` on the blocks,
`Σ_{i<d} dslope u i · dslope c i = (c d − c 0)·A − B·Σ_s (ℓ_{s+1} − ℓ_s)·Λ s`.
With `c 0 = c d = 0` (Grayson polygon of a unimodular flow lattice, via
`grayson_slopes_sum_zero`) the first term vanishes, giving the shape of Lemma 4's
conclusion `⟨ċ_t,c_t⟩ = −(1/ℓ₀+1/(d−ℓ₀))·Σ_s (ℓ_{s+1}−ℓ_s)·Λ_{j_s+1}` after the concrete
instantiation `u := ċ_t`, `A := 1/(d−ℓ₀)`, `B := 1/ℓ₀ + 1/(d−ℓ₀)`. -/
lemma lemma4_algebraic {d r : ℕ} (u c : ℕ → ℝ) (j : ℕ → ℕ) (ell : ℕ → ℝ) (Λ : ℕ → ℝ)
    (hj0 : j 0 = 0) (hjd : j (r + 1) = d)
    (hmono : ∀ s : ℕ, s ≤ r → j s ≤ j (s + 1))
    (hΛ : ∀ s : ℕ, s ≤ r → ∀ i : ℕ, j s ≤ i → i < j (s + 1) → dslope c i = Λ s)
    {A B : ℝ}
    (hder : ∀ s : ℕ, s ≤ r →
      u (j (s + 1)) - u (j s) = ((j (s + 1) - j s : ℕ) : ℝ) * A - (ell (s + 1) - ell s) * B) :
    (∑ i ∈ Finset.range d, dslope u i * dslope c i) =
      (c d - c 0) * A -
        (∑ s ∈ Finset.range (r + 1), (ell (s + 1) - ell s) * Λ s) * B := by
  have hreg := block_regroup u c j Λ hj0 hjd hmono hΛ
  have hw := block_sum_weighted c j Λ hj0 hjd hmono hΛ
  calc
    (∑ i ∈ Finset.range d, dslope u i * dslope c i)
        = ∑ s ∈ Finset.range (r + 1), (u (j (s + 1)) - u (j s)) * Λ s := hreg
    _ = ∑ s ∈ Finset.range (r + 1),
          (((j (s + 1) - j s : ℕ) : ℝ) * A - (ell (s + 1) - ell s) * B) * Λ s := by
          apply Finset.sum_congr rfl
          intro s hs
          have hs_le : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
          rw [hder s hs_le]
    _ = (∑ s ∈ Finset.range (r + 1), (((j (s + 1) - j s : ℕ) : ℝ)) * Λ s) * A -
        (∑ s ∈ Finset.range (r + 1), (ell (s + 1) - ell s) * Λ s) * B := by
          calc
            (∑ s ∈ Finset.range (r + 1),
                  (((j (s + 1) - j s : ℕ) : ℝ) * A - (ell (s + 1) - ell s) * B) * Λ s)
                = ∑ s ∈ Finset.range (r + 1),
                    ((((j (s + 1) - j s : ℕ) : ℝ) * Λ s) * A -
                      ((ell (s + 1) - ell s) * Λ s) * B) := by
                    apply Finset.sum_congr rfl
                    intro s hs
                    ring
            _ = (∑ s ∈ Finset.range (r + 1), (((j (s + 1) - j s : ℕ) : ℝ) * Λ s) * A) -
                (∑ s ∈ Finset.range (r + 1), ((ell (s + 1) - ell s) * Λ s) * B) := by
                    rw [Finset.sum_sub_distrib]
            _ = (∑ s ∈ Finset.range (r + 1), (((j (s + 1) - j s : ℕ) : ℝ)) * Λ s) * A -
                (∑ s ∈ Finset.range (r + 1), (ell (s + 1) - ell s) * Λ s) * B := by
                    rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ = (c d - c 0) * A -
        (∑ s ∈ Finset.range (r + 1), (ell (s + 1) - ell s) * Λ s) * B := by
          rw [hw]


/-- **Lemma 4, conclusion shape**: with the polygon endpoints vanishing (`c 0 = c d = 0`,
as forced for the Grayson polygon by the data function `g 0 = g d = 0` — see
`largestConvexMinorant_ends_zero` / `grayson_slopes_sum_zero`), the `A`-term of
`lemma4_algebraic` drops and one obtains exactly the shape of de Saxcé's Lemma 4:
`⟨ċ_t, c_t⟩ = −B·Σ_s (ℓ_{s+1} − ℓ_s)·Λ_{j_s+1}` (the concrete `B := 1/ℓ₀ + 1/(d−ℓ₀)`
instantiation and the flow-derivative hypothesis `hder` are the flow-level input). -/
lemma lemma4_ends_zero {d r : ℕ} (u c : ℕ → ℝ) (j : ℕ → ℕ) (ell : ℕ → ℝ) (Λ : ℕ → ℝ)
    (hj0 : j 0 = 0) (hjd : j (r + 1) = d)
    (hmono : ∀ s : ℕ, s ≤ r → j s ≤ j (s + 1))
    (hΛ : ∀ s : ℕ, s ≤ r → ∀ i : ℕ, j s ≤ i → i < j (s + 1) → dslope c i = Λ s)
    (hc0 : c 0 = 0) (hcd : c d = 0) {A B : ℝ}
    (hder : ∀ s : ℕ, s ≤ r →
      u (j (s + 1)) - u (j s) = ((j (s + 1) - j s : ℕ) : ℝ) * A - (ell (s + 1) - ell s) * B) :
    (∑ i ∈ Finset.range d, dslope u i * dslope c i) =
      - (∑ s ∈ Finset.range (r + 1), (ell (s + 1) - ell s) * Λ s) * B := by
  have h := lemma4_algebraic u c j ell Λ hj0 hjd hmono hΛ (A := A) (B := B) hder
  calc
    (∑ i ∈ Finset.range d, dslope u i * dslope c i) =
        (c d - c 0) * A - (∑ s ∈ Finset.range (r + 1), (ell (s + 1) - ell s) * Λ s) * B := h
    _ = - (∑ s ∈ Finset.range (r + 1), (ell (s + 1) - ell s) * Λ s) * B := by
          rw [hcd, hc0]
          ring

end Submission.Polygon
