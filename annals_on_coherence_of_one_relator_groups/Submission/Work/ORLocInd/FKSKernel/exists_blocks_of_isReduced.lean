import Mathlib

/-!
# Block decomposition of a reduced word

For a reduced word `L : List (S × Bool)` over a group `S` (viewed as the generating set of a free
group), the maximal runs of equal letters can be grouped into *blocks* `(x, k) : S × ℤ` carrying a
nonzero integer exponent `k`.  Adjacent blocks carry distinct letters, the product of the blocks
evaluated in `FreeGroup S` is `FreeGroup.mk L`, and the block list is empty exactly when `L` is.

This is the combinatorial input behind the Freiheitssatz-style kernel computations: it turns a word
in the free group into a chain of powers of the generators.
-/

namespace Work.ORLocInd.FKSKernel

universe u

/-- The integer sign of a `Bool`: `true ↦ 1`, `false ↦ -1`. -/
def eb (b : Bool) : ℤ := if b then 1 else -1

@[simp] lemma eb_true : eb true = 1 := rfl
@[simp] lemma eb_false : eb false = -1 := rfl

lemma eb_ne_zero (b : Bool) : eb b ≠ 0 := by cases b <;> simp [eb]

variable {S : Type u}

/-- Accumulate the maximal run of letters equal to `x`, emitting blocks `(letter, exponent)`.

`blk x k t` treats `x` as the letter of an already started block with current exponent `k`, and
continues consuming `t`: while the next letter agrees with `x` the exponent is incremented
accordingly, and at the first letter different from `x` the finished block `(x, k)` is emitted and a
new block is started. -/
noncomputable def blk [DecidableEq S] (x : S) (k : ℤ) : List (S × Bool) → List (S × ℤ)
  | [] => [(x, k)]
  | (y, c) :: t => if x = y then blk x (k + eb c) t else (x, k) :: blk y (eb c) t

/-- The output of `blk` is always nonempty, and its first block carries the starting letter. -/
lemma blk_head [DecidableEq S] (t : List (S × Bool)) (x : S) (k : ℤ) :
    ∃ (k' : ℤ) (rest : List (S × ℤ)), blk x k t = (x, k') :: rest := by
  induction t generalizing x k with
  | nil => exact ⟨k, [], rfl⟩
  | cons hd tl ih =>
      obtain ⟨y, c⟩ := hd
      by_cases h : x = y
      · simp only [blk, if_pos h]; exact ih x (k + eb c)
      · simp only [blk, if_neg h]; exact ⟨k, blk y (eb c) tl, rfl⟩

/-- Consecutive blocks produced by `blk` carry distinct letters. -/
lemma blk_chain [DecidableEq S] (t : List (S × Bool)) (x : S) (k : ℤ) :
    (blk x k t).IsChain (fun a b : S × ℤ => a.1 ≠ b.1) := by
  induction t generalizing x k with
  | nil => simp only [blk]; exact List.isChain_singleton _
  | cons hd tl ih =>
      obtain ⟨y, c⟩ := hd
      by_cases h : x = y
      · simp only [blk, if_pos h]; exact ih x (k + eb c)
      · simp only [blk, if_neg h]
        obtain ⟨k', rest, hk'⟩ := blk_head tl y (eb c)
        rw [hk']
        refine List.IsChain.cons (by rw [← hk']; exact ih y (eb c)) ?_
        intro z hz
        simp only [List.head?_cons, Option.mem_some_iff] at hz
        subst hz
        exact h

/-- A single letter evaluates to the corresponding power of a free generator. -/
lemma mk_singleton (x : S) (b : Bool) :
    FreeGroup.mk (α := S) [(x, b)] = FreeGroup.of x ^ eb b := by
  cases b
  · rw [eb_false, zpow_neg_one, FreeGroup.of, FreeGroup.inv_mk]; rfl
  · rw [eb_true, zpow_one]; rfl

/-- Splitting off the head of a word, evaluated in the free group. -/
lemma mk_cons (x : S) (b : Bool) (t : List (S × Bool)) :
    FreeGroup.mk ((x, b) :: t) = FreeGroup.of x ^ eb b * FreeGroup.mk t := by
  have h1 : FreeGroup.mk ((x, b) :: t) = FreeGroup.mk ([(x, b)] ++ t) := rfl
  rw [h1, ← FreeGroup.mul_mk, mk_singleton]

/-- The product of the blocks of `blk x k t`, evaluated in the free group, is the free-group
element `of x ^ k` followed by the image of the remaining word `t`. -/
lemma blk_prod [DecidableEq S] (t : List (S × Bool)) (x : S) (k : ℤ) :
    FreeGroup.of x ^ k * FreeGroup.mk t =
      ((blk x k t).map (fun c : S × ℤ => FreeGroup.of c.1 ^ c.2)).prod := by
  induction t generalizing x k with
  | nil =>
      simp only [blk, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        ← FreeGroup.one_eq_mk, mul_one]
  | cons hd tl ih =>
      obtain ⟨y, c⟩ := hd
      by_cases h : x = y
      · simp only [blk, if_pos h]
        rw [mk_cons, ← h]
        rw [← mul_assoc, ← zpow_add]
        exact ih x (k + eb c)
      · simp only [blk, if_neg h, List.map_cons, List.prod_cons]
        rw [mk_cons, ih y (eb c)]

/-- The exponents of all blocks of `blk` are nonzero, provided the block has been started by a
previous letter with the same value and sign, so that all letters accumulated into the block are
equal (which is exactly what reducedness guarantees). -/
lemma blk_second_ne_zero [DecidableEq S] (t : List (S × Bool)) (x : S) (b : Bool) (n : ℕ)
    (hred : FreeGroup.IsReduced ((x, b) :: t)) :
    ∀ c ∈ blk x (eb b * ((n : ℤ) + 1)) t, c.2 ≠ 0 := by
  induction t generalizing x b n with
  | nil =>
      intro c hc
      simp only [blk, List.mem_singleton] at hc
      subst hc
      exact mul_ne_zero (eb_ne_zero b) (by omega)
  | cons hd tl ih =>
      obtain ⟨y, c⟩ := hd
      intro d hd_mem
      obtain ⟨hb, hred'⟩ := FreeGroup.isReduced_cons_cons.mp hred
      by_cases h : x = y
      · simp only [blk, if_pos h] at hd_mem
        have hbc : c = b := (hb h).symm
        have hK : eb b * ((n : ℤ) + 1) + eb c = eb b * (((n + 1 : ℕ) : ℤ) + 1) := by
          rw [hbc]; push_cast; ring
        rw [hK] at hd_mem
        have hred'' : FreeGroup.IsReduced ((x, b) :: tl) := by
          have : (x, b) = (y, c) := by simp only [Prod.mk.injEq]; exact ⟨h, hb h⟩
          rw [this]; exact hred'
        exact ih x b (n + 1) hred'' d hd_mem
      · simp only [blk, if_neg h, List.mem_cons] at hd_mem
        rcases hd_mem with hd_eq | hd_mem'
        · rw [hd_eq]
          show eb b * ((n : ℤ) + 1) ≠ 0
          exact mul_ne_zero (eb_ne_zero b) (by omega)
        · exact ih y c 0 hred' d (by simpa using hd_mem')

theorem exists_blocks_of_isReduced {S : Type u} [Group S] (L : List (S × Bool))
    (hL : FreeGroup.IsReduced L) :
    ∃ M : List (S × ℤ), (∀ c ∈ M, c.2 ≠ 0) ∧ M.IsChain (fun x y => x.1 ≠ y.1) ∧
      FreeGroup.mk L = (M.map (fun c => FreeGroup.of c.1 ^ c.2)).prod ∧ (M = [] ↔ L = []) := by
  classical
  cases L with
  | nil => exact ⟨[], by simp, List.isChain_nil, rfl, by simp⟩
  | cons hd t =>
      obtain ⟨x, b⟩ := hd
      refine ⟨blk x (eb b) t, ?_, ?_, ?_, ?_⟩
      · intro c hc
        exact blk_second_ne_zero t x b 0 hL c (by simpa using hc)
      · exact blk_chain t x (eb b)
      · rw [mk_cons]; exact blk_prod t x (eb b)
      · constructor
        · intro h
          obtain ⟨k', rest, hk'⟩ := blk_head t x (eb b)
          exact absurd (hk'.symm.trans h) (by simp)
        · intro h
          exact absurd h (by simp)

end Work.ORLocInd.FKSKernel
