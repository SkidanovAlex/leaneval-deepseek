import Mathlib
import Submission.Work.ANALYTIC.HaarBasisDefs

/-!
# `haar_expand`: the level-`N` expansion of a locally constant function

This is AN3's expansion theorem for the Haar/Schauder basis of `LC T = LocallyConstant ↥T ℤ`
(`Submission/Work/ANALYTIC/HaarDefs.lean`, REFS/03 §4): every function `g` which is invariant
under the level-`N` idempotent `e_N` is the finite combination

  `g x = g s₀ + ∑_{j : lvl j ≤ N} (phi T j g) * fCyl T j x`,

i.e. it lies in the span of the constant function `1` and the cylinders `fCyl T j` of level
`≤ N`, with the coordinates `phi T j g` given by the dual functionals of `HaarDefs.lean`.

Since `g` is `e_N`-invariant it is determined by its values on the finite set
`A N = range (e_N)`; the proof does not need that reduction explicitly, because the level-wise
identity below holds for *every* point `x`:

* `Haar.level_sum`: for each level `k`, the part of the expansion supported on the cylinder
  basis elements of level exactly `k` is a *telescoping* difference
  `g (e_k x) - g (chain x k)`, where the "chain" `chain x` is `s₀, e₀ x, e₁ x, …`;
* summing over `k ≤ N` (the decomposition `lvlFinset T N = ⋃_{k ≤ N} newFinset T k`) then
  telescopes to `g (e_N x) - g s₀`, and `g x = g (e_N x)` by hypothesis.

The mathematical content of `Haar.level_sum` is that the only basis element of level `k` which
can pair nontrivially with `x` is the one whose point `a_j` equals `e_k x` (there is at most one,
by injectivity of the enumeration `a`, and its "parent" is then `e_{k-1} x`); the cases where no
such `j` exists are exactly the cases where `e_k x` is fixed by `e_{k-1}`, so that the
difference already vanishes.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

attribute [local instance] Classical.propDecidable

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Haar

/-- The "chain" of a point: `chain x 0 = s₀` and `chain x (k+1) = e_k x`, i.e. the sequence
`s₀, e₀ x, e₁ x, e₂ x, …`.  (The `k`-th entry is the `k`-th predecessor in the telescoping sum
of `Haar.level_sum`.) -/
noncomputable def chain (T : LightProfinite.{0}) [Infinite T] (x : ↥T) (k : ℕ) : ↥T :=
  if k = 0 then (Work.ATOM.levelData T).s₀ else Work.ATOM.e T (k - 1) x

@[simp] theorem chain_succ (T : LightProfinite.{0}) [Infinite T] (x : ↥T) (k : ℕ) :
    Haar.chain T x (k+1) = Work.ATOM.e T k x := by
  rw [Haar.chain, if_neg (Nat.succ_ne_zero k), show k + 1 - 1 = k from rfl]

@[simp] theorem chain_zero (T : LightProfinite.{0}) [Infinite T] (x : ↥T) :
    Haar.chain T x 0 = (Work.ATOM.levelData T).s₀ := by
  rw [Haar.chain, if_pos rfl]

/-- The "parent" `par T j` of a new point of level `k` is the `k`-th element of the chain of any
point `x` with `e_k x = a_j`. -/
theorem par_eq_chain (T : LightProfinite.{0}) [Infinite T] (k : ℕ) (j : ℕ) (x : ↥T)
    (hj : Haar.lvl T j = k) (h : Work.ATOM.e T k x = (Work.ATOM.levelData T).a j) :
    Haar.par T j = Haar.chain T x k := by
  have hj' : Work.ATOM.lvl T j = k := hj
  rw [Haar.par, Haar.chain, hj']
  rw [← h]
  by_cases hk : k = 0
  · rw [dif_pos hk, if_pos hk]
  · rw [dif_neg hk, if_neg hk]
    rw [Haar.e_comp_apply T k (k - 1) x, Nat.min_eq_right (by omega : k - 1 ≤ k)]

/-- **The "no new point at level `k`" case**: if no `a_j` of level `k` equals `e_k x`, then
`e_{k-1} x = e_k x` (this is the case in which the level-`k` part of the expansion is empty and
the telescoping difference vanishes). -/
theorem chain_eq_of_no_mem (T : LightProfinite.{0}) [Infinite T] (k : ℕ) (x : ↥T)
    (h : ¬ ∃ j ∈ Haar.newFinset T k, (Work.ATOM.levelData T).a j = Work.ATOM.e T k x) :
    Work.ATOM.e T k x = Haar.chain T x k := by
  rcases k with _ | m
  · rw [Haar.chain_zero]
    have hmem : Work.ATOM.e T 0 x ∈ Work.ATOM.levelSet T :=
      Set.mem_iUnion.mpr ⟨0, ⟨x, rfl⟩⟩
    rcases (Work.ATOM.levelData_mem_levelSet_iff (S := T) (Work.ATOM.e T 0 x)).mp hmem with
      ⟨j, hj⟩ | h0
    · exfalso
      refine h ⟨j, ?_, hj⟩
      rw [Haar.mem_newFinset]
      have hle : Haar.lvl T j ≤ 0 := by
        change (Work.ATOM.levelData T).lv ((Work.ATOM.levelData T).a j) ≤ 0
        rw [hj]
        exact Work.ATOM.levelData_lv_le (⟨x, rfl⟩ : Work.ATOM.e T 0 x ∈ Work.ATOM.A T 0)
      omega
    · exact h0
  · rw [Haar.chain_succ]
    by_contra hne
    have hmem : Work.ATOM.e T (m+1) x ∈ Work.ATOM.A T (m+1) := ⟨x, rfl⟩
    have hnot : Work.ATOM.e T (m+1) x ∉ Work.ATOM.A T m := by
      intro hc
      have h1 : Work.ATOM.e T m (Work.ATOM.e T (m+1) x) = Work.ATOM.e T (m+1) x :=
        Work.ATOM.e_fixes_of_mem_A T hc
      have h2 : Work.ATOM.e T m (Work.ATOM.e T (m+1) x) = Work.ATOM.e T m x := by
        rw [Haar.e_comp_apply T (m+1) m x, Nat.min_eq_right (by omega : m ≤ m + 1)]
      exact hne (h1.symm.trans h2)
    obtain ⟨j, hj, haj⟩ := Haar.exists_a_eq_of_mem_A_succ_not_mem_A T hmem hnot
    exact h ⟨j, by rw [Haar.mem_newFinset]; exact hj, haj⟩

/-- **The level-`k` part of the expansion is a telescoping difference.**  For every point `x`
and every `g : LC T`, the sum of `phi T j g * fCyl T j x` over the new points of level `k`
collapses to `g (e_k x) - g (chain x k)`. -/
theorem level_sum (T : LightProfinite.{0}) [Infinite T] (k : ℕ) (x : ↥T) (g : Haar.LC T) :
    ∑ j ∈ Haar.newFinset T k, Haar.phi T j g * Haar.fCyl T j x
      = g (Work.ATOM.e T k x) - g (Haar.chain T x k) := by
  have hterm : ∀ j ∈ Haar.newFinset T k,
      Haar.phi T j g * Haar.fCyl T j x
        = (if Work.ATOM.e T k x = (Work.ATOM.levelData T).a j then (1:ℤ) else 0)
          * (g (Work.ATOM.e T k x) - g (Haar.chain T x k)) := by
    intro j hj
    rw [Haar.mem_newFinset] at hj
    rw [Haar.fCyl_apply', hj]
    by_cases h : Work.ATOM.e T k x = (Work.ATOM.levelData T).a j
    · simp only [if_pos h, one_mul, mul_one]
      show g ((Work.ATOM.levelData T).a j) - g (Haar.par T j)
        = g (Work.ATOM.e T k x) - g (Haar.chain T x k)
      rw [← h, Haar.par_eq_chain T k j x hj h]
    · simp only [if_neg h, mul_zero, zero_mul]
  have hmain : (∑ j ∈ Haar.newFinset T k,
      (if Work.ATOM.e T k x = (Work.ATOM.levelData T).a j then (1:ℤ) else 0)
        * (g (Work.ATOM.e T k x) - g (Haar.chain T x k)))
      = g (Work.ATOM.e T k x) - g (Haar.chain T x k) := by
    by_cases h : ∃ j ∈ Haar.newFinset T k,
      (Work.ATOM.levelData T).a j = Work.ATOM.e T k x
    · obtain ⟨j₀, hj₀, haj₀⟩ := h
      have hsingle : ∀ b ∈ Haar.newFinset T k, b ≠ j₀ →
          (if Work.ATOM.e T k x = (Work.ATOM.levelData T).a b then (1:ℤ) else 0)
            * (g (Work.ATOM.e T k x) - g (Haar.chain T x k)) = 0 := by
        intro b hb hne
        rw [if_neg (fun hcontra =>
          hne (Work.ATOM.levelData_a_inj (hcontra.symm.trans haj₀.symm))), zero_mul]
      rw [Finset.sum_eq_single_of_mem j₀ hj₀ hsingle, if_pos haj₀.symm, one_mul]
    · have hzero : ∀ b ∈ Haar.newFinset T k,
          (if Work.ATOM.e T k x = (Work.ATOM.levelData T).a b then (1:ℤ) else 0)
            * (g (Work.ATOM.e T k x) - g (Haar.chain T x k)) = 0 := by
        intro b hb
        rw [if_neg (fun hcontra => h ⟨b, hb, hcontra.symm⟩), zero_mul]
      rw [Finset.sum_eq_zero hzero, Haar.chain_eq_of_no_mem T k x h, sub_self]
  exact (Finset.sum_congr rfl hterm).trans hmain

end Haar

theorem haar_expand (T : LightProfinite.{0}) [Infinite T] (N : ℕ) (g : Work.ANALYTIC.Haar.LC T)
    (hg : ∀ x, g x = g (Work.ATOM.e T N x)) (x : ↥T) :
    g x = g (Work.ATOM.levelData T).s₀ + ∑ j ∈ Work.ANALYTIC.Haar.lvlFinset T N,
      (Work.ANALYTIC.Haar.phi T j g) * Work.ANALYTIC.Haar.fCyl T j x := by
  have hsum : ∑ j ∈ Haar.lvlFinset T N, (Haar.phi T j g) * Haar.fCyl T j x
      = g (Work.ATOM.e T N x) - g (Work.ATOM.levelData T).s₀ := by
    rw [show Haar.lvlFinset T N = (Finset.range (N + 1)).biUnion
        (fun k => Haar.newFinset T k) from rfl]
    rw [Finset.sum_biUnion]
    · simp_rw [Haar.level_sum]
      simp_rw [← Haar.chain_succ]
      rw [Finset.sum_range_sub (fun i => g (Haar.chain T x i)) (N+1), Haar.chain_zero]
    · intro a _ b _ hab
      change Disjoint (Haar.newFinset T a) (Haar.newFinset T b)
      rw [Finset.disjoint_left]
      intro j hja hjb
      rw [Haar.mem_newFinset] at hja hjb
      exact hab (hja.symm.trans hjb)
  rw [hg x, hsum]
  ring

end Work.ANALYTIC
