import Mathlib

/-!
# Counting binary vectors of bounded Hamming weight

The number of vectors `v : ι → ZMod 2` with `hammingNorm v ≤ w` equals the sum of
the binomial coefficients `∑_{k ≤ w} (|ι| choose k)`.

The proof goes by identifying a vector over `ZMod 2` with its support (the set of
coordinates where it is non-zero); over `ZMod 2` the value at any coordinate of the
support is forced to be `1`, so this support map is a bijection onto the set of all
finsets of `ι`. It preserves cardinality of the support (= the Hamming norm by
definition), and the finsets of size at most `w` are partitioned by their size.
-/

namespace Work.LT

open Finset

/-- The support of a vector over `ZMod 2`, i.e. the set of coordinates where it is non-zero. -/
def supp {ι : Type*} [Fintype ι] (v : ι → ZMod 2) : Finset ι :=
  Finset.univ.filter (fun i => v i ≠ 0)

/-- By definition the Hamming norm of `v` is the size of its support. -/
lemma hammingNorm_eq_supp {ι : Type*} [Fintype ι] (v : ι → ZMod 2) :
    hammingNorm v = (supp v).card := rfl

/-- In `ZMod 2` every non-zero element is `1`. -/
lemma zmod2_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have hne : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).mp h)
  have h1 : x.val = 1 := by omega
  calc x = ((x.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val x).symm
    _ = ((1 : ℕ) : ZMod 2) := by rw [h1]
    _ = 1 := by norm_num

/-- The support of the characteristic vector of `s` is `s`. -/
lemma supp_right_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) :
    supp (fun i => if i ∈ s then 1 else 0) = s := by
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i ∈ s
  · simp [h]
  · simp [h]

/-- A vector over `ZMod 2` is the characteristic vector of its support. -/
lemma supp_left_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ZMod 2) :
    (fun i => if i ∈ supp v then 1 else 0) = v := by
  funext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : v i = 0
  · simp [h]
  · simp [zmod2_eq_one_of_ne_zero (v i) h]

/-- Two vectors over `ZMod 2` with the same support are equal. -/
lemma eq_of_supp_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {v u : ι → ZMod 2}
    (h : supp v = supp u) : v = u := by
  rw [← supp_left_inv v, h, supp_left_inv u]

/-- The number of vectors `v : ι → ZMod 2` of Hamming weight at most `w` equals `∑_{k=0}^{w} (|ι| choose k)`. -/
theorem card_filter_hammingNorm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℕ) :
    (Finset.univ.filter (fun v : ι → ZMod 2 => hammingNorm v ≤ w)).card =
      ∑ k ∈ Finset.range (w + 1), (Fintype.card ι).choose k := by
  -- Step 1: transport along the support bijection to the counting of finsets of size `≤ w`.
  have h1 : (Finset.univ.filter (fun v : ι → ZMod 2 => hammingNorm v ≤ w)).card
      = (Finset.univ.filter (fun s : Finset ι => s.card ≤ w)).card := by
    refine Finset.card_bij (fun v _ => supp v) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rwa [← hammingNorm_eq_supp]
    · intro v hv u hu h
      exact eq_of_supp_eq h
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      refine ⟨fun i => if i ∈ s then 1 else 0, ?_, supp_right_inv s⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hammingNorm_eq_supp, supp_right_inv]
      exact hs
  -- Step 2: the finsets of size `≤ w` are the disjoint union of the `k`-subsets, `k ≤ w`.
  have h2 : (Finset.univ.filter (fun s : Finset ι => s.card ≤ w))
      = Finset.biUnion (Finset.range (w + 1))
          (fun k => (Finset.univ : Finset ι).powersetCard k) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · intro h
      exact ⟨s.card, Nat.lt_succ_of_le h, Finset.subset_univ s, rfl⟩
    · rintro ⟨k, hk, -, hk2⟩
      omega
  rw [h1, h2, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, Finset.card_univ]
  · -- the `k`-subsets are pairwise disjoint for distinct `k`
    intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro a ha b hb hab
    simp only [Finset.mem_powersetCard] at ha hb
    exact hxy (by rw [← ha.2, ← hb.2, hab])

end Work.LT
