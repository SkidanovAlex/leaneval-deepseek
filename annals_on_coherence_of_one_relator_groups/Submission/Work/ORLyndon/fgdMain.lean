/-
# Free groups have the unique product property, and `K[F(X)]` is a domain

This file assembles the proof that the group algebra of a free group over any field is an integral
domain, a basic input to the coherence theory of one-relator groups (Jaikin-Zapirain--Linton,
*Annals* 201 (2025)).

## The mathematics

Let `T` be the Cayley graph of the free group `F(X)` with respect to `X`.  `T` is a tree, and the
geodesic from `1` to `g` is obtained from the reduced word `toWord g` by taking its successive
prefixes.  Two consequences are used:

* the *word length* `norm` satisfies the tree/geodesic identity, in the quantitative form
  `norm (a⁻¹ * b) + 2 * lcpLen (toWord a) (toWord b) = norm a + norm b`, where `lcpLen` is the
  length of the longest common prefix of the two reduced words (if the reduced words split as
  `toWord a = P ++ A`, `toWord b = P ++ B` with `P` the maximal common prefix, then
  `toWord (a⁻¹ * b) = reduce (invRev A ++ B)`, whose length is `|A| + |B|`);
* hence, for `k ≠ 1` and arbitrary `g`, the function `n ↦ norm (g * k ^ n)` is `V`-shaped, so it has
  no weak local maximum: **`norm g < norm (g * k)` or `norm g < norm (g * k⁻¹)`**
  (`norm_lt_mul_or_norm_lt_mul_inv`).

The last statement is the key to the *unique product property*: if `A` and `B` are finite nonempty
subsets of `F(X)` and `(a₀, b₀)` maximises `norm (a * b)` over `A × B`, then `a₀ * b₀` has a unique
splitting.  Indeed, if `a * b = a₀ * b₀` with `a ≠ a₀`, then with `h = a⁻¹ * a₀ ≠ 1` one has
`b = h * b₀` and, by maximality, both `norm (g * k) ≤ norm g` and `norm (g * k⁻¹) ≤ norm g` for
`g = a * h * b₀` and `k = b₀⁻¹ * h * b₀`, contradicting the tree identity.

Since `FreeGroup X` is a group, `UniqueProds (FreeGroup X)` yields `TwoUniqueProds` and the
`NoZeroDivisors`/`IsDomain` instances of `Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors` apply.
-/
import Mathlib
import Submission.Work.ORLyndon.fgdDefs
import Submission.Work.ORLyndon.take_eq_of_le_lcpLen
import Submission.Work.ORLyndon.reduce_invRev_append_length

set_option autoImplicit false

namespace Work.ORLyndon

open FreeGroup

/-! ### The norm formula -/

/-- **The tree identity for the word length.**  For `a b : FreeGroup X`,

`norm (a⁻¹ * b) + 2 * lcpLen (toWord a) (toWord b) = norm a + norm b`.

The correction term is twice the length of the common prefix of the two reduced words, i.e. twice
the distance from `1` to the geodesic joining `a` and `b` in the Cayley tree. -/
theorem norm_inv_mul_add {α : Type*} [DecidableEq α] (a b : FreeGroup α) :
    FreeGroup.norm (a⁻¹ * b) + 2 * lcpLen (FreeGroup.toWord a) (FreeGroup.toWord b)
      = FreeGroup.norm a + FreeGroup.norm b := by
  have h := reduce_invRev_append_length (W := FreeGroup.toWord a) (Z := FreeGroup.toWord b)
    (FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_toWord a))
    (FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_toWord b))
  have hw : FreeGroup.toWord (a⁻¹ * b) =
      FreeGroup.reduce (FreeGroup.invRev (FreeGroup.toWord a) ++ FreeGroup.toWord b) := by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv]
  simp only [FreeGroup.norm]
  rw [hw]
  exact h

/-- The inverse-reversal of a list, entry by entry, at the level of `getElem?`.  (Stated with
`getElem?` so that no index proofs are involved.) -/
theorem invRev_getElem?_eq {α : Type*} [DecidableEq α] (V : List (α × Bool)) {j : ℕ}
    (hj : j < V.length) :
    (FreeGroup.invRev V)[j]? = (V[V.length - 1 - j]?).map invSym := by
  have h : FreeGroup.invRev V = (V.map (fun x : α × Bool => invSym x)).reverse := rfl
  rw [h, List.getElem?_reverse (h := by rw [List.length_map]; exact hj), List.length_map,
    List.getElem?_map]

/-! ### The key cancellation lemma -/

/-- **No element can cancel into the end of `g` on both sides.**  In a free group, for `k ≠ 1` the
products `g * k` and `g * k⁻¹` cannot both be no longer than `g`: the image of `n ↦ norm (g * kⁿ)`
in the Cayley tree is `V`-shaped with vertices at distance `norm k` from each other, so it has no
weak local maximum at `n = 0`. -/
theorem norm_lt_mul_or_norm_lt_mul_inv {α : Type*} [DecidableEq α] {g k : FreeGroup α}
    (hk : k ≠ 1) :
    FreeGroup.norm g < FreeGroup.norm (g * k) ∨ FreeGroup.norm g < FreeGroup.norm (g * k⁻¹) := by
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h1' : (g * k).toWord.length ≤ g.toWord.length := by simpa only [FreeGroup.norm] using h1
  have h2' : (g * k⁻¹).toWord.length ≤ g.toWord.length := by simpa only [FreeGroup.norm] using h2
  have key1 : (g * k).toWord.length + 2 * lcpLen (FreeGroup.invRev g.toWord) k.toWord
      = g.toWord.length + k.toWord.length := by
    have h := norm_inv_mul_add (α := α) (a := g⁻¹) (b := k)
    simpa only [FreeGroup.norm, inv_inv, FreeGroup.toWord_inv, FreeGroup.norm_inv_eq,
      FreeGroup.invRev_length] using h
  have key2 : (g * k⁻¹).toWord.length + 2 * lcpLen (FreeGroup.invRev g.toWord) (FreeGroup.invRev k.toWord)
      = g.toWord.length + k.toWord.length := by
    have h := norm_inv_mul_add (α := α) (a := g⁻¹) (b := k⁻¹)
    simpa only [FreeGroup.norm, inv_inv, FreeGroup.toWord_inv, FreeGroup.norm_inv_eq,
      FreeGroup.invRev_length] using h
  have hL1 : k.toWord.length ≤ 2 * lcpLen (FreeGroup.invRev g.toWord) k.toWord := by
    have step : g.toWord.length + k.toWord.length ≤
        g.toWord.length + 2 * lcpLen (FreeGroup.invRev g.toWord) k.toWord := by
      rw [← key1]
      exact Nat.add_le_add_right h1' _
    omega
  have hL2 : k.toWord.length ≤ 2 * lcpLen (FreeGroup.invRev g.toWord) (FreeGroup.invRev k.toWord) := by
    have step : g.toWord.length + k.toWord.length ≤
        g.toWord.length + 2 * lcpLen (FreeGroup.invRev g.toWord) (FreeGroup.invRev k.toWord) := by
      rw [← key2]
      exact Nat.add_le_add_right h2' _
    omega
  have hVne : k.toWord ≠ [] := fun hh => hk (FreeGroup.toWord_eq_nil_iff.mp hh)
  have hVpos : 0 < k.toWord.length := List.length_pos_iff.mpr hVne
  have hred : FreeGroup.IsReduced k.toWord :=
    FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_toWord k)
  -- `k.toWord` is reflected onto itself, entrywise, in the overlap of its first and last
  -- `lcpLen`-many letters:
  have hentry : ∀ (j : ℕ), j + 1 ≤ lcpLen (FreeGroup.invRev g.toWord) k.toWord →
      j + 1 ≤ lcpLen (FreeGroup.invRev g.toWord) (FreeGroup.invRev k.toWord) →
      j < k.toWord.length →
      k.toWord[j]? = (k.toWord[k.toWord.length - 1 - j]?).map invSym := by
    intro j hj1 hj2 hjV
    have hta := take_eq_of_le_lcpLen (W := FreeGroup.invRev g.toWord) (Z := k.toWord) (m := j + 1) hj1
    have htb := take_eq_of_le_lcpLen (W := FreeGroup.invRev g.toWord) (Z := FreeGroup.invRev k.toWord)
      (m := j + 1) hj2
    have hVtake : k.toWord.take (j + 1) = (FreeGroup.invRev k.toWord).take (j + 1) :=
      hta.symm.trans htb
    have hopt : (k.toWord.take (j + 1))[j]? = ((FreeGroup.invRev k.toWord).take (j + 1))[j]? :=
      congrArg (fun l : List (α × Bool) => l[j]?) hVtake
    rw [List.getElem?_take, List.getElem?_take] at hopt
    simp only [if_pos (show j < j + 1 by omega)] at hopt
    rw [invRev_getElem?_eq k.toWord hjV] at hopt
    exact hopt
  obtain ⟨t, ht⟩ | ⟨t, ht⟩ := Nat.even_or_odd k.toWord.length
  · -- even case: `k.toWord.length = t + t`; two neighbouring letters are inverse to each other
    have ht1 : 1 ≤ t := by omega
    have h₁ : t - 1 < k.toWord.length := by omega
    have h₂ : t < k.toWord.length := by omega
    have hkey : k.toWord[t-1]'h₁ = invSym (k.toWord[t]'h₂) := by
      have hopt := hentry (t - 1) (by omega) (by omega) h₁
      rw [show k.toWord.length - 1 - (t - 1) = t from by omega] at hopt
      rw [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at hopt
      simpa only [Option.map_some] using Option.some.inj hopt
    have hdec : k.toWord = k.toWord.take (t - 1) ++
        k.toWord[t-1]'h₁ :: k.toWord[t]'h₂ :: k.toWord.drop (t + 1) := by
      have d1 := List.drop_eq_getElem_cons (l := k.toWord) (i := t - 1) h₁
      have d2 := List.drop_eq_getElem_cons (l := k.toWord) (i := t) h₂
      rw [Nat.sub_add_cancel ht1] at d1
      rw [← d2, ← d1, List.take_append_drop]
    have hrel := (List.isChain_iff_forall_rel_of_append_cons_cons.mp hred)
      (a := k.toWord[t-1]'h₁) (b := k.toWord[t]'h₂)
      (l₁ := k.toWord.take (t - 1)) (l₂ := k.toWord.drop (t + 1)) hdec
    have hfk : (k.toWord[t-1]'h₁).1 = (k.toWord[t]'h₂).1 := by rw [hkey]; rfl
    have hsk : (k.toWord[t-1]'h₁).2 = !(k.toWord[t]'h₂).2 := by rw [hkey]; rfl
    exact Bool.not_ne_self _ (by rw [← hsk]; exact hrel hfk)
  · -- odd case: `k.toWord.length = 2 * t + 1`; the middle letter is its own inverse
    have h₁ : t < k.toWord.length := by omega
    have hkey : k.toWord[t]'h₁ = invSym (k.toWord[t]'h₁) := by
      have hopt := hentry t (by omega) (by omega) h₁
      rw [show k.toWord.length - 1 - t = t from by omega] at hopt
      rw [List.getElem?_eq_getElem h₁] at hopt
      simpa only [Option.map_some] using Option.some.inj hopt
    exact invSym_ne_self _ hkey.symm

/-! ### The unique product property -/

/-- **Free groups have the unique product property.**  For finite nonempty `A B : Finset (FreeGroup X)`
there are `a₀ ∈ A`, `b₀ ∈ B` such that `a * b = a₀ * b₀` with `a ∈ A`, `b ∈ B` forces `a = a₀` and
`b = b₀`: take `(a₀, b₀)` maximising the word length of the product. -/
instance uniqueProds_freeGroup (X : Type*) : UniqueProds (FreeGroup X) := by
  classical
  refine ⟨fun {A B} hA hB => ?_⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (A ×ˢ B)
    (fun p : FreeGroup X × FreeGroup X => FreeGroup.norm (p.1 * p.2)) (hA.product hB)
  rw [Finset.mem_product] at hp
  refine ⟨p.1, hp.1, p.2, hp.2, ?_⟩
  intro a b ha hb hab
  have hkey : a = p.1 := by
    by_contra hane
    set h : FreeGroup X := a⁻¹ * p.1 with hh
    have hh1 : h ≠ 1 := by
      intro hc
      apply hane
      have key : p.1 = a := by
        have := congrArg (fun z => a * z) hc
        simpa [hh, mul_assoc] using this
      exact key.symm
    have hb_eq : b = h * p.2 := by
      rw [← inv_mul_cancel_left a b, hab, hh, mul_assoc]
    have hconj : p.2⁻¹ * h * p.2 ≠ 1 := by
      intro hc
      apply hh1
      have := congrArg (fun z => p.2 * z * p.2⁻¹) hc
      simpa [mul_assoc] using this
    have hg : a * h * p.2 = p.1 * p.2 := by rw [hh]; group
    have hp1 : p.1 = a * h := by rw [hh]; group
    -- both products with `k = p.2⁻¹ * h * p.2` are no longer than the maximal one
    have h1 : FreeGroup.norm (a * h * p.2 * (p.2⁻¹ * h * p.2)) ≤
        FreeGroup.norm (a * h * p.2) := by
      have hm : FreeGroup.norm (p.1 * b) ≤ FreeGroup.norm (p.1 * p.2) :=
        hmax (p.1, b) (by rw [Finset.mem_product]; exact ⟨hp.1, hb⟩)
      have heq : p.1 * b = a * h * p.2 * (p.2⁻¹ * h * p.2) := by
        rw [hb_eq, hp1]; group
      rw [heq, ← hg] at hm
      exact hm
    have h2 : FreeGroup.norm (a * h * p.2 * (p.2⁻¹ * h * p.2)⁻¹) ≤
        FreeGroup.norm (a * h * p.2) := by
      have hm : FreeGroup.norm (a * p.2) ≤ FreeGroup.norm (p.1 * p.2) :=
        hmax (a, p.2) (by rw [Finset.mem_product]; exact ⟨ha, hp.2⟩)
      have heq : a * p.2 = a * h * p.2 * (p.2⁻¹ * h * p.2)⁻¹ := by group
      rw [heq, ← hg] at hm
      exact hm
    rcases norm_lt_mul_or_norm_lt_mul_inv hconj with hlt | hlt
    · exact absurd h1 (not_le.mpr hlt)
    · exact absurd h2 (not_le.mpr hlt)
  rw [hkey] at hab
  exact ⟨hkey, mul_left_cancel hab⟩

end Work.ORLyndon
