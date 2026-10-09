import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.DivisionPoints
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fibres of `[π] : Λ_{n+1} → Λ_n` have exactly `q` elements

For the standard Lubin–Tate group with `f(T) = πT + T^q` and `q ≥ 2`, the reduction
`f : Λ_{n+1} → Λ_n` (`Λ_m = LTdivisionSet F (π:F) q m`) is well defined by
`f^{(n)}(f(x)) = f^{(n+1)}(x)`, and every fibre has exactly `q` elements (Milne, *CFT*, §I.3:
`Λ_{n+1}/Λ_n ≅ Λ_1`, which has `q` elements).

The proof is a counting argument.  The fibres partition `Λ_{n+1}` over the base `Λ_n`, each
fibre is contained in the root set of the degree-`q` polynomial `X^q + πX - β`, and
`#Λ_{n+1} = q^{n+1} = q · #Λ_n`, so every fibre has the maximal possible size `q`.

## Main result

* `NK.LocalReciprocityLubinTate.LubinTate.ncard_fiber_LTdivisionSet` — every fibre has `q`
  elements.
-/

open Polynomial

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

/-- **Every fibre of `f : Λ_{n+1} → Λ_n` over a point `β ∈ Λ_n` has exactly `q` elements**
(Milne, *CFT*, §I.3: `Λ_{n+1}/Λ_n ≅ Λ_1` has `q` elements).

Counting argument: the preimages of the points of `Λ_n` partition `Λ_{n+1}`, each preimage lies in
the root set of the degree-`q` polynomial `X^q + πX - β` so has at most `q` elements, and
`#Λ_{n+1} = q^{n+1} = q·#Λ_n`, so each has exactly `q`. -/
theorem ncard_fiber_LTdivisionSet (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    {β : AlgebraicClosure F} (hβ : β ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n) :
    {x : AlgebraicClosure F | x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q (n + 1) ∧
      (Polynomial.aeval x) (NK.LocalReciprocityLubinTate.LTpoly (π : F) q) = β}.ncard = q := by
  classical
  let f : AlgebraicClosure F → AlgebraicClosure F :=
    fun x => (Polynomial.aeval x) (LTpoly (π : F) q)
  -- `x ∈ Λ_{n+1}` iff `f x ∈ Λ_n`
  have hsucc : ∀ x : AlgebraicClosure F,
      x ∈ LTdivisionSet F (π : F) q (n + 1) ↔ f x ∈ LTdivisionSet F (π : F) q n := by
    intro x
    rw [mem_LTdivisionSet_iff (π : F) q (n + 1) hq, mem_LTdivisionSet_iff (π : F) q n hq,
      LTpolyIter_succ, Polynomial.aeval_comp]
  have hfin_n : (LTdivisionSet F (π : F) q n).Finite := by
    unfold LTdivisionSet; exact Set.toFinite _
  have hfin_s : (LTdivisionSet F (π : F) q (n + 1)).Finite := by
    unfold LTdivisionSet; exact Set.toFinite _
  let A : Finset (AlgebraicClosure F) := hfin_n.toFinset
  let U : Finset (AlgebraicClosure F) := hfin_s.toFinset
  have hA : (A : Set (AlgebraicClosure F)) = LTdivisionSet F (π : F) q n := hfin_n.coe_toFinset
  have hU : (U : Set (AlgebraicClosure F)) = LTdivisionSet F (π : F) q (n + 1) :=
    hfin_s.coe_toFinset
  have hmaps : Set.MapsTo f (U : Set (AlgebraicClosure F)) (A : Set (AlgebraicClosure F)) := by
    intro x hx
    rw [hU] at hx
    rw [hA]
    exact (hsucc x).mp hx
  -- the fibres partition `Λ_{n+1}` over `Λ_n`
  have hsum := Finset.card_eq_sum_card_fiberwise (f := f) (s := U) (t := A) hmaps
  have hUcard : U.card = q ^ (n + 1) := by
    rw [← Set.ncard_coe_finset U, hU]
    exact ncard_LTdivisionSet F π hπ q (n + 1) hq
  have hAcard : A.card = q ^ n := by
    rw [← Set.ncard_coe_finset A, hA]
    exact ncard_LTdivisionSet F π hπ q n hq
  have hfe : ∀ x : AlgebraicClosure F,
      f x = algebraMap F (AlgebraicClosure F) (π : F) * x + x ^ q := by
    intro x
    simp only [f, LTpoly, map_add, Polynomial.aeval_C, Polynomial.aeval_mul, Polynomial.aeval_X,
      Polynomial.aeval_X_pow]
  -- each fibre has at most `q` elements
  have hbound : ∀ b ∈ A, (U.filter (fun x => f x = b)).card ≤ q := by
    intro b _
    set g : Polynomial (AlgebraicClosure F) :=
      (Polynomial.X : Polynomial (AlgebraicClosure F)) ^ q
        + Polynomial.C (algebraMap F (AlgebraicClosure F) (π : F)) * Polynomial.X
        - Polynomial.C b with hg
    have hevaleq : ∀ x : AlgebraicClosure F, Polynomial.eval x g = f x - b := by
      intro x
      rw [hg, hfe x]
      rw [show (Polynomial.X : Polynomial (AlgebraicClosure F)) ^ q
            + Polynomial.C (algebraMap F (AlgebraicClosure F) (π : F)) * Polynomial.X
            - Polynomial.C b
          = (Polynomial.X : Polynomial (AlgebraicClosure F)) ^ q
            + (Polynomial.C (algebraMap F (AlgebraicClosure F) (π : F)) * Polynomial.X
              - Polynomial.C b) from by ring]
      rw [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hgnat : g.natDegree ≤ q := by
      rw [hg]
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      rw [if_neg (by omega : ¬ m = q), if_neg (by omega : ¬ m = 1),
        if_neg (by omega : ¬ m = 0)]
      ring
    have hg0 : g ≠ 0 := by
      intro h
      have hc := congrArg (fun p => p.coeff q) h
      rw [hg] at hc
      simp only [Polynomial.coeff_zero] at hc
      rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at hc
      rw [if_pos rfl, if_neg (by omega : ¬ q = 1), if_neg (by omega : ¬ q = 0)] at hc
      simp only [add_zero, sub_zero] at hc
      exact one_ne_zero hc
    have hsub : U.filter (fun x => f x = b) ⊆ g.roots.toFinset := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨_, hxf⟩ := hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0, Polynomial.IsRoot.def]
      rw [hevaleq x, hxf, sub_self]
    calc (U.filter (fun x => f x = b)).card
        ≤ g.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ g.roots.card := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' g
      _ ≤ q := hgnat
  -- summing: the fibre sizes add up to `#Λ_{n+1} = q^{n+1} = ∑ q`
  have hle_sum : ∑ b ∈ A, (U.filter (fun x => f x = b)).card = ∑ b ∈ A, q := by
    have h1 : ∑ b ∈ A, (U.filter (fun x => f x = b)).card = q ^ (n + 1) := by
      rw [← hsum, hUcard]
    have h2 : ∑ b ∈ A, q = q ^ (n + 1) := by
      rw [Finset.sum_const, hAcard, nsmul_eq_mul, Nat.cast_id, ← pow_succ]
    rw [h1, h2]
  have hterm : ∀ b ∈ A, (U.filter (fun x => f x = b)).card = q :=
    (Finset.sum_eq_sum_iff_of_le hbound).mp hle_sum
  have hbA : β ∈ A := by rw [← Finset.mem_coe, hA]; exact hβ
  have hfib : (U.filter (fun x => f x = β)).card = q := hterm β hbA
  have hset : (U.filter (fun x => f x = β) : Set (AlgebraicClosure F))
      = {x : AlgebraicClosure F | x ∈ LTdivisionSet F (π : F) q (n + 1) ∧ f x = β} := by
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq]
    rw [← Finset.mem_coe, hU]
  change ({x : AlgebraicClosure F | x ∈ LTdivisionSet F (π : F) q (n + 1) ∧ f x = β} :
    Set (AlgebraicClosure F)).ncard = q
  rw [← hset, Set.ncard_coe_finset]
  exact hfib

end NK.LocalReciprocityLubinTate.LubinTate
