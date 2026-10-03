/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Translation invariance of Peluse's box norm

The Gowers *box* norm `‖f‖_{□^t_{Q₁,…,Q_t}(S)}` of Peluse's Definition 2.1 is built from the
`2^t`-th power

`‖f‖^{2^t} = (1/|S|) ∑_x E_{h,h' ∈ ∏ Q_i} ∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`

(`Work.Peluse.boxNormPow`), whose `x`-average is an unconditional `tsum` over `ℤ`.  Translating
the argument of `f`, i.e. replacing `f` by the shift `T_p f = f (· + p)`
(`Work.Peluse.shift`), is the change of variables `x ↦ x + p`, a bijection of `ℤ`, so the norm is
unchanged:

* `Work.Peluse.BoxNorm.boxNormPow_shift` : `‖T_p f‖ = ‖f‖`.

Nothing here needs summability of `f` (`FinSuppZ`): the `tsum` over `ℤ` of Mathlib is invariant
under any bijection of the index type, summable or not.  The hypothesis `FinSuppZ f` is kept
because it is the standing hypothesis of the area, and it is what makes the quantity a genuine
finite sum in the applications.

The proof is a reindexing, isolated in the two helper lemmas `tsum_shift_add` (the change of
variables for a `tsum` over `ℤ`) and `tsum_cubeTerm_shift` (the cube term `∏_ω C^{|ω|} f_ω (x + c_ω)`
with all the shifts pushed onto the arguments).  The general forms `prodCubeSum_shift` and
`boxSumPow_shift` are proved first since they are the natural statements.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.BoxNorm

/-! ## Reindexing lemmas -/

/-- Change of variables for an unconditional sum over `ℤ`: translating the argument by `p` is a
bijection of `ℤ`, so `∑' x, G (x + p) = ∑' x, G x`.  No summability hypothesis is needed. -/
lemma tsum_shift_add (G : ℤ → ℂ) (p : ℤ) : (∑' x : ℤ, G (x + p)) = ∑' x : ℤ, G x := by
  simpa [Equiv.coe_addRight] using Equiv.tsum_eq (Equiv.addRight p) G

/-- The cube term `∏_ω C^{|ω|} f_ω (x + c_ω)`, summed over `x ∈ ℤ`, is unchanged when every one of
the `2^t` functions `f_ω` is replaced by its shift `T_p f_ω` — the substitution `x ↦ x + p` moves
the shift off the functions and into the argument. -/
lemma tsum_cubeTerm_shift (t : ℕ) (F : (Fin t → Bool) → ℤ → ℂ) (p : ℤ)
    (c : (Fin t → Bool) → ℤ) :
    (∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) ((Work.Peluse.shift p (F ω)) (x + c ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (x + c ω)) := by
  have h1 : (∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) ((Work.Peluse.shift p (F ω)) (x + c ω)))
      = ∑' x : ℤ, (fun y : ℤ => ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (y + c ω))) (x + p) := by
    apply tsum_congr
    intro x
    show (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω]) ((Work.Peluse.shift p (F ω)) (x + c ω)))
        = ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω]) (F ω (x + p + c ω))
    refine Finset.prod_congr rfl fun ω _ => ?_
    simp only [Work.Peluse.shift]
    congr 1
    ring_nf
  exact h1.trans (tsum_shift_add (fun y : ℤ => ∏ ω : Fin t → Bool,
    (star^[Work.Peluse.weight ω]) (F ω (y + c ω))) p)

/-! ## The invariance statements -/

/-- The cube average `prodCubeSum` with `2^t` (not necessarily equal) functions is invariant under
translating all the functions simultaneously. -/
lemma prodCubeSum_shift (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (F : (Fin t → Bool) → ℤ → ℂ) (p : ℤ) :
    Work.Peluse.prodCubeSum t Q S (fun ω => Work.Peluse.shift p (F ω))
      = Work.Peluse.prodCubeSum t Q S F := by
  simp only [Work.Peluse.prodCubeSum]
  have hsum : (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω]) ((Work.Peluse.shift p (F ω))
            (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
      = (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω]) (F ω
            (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := by
    refine Finset.sum_congr rfl fun h _ => ?_
    refine Finset.sum_congr rfl fun h' _ => ?_
    exact tsum_cubeTerm_shift t F p
      (fun ω => Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)
  rw [hsum]

/-- The `2^t`-th power `boxSumPow` of the box norm is invariant under translating `f`.  (The
`tsum` over `x` is reindexed by `x ↦ x + p`; the prefactor `(1/|S|)·E_{h,h'} …` is untouched.) -/
lemma boxSumPow_shift (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) (p : ℤ) :
    Work.Peluse.boxSumPow t Q S (Work.Peluse.shift p f) = Work.Peluse.boxSumPow t Q S f :=
  prodCubeSum_shift t Q S (fun _ => f) p

/-- Translating `f` does not change the `2^t`-th power `boxNormPow` of its Gowers box norm.  This
is immediate from `boxSumPow_shift`, `boxNormPow` being the modulus of `boxSumPow`.  The standing
hypothesis `FinSuppZ f` is not needed: the reindexing is unconditional. -/
theorem boxNormPow_shift (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) (p : ℤ)
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow t Q S (Work.Peluse.shift p f) = Work.Peluse.boxNormPow t Q S f := by
  have _ := hf
  simp only [Work.Peluse.boxNormPow]
  rw [boxSumPow_shift]

end Work.Peluse.BoxNorm
