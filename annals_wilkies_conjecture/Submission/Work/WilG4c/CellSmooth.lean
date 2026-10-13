import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.StepBadLoc
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-!
# `CellSmooth`

Given a sharply o-minimal structure `S` (with sharp cell decomposition `hcd` and sharp
derivatives `hder`), a definable family `F : Fin k → ℝ^p → ℝ^N → ℝ` of `Ω`-bounded graphs
admits a cylindrical decomposition of `ℝ^{p+N}` every cell of which is, for each family
member, either entirely a `C^r`-locus or entirely contained in the union of its bad loci.

The proof is a direct application of `hcd` to the finitely many *bad unions*
`⋃_{m ≤ r} badLoc (F i) m` — which `SharpDeriv` makes `Ω`-bounded, via `StepBadLoc`; hence the
cells refine each bad union and its complement.  On a cell that avoids the bad union the
function is `C^r` everywhere, since a point that is not `C^r` automatically lies in the bad
locus `badLoc (F i) r`.

The only bookkeeping is that the degree parameter passed to `hcd` is the *value*
`(r + 1) · eval ![D, r] b₁`, whereas the conclusion demands a degree of the shape
`eval ![D, r] B` for a fixed `B : MvPolynomial (Fin 2) ℕ`.  This is handled by `liftPoly`.
-/

/-! ## Degree bookkeeping: from a univariate degree bound to `eval ![D, r] B` -/

/-- Given a two-variable degree polynomial `b` and a *univariate* degree polynomial `c`, the
polynomial `liftPoly b c` is chosen so that
`eval ![D, r] (liftPoly b c) = c.eval ((r + 1) * eval ![D, r] b)`.
Concretely `liftPoly b c = ∑ n ≤ c.natDegree, c.coeff n • (b * (X₁ + 1))^n`, because
`eval ![D, r] (b * (X₁ + 1)) = (r + 1) * eval ![D, r] b`. -/
noncomputable def liftPoly (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) :
    MvPolynomial (Fin 2) ℕ :=
  ∑ n ∈ Finset.range (c.natDegree + 1),
    MvPolynomial.C (c.coeff n) * (b * (MvPolynomial.X 1 + 1)) ^ n

theorem liftPoly_eval (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) (D r : ℕ) :
    MvPolynomial.eval ![D, r] (liftPoly b c) =
      c.eval ((r + 1) * MvPolynomial.eval ![D, r] b) := by
  rw [liftPoly, map_sum]
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [map_mul, map_pow, MvPolynomial.eval_C]
  congr 2
  simp [MvPolynomial.eval_add, MvPolynomial.eval_X, mul_comm]

/-! ## The union of the bad loci is `Ω`-bounded -/

/-- The *bad union* `⋃_{m ≤ r} badLoc f m` of a family member whose graph is `Ω`-bounded is
itself `Ω`-bounded, with a format independent of `D, r` and a degree polynomial in `D, r`.

This is `StepBadLoc` (one bad locus at a time) combined with `SOMin.union` over the `r + 1`
members; the extra factor `X₁ + 1` accounts for the `r + 1` summands. -/
theorem badUnion_mem (S : SOMin) (hder : S.SharpDeriv) (p N F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (F : (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
        famGraph F ∈ S.Ω F0 D (p + N + 1) →
        (⋃ m ∈ Finset.range (r + 1), badLoc F m) ∈
          S.Ω a (MvPolynomial.eval ![D, r] b) (p + N) := by
  obtain ⟨a, b, hb⟩ := StepBadLoc S hder p N F0
  refine ⟨a, b * (MvPolynomial.X 1 + 1), ?_⟩
  intro D r F hF
  have hset : (⋃ m ∈ Finset.range (r + 1), badLoc F m) =
      ⋃ j : Fin (r + 1), badLoc F (j : ℕ) := by
    ext z; simp only [Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, hz⟩; exact ⟨⟨m, hm⟩, hz⟩
    · rintro ⟨j, hz⟩; exact ⟨j, j.isLt, hz⟩
  rw [hset]
  have h := S.union (F := a) (n := p + N) (k := r + 1)
      (D := fun _ : Fin (r + 1) => MvPolynomial.eval ![D, r] b)
      (A := fun j : Fin (r + 1) => badLoc F (j : ℕ))
      (fun j => hb D r F hF (j : ℕ) (Nat.lt_succ_iff.mp j.isLt))
  have hsum : (∑ _j : Fin (r + 1), MvPolynomial.eval ![D, r] b) =
      MvPolynomial.eval ![D, r] (b * (MvPolynomial.X 1 + 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp [MvPolynomial.eval_add, MvPolynomial.eval_X, mul_comm]
  rw [hsum] at h
  exact h

/-! ## The main statement -/

theorem CellSmooth (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p N : ℕ) :
    ∀ (F0 : ℕ), ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r k : ℕ) (F : Fin k → (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + N + 1)) →
        ∃ (C : Finset (Set (Fin (p + N) → ℝ))),
          WilkiesDesign.IsCylDecomp (p + N) C ∧
          (∀ κ ∈ C, κ ∈ S.Ω A (MvPolynomial.eval ![D, r] B) (p + N)) ∧
          (∀ κ ∈ C, ∀ i : Fin k,
            (∀ z ∈ κ, ContDiffAt ℝ r (Work.WilG4c.famFun (F i)) z) ∨
              κ ⊆ ⋃ m ∈ Finset.range (r + 1), Work.WilG4c.badLoc (F i) m) := by
  intro F0
  -- `StepBadLoc`: each bad locus `badLoc (F i) m` (`m ≤ r`) is `Ω`-bounded.
  obtain ⟨a1, b1, hb1⟩ := StepBadLoc S hder p N F0
  -- `hcd` at format `a1` in dimension `p + N` produces the formats / degrees of the cells.
  obtain ⟨a2, b2, c2, hcd2⟩ := hcd a1 (p + N)
  refine ⟨a2, liftPoly b1 c2, ?_⟩
  intro D r k F hF
  -- Apply `hcd` to the `k` bad unions, with degree parameter `(r+1) * eval ![D,r] b1`.
  obtain ⟨C, hcyl, hdich, _hcard, hmemC⟩ :=
    hcd2 ((r + 1) * MvPolynomial.eval ![D, r] b1) k
      (fun i => ⋃ m ∈ Finset.range (r + 1), badLoc (F i) m)
      (fun i => by
        have hset : (⋃ m ∈ Finset.range (r + 1), badLoc (F i) m) =
            ⋃ j : Fin (r + 1), badLoc (F i) (j : ℕ) := by
          ext z; simp only [Set.mem_iUnion, Finset.mem_range]
          constructor
          · rintro ⟨m, hm, hz⟩; exact ⟨⟨m, hm⟩, hz⟩
          · rintro ⟨j, hz⟩; exact ⟨j, j.isLt, hz⟩
        rw [hset]
        have h := S.union (F := a1) (n := p + N) (k := r + 1)
            (D := fun _ : Fin (r + 1) => MvPolynomial.eval ![D, r] b1)
            (A := fun j : Fin (r + 1) => badLoc (F i) (j : ℕ))
            (fun j => hb1 D r (F i) (hF i) (j : ℕ) (Nat.lt_succ_iff.mp j.isLt))
        have hsum : (∑ _j : Fin (r + 1), MvPolynomial.eval ![D, r] b1) =
            (r + 1) * MvPolynomial.eval ![D, r] b1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp
        rw [hsum] at h
        exact h)
  refine ⟨C, hcyl, ?_, ?_⟩
  · -- Degree of every cell matches `eval ![D, r] (liftPoly b1 c2)`.
    intro κ hκ
    rw [liftPoly_eval]
    exact hmemC κ hκ
  · -- The dichotomy, from `hcd`'s compatibility with each bad union.
    intro κ hκ i
    rcases hdich i κ hκ with hsub | hdisj
    · exact Or.inr hsub
    · refine Or.inl ?_
      intro z hz
      by_contra hzcon
      -- A point that is not `C^r` lies in `badLoc (F i) r ⊆ ⋃_{m ≤ r} badLoc (F i) m`.
      have hzbad : z ∈ badLoc (F i) r := by
        rw [badLoc, cLoc]
        exact fun h => hzcon (interior_subset h)
      have hzBi : z ∈ ⋃ m ∈ Finset.range (r + 1), badLoc (F i) m := by
        simp only [Set.mem_iUnion]
        exact ⟨r, Finset.mem_range.mpr (Nat.lt_succ_self r), hzbad⟩
      exact Set.disjoint_left.mp hdisj hz hzBi

end Work.WilG4c
