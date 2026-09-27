import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology

namespace Work.Cohomology

/-!
## The computation rule for the cup product on cohomology

`H.cupOf` is defined on cohomology classes by choosing representatives with `Quot.out`; here we
prove that on classes `H.mk u hu`, `H.mk v hv` of actual cocycles the choice is irrelevant and the
product is computed by the chain-level cup product.  The two auxiliary lemmas isolate the only
homological input: the cup product of a *coboundary* with a cocycle is a coboundary (on either
side).  Both are proved by decomposing the coboundary into degrees and invoking the chain level
statements `cupOf_coboundary_left_mem_boundaries` / `cupOf_coboundary_right_mem_boundaries`.
-/

/-- A coboundary cupped on the left with a cocycle is a coboundary. -/
lemma cupOf_mem_boundaries_left {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ}
    (h : p + q = n) {A : Submission.Cohomology.Cochain S R p}
    (hA : A ∈ Submission.Cohomology.boundaries S R p)
    {b : Submission.Cohomology.Cochain S R q}
    (hb : b ∈ Submission.Cohomology.cycles S R q) :
    Submission.Cohomology.cupOf S R h A b ∈ Submission.Cohomology.boundaries S R n := by
  cases p with
  | zero =>
      have hA0 : A = 0 := by
        simpa only [Submission.Cohomology.boundaries, Submodule.mem_bot] using hA
      subst hA0
      rw [Submission.Cohomology.cupOf_zero_left]
      exact Submodule.zero_mem _
  | succ m =>
      have hn : n = m + q + 1 := by omega
      subst hn
      obtain ⟨a, rfl⟩ := (Submission.Cohomology.mem_boundaries_succ (R := R) (n := m) A).mp hA
      exact Submission.Cohomology.cupOf_coboundary_left_mem_boundaries
        (R := R) (n := m + q) (p := m) (q := q) rfl a hb

/-- A coboundary cupped on the right with a cocycle is a coboundary. -/
lemma cupOf_mem_boundaries_right {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ}
    (h : p + q = n) {u : Submission.Cohomology.Cochain S R p}
    (hu : u ∈ Submission.Cohomology.cycles S R p)
    {B : Submission.Cohomology.Cochain S R q}
    (hB : B ∈ Submission.Cohomology.boundaries S R q) :
    Submission.Cohomology.cupOf S R h u B ∈ Submission.Cohomology.boundaries S R n := by
  cases q with
  | zero =>
      have hB0 : B = 0 := by
        simpa only [Submission.Cohomology.boundaries, Submodule.mem_bot] using hB
      subst hB0
      rw [Submission.Cohomology.cupOf_zero_right]
      exact Submodule.zero_mem _
  | succ m =>
      have hn : n = p + (m + 1) := by omega
      subst hn
      obtain ⟨b, rfl⟩ := (Submission.Cohomology.mem_boundaries_succ (R := R) (n := m) B).mp hB
      exact Submission.Cohomology.cupOf_coboundary_right_mem_boundaries
        (R := R) (m := p + (m + 1)) (p := p) (q := m) rfl hu b

theorem H_cupOf_mk {S : SSet.{0}} {R : Type} [CommRing R] {n p q : ℕ} (h : p + q = n)
    (u : Submission.Cohomology.Cochain S R p) (v : Submission.Cohomology.Cochain S R q)
    (hu : u ∈ Submission.Cohomology.cycles S R p) (hv : v ∈ Submission.Cohomology.cycles S R q) :
    Submission.Cohomology.H.cupOf h (Submission.Cohomology.H.mk u hu)
        (Submission.Cohomology.H.mk v hv)
      = Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h u v)
          (Submission.Cohomology.cupOf_mem_cycles (R := R) h hu hv) := by
  let a : Submission.Cohomology.Cochain S R p := (Quot.out (Submission.Cohomology.H.mk u hu)).1
  let b : Submission.Cohomology.Cochain S R q := (Quot.out (Submission.Cohomology.H.mk v hv)).1
  have ha : a ∈ Submission.Cohomology.cycles S R p :=
    (Quot.out (Submission.Cohomology.H.mk u hu)).2
  have hb : b ∈ Submission.Cohomology.cycles S R q :=
    (Quot.out (Submission.Cohomology.H.mk v hv)).2
  have hmk_a : Submission.Cohomology.H.mk a ha = Submission.Cohomology.H.mk u hu :=
    Quot.out_eq (Submission.Cohomology.H.mk u hu)
  have hmk_b : Submission.Cohomology.H.mk b hb = Submission.Cohomology.H.mk v hv :=
    Quot.out_eq (Submission.Cohomology.H.mk v hv)
  have hAb : a - u ∈ Submission.Cohomology.boundaries S R p :=
    (Submission.Cohomology.H.mk_eq_mk_iff a u ha hu).mp hmk_a
  have hBb : b - v ∈ Submission.Cohomology.boundaries S R q :=
    (Submission.Cohomology.H.mk_eq_mk_iff b v hb hv).mp hmk_b
  show Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h a b)
      (Submission.Cohomology.cupOf_mem_cycles (R := R) h ha hb)
    = Submission.Cohomology.H.mk (Submission.Cohomology.cupOf S R h u v)
      (Submission.Cohomology.cupOf_mem_cycles (R := R) h hu hv)
  rw [Submission.Cohomology.H.mk_eq_mk_iff]
  have hleft : Submission.Cohomology.cupOf S R h (a - u) b
      ∈ Submission.Cohomology.boundaries S R n :=
    cupOf_mem_boundaries_left (R := R) h hAb hb
  have hright : Submission.Cohomology.cupOf S R h u (b - v)
      ∈ Submission.Cohomology.boundaries S R n :=
    cupOf_mem_boundaries_right (R := R) h hu hBb
  have hdecomp : Submission.Cohomology.cupOf S R h a b - Submission.Cohomology.cupOf S R h u v
      = Submission.Cohomology.cupOf S R h u (b - v)
        + Submission.Cohomology.cupOf S R h (a - u) b := by
    have e1 : a = u + (a - u) := by abel
    have e2 : b = v + (b - v) := by abel
    rw [e1, e2, Submission.Cohomology.cupOf_add_left, Submission.Cohomology.cupOf_add_right]
    abel_nf
  rw [hdecomp]
  exact add_mem hright hleft

end Work.Cohomology
