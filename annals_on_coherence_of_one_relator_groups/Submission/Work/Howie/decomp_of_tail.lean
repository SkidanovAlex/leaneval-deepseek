/-
# Decomposition of the tail of a path after an edge of code `c`

This file proves `Work.Howie.decomp_of_tail`, the "splitting the tail at the edge `E`" step of the
forest lemma L5c (`edgeCount_eq_one_of_forest`).

Fix a groupoid presentation `P` of a quiver `V` with an involutive reversal of arrows, an arrow
`E` of `V` with code `c = P.edgeOf E`, and assume

* `hsep : P.CodeSeparates` — the code separates unoriented edges;
* `hfor` — the graph `Γ ∖ e` obtained by deleting the arrows of code `c` is a forest, i.e. every
  reduced closed path of `Γ ∖ e` is empty (`Defs.lean`).

If `X · E · p` is a reduced path, then the tail `p` either avoids the code `c` throughout, or else
it consists of a number `j ≥ 1` of copies of the block `Q · E` (where `Q` is a reduced, `c`-free
path from `E.right` to `E.left`), followed by a `c`-free reduced path `R`:

`p = (Q · E)^j · R`.

Mathematically this is the assertion that in the arrow list of `p`, every arrow of code `c` is the
arrow `E` itself and the `c`-free segments between consecutive occurrences are all equal: the first
one cannot be `E⁻¹` (a backtrack with the initial `E`), and all the later ones are reduced `c`-free
paths from `E.right` to `E.left`, hence equal to the first one by uniqueness of reduced paths in
the forest `Γ ∖ e`.
-/
import Mathlib
import Submission.Work.Howie.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Elementary path identities -/

/-- `q^1 = q` for the `Quiver.Path.compPower` of a closed path. -/
theorem compPower_one {a : V} (q : Quiver.Path a a) : Quiver.Path.compPower q 1 = q := by
  rw [Quiver.Path.compPower_succ, Quiver.Path.compPower_zero, Quiver.Path.comp_nil]

/-- `(q ^ (n+1)) · R = q · ((q ^ n) · R)`: the successor of a `compPower`, applied to a path. -/
theorem compPower_succ_comp {a w : V} (q : Quiver.Path a a) (n : ℕ) (R : Quiver.Path a w) :
    (Quiver.Path.compPower q (n + 1)).comp R = q.comp ((Quiver.Path.compPower q n).comp R) := by
  rw [Quiver.Path.compPower_succ]
  exact Quiver.Path.comp_assoc q (Quiver.Path.compPower q n) R

/-- Every factor of a reduced path occurring strictly inside it is reduced.  (More precisely: if
`U · (V · W)` is reduced then so is the middle factor `V · W`; a backtrack of `V · W` survives in
`U · (V · W)`.) -/
theorem isReduced_of_comp_mid {x a b w : V} {U : Quiver.Path x a} {Vp : Quiver.Path a b}
    {Wp : Quiver.Path b w} (h : (U.comp (Vp.comp Wp)).IsReduced) : (Vp.comp Wp).IsReduced :=
  fun Y hY => h (U.comp Y) (hY.comp_left U)

/-! ## The shape of the conclusion -/

/-- The conclusion of `decomp_of_tail` for a tail `p : Path E.right w`, isolated as a definition so
that it can be used in the induction. -/
def TailDecomp (P : Work.ORLocInd.Howie.Presentation V) (c : P.α) (E : Quiver.Total V)
    {w : V} (p : Quiver.Path E.right w) : Prop :=
  EFree P c p ∨
    ∃ (Q : Quiver.Path E.right E.left) (j : ℕ) (R : Quiver.Path E.right w),
      1 ≤ j ∧ Q.IsReduced ∧ EFree P c Q ∧ R.IsReduced ∧ EFree P c R ∧
      p = (Quiver.Path.compPower (Q.comp E.hom.toPath) j).comp R

/-! ## The first arrow of code `c` is `E` -/

/-- **The first arrow of code `c` in a tail is `E` itself.**  If `p = A · E' · p'` with `A` free of
the code `c` and `E'` of code `c`, and if the path `E · p` is reduced, then the arrow `E'` is exactly
the arrow `E` of the initial factor: the other possibility, `E' = E⁻¹`, would force `A` to be a
closed reduced `c`-free path, hence empty by the forest hypothesis, producing a backtrack with the
initial `E`. -/
theorem first_code_arrow_eq_E (P : Work.ORLocInd.Howie.Presentation V) (c : P.α)
    (hsep : P.CodeSeparates)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    (E : Quiver.Total V) (hEc : P.edgeOf E = c)
    {w d d' : V} {E' : d ⟶ d'} {A : Quiver.Path E.right d} {p' : Quiver.Path d' w}
    (hA : Work.Howie.EFree P c A) (hE' : P.edgeOf (Quiver.Total.mk d d' E') = c)
    (hred : (E.hom.toPath.comp (A.comp (E'.toPath.comp p'))).IsReduced) :
    Quiver.Total.mk d d' E' = E := by
  obtain h | h := hsep (Quiver.Total.mk d d' E') E (hE'.trans hEc.symm)
  · exact h
  · -- `E'` is the reverse of `E`: then `A` is a closed `c`-free reduced path, hence empty,
    -- and the tail begins with the reverse of `E`, a backtrack with the initial `E`.
    exfalso
    have hd : d = E.right := congrArg Quiver.Total.left h
    have hd' : d' = E.left := congrArg Quiver.Total.right h
    subst hd
    subst hd'
    have hhom : HEq E' (Quiver.reverse E.hom) :=
      ((Quiver.Total.mk.injEq E.right E.left E' E.right E.left (Quiver.reverse E.hom)).mp h).2.2
    have hE'hom : E' = Quiver.reverse E.hom := eq_of_heq hhom
    have hpred : (A.comp (E'.toPath.comp p')).IsReduced :=
      Work.Howie.isReduced_of_comp_right hred
    have hAred : A.IsReduced := Quiver.Path.IsReduced.of_comp hpred
    have hAnil : A = Quiver.Path.nil :=
      Work.Howie.closed_efree_isReduced_eq_nil P c hfor hAred hA
    rw [hAnil] at hred
    simp only [Quiver.Path.nil_comp] at hred
    rw [hE'hom] at hred
    have hdb :=
      Quiver.Path.DeleteBacktrack.intro (Quiver.Path.nil : Quiver.Path E.left E.left) E.hom p'
    rw [Quiver.Path.nil_comp] at hdb
    exact hred _ hdb

/-! ## The induction -/

/-- The tail decomposition, by strong induction on the length of the tail.  Splitting `p` at its
first arrow of code `c` (which is `E`, by `first_code_arrow_eq_E`) leaves `p = A · E · p'` with `A`
reduced and `c`-free; the induction hypothesis applies to `p'`, and the `c`-free path `Q'` it
produces is equal to `A` by uniqueness of reduced `c`-free paths between `E.right` and `E.left`. -/
theorem decomp_of_tail_aux (P : Work.ORLocInd.Howie.Presentation V) (c : P.α)
    (hsep : P.CodeSeparates)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    (E : Quiver.Total V) (hEc : P.edgeOf E = c) :
    ∀ (n : ℕ) (w : V) (p : Quiver.Path E.right w), p.length = n →
      (E.hom.toPath.comp p).IsReduced → TailDecomp P c E p := by
  intro n
  refine Nat.strong_induction_on n (fun m ihm => ?_)
  intro w p hlen hred
  rcases Work.Howie.strip_efree_decomp P c p with hpfree | ⟨d, d', A, E', p', hA, hE'c, hp⟩
  · exact Or.inl hpfree
  · right
    have hred1 : (E.hom.toPath.comp (A.comp (E'.toPath.comp p'))).IsReduced := by
      rw [← hp]; exact hred
    -- the first arrow of code `c` is `E`
    have hmk : Quiver.Total.mk d d' E' = E :=
      first_code_arrow_eq_E P c hsep hfor E hEc (E' := E') (A := A) (p' := p') hA hE'c hred1
    obtain ⟨hd, hd', hhom⟩ := (Quiver.Total.mk.injEq d d' E' E.left E.right E.hom).mp hmk
    subst hd
    subst hd'
    have hE'hom : E' = E.hom := eq_of_heq hhom
    have hp' : p = A.comp (E.hom.toPath.comp p') := by rw [hp, hE'hom]
    have hred1' : (E.hom.toPath.comp (A.comp (E.hom.toPath.comp p'))).IsReduced := by
      rw [← hp']; exact hred
    have hpred : (A.comp (E.hom.toPath.comp p')).IsReduced :=
      Work.Howie.isReduced_of_comp_right hred1'
    have hAred : A.IsReduced := hpred.of_comp
    have hred' : (E.hom.toPath.comp p').IsReduced := by
      have h1 : ((E.hom.toPath.comp A).comp (E.hom.toPath.comp p')).IsReduced := by
        rw [Quiver.Path.comp_assoc]; exact hred1'
      exact Work.Howie.isReduced_of_comp_right h1
    have hlen' : p'.length < m := by
      have h2 : p.length = A.length + (1 + p'.length) := by
        rw [hp', Quiver.Path.length_comp, Quiver.Path.length_comp, Quiver.Path.length_toPath]
      omega
    rcases ihm p'.length hlen' w p' rfl hred' with
      hp'free | ⟨Q', j', R, hj', hQ'red, hQ'free, hRred, hRfree, hpeq⟩
    · -- the tail `p'` is already `c`-free: one block
      refine ⟨A, 1, p', le_refl 1, hAred, hA, Work.Howie.isReduced_of_comp_right hred',
        hp'free, ?_⟩
      rw [hp', compPower_one]
      exact (Quiver.Path.comp_assoc A E.hom.toPath p').symm
    · -- one more block, with the same `c`-free path `Q' = A`
      have hQ'A : Q' = A :=
        Work.Howie.efree_isReduced_eq_of_same_ends P c hfor hQ'red hAred hQ'free hA
      refine ⟨A, j' + 1, R, by omega, hAred, hA, hRred, hRfree, ?_⟩
      rw [hp', hpeq, hQ'A, ← Quiver.Path.comp_assoc, compPower_succ_comp]

/-! ## The main statement -/

theorem decomp_of_tail {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (c : P.α) (hsep : P.CodeSeparates)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    (E : Quiver.Total V) (hEc : P.edgeOf E = c)
    {x w : V} {X : Quiver.Path x E.left} {p : Quiver.Path E.right w}
    (hr : (X.comp (E.hom.toPath.comp p)).IsReduced) :
    Work.Howie.EFree P c p ∨
      ∃ (Q : Quiver.Path E.right E.left) (j : ℕ) (R : Quiver.Path E.right w),
        1 ≤ j ∧ Q.IsReduced ∧ Work.Howie.EFree P c Q ∧ R.IsReduced ∧ Work.Howie.EFree P c R ∧
        p = (Quiver.Path.compPower (Q.comp E.hom.toPath) j).comp R :=
  decomp_of_tail_aux P c hsep hfor E hEc p.length w p rfl (isReduced_of_comp_mid hr)

end Work.Howie
