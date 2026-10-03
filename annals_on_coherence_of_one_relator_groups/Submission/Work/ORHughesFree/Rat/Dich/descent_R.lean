import Mathlib
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Ugen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid
import Submission.Work.ORHughesFree.Rat.mem_NUV_of_relNE

namespace Work.ORHughesFree.Rat.Dich

open Work.ORHughesFree
open Work.ORHughesFree.Rat
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-!
# Right descent for a list of good `Rat(U)`-elements

This file proves `descent_R`, the "right" descent step of the source theory of [DHS04, §5] as
formalised through the word model `U ♮ X`.

The statement is the following.  Let `V ≤ U`, let `T` be a tree, and suppose that every non-zero
`y ∈ Rat(A V)` of complexity `< T` is "`V`-closed under division": `y * φw ∈ A V` and `φw * y ∈ A V`
both force `w ∈ V` (`hISS`, the transfinite-induction hypothesis of [DHS04, Definition 5.3]).  Let
`B` be a non-empty list of such `y`, and let `g : U`.  If the word `⟦B⟧ ∈ U ♮ X` lies in the
`V`-part `NUV V`, and so does the word `⟦mulLast B g⟧ = ⟦B⟧ * Ugen g` obtained by appending the
group letter `g` on the right, then `g ∈ V`.

The proof is an induction on the list, peeling the first `X`-letter of *both* words with the
first-letter recursion `Xgen_mem_closure_iff`.  In the degenerate case `B = [x]` the appended word
is the single letter `Xgen (actR g x)`, so `actR g x = φ(g⁻¹) * x ∈ A V`, and `hISS` applied to `x`
(with `w = g⁻¹`) gives `g⁻¹ ∈ V`.  In the step `B = x :: C` we get `φ(v⁻¹) * x ∈ A V` with
`φ(v⁻¹) ∈ NUV V` for both words, whence `v ∈ V` by `hISS`, and cancelling the common left factor
`Ugen v` exhibits the two shorter words `⟦C⟧` and `⟦mulLast C g⟧ = ⟦C⟧ * Ugen g` in `NUV V`, to
which the induction hypothesis applies.
-/

/-- **Right descent, list form**: for a non-empty list `C` of non-zero elements of `A V` of
complexity `< T`, if both `⟦C⟧` and `⟦mulLast C g⟧ = ⟦C⟧ * Ugen g` lie in `NUV V` then `g ∈ V`. -/
private theorem descent_R_aux {V : Subgroup U} {T : Tree}
    (hISS : ∀ y : RatU U, Tree.lt (treeOfRat U y) T → y ≠ 0 →
      ((∀ w : U, y ∈ A V → y * RatU.ofGroup w ∈ A V → w ∈ V) ∧
       (∀ w : U, y ∈ A V → RatU.ofGroup w * y ∈ A V → w ∈ V))) :
    ∀ C : List (RatU U), C ≠ [] →
      (∀ y ∈ C, y ∈ A V ∧ y ≠ 0 ∧ Tree.lt (treeOfRat U y) T) →
      ∀ g : U,
        List.prod (C.map FreeProduct.NU.Xgen) ∈ Orbit.NUV V →
        List.prod ((FreeProduct.mulLast C g).map FreeProduct.NU.Xgen) ∈ Orbit.NUV V →
        g ∈ V := by
  intro C
  induction C with
  | nil => intro hC; exact absurd rfl hC
  | cons x C' ih =>
    intro _ hgood g hX hXg
    obtain ⟨hxA, hxne, hxT⟩ := hgood x (by simp)
    cases C' with
    | nil =>
      -- `C = [x]`: the appended word is the single letter `Xgen (actR g x)`
      have hmem : FreeProduct.actR g x ∈ A V := by
        refine (Xgen_mem_NUV_iff V (FreeProduct.actR g x)).mp ?_
        simpa only [FreeProduct.mulLast, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one] using hXg
      have hinv : g⁻¹ ∈ V := (hISS x hxT hxne).2 g⁻¹ hxA hmem
      simpa using V.inv_mem hinv
    | cons y ys =>
      have hC' : (y :: ys) ≠ [] := by simp
      have hgood' : ∀ z ∈ (y :: ys), z ∈ A V ∧ z ≠ 0 ∧ Tree.lt (treeOfRat U z) T :=
        fun z hz => hgood z (by simp [hz])
      -- peel the first letter of `⟦C⟧`
      have h1 : FreeProduct.NU.Xgen x * List.prod ((y :: ys).map FreeProduct.NU.Xgen)
          ∈ Orbit.NUV V := by
        simpa only [List.map_cons, List.prod_cons] using hX
      obtain ⟨v, hvA, hvq⟩ :=
        (Xgen_mem_closure_iff V x (List.prod ((y :: ys).map FreeProduct.NU.Xgen))).mp h1
      have hvV : v⁻¹ ∈ V := (hISS x hxT hxne).2 v⁻¹ hxA hvA
      have hvmem : v ∈ V := by simpa using V.inv_mem hvV
      -- peel the first letter of `⟦mulLast C g⟧`
      have hml : FreeProduct.mulLast (x :: y :: ys) g
          = x :: FreeProduct.mulLast (y :: ys) g :=
        FreeProduct.NU.mulLast_cons_ne_nil g x (y :: ys) (by simp)
      have h2 : FreeProduct.NU.Xgen x
            * List.prod ((FreeProduct.mulLast (y :: ys) g).map FreeProduct.NU.Xgen)
          ∈ Orbit.NUV V := by
        rw [hml] at hXg
        simpa only [List.map_cons, List.prod_cons] using hXg
      obtain ⟨v', hv'A, hv'q⟩ :=
        (Xgen_mem_closure_iff V x
          (List.prod ((FreeProduct.mulLast (y :: ys) g).map FreeProduct.NU.Xgen))).mp h2
      have hv'V : v'⁻¹ ∈ V := (hISS x hxT hxne).2 v'⁻¹ hxA hv'A
      have hv'mem : v' ∈ V := by simpa using V.inv_mem hv'V
      -- cancel the common left factors `Ugen v`, `Ugen v'`
      have hq : List.prod ((y :: ys).map FreeProduct.NU.Xgen) ∈ Orbit.NUV V := by
        have hmem : FreeProduct.NU.Ugen v ∈ Orbit.NUV V := Orbit.Ugen_mem_NUV hvmem
        have hkey : FreeProduct.NU.Ugen v * FreeProduct.NU.Ugen v⁻¹ = 1 := by
          rw [FreeProduct.NU.Ugen_mul, mul_inv_cancel]
          rfl
        have h := (Orbit.NUV V).mul_mem hmem hvq
        rwa [← mul_assoc, hkey, one_mul] at h
      have hqg : List.prod ((FreeProduct.mulLast (y :: ys) g).map FreeProduct.NU.Xgen)
          ∈ Orbit.NUV V := by
        have hmem : FreeProduct.NU.Ugen v' ∈ Orbit.NUV V := Orbit.Ugen_mem_NUV hv'mem
        have hkey : FreeProduct.NU.Ugen v' * FreeProduct.NU.Ugen v'⁻¹ = 1 := by
          rw [FreeProduct.NU.Ugen_mul, mul_inv_cancel]
          rfl
        have h := (Orbit.NUV V).mul_mem hmem hv'q
        rwa [← mul_assoc, hkey, one_mul] at h
      exact ih hC' hgood' g hq hqg

theorem descent_R {U : Type} [Group U] {V : Subgroup U} {T : Work.ORHughesFree.Tree}
    (hISS : ∀ y : Work.ORHughesFree.RatU U, Work.ORHughesFree.Tree.lt
      (Work.ORHughesFree.Rat.treeOfRat U y) T → y ≠ 0 →
      ((∀ w : U, y ∈ Work.ORHughesFree.Rat.A V →
          y * Work.ORHughesFree.RatU.ofGroup w ∈ Work.ORHughesFree.Rat.A V → w ∈ V) ∧
       (∀ w : U, y ∈ Work.ORHughesFree.Rat.A V →
          Work.ORHughesFree.RatU.ofGroup w * y ∈ Work.ORHughesFree.Rat.A V → w ∈ V)))
    (B : List (Work.ORHughesFree.RatU U)) (hB : B ≠ [])
    (hgood : ∀ y ∈ B, y ∈ Work.ORHughesFree.Rat.A V ∧ y ≠ 0 ∧
      Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U y) T)
    (g : U)
    (hP : (Sum.inr (Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U) ⟨B, hB⟩) :
        Work.ORHughesFree.Rat.FreeProduct.NU U) ∈ Work.ORHughesFree.Rat.Orbit.NUV V)
    (hPg : (Sum.inr (Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U)
        ⟨Work.ORHughesFree.Rat.FreeProduct.mulLast B g,
          Work.ORHughesFree.Rat.FreeProduct.mulLast_ne_nil g hB⟩) :
        Work.ORHughesFree.Rat.FreeProduct.NU U) ∈ Work.ORHughesFree.Rat.Orbit.NUV V) :
    g ∈ V := by
  have hP' : List.prod (B.map FreeProduct.NU.Xgen) ∈ Orbit.NUV V := by
    rw [map_Xgen_prod_eq_mk B hB]; exact hP
  have hPg' : List.prod ((FreeProduct.mulLast B g).map FreeProduct.NU.Xgen) ∈ Orbit.NUV V := by
    rw [map_Xgen_prod_eq_mk (FreeProduct.mulLast B g) (FreeProduct.mulLast_ne_nil g hB)]
    exact hPg
  exact descent_R_aux hISS B hB hgood g hP' hPg'

end Work.ORHughesFree.Rat.Dich
