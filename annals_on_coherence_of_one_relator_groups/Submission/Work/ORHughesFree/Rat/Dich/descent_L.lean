import Mathlib
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Ugen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid
import Submission.Work.ORHughesFree.Rat.PhiCoset

/-!
# Descent along a left translate of a word over the `V`-letters

`descent_L` is the "left" descent step of the dichotomy for the translate fibres of `Rat.A V`
(`V ≤ U` a subgroup): if `B = [x₁, …, xₙ]` is a non-empty word whose letters all lie in `Rat.A V`,
are non-zero, and have complexity `< T`, and if the corresponding point of `U ♮ X`
(the product of the `X`-letters of `B`) can be left-multiplied by `Ugen g` staying inside the
`V`-part `NUV V` of `U ♮ X`, then `g ∈ V`.

The proof is an induction on the word, driven by the first-letter recursion
`Xgen_mem_closure_iff V a q : Xgen a * q ∈ NUV V ↔ ∃ v, actR v a ∈ A V ∧ Ugen v⁻¹ * q ∈ NUV V`.
Writing `Ugen g * wprod (x :: l) = Xgen (actL g x) * wprod l` with `actL g x = x * ofGroup g⁻¹`,
the recursion produces `v` with

  `ofGroup v⁻¹ * x * ofGroup g⁻¹ ∈ Rat.A V`   and   `Ugen v⁻¹ * wprod l ∈ NUV V`.

The induction hypothesis applied to the tail `l` gives `v ∈ V`, hence `ofGroup v ∈ Rat.A V`, and
multiplying the first membership by `ofGroup v` (inside the subsemiring `Rat.A V`) yields

  `x * ofGroup g⁻¹ ∈ Rat.A V`.

The induction hypothesis `hISS` at the head `x` — `x ∈ Rat.A V`, `x ≠ 0`, `treeOfRat x < T` — now
gives `g⁻¹ ∈ V`, i.e. `g ∈ V`.

The *right* half of `hISS` (the one about `y * ofGroup w`) is the part used; the hypothesis `hP`
of `descent_L` (membership of the word itself in `NUV V`) is not needed by this argument.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat.Dich

open Work.ORHughesFree
open Work.ORHughesFree.Rat
open Work.ORHughesFree.Rat.FreeProduct

/-- **The left translate of a good word.** If every letter of the list `l` lies in `Rat.A V`, is
non-zero and has complexity `< T`, then every `g` with `Ugen g * wprod l ∈ NUV V` lies in `V`. -/
theorem leftTranslate_subset_V {U : Type} [Group U] {V : Subgroup U}
    {T : Work.ORHughesFree.Tree}
    (hISS : ∀ y : Work.ORHughesFree.RatU U, Work.ORHughesFree.Tree.lt
      (Work.ORHughesFree.Rat.treeOfRat U y) T → y ≠ 0 →
      ((∀ w : U, y ∈ Work.ORHughesFree.Rat.A V →
          y * Work.ORHughesFree.RatU.ofGroup w ∈ Work.ORHughesFree.Rat.A V → w ∈ V) ∧
       (∀ w : U, y ∈ Work.ORHughesFree.Rat.A V →
          Work.ORHughesFree.RatU.ofGroup w * y ∈ Work.ORHughesFree.Rat.A V → w ∈ V))) :
    ∀ l : List (Work.ORHughesFree.RatU U),
      (∀ y ∈ l, y ∈ Work.ORHughesFree.Rat.A V ∧ y ≠ 0 ∧
        Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Rat.treeOfRat U y) T) →
      ∀ g : U, Work.ORHughesFree.Rat.FreeProduct.NU.Ugen g *
        Work.ORHughesFree.Rat.wprod l ∈ Work.ORHughesFree.Rat.Orbit.NUV V → g ∈ V := by
  intro l
  induction l with
  | nil =>
    intro _ g hg
    rw [wprod_nil, mul_one] at hg
    exact (Ugen_mem_NUV_iff V g).mp hg
  | cons x rest ih =>
    intro hl g hg
    -- peel off the head: `Ugen g * wprod (x :: rest) = Xgen (actL g x) * wprod rest`
    rw [wprod_cons, ← mul_assoc, NU.Ugen_mul_Xgen] at hg
    obtain ⟨v, hv1, hv2⟩ := (Xgen_mem_closure_iff V (actL g x) (wprod rest)).mp hg
    have hx := hl x List.mem_cons_self
    have hrest : ∀ y ∈ rest, y ∈ Rat.A V ∧ y ≠ 0 ∧ Tree.lt (treeOfRat U y) T :=
      fun y hy => hl y (List.mem_cons_of_mem x hy)
    -- the induction hypothesis at the tail, with `g := v⁻¹`
    have hvv : v ∈ V := by
      have h1 : v⁻¹ ∈ V := ih hrest v⁻¹ hv2
      simpa using V.inv_mem h1
    -- `ofGroup v⁻¹ * x * ofGroup g⁻¹ ∈ A V` and `ofGroup v ∈ A V`: multiply
    have hxAg : x * RatU.ofGroup g⁻¹ ∈ Rat.A V := by
      have hmul : RatU.ofGroup v * actR v (actL g x) ∈ Rat.A V :=
        (Weak.ASub V).mul_mem (Weak.A_ofGroup_mem hvv) hv1
      have heq : RatU.ofGroup v * actR v (actL g x) = x * RatU.ofGroup g⁻¹ := by
        rw [actR, actL, ← mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one,
          one_mul]
      rwa [heq] at hmul
    -- the descent hypothesis at the head
    have hginv : g⁻¹ ∈ V := (hISS x hx.2.2 hx.2.1).1 g⁻¹ hx.1 hxAg
    simpa using V.inv_mem hginv

theorem descent_L {U : Type} [Group U] {V : Subgroup U} {T : Work.ORHughesFree.Tree}
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
        ⟨Work.ORHughesFree.Rat.FreeProduct.mulFirst g B,
          Work.ORHughesFree.Rat.FreeProduct.mulFirst_ne_nil g hB⟩) :
        Work.ORHughesFree.Rat.FreeProduct.NU U) ∈ Work.ORHughesFree.Rat.Orbit.NUV V) :
    g ∈ V := by
  have hp : FreeProduct.NU.Ugen g * wprod B ∈ Orbit.NUV V := by
    -- `Ugen g * wprod B = Ugen g * ⟦B⟧ = ⟦mulFirst g B⟧`, which is the hypothesis `hPg`
    have h1 : FreeProduct.NU.Ugen g *
        (Sum.inr (Quotient.mk (FreeProduct.relNESetoid U) ⟨B, hB⟩) :
          FreeProduct.NU U) ∈ Orbit.NUV V := by
      rw [FreeProduct.NU.inl_mul_mk]
      exact hPg
    have h2 : wprod B = (Sum.inr (Quotient.mk (FreeProduct.relNESetoid U) ⟨B, hB⟩) :
        FreeProduct.NU U) := listProd_Xgen_eq_mk B hB
    rw [h2]
    exact h1
  exact leftTranslate_subset_V hISS B hgood g hp

end Work.ORHughesFree.Rat.Dich
