import Mathlib
import Submission.Work.WilC4.Defs

set_option autoImplicit false

namespace Work.WilC4

open FirstOrder FirstOrder.Language WilkiesDesign.CG

/-- The definable closure `Dcl S A` is closed under addition: `Dcl` is closed under
`LRc`-definable functions, and the sum is witnessed by the `LRc` term `v (inr 0) + v (inr 1)`
applied to the (definable) pair `(x, y)`.

Concretely, `{fun _ : Fin 1 => x + y}` is the projection onto the first coordinate of the set of
triples `(z, u₀, u₁)` with `u₀ = x`, `u₁ = y`, `z = u₀ + u₁`; that set is definable (each of the
three conditions is a preimage of a definable singleton, resp. an instance of
`Set.DefinableFun.ofPred_eq` for the term-graph of addition), and definability survives the
finite existential quantification `∃ u : Fin 2 → M` (`Set.Definable.exists_of_finite`). -/
theorem dcl_add {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] {S A : Set M} {x y : M}
    (hx : x ∈ Dcl S A) (hy : y ∈ Dcl S A) : x + y ∈ Dcl S A := by
  -- `LRc`-term computing the sum of the two `Sum.inr`-coordinates of `Fin 1 ⊕ Fin 2 → M`.
  have haddterm : (fun v : (Fin 1 ⊕ Fin 2) → M => v (Sum.inr 0) + v (Sum.inr 1)) =
      (((Language.lhomWithConstants (Language.ring.sum rexpL) ℝ).onTerm
        ((LHom.sumInl : Language.ring →ᴸ Language.ring.sum rexpL).onTerm
          ((Term.var (Sum.inr 0)) + (Term.var (Sum.inr 1)))))).realize := by
    funext v
    rw [LHom.realize_onTerm, LHom.realize_onTerm]
    simp
  -- the graph of that sum is definable
  have hadddef : (S ∪ A).Definable LRc
      {v : (Fin 1 ⊕ Fin 2) → M | v (Sum.inl 0) = v (Sum.inr 0) + v (Sum.inr 1)} := by
    have h2 : (S ∪ A).DefinableFun LRc
        (fun v : (Fin 1 ⊕ Fin 2) → M => v (Sum.inr 0) + v (Sum.inr 1)) := by
      rw [haddterm]
      exact (Term.definableFun_realize _).of_empty
    have h1 : (S ∪ A).DefinableFun LRc (fun v : (Fin 1 ⊕ Fin 2) → M => v (Sum.inl 0)) :=
      Set.DefinableFun.proj (L := LRc) (A := S ∪ A) (i := Sum.inl 0)
    exact Set.DefinableFun.ofPred_eq h1 h2
  -- `u₀ = x`
  have hgx : (S ∪ A).Definable LRc
      {v : (Fin 1 ⊕ Fin 2) → M | v (Sum.inr 0) = x} := by
    have h := (hx.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))).preimage_comp
      (Sum.inr : Fin 2 → Fin 1 ⊕ Fin 2)
    convert h using 1
    ext v
    simp [Set.mem_preimage, Function.comp_def, funext_iff]
  -- `u₁ = y`
  have hgy : (S ∪ A).Definable LRc
      {v : (Fin 1 ⊕ Fin 2) → M | v (Sum.inr 1) = y} := by
    have h := (hy.preimage_comp (fun _ : Fin 1 => (1 : Fin 2))).preimage_comp
      (Sum.inr : Fin 2 → Fin 1 ⊕ Fin 2)
    convert h using 1
    ext v
    simp [Set.mem_preimage, Function.comp_def, funext_iff]
  have hS' : (S ∪ A).Definable LRc
      ({v : (Fin 1 ⊕ Fin 2) → M | v (Sum.inr 0) = x} ∩
          {v : (Fin 1 ⊕ Fin 2) → M | v (Sum.inr 1) = y} ∩
          {v : (Fin 1 ⊕ Fin 2) → M | v (Sum.inl 0) = v (Sum.inr 0) + v (Sum.inr 1)}) :=
    (hgx.inter hgy).inter hadddef
  -- project onto the first coordinate
  have hex := hS'.exists_of_finite (α := Fin 1) (β := Fin 2)
  have key : (S ∪ A).Definable LRc {v : Fin 1 → M | v 0 = x + y} := by
    convert hex using 1
    ext v
    constructor
    · intro hv
      simp only [Set.mem_ofPred_eq] at hv
      refine ⟨![x, y], ⟨⟨?_, ?_⟩, ?_⟩⟩
      · simp
      · simp
      · simpa using hv
    · rintro ⟨u, ⟨⟨h1, h2⟩, h3⟩⟩
      simp only [Sum.elim_inl, Sum.elim_inr, Set.mem_ofPred_eq] at h1 h2 h3
      change v 0 = x + y
      rw [h3, h1, h2]
  have hset : ({fun _ : Fin 1 => x + y} : Set (Fin 1 → M)) =
      {v : Fin 1 → M | v 0 = x + y} := by
    ext v; simp [funext_iff]
  have hif : x + y ∈ Dcl S A ↔
      (S ∪ A).Definable LRc {fun _ : Fin 1 => x + y} := Iff.rfl
  rw [hif, hset]
  exact key

end Work.WilC4
