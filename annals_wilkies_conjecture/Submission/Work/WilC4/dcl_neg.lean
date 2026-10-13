/-
  WilC4 : area C4 of `annals_wilkies_conjecture` (Wilkie's valuation inequality for `TR`).

  The definable closure `Dcl S A` is closed under negation: if `x` is definable from the
  parameters `S ∪ A`, then so is `-x`.

  The language `LRc` has the ring language as a reduct, so `y ↦ -y` is a term (`negFunc`)
  and its graph is definable without parameters; the element `-x` is the projection of the
  parameter-definable set `{(z, u) | u = x, z = -u}`.  Unlike inversion no hypothesis `x ≠ 0`
  is needed: negation is defined everywhere on the field.
-/
import Mathlib
import Submission.Work.WilC4.Defs

set_option autoImplicit false

namespace Work.WilC4

open FirstOrder FirstOrder.Language WilkiesDesign WilkiesDesign.CG

/-- The definable closure `Dcl S A` is closed under negation: `Dcl` is closed under
`LRc`-definable functions, and `-x` is witnessed by the `LRc` term `-(v (inr 0))` applied to
the (definable) parameter `x`.

Concretely, `{fun _ : Fin 1 => -x}` is the projection onto the first (`inl`) coordinate of the
set of pairs `(z, u)` with `u = x` and `z = -u`: the second condition is the graph of the ring
term `negFunc`, hence definable without parameters, the first is the preimage of the definable
singleton `{x}` under the projection `w ↦ w ∘ Sum.inr`, and definability survives the finite
existential quantification `∃ u : Fin 1 → M` (`Set.Definable.exists_of_finite`). -/
theorem dcl_neg {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {S A : Set M} {x : M} (hx : x ∈ Dcl S A) : -x ∈ Dcl S A := by
  show (S ∪ A).Definable LRc {fun _ : Fin 1 => -x}
  -- `LRc`-term computing the negation of the `Sum.inr`-coordinate of `Fin 1 ⊕ Fin 1 → M`.
  have hnegterm : (fun v : (Fin 1 ⊕ Fin 1) → M => - v (Sum.inr 0)) =
      (((Language.lhomWithConstants (Language.ring.sum rexpL) ℝ).onTerm
        ((LHom.sumInl : Language.ring →ᴸ Language.ring.sum rexpL).onTerm
          (-(Term.var (Sum.inr 0)))))).realize := by
    funext v
    rw [LHom.realize_onTerm, LHom.realize_onTerm]
    simp
  -- the graph of that negation is definable (without parameters)
  have hnegdef : (S ∪ A).Definable LRc
      {v : (Fin 1 ⊕ Fin 1) → M | v (Sum.inl 0) = - v (Sum.inr 0)} := by
    have h2 : (S ∪ A).DefinableFun LRc (fun v : (Fin 1 ⊕ Fin 1) → M => - v (Sum.inr 0)) := by
      rw [hnegterm]
      exact (Term.definableFun_realize _).of_empty
    have h1 : (S ∪ A).DefinableFun LRc (fun v : (Fin 1 ⊕ Fin 1) → M => v (Sum.inl 0)) :=
      Set.DefinableFun.proj (L := LRc) (A := S ∪ A) (i := Sum.inl 0)
    exact Set.DefinableFun.ofPred_eq h1 h2
  -- the condition that the `inr`-coordinate holds the parameter `x`
  have hgx : (S ∪ A).Definable LRc {v : (Fin 1 ⊕ Fin 1) → M | v (Sum.inr 0) = x} := by
    have h := hx.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    convert h using 1
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hv
      funext i
      rw [Subsingleton.elim i 0]
      exact hv
    · intro hv
      have := congr_fun hv 0
      simpa using this
  have hInt := hnegdef.inter hgx
  -- project out the existentially quantified `inr`-coordinate
  have hProj := Set.Definable.exists_of_finite hInt
  have hset : {v : Fin 1 → M | ∃ u : Fin 1 → M, Sum.elim v u ∈
      ({v : (Fin 1 ⊕ Fin 1) → M | v (Sum.inl 0) = - v (Sum.inr 0)} ∩
       {v : (Fin 1 ⊕ Fin 1) → M | v (Sum.inr 0) = x})} = {fun _ : Fin 1 => -x} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_singleton_iff,
      Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨u, h1, h2⟩
      have hv : v 0 = -x := by rw [h1, h2]
      funext i
      rw [Subsingleton.elim i 0]
      exact hv
    · intro hv
      refine ⟨fun _ => x, ?_, rfl⟩
      simp [hv]
  rw [hset] at hProj
  exact hProj

end Work.WilC4
