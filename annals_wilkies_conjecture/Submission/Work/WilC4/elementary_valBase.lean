import Mathlib
import Submission.Work.WilC4.Defs

/-!
# The carrier of an elementary substructure is a value base

`IsValBase S` says that `Γ S = {ν c : c ∈ S, c ≠ 0}` is a subgroup of the value group, which
concretely means `1 ∈ S`, `S` is closed under multiplication, and `S` is closed under inversion.

For the carrier of an `LRc`-elementary substructure `S ≼ M` of a field `M`:

* `1 ∈ S` and `x * y ∈ S` are the interpretation of the *constant* symbol `1` and of the
  *binary function* symbol `*` of the ring part of `LRc`, so they are instances of the closure
  of a substructure under function symbols (`Substructure.fun_mem`);

* `x⁻¹ ∈ S` is *not* a function symbol of the language (the language of rings has no inversion),
  but inversion is definable: the set `{y : M | x * y = 1}` is definable over `S` as soon as
  `x ∈ S`, and an elementary substructure meets every definable set
  (`FirstOrder.Language.ElementarySubstructure.meetsDefinable`).

The auxiliary statement `elementary_valBase_aux` is phrased with the carrier presented as
`↑↑S` (the coercion through `LRc.Substructure M`); this is the form in which
`Substructure.fun_mem` produces elements.  It is definitionally the same set, so the requested
statement `elementary_valBase` follows immediately.
-/

namespace Work.WilC4

open FirstOrder FirstOrder.Language

set_option backward.isDefEq.respectTransparency false in
theorem elementary_valBase_aux {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) :
    IsValBase (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `1` is the interpretation of the constant symbol `1` of `LRc`
    have h := (S : WilkiesDesign.CG.LRc.Substructure M).fun_mem
      (f := (Sum.inl (Sum.inl Ring.oneFunc) : WilkiesDesign.CG.LRc.Functions 0))
      (x := (fun i : Fin 0 => i.elim0)) (by intro i; exact i.elim0)
    simpa using h
  · -- closure under inversion, via definability of `y ↦ x * y = 1`
    intro x hx hx0
    have h1 : (1 : M) ∈ (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M)) := by
      have h := (S : WilkiesDesign.CG.LRc.Substructure M).fun_mem
        (f := (Sum.inl (Sum.inl Ring.oneFunc) : WilkiesDesign.CG.LRc.Functions 0))
        (x := (fun i : Fin 0 => i.elim0)) (by intro i; exact i.elim0)
      simpa using h
    have hdef : (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M)).Definable₁
        WilkiesDesign.CG.LRc {y : M | x * y = 1} := by
      change (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M)).Definable
        WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ ({y : M | x * y = 1})}
      -- `v ↦ funMap mul ![x, v 0]` is a definable function of `v`
      have hf : (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M)).DefinableFun
          WilkiesDesign.CG.LRc
          (Structure.funMap (Sum.inl (Sum.inl Ring.mulFunc) : WilkiesDesign.CG.LRc.Functions 2)) :=
        (Set.DefinableFun.fun_symbol (L := WilkiesDesign.CG.LRc) _).mono (Set.empty_subset _)
      have hg : (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M)).DefinableMap
          WilkiesDesign.CG.LRc (fun v : Fin 1 → M => ![x, v 0]) := by
        intro i
        fin_cases i
        · simpa using (definableFun_const WilkiesDesign.CG.LRc
            (A := (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M))) (γ := Fin 1) hx)
        · simpa using (Set.DefinableFun.proj WilkiesDesign.CG.LRc
            (A := (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M))) (α := Fin 1) (i := 0))
      have hfin := Set.DefinableFun.ofPred_eq_const
        (A := (((S : WilkiesDesign.CG.LRc.Substructure M) : Set M))) (hf.comp hg) h1
      convert hfin using 1
      ext v
      simp
    -- the elementary substructure meets the definable set `{y | x * y = 1}`
    obtain ⟨y, hyD, hyS⟩ :=
      (FirstOrder.Language.ElementarySubstructure.meetsDefinable (L := WilkiesDesign.CG.LRc) S)
        {y : M | x * y = 1} ⟨x⁻¹, by simp [mul_inv_cancel₀ hx0]⟩ hdef
    have hyeq : y = x⁻¹ := mul_left_cancel₀ hx0 (by rw [hyD, mul_inv_cancel₀ hx0])
    rw [hyeq] at hyS
    exact hyS
  · -- closure under multiplication, the binary function symbol `*` of `LRc`
    intro x hx y hy
    have h := (S : WilkiesDesign.CG.LRc.Substructure M).fun_mem
      (f := (Sum.inl (Sum.inl Ring.mulFunc) : WilkiesDesign.CG.LRc.Functions 2))
      (x := ![x, y]) (by intro i; fin_cases i <;> assumption)
    simpa using h

theorem elementary_valBase {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) : IsValBase (S : Set M) :=
  elementary_valBase_aux S

end Work.WilC4
