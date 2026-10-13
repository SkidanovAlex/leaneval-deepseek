import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.dcl_mul
import Submission.Work.WilC4.dcl_inv

set_option autoImplicit false

namespace Work.WilC4

open FirstOrder FirstOrder.Language WilkiesDesign WilkiesDesign.CG

/-- `(1 : M) ∈ T` for a `dcl`-closed `T`.

The elements of `T` are exactly the `LRc`-definable elements of the parameter set `T`, so it
suffices to see that the constant `1` is definable from the empty parameter set, and hence from
any parameter set.  The language `LRc` contains the language of rings *and* constant symbols for
the reals, so the constant `1` is not directly a nullary symbol of `LRc`: it is the image of the
nullary ring symbol `1` under the language inclusion `ring →ᴸ LR →ᴸ LRc`.  Accordingly the
definable set `{v : Fin 1 → M | v 0 = 1}` is first produced in the language of rings (from the
projection `v ↦ v 0` and the nullary term `1`), and then pushed forward along the two language
inclusions with `Set.Definable.map_expansion`. -/
theorem one_mem_of_dcl_closed {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] {T : Set M}
    (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) : (1 : M) ∈ T := by
  -- `{v : Fin 1 → M | v 0 = 1}` is definable without parameters in the language of rings:
  -- the projection `v ↦ v 0` and the constant `v ↦ 1` are both definable functions.
  have hdef : (∅ : Set M).Definable LRc {fun _ : Fin 1 => (1 : M)} := by
    have hproj : (∅ : Set M).DefinableFun Language.ring (fun v : Fin 1 → M => v 0) :=
      Set.DefinableFun.proj (L := Language.ring) (A := (∅ : Set M)) (i := 0)
    have hone : (∅ : Set M).DefinableFun Language.ring (fun _ : Fin 1 → M => (1 : M)) := by
      have h := Term.definableFun_realize (M := M) (L := Language.ring)
        (1 : Language.ring.Term (Fin 1))
      convert h using 1
      funext v
      simp
    have hring : (∅ : Set M).Definable Language.ring {v : Fin 1 → M | v 0 = 1} :=
      hproj.ofPred_eq hone
    have h1 : (∅ : Set M).Definable (Language.ring.sum rexpL) {v : Fin 1 → M | v 0 = 1} :=
      hring.map_expansion (LHom.sumInl : Language.ring →ᴸ Language.ring.sum rexpL)
    have h2 : (∅ : Set M).Definable LRc {v : Fin 1 → M | v 0 = 1} :=
      h1.map_expansion (Language.lhomWithConstants (Language.ring.sum rexpL) ℝ)
    rw [const_tuple_set (1 : M)]
    exact h2
  refine (hTdcl 1).mp ?_
  rw [DefinableElt, Set.union_empty]
  exact hdef.mono (Set.empty_subset T)

/-- **A `dcl`-closed set is a value base.**

`IsValBase T` says that `Γ T = {ν c : c ∈ T, c ≠ 0}` is a subgroup of the value group, i.e. that
`1 ∈ T` and that `T` is closed under multiplication and inversion.  All three are instances of the
closure of `T` under `LRc`-definable functions: `1` is definable from the empty parameter set
(`one_mem_of_dcl_closed`), while for `x ∈ T` the elements `x⁻¹` (`dcl_inv`, using `x ≠ 0` to make
`{y | x * y = 1}` the singleton `{x⁻¹}`) and `x * y` (`dcl_mul`, multiplication being a function
symbol of the ring part of `LRc`) are definable from the parameter set `T ∪ ∅`, hence lie in `T`
because `T` is `dcl`-closed. -/
theorem valBase_of_dcl_closed {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {T : Set M} (hTdcl : ∀ x : M, Work.WilC4.DefinableElt T ∅ x ↔ x ∈ T) : Work.WilC4.IsValBase T := by
  refine ⟨one_mem_of_dcl_closed hTdcl, ?_, ?_⟩
  · intro x hx hx0
    exact (hTdcl x⁻¹).mp (dcl_inv ((hTdcl x).mpr hx) hx0)
  · intro x hx y hy
    exact (hTdcl (x * y)).mp (dcl_mul ((hTdcl x).mpr hx) ((hTdcl y).mpr hy))

end Work.WilC4
