/-
  WilC4/CritFibreDefinable : the fibre `Cfib Y c` of a `∅`-definable family is `∅`-definable.

  The language `LRc = LR[[ℝ]]` names every real as a constant, so the "parametric" fibre of a
  `∅`-definable family `Y ⊆ ℝ^{k+2}` at a *real* parameter tuple `c` is again `∅`-definable.  This
  is what makes the `∅`-definable monotonicity theorem (`mono_real` / `monoOn_main`, which speak
  about `∅`-definable subsets of `ℝ²`) applicable to the fibre of `Y` at `c` — the point of the
  lemmas `crit_mono_onesided` and `crit_fail_mem_bad`.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- The constant map `Fin 2 → ℝ` with value `r` is `∅`-definable in `LRc` (the constant `r` is
named by the constant symbol `LR.con r`). -/
lemma definableFun_const_LRc (r : ℝ) :
    (∅ : Set ℝ).DefinableFun LRc (fun (_ : Fin 2 → ℝ) => r) := by
  rw [Set.empty_definableFun_iff]
  refine ⟨(Term.var none).equal (FirstOrder.Language.Constants.term
    (show LRc.Constants from WilkiesDesign.CG.LR.con r)), ?_⟩
  ext p
  have h : ((show LRc.Constants from WilkiesDesign.CG.LR.con r) : ℝ) = r := rfl
  simp [Function.tupleGraph, h, eq_comm]

/-- **The fibre of a `∅`-definable family at a real parameter is `∅`-definable.**  The fibre
`Cfib Y c = {v : Fin 2 → ℝ | Fin.cons (v 0) (Fin.cons (v 1) c) ∈ Y}` is the preimage of `Y`
under the map `v ↦ Fin.cons (v 0) (Fin.cons (v 1) c)`, whose coordinates are projections and the
constants `c j`. -/
theorem cfib_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (c : Fin k → ℝ) :
    (∅ : Set ℝ).Definable LRc (Cfib Y c) := by
  have hF : (∅ : Set ℝ).DefinableMap LRc
      (fun v : Fin 2 → ℝ => Fin.cons (v 0) (Fin.cons (v 1) c)) := by
    intro i
    induction i using Fin.cases with
    | zero => simpa using FirstOrder.Language.definableFun_var LRc (0 : Fin 2)
    | succ j =>
      induction j using Fin.cases with
      | zero => simpa using FirstOrder.Language.definableFun_var LRc (1 : Fin 2)
      | succ j' => simpa using definableFun_const_LRc (c j')
  exact hY.preimage_map hF

end Work.WilC4
