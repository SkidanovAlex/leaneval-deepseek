import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.FirstPageCF.ZsqElts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Bsq` contains the classes represented by relative cycles with a lift, modulo boundaries

The model `Bsq ξ s n ⊆ (F_s/F_{s-1})_n` of the boundaries of the second page is

`Bsq ξ s n = projQ ({y ∈ F_s : Finc y ∈ ∂(F_{s+1})})`.

The lemma proved here records two elementary facts about it:

* the class `projQ x` of any chain `x ∈ F_s` admitting `e ∈ F_{s+1}` with `∂e = Finc x` lies in
  `Bsq` (this is `x + ∂y` with `y` a lift of the boundary correction);
* consequently `z ∈ Bsq` whenever `z` differs from such a class `projQ x` by a boundary of the
  graded piece `grF ξ.F s` (the image of `d : (grF ξ.F s)_{n+1} → (grF ξ.F s)_n`).

The argument is purely at the chain level: `projQ` is a chain map, and `Finc` is a chain map, so
the differential of the graded piece is again of the required shape.
-/

namespace Work.SSS.FirstPageCF

open CategoryTheory CategoryTheory.Limits

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- The projection `F_{k+1} → F_{k+1}/F_k` onto the graded piece is surjective. -/
private lemma projQ_surj (ξ : Work.SSS.Filtration C) (k n : ℕ) :
    Function.Surjective (Work.SSS.projQ ξ (k+1) n) := by
  rw [Work.SSS.projQ_succ]
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The projection `projQ` is a chain map, stated in the two consecutive degrees `n+1` and `n`. -/
private lemma projQ_d_comm' (ξ : Work.SSS.Filtration C) (k n : ℕ)
    (y : (ξ.F.obj (k+1)).X (n+1)) :
    ((Work.SSS.grF ξ.F (k+1)).d (n+1) n).hom (Work.SSS.projQ ξ (k+1) (n+1) y)
      = Work.SSS.projQ ξ (k+1) n (Work.SSS.dFs ξ (k+1) (n+1) n y) := by
  simpa using Work.SSS.FirstPageCF.projQ_d_comm ξ k (n+1) y

/-- The inclusion `Finc : F_s → F_{s+1}` is a chain map. -/
private lemma Finc_dFs_comm (ξ : Work.SSS.Filtration C) (s n : ℕ)
    (y : (ξ.F.obj s).X (n+1)) :
    Work.SSS.dFs ξ (s+1) (n+1) n (Work.SSS.Finc ξ s (s+1) (Nat.le_succ s) (n+1) y)
      = Work.SSS.Finc ξ s (s+1) (Nat.le_succ s) n (Work.SSS.dFs ξ s (n+1) n y) :=
  Work.SSS.chainMap_comm_apply_C (ξ.F.obj s) (ξ.F.obj (s+1))
    (ξ.F.map (homOfLE (Nat.le_succ s))) (n+1) n y

lemma mem_Bsq_of_sub_mem_range {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C)
    (s n : ℕ) (hs : 1 ≤ s)
    (x : (ξ.F.obj s).X n)
    (e : (ξ.F.obj (s+1)).X (n+1))
    (he : (Work.SSS.dFs ξ (s+1) (n+1) n) e
      = (Work.SSS.Finc ξ s (s+1) (Nat.le_succ s) n) x)
    (z : (Work.SSS.grF ξ.F s).X n)
    (hz : z - Work.SSS.projQ ξ s n x
      ∈ LinearMap.range ((Work.SSS.grF ξ.F s).d (n+1) n).hom) :
    z ∈ Work.SSS.Bsq ξ s n := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [Work.SSS.FirstPageCF.Bsq_mem_iff]
  -- `z - projQ x` is the class of `∂y` for some chain `y ∈ F_{k+1}`.
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hz
  obtain ⟨y, hy⟩ := projQ_surj ξ k (n+1) v
  -- Correct `x` by the boundary `∂y`: `x' = x + ∂y` has `projQ x' = z` and its image in
  -- `F_{k+2}` is again a boundary of `F_{k+2}`.
  refine ⟨x + Work.SSS.dFs ξ (k+1) (n+1) n y, ?_,
    e + Work.SSS.Finc ξ (k+1) (k+1+1) (Nat.le_succ (k+1)) (n+1) y, ?_⟩
  · rw [map_add, ← projQ_d_comm' ξ k n y, hy, hv]
    exact add_sub_cancel _ _
  · simp only [map_add, he, Finc_dFs_comm]

end Work.SSS.FirstPageCF
