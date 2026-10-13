import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilC4.dcl_elementary
import Submission.Work.WilC4.definableElt_of_mem_left
import Submission.Work.WilC4g.definable_fibre_cons
import Submission.Work.WilC4g.definable_prepend

namespace Work.WilVP

/-- The values of an `S`-instance of an `∅`-definable family of graphs at points of `S` lie in
`S`: `y` is the unique solution of a formula with parameters in `S`, hence definable from `S`,
and `Work.WilC4.dcl_elementary` gives `Work.WilC4.Dcl (S : Set M) ∅ = (S : Set M)` (Tarski–Vaught
for an elementary substructure).  The fibre `{t | (a,t,c) ∈ Y}` is `S`-definable by
`Work.WilC4g.definable_fibre_cons`, with `{a} ∪ range c ⊆ S`. -/
theorem fibre_value_mem {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {k : ℕ} {c : Fin k → M}
    (hc : ∀ i, c i ∈ (S : Set M)) {Y : Set (Fin (k + 2) → M)}
    (hY : (∅ : Set M).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (x y y' : M), Fin.cons x (Fin.cons y c) ∈ Y → Fin.cons x (Fin.cons y' c) ∈ Y → y = y')
    {a y : M} (ha : a ∈ (S : Set M)) (hy : Fin.cons a (Fin.cons y c) ∈ Y) :
    y ∈ (S : Set M) := by
  -- The slice of `Y` at first coordinate `a`: `Z = {w : Fin (k+1) → M | Fin.cons a w ∈ Y}`.
  -- It is `LRc`-definable with the single parameter `a` (`Work.WilC4g.definable_prepend`).
  have hZ : ({(a : M)} : Set M).Definable WilkiesDesign.CG.LRc
      {w : Fin (k + 1) → M | Fin.cons a w ∈ Y} := by
    have h := Work.WilC4g.definable_prepend (A := (∅ : Set M)) hY a
    simpa using h
  -- Peeling the first coordinate of a `(k+1)`-tuple, the set
  -- `W = {u : Fin 1 → M | (a, u 0, c) ∈ Y}` is definable with parameters `{a} ∪ range c`.
  have hW : ({(a : M)} ∪ Set.range c).Definable WilkiesDesign.CG.LRc
      {u : Fin 1 → M | Fin.cons (u 0) c ∈
        {w : Fin (k + 1) → M | Fin.cons a w ∈ Y}} :=
    Work.WilC4g.definable_fibre_cons (A := ({(a : M)} : Set M)) hZ c
  -- All the parameters used are in `S`.
  have hsub : ({(a : M)} ∪ Set.range c) ⊆ (S : Set M) := by
    intro x hx
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ha
    · rcases hx with ⟨i, rfl⟩
      exact hc i
  have hW' : (S : Set M).Definable WilkiesDesign.CG.LRc
      {u : Fin 1 → M | Fin.cons (u 0) c ∈
        {w : Fin (k + 1) → M | Fin.cons a w ∈ Y}} :=
    hW.mono hsub
  -- By uniqueness of the value, that definable set is the singleton `{fun _ => y}`.
  have hEq : {u : Fin 1 → M | Fin.cons (u 0) c ∈
        {w : Fin (k + 1) → M | Fin.cons a w ∈ Y}} = {fun _ : Fin 1 => y} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hu
      have hu' : Fin.cons a (Fin.cons (u 0) c) ∈ Y := hu
      funext i
      rw [Subsingleton.elim i 0]
      exact hfun a (u 0) y hu' hy
    · intro hu
      rw [hu]
      simpa using hy
  -- Hence `y` is definable from `S` alone.
  have hDef : Work.WilC4.DefinableElt (S : Set M) ∅ y := by
    rw [Work.WilC4.DefinableElt, Set.union_empty]
    rw [← hEq]
    exact hW'
  -- `S` is `dcl`-closed (Tarski–Vaught), so `y ∈ S`.
  have hmem : y ∈ Work.WilC4.Dcl (S : Set M) ∅ := hDef
  rwa [Work.WilC4.dcl_elementary S] at hmem

end Work.WilVP
