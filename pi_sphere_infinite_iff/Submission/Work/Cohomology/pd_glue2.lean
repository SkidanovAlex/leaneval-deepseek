import Mathlib
import Submission.Work.Cohomology.pd_ab_defs
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Cohomology.capRelAux

/-!
# The cohomology row of the gluing of the `Good` framework

The five-lemma diagram of the gluing `Good U → Good V → Good (U∩V) → Good (U∪V)`
(Hatcher, Lemma 3.36) has the cohomology row

`H^k(C^*(W,W∖K) ∩ C^*(W,W∖L)) ⟶ H^k(W,W∖K) ⊕ H^k(W,W∖L) ⟶ H^k(W,W∖(K∪L)) --δ--> ⋯`

(`W = U ∪ V`, `K ⊆ U`, `L ⊆ V` compact), the long exact sequence of Hatcher's `A+B` short exact
sequence (`pd_ab_les.lean`).

This file contains, in the clash-free part of the workspace (`capRelAux` instead of `dualZ`), the
**excision isomorphism for one piece of the cover** — the identification
`H^k(W, W∖K) ≅ H^k(U, U∖K)` used for the `biprod` slot of the diagram (and, dually, for the
transport of compactly supported cohomology along open inclusions in the increasing-union step).

## Why this file does not import `pd_ab_les`

`Submission/Work/Cohomology/pdAB_shortExact.lean` (needed by `pd_ab_les.lean` for the connecting
map `pdABδ`) declares `Work.Cohomology.gen`, while `Submission/Work/Cohomology/Sd_comm.lean`
(imported by every subdivision-based module, in particular by the honest Mayer–Vietoris long exact
sequence `homologyMV_honest_les` and by `exists_decomposed_chain`) declares `Work.Cohomology.gen`
as well.  The two declarations clash (`gen._proof_1` is created twice), so *no file can import
both* `pd_ab_les` and the subdivision world.  Consequently every statement that mentions `pdABδ`
*and* `mvδ`/`goodD` must be split, or the relevant lemma must be restated in a clash-free module.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Cohomological excision for one piece of the cover -/

/-- **Cohomological excision for one piece.**  For open `U ⊆ W`, a compact `K ⊆ U` and a
Hausdorff ambient space, the restriction `H^k(W, W∖K) ⟶ H^k(U, U∖K)` is an isomorphism.

Both `H^k(M, M∖K) ⟶ H^k(W, W∖K)` and `H^k(M, M∖K) ⟶ H^k(U, U∖K)` are isomorphisms
(`Work.Cohomology.capRel_excision_isIso`), and they factor the restriction, which is therefore an
isomorphism as well. -/
theorem pdCohExcision {M : TopCat} [T2Space M] {W U : Set M} (hUW : U ⊆ W) (hU : IsOpen U)
    (hW : IsOpen W) {K : Set M} (hKU : K ⊆ U) (hKc : IsCompact K) (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub U K) (pdRelSub W K) (pdIncl W U hUW) (fun x hx => hx)) k) := by
  have hA : IsOpen (Kᶜ : Set M) := hKc.isClosed.isOpen_compl
  have hcovW : W ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hUW (hKU hx))
    · exact Or.inr hx
  have hcovU : U ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  haveI hEW : IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ (pdRelSub W K) Kᶜ (subtypeIncl M W) (fun y hy => hy)) k) :=
    capRel_excision_isIso M W Kᶜ hW hA hcovW k (fun y hy => hy)
  haveI hEU : IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ (pdRelSub U K) Kᶜ (subtypeIncl M U) (fun x hx => hx)) k) :=
    capRel_excision_isIso M U Kᶜ hU hA hcovU k (fun x hx => hx)
  have hcomp := capRel_relComplexMap_comp (R := ℤ) (pdRelSub U K) (pdRelSub W K) Kᶜ
      (pdIncl W U hUW) (subtypeIncl M W) (fun x hx => hx) (fun y hy => hy)
  have hcongr := capRel_relComplexMap_congr (R := ℤ) (X₁ := TopCat.of U) (X₂ := M)
      (pdRelSub U K) Kᶜ
      (show pdIncl W U hUW ≫ subtypeIncl M W = subtypeIncl M U from by ext x; rfl)
      (fun x hx => hx) (fun x hx => hx)
  have hkey := hcomp.symm.trans hcongr
  have hhom := congrArg (fun φ => HomologicalComplex.homologyMap φ k) hkey
  rw [HomologicalComplex.homologyMap_comp] at hhom
  have hB : HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub U K) (pdRelSub W K)
        (pdIncl W U hUW) (fun x hx => hx)) k
      = inv (HomologicalComplex.homologyMap
          (relComplexMap ℤ (pdRelSub W K) Kᶜ (subtypeIncl M W) (fun y hy => hy)) k)
        ≫ HomologicalComplex.homologyMap
          (relComplexMap ℤ (pdRelSub U K) Kᶜ (subtypeIncl M U) (fun x hx => hx)) k := by
    rw [← hhom, CategoryTheory.IsIso.inv_hom_id_assoc]
  rw [hB]
  infer_instance

/-! ## The slots of the cohomology row -/

/-- The `∩`-slot of the five-lemma diagram: the degree-`k` cohomology of Hatcher's `A+B` complex
for the pair of compact sets `(K,L)` inside `W`. -/
abbrev pdCohAB (M : TopCat) (W : Set M) (K L : Set M) (k : ℕ) : ModuleCat ℤ :=
  (pdABCoh (TopCat.of W) (pdRelSub W K) (pdRelSub W L)).homology k

end
end Work.Cohomology
