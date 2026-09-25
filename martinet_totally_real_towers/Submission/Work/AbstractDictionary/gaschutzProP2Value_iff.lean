import Mathlib
import Submission.Work.AbstractDictionary.Defs
import Submission.Work.HopfGaschutz.ClosedDictionary

/-!
# `Work.AbstractDictionary.gaschutzProP2Value_iff` -- the two halves of the closed Gaschütz value
theorem

**Namespace** `Work.AbstractDictionary`; module
`Submission.Work.AbstractDictionary.gaschutzProP2Value_iff`.

`Work.AbstractDictionary.Defs` names the closed Gaschütz value theorem

  `GaschutzProP2Value d gen` = `∀ r, ContH2DimLe Γ r ↔ ∃ S, #S ≤ r ∧ (relators) ∧ ClosedNormalGeneratesTwo K S`

and its two halves, `Work.HopfGaschutz.ProPHopfCohomologicalInput` (the `⟹`-half, stated with the
*spanning-modulo-`K^p[K,F]`* shape of the relation condition) and
`ProPHopfCohomologicalBound` (the `⟸`-half, stated with the *closed normal generation* shape).

This file proves that `GaschutzProP2Value` is exactly the conjunction of the two halves.  The only
mathematical content is the observation that the **two shapes of the relation condition agree**:

  `ClosedNormalGenerates 2 K S ↔ (∀ Q finite 2-group, ∀ φ : F →* Q, K ≤ ⟪S⟫ ⊔ K^2[K,F] ⊔ ker φ)`.

* `⟸` is the engine of the closed dictionary,
  `Work.HopfGaschutz.closedNormalGenerates_of_spanningModulo` (already proved elsewhere in the
  workspace);
* `⟹` is `spanningModulo_of_closedNormalGenerates` below: given a finite `2`-group `Q` and
  `φ : F →* Q`, the quotient of `F` by `M = ⟪S⟫ ⊔ K^2[K,F] ⊔ ker φ` is a quotient of the *finite*
  `2`-group `φ.range` (namely `φ.range ⧸ φ(M)`), hence a finite `2`-group quotient of `F` killing
  `S`; the closed condition applied to it says `K ≤ M`, as required.

Everything else is bookkeeping: both predicates are `∃`-statements whose bodies differ only in the
shape of the relation condition, so they are pointwise equivalent in `r`, and the two implications
of the value theorem are then assembled from the two halves.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.AbstractDictionary

/-! ## The two shapes of the closed relation condition -/

/-- **Closed normal generation implies the spanning-modulo condition at every finite `2`-group
quotient**, in the direction *not* supplied by the workspace's closed engine.

Suppose the finite set `S ⊆ FreeGroup α` closed-normally generates the normal subgroup `K`, i.e.
every finite `2`-group quotient of `FreeGroup α` killing `S` kills `K`.  Then for *every* finite
`2`-group `Q` and *every* `φ : FreeGroup α →* Q`, the subgroup `K` is contained in
`⟪S⟫ · K^2[K,FreeGroup α] · ker φ`.

The proof: put `M = ⟪S⟫ ⊔ relFrattini 2 K ⊔ ker φ`, a normal subgroup containing `ker φ`.  The group
`FreeGroup α ⧸ M` is a quotient of `φ.range ⧸ φ(M)`, hence a finite `2`-group, and `S ⊆ M`, so the
closed condition applied to the projection `FreeGroup α ↠ FreeGroup α ⧸ M` gives `K ≤ M`.  (Building
`FreeGroup α ⧸ M` directly is not convenient -- `FreeGroup α` is infinite, so it carries no
`Fintype` instance; `φ.range ⧸ φ(M)` is the same quotient, made finite by `φ.range`.) -/
theorem spanningModulo_of_closedNormalGenerates {α : Type} [Fintype α]
    {K : Subgroup (FreeGroup α)} [K.Normal] {S : Finset (FreeGroup α)}
    (h : ClosedNormalGeneratesTwo K S) :
    ∀ (Q : Type) [Group Q] [Fintype Q], IsPGroup 2 Q → ∀ φ : FreeGroup α →* Q,
      K ≤ Subgroup.normalClosure (S : Set (FreeGroup α)) ⊔
        Work.HopfGaschutz.relFrattini 2 K ⊔ MonoidHom.ker φ := by
  classical
  intro Q _ _ hQ φ
  -- the normal subgroup `M = ⟪S⟫ ⊔ K²[K,F] ⊔ ker φ`
  set M : Subgroup (FreeGroup α) :=
    Subgroup.normalClosure (S : Set (FreeGroup α)) ⊔
      Work.HopfGaschutz.relFrattini 2 K ⊔ MonoidHom.ker φ with hMdef
  have hSmem : ∀ s ∈ S, s ∈ M := by
    intro s hs
    rw [hMdef]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.subset_normalClosure hs))
  have hMnorm : M.Normal := by
    rw [hMdef]; infer_instance
  -- corestrict `φ` to its range, and pass to the quotient by the image of `M`
  have hmemr : ∀ x : FreeGroup α, φ x ∈ φ.range := fun x => ⟨x, rfl⟩
  let φr : FreeGroup α →* ↥φ.range := φ.codRestrict φ.range hmemr
  have hφrsurj : Function.Surjective φr := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  haveI hN : (M.map φr).Normal := hMnorm.map φr hφrsurj
  let ψ : FreeGroup α →* (↥φ.range) ⧸ (M.map φr) :=
    (QuotientGroup.mk' (M.map φr)).comp φr
  have hψS : ∀ s ∈ S, ψ s = 1 := by
    intro s hs
    have hsM : φr s ∈ M.map φr := Subgroup.mem_map_of_mem φr (hSmem s hs)
    show ((QuotientGroup.mk' (M.map φr)) (φr s)) = 1
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (φr s)).mpr hsM
  -- the kernel of `ψ` is exactly `M`
  have hker : MonoidHom.ker ψ = M := by
    have h1 : MonoidHom.ker ψ = Subgroup.comap φr (M.map φr) := by
      ext x
      simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        Subgroup.mem_comap, QuotientGroup.eq_one_iff]
    rw [h1, Subgroup.comap_map_eq, MonoidHom.ker_codRestrict]
    exact sup_eq_left.mpr (by rw [hMdef]; exact le_sup_right)
  -- `φ.range ⧸ φ(M)` is a finite `2`-group, so the closed condition applies to it
  have hQ' : IsPGroup 2 ((↥φ.range) ⧸ (M.map φr)) := (hQ.to_subgroup φ.range).to_quotient _
  exact hker ▸ h _ hQ' ψ hψS

universe u

theorem gaschutzProP2Value_iff {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (gen : Fin d → Γ) :
    Work.AbstractDictionary.GaschutzProP2Value d gen ↔
      Work.HopfGaschutz.ProPHopfCohomologicalInput.{u, 0} 2 d Γ gen ∧
        Work.AbstractDictionary.ProPHopfCohomologicalBound d gen := by
  classical
  -- the relation condition has the same two shapes in every `∃`-statement below
  have key : ∀ r : ℕ,
      (∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
        (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
        ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S) ↔
      (∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
        (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
        (∀ (Q : Type) [Group Q] [Fintype Q], IsPGroup 2 Q → ∀ φ : FreeGroup (Fin d) →* Q,
          MonoidHom.ker (FreeGroup.lift gen) ≤
            Subgroup.normalClosure (S : Set (FreeGroup (Fin d))) ⊔
              Work.HopfGaschutz.relFrattini 2 (MonoidHom.ker (FreeGroup.lift gen)) ⊔
                MonoidHom.ker φ)) := by
    intro r
    constructor
    · rintro ⟨S, hc, himg, hcl⟩
      exact ⟨S, hc, himg, spanningModulo_of_closedNormalGenerates hcl⟩
    · rintro ⟨S, hc, himg, hsp⟩
      exact ⟨S, hc, himg, Work.HopfGaschutz.closedNormalGenerates_of_spanningModulo hsp⟩
  constructor
  · -- `GaschutzProP2Value` gives both halves: the `⟹`-half via `key`, the `⟸`-half directly
    intro hall
    exact ⟨fun r hr => (key r).mp ((hall r).mp hr), fun r hr => (hall r).mpr hr⟩
  · -- conversely the two halves give the equivalence at every `r`
    rintro ⟨hin, hb⟩ r
    exact ⟨fun hr => (key r).mpr (hin r hr), fun hr => hb r hr⟩

end Work.AbstractDictionary
