import Mathlib
import Submission.Work.CFTLib.ShafDeps
import Submission.Work.CFT.MaxProP.ContCohomology.Defs
import Submission.Work.CFTLib.Algebra.finiteDimensional_of_bdd_finrank

/-!
# Reducing the relation-rank bound to a bound on the finite levels

Let `G` be a profinite group and `V = continuousCohomology 2 (trivialZModpRep p G)` its second
continuous cohomology with trivial `𝔽_p`-coefficients (Mathlib's definition).  The library's
`Work.CFT.MaxProP.H2FpCont p G` is the filtered colimit of the finite-level groups
`H²(G ⧸ U, 𝔽_p)` over the open normal subgroups `U ◁ G`.

This file contains the *bookkeeping* that turns a compatible family of linear maps
`Φ U : H²(G ⧸ U) → V` with

* naturality in `U` (compatibility with the inflation maps),
* `V = ⋃_U range (Φ U)` (every class comes from a finite level),

and a uniform bound `dim (range (Φ U)) ≤ N`, into the two conclusions required by the challenge:

* `H2Finite p G` (finite-dimensionality of `V`), and
* `relationRank p G ≤ N`.

The argument is the one used for Shafarevich's relation-rank bound: any finitely generated
submodule `W ≤ V` is spanned by finitely many elements, each of which lies in some finite level;
directedness of the open normal subgroups puts them all in *one* level `range (Φ U₀)`, so
`finrank W ≤ finrank (range (Φ U₀)) ≤ N`.  Then `Work.CFTLib.Algebra.finiteDimensional_of_bdd_finrank`
applies.

## Main results

* `Work.CFTLib.Shaf.levelMap` — `Φ U = e.symm ∘ H2FpCont.of p G U` from an identification
  `e : V ≃ₗ H2FpCont p G`.
* `Work.CFTLib.Shaf.levelMap_natural` — naturality of `Φ`.
* `Work.CFTLib.Shaf.h2Finite_and_relationRank_le_of_levelBound` — the reduction.
-/

open scoped Classical

noncomputable section

namespace Work.CFTLib.Shaf

open Work.CFT.MaxProP

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The finite-level map** `Φ U : H²(G ⧸ U, 𝔽_p) → V`, where `V = H²_cont(G, 𝔽_p)` is Mathlib's
continuous cohomology, obtained by transporting the canonical map out of the direct limit along an
identification `e : V ≃ₗ H2FpCont p G`. -/
def levelMap
    (e : (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type) ≃ₗ[ZMod p]
      (H2FpCont p G : Type))
    (U : OpenNormal G) : (H2FpContFamily p G U) →ₗ[ZMod p]
      (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type) :=
  e.symm.toLinearMap.comp (H2FpCont.of p G U)

/-- Naturality of the finite-level maps: for `U ≤ V` (i.e. `V ≤ U` as subgroups) the diagram
`H²(G ⧸ U) → H²(G ⧸ V) → V` commutes, by the defining relation `H2FpCont.of_f` of the direct
limit. -/
theorem levelMap_natural
    (e : (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type) ≃ₗ[ZMod p]
      (H2FpCont p G : Type))
    {U V : OpenNormal G} (h : U ≤ V) (x : H2FpContFamily p G U) :
    levelMap e V (contMap p G U V h x) = levelMap e U x := by
  simp only [levelMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [H2FpCont.of_f h]

/-- Every element of `V` lies in the range of some finite level map. -/
theorem exists_mem_range_levelMap
    (e : (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type) ≃ₗ[ZMod p]
      (H2FpCont p G : Type))
    (hsurj : ∀ z : H2FpCont p G, ∃ (U : OpenNormal G) (x : H2FpContFamily p G U),
      H2FpCont.of p G U x = z)
    (v : (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type)) :
    ∃ U : OpenNormal G, v ∈ LinearMap.range (levelMap e U) := by
  obtain ⟨U, x, hx⟩ := hsurj (e v)
  refine ⟨U, x, ?_⟩
  simp only [levelMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hx, LinearEquiv.symm_apply_apply]

open scoped Classical in
/-- **The reduction.**  Let `Φ U : H²(G ⧸ U, 𝔽_p) → V` be a compatible family of finite-level maps
into `V = H²_cont(G, 𝔽_p)`, whose ranges cover `V` and whose dimensions are uniformly bounded by
`N`.  Then `H²_cont(G, 𝔽_p)` is finite dimensional and `relationRank p G ≤ N`. -/
theorem h2Finite_and_relationRank_le_of_levelBound
    (Φ : (U : OpenNormal G) → (H2FpContFamily p G U) →ₗ[ZMod p]
      (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type))
    (hnat : ∀ (U V : OpenNormal G) (h : U ≤ V) (x : H2FpContFamily p G U),
      Φ V (contMap p G U V h x) = Φ U x)
    (hsurj : ∀ v : (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type),
      ∃ U : OpenNormal G, v ∈ LinearMap.range (Φ U))
    (hfin : ∀ U : OpenNormal G,
      FiniteDimensional (ZMod p) (LinearMap.range (Φ U)))
    (N : ℕ) (hbound : ∀ U : OpenNormal G,
      Module.finrank (ZMod p) (LinearMap.range (Φ U)) ≤ N) :
    LeanEval.NumberTheory.H2Finite p G ∧ LeanEval.NumberTheory.relationRank p G ≤ N := by
  classical
  have key : ∀ s : Finset
      (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type),
      (∀ x ∈ s, ∃ U : OpenNormal G, x ∈ LinearMap.range (Φ U)) →
      ∃ U : OpenNormal G, ∀ x ∈ s, x ∈ LinearMap.range (Φ U) := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; exact ⟨Classical.arbitrary (OpenNormal G), by simp⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨U₁, hU₁⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨U₂, hU₂⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
      obtain ⟨U₀, h₁, h₂⟩ := exists_ge_ge U₁ U₂
      refine ⟨U₀, fun x hx => ?_⟩
      rw [Finset.mem_insert] at hx
      rcases hx with hxa | hx
      · subst hxa
        obtain ⟨y, hy⟩ := hU₁
        exact ⟨contMap p G U₁ U₀ h₁ y, by rw [hnat U₁ U₀ h₁ y, hy]⟩
      · obtain ⟨y, hy⟩ := hU₂ x hx
        exact ⟨contMap p G U₂ U₀ h₂ y, by rw [hnat U₂ U₀ h₂ y, hy]⟩
  have hbdd : ∀ W : Submodule (ZMod p)
      (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) : Type),
      W.FG → Module.finrank (ZMod p) W ≤ N := by
    intro W hW
    obtain ⟨s, hspan⟩ := hW
    obtain ⟨U₀, hU₀⟩ := key s (fun x _ => hsurj x)
    have hle : W ≤ LinearMap.range (Φ U₀) := hspan ▸ Submodule.span_le.mpr hU₀
    haveI := hfin U₀
    exact le_trans (Submodule.finrank_mono hle) (hbound U₀)
  obtain ⟨hfd, hfr⟩ :=
    Work.CFTLib.Algebra.finiteDimensional_of_bdd_finrank (ZMod p) _ N hbdd
  exact ⟨hfd, hfr⟩

end Work.CFTLib.Shaf

