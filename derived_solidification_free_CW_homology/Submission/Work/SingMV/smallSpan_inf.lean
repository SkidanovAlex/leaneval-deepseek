import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# `smallSpan` is compatible with intersections

For a topological space `X`, a natural number `n` and a subset `U ⊆ X`, the singular `n`-chains
of `X` carried by `U` form the submodule

`smallSpan X n U = span ℤ {gen X n σ | σ : Δⁿ ⟶ X, image σ ⊆ U}`

of the singular `n`-chains `C_n(X)` (`Submission.Blueprint.singC`).  The purpose of this file is
the elementary computation

`smallSpan X n U ⊓ smallSpan X n V = smallSpan X n (U ∩ V)`,

which is the "chain-level" part of the Mayer–Vietoris argument: a chain that is both a sum of
simplices lying in `U` and a sum of simplices lying in `V` is a sum of simplices lying in
`U ∩ V`.

## Proof

`C_n(X)` is, by definition, the coproduct of one copy of `ℤ` for each singular `n`-simplex of
`X` (Mathlib's `SSet.chainComplexXCofan`/`IsColimit` description of the simplicial chain
complex).  Writing that coproduct as the module `singMap X n →₀ ℤ` of finitely supported
functions via the canonical isomorphism `smallSpanIso`, the generator `gen X n σ` becomes the
basis vector `Finsupp.single σ 1`, so `smallSpan X n U` corresponds to the submodule of functions
supported on the simplices whose image lies in `U` (`Finsupp.supported`).  The statement is then
`Finsupp.supported_inter`.  Concretely the key point is that in a free module the support of an
element is intrinsic, so a chain lying in both `smallSpan U` and `smallSpan V` cannot involve any
simplex outside `U` or outside `V`.
-/

open CategoryTheory Limits
open scoped Simplicial

noncomputable section

namespace Work.SingMV

namespace SmallSpanAux

/-- The `n`-simplices of the singular simplicial set of `X`. -/
abbrev sImp (X : TopCat) (n : ℕ) : Type := (TopCat.toSSet.obj X) _⦋n⦌

/-- `C_n(X)`, the group of singular `n`-chains of `X`, is the coproduct of one copy of `ℤ` for
each singular `n`-simplex; this is the canonical isomorphism with the module of finitely
supported functions on the singular `n`-simplices. -/
noncomputable def coprodIso (X : TopCat) (n : ℕ) :
    ((Submission.Blueprint.singC).obj X).X n ≅ ↧(sImp X n →₀ ℤ) :=
  IsColimit.coconePointUniqueUpToIso
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (sImp X n))

/-- The isomorphism `coprodIso` sends the generator of the summand of a simplex to the
corresponding basis vector. -/
lemma coprodIso_gen (X : TopCat) (n : ℕ) (σ : singMap X n) :
    (coprodIso X n).toLinearEquiv (gen X n σ) =
      Finsupp.single ((singEquiv X n).symm σ) (1 : ℤ) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (sImp X n)) ⟨(singEquiv X n).symm σ⟩
  have h2 := DFunLike.congr_fun (congrArg (fun f => ModuleCat.Hom.hom f) h) (1 : ℤ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [gen]
  exact h2

/-- The singular `n`-chains of `X`, identified with the finitely supported functions on the
singular `n`-simplices of `X`, reindexed so that the index type is `singMap X n`. -/
noncomputable def eLin (X : TopCat) (n : ℕ) :
    ((Submission.Blueprint.singC).obj X).X n ≃ₗ[ℤ] (singMap X n →₀ ℤ) :=
  (coprodIso X n).toLinearEquiv.trans (Finsupp.domLCongr (singEquiv X n))

/-- `eLin` sends the generator attached to a simplex to the corresponding basis vector. -/
lemma eLin_gen (X : TopCat) (n : ℕ) (σ : singMap X n) :
    eLin X n (gen X n σ) = Finsupp.single σ (1 : ℤ) := by
  rw [eLin, LinearEquiv.trans_apply, coprodIso_gen, Finsupp.domLCongr_single]
  simp

/-- The singular `n`-simplices of `X` whose image lies in `U`. -/
def simpIn (X : TopCat) (n : ℕ) (U : Set X) : Set (singMap X n) := fun σ => ∀ x, σ x ∈ U

lemma map_smallSpan_le (X : TopCat) (n : ℕ) (U : Set X) :
    Submodule.map (eLin X n).toLinearMap (smallSpan X n U) ≤
      Finsupp.supported ℤ ℤ (simpIn X n U) := by
  rw [smallSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨a, ⟨σ, rfl⟩, rfl⟩
  dsimp only
  exact (eLin_gen X n σ.1).symm ▸
    Finsupp.single_mem_supported (M := ℤ) (R := ℤ) (s := simpIn X n U) (a := σ.1) (1 : ℤ) σ.2

lemma supported_le_map_smallSpan (X : TopCat) (n : ℕ) (U : Set X) :
    Finsupp.supported ℤ ℤ (simpIn X n U) ≤
      Submodule.map (eLin X n).toLinearMap (smallSpan X n U) := by
  rw [Finsupp.supported_eq_span_single, Submodule.span_le]
  rintro _ ⟨σ, hσ, rfl⟩
  dsimp only
  exact (eLin_gen X n σ) ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩)

/-- Under `eLin`, the chains carried by `U` are exactly the finitely supported functions supported
on the simplices whose image lies in `U`. -/
lemma map_smallSpan (X : TopCat) (n : ℕ) (U : Set X) :
    Submodule.map (eLin X n).toLinearMap (smallSpan X n U) =
      Finsupp.supported ℤ ℤ (simpIn X n U) :=
  le_antisymm (map_smallSpan_le X n U) (supported_le_map_smallSpan X n U)

/-- A chain lies in `smallSpan X n U` if and only if, in its expression as a finite linear
combination of the basis elements `gen X n σ`, only simplices with image in `U` occur. -/
lemma mem_smallSpan_iff (X : TopCat) (n : ℕ) (U : Set X)
    (z : ((Submission.Blueprint.singC).obj X).X n) :
    z ∈ smallSpan X n U ↔ ∀ σ : singMap X n, eLin X n z σ ≠ 0 → ∀ x, σ x ∈ U := by
  have h := map_smallSpan X n U
  constructor
  · intro hz
    have hmem : eLin X n z ∈ Finsupp.supported ℤ ℤ (simpIn X n U) := by
      rw [← h]
      exact Submodule.mem_map_of_mem hz
    rw [Finsupp.mem_supported'] at hmem
    intro σ hσ
    by_contra hc
    exact hσ (hmem σ hc)
  · intro hz
    have hmem : eLin X n z ∈ Finsupp.supported ℤ ℤ (simpIn X n U) := by
      rw [Finsupp.mem_supported']
      intro σ hσ
      by_contra hne
      exact hσ (hz σ hne)
    rw [← h, Submodule.mem_map] at hmem
    obtain ⟨w, hw, hwe⟩ := hmem
    rw [← (eLin X n).injective hwe]
    exact hw

end SmallSpanAux

open SmallSpanAux

/-- The chains carried by `U ∩ V` are the intersection of the chains carried by `U` and by `V`:
a chain that is a sum of simplices lying in `U` and a sum of simplices lying in `V` involves only
simplices lying in `U ∩ V`. -/
theorem smallSpan_inf (X : TopCat) (n : ℕ) (U V : Set X) :
    Work.SingMV.smallSpan X n U ⊓ Work.SingMV.smallSpan X n V =
      Work.SingMV.smallSpan X n (U ∩ V) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [mem_smallSpan_iff]
    have hz' := Submodule.mem_inf.mp hz
    have hU := (mem_smallSpan_iff X n U z).mp hz'.1
    have hV := (mem_smallSpan_iff X n V z).mp hz'.2
    intro σ hσ x
    exact ⟨hU σ hσ x, hV σ hσ x⟩
  · rw [le_inf_iff]
    constructor
    · rw [smallSpan, smallSpan]
      apply Submodule.span_mono
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨σ.1, fun x => (σ.2 x).1⟩, rfl⟩
    · rw [smallSpan, smallSpan]
      apply Submodule.span_mono
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨σ.1, fun x => (σ.2 x).2⟩, rfl⟩

end Work.SingMV
