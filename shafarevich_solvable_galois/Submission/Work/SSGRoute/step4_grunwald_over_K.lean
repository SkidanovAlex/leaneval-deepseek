import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.overK
import Submission.Work.SSGRoute.grunwald_surjective_odd
import Submission.Work.SSGRoute.grunwald_surjective_two
import Submission.Work.SSGRoute.exists_open_decompDown
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The Grünwald statement over the base field `↥K` with top field `⊥`

The node `Work.SSGRoute.step4_y_exists` needs its class `ε` on `Gal(ℚ̄/↥K)` (not on `G_ℚ`), with
prescribed local values on the decomposition groups `decomp ↥K A` of a finite set `S` of places
whose `↥K`-primes are pairwise distinct.  Grünwald's theorem gives exactly this: applied over the
base field `↥K` with top field `⊥`, its local groups are `decomp ↥K A ⊓ (⊥).fixingSubgroup`, and
`(⊥ : IntermediateField ↥K ℚ̄).fixingSubgroup = ⊤`, so the local groups are the `decomp ↥K A`
themselves and the conclusion is stated on the whole of `Gal(ℚ̄/↥K)`.

This module isolates that application (`step4_grunwald_surjective_over_K`, `ZMod p`-valued, with
arbitrary continuous additive local data) and its coordinatewise lift to an arbitrary finite
`𝔽_p`-module `E` (`step4_grunwald_E_coordinatewise`, a copy of
`Work.SSGRoute.grunwald_E_coordinatewise` for a general group `Γ` instead of `G_ℚ`).

These two are the "local realization" half of Schmidt--Wingberg's Fourth Step: they produce the
class `ε` with the prescribed local behaviour but with *no* control on its ramification (that is
the shrinking, `Work.CohomologicalShrinking.exists_shrinking_H1`).
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- **Grünwald over the base field `↥K`, top field `⊥`.**  For a finite set `S` of places whose
`↥K`-primes are pairwise distinct and an arbitrary additive, locally constant (i.e. continuous for
a discrete module) local datum `f A` on `decomp ↥K A` for each `A ∈ S`, there is an additive,
locally constant `z : Gal(ℚ̄/↥K) → ZMod p` restricting to `f A` on `decomp ↥K A` for every
`A ∈ S`. -/
theorem step4_grunwald_surjective_over_K (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ (⊥ : IntermediateField ↥K SSGRoute.QBar))
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ↥K A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ↥K A B → A = B)
    (f : ∀ A : {A // A ∈ S},
      ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup) → ZMod p)
    (hf : ∀ A : {A // A ∈ S},
      ∀ a b : ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
      f A (a * b) = f A a + f A b)
    (hfc : ∀ A : {A // A ∈ S},
      ∃ U : Subgroup ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
          (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup)) ∧
        ∀ x ∈ U, f A x = 0) :
    ∃ z : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
      (∀ a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, z (a * b) = z a + z b) ∧
      SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) z ∧
      (∀ A : {A // A ∈ S},
        ∀ δ : ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
          (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
        z (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) = f A δ) := by
  haveI hNumK : NumberField ↥K := Work.SSGRoute.numberField_K K
  haveI hAlgClK : IsAlgClosure ↥K SSGRoute.QBar := Work.SSGRoute.isAlgClosure_qbar_over_K K
  haveI hFinBot : FiniteDimensional ↥K (⊥ : IntermediateField ↥K SSGRoute.QBar) := inferInstance
  haveI hGalBot : IsGalois ↥K (⊥ : IntermediateField ↥K SSGRoute.QBar) := inferInstance
  have key : ∀ z : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
      (∀ g ∈ (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup,
        ∀ h ∈ (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup, z (g * h) = z g + z h) →
      SSGRoute.IsLocConstOn (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup z →
      (∀ A : {A // A ∈ S},
        ∀ δ : ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
          (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
        z (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) = f A δ) →
      ∃ z' : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, z' (a * b) = z' a + z' b) ∧
        SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) z' ∧
        (∀ A : {A // A ∈ S},
          ∀ δ : ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
            (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
          z' (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) = f A δ) := by
    intro z h1 h2 h3
    refine ⟨z, ?_, ?_, h3⟩
    · intro a b
      exact h1 a (by rw [IntermediateField.fixingSubgroup_bot]; trivial) b
        (by rw [IntermediateField.fixingSubgroup_bot]; trivial)
    · simpa only [IntermediateField.fixingSubgroup_bot] using h2
  by_cases hp2 : p = 2
  · obtain ⟨z, h1, h2, h3⟩ :=
      @grunwald_surjective_two p (inferInstance : Fact p.Prime) hp2 ↥K SSGRoute.QBar
        (inferInstance : Field ↥K) hNumK (inferInstance : Field SSGRoute.QBar)
        (inferInstance : Algebra ↥K SSGRoute.QBar) hAlgClK
        (⊥ : IntermediateField ↥K SSGRoute.QBar) hFinBot hGalBot
        ζ hζ hζK S hSfin hSdisj f hf hfc
    exact key z h1 h2 h3
  · obtain ⟨z, h1, h2, h3⟩ :=
      @grunwald_surjective_odd p (inferInstance : Fact p.Prime) hp2 ↥K SSGRoute.QBar
        (inferInstance : Field ↥K) hNumK (inferInstance : Field SSGRoute.QBar)
        (inferInstance : Algebra ↥K SSGRoute.QBar) hAlgClK
        (⊥ : IntermediateField ↥K SSGRoute.QBar) hFinBot hGalBot
        ζ hζ hζK S hSfin hSdisj f hf hfc
    exact key z h1 h2 h3

/-- **Coordinatewise lift to an arbitrary finite `𝔽_p`-module.**  If the `ZMod p`-valued Grünwald
statement holds for every additive, locally constant local datum on a family of subgroups `D i` of
a profinite group `Γ`, then it holds with values in any finite `𝔽_p`-module `E` (choose an
`𝔽_p`-basis and reassemble).  This is `Work.SSGRoute.grunwald_E_coordinatewise` with `G_ℚ`
replaced by a general group `Γ`. -/
theorem step4_grunwald_E_coordinatewise {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (p : ℕ) [Fact p.Prime] {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    {G : Type} [Group G] [DistribMulAction G E]
    {ι : Type} [Fintype ι] (D : ι → Subgroup Γ) (H : Subgroup Γ)
    (hzmod : ∀ (g : ∀ i, ↥(D i) → ZMod p),
        (∀ i, ∀ a b : ↥(D i), g i (a * b) = g i a + g i b) →
        (∀ i, ∃ U : Subgroup ↥(D i), IsOpen (U : Set ↥(D i)) ∧ ∀ x ∈ U, g i x = 0) →
        ∃ z : Γ → ZMod p,
          (∀ a ∈ H, ∀ b ∈ H, z (a * b) = z a + z b) ∧
          SSGRoute.IsLocConstOn H z ∧
          (∀ i, ∀ δ : ↥(D i), z (δ : Γ) = g i δ))
    (f : ∀ i, ↥(D i) → E)
    (hf : ∀ i, ∀ a b : ↥(D i), f i (a * b) = f i a + f i b)
    (hfc : ∀ i, ∃ U : Subgroup ↥(D i), IsOpen (U : Set ↥(D i)) ∧ ∀ x ∈ U, f i x = 0) :
    ∃ y : Γ → E, (∀ a ∈ H, ∀ b ∈ H, y (a * b) = y a + y b) ∧
      SSGRoute.IsLocConstOn H y ∧
      ∀ i, ∀ δ : ↥(D i), y (δ : Γ) = f i δ := by
  classical
  have hfin : Module.Finite (ZMod p) E := Module.Finite.of_finite
  let e : E ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) E) → ZMod p) :=
    (Module.finBasis (ZMod p) E).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin (Module.finrank (ZMod p) E)))
  have hcoord : ∀ k : Fin (Module.finrank (ZMod p) E),
      ∃ z : Γ → ZMod p,
        (∀ a ∈ H, ∀ b ∈ H, z (a * b) = z a + z b) ∧
        SSGRoute.IsLocConstOn H z ∧
        (∀ i, ∀ δ : ↥(D i), z (δ : Γ) = (e (f i δ)) k) := by
    intro k
    refine hzmod (fun i x => (e (f i x)) k) ?_ ?_
    · intro i a b
      rw [hf i a b, map_add]
      rfl
    · intro i
      obtain ⟨U, hUo, hU⟩ := hfc i
      exact ⟨U, hUo, fun x hx => by simp [hU x hx]⟩
  choose z hza hzl hzag using hcoord
  refine ⟨fun σ => e.symm (fun k => z k σ), ?_, ?_, ?_⟩
  · intro a ha b hb
    change e.symm (fun k => z k (a * b)) = e.symm (fun k => z k a) + e.symm (fun k => z k b)
    have h1 : (fun k => z k (a * b)) = (fun k => z k a) + (fun k => z k b) := by
      funext k; exact hza k a ha b hb
    rw [h1]; exact map_add e.symm _ _
  · have hloc : ∀ k, ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧
        ∀ a ∈ H, ∀ u ∈ U, u ∈ H → z k (a * u) = z k a := fun k => hzl k
    choose U hUo hU using hloc
    refine ⟨⨅ k, U k, ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite (fun k => hUo k)
    · intro a ha u hu huH
      have hu' : ∀ k, u ∈ U k := fun k => (Subgroup.mem_iInf.mp hu) k
      have h1 : (fun k => z k (a * u)) = (fun k => z k a) := by
        funext k; exact hU k a ha u (hu' k) huH
      show e.symm (fun k => z k (a * u)) = e.symm (fun k => z k a)
      rw [h1]
  · intro i δ
    show e.symm (fun k => z k (δ : Γ)) = f i δ
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    exact hzag k i δ

/-- **Local constancy transports from the `ℚ`-level to the `↥K`-level.**  For a place `A` split in
`K` and an additive datum `η` on `decomp ℚ A` which is locally constant there, the datum
`x ↦ η ((fixingSubgroupEquiv K).symm x)` on `decomp ↥K A ⊓ (⊥).fixingSubgroup` vanishes on an open
subgroup.  This is the "open vanishing subgroup" form of continuity (`hfcont`) that the Grünwald
statements ask for; it is proved by transporting the Krull-basic open subgroup through
`Work.SSGRoute.exists_open_decompDown` (`decompDownHom` carries open subgroups the right way). -/
theorem step4_localDatum_open_vanishing {M G : Type} [AddCommGroup M] [Group G]
    [DistribMulAction G M]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (hsplit : SSGRoute.IsSplitIn ℚ K A)
    (η : SSGRoute.GalQ → M)
    (hadd : ∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ)
    (hlc : SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η) :
    ∃ U : Subgroup ↥(SSGRoute.decomp ↥K A ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
      IsOpen (U : Set ↥(SSGRoute.decomp ↥K A ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup)) ∧
      ∀ x ∈ U,
        η ((((IntermediateField.fixingSubgroupEquiv K).symm x.1 : ↥(K.fixingSubgroup)) :
          SSGRoute.GalQ)) = 0 := by
  classical
  have hsplit' : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup := hsplit
  obtain ⟨U₀, hU₀open, hU₀⟩ := hlc
  have hη1 : η 1 = 0 := by
    have h := hadd 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [one_mul] at h
    exact (add_left_cancel (show η 1 + 0 = η 1 + η 1 from by rw [add_zero, ← h])).symm
  let U₁ : Subgroup ↥(SSGRoute.decomp ℚ A) := U₀.comap (SSGRoute.decomp ℚ A).subtype
  have hU₁open : IsOpen (U₁ : Set ↥(SSGRoute.decomp ℚ A)) := by
    rw [Subgroup.coe_comap]
    exact hU₀open.preimage continuous_subtype_val
  have hU₁vanish : ∀ x ∈ U₁, η (((x : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)) = 0 := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    have h := hU₀ 1 (Subgroup.one_mem _) ((x : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) hx x.2
    rw [one_mul, hη1] at h
    exact h
  obtain ⟨U', hU'open, hU'⟩ := Work.SSGRoute.exists_open_decompDown K A hsplit' U₁ hU₁open
  refine ⟨U'.comap (Subgroup.inclusion inf_le_left), ?_, ?_⟩
  · rw [Subgroup.coe_comap]
    exact IsOpen.preimage (Continuous.subtype_mk continuous_subtype_val _) hU'open
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    have hmem : SSGRoute.decompDownHom K A hsplit' (Subgroup.inclusion inf_le_left x) ∈ U₁ :=
      hU' _ hx
    have hfun : ⇑((SSGRoute.decompDownHom K A hsplit' (Subgroup.inclusion inf_le_left x) :
        ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
        = ⇑((((IntermediateField.fixingSubgroupEquiv K).symm x.1 : ↥(K.fixingSubgroup)) :
          SSGRoute.GalQ)) := by
      rw [Work.SSGRoute.coe_decompDownHom, Work.SSGRoute.coe_symm_fixingSubgroupEquiv]
      rfl
    have hgal : ((SSGRoute.decompDownHom K A hsplit' (Subgroup.inclusion inf_le_left x) :
        ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
        = (((IntermediateField.fixingSubgroupEquiv K).symm x.1 : ↥(K.fixingSubgroup)) :
          SSGRoute.GalQ) :=
      AlgEquiv.ext (funext_iff.mp hfun)
    rw [← hgal]
    exact hU₁vanish _ hmem

/-- **Grünwald over the base field `↥K` with coefficients in `E p (K ≃ₐ[ℚ] K) n i j`.**  This is the
`E`-valued form of `step4_grunwald_surjective_over_K`, obtained by the coordinatewise lift
`step4_grunwald_E_coordinatewise`: an additive, locally constant class on `Gal(ℚ̄/↥K)` with arbitrary
prescribed local behaviour on the decomposition groups `decomp ↥K A`, `A ∈ S`. -/
theorem step4_grunwald_E_over_K (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ)
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ (⊥ : IntermediateField ↥K SSGRoute.QBar))
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ↥K A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ↥K A B → A = B)
    (f : ∀ A : {A // A ∈ S},
      ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup) → E p (K ≃ₐ[ℚ] K) n i j)
    (hf : ∀ A : {A // A ∈ S},
      ∀ a b : ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
      f A (a * b) = f A a + f A b)
    (hfc : ∀ A : {A // A ∈ S},
      ∃ U : Subgroup ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
        (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
          (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup)) ∧
        ∀ x ∈ U, f A x = 0) :
    ∃ y : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E p (K ≃ₐ[ℚ] K) n i j,
      (∀ a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, y (a * b) = y a + y b) ∧
      SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) y ∧
      (∀ A : {A // A ∈ S},
        ∀ δ : ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
          (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
        y (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) = f A δ) := by
  classical
  haveI hE : Finite (E p (K ≃ₐ[ℚ] K) n i j) :=
    Work.CohomologicalShrinking.flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n i j
  have hfin : Module.Finite (ZMod p) (E p (K ≃ₐ[ℚ] K) n i j) := Module.Finite.of_finite
  let e : E p (K ≃ₐ[ℚ] K) n i j ≃ₗ[ZMod p]
      (Fin (Module.finrank (ZMod p) (E p (K ≃ₐ[ℚ] K) n i j)) → ZMod p) :=
    (Module.finBasis (ZMod p) (E p (K ≃ₐ[ℚ] K) n i j)).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p)
        (Fin (Module.finrank (ZMod p) (E p (K ≃ₐ[ℚ] K) n i j))))
  have hcoord : ∀ k : Fin (Module.finrank (ZMod p) (E p (K ≃ₐ[ℚ] K) n i j)),
      ∃ z : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, z (a * b) = z a + z b) ∧
        SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) z ∧
        (∀ A : {A // A ∈ S},
          ∀ δ : ↥(SSGRoute.decomp ↥K (A : ValuationSubring SSGRoute.QBar) ⊓
            (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup),
          z (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) = (e (f A δ)) k) := by
    intro k
    obtain ⟨z, h1, h2, h3⟩ :=
      step4_grunwald_surjective_over_K p K ζ hζ hζK S hSfin hSdisj
        (fun A x => (e (f A x)) k)
        (fun A a b => by simp only [hf A a b, map_add, Pi.add_apply])
        (fun A => by
          obtain ⟨U, hUo, hU⟩ := hfc A
          exact ⟨U, hUo, fun x hx => by simp [hU x hx]⟩)
    exact ⟨z, h1, h2, h3⟩
  choose z hza hzl hzag using hcoord
  refine ⟨fun σ => e.symm (fun k => z k σ), ?_, ?_, ?_⟩
  · intro a b
    change e.symm (fun k => z k (a * b)) = e.symm (fun k => z k a) + e.symm (fun k => z k b)
    have h1 : (fun k => z k (a * b)) = (fun k => z k a) + (fun k => z k b) := by
      funext k; exact hza k a b
    rw [h1]; exact map_add e.symm _ _
  · have hloc : ∀ k, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
        IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
        ∀ a : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, a ∈ (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) →
        ∀ u ∈ U, u ∈ (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) →
        z k (a * u) = z k a := fun k => hzl k
    choose U hUo hU using hloc
    refine ⟨⨅ k, U k, ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite (fun k => hUo k)
    · intro a ha u hu huH
      have hu' : ∀ k, u ∈ U k := fun k => (Subgroup.mem_iInf.mp hu) k
      have h1 : (fun k => z k (a * u)) = (fun k => z k a) := by
        funext k; exact hU k a ha u (hu' k) huH
      show e.symm (fun k => z k (a * u)) = e.symm (fun k => z k a)
      rw [h1]
  · intro A δ
    show e.symm (fun k => z k (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) = f A δ
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    exact hzag k A δ

end Work.SSGRoute
