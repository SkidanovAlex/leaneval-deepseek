import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.ramifiedPlaces_finite
import Submission.Work.SSGRoute.flowKernel_fixedField
import Submission.Work.SSGRoute.fixedField_of_le_fixingSubgroup
import Submission.Work.SSGRoute.step4_transport_of_sha13_psi
import Submission.Work.SSGRoute.step4_items_assembly
import Submission.Work.SSGRoute.t0Generation_cyclic
import Submission.Work.SSGRoute.properStageAssemblyData
import Submission.Work.CohomologicalShrinking.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The Step-4 assembly: from the arithmetic bundle to `Step4Input`

This module contains the part of `Work.SSGRoute.step4_shrunk_input` that is *not* arithmetic:
namely the passage from

* the level-`n` stage-3 data `(φ, ψ)` and the finite set `T⁰`;
* the field `Λ` of `ψ`, the finite set `S` of places over `Ram(Λ) ∪ {p}`, a section `sec`;
* the datum `y` (the prescribed local targets over `K`, from `coker_obstruction` over `K`) and the
  class `x = cor(y)` with Theorem 13's local clauses (`hxsplit`, `hxnot`, `hxinertia`, `hxloc`, the
  involution clause);
* the `y`/`x`-bundle of `Work.SSGRoute.step4_items_assembly` (`hreal`, `hcycOut`, `hdich`),

to the conclusion `Step4Input p K n i j` of the sibling node
`Work.SSGRoute.scholz_succ_of_properStage` (definitionally the body of
`Work.SSGRoute.step4_shrunk_input`).

Everything except the two inputs named above is on disk and `sorry`-free.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

set_option maxHeartbeats 2000000


/-- A section of `G_ℚ → Gal(K/ℚ)` (local re-proof of `exists_section_restrict`). -/
theorem exists_section_local (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    [Normal ℚ K] :
    ∃ sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ, ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s := by
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  have : Normal ℚ SSGRoute.QBar := inferInstance
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom K) :=
    AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) (E := SSGRoute.QBar)
  exact ⟨fun s => Classical.choose (hsurj s), fun s => Classical.choose_spec (hsurj s)⟩

/-- A sibling-free copy of the predicate `Step4Input` of `scholz_succ_of_properStage`
(definitionally the same bundle; this module must not import that node, since that node imports
this one once the arithmetic lands). -/
def Step4InputData (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ) : Prop :=
  ∃ (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ),
      SSGRoute.IsScholzSolution p K n i j φ ∧ SSGRoute.LiftsFlow ψ φ ∧
      IsOpen (ψ.ker : Set SSGRoute.GalQ) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
        ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1) ∧
      (∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
        ((∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) ∨
          (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
            ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ))) ∧
      SSGRoute.IsLocConstOn ⊤ x ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x) ∧
      (∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (Subgroup.zpowers c) x) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1)) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
          (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
        IsCyclic ((SSGRoute.decomp ℚ A).map
          (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul))) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
          (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
        (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ) →
        IsCyclic ((SSGRoute.decomp ℚ A).map
            (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul)) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) τ =
            (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) σ) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = Work.SSGRoute.flowEKer p (K ≃ₐ[ℚ] K) n i j ∧
      (∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = 0) ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ))

/-! ## The local target at a place over `p`

At a finite place `A` over `p` the prescription of the paper is `η := 0`: the level-`τ+1` solution
`ψ` is trivial on `D_A ∩ G_K` by the `T¹`-clause, so the twist of `ψ` by `0` is trivial on `D_A`
(hence cyclic and inertia-generated, the trivial group being generated by its inertia), and the
cokernel datum agrees with `x = 0`.  This is the `p`-adic counterpart of
`Work.SSGRoute.step4_local_target`, which is stated only for `ℓ ≠ p` (it uses the pro-cyclicity of
the tame inertia). -/
theorem step4_local_target_over_p (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = Work.SSGRoute.restrict K σ)
    (hT1 : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (A : ValuationSubring SSGRoute.QBar) (hAfin : SSGRoute.IsFinPlace ℚ A)
    (hAp : A.valuation (p : SSGRoute.QBar) < 1)
    (hφ1 : ∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) (hx0 : ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = 0) :
    ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
      (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
      IsCyclic (Subgroup.closure
        ((Work.SSGRoute.flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        Work.SSGRoute.flowTwistE p K n i j η ψ τ =
          Work.SSGRoute.flowTwistE p K n i j η ψ σ) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ := by
  -- `D_A ≤ G_K` because `φ` is trivial on `D_A`
  have hDK : ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup := by
    intro σ hσ
    exact mem_fixingSubgroup_of_restrict_eq_one K (by rw [← hφquot σ, hφ1 σ hσ, map_one])
  -- `ψ` is trivial on `D_A`
  have hψ1 : ∀ σ ∈ SSGRoute.decomp ℚ A, ψ σ = 1 :=
    fun σ hσ => hT1 A ⟨hAfin, Or.inl hAp⟩ σ hσ (hDK σ hσ)
  refine ⟨0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ _ τ _; simp
  · exact ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩
  · intro σ _; rfl
  · -- the twist of `ψ` by `0` is trivial on `D_A`
    have htw : ∀ σ ∈ SSGRoute.decomp ℚ A, Work.SSGRoute.flowTwistE p K n i j 0 ψ σ = 1 := by
      intro σ hσ
      rw [Work.SSGRoute.flowTwistE_eq_of_eq_zero p K n i j 0 ψ (H := SSGRoute.decomp ℚ A)
        (fun τ _ => rfl) σ hσ]
      exact hψ1 σ hσ
    have himg : (Work.SSGRoute.flowTwistE p K n i j 0 ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ)
        = {(1 : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)} := by
      ext y
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact Set.mem_singleton_iff.mpr (htw σ hσ)
      · intro hy
        exact ⟨1, SSGRoute.decomp ℚ A |>.one_mem, by rw [Set.mem_singleton_iff.mp hy]; exact htw 1 (Subgroup.one_mem _)⟩
    rw [himg]
    have : Subgroup.closure ({(1 : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)} :
        Set (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)) = ⊥ := by simp
    rw [this]
    exact isCyclic_of_subsingleton
  · -- the inertia generates the (trivial) local group of the twist
    intro σ hσ
    refine ⟨1, ?_, ?_⟩
    · exact ⟨Subgroup.one_mem _, fun x _ => by simp⟩
    · rw [Work.SSGRoute.flowTwistE_eq_of_eq_zero p K n i j 0 ψ (H := SSGRoute.decomp ℚ A)
        (fun τ _ => rfl) σ hσ, hψ1 σ hσ]
      exact (Work.SSGRoute.flowTwistE_eq_of_eq_zero p K n i j 0 ψ (H := SSGRoute.decomp ℚ A)
        (fun τ _ => rfl) 1 (Subgroup.one_mem _)).trans (hψ1 1 (Subgroup.one_mem _))
  · exact hx0

/-! ## The assembly

The following is the whole of `Step4Input p K n i j` minus the arithmetic: given the stage-3 data,
the finite set `T⁰`, the field `Λ` of `ψ`, the places `S`, the datum `y` and the class `x = cor(y)`
with the clauses of Theorem 13, plus the `y`/`x`-bundle of `item5_of_bundle`/`item6_of_bundle`, it
produces the full `Step4Input` bundle. -/
/-- **Item (5) of the assembly.**  The local cyclicity of the twist at the places of new
ramification outside `T⁰`, from the `y`/`x` bundle: the local-target bridge at the conjugates of
`S`, Theorem 13's cyclicity clause outside them, and vacuity where the twist is unramified. -/
theorem item5_of_bundle_guarded (p : ℕ) [Fact p.Prime] (K Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n
      (tauSucc i j).1 (tauSucc i j).2)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = Work.SSGRoute.restrict K σ)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hΛker : ψ.ker = Λ.fixingSubgroup)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0)
    (hreal : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
      ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
        (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
        IsCyclic (Subgroup.closure
          ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    (hcycOut : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → SSGRoute.IsSplitIn ℚ Λ B →
      ∃ U : Subgroup SSGRoute.GalQ,
        (∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
          U = V ⊓ SSGRoute.decomp ℚ B) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ U, δ * u * δ⁻¹ ∈ U) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ U) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) U x) :
    ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
      IsCyclic ((SSGRoute.decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) := by
  intro A hAfin hAT0 hram hφ1
  by_cases hS : ∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A
  · -- the local target at `A` and the pointwise bridge
    obtain ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩ := hreal A hAfin hAT0 hS hram hφ1
    have hb := step4_local_cyclic_of_eq_on p K n i j ψ x A
      ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩
    rw [← closure_image_eq_map (flowTwistEHom p K n i j x ψ hψquot hxmul)
      (SSGRoute.decomp ℚ A)]
    exact hb.1
  · have hS' : ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace ℚ A₀ A :=
      fun A₀ hA₀ hconj => hS ⟨A₀, hA₀, hconj⟩
    by_cases hΛ : SSGRoute.IsSplitIn ℚ Λ A
    · -- Theorem 13's cyclicity clause, at a place where `ψ` is trivial on `D_A`
      have hDK := decomp_le_fixingSubgroup_of_eq_one p K n i j φ hφquot A hφ1
      have hψA := eq_one_of_isSplitIn p K Λ n i j ψ hΛker A hΛ
      exact twist_cyclic_of_psi_trivial p K n i j x ψ hψquot hxmul A hDK hψA
        (hcycOut A hAfin hS' hΛ)
    · -- vacuity: both `ψ` and `x` are unramified on `I_A ∩ G_K`
      obtain ⟨σ, hI, hσK, hne⟩ := hram
      have hx0 : x σ = 0 := hxinertia A hAfin hS' hΛ σ hI
      have hnotram : ¬ SSGRoute.IsRamifiedIn ℚ Λ A :=
        fun hram' => hS (hSram A hAfin (Or.inl hram'))
      have hσΛ : σ ∈ Λ.fixingSubgroup := by
        by_contra hcon
        exact hnotram ⟨σ, hI, hcon⟩
      have hψ1 : ψ σ = 1 := by
        rw [← MonoidHom.mem_ker, hΛker]
        exact hσΛ
      rw [flowTwistEHom_apply, flowTwistE, flowTwist, hx0, hψ1] at hne
      simp at hne

/-- **Item (6) of the assembly.**  The transfer of the cyclic local structure from `ψ` to the twist,
from the `y`/`x` bundle.

The bundle input `hdich` is the paper's two local prescriptions at the places where the twist is
ramified: either `x` is a `1`-coboundary on `D_A` — so that on `D_A` the twist is the conjugate of
`ψ` (`Work.SSGRoute.flowTwistEHom_eq_conj_of_isCoboundaryOn`) and both properties transfer from the
hypothesis on `ψ` — or the local target realises the twist (`Work.SSGRoute.step4_local_target`),
when `pointwise agreement on `D_A`` gives both properties by the bridge
`Work.SSGRoute.step4_local_cyclic_of_eq_on`.  (This is the `T²` prescription "subtract the unramified
part" together with the `T³` local targets; at the places where `ψ` is trivial on `D_A` and `x`
ramifies the coboundary case is what Theorem 13's `hxnot`/`hxsplit` supplies.) -/
theorem item6_of_bundle_guarded (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n
      (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hdich : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x ∨
        ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
          (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
          IsCyclic (Subgroup.closure
            ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ) :
    ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ) →
      IsCyclic ((SSGRoute.decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          (flowTwistEHom p K n i j x ψ hψquot hxmul) τ =
          (flowTwistEHom p K n i j x ψ hψquot hxmul) σ := by
  intro A hAfin hramψ hramtw hcycψ
  rcases hdich A hAfin hramψ hramtw with hcob | ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩
  · -- the twist is the conjugate of `ψ` on `D_A`: everything transfers
    obtain ⟨M, hM⟩ := flowTwistEHom_eq_conj_of_isCoboundaryOn p K n i j x ψ hψquot hxmul
      (H := SSGRoute.decomp ℚ A) hcob
    refine ⟨isCyclic_map_flowTwistEHom_of_isCoboundaryOn p K n i j x ψ hψquot hxmul
      (H := SSGRoute.decomp ℚ A) hcob hcycψ.1, ?_⟩
    intro σ hσ
    obtain ⟨τ, hτ, hτeq⟩ := hcycψ.2 σ hσ
    exact ⟨τ, hτ, by rw [hM τ hτ.1, hM σ hσ, hτeq]⟩
  · -- the local target realises the twist: the bridge
    obtain ⟨hb1, hb2⟩ := step4_local_cyclic_of_eq_on p K n i j ψ x A
      ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩
    refine ⟨?_, ?_⟩
    · rw [← closure_image_eq_map (flowTwistEHom p K n i j x ψ hψquot hxmul)
        (SSGRoute.decomp ℚ A)]
      exact hb1
    · intro σ hσ
      obtain ⟨τ, hτ, hτeq⟩ := hb2 σ hσ
      exact ⟨τ, hτ, by rw [flowTwistEHom_apply, flowTwistEHom_apply]; exact hτeq⟩

theorem step4Input_of_bundle (p : ℕ) [Fact p.Prime] (K Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] [FiniteDimensional ℚ Λ] [Normal ℚ Λ] (hKΛ : K ≤ Λ)
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hφ : SSGRoute.IsScholzSolution p K n i j φ)
    (hLift : SSGRoute.LiftsFlow ψ φ)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = Work.SSGRoute.restrict K σ)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hΛker : ψ.ker = Λ.fixingSubgroup)
    (hT1ψ : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (hInvψ : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1)
    (hProp : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      ((∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) ∨
        (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ)))
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hxloc : SSGRoute.IsLocConstOn ⊤ x)
    (hxsplit : ∀ A ∈ S, SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hxnot : ∀ A ∈ S, ¬ SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) x)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0)
    (hinv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (Subgroup.zpowers c) x)
    (hreal : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
      ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
        (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
        IsCyclic (Subgroup.closure
          ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    (hcycOut : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → SSGRoute.IsSplitIn ℚ Λ B →
      ∃ U : Subgroup SSGRoute.GalQ,
        (∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
          U = V ⊓ SSGRoute.decomp ℚ B) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ U, δ * u * δ⁻¹ ∈ U) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ U) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) U x)
    (hdich : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x ∨
        ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
          (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
          IsCyclic (Subgroup.closure
            ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    (hT0gen : (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j)
    (hxT0 : ∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = 0)
    (hT0cyc : ∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ)) :
    Step4InputData p K n i j := by
  have hxcoc : SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) ⊤ x := fun g _ h _ => hxmul g h
  obtain ⟨hT1cob, hram⟩ :=
    step4_transport_general p K Λ hKΛ n i j
      (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) ψ hΛker S hSfin hSram sec hsec y hyT hy0
      x hxcoc hxsplit hxnot hxinertia
  refine ⟨φ, ψ, hψquot, T0, x, hxmul, hφ, hLift, hopen, hT1ψ, hInvψ, hProp, hxloc, hT1cob, hinv,
    ?_, ?_, ?_, hT0gen, hxT0, hT0cyc⟩
  · -- item (4): if `x` ramifies at `A` then `φ` is trivial on `D_A`
    intro A hAfin hramA
    obtain ⟨σ, hσI, hσK, hne⟩ := hramA
    obtain ⟨hnotconj, hψ1⟩ := hram A hAfin ⟨σ, hσI, hσK, hne⟩
    intro δ hδ
    have hδ' : flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (ψ δ) = φ δ :=
      (liftsFlowAt_iff_flowGroupSucc p K n i j (ψ δ) (φ δ)).mp (hLift δ)
    rw [← hδ', hψ1 δ hδ, map_one]
  · -- item (5)
    exact item5_of_bundle_guarded p K Λ n i j φ ψ hφquot hψquot hΛker S hSram T0 x hxmul
      hxinertia hreal hcycOut
  · -- item (6)
    exact item6_of_bundle_guarded p K n i j ψ hψquot x hxmul hdich

/-! ## The field of a level-`τ+1` flow solution

The construction `flowKernel_fixedField` is stated for the level `(i,j)`; Step 4 needs the field of
the level-`τ+1` map `ψ`.  The proof is the same (only the `G`-component of `ψ` is used). -/
theorem exists_field_of_flowKernel (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hflow : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      AlgEquiv.restrictNormalHom K σ) :
    ∃ N : IntermediateField ℚ SSGRoute.QBar, FiniteDimensional ℚ N ∧ IsGalois ℚ N ∧ K ≤ N ∧
      ψ.ker = N.fixingSubgroup ∧
      (∀ A : ValuationSubring SSGRoute.QBar,
        SSGRoute.IsSplitIn ℚ N A ↔ ∀ σ ∈ SSGRoute.decomp ℚ A, ψ σ = 1) ∧
      ∀ A : ValuationSubring SSGRoute.QBar,
        SSGRoute.IsRamifiedIn ℚ N A ↔ ∃ σ, SSGRoute.IsInertia ℚ A σ ∧ ψ σ ≠ 1 := by
  classical
  haveI hAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hclosed : IsClosed (ψ.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isClosed_of_isOpen ψ.ker hopen
  let N : IntermediateField ℚ SSGRoute.QBar := IntermediateField.fixedField ψ.ker
  have hfix : N.fixingSubgroup = ψ.ker := by
    have h := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := AlgebraicClosure ℚ)
      (⟨ψ.ker, hclosed⟩ : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    simpa [N] using h
  refine ⟨N, ?_, ?_, ?_, hfix.symm, ?_, ?_⟩
  · refine (InfiniteGalois.isOpen_iff_finite (k := ℚ) (K := AlgebraicClosure ℚ) N).mp ?_
    rw [hfix]
    exact hopen
  · exact IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := AlgebraicClosure ℚ) ψ.ker
      (hn := MonoidHom.normal_ker ψ)
  · show K ≤ IntermediateField.fixedField ψ.ker
    rw [IntermediateField.le_iff_le]
    intro σ hσ
    refine mem_fixingSubgroup_of_restrict_eq_one K ?_
    rw [← hflow σ, MonoidHom.mem_ker.mp hσ, map_one]
  · intro A
    rw [SSGRoute.IsSplitIn, SetLike.le_def]
    constructor
    · intro h σ hσ
      exact MonoidHom.mem_ker.mp (hfix ▸ h hσ)
    · intro h σ hσ
      exact hfix.symm ▸ MonoidHom.mem_ker.mpr (h σ hσ)
  · intro A
    rw [SSGRoute.IsRamifiedIn, hfix]
    constructor
    · rintro ⟨σ, hI, hne⟩
      exact ⟨σ, hI, fun h => hne (MonoidHom.mem_ker.mpr h)⟩
    · rintro ⟨σ, hI, hne⟩
      exact ⟨σ, hI, fun h => hne (MonoidHom.mem_ker.mp h)⟩

/-! ## The non-arithmetic data of Step 4

Given the level-`n` stage-3 data, the rest of the *data* of Step 4 (the field `Λ` of `ψ`, the finite
sets `S` and `T⁰`, and a section `sec` of `G_ℚ → Gal(K/ℚ)`) is produced here from the proved pieces:
`flowKernel_fixedField` (the field of `ψ`), `ramifiedPlaces_finite` (the places over
`Ram(Λ) ∪ {p}`, one per prime), `exists_T0_cyclic_of_surjective` (Chebotarev) and
`exists_section_restrict`.  The only Step-4 input not produced here is the arithmetic (`y`, `x`). -/
theorem exists_step4_data (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hsurj : Function.Surjective ψ)
    (hflow : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ) :
    ∃ (Λ : IntermediateField ℚ SSGRoute.QBar) (S T0 : Finset (ValuationSubring SSGRoute.QBar))
      (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ),
      FiniteDimensional ℚ Λ ∧ IsGalois ℚ Λ ∧ K ≤ Λ ∧ ψ.ker = Λ.fixingSubgroup ∧
      (∀ A ∈ S, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ℚ A B → A = B) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ)) ∧
      (∀ s : K ≃ₐ[ℚ] K, AlgEquiv.restrictNormalHom K (sec s) = s) := by
  obtain ⟨Λ, hfd, hgal, hKΛ, hker, -, -⟩ :=
    exists_field_of_flowKernel p K n i j ψ hopen hflow
  haveI : IsGalois ℚ Λ := hgal
  haveI : FiniteDimensional ℚ Λ := hfd
  obtain ⟨S, hSfin, hSdisj, hSram⟩ := ramifiedPlaces_finite p Λ
  obtain ⟨T0, hT0gen, hT0cyc⟩ := t0Generation_cyclic
    (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) ψ hopen hsurj
    (flowEKer p (K ≃ₐ[ℚ] K) n i j)
  obtain ⟨sec, hsec⟩ := exists_section_local K
  exact ⟨Λ, S, T0, sec, hfd, hgal, hKΛ, hker, hSfin, hSdisj, hSram, hT0gen, hT0cyc, hsec⟩


/-! ## What remains for `Work.SSGRoute.step4_shrunk_input`

With this module (all `sorry`-free, axiom-clean — verified by `#print axioms`) the target of
`Work.SSGRoute.step4_shrunk_input` reduces to the following **arithmetic** obligations, everything
else being proved above or on disk:

1. *The data.*  From `hP n hn`, `IsProperStage p K n i j` gives `(φ, ψ)` with the stage-3 clauses;
   `exists_step4_data` then supplies `Λ` (the field of `ψ`, with `Λ.fixingSubgroup = ψ.ker`), the
   finite set `S` (one place per prime of `Ram(Λ) ∪ {p}`), the finite set `T⁰`
   (`exists_T0_cyclic_of_surjective`) and the section `sec`.

2. *The prescribed local data and its realisation (`coker_obstruction` over the base `K`).*  At each
   place `A ∈ S` whose decomposition group lies in `G_K` and where `φ` is trivial:
   * if `A` lies over `p`, the datum is `0` and the `T¹`-clause of the stage-3 data already makes
     the twist trivial (`step4_local_target_over_p` above);
   * otherwise the datum is the local target `η_A` of `Work.SSGRoute.step4_local_target` (which
     makes the twist of `ψ` by `η_A` cyclic and inertia-generated).
   The arithmetic input is that these data are realised by a global cocycle `y` over `K`
   (SW pp. 30–31: the second shrinking, via `coker_obstruction` over `K` and
   `exists_shrinking_H1`), i.e. `x = cor(y)` agrees *pointwise* with `η_A` on `D_A` (the coboundary
   ambiguity vanishes on `D_A` because `D_A ≤ G_K` acts trivially: `eq_zero_of_isCoboundaryOn`).
   This is the hypothesis `hreal` of `step4Input_of_bundle`.

3. *The class `x` (`SSGRoute.shafarevich_theorem13` / `shafarevich_existence` with `Λ` the field of
   `ψ`).*  The clauses (1)–(7) of Theorem 13 for `x = cor(z)` are exactly: `hxmul`, `hxloc`, the
   coboundary clauses at the places of `S` (which give `x`'s pointwise agreement above), the
   involution clause `hinv`, `hxinertia`, and the cyclicity clause `hcycOut`.

4. *The local dichotomy `hdich`* (the `T²`/`T³` prescriptions at the places where the twist is
   ramified): either `x` is a coboundary on `D_A`, or the local target realises the twist.

Items (5) and (6) of the conclusion then follow from `item5_of_bundle`/`item6_of_bundle`
(`step4_items_assembly.lean`), and the remaining conjuncts from `step4_transport_general`
(`step4_transport_of_sha13_psi.lean`).
5. *Import hygiene (one-line flips elsewhere).*  This module imports
   `step4_items_assembly`, which imports `twist_cyclic_of_psi_trivial`, which still imports
   `scholz_succ_of_properStage`; likewise `step4_local_target` imports it.  Each of those files
   elaborates and proves its statement with that import replaced by
   `Submission.Work.SSGRoute.twistLayer` (checked by the prover of `scholz_succ_of_properStage` in
   its Addendum IV), and `step4_shrunk_input` itself must keep its own import until its proof is
   replaced by the arithmetic.  After the flips this module becomes importable by
   `scholz_succ_of_properStage`, so that the body of `step4Input_of_properStages` can be the single
   call `step4Input_of_bundle ...` (its conclusion `Step4InputData p K n i j` is definitionally
   `Step4Input p K n i j`).
-/


/-! ## The Theorem-13 wiring of Step 4

Clauses (1)–(7) of `SSGRoute.shafarevich_existence` are *exactly* the `x`-hypotheses of
`step4Input_of_bundle`, with two conversions done here: clause (7) becomes `hcycOut` (taking
`U := decomp ℚ B ⊓ V`), and clause (3), evaluated at the places of `T⁰` — which the arithmetic
places inside `S` (`hT0S`), splitting in `K` (`hT0split`), with prescribed local datum `0`
(`hyT0`) — gives `x = 0` on their decomposition groups.  The hypotheses `hreal` and `hdich` are
the remaining arithmetic ones and are consumed with `x` already in hand, which is the form in
which the local-target side produces them. -/
theorem step4_bundle_of_sha13 (p : ℕ) [Fact p.Prime] (K Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] [FiniteDimensional ℚ Λ] (hΛgal : IsGalois ℚ Λ)
    (hKΛ : K ≤ Λ) (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hφ : SSGRoute.IsScholzSolution p K n i j φ) (hLift : SSGRoute.LiftsFlow ψ φ)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = Work.SSGRoute.restrict K σ)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hΛker : ψ.ker = Λ.fixingSubgroup)
    (hT1ψ : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (hInvψ : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1)
    (hProp : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      ((∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) ∨
        (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ)))
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (hT0gen : (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j)
    (hT0cyc : ∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ))
    (hT0S : ∀ A ∈ T0, A ∈ S)
    (hT0split : ∀ A ∈ T0, SSGRoute.IsSplitIn ℚ K A)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0)
    (hyT0 : ∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A,
      (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hxloc : SSGRoute.IsLocConstOn ⊤ x)
    (hxsplit : ∀ A ∈ S, SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hxnot : ∀ A ∈ S, ¬ SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) x)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0)
    (hinv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (Subgroup.zpowers c) x)
    (hcyc7 : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) →
      ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ SSGRoute.decomp ℚ B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ B ⊓ V) x)
    (hreal : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
      ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
        (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
        IsCyclic (Subgroup.closure
          ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    (hdich : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x ∨
        ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
          (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
          IsCyclic (Subgroup.closure
            ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    : Step4InputData p K n i j := by
  haveI : Normal ℚ Λ := hΛgal.to_normal
  have hxT0 : ∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = 0 := by
    intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := hT0split A hA hσ
    have hcob := hxsplit A (hT0S A hA) (hT0split A hA)
    have h0 : x σ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) = 0 :=
      eq_zero_of_isCoboundaryOn p K n i j
        (x := fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s))
        hcob σ hσ hσK
    rw [hyT0 A hA σ hσ, sub_zero] at h0
    exact h0
  have hcycOut : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → SSGRoute.IsSplitIn ℚ Λ B →
      ∃ U : Subgroup SSGRoute.GalQ,
        (∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
          U = V ⊓ SSGRoute.decomp ℚ B) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ U, δ * u * δ⁻¹ ∈ U) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ U) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) U x := by
    intro B hB hconj _
    obtain ⟨V, hVopen, hnorm, hgen, hcob⟩ := hcyc7 B hB hconj
    refine ⟨SSGRoute.decomp ℚ B ⊓ V, ?_, ?_, ?_, ?_⟩
    · exact ⟨V, hVopen, inf_comm _ _⟩
    · intro δ hδ u hu
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hδ hu.1) (Subgroup.inv_mem _ hδ),
          hnorm δ hδ u hu⟩
    · obtain ⟨g, hg, hgm⟩ := hgen
      refine ⟨g, hg, fun δ hδ => ?_⟩
      obtain ⟨m, hm⟩ := hgm δ hδ
      exact ⟨m, Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _
        (Subgroup.inv_mem _ hδ) (Subgroup.zpow_mem _ hg m), hm⟩⟩
    · exact hcob
  exact step4Input_of_bundle p K Λ hKΛ n i j hj hji φ ψ hφ hLift hφquot hψquot hopen hΛker
    hT1ψ hInvψ hProp S hSfin hSram sec hsec y hyT hy0 T0 x hxmul hxloc hxsplit hxnot hxinertia
    hinv hreal hcycOut hdich hT0gen hxT0 hT0cyc

end Work.SSGRoute
