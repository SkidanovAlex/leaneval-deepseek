import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.effSES_defs

set_option maxHeartbeats 3200000

/-!
# The descent step for the `Ext`/group-cohomology bridge

Given a natural family `D : NatFamily G n` of additive isomorphisms
`Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)` (`D.e`) with its coefficient naturality `D.nat`, this file proves that
the descent step `eStep G n D A : Hⁿ⁺¹(G,A) →+ Extⁿ⁺¹_G(ℤ,A)` (built in `effSES_defs` by
descending `dE ∘ D.e` along the surjection `dH` of the effacement sequence of `A`) is

* bijective (`eStep_bijective`),
* natural in the coefficient (`eStep_nat`),
* compatible with the connecting maps of an arbitrary short exact sequence (`eStep_delta`).

These three facts are exactly what is needed to iterate the step and produce the bridge
`Work.SSGRoute.Phi1.ExtGroupCohomologyBridge`.
-/

namespace Work.SSGRoute

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-- **The descent step is bijective.**  The two rows
`Hⁿ(I) → Hⁿ(C) → Hⁿ⁺¹(A) → 0` and `Extⁿ(I) → Extⁿ(C) → Extⁿ⁺¹(A) → 0` of the effacement
sequences have vanishing outer terms (`I` is injective), so the five lemma compares them. -/
theorem eStep_bijective (G : Type) [Group G] (n : ℕ) (D : NatFamily G n)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Function.Bijective (eStep G n D A) := by
  constructor
  · have hker : ∀ u, eStep G n D A u = 0 → u = 0 := by
      intro u hu
      obtain ⟨x, hx⟩ := dH_surj G n A u
      rw [← hx, eStep_dH, dE_apply] at hu
      obtain ⟨w₂, hw₂⟩ :=
        (extClass_comp_ker_iff G (effSES G A) (effSES_shortExact G A) n
          (D.e (effSES G A).X₃ x)).1 hu
      have h1 : D.e (effSES G A).X₃
          ((groupCohomology.map (MonoidHom.id G) (effSES G A).g n).hom
            ((D.e (effSES G A).X₂).symm w₂)) = D.e (effSES G A).X₃ x := by
        have hnat := D.nat (effSES G A).X₂ (effSES G A).X₃ (effSES G A).g
          ((D.e (effSES G A).X₂).symm w₂)
        simp only [AddEquiv.apply_symm_apply] at hnat
        exact hnat.trans hw₂
      have h2 : x = (groupCohomology.map (MonoidHom.id G) (effSES G A).g n).hom
          ((D.e (effSES G A).X₂).symm w₂) := ((D.e (effSES G A).X₃).injective h1).symm
      rw [← hx, h2]
      exact (groupCohomology_delta_ker_iff G (effSES G A) (effSES_shortExact G A) n
        ((groupCohomology.map (MonoidHom.id G) (effSES G A).g n).hom
          ((D.e (effSES G A).X₂).symm w₂))).2
        ⟨(D.e (effSES G A).X₂).symm w₂, rfl⟩
    intro u v huv
    have h0 : eStep G n D A (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker _ h0)
  · intro z
    obtain ⟨w, hw⟩ := dE_surj G n A z
    exact ⟨dH G n A ((D.e (effSES G A).X₃).symm w), by
      rw [eStep_dH, AddEquiv.apply_symm_apply, hw]⟩

/-- **Naturality of the descent step.**  Naturality of `D` in degree `n`, transported through the
comparison morphism `effHom φ` of the two effacement sequences, gives naturality of `eStep` in
degree `n + 1`. -/
theorem eStep_nat (G : Type) [Group G] (n : ℕ) (D : NatFamily G n)
    (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B)
    (y : groupCohomology A (n + 1)) :
    eStep G n D B
        ((groupCohomology.map (MonoidHom.id G) φ (n + 1)).hom y) =
      (eStep G n D A y).comp (Abelian.Ext.mk₀ φ) (add_zero (n + 1)) := by
  obtain ⟨x, hx⟩ := dH_surj G n A y
  have hδ := groupCohomology.δ_naturality (effSES_shortExact G A) (effSES_shortExact G B)
    (effHom G φ) n (n + 1) rfl
  have hδ' : (groupCohomology.δ (effSES_shortExact G A) n (n + 1) rfl) ≫
        (groupCohomology.map (MonoidHom.id G) φ (n + 1)) =
      (groupCohomology.map (MonoidHom.id G) (effHom G φ).τ₃ n) ≫
        (groupCohomology.δ (effSES_shortExact G B) n (n + 1) rfl) := by
    simpa only [effHom_τ₁] using hδ
  have hnat_delta : (groupCohomology.map (MonoidHom.id G) φ (n + 1)).hom (dH G n A x) =
      dH G n B ((groupCohomology.map (MonoidHom.id G) (effHom G φ).τ₃ n).hom x) := by
    have h := congrArg
      (fun (g : groupCohomology (effSES G A).X₃ n ⟶ groupCohomology (effSES G B).X₁ (n + 1)) =>
        g x) hδ'
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h
    rw [dH_apply, dH_apply]
    exact h
  rw [← hx, hnat_delta]
  rw [eStep_dH, eStep_dH]
  rw [D.nat (effSES G A).X₃ (effSES G B).X₃ (effHom G φ).τ₃ x]
  rw [dE_apply, dE_apply]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [← ShortComplex.ShortExact.extClass_naturality
    (effSES_shortExact G A) (effSES_shortExact G B) (effHom G φ)]
  rw [effHom_τ₁]

/-- **Compatibility of the descent step with connecting maps.**  For an arbitrary short exact
sequence `S`, the comparison morphism `bridgeHom S : S ⟶ effSES S.X₁` (extending the identity of
`S.X₁`) together with the naturality of `δ`, of `extClass` and of `D` identifies
`eStep` on `δ` with composition with `S.extClass`. -/
theorem eStep_delta (G : Type) [Group G] (n : ℕ) (D : NatFamily G n)
    (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) (y : groupCohomology S.X₃ n) :
    eStep G n D S.X₁
        ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
      (D.e S.X₃ y).comp hS.extClass rfl := by
  have hδ := groupCohomology.δ_naturality hS (effSES_shortExact G S.X₁)
    (bridgeHom G S hS) n (n + 1) rfl
  have hδ' : (groupCohomology.δ hS n (n + 1) rfl) =
      (groupCohomology.map (MonoidHom.id G) (bridgeHom G S hS).τ₃ n) ≫
        (groupCohomology.δ (effSES_shortExact G S.X₁) n (n + 1) rfl) := by
    have h := hδ
    rw [bridgeHom_τ₁, groupCohomology.map_id, Category.comp_id] at h
    exact h
  have hδy : dH G n S.X₁
      ((groupCohomology.map (MonoidHom.id G) (bridgeHom G S hS).τ₃ n).hom y) =
      (groupCohomology.δ hS n (n + 1) rfl).hom y := by
    have h := congrArg
      (fun (g : groupCohomology S.X₃ n ⟶ groupCohomology (effSES G S.X₁).X₁ (n + 1)) => g y) hδ'
    rw [CategoryTheory.comp_apply] at h
    rw [dH_apply]
    exact h.symm
  rw [← hδy]
  rw [eStep_dH]
  rw [D.nat S.X₃ (effSES G S.X₁).X₃ (bridgeHom G S hS).τ₃ y]
  rw [dE_apply]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [← ShortComplex.ShortExact.extClass_naturality hS (effSES_shortExact G S.X₁)
    (bridgeHom G S hS)]
  rw [bridgeHom_τ₁, Abelian.Ext.comp_mk₀_id]

/-! ## The recursion -/

/-- The recursive family of natural additive isomorphisms `Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)`, starting at
degree `0` with the canonical `eZero` and iterating the descent step. -/
noncomputable def eSeq (G : Type) [Group G] : ∀ n, NatFamily G n
  | 0 => ⟨fun A => eZero G A, fun A B φ y => eZero_nat G A B φ y⟩
  | n + 1 => ⟨
      fun A => AddEquiv.ofBijective (eStep G n (eSeq G n) A)
        (eStep_bijective G n (eSeq G n) A),
      fun A B φ y => eStep_nat G n (eSeq G n) A B φ y⟩

/-- The degree-`n` isomorphism `Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)` produced by the recursion. -/
noncomputable def eSeqFun (G : Type) [Group G] (n : ℕ) (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    groupCohomology A n ≃+ SSGRoute.PTExt.extH A n :=
  (eSeq G n).e A

theorem eSeqFun_nat (G : Type) [Group G] (n : ℕ)
    (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B) (y : groupCohomology A n) :
    eSeqFun G n B ((groupCohomology.map (MonoidHom.id G) φ n).hom y) =
      (eSeqFun G n A y).comp (Abelian.Ext.mk₀ φ) (add_zero n) :=
  (eSeq G n).nat A B φ y

theorem eSeqFun_delta (G : Type) [Group G] (n : ℕ)
    (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact)
    (y : groupCohomology S.X₃ n) :
    eSeqFun G (n + 1) S.X₁ ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
      (eSeqFun G n S.X₃ y).comp hS.extClass rfl :=
  eStep_delta G n (eSeq G n) S hS y

end

end Work.SSGRoute
