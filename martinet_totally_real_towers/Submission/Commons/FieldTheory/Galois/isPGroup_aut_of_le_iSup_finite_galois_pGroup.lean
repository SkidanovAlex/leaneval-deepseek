import Mathlib
import Submission.Commons.FieldTheory.Galois.fixingSubgroup_iSup_of_fintype
import Submission.Commons.FieldTheory.Galois.isGalois_iSup_of_charZero
import Submission.Commons.FieldTheory.IntermediateField.restrict_iSup_eq_top
import Submission.Commons.FieldTheory.IntermediateField.exists_finset_of_le_iSup_of_finiteDimensional
import Submission.Commons.GroupTheory.PGroup.of_injective_pi

/-!
# The Galois group of a subextension of a compositum of `p`-group extensions is a `p`-group

Let `F` be a field of characteristic zero, `K / F` a field extension and `f : ι → IntermediateField F K`
a family of finite-dimensional Galois subextensions of `K / F` whose Galois groups
`Gal(f i / F)` are `p`-groups.  This file shows that whenever `L ≤ ⨆ i, f i` is a
finite-dimensional Galois subextension of `K / F`, then `Gal(L / F)` is a `p`-group as well.

The argument is the standard one: `L` is finite over `F`, hence lies in a finite sub-compositum
`M = ⨆_{i ∈ s} f i`; the compositum `M` is again finite Galois over `F`, and restriction of
`F`-automorphisms of `M` to the (normal) subextensions `f i` embeds `Gal(M/F)` into the finite
product of the `p`-groups `Gal(f i / F)`, so `Gal(M/F)` is a `p`-group.  Finally `Gal(L/F)` is a
quotient of `Gal(M/F)` (restriction along the normal subextension `L ⊆ M`), hence a `p`-group.
-/

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

open _root_.IntermediateField

lemma isPGroup_aut_of_le_iSup_finite_galois_pGroup {F K : Type*} [Field F] [CharZero F]
    [Field K] [Algebra F K] {p : ℕ} [Fact (Nat.Prime p)]
    {ι : Type*} {f : ι → IntermediateField F K}
    (hfd : ∀ i, FiniteDimensional F ↥(f i))
    (hgal : ∀ i, IsGalois F ↥(f i)) (hpg : ∀ i, IsPGroup p (↥(f i) ≃ₐ[F] ↥(f i)))
    {L : IntermediateField F K} (hL : L ≤ ⨆ i, f i)
    [FiniteDimensional F ↥L] [IsGalois F ↥L] :
    IsPGroup p (↥L ≃ₐ[F] ↥L) := by
  classical
  have hfdI : ∀ i, FiniteDimensional F ↥(f i) := hfd
  haveI := hfdI
  haveI hnormf : ∀ i, Normal F ↥(f i) := fun i => (hgal i).to_normal
  -- Step 1: reduce to a finite sub-compositum.
  obtain ⟨s, hs⟩ :=
    Commons.FieldTheory.IntermediateField.exists_finset_of_le_iSup_of_finiteDimensional hL
  set M : IntermediateField F K := ⨆ i : {x // x ∈ s}, f i.1 with hM
  have hLM : L ≤ M := by
    rw [hM]
    refine le_trans hs ?_
    refine iSup_le (fun i => iSup_le (fun hi => ?_))
    exact le_iSup (fun j : {x // x ∈ s} => f j.1) ⟨i, hi⟩
  haveI hfdM : FiniteDimensional F ↥M := inferInstance
  -- Step 2: `M` is Galois over `F`.
  have hgalM : IsGalois F ↥M := by
    haveI : ∀ i : {x // x ∈ s}, IsGalois F ↥(f i.1) := fun i => hgal i.1
    rw [hM]
    exact isGalois_iSup_of_charZero (fun i : {x // x ∈ s} => f i.1)
  haveI := hgalM
  haveI hnormM : Normal F ↥M := hgalM.to_normal
  -- Step 3: `Gal(M/F)` is a `p`-group.
  have hle : ∀ i : {x // x ∈ s}, f i.1 ≤ M := by
    intro i
    rw [hM]
    exact le_iSup (fun j : {x // x ∈ s} => f j.1) i
  have htop : (⨆ i : {x // x ∈ s}, IntermediateField.restrict (hle i)) = ⊤ :=
    Commons.FieldTheory.IntermediateField.restrict_iSup_eq_top
      (fun i : {x // x ∈ s} => f i.1) M hM hle
  haveI hnormR : ∀ i : {x // x ∈ s}, Normal F ↥(IntermediateField.restrict (hle i)) :=
    fun i => Normal.of_algEquiv (IntermediateField.restrictAlgEquiv (hle i))
  -- an automorphism of `M` restricting to `1` on every `f i` is trivial
  have hker : ∀ σ : ↥M ≃ₐ[F] ↥M,
      (∀ i : {x // x ∈ s},
        AlgEquiv.restrictNormalHom (E := ↥(IntermediateField.restrict (hle i))) σ = 1) →
      σ = 1 := by
    intro σ hσ
    have hmem : σ ∈ ⨅ i : {x // x ∈ s},
        (IntermediateField.restrict (hle i)).fixingSubgroup := by
      refine Subgroup.mem_iInf.mpr (fun i => ?_)
      rw [← IntermediateField.restrictNormalHom_ker (IntermediateField.restrict (hle i))]
      exact MonoidHom.mem_ker.mpr (hσ i)
    rw [← fixingSubgroup_iSup_of_fintype
        (fun i : {x // x ∈ s} => IntermediateField.restrict (hle i)),
      htop, IntermediateField.fixingSubgroup_top] at hmem
    simpa using hmem
  have hpgM : IsPGroup p (↥M ≃ₐ[F] ↥M) := by
    refine Commons.GroupTheory.PGroup.of_injective_pi
      (G := fun i : {x // x ∈ s} =>
        ↥(IntermediateField.restrict (hle i)) ≃ₐ[F] ↥(IntermediateField.restrict (hle i)))
      (MonoidHom.pi (fun i : {x // x ∈ s} =>
        AlgEquiv.restrictNormalHom (E := ↥(IntermediateField.restrict (hle i))))) ?_ ?_
    · intro σ τ h
      have h1 : σ * τ⁻¹ = 1 := by
        apply hker
        intro i
        have hi : AlgEquiv.restrictNormalHom
              (E := ↥(IntermediateField.restrict (hle i))) σ =
            AlgEquiv.restrictNormalHom
              (E := ↥(IntermediateField.restrict (hle i))) τ :=
          congrFun h i
        rw [map_mul, map_inv, hi, mul_inv_cancel]
      exact mul_inv_eq_one.mp h1
    · intro i
      exact (hpg i.1).of_equiv
        (AlgEquiv.autCongr (IntermediateField.restrictAlgEquiv (hle i)))
  -- Step 4: `Gal(L/F)` is a quotient of `Gal(M/F)`.
  set Lr : IntermediateField F ↥M := IntermediateField.restrict hLM with hLr
  haveI hnormLr : Normal F ↥Lr :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hLM)
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (E := ↥Lr) :
        (↥M ≃ₐ[F] ↥M) →* (↥Lr ≃ₐ[F] ↥Lr)) :=
    AlgEquiv.restrictNormalHom_surjective (K₁ := ↥Lr) (E := ↥M)
  have hpgLr : IsPGroup p (↥Lr ≃ₐ[F] ↥Lr) :=
    hpgM.of_surjective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (E := ↥Lr)) hsurj
  exact hpgLr.of_equiv (AlgEquiv.autCongr (IntermediateField.restrictAlgEquiv hLM)).symm

end Commons.FieldTheory.Galois
