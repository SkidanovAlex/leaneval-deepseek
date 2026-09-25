import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.Reconstruct.hausPi
import Submission.NK.ShimizuRank.hausQuot_torsionFree
import Submission.NK.NUV2.Transfer.levelInfinity_mono
import Submission.NK.RankTheoryDeep.hausPi_tauStar_invariant
import Submission.NK.NUV2.Transfer.kerTorsion_of_key

/-!
# `K₁^{(∞,2)} ⊔ L = M^{(∞,2)} ⊔ L` for `M = K₁ ⊓ K₂` (Shimizu, Prop. 4f.5, kernel form)

This file proves the field-theoretic form of the rank step of Shimizu's Proposition 4f.5
(arXiv:2009.10431, §4) at `ℓ = 2`: in Shimizu's situation (`M.L = K₁.L ⊓ K₂.L`, `L` a finite Galois
level containing `K₁.L` and `K₂.L`, and `K₁^{(∞,2)}L = L K₂^{(∞,2)}`),

  `K₁^{(∞,2)} ⊔ L.L = M^{(∞,2)} ⊔ L.L`.

The proof is the *kernel* form of the rank step, as in `Submission/Work/NUV2/RouteB/resKernel_two`:
by the sharp criterion `hausPi_eq_zero_iff_fixes_sup`, an element of `HausQuot L`
lies in the kernel of `hausPi K L h 2` exactly when its representatives fix `K^{(∞,2)} ⊔ L.L`, so
the field statement is *equivalent* to

  `ker (hausPi K₁ L h₁ 2) = ker (hausPi M L hM 2)`,

and this is what is proved here: the inclusion `⊆` is the base-change calculus
(`K^{(∞,2)}` is monotone in the base field), and the reverse inclusion is Shimizu's arithmetic
statement that the kernel of `π_{L/M}` is killed by a power of `2` modulo `ker π_{L/K₁}`
(the transfer/norm identity of the rank step, `NK.NUV2.Transfer.kerTorsion`).  Torsion-freeness
of `HausQuot L` modulo the smaller kernel then upgrades the torsion statement to an inclusion.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace NK.NUV2

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]


/-- **The sharp criterion**: for an automorphism `σ` of `Ω` over `L.L`, the class
`hausMk (galToGamma σ)` is killed by `hausPi K L h ℓ` exactly when `σ` fixes `K^{(∞,ℓ)} ⊔ L.L`
pointwise.  (This is Shimizu's description of the kernel of the base change, cf.
`NK.Reconstruct.hausPi_hausMk_galToGamma_eq_zero_iff`.) -/
theorem hausPi_eq_zero_iff_fixes_sup (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    [IsSepClosure ↥L.L Ω] (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] (σ : Ω ≃ₐ[↥L.L] Ω) :
    hausPi K L h ℓ (hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))) = 0 ↔
      ∀ x ∈ (levelInfinityOf K ℓ ⊔ L.L : IntermediateField ℚ Ω), σ x = x := by
  rw [hausPi_hausMk_galToGamma_eq_zero_iff K L h ℓ σ]
  constructor
  · intro hfix x hx
    have hσL : restrictScalarsHom L.L σ ∈ (L.L : IntermediateField ℚ Ω).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      rw [restrictScalarsHom_apply]
      simpa using σ.commutes' (⟨y, hy⟩ : ↥L.L)
    have hσK : restrictScalarsHom L.L σ ∈ (levelInfinityOf K ℓ : IntermediateField ℚ Ω).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      rw [restrictScalarsHom_apply]
      exact hfix y hy
    have hσsup : restrictScalarsHom L.L σ
        ∈ ((levelInfinityOf K ℓ ⊔ L.L : IntermediateField ℚ Ω)).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hσK, hσL⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσsup x hx
  · intro hfix x hx
    exact hfix x ((le_sup_left : (levelInfinityOf K ℓ : IntermediateField ℚ Ω) ≤ _) hx)

/-! ## The two inputs

`NK.NUV2.Transfer.levelInfinity_mono` (monotonicity of `K^{(∞,ℓ)}` in the base field) and
`NK.NUV2.Transfer.kerTorsion` (Shimizu's rank step) are proved in sibling modules.
-/

/-- Shimizu's rank step in kernel form.

**This is the single remaining input.**  It is *equivalent* to Shimizu's rank step of Proposition
4f.5 (the named residual `NK.ShimizuRank.ResKernelRankInput Ω 2`), and its proof is the
transfer/duality argument of Shimizu's Lemma 4f.1: the `G(L/M)`-action `τ^*` on `HausQuot L`, the
norm identity `Ver ∘ π_{L/M} = Σ_{g ∈ Gal(L/M)} τ^*_g`, and the containment
`I_{G(L/K)} · HausQuot L ≤ ker (hausPi K L h 2)` (the latter from
`NK.RankTheoryDeep.hausPi_tauStar_invariant`).  It is delegated as
`NK.NUV2.Transfer.kerTorsion` (sibling module); the statement below is that statement. -/
theorem kerTorsion_aux (K₁ K₂ M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω]
    (hM : M.L = K₁.L ⊓ K₂.L) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (hM' : M.L ≤ L.L)
    (hsup : (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
      = L.L ⊔ levelInfinityOf K₂ 2) :
    ∀ x ∈ LinearMap.ker (hausPi M L hM' 2),
      ∃ n : ℕ, (2 : ℤ_[2]) ^ n • x ∈ LinearMap.ker (hausPi K₁ L h₁ 2) := by
  letI : Algebra ↥M.L ↥L.L := algOfLeNumFieldIn M (NumFieldIn.ofFrobLevel L) hM'
  haveI : IsScalarTower ↥M.L ↥L.L Ω := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show (algebraMap ↥M.L Ω x : Ω) = (algebraMap ↥L.L Ω (⟨(x : Ω), hM' x.2⟩ : ↥L.L) : Ω)
    rfl
  letI : Algebra ↥K₁.L ↥L.L := algOfLeNumFieldIn K₁ (NumFieldIn.ofFrobLevel L) h₁
  haveI : IsScalarTower ↥K₁.L ↥L.L Ω := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show (algebraMap ↥K₁.L Ω x : Ω) = (algebraMap ↥L.L Ω (⟨(x : Ω), h₁ x.2⟩ : ↥L.L) : Ω)
    rfl
  letI : Algebra ↥K₂.L ↥L.L := algOfLeNumFieldIn K₂ (NumFieldIn.ofFrobLevel L) h₂
  haveI : IsScalarTower ↥K₂.L ↥L.L Ω := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show (algebraMap ↥K₂.L Ω x : Ω) = (algebraMap ↥L.L Ω (⟨(x : Ω), h₂ x.2⟩ : ↥L.L) : Ω)
    rfl
  obtain ⟨ρ, hρ⟩ := NK.NUV2.Transfer.exists_tauStarAction Ω L 2
  exact NK.NUV2.kerTorsion_of_key K₁ K₂ M L hM h₁ h₂ hM' hsup ρ hρ

/-! ## The kernel equality -/

/-- **The kernel equality**: in Shimizu's situation the two kernels of the base changes
`π_{L/K₁}` and `π_{L/M}` agree (as submodules of `HausQuot L`). -/
theorem ker_hausPi_eq (K₁ K₂ M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω]
    (hM : M.L = K₁.L ⊓ K₂.L) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (hM' : M.L ≤ L.L)
    (hsup : (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
      = L.L ⊔ levelInfinityOf K₂ 2) :
    LinearMap.ker (hausPi K₁ L h₁ 2) = LinearMap.ker (hausPi M L hM' 2) := by
  have hMK : M.L ≤ K₁.L := by rw [hM]; exact inf_le_left
  refine le_antisymm ?_ ?_
  · -- the base-change calculus: `N_{K₁} ⊆ N_M`
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    obtain ⟨σ, hσ⟩ := hausMk_galToGamma_surjective L 2 x
    rw [← hσ] at hx ⊢
    rw [hausPi_eq_zero_iff_fixes_sup K₁ L h₁ 2 σ] at hx
    rw [hausPi_eq_zero_iff_fixes_sup M L hM' 2 σ]
    intro y hy
    exact hx y (sup_le_sup_right (NK.NUV2.Transfer.levelInfinity_mono M K₁ hMK 2) (L.L) hy)
  · -- Shimizu's rank step: `N_M ⊆ N_{K₁}` from `N_M / N_{K₁}` torsion
    haveI := NK.ShimizuRank.hausQuot_torsionFree (K := ↥K₁.L) (K' := Ω) (ℓ := 2)
    intro x hx
    obtain ⟨n, hn⟩ := kerTorsion_aux K₁ K₂ M L hM h₁ h₂ hM' hsup x hx
    rw [LinearMap.mem_ker] at hn ⊢
    have h2 : ((2 : ℤ_[2]) ^ n) • (hausPi K₁ L h₁ 2 x) = 0 := by
      rw [← LinearMap.map_smul, hn]
    have hne : (2 : ℤ_[2]) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    exact (smul_right_injective (HausQuot ↥K₁.L Ω 2) hne) (by simp [h2])

/-! ## The field statement -/

/-- **Shimizu's Proposition 4f.5, field form at `ℓ = 2`.** -/
theorem levelInfinity_sup_eq (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (K₁ K₂ M : NK.Reconstruct.NumFieldIn ℚ Ω)
    (L : NK.Reconstruct.FrobLevel ℚ Ω) [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω]
    [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hM : M.L = K₁.L ⊓ K₂.L) (h₁ : K₁.L ≤ L.L)
    (h₂ : K₂.L ≤ L.L) (hM' : M.L ≤ L.L)
    (hsup : (NK.Reconstruct.levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
      = L.L ⊔ NK.Reconstruct.levelInfinityOf K₂ 2) :
    (NK.Reconstruct.levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
      = NK.Reconstruct.levelInfinityOf M 2 ⊔ L.L := by
  have hker : LinearMap.ker (hausPi K₁ L h₁ 2) = LinearMap.ker (hausPi M L hM' 2) :=
    ker_hausPi_eq K₁ K₂ M L hM h₁ h₂ hM' hsup
  -- the fixing subgroups agree, hence the fields agree
  have key : ∀ σ : Ω ≃ₐ[ℚ] Ω, σ ∈ (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup ↔
      σ ∈ (levelInfinityOf M 2 ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup := by
    intro σ
    constructor
    · intro hσ
      have hσL : ∀ y ∈ (L.L : IntermediateField ℚ Ω), σ y = y := fun y hy =>
        (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ y
          ((le_sup_right : (L.L : IntermediateField ℚ Ω) ≤ _) hy)
      set τ : Ω ≃ₐ[↥L.L] Ω :=
        (IntermediateField.fixingSubgroupEquiv L.L) ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr hσL⟩
        with hτ
      have hτcoe : ⇑τ = ⇑σ := rfl
      have hτK : ∀ y ∈ (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω), τ y = y := by
        intro y hy
        rw [hτcoe]
        exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ y hy
      have h0 : (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) 2 τ))) ∈ LinearMap.ker (hausPi K₁ L h₁ 2) :=
        (hausPi_eq_zero_iff_fixes_sup K₁ L h₁ 2 τ).mpr hτK
      have h1 : (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) 2 τ))) ∈ LinearMap.ker (hausPi M L hM' 2) := by
        rw [← hker]; exact h0
      have hτM : ∀ y ∈ (levelInfinityOf M 2 ⊔ L.L : IntermediateField ℚ Ω), τ y = y :=
        (hausPi_eq_zero_iff_fixes_sup M L hM' 2 τ).mp h1
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      rw [← hτcoe]
      exact hτM y hy
    · intro hσ
      have hσL : ∀ y ∈ (L.L : IntermediateField ℚ Ω), σ y = y := fun y hy =>
        (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ y
          ((le_sup_right : (L.L : IntermediateField ℚ Ω) ≤ _) hy)
      set τ : Ω ≃ₐ[↥L.L] Ω :=
        (IntermediateField.fixingSubgroupEquiv L.L) ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr hσL⟩
        with hτ
      have hτcoe : ⇑τ = ⇑σ := rfl
      have hτM : ∀ y ∈ (levelInfinityOf M 2 ⊔ L.L : IntermediateField ℚ Ω), τ y = y := by
        intro y hy
        rw [hτcoe]
        exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ y hy
      have h0 : (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) 2 τ))) ∈ LinearMap.ker (hausPi M L hM' 2) :=
        (hausPi_eq_zero_iff_fixes_sup M L hM' 2 τ).mpr hτM
      have h1 : (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) 2 τ))) ∈ LinearMap.ker (hausPi K₁ L h₁ 2) := by
        rw [hker]; exact h0
      have hτK : ∀ y ∈ (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω), τ y = y :=
        (hausPi_eq_zero_iff_fixes_sup K₁ L h₁ 2 τ).mp h1
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      rw [← hτcoe]
      exact hτK y hy
  have hfix : (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup
      = (levelInfinityOf M 2 ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup :=
    Subgroup.ext fun σ => key σ
  calc (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
      = IntermediateField.fixedField
          ((levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup) :=
        (InfiniteGalois.fixedField_fixingSubgroup _).symm
    _ = IntermediateField.fixedField
          ((levelInfinityOf M 2 ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup) := by rw [hfix]
    _ = (levelInfinityOf M 2 ⊔ L.L : IntermediateField ℚ Ω) :=
        InfiniteGalois.fixedField_fixingSubgroup _

end NK.NUV2
