import Submission.NK.Reconstruct.gammaSmul
import Submission.NK.Reconstruct.gammaBaseChangeLinear
import Submission.NK.Reconstruct.lemma4f4_defs
import Submission.NK.Reconstruct.finite_coker_gammaBaseChangeHom
import Submission.NK.Reconstruct.rankLemmas
import Submission.NK.Reconstruct.moduleFinite_gamma
import Submission.NK.Reconstruct.NumFieldIn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base change on the Hausdorff torsion-free quotient `Γ_K^{tf}`

For finite Galois levels `K ⊆ L` of a separable closure `Ω` of `ℚ`, Shimizu's base change
`π_{L/K} : Γ_L → Γ_K` (`NK.Reconstruct.gammaBaseChangeHom`, `ℤ_ℓ`-linear by
`NK.Reconstruct.gammaBaseChangeLinear`) descends along the Hausdorff torsion-free quotients
`Γ ↠ Γ^{tf}` (`NK.Reconstruct.hausMk`), because it maps the invisible subgroup of `Γ_L` into the
invisible subgroup of `Γ_K` (`NK.Reconstruct.invisibleSubmodule_le_comap`, immediate from
`NK.Reconstruct.gammaHausLift_comp`).

The descended map `NK.Reconstruct.hausPi` is the object of the rank computation of Shimizu's
Proposition 4f.5:

* `NK.Reconstruct.hausPi_hausMk_galToGamma_eq_zero_iff` — **the kernel of `hausPi` consists of the
  automorphisms fixing `K^{(∞,ℓ)}`**, the field-theoretic description of
  `ker π^{tf}_{L/K} = Gal(L^{(∞)}/K^{(∞)}L)`;
* `NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq` — consequently, if
  `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}` then `ker π^{tf}_{L/K₁} = ker π^{tf}_{L/K₂}` (this is the step in
  Shimizu's proof of Proposition 4f.5 that identifies the two kernels `N`);
* `NK.Reconstruct.finite_coker_hausPi`, `NK.Reconstruct.rank_hausQuot_eq_rank_range_hausPi` —
  the cokernel is finite, so the rank of `Γ_K^{tf}` equals the rank of the image, which is the rank
  of `Γ_L^{tf}/ker π^{tf}_{L/K}`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The base change `π_{L/K}`, as a `ℤ_ℓ`-linear map** (`NK.Reconstruct.gammaBaseChangeLinear`,
made a definition). -/
noncomputable def baseChangeLinear (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    Additive (Gamma ↥L.L Ω ℓ) →ₗ[PadicInt ℓ] Additive (Gamma ↥K.L Ω ℓ) :=
  (gammaBaseChangeLinear (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h)).choose

theorem baseChangeLinear_apply (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime]
    (f : Additive (Gamma ↥L.L Ω ℓ)) :
    baseChangeLinear K L h ℓ f = MonoidHom.toAdditive (ambientPi K L h ℓ) f :=
  (gammaBaseChangeLinear (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h)).choose_spec f

/-! ## The descent to `Γ^{tf}` -/

/-- **The base change maps the invisible subgroup into the invisible subgroup.**  This is the
compatibility `gammaHausLift_comp` of the descent with the projection `Γ ↠ Γ^{tf}`. -/
theorem invisibleSubmodule_le_comap (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    invisibleSubmodule (K := ↥L.L) (K' := Ω) (ℓ := ℓ)
      ≤ Submodule.comap (baseChangeLinear K L h ℓ)
          (invisibleSubmodule (K := ↥K.L) (K' := Ω) (ℓ := ℓ)) := by
  intro x hx
  rw [Submodule.mem_comap, mem_invisibleSubmodule_iff_gammaHausMk, baseChangeLinear_apply]
  have hx' : gammaHausMk (K := ↥L.L) (K' := Ω) ℓ (Additive.toMul x) = 1 :=
    (mem_invisibleSubmodule_iff_gammaHausMk (K := ↥L.L) (K' := Ω) x).mp hx
  have hcomp := gammaHausLift_comp (K₁ := ↥L.L) (K₁' := Ω) (K₂ := ↥K.L) (K₂' := Ω) ℓ
    (ambientPi K L h ℓ)
    (gammaBaseChange_continuous (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h))
    (Additive.toMul x)
  rw [hx', map_one] at hcomp
  exact hcomp.symm

/-- **The descended base change `π^{tf}_{L/K} : Γ_L^{tf} → Γ_K^{tf}`** on the Hausdorff
torsion-free quotients, as a `ℤ_ℓ`-linear map. -/
noncomputable def hausPi (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    HausQuot ↥L.L Ω ℓ →ₗ[PadicInt ℓ] HausQuot ↥K.L Ω ℓ :=
  Submodule.mapQ (invisibleSubmodule (K := ↥L.L) (K' := Ω) (ℓ := ℓ))
    (invisibleSubmodule (K := ↥K.L) (K' := Ω) (ℓ := ℓ))
    (baseChangeLinear K L h ℓ) (invisibleSubmodule_le_comap K L h ℓ)

/-- The defining property of the descended map: it commutes with the quotient maps. -/
theorem hausPi_hausMk (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] (x : Additive (Gamma ↥L.L Ω ℓ)) :
    hausPi K L h ℓ (hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) x) = hausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ) (baseChangeLinear K L h ℓ x) := by
  rw [hausPi, hausMk_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, hausMk_apply,
    Submodule.mkQ_apply]

/-! ## The kernel of `π^{tf}_{L/K}` -/

/-- **Shimizu's description of the kernel**: under the identification of `Γ_L^{tf}` with the classes
of automorphisms of `Ω` over `L`, the kernel of `π^{tf}_{L/K}` consists exactly of the
automorphisms fixing `K^{(∞,ℓ)}` pointwise.

Both directions use the definition of `K^{(∞,ℓ)}` as the fixed field of the kernel of
`G_K → Γ_K^{tf}`: an automorphism is invisible (`gammaHausMk (galToGamma ·) = 1`) exactly when it
fixes `K^{(∞,ℓ)}` (`NK.Reconstruct.mem_levelInfinity_iff` for one direction,
`NK.Reconstruct.gammaHausMk_galToGamma_eq_one_of_fixes` for the other). -/
theorem hausPi_hausMk_galToGamma_eq_zero_iff (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] (σ : Ω ≃ₐ[↥L.L] Ω) :
    hausPi K L h ℓ (hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))) = 0
      ↔ ∀ x ∈ levelInfinityOf K ℓ, σ x = x := by
  rw [hausPi_hausMk, baseChangeLinear_apply, hausMk_eq_zero_iff,
    mem_invisibleSubmodule_iff_gammaHausMk]
  rw [show Additive.toMul (MonoidHom.toAdditive (ambientPi K L h ℓ)
      (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)))
      = ambientPi K L h ℓ (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ) from rfl]
  rw [ambientPi_galToGamma K L h ℓ σ]
  constructor
  · intro hgm x hx
    have h1 : galRestrict h σ x = x :=
      (mem_levelInfinity_iff (K := K.L) ℓ x).mp hx (galRestrict h σ) hgm
    rwa [galRestrict_apply] at h1
  · intro hfix
    exact gammaHausMk_galToGamma_eq_one_of_fixes K ℓ (galRestrict h σ) (fun x hx => by
      rw [galRestrict_apply]; exact hfix x hx)

/-- The composite `Gal(Ω/↥L) → Γ_L^{tf}` (i.e. `gammaHausMk ∘ galToGamma`) is surjective. -/
theorem hausMk_galToGamma_surjective (L : FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Surjective fun σ : Ω ≃ₐ[↥L.L] Ω =>
      hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ)
        (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)) := by
  intro x
  obtain ⟨y, rfl⟩ := hausMk_surjective (K := ↥L.L) (K' := Ω) (ℓ := ℓ) x
  obtain ⟨σ, hσ⟩ := galToGamma_surjective (K := ↥L.L) (K' := Ω) ℓ (Additive.toMul y)
  refine ⟨σ, ?_⟩
  show hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)) = hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) y
  rw [hσ, ofMul_toMul]

/-- **The kernels of `π^{tf}_{L/K₁}` and `π^{tf}_{L/K₂}` agree when the corresponding
`(∞,ℓ)`-fields agree.**

This is the step of Shimizu's proof of Proposition 4f.5 that computes `N = ker(π_{L/K₁}) =
ker(π_{L/K₂})` from `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}`: an automorphism `σ` of `Ω` over `L` fixes
`K₁^{(∞,ℓ)}` iff it fixes `K₁^{(∞,ℓ)}L` (it fixes `L`), i.e. `LK₂^{(∞,ℓ)}`, iff it fixes
`K₂^{(∞,ℓ)}`. -/
theorem ker_hausPi_eq_of_levelInfinity_eq (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime]
    (hsup : (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
      = L.L ⊔ levelInfinityOf K₂ ℓ) :
    LinearMap.ker (hausPi K₁ L h₁ ℓ) = LinearMap.ker (hausPi K₂ L h₂ ℓ) := by
  -- an automorphism of `Ω` over `L` which fixes `L.L` pointwise
  have hfixL : ∀ σ : Ω ≃ₐ[↥L.L] Ω,
      restrictScalarsHom L.L σ ∈ (L.L).fixingSubgroup := by
    intro σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rw [restrictScalarsHom_apply]
    exact σ.commutes' ⟨y, hy⟩
  -- the key pointwise equivalence of the kernels
  have key : ∀ σ : Ω ≃ₐ[↥L.L] Ω,
      hausPi K₁ L h₁ ℓ (hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))) = 0
        ↔ hausPi K₂ L h₂ ℓ
            (hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))) = 0 := by
    intro σ
    rw [hausPi_hausMk_galToGamma_eq_zero_iff, hausPi_hausMk_galToGamma_eq_zero_iff]
    constructor
    · intro hx z hz
      have hmem₁ : restrictScalarsHom L.L σ ∈ (levelInfinityOf K₁ ℓ).fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        rw [restrictScalarsHom_apply]
        exact hx y hy
      have hmem : restrictScalarsHom L.L σ
          ∈ (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]
        exact ⟨hmem₁, hfixL σ⟩
      have hmem' : restrictScalarsHom L.L σ
          ∈ (L.L ⊔ levelInfinityOf K₂ ℓ : IntermediateField ℚ Ω).fixingSubgroup := by
        rw [← hsup]; exact hmem
      rw [IntermediateField.mem_fixingSubgroup_iff] at hmem'
      exact hmem' z ((le_sup_right : levelInfinityOf K₂ ℓ
        ≤ (L.L ⊔ levelInfinityOf K₂ ℓ : IntermediateField ℚ Ω)) hz)
    · intro hx z hz
      have hmem₂ : restrictScalarsHom L.L σ ∈ (levelInfinityOf K₂ ℓ).fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        rw [restrictScalarsHom_apply]
        exact hx y hy
      have hmem : restrictScalarsHom L.L σ
          ∈ (L.L ⊔ levelInfinityOf K₂ ℓ : IntermediateField ℚ Ω).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]
        exact ⟨hfixL σ, hmem₂⟩
      have hmem' : restrictScalarsHom L.L σ
          ∈ (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω).fixingSubgroup := by
        rw [hsup]; exact hmem
      rw [IntermediateField.mem_fixingSubgroup_iff] at hmem'
      exact hmem' z ((le_sup_left : levelInfinityOf K₁ ℓ
        ≤ (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)) hz)
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨σ, rfl⟩ := hausMk_galToGamma_surjective L ℓ x
    rw [LinearMap.mem_ker] at hx ⊢
    exact (key σ).mp hx
  · obtain ⟨σ, rfl⟩ := hausMk_galToGamma_surjective L ℓ x
    rw [LinearMap.mem_ker] at hx ⊢
    exact (key σ).mpr hx

/-- **The kernel of the projection `Γ_K → Γ_{L,ℓ}` is the range of the base change**, in the
`ℤ_ℓ`-linear form needed for the rank computation.  This is
`NK.Reconstruct.ker_proj_eq_range_gammaBaseChangeHom` read through the additive structures. -/
theorem ker_projAdd_eq_range_baseChangeLinear (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    LinearMap.ker (projAdd (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h))
      = LinearMap.range (baseChangeLinear K L h ℓ) := by
  have hgrp : (Gamma.proj (K := ↥K.L) (K' := Ω) (ℓ := ℓ) (levelExtendGen K L h)).ker =
      (ambientPi K L h ℓ).range :=
    ker_proj_eq_range_gammaBaseChangeHom (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h)
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [LinearMap.mem_range]
    have hx1 : Gamma.proj (K := ↥K.L) (K' := Ω) (ℓ := ℓ) (levelExtendGen K L h)
        (Additive.toMul x) = 1 := by
      have h0 : projAdd (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h) x = 0 :=
        LinearMap.mem_ker.mp hx
      rw [projAdd_apply] at h0
      have h1 := congrArg Additive.toMul h0
      rw [toMul_ofMul, toMul_zero] at h1
      exact h1
    have hx2 : Additive.toMul x
        ∈ (Gamma.proj (K := ↥K.L) (K' := Ω) (ℓ := ℓ) (levelExtendGen K L h)).ker :=
      MonoidHom.mem_ker.mpr hx1
    rw [hgrp] at hx2
    obtain ⟨g, hg⟩ := hx2
    exact ⟨Additive.ofMul g, by
      rw [baseChangeLinear_apply]
      show Additive.ofMul (ambientPi K L h ℓ g) = x
      rw [hg, ofMul_toMul]⟩
  · rw [LinearMap.mem_ker, projAdd_apply]
    obtain ⟨y, hy⟩ := hx
    have hy' : Additive.toMul x = ambientPi K L h ℓ (Additive.toMul y) := by
      rw [← hy, baseChangeLinear_apply]
      rfl
    have hmem : Additive.toMul x
        ∈ (Gamma.proj (K := ↥K.L) (K' := Ω) (ℓ := ℓ) (levelExtendGen K L h)).ker := by
      rw [hgrp]
      exact ⟨Additive.toMul y, hy'.symm⟩
    rw [MonoidHom.mem_ker] at hmem
    rw [hmem]
    exact ofMul_one

end NK.Reconstruct
