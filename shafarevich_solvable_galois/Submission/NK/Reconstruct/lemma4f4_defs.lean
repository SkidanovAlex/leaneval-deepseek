import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.NK.Reconstruct.ambient4f3
import Submission.NK.Reconstruct.finite_coker_gammaBaseChangeHom
import Submission.NK.Reconstruct.gammaBaseChangeHom_galToGamma
import Submission.NK.Reconstruct.levelInfinity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for Shimizu's Lemma 4f.4

This file fixes the vocabulary in which `NK.Reconstruct.lemma4f4` (Shimizu, arXiv:2009.10431,
Lemma 4f.4) is proved.  All fields are intermediate fields of a separable closure `Ω` of `ℚ`.

For a finite normal level `K` of `Ω/ℚ` (`NK.Reconstruct.FrobLevel`) put

  `H_K := ker (G_K --galToGamma--> Γ_K --gammaHausMk--> Γ_K^{tf}) ≤ Gal(Ω/↥K.L)`,

the subgroup of automorphisms of `Ω` over `K.L` whose ℓ-adic abelianised class is *invisible*, and
let `invisibleSub K ℓ` be its image in `Gal(Ω/ℚ)` under the restriction of scalars.  By
construction (`levelInfinityOf_eq_fixedField`) the fixed field of `invisibleSub K ℓ` is Shimizu's
field `K^{(∞,ℓ)}` (`NK.Reconstruct.levelInfinityOf`).

The main contents are:

* `invisibleSub`, `restrictScalarsHom`, `galRestrict` — the vocabulary;
* `mem_invisibleSub_iff` — the defining membership condition;
* `levelInfinityOf_eq_fixedField` — `K^{(∞,ℓ)}` is the fixed field of `invisibleSub K ℓ`;
* `invisibleSub_le_fixingSubgroup` — the invisible subgroup fixes `K^{(∞,ℓ)}`;
* `le_levelInfinityOf` — `K.L ⊆ K^{(∞,ℓ)}`;
* `gammaHausMk_galToGamma_eq_one_of_fixes` — the descent half of the Galois correspondence for
  the closed subgroup `H_K`: an automorphism of `Ω` over `K.L` which fixes `K^{(∞,ℓ)}` pointwise is
  invisible;
* `fixingSubgroup_levelInfinityOf` — consequently the fixing subgroup of `K^{(∞,ℓ)}` in
  `Gal(Ω/ℚ)` is exactly `invisibleSub K ℓ`.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

section Basic

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]

/-- **Restriction of scalars** `Gal(Ω/K) →* Gal(Ω/ℚ)` as a monoid homomorphism. -/
noncomputable def restrictScalarsHom (K : IntermediateField ℚ Ω) :
    (Ω ≃ₐ[↥K] Ω) →* (Ω ≃ₐ[ℚ] Ω) where
  toFun σ := σ.restrictScalars ℚ
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

@[simp] theorem restrictScalarsHom_apply (K : IntermediateField ℚ Ω) (σ : Ω ≃ₐ[↥K] Ω) :
    ⇑(restrictScalarsHom K σ) = ⇑σ := rfl

/-- **Restriction of scalars** `Gal(Ω/F) →* Gal(Ω/E)` for `E ≤ F`. -/
noncomputable def galRestrict {E F : IntermediateField ℚ Ω} (hle : E ≤ F) :
    (Ω ≃ₐ[↥F] Ω) →* (Ω ≃ₐ[↥E] Ω) where
  toFun h := { h.toRingEquiv with commutes' := fun c => h.commutes' ⟨c.1, hle c.2⟩ }
  map_one' := by ext x; rfl
  map_mul' h h' := by ext x; rfl

@[simp] theorem galRestrict_apply {E F : IntermediateField ℚ Ω} (hle : E ≤ F)
    (h : Ω ≃ₐ[↥F] Ω) : ⇑(galRestrict hle h) = ⇑h := rfl

end Basic

section Invisible

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The invisible subgroup of a level, inside `Gal(Ω/ℚ)`**: the image under the restriction of
scalars of the subgroup of `Gal(Ω/↥K.L)` of the automorphisms whose ℓ-adic abelianised class is
invisible. -/
noncomputable def invisibleSub (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] : Subgroup (Ω ≃ₐ[ℚ] Ω) :=
  ((gammaHausMk (K := ↥K.L) (K' := Ω) ℓ).comp (galToGamma (K := ↥K.L) (K' := Ω) ℓ)).ker.map
    (restrictScalarsHom K.L)

theorem mem_invisibleSub_iff (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Ω ≃ₐ[ℚ] Ω) :
    σ ∈ invisibleSub K ℓ ↔ ∃ h : Ω ≃ₐ[↥K.L] Ω, restrictScalarsHom K.L h = σ ∧
      gammaHausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)
        (galToGamma (K := ↥K.L) (K' := Ω) ℓ h) = 1 := by
  simp only [invisibleSub, Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, rfl, hh⟩
  · rintro ⟨h, rfl, hh⟩
    exact ⟨h, hh, rfl⟩

/-- **`K^{(∞,ℓ)}` is the fixed field of the invisible subgroup**: the defining fixed-point
condition of `NK.Reconstruct.levelInfinityOf` is exactly that of the fixed field of
`invisibleSub K ℓ`. -/
theorem levelInfinityOf_eq_fixedField (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] :
    levelInfinityOf K ℓ = IntermediateField.fixedField (invisibleSub K ℓ) := by
  refine SetLike.ext fun x => ?_
  change x ∈ levelInfinity K.L ℓ ↔ x ∈ IntermediateField.fixedField (invisibleSub K ℓ)
  rw [mem_levelInfinity_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ hσ
    simp only [invisibleSub, Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ
    obtain ⟨g, hg, rfl⟩ := hσ
    exact h g hg
  · intro h g hg
    exact h (restrictScalarsHom K.L g) (by
      simp only [invisibleSub, Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact ⟨g, hg, rfl⟩)

/-- **The invisible subgroup fixes `K^{(∞,ℓ)}`.** -/
theorem invisibleSub_le_fixingSubgroup (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] :
    invisibleSub K ℓ ≤ (levelInfinityOf K ℓ).fixingSubgroup := by
  rw [← IntermediateField.le_iff_le]
  exact le_of_eq (levelInfinityOf_eq_fixedField K ℓ)

/-- **The level `K.L` is contained in `K^{(∞,ℓ)}`**: the invisible subgroup is a subgroup of
`Gal(Ω/↥K.L)`. -/
theorem le_levelInfinityOf (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    K.L ≤ levelInfinityOf K ℓ := by
  intro x hx
  change x ∈ levelInfinity K.L ℓ
  rw [mem_levelInfinity_iff]
  intro g _
  exact AlgEquiv.commutes g ⟨x, hx⟩

/-- **The descent half of the Galois correspondence for the invisible subgroup.**  An
automorphism `h` of `Ω` over `↥K.L` which fixes `K^{(∞,ℓ)}` pointwise lies in the kernel of
`galToGamma ≫ gammaHausMk`.  This is the fundamental theorem of infinite Galois theory applied to
the *closed* subgroup `H_K` (closed as the kernel of a continuous homomorphism into the Hausdorff
group `Γ_K^{tf}`). -/
theorem gammaHausMk_galToGamma_eq_one_of_fixes (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (h : Ω ≃ₐ[↥K.L] Ω)
    (hf : ∀ x ∈ levelInfinityOf K ℓ, h x = x) :
    gammaHausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)
      (galToGamma (K := ↥K.L) (K' := Ω) ℓ h) = 1 := by
  let Φ : (Ω ≃ₐ[↥K.L] Ω) →* GammaHaus ↥K.L Ω ℓ :=
    (gammaHausMk (K := ↥K.L) (K' := Ω) ℓ).comp (galToGamma (K := ↥K.L) (K' := Ω) ℓ)
  have hclosed : IsClosed (Φ.ker : Set (Ω ≃ₐ[↥K.L] Ω)) :=
    isClosed_singleton.preimage
      ((continuous_gammaHausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)).comp
        (galToGamma_continuous (K := ↥K.L) (K' := Ω) ℓ))
  have hset : (IntermediateField.fixedField Φ.ker : Set Ω) = (levelInfinityOf K ℓ : Set Ω) := by
    rw [levelInfinityOf_eq_fixedField]
    ext x
    simp only [SetLike.mem_coe, IntermediateField.mem_fixedField_iff, invisibleSub,
      Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hx σ hσ
      obtain ⟨g, hg, rfl⟩ := hσ
      exact hx g hg
    · intro hx g hg
      exact hx (restrictScalarsHom K.L g) ⟨g, hg, rfl⟩
  have hmem : h ∈ (IntermediateField.fixedField Φ.ker).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ∈ (levelInfinityOf K ℓ : Set Ω) := by rw [← hset]; exact hx
    exact hf x hx'
  rw [InfiniteGalois.fixingSubgroup_fixedField ⟨Φ.ker, hclosed⟩] at hmem
  exact MonoidHom.mem_ker.mp hmem

/-- **The fixing subgroup of `K^{(∞,ℓ)}` in `Gal(Ω/ℚ)` is the invisible subgroup.** -/
theorem fixingSubgroup_levelInfinityOf (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] :
    (levelInfinityOf K ℓ).fixingSubgroup = invisibleSub K ℓ := by
  refine le_antisymm ?_ (invisibleSub_le_fixingSubgroup K ℓ)
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [mem_invisibleSub_iff]
  have hσC : ∀ x ∈ K.L, σ x = x := fun x hx => hσ x (le_levelInfinityOf K ℓ hx)
  refine ⟨{ σ.toRingEquiv with commutes' := fun c => hσC c.1 c.2 }, ?_, ?_⟩
  · exact AlgEquiv.ext (fun _ => rfl)
  · exact gammaHausMk_galToGamma_eq_one_of_fixes K ℓ _ (fun x hx => hσ x hx)

end Invisible


section Helpers

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Every intermediate field of a separable closure of `ℚ` is again a separable closure of its
own prime field**: `Ω` is separably closed and separable over `ℚ`, hence over any intermediate
field. -/
theorem isSepClosure_of_le (E : IntermediateField ℚ Ω) : IsSepClosure ↥E Ω :=
  ⟨IsSepClosure.sep_closed ℚ, inferInstance⟩

/-- **Naturality of `galToGamma` with respect to the base-change map**: for levels `K ⊆ N` and
`h : Gal(Ω/↥N.L)`, the base change `π_{N/K}` of the class of `h` is the class of the restriction of
`h` to `↥K.L`.  This is `NK.Reconstruct.gammaBaseChangeHom_galToGamma` rewritten in the
vocabulary `ambientPi`/`galRestrict`. -/
theorem ambientPi_galToGamma (K : NumFieldIn ℚ Ω) (N : FrobLevel ℚ Ω) [IsSepClosure ↥(K.L) Ω]
    (hKN : K.L ≤ N.L) (ℓ : ℕ) [Fact ℓ.Prime] (h : Ω ≃ₐ[↥(N.L)] Ω) :
    ambientPi K N hKN ℓ (galToGamma (K := ↥(N.L)) (K' := Ω) ℓ h)
      = galToGamma (K := ↥(K.L)) (K' := Ω) ℓ (galRestrict hKN h) := by
  haveI : IsSepClosure ↥(N.L) Ω := isSepClosure_of_le N.L
  show gammaBaseChangeHom (K := ↥(K.L)) (K' := Ω) ℓ (levelExtendGen K N hKN)
        (galToGamma (K := ↥(levelExtendGen K N hKN).L) (K' := Ω) ℓ h)
      = galToGamma (K := ↥(K.L)) (K' := Ω) ℓ (galRestrict hKN h)
  rw [gammaBaseChangeHom_galToGamma (K := ↥(K.L)) (K' := Ω) ℓ (levelExtendGen K N hKN) h]
  congr 1

/-- **Functoriality of the base-change maps in the level**: for `K ⊆ N ⊆ L` one has
`π_{N/K} ∘ π_{L/N} = π_{L/K}`. -/
theorem ambientPi_trans (K N L : FrobLevel ℚ Ω) [IsSepClosure ↥(K.L) Ω] [IsSepClosure ↥(N.L) Ω]
    (hKN : K.L ≤ N.L) (hNL : N.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] (γ : Gamma ↥(L.L) Ω ℓ) :
    ambientPi (NumFieldIn.ofFrobLevel K) N hKN ℓ (ambientPi (NumFieldIn.ofFrobLevel N) L hNL ℓ γ)
      = ambientPi (NumFieldIn.ofFrobLevel K) L (hKN.trans hNL) ℓ γ := by
  haveI : IsSepClosure ↥(L.L) Ω := isSepClosure_of_le L.L
  haveI hN' : IsSepClosure ↥(NumFieldIn.ofFrobLevel N).L Ω := ‹IsSepClosure ↥N.L Ω›
  haveI hK' : IsSepClosure ↥(NumFieldIn.ofFrobLevel K).L Ω := ‹IsSepClosure ↥K.L Ω›
  obtain ⟨τ, rfl⟩ := galToGamma_surjective (K := ↥(L.L)) (K' := Ω) ℓ γ
  rw [ambientPi_galToGamma (NumFieldIn.ofFrobLevel N) L hNL ℓ τ]
  rw [ambientPi_galToGamma (NumFieldIn.ofFrobLevel K) N hKN ℓ (galRestrict hNL τ)]
  rw [ambientPi_galToGamma (NumFieldIn.ofFrobLevel K) L (hKN.trans hNL) ℓ τ]
  congr 1

/-- **The range of the restriction of scalars is the fixing subgroup.** -/
theorem range_restrictScalarsHom (K : IntermediateField ℚ Ω) :
    (restrictScalarsHom K).range = K.fixingSubgroup := by
  refine le_antisymm ?_ ?_
  · rintro σ ⟨h, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact h.commutes' ⟨x, hx⟩
  · intro σ hσ
    refine ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩, ?_⟩
    ext x
    rfl

end Helpers

end NK.Reconstruct
