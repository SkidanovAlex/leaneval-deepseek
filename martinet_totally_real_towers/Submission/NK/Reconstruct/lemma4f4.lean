import Mathlib
import Submission.NK.Reconstruct.levelInfinity
import Submission.NK.Reconstruct.ambient4f3
import Submission.NK.Reconstruct.gammaHaus
import Submission.NK.Reconstruct.gammaBaseChangeHom_galToGamma
import Submission.NK.Reconstruct.lemma4f4_defs
import Submission.NK.Reconstruct.gammaHausMk_sbar_eq_one_iff
import Submission.NK.Reconstruct.ambientPi_hausMk_heq_of_le

/-!
# Shimizu's Lemma 4f.4

Shimizu (arXiv:2009.10431, §4, Lemma 4f.4), in the ambient setting of
`Submission/Work/Reconstruct/ambient4f3.lean`: if `K₁, K₂` are finite normal levels of a separable
closure `Ω` of `ℚ`, `L ⊇ K₁.L ⊔ K₂.L` is a further level and `σbar : Γ_{K₁} ≃* Γ_{K₂}` is a
*continuous* isomorphism of Shimizu's ℓ-adic abelianisations which matches the base-change maps
modulo the invisible subgroup,

  `gammaHausMk (σbar (π_{L/K₁} γ)) = gammaHausMk (π_{L/K₂} γ)`  for all `γ ∈ Γ_L`,

then

  `K₁^{(∞,ℓ)} · K₂.L = K₁.L · K₂^{(∞,ℓ)}`.

The proof given here is the one adapted to the Hausdorff quotient `Γ^{tf}` (the form in which the
hypothesis is produced by `NK.Reconstruct.prop4f3`):

* by `NK.Reconstruct.ambientPi_hausMk_heq_of_le` the hypothesis descends from the level `L` to the
  level `N = K₁ ⊔ K₂` (`K₁.L ⊔ K₂.L`), the base change having finite cokernel while `Γ^{tf}` is
  torsion-free;
* by `NK.Reconstruct.gammaHausMk_sbar_eq_one_iff` a continuous isomorphism `σbar` transports the
  *invisible* subgroup (the kernel of `Γ_K ↠ Γ_K^{tf}`);
* consequently, for every automorphism `σ` of `Ω` over `K₁.L ⊔ K₂.L`, the class of its restriction
  to `K₁.L` is invisible if and only if the class of its restriction to `K₂.L` is
  (`hausMk_galToGamma_iff`);
* the Galois correspondence (`NK.Reconstruct.fixingSubgroup_levelInfinityOf`) turns this
  equivalence of invisibility conditions into the desired equality of fixing subgroups, whence the
  equality of the fixed fields.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

namespace NK.Reconstruct

open scoped Pointwise

/-- **The pointwise form of Shimizu's hypothesis at the level `N`** (`K₁.L ⊔ K₂.L ≤ N.L ≤ L.L`):
for an automorphism `h` of `Ω` over `↥N.L`, the two reduced classes `σbar (π_{N/K₁}(galToGamma h))`
and `π_{N/K₂}(galToGamma h)` have the same image in `Γ_{K₂}^{tf}`, hence the invisibility of
`galToGamma (h|K₁.L)` and of `galToGamma (h|K₂.L)` are equivalent. -/
theorem hausMk_galToGamma_iff {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ L N : FrobLevel ℚ Ω) [IsSepClosure ↥(K₁.L) Ω] [IsSepClosure ↥(K₂.L) Ω]
    [IsSepClosure ↥(N.L) Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (hN₁ : K₁.L ≤ N.L) (hN₂ : K₂.L ≤ N.L) (hNL : N.L ≤ L.L)
    (ℓ : ℕ) [Fact ℓ.Prime] (σbar : Gamma ↥(K₁.L) Ω ℓ ≃* Gamma ↥(K₂.L) Ω ℓ)
    (hσbar : Continuous ⇑σbar)
    (heq : ∀ (γ : Gamma ↥(L.L) Ω ℓ),
      gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ γ))
        = gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi (NumFieldIn.ofFrobLevel K₂) L h₂ ℓ γ))
    (h : Ω ≃ₐ[↥(N.L)] Ω) :
    gammaHausMk (K := ↥(K₁.L)) (K' := Ω) (ℓ := ℓ)
        (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
          (galRestrict (E := K₁.L) (F := N.L) hN₁ h)) = 1
      ↔ gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
        (galToGamma (K := ↥(K₂.L)) (K' := Ω) ℓ
          (galRestrict (E := K₂.L) (F := N.L) hN₂ h)) = 1 := by
  set x₁ : Gamma ↥(K₁.L) Ω ℓ :=
    galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ (galRestrict (E := K₁.L) (F := N.L) hN₁ h) with hx₁
  set x₂ : Gamma ↥(K₂.L) Ω ℓ :=
    galToGamma (K := ↥(K₂.L)) (K' := Ω) ℓ (galRestrict (E := K₂.L) (F := N.L) hN₂ h) with hx₂
  have hγ : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar x₁)
      = gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) x₂ := by
    have h0 := ambientPi_hausMk_heq_of_le K₁ K₂ L N h₁ h₂ hN₁ hN₂ hNL ℓ σbar heq
      (galToGamma (K := ↥(N.L)) (K' := Ω) ℓ h)
    rw [ambientPi_galToGamma (NumFieldIn.ofFrobLevel K₁) N hN₁ ℓ h, ambientPi_galToGamma (NumFieldIn.ofFrobLevel K₂) N hN₂ ℓ h] at h0
    rw [hx₁, hx₂]
    exact h0
  constructor
  · intro h1
    have h2 : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar x₁) = 1 :=
      (gammaHausMk_sbar_eq_one_iff (NumFieldIn.ofFrobLevel K₁) (NumFieldIn.ofFrobLevel K₂) ℓ σbar hσbar x₁).mpr h1
    rwa [hγ] at h2
  · intro h2
    have h1 : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar x₁) = 1 := by
      rw [hγ]; exact h2
    exact (gammaHausMk_sbar_eq_one_iff (NumFieldIn.ofFrobLevel K₁) (NumFieldIn.ofFrobLevel K₂) ℓ σbar hσbar x₁).mp h1

theorem lemma4f4 {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ L : FrobLevel ℚ Ω) [IsSepClosure ↥(K₁.L) Ω] [IsSepClosure ↥(K₂.L) Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥(K₁.L) Ω ℓ ≃* Gamma ↥(K₂.L) Ω ℓ) (hσbar : Continuous ⇑σbar)
    (hπ₁ : Continuous ⇑(ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ)) (hπ₂ : Continuous ⇑(ambientPi (NumFieldIn.ofFrobLevel K₂) L h₂ ℓ))
    (heq : ∀ (γ : Gamma ↥(L.L) Ω ℓ),
      gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ γ))
        = gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi (NumFieldIn.ofFrobLevel K₂) L h₂ ℓ γ)) :
    (levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ K₂.L : IntermediateField ℚ Ω)
      = (K₁.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel K₂) ℓ : IntermediateField ℚ Ω) := by
  -- the intermediate level `N = K₁ ⊔ K₂`
  set N : FrobLevel ℚ Ω := K₁.sup K₂ with hNdef
  have hN₁ : K₁.L ≤ N.L := by rw [hNdef]; exact FrobLevel.le_sup_left K₁ K₂
  have hN₂ : K₂.L ≤ N.L := by rw [hNdef]; exact FrobLevel.le_sup_right K₁ K₂
  have hNL : N.L ≤ L.L := by
    rw [hNdef, FrobLevel.sup_L]; exact sup_le h₁ h₂
  haveI : IsSepClosure ↥(N.L) Ω := isSepClosure_of_le N.L
  -- the pointwise equivalence of invisibility on `Gal(Ω/↥N.L)`
  have key : ∀ (h : Ω ≃ₐ[↥(N.L)] Ω),
      gammaHausMk (K := ↥(K₁.L)) (K' := Ω) (ℓ := ℓ)
          (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
            (galRestrict (E := K₁.L) (F := N.L) hN₁ h)) = 1
        ↔ gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
          (galToGamma (K := ↥(K₂.L)) (K' := Ω) ℓ
            (galRestrict (E := K₂.L) (F := N.L) hN₂ h)) = 1 :=
    fun h => hausMk_galToGamma_iff K₁ K₂ L N h₁ h₂ hN₁ hN₂ hNL ℓ σbar hσbar heq h
  -- the equality of fixing subgroups
  have hfix : (levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ K₂.L).fixingSubgroup
      = (K₁.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel K₂) ℓ).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_sup,
      fixingSubgroup_levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ, fixingSubgroup_levelInfinityOf (NumFieldIn.ofFrobLevel K₂) ℓ]
    refine le_antisymm ?_ ?_
    · rintro σ ⟨hσ₁, hσ₂⟩
      obtain ⟨hC, hCeq, hCinv⟩ := (mem_invisibleSub_iff (NumFieldIn.ofFrobLevel K₁) ℓ σ).mp hσ₁
      have hσC : σ ∈ (K₁.L).fixingSubgroup := by
        rw [← range_restrictScalarsHom K₁.L]
        exact ⟨hC, hCeq⟩
      have hσN : σ ∈ (N.L).fixingSubgroup := by
        rw [hNdef, FrobLevel.sup_L, IntermediateField.fixingSubgroup_sup]
        exact ⟨hσC, hσ₂⟩
      set hN : Ω ≃ₐ[↥(N.L)] Ω := (IntermediateField.fixingSubgroupEquiv N.L) ⟨σ, hσN⟩ with hNdef'
      have hNcoe : ⇑hN = ⇑σ := rfl
      have hrest₁ : galRestrict (E := K₁.L) (F := N.L) hN₁ hN = hC := by
        ext x
        exact (congrFun hNcoe x).trans (congrFun (congrArg (fun f : Ω ≃ₐ[ℚ] Ω => ⇑f) hCeq) x).symm
      have hrest₂ : restrictScalarsHom K₂.L (galRestrict (E := K₂.L) (F := N.L) hN₂ hN) = σ := by
        ext x
        exact congrFun hNcoe x
      refine ⟨hσC, ?_⟩
      change σ ∈ invisibleSub (NumFieldIn.ofFrobLevel K₂) ℓ
      rw [mem_invisibleSub_iff]
      exact ⟨galRestrict (E := K₂.L) (F := N.L) hN₂ hN, hrest₂,
        (key hN).mp (by rw [hrest₁]; exact hCinv)⟩
    · rintro σ ⟨hσ₁, hσ₂⟩
      obtain ⟨hD, hDeq, hDinv⟩ := (mem_invisibleSub_iff (NumFieldIn.ofFrobLevel K₂) ℓ σ).mp hσ₂
      have hσD : σ ∈ (K₂.L).fixingSubgroup := by
        rw [← range_restrictScalarsHom K₂.L]
        exact ⟨hD, hDeq⟩
      have hσN : σ ∈ (N.L).fixingSubgroup := by
        rw [hNdef, FrobLevel.sup_L, IntermediateField.fixingSubgroup_sup]
        exact ⟨hσ₁, hσD⟩
      set hN : Ω ≃ₐ[↥(N.L)] Ω := (IntermediateField.fixingSubgroupEquiv N.L) ⟨σ, hσN⟩ with hNdef'
      have hNcoe : ⇑hN = ⇑σ := rfl
      have hrest₂ : galRestrict (E := K₂.L) (F := N.L) hN₂ hN = hD := by
        ext x
        exact (congrFun hNcoe x).trans (congrFun (congrArg (fun f : Ω ≃ₐ[ℚ] Ω => ⇑f) hDeq) x).symm
      have hrest₁ : restrictScalarsHom K₁.L (galRestrict (E := K₁.L) (F := N.L) hN₁ hN) = σ := by
        ext x
        exact congrFun hNcoe x
      refine ⟨?_, hσD⟩
      change σ ∈ invisibleSub (NumFieldIn.ofFrobLevel K₁) ℓ
      rw [mem_invisibleSub_iff]
      exact ⟨galRestrict (E := K₁.L) (F := N.L) hN₁ hN, hrest₁,
        (key hN).mpr (by rw [hrest₂]; exact hDinv)⟩
  calc (levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ K₂.L : IntermediateField ℚ Ω)
      = IntermediateField.fixedField ((levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ K₂.L).fixingSubgroup) :=
        (InfiniteGalois.fixedField_fixingSubgroup _).symm
    _ = IntermediateField.fixedField ((K₁.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel K₂) ℓ).fixingSubgroup) := by
        rw [hfix]
    _ = (K₁.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel K₂) ℓ : IntermediateField ℚ Ω) :=
        InfiniteGalois.fixedField_fixingSubgroup _

end NK.Reconstruct
