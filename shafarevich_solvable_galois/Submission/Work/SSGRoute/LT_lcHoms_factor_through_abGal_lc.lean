import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Connected.Separation
import Submission.NK.NUV2.kernelCondition_all
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every locally constant `𝔽_p`-character of `Gal(F'/F)` factors through `Gal(F^{ab}/F)`

Let `F'/F` be a Galois extension and `p` a prime.  A locally constant (for the Krull
topology) group homomorphism `χ : Gal(F'/F) →* 𝔽_pˣ` has abelian target, so it kills the
commutator subgroup `⁅G,G⁆` of `G = Gal(F'/F)`; being locally constant its kernel is
*open*, hence closed, so it kills the closure `⁅G,G⁆̄ = ker ρ` of the commutator subgroup,
where `ρ = AlgEquiv.restrictNormalHom : Gal(F'/F) →* Gal(F^{ab}/F)` is the restriction to the
maximal abelian subextension `F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'`
(`ker ρ = ⁅G,G⁆̄`, `NK.PTorsionTop.ker_restrictNormalHom_maxAbelianSubext_eq`).

Hence `χ` descends along `ρ` to a homomorphism `χbar` on `Gal(F^{ab}/F)`, and `χbar` is again
locally constant: `ρ` is an open surjection (a continuous surjective homomorphism between the
compact group `Gal(F'/F)` and the Hausdorff group `Gal(F^{ab}/F)` is a quotient map, and a
quotient map which is a group homomorphism is open), so the openness of `ker χ` transfers to
the openness of `ker χbar`.

This is the local-class-field-theory side of the statement that the elementary abelian
`p`-characters of the absolute Galois group are exactly the characters of its topological
abelianisation.
-/

open scoped Classical Pointwise

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- A group homomorphism out of a topological group whose kernel is open is locally constant: it
is constant on the cosets of its kernel, and those are open. -/
private theorem lcHoms_factor_isLocallyConstant_of_isOpen_ker {G M : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Group M] (f : G →* M)
    (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨x • (f.ker : Set G), h.smul x, ⟨1, f.ker.one_mem, by simp⟩, ?_⟩
  rintro y ⟨k, hk, rfl⟩
  change f (x * k) = f x
  rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]

/-- A locally constant homomorphism has open kernel: its kernel is the preimage of the point `1`
under such a map. -/
private theorem lcHoms_factor_isOpen_ker_of_isLocallyConstant {G M : Type*} [Group G]
    [TopologicalSpace G] [Group M] (f : G →* M) (hf : IsLocallyConstant f) :
    IsOpen (f.ker : Set G) := by
  rw [show (f.ker : Set G) = f ⁻¹' ({1} : Set M) from by
    ext y; simp [MonoidHom.mem_ker]]
  exact hf {1}

theorem LT_lcHoms_factor_through_abGal_lc {F F' : Type} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (p : ℕ) [Fact p.Prime]
    (χ : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[F] F'))) :
    ∃ χbar : ↥(Work.SSGRoute.lcHoms p (NK.LocalCFT.AbGal F F')),
      ∀ σ : F' ≃ₐ[F] F',
        χbar.1 (AlgEquiv.restrictNormalHom (F := F) (K₁ := F')
          (NK.LocalReciprocity.maxAbelianSubext F F') σ) = χ.1 σ := by
  -- Notation: `M = F^{ab}` is the maximal abelian subextension and `ρ` the restriction map.
  let M := NK.LocalReciprocity.maxAbelianSubext F F'
  let ρ : (F' ≃ₐ[F] F') →* (M ≃ₐ[F] M) := AlgEquiv.restrictNormalHom (F := F) (K₁ := F') M
  haveI : IsGalois F M := NK.LocalReciprocity.instIsGaloisMaxAbelianSubext
  have hρ_surj : Function.Surjective ρ :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) F'
  -- The kernel of `ρ` is the (Krull-)closure of the commutator subgroup of `Gal(F'/F)`.
  have hkerρ : ρ.ker = (commutator (F' ≃ₐ[F] F')).topologicalClosure := by
    rw [show ρ = AlgEquiv.restrictNormalHom (F := F) (K₁ := F') M from rfl,
      IntermediateField.restrictNormalHom_ker M]
    exact NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure _
  -- `χ.1` lands in an abelian group, so it kills the commutator subgroup ...
  have hcomm_le : commutator (F' ≃ₐ[F] F') ≤ χ.1.ker := by
    change ⁅(⊤ : Subgroup (F' ≃ₐ[F] F')), ⊤⁆ ≤ χ.1.ker
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  -- ... and, being locally constant, it has open (hence closed) kernel.
  have hχker_open : IsOpen (χ.1.ker : Set (F' ≃ₐ[F] F')) :=
    lcHoms_factor_isOpen_ker_of_isLocallyConstant χ.1 χ.2
  have hχker_closed : IsClosed (χ.1.ker : Set (F' ≃ₐ[F] F')) :=
    Subgroup.isClosed_of_isOpen χ.1.ker hχker_open
  have hker_le : ρ.ker ≤ χ.1.ker := by
    rw [hkerρ]
    exact Subgroup.topologicalClosure_minimal _ hcomm_le hχker_closed
  -- Descent of `χ.1` through the quotient by `ker ρ ≅ Gal(F^{ab}/F)`.
  let f₁ : (F' ≃ₐ[F] F') ⧸ ρ.ker →* Multiplicative (ZMod p) :=
    QuotientGroup.lift ρ.ker χ.1 hker_le
  let e : ((F' ≃ₐ[F] F') ⧸ ρ.ker) ≃* NK.LocalCFT.AbGal F F' :=
    QuotientGroup.quotientKerEquivOfSurjective ρ hρ_surj
  have he_apply : ∀ σ : F' ≃ₐ[F] F', e (QuotientGroup.mk σ) = ρ σ := by
    intro σ
    exact QuotientGroup.kerLift_mk ρ σ
  -- The factorization formula `χbar (ρ σ) = χ σ`.
  have hfac : ∀ σ : F' ≃ₐ[F] F', (f₁.comp e.symm.toMonoidHom) (ρ σ) = χ.1 σ := by
    intro σ
    change f₁ (e.symm (ρ σ)) = χ.1 σ
    rw [← he_apply σ, MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk' ρ.ker hker_le σ
  -- The kernel of the descended character is the image of `ker χ.1` under `ρ`.
  have hker_map : (f₁.comp e.symm.toMonoidHom).ker = χ.1.ker.map ρ := by
    ext a
    constructor
    · intro ha
      obtain ⟨g, rfl⟩ := hρ_surj a
      exact ⟨g, MonoidHom.mem_ker.mpr (by rw [← hfac g]; exact MonoidHom.mem_ker.mp ha), rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact MonoidHom.mem_ker.mpr (by rw [hfac g]; exact MonoidHom.mem_ker.mp hg)
  -- `ρ` is open (it is a quotient map, being a continuous surjection from a compact group onto a
  -- Hausdorff group), so the descended character is locally constant.
  have hker_open : IsOpen ((f₁.comp e.symm.toMonoidHom).ker : Set (M ≃ₐ[F] M)) := by
    haveI : CompactSpace (F' ≃ₐ[F] F') := inferInstance
    haveI : T2Space (M ≃ₐ[F] M) := inferInstance
    have hcont : Continuous (⇑ρ) := by
      rw [show ρ = AlgEquiv.restrictNormalHom (F := F) (K₁ := F') M from rfl]
      exact InfiniteGalois.restrictNormalHom_continuous M
    have hquot : Topology.IsQuotientMap (⇑ρ) :=
      Topology.IsQuotientMap.of_surjective_continuous hρ_surj hcont
    have hρopen : IsOpenMap (⇑ρ) :=
      (MonoidHom.isOpenQuotientMap_of_isQuotientMap hquot).isOpenMap
    rw [hker_map, Subgroup.coe_map]
    exact hρopen _ hχker_open
  refine ⟨⟨f₁.comp e.symm.toMonoidHom,
    lcHoms_factor_isLocallyConstant_of_isOpen_ker _ hker_open⟩, ?_⟩
  intro σ
  simpa only using hfac σ

end Work.SSGRoute
