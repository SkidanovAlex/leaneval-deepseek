import Submission.NeukirchUchida.Conjugation
import Submission.NeukirchUchida.GaloisIso
import Submission.Commons.NumberTheory.NumberField.Valuation.normalizer_stabilizer_valuationSubring_sepClosure
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Neukirch–Uchida existence half: precise reduction to named inputs

This file isolates *exactly* what the existence half of CoNF XII Thm 12.2.1 needs beyond the
elementary conjugation machinery.  Nothing here is a `sorry`: the single remaining gap of the
challenge theorem is the conjunction of the three inputs defined below, and
`exists_sigma_of_inputs` assembles them into the conclusion.

Let `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be a continuous (indeed homeomorphic) isomorphism of
absolute Galois groups of number fields and let `A` range over the places of `K₁'` (as valuation
subrings) over the finite primes of `K₁`, with `D_A := {g : g A = A}` the decomposition group.

* `PreservesDecompositionGroups ϕ` — CoNF (12.1.9), the "if" direction, applied to `ϕ`: every
  decomposition group of `K₁'` is mapped onto a decomposition group of `K₂'`, and conversely
  (equivalently: `ϕ` preserves the place systems).  This is the input that the *local structure
  theory* of the absolute Galois groups of p-adic fields (CoNF (12.1.10) and the Demushkin theory
  of local Galois groups) has to supply.

* `RealizesPlaceMap ϕ σ` — the *reconstruction* input of CoNF §12.2: the place correspondence
  produced by `ϕ` is realized by an actual field isomorphism `σ : K₂' ≃+* K₁'` mapping the
  embedded `K₂` onto the embedded `K₁`, in the sense that the images of the decomposition groups
  under the conjugation `g ↦ σ⁻¹gσ` and under `ϕ` coincide.  In Neukirch's proof this is where the
  Čebotarev density theorem enters (the local correspondence fixes the residue characteristic and
  the absolute degree of every prime, whence `[K₁ : ℚ] = [K₂ : ℚ]`, and Čebotarev then pins down
  the field isomorphism).

* `LocalRigidity` — the anabelian rigidity statement that an automorphism of `Gal(K₂'/K₂)` which
  preserves every decomposition group setwise is the identity.  (Equivalently, by
  `stabilizer_iSup_eq_top`, that the action of `Aut(G_{K₂})` on the inverse limit of the place
  systems is faithful; equivalently, the "only if" direction of CoNF (12.1.9).)  This is a
  consequence of (12.2.1) itself with `K₁ = K₂`, and the classical proofs of the *local* version
  are due to Jarden–Ritter.

Given the three inputs, the argument is then purely group-theoretic: the automorphism
`δ = σ⁻¹ ∘ ϕ` of `G_{K₂}` preserves each decomposition group, hence is trivial by rigidity, hence
`ϕ` is the conjugation by `σ` — and `Conjugates σ ϕ` follows.
-/

namespace Submission.NeukirchUchida

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- The **decomposition group** of a place `A` of `K₁'`: the stabiliser of `A` in
`Gal(K₁'/K₁)`, i.e. the subgroup of elements `g` with `A.comap g = A`. -/
def decompositionGroup (A : ValuationSubring K₁') : Subgroup Gal(K₁'/K₁) :=
  MulAction.stabilizer Gal(K₁'/K₁) A

/-- The decomposition group of a place of `K₂'`. -/
def decompositionGroup₂ (B : ValuationSubring K₂') : Subgroup Gal(K₂'/K₂) :=
  MulAction.stabilizer Gal(K₂'/K₂) B

/-- `decompositionGroup₂` is `decompositionGroup` instantiated at the second field. -/
lemma decompositionGroup₂_eq (B : ValuationSubring K₂') :
    decompositionGroup₂ B = decompositionGroup (K₁ := K₂) (K₁' := K₂') B := rfl

/-- **Input A: CoNF (12.1.9), "if" direction, for `ϕ`.**  `ϕ` maps the decomposition groups of
the places of `K₁'` over the finite primes of `K₁` bijectively onto those of `K₂'` over the finite
primes of `K₂`. -/
def PreservesDecompositionGroups (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) : Prop :=
  (∀ A : ValuationSubring K₁', A.comap (algebraMap K₁ K₁') ≠ ⊤ →
      ∃ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ ∧
        (decompositionGroup A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = decompositionGroup₂ B) ∧
  (∀ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ →
      ∃ A : ValuationSubring K₁', A.comap (algebraMap K₁ K₁') ≠ ⊤ ∧
        (decompositionGroup A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = decompositionGroup₂ B)

/-- **Input B: the reconstruction of CoNF §12.2.**  There is a field isomorphism
`σ : K₂' ≃+* K₁'` mapping the embedded `K₂` onto the embedded `K₁` which realizes the place
correspondence induced by `ϕ`: the image of every decomposition group under the conjugation
`g ↦ σ⁻¹gσ` is the same as its image under `ϕ`. -/
def RealizesPlaceMap (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (σ : K₂' ≃+* K₁')
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) : Prop :=
  ∀ A : ValuationSubring K₁', A.comap (algebraMap K₁ K₁') ≠ ⊤ →
    (decompositionGroup A).map ((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      (decompositionGroup A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))

/-- **Input C: local rigidity of `G_{K₂}`.**  An automorphism of the absolute Galois group of
`K₂` which preserves each decomposition group of a place over a finite prime of `K₂` setwise is
the identity.  (The classical statement is the same with the extra hypothesis that the
automorphism is a homeomorphism of the Krull topology; the version below is the clean
group-theoretic form, and it is a consequence of the local rigidity of the absolute Galois groups
of p-adic fields.) -/
def LocalRigidity : Prop :=
  ∀ ψ : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂),
    (∀ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ →
      (decompositionGroup₂ B).map (ψ : Gal(K₂'/K₂) →* Gal(K₂'/K₂)) = decompositionGroup₂ B) → ψ = 1

/-- If `ϕ(D_A) = D_B` then `ϕ.symm` maps `D_B` back onto `D_A`. -/
lemma map_symm_map_eq {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {A : ValuationSubring K₁'}
    {B : ValuationSubring K₂'}
    (hAB : (decompositionGroup A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = decompositionGroup₂ B) :
    (decompositionGroup₂ B).map (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) =
      decompositionGroup A := by
  calc (decompositionGroup₂ B).map (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁))
      = ((decompositionGroup A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))).map
          (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) := by rw [hAB]
    _ = (decompositionGroup A).map
          ((ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)).comp (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))) :=
        Subgroup.map_map _ _ _
    _ = (decompositionGroup A).map (MonoidHom.id Gal(K₁'/K₁)) := by
        congr 1
        ext x
        simp
    _ = decompositionGroup A := Subgroup.map_id _

/-- **The existence half of Neukirch–Uchida, from the three named inputs.**

If `ϕ` preserves the decomposition groups (input A), the induced place correspondence is realized
by a base-field-mapping field isomorphism `σ` (input B), and `G_{K₂}` has no non-trivial
place-preserving automorphism (input C), then `σ` induces `ϕ`, i.e. `Conjugates σ ϕ`. -/
theorem exists_sigma_of_inputs {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ : K₂' ≃+* K₁'}
    {hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ}
    (hA : PreservesDecompositionGroups ϕ) (hB : RealizesPlaceMap ϕ σ hσ)
    (hC : LocalRigidity (K₂ := K₂) (K₂' := K₂')) :
    ∃ σ' : K₂' ≃+* K₁', Conjugates σ' ϕ := by
  refine ⟨σ, hσ, ?_⟩
  -- the automorphism `δ := ϕ⁻¹ ∘ (conjugation by σ)` of `G_{K₂}` preserves every `D_B`
  have hpres : ∀ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ →
      (decompositionGroup₂ B).map
          ((ϕ.symm.trans (conjHomEquiv hσ) : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) :
            Gal(K₂'/K₂) →* Gal(K₂'/K₂)) = decompositionGroup₂ B := by
    intro B hB'
    obtain ⟨A, hA', hAB⟩ := hA.2 B hB'
    have hhom : ((ϕ.symm.trans (conjHomEquiv hσ) : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) :
          Gal(K₂'/K₂) →* Gal(K₂'/K₂)) =
        ((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
          (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) := by
      ext x
      simp [MulEquiv.trans_apply, MonoidHom.comp_apply]
    rw [hhom]
    calc (decompositionGroup₂ B).map
            (((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
              (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)))
        = ((decompositionGroup₂ B).map (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁))).map
            ((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
          (Subgroup.map_map _ _ _).symm
      _ = (decompositionGroup A).map ((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := by
          rw [map_symm_map_eq hAB]
      _ = (decompositionGroup A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := hB A hA'
      _ = decompositionGroup₂ B := hAB
  have htriv : ϕ.symm.trans (conjHomEquiv hσ) = 1 := hC _ hpres
  have hEq : ∀ g : Gal(K₁'/K₁), ϕ g = conjHomEquiv hσ g := by
    intro g
    have h1 : (ϕ.symm.trans (conjHomEquiv hσ)) (ϕ g) =
        (1 : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) (ϕ g) := by rw [htriv]
    simpa [MulEquiv.trans_apply] using h1.symm
  intro g
  rw [hEq g]
  exact conj_toRingEquiv hσ g

/-- **The inverse of a homeomorphic group isomorphism is again one.** -/
theorem isHomeomorph_symm {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] (ψ : G ≃* H) (hψ : IsHomeomorph ψ) :
    IsHomeomorph (ψ.symm : H → G) := by
  refine ⟨?_, ?_, ψ.symm.bijective⟩
  · exact (Equiv.continuous_symm_iff (ψ.toEquiv)).mpr hψ.isOpenMap
  · intro U hU
    have : (ψ.symm : H → G) '' U = (ψ : G → H) ⁻¹' U := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa using hu
      · intro hx
        exact ⟨ψ x, hx, ψ.symm_apply_apply x⟩
    rw [this]
    exact hψ.continuous.isOpen_preimage U hU

/-- **Input C, homeomorphic form** (the classical statement): a *homeomorphic* automorphism of the
absolute Galois group of `K₂` which preserves every decomposition group setwise is the
identity. -/
def LocalRigidityHomeomorph : Prop :=
  ∀ ψ : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂), IsHomeomorph ψ →
    (∀ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ →
      (decompositionGroup₂ B).map (ψ : Gal(K₂'/K₂) →* Gal(K₂'/K₂)) = decompositionGroup₂ B) →
    ψ = 1

/-- **The existence half of Neukirch–Uchida from the three inputs, with the classical
(homeomorphic) form of the rigidity input.** -/
theorem exists_sigma_of_inputs_homeomorph {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    {σ : K₂' ≃+* K₁'} {hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ}
    (he : IsHomeomorph ϕ) (hconj : IsHomeomorph (conjHomEquiv hσ))
    (hA : PreservesDecompositionGroups ϕ) (hB : RealizesPlaceMap ϕ σ hσ)
    (hC : LocalRigidityHomeomorph (K₂ := K₂) (K₂' := K₂')) :
    ∃ σ' : K₂' ≃+* K₁', Conjugates σ' ϕ := by
  refine ⟨σ, hσ, ?_⟩
  have hδ : IsHomeomorph ((ϕ.symm.trans (conjHomEquiv hσ) : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) :
      Gal(K₂'/K₂) → Gal(K₂'/K₂)) := by
    have h1 : IsHomeomorph (ϕ.symm : Gal(K₂'/K₂) → Gal(K₁'/K₁)) := isHomeomorph_symm ϕ he
    have h2 : IsHomeomorph ((conjHomEquiv hσ) : Gal(K₁'/K₁) → Gal(K₂'/K₂)) := hconj
    have hcomp : ((ϕ.symm.trans (conjHomEquiv hσ) : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) :
        Gal(K₂'/K₂) → Gal(K₂'/K₂)) =
        ((conjHomEquiv hσ) : Gal(K₁'/K₁) → Gal(K₂'/K₂)) ∘
          (ϕ.symm : Gal(K₂'/K₂) → Gal(K₁'/K₁)) := by
      ext x
      simp [MulEquiv.trans_apply]
    rw [hcomp]
    exact h2.comp h1
  have hpres : ∀ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ →
      (decompositionGroup₂ B).map
          ((ϕ.symm.trans (conjHomEquiv hσ) : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) :
            Gal(K₂'/K₂) →* Gal(K₂'/K₂)) = decompositionGroup₂ B := by
    intro B hB'
    obtain ⟨A, hA', hAB⟩ := hA.2 B hB'
    have hhom : ((ϕ.symm.trans (conjHomEquiv hσ) : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) :
          Gal(K₂'/K₂) →* Gal(K₂'/K₂)) =
        ((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
          (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) := by
      ext x
      simp [MulEquiv.trans_apply, MonoidHom.comp_apply]
    rw [hhom]
    calc (decompositionGroup₂ B).map
            (((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
              (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)))
        = ((decompositionGroup₂ B).map (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁))).map
            ((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
          (Subgroup.map_map _ _ _).symm
      _ = (decompositionGroup A).map ((conjHomEquiv hσ) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := by
          rw [map_symm_map_eq hAB]
      _ = (decompositionGroup A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := hB A hA'
      _ = decompositionGroup₂ B := hAB
  have htriv : ϕ.symm.trans (conjHomEquiv hσ) = 1 := hC _ hδ hpres
  have hEq : ∀ g : Gal(K₁'/K₁), ϕ g = conjHomEquiv hσ g := by
    intro g
    have h1 : (ϕ.symm.trans (conjHomEquiv hσ)) (ϕ g) =
        (1 : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) (ϕ g) := by rw [htriv]
    simpa [MulEquiv.trans_apply] using h1.symm
  intro g
  rw [hEq g]
  exact conj_toRingEquiv hσ g

end Submission.NeukirchUchida
