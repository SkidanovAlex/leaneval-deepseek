import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.NUV2.LC.hilbertSymbolNormCriterion
import Submission.NK.NUV2.TamePrimeLevel.index_range_powMonoidHom_le_sq
import Submission.NK.NUV2.TamePrimeLevel.normGroup_ne_of_prime_dvd_residueCard_sub_one
import Submission.NK.Summary.NUV2.normGroup_quadratic_faithful
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Distinct tame prime-degree local levels have distinct norm groups

For `F = Q.adicCompletion K` and a prime `ℓ` which is a unit of the ring of integers `𝒪_F` (i.e.
`ℓ` differs from the residue characteristic), two distinct normal intermediate fields `L₁ ≠ L₂` of
the maximal abelian subextension of a separable closure of `F`, of degree `ℓ` over `F`, have
distinct norm groups `N_{Lᵢ/F}Lᵢˣ`.

This is the tame (`ℓ ≠ p`) case of the statement that the norm group determines the abelian level;
the two cases `ℓ ∤ q-1` and `ℓ | q-1` (`q` the residue cardinality) are treated separately:

* `ℓ ∤ q-1`: a degree-`ℓ` level is unramified, and there is only one unramified degree-`ℓ` level;
* `ℓ | q-1`: `μ_ℓ ⊆ F`, Kummer theory writes `L = F⟮α⟯` with `α ^ ℓ ∈ F`, and the norm group is
  `⟨α ^ ℓ⟩ · (Fˣ)^ℓ`, which determines `L`.
-/

set_option maxHeartbeats 800000

namespace NK.NUV2.TamePrimeLevel

open IsDedekindDomain
open scoped Classical

/-- A prime `ℓ` which is a unit of the ring of integers of the completion is not the residue
characteristic. -/
lemma ne_resCharAt_of_isUnit {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ℓ : ℕ) (hunit : IsUnit ((ℓ : ℕ) : Q.adicCompletionIntegers K)) :
    ℓ ≠ NK.TameStructureDeep.Tame.resCharAt Q := by
  intro h
  have h' : ℓ = ringChar (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) := h
  have h0 : ((ℓ : ℕ) : IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) = 0 := by
    rw [ringChar.spec]
    exact ⟨1, by rw [mul_one]; exact h'⟩
  have hunit' : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) :=
    hunit.map (algebraMap (Q.adicCompletionIntegers K)
      (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)))
  exact hunit'.ne_zero h0

/-- **Two degree-`ℓ` levels inside the maximal unramified extension coincide** (`ℓ` a prime).

`Gal(F^{ur}/F) ≅ Ẑ` (`NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv`); a
subgroup of index `ℓ` contains the subgroup of `ℓ`-th powers, which has index `ℓ` in `Ẑ`, so the
index-`ℓ` subgroup is unique.  For a degree-`ℓ` normal level `M ≤ F^{ur}` the fixing subgroup has
index `[M : F] = ℓ`, and `fixedField (fixingSubgroup M) = M`, giving the result. -/
theorem eq_of_le_unramifiedClosure_of_finrank_eq_prime {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (M₁ M₂ : IntermediateField (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)))
    [FiniteDimensional (Q.adicCompletion K) ↥M₁] [Normal (Q.adicCompletion K) ↥M₁]
    [FiniteDimensional (Q.adicCompletion K) ↥M₂] [Normal (Q.adicCompletion K) ↥M₂]
    (h₁ : Module.finrank (Q.adicCompletion K) ↥M₁ = ℓ)
    (h₂ : Module.finrank (Q.adicCompletion K) ↥M₂ = ℓ)
    (hU₁ : M₁ ≤ NK.LocalAnabelian.unramifiedClosure (κ := Q.adicCompletion K)
      (K' := SeparableClosure (Q.adicCompletion K)) (NK.TameStructureDeep.Tame.resCharAt Q))
    (hU₂ : M₂ ≤ NK.LocalAnabelian.unramifiedClosure (κ := Q.adicCompletion K)
      (K' := SeparableClosure (Q.adicCompletion K)) (NK.TameStructureDeep.Tame.resCharAt Q)) :
    M₁ = M₂ := by
  set U : IntermediateField (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)) :=
    NK.LocalAnabelian.unramifiedClosure (κ := Q.adicCompletion K)
      (K' := SeparableClosure (Q.adicCompletion K)) (NK.TameStructureDeep.Tame.resCharAt Q)
    with hUdef
  have hgalU : IsGalois (Q.adicCompletion K) ↥U :=
    NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure _
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨e⟩ := NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv (K := K) Q
    (K' := SeparableClosure (Q.adicCompletion K))
  have hcomm : ∀ a b : ↥U ≃ₐ[Q.adicCompletion K] ↥U, a * b = b * a := by
    intro a b
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  haveI hcm : IsMulCommutative (↥U ≃ₐ[Q.adicCompletion K] ↥U) :=
    isMulCommutative_iff.mpr hcomm
  have huniq : ∀ (H₁ H₂ : Subgroup (↥U ≃ₐ[Q.adicCompletion K] ↥U)),
      H₁.index = ℓ → H₂.index = ℓ → H₁ = H₂ := by
    intro H₁ H₂ hi₁ hi₂
    haveI : H₁.Normal := Subgroup.normal_of_isMulCommutative H₁
    haveI : H₂.Normal := Subgroup.normal_of_isMulCommutative H₂
    set P : Subgroup (↥U ≃ₐ[Q.adicCompletion K] ↥U) :=
      (NK.TowerRank.powSubgroup ℓ).comap
        (e : (↥U ≃ₐ[Q.adicCompletion K] ↥U) →* NK.LocalAnabelian.Zhat) with hP
    have hidxP : P.index = ℓ := by
      rw [hP, Subgroup.index_comap_of_surjective (NK.TowerRank.powSubgroup ℓ) e.surjective]
      rw [← NK.TameStructureDeep.Degree.ker_compHomZMod_eq_powSubgroup ℓ hℓ.ne_zero]
      rw [Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (NK.TameStructureDeep.Degree.compHomZMod_surjective ℓ hℓ.ne_zero)).toEquiv).trans
        (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
    have hle₁ : P ≤ H₁ := by
      intro σ hσ
      rw [hP, Subgroup.mem_comap] at hσ
      have hσ' : ∃ z : NK.LocalAnabelian.Zhat,
          z ^ ℓ = (e : (↥U ≃ₐ[Q.adicCompletion K] ↥U) →* NK.LocalAnabelian.Zhat) σ := by
        rw [← Set.mem_range, ← NK.TowerRank.coe_powSubgroup]
        exact hσ
      obtain ⟨z, hz⟩ := hσ'
      have hpow : ((e.symm z) ^ ℓ) ∈ H₁ := by
        have h := Subgroup.pow_index_mem H₁ (e.symm z)
        rwa [hi₁] at h
      rw [show σ = (e.symm z) ^ ℓ from ?_]
      · exact hpow
      · apply e.injective
        rw [map_pow, MulEquiv.apply_symm_apply]
        exact hz.symm
    have hle₂ : P ≤ H₂ := by
      intro σ hσ
      rw [hP, Subgroup.mem_comap] at hσ
      have hσ' : ∃ z : NK.LocalAnabelian.Zhat,
          z ^ ℓ = (e : (↥U ≃ₐ[Q.adicCompletion K] ↥U) →* NK.LocalAnabelian.Zhat) σ := by
        rw [← Set.mem_range, ← NK.TowerRank.coe_powSubgroup]
        exact hσ
      obtain ⟨z, hz⟩ := hσ'
      have hpow : ((e.symm z) ^ ℓ) ∈ H₂ := by
        have h := Subgroup.pow_index_mem H₂ (e.symm z)
        rwa [hi₂] at h
      rw [show σ = (e.symm z) ^ ℓ from ?_]
      · exact hpow
      · apply e.injective
        rw [map_pow, MulEquiv.apply_symm_apply]
        exact hz.symm
    have hfinP : P.FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by rw [hidxP]; exact hℓ.ne_zero)
    haveI : P.FiniteIndex := hfinP
    exact (NK.Summary.NUV2.eq_of_le_of_index_eq hle₁ (by rw [hi₁, hidxP])).symm.trans
      (NK.Summary.NUV2.eq_of_le_of_index_eq hle₂ (by rw [hi₂, hidxP]))
  let M₁' : IntermediateField (Q.adicCompletion K) ↥U := M₁.comap U.val
  let M₂' : IntermediateField (Q.adicCompletion K) ↥U := M₂.comap U.val
  let e₁ : ↥M₁' ≃ₐ[Q.adicCompletion K] ↥M₁ :=
    { toFun := fun x => ⟨U.val x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hU₁ y.2⟩, y.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext (map_mul U.val x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add U.val x.1 y.1)
      commutes' := fun c => Subtype.ext (AlgHom.commutes U.val c) }
  let e₂ : ↥M₂' ≃ₐ[Q.adicCompletion K] ↥M₂ :=
    { toFun := fun x => ⟨U.val x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hU₂ y.2⟩, y.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext (map_mul U.val x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add U.val x.1 y.1)
      commutes' := fun c => Subtype.ext (AlgHom.commutes U.val c) }
  have hidx₁ : M₁'.fixingSubgroup.index = ℓ := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index (E' := ↥U) M₁',
      e₁.toLinearEquiv.finrank_eq, h₁]
  have hidx₂ : M₂'.fixingSubgroup.index = ℓ := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index (E' := ↥U) M₂',
      e₂.toLinearEquiv.finrank_eq, h₂]
  have hfix : M₁'.fixingSubgroup = M₂'.fixingSubgroup := huniq _ _ hidx₁ hidx₂
  have hmap₁ : M₁ = M₁'.map U.val := by
    change M₁ = (M₁.comap U.val).map U.val
    exact (IntermediateField.map_comap_eq_self (f := U.val) (S := M₁)
      (by rw [IntermediateField.fieldRange_val]; exact hU₁)).symm
  have hmap₂ : M₂ = M₂'.map U.val := by
    change M₂ = (M₂.comap U.val).map U.val
    exact (IntermediateField.map_comap_eq_self (f := U.val) (S := M₂)
      (by rw [IntermediateField.fieldRange_val]; exact hU₂)).symm
  have hM₁' : M₁' = M₂' := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M₁',
      ← InfiniteGalois.fixedField_fixingSubgroup M₂', hfix]
  rw [hmap₁, hmap₂, hM₁']


theorem le_unramifiedClosure_of_prime_ne_resCharAt {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hne_char : ℓ ≠ NK.TameStructureDeep.Tame.resCharAt Q)
    (hnotdvd : ¬ ℓ ∣ NK.LocalStructure.residueCard K Q - 1)
    (L : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) ↥L] [Normal (Q.adicCompletion K) ↥L]
    (hL : Module.finrank (Q.adicCompletion K) ↥L = ℓ) :
    NK.LocalReciprocity.levelMap L ≤
      NK.LocalAnabelian.unramifiedClosure (κ := Q.adicCompletion K)
        (K' := SeparableClosure (Q.adicCompletion K))
        (NK.TameStructureDeep.Tame.resCharAt Q) := by
  have hcore : NK.TameStructureDeep.TameRamificationCore
      (NK.TameStructureDeep.Tame.resCharAt Q) (NK.LocalStructure.residueCard K Q)
      (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)) :=
    NK.TameStructureDeep.Tame.tameRamificationCore_adicCompletion_residueChar (K := K) Q
      (K' := SeparableClosure (Q.adicCompletion K))
  have hgp : Nat.card (↥(NK.LocalReciprocity.levelMap L) ≃ₐ[Q.adicCompletion K]
      ↥(NK.LocalReciprocity.levelMap L)) = ℓ := by
    rw [IsGalois.card_aut_eq_finrank]
    exact ((NK.LocalReciprocity.levelEquiv L).toLinearEquiv.finrank_eq).symm.trans hL
  -- (a) the wild inertia acts trivially on the level
  have hVker : NK.LocalTame.wildInertiaSubgroup
        (κ := Q.adicCompletion K) (K' := SeparableClosure (Q.adicCompletion K))
        (NK.TameStructureDeep.Tame.resCharAt Q) ≤
      (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K)) ↥(NK.LocalReciprocity.levelMap L)).ker := by
    have hpro : NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt Q)
        ↥(NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
          (K' := SeparableClosure (Q.adicCompletion K))
          (NK.TameStructureDeep.Tame.resCharAt Q)) :=
      NK.LocalTame.wildInertiaSubgroup_isProP (κ := Q.adicCompletion K)
        (K' := SeparableClosure (Q.adicCompletion K)) (NK.TameStructureDeep.Tame.resCharAt Q)
    haveI : ((AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K))
        ↥(NK.LocalReciprocity.levelMap L)).comp
          (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
            (K' := SeparableClosure (Q.adicCompletion K))
            (NK.TameStructureDeep.Tame.resCharAt Q)).subtype).ker.Normal :=
      MonoidHom.normal_ker _
    haveI hfin : ((AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K))
        ↥(NK.LocalReciprocity.levelMap L)).comp
          (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
            (K' := SeparableClosure (Q.adicCompletion K))
            (NK.TameStructureDeep.Tame.resCharAt Q)).subtype).ker.FiniteIndex :=
      Subgroup.finiteIndex_ker _
    obtain ⟨k, hk⟩ := hpro ((AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K))
        ↥(NK.LocalReciprocity.levelMap L)).comp
          (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
            (K' := SeparableClosure (Q.adicCompletion K))
            (NK.TameStructureDeep.Tame.resCharAt Q)).subtype).ker hfin
    have hcard : Nat.card (MonoidHom.range ((AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K))
        ↥(NK.LocalReciprocity.levelMap L)).comp
          (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
            (K' := SeparableClosure (Q.adicCompletion K))
            (NK.TameStructureDeep.Tame.resCharAt Q)).subtype)) =
        (NK.TameStructureDeep.Tame.resCharAt Q) ^ k := by
      rw [← hk, Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv.symm
    have hdvd : (NK.TameStructureDeep.Tame.resCharAt Q) ^ k ∣ ℓ := by
      rw [← hcard]
      have h2 := Subgroup.card_subgroup_dvd_card (MonoidHom.range ((AlgEquiv.restrictNormalHom
        (F := Q.adicCompletion K) (K₁ := SeparableClosure (Q.adicCompletion K))
        ↥(NK.LocalReciprocity.levelMap L)).comp
          (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
            (K' := SeparableClosure (Q.adicCompletion K))
            (NK.TameStructureDeep.Tame.resCharAt Q)).subtype))
      rwa [hgp] at h2
    have hp1 : (NK.TameStructureDeep.Tame.resCharAt Q) ^ k = 1 := by
      rcases hℓ.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact h1
      · exfalso
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [pow_zero] at h1
          exact absurd h1 (by have := hℓ.two_le; omega)
        have hple : NK.TameStructureDeep.Tame.resCharAt Q ∣ ℓ := by
          rw [← h1]; exact dvd_pow_self _ hk0
        rcases (Nat.dvd_prime hℓ).mp hple with h2 | h2
        · exact hcore.hp.ne_one h2
        · exact hne_char h2.symm
    have htop : ((AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K))
        ↥(NK.LocalReciprocity.levelMap L)).comp
          (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
            (K' := SeparableClosure (Q.adicCompletion K))
            (NK.TameStructureDeep.Tame.resCharAt Q)).subtype).ker = ⊤ :=
      Subgroup.index_eq_one.mp (by rw [hk, hp1])
    intro x hx
    rw [MonoidHom.mem_ker]
    have hmem : (⟨x, hx⟩ : ↥(NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
        (K' := SeparableClosure (Q.adicCompletion K))
        (NK.TameStructureDeep.Tame.resCharAt Q))) ∈ ((AlgEquiv.restrictNormalHom
          (F := Q.adicCompletion K) (K₁ := SeparableClosure (Q.adicCompletion K))
          ↥(NK.LocalReciprocity.levelMap L)).comp
            (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
              (K' := SeparableClosure (Q.adicCompletion K))
              (NK.TameStructureDeep.Tame.resCharAt Q)).subtype).ker := by
      rw [htop]; trivial
    rw [MonoidHom.mem_ker] at hmem
    simpa using hmem
  -- (b) the inertia acts trivially
  have hIker : NK.LocalAnabelian.inertiaSubgroup
        (κ := Q.adicCompletion K) (K' := SeparableClosure (Q.adicCompletion K))
        (NK.TameStructureDeep.Tame.resCharAt Q) ≤
      (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K)) ↥(NK.LocalReciprocity.levelMap L)).ker := by
    obtain ⟨x, hx⟩ := hcore.exists_frobenius
    have hx' : NK.LocalTame.IsTameFrobeniusLift (NK.LocalStructure.residueCard K Q)
        (NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
          (K' := SeparableClosure (Q.adicCompletion K))
          (NK.TameStructureDeep.Tame.resCharAt Q))
        (NK.LocalAnabelian.inertiaSubgroup (κ := Q.adicCompletion K)
          (K' := SeparableClosure (Q.adicCompletion K))
          (NK.TameStructureDeep.Tame.resCharAt Q)) x := (hcore.frobenius_iff x).mp hx
    intro y hy
    have hmem : x * y * x⁻¹ * (y ^ NK.LocalStructure.residueCard K Q)⁻¹ ∈
        NK.LocalTame.wildInertiaSubgroup (κ := Q.adicCompletion K)
          (K' := SeparableClosure (Q.adicCompletion K))
          (NK.TameStructureDeep.Tame.resCharAt Q) := hx'.2 y hy
    set rx := (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
      (K₁ := SeparableClosure (Q.adicCompletion K)) ↥(NK.LocalReciprocity.levelMap L)) x with hrx
    set ry := (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
      (K₁ := SeparableClosure (Q.adicCompletion K)) ↥(NK.LocalReciprocity.levelMap L)) y with hry
    have hcomm : ∀ a b : ↥(NK.LocalReciprocity.levelMap L) ≃ₐ[Q.adicCompletion K]
        ↥(NK.LocalReciprocity.levelMap L), a * b = b * a :=
      NK.LocalReciprocity.commutative_levelMap L
    have h1 : (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := SeparableClosure (Q.adicCompletion K))
        ↥(NK.LocalReciprocity.levelMap L))
        (x * y * x⁻¹ * (y ^ NK.LocalStructure.residueCard K Q)⁻¹) = 1 := hVker hmem
    have h2 : rx * ry * rx⁻¹ = ry ^ (NK.LocalStructure.residueCard K Q) := by
      have key : (rx * ry * rx⁻¹) * (ry ^ (NK.LocalStructure.residueCard K Q))⁻¹ = 1 := by
        rw [hrx, hry]
        simpa only [map_mul, map_inv, map_pow] using h1
      exact mul_inv_eq_one.mp key
    have h3 : ry ^ (NK.LocalStructure.residueCard K Q) = ry := by
      rw [← h2, hcomm rx ry, mul_assoc, mul_inv_cancel, mul_one]
    rw [MonoidHom.mem_ker, ← hry]
    have hq2 : 1 ≤ NK.LocalStructure.residueCard K Q := by
      have h := NK.TameStructureDeep.Tame.two_le_residueCard_adicCompletion K Q
      omega
    have hq1 : ry ^ (NK.LocalStructure.residueCard K Q - 1) = 1 := by
      have hpow : ry ^ (NK.LocalStructure.residueCard K Q - 1) * ry = 1 * ry := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hq2, h3]
      exact mul_right_cancel hpow
    have hℓ1 : ry ^ ℓ = 1 := by
      rw [← hgp]
      exact pow_card_eq_one'
    have hcop : Nat.Coprime ℓ (NK.LocalStructure.residueCard K Q - 1) :=
      (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hnotdvd
    have hord : orderOf ry ∣ ℓ := orderOf_dvd_iff_pow_eq_one.mpr hℓ1
    have hord2 : orderOf ry ∣ (NK.LocalStructure.residueCard K Q - 1) :=
      orderOf_dvd_iff_pow_eq_one.mpr hq1
    have hone : orderOf ry = 1 :=
      Nat.dvd_one.mp (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hord hord2)
    exact orderOf_eq_one_iff.mp hone
  -- (c) the conclusion
  have hle : NK.LocalReciprocity.levelMap L ≤ IntermediateField.fixedField
      (NK.LocalAnabelian.inertiaSubgroup (κ := Q.adicCompletion K)
        (K' := SeparableClosure (Q.adicCompletion K))
        (NK.TameStructureDeep.Tame.resCharAt Q)) :=
    (IntermediateField.le_iff_le _ (NK.LocalReciprocity.levelMap L)).mpr
      (by rw [← IntermediateField.restrictNormalHom_ker (NK.LocalReciprocity.levelMap L)]
          exact hIker)
  rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
      (κ := Q.adicCompletion K) (K' := SeparableClosure (Q.adicCompletion K))
      (NK.TameStructureDeep.Tame.resCharAt Q),
    InfiniteGalois.fixedField_fixingSubgroup] at hle
  exact hle


/-- **Distinct tame prime-degree levels have distinct norm groups.**  `F = Q.adicCompletion K`,
`ℓ` a prime which is a unit of `𝒪_F`, and `L₁ ≠ L₂` normal levels of `F^{ab}` of degree `ℓ`. -/
theorem normGroup_ne_of_finrank_eq_prime_tame
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓunit : IsUnit ((ℓ : ℕ) : Q.adicCompletionIntegers K))
    (L₁ L₂ : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) ↥L₁] [Normal (Q.adicCompletion K) ↥L₁]
    [FiniteDimensional (Q.adicCompletion K) ↥L₂] [Normal (Q.adicCompletion K) ↥L₂]
    (h₁ : Module.finrank (Q.adicCompletion K) ↥L₁ = ℓ)
    (h₂ : Module.finrank (Q.adicCompletion K) ↥L₂ = ℓ)
    (hne : L₁ ≠ L₂) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁
      ≠ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ := by
  by_cases htwo : ℓ = 2
  · subst htwo
    exact NK.Summary.NUV2.normGroup_quadratic_faithful Q L₁ L₂ h₁ h₂ hne
  · by_cases hdvd : ℓ ∣ NK.LocalStructure.residueCard K Q - 1
    · exact normGroup_ne_of_prime_dvd_residueCard_sub_one Q ℓ hℓ htwo hdvd
        (index_range_powMonoidHom_le_sq Q ℓ hℓ hℓunit) L₁ L₂ h₁ h₂ hne
    · exfalso
      apply hne
      have hne_char : ℓ ≠ NK.TameStructureDeep.Tame.resCharAt Q :=
        ne_resCharAt_of_isUnit Q ℓ hℓunit
      have hU₁ := le_unramifiedClosure_of_prime_ne_resCharAt Q ℓ hℓ hne_char hdvd L₁ h₁
      have hU₂ := le_unramifiedClosure_of_prime_ne_resCharAt Q ℓ hℓ hne_char hdvd L₂ h₂
      have hlev : NK.LocalReciprocity.levelMap L₁ = NK.LocalReciprocity.levelMap L₂ :=
        eq_of_le_unramifiedClosure_of_finrank_eq_prime Q ℓ hℓ _ _
          (by rw [← (NK.LocalReciprocity.levelEquiv L₁).toLinearEquiv.finrank_eq, h₁])
          (by rw [← (NK.LocalReciprocity.levelEquiv L₂).toLinearEquiv.finrank_eq, h₂])
          hU₁ hU₂
      exact IntermediateField.map_injective _ hlev

end NK.NUV2.TamePrimeLevel
