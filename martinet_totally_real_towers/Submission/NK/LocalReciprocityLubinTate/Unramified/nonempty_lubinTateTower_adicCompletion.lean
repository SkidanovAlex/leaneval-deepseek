import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.unramifiedNormGroup_eq_zpowers_sup
import Submission.NK.Unramified.exists_unramified_level_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.isGalois_sup_of_commutative
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits

namespace NK.LocalReciprocityLubinTate.Unramified

/-! ### Plan for the prover

Goal: build the `LubinTateTower` for `F = Q.adicCompletion K`, `F' = SeparableClosure F`,
`π` a uniformiser, `U = higherUnits F`, `q = residueCard F`, from Honda's reciprocity law
**alone** (no `KernelCondition`).

For each `(m, n) : ℕ × ℕ`, put `E_{m,n} = E^{ur}_{m+1} ⊔ K_{n+1}` inside `F'`, where

* `E^{ur}_{m+1} ≤ AlgebraicClosure F` is the unramified level of degree `m+1` supplied by
  `NK.Unramified.exists_unramified_level_adicCompletion K Q (m+1) (by omega)`, which gives
  `FiniteDimensional`, `IsGalois`, commutativity of the Galois group, `finrank = m+1` and
  `normGroup F E^{ur}_{m+1} = unramifiedNormGroup K Q (m+1)`;
* `K_{n+1} = LTLevel F (π : F) (residueCard F) (n+1)` inside `AlgebraicClosure F`; use
  `NK.LocalReciprocityLubinTate.LubinTate.finiteDimensional_LTLevel`,
  `...isGalois_LTLevel` and the file's
  `NK.LocalReciprocityLubinTate.Unramified.LTLevel_commutative_of_isUniformizer` for its
  Galois group, and `hH (n+1) (by omega)` for its norm group.

Transport both factors into `F'` using
`NK.LocalReciprocityLubinTate.Unramified.exists_intermediateField_algEquiv_of_isSepClosed`
(the instance `IsSepClosed (SeparableClosure F)` and `IsGalois F (SeparableClosure F)` are
available; separability comes from `CharZero F`), obtaining `E', K' : IntermediateField F F'`
with `↥E' ≃ₐ[F] ↥E^{ur}_{m+1}` and `↥K' ≃ₐ[F] ↥K_{n+1}`; `normGroup` transfers by
`NK.LocalReciprocity.normGroup_eq_of_algEquiv`.

Now `L := E' ⊔ K'` is finite dimensional, normal and abelian over `F`
(`NK.LocalReciprocityLubinTate.Unramified.isGalois_sup_of_commutative`), hence
`L ≤ maxAbelianSubext F F'`
(`NK.LocalReciprocity.le_maxAbelianSubext_of_commutative`); the level of the tower is
`NK.LocalReciprocityLubinTate.Unramified.restrictLevel L hL`, and all the required properties
(including `normGroup`) transport along `restrictLevelEquiv` / `normGroup_restrictLevel` from
`Tools.lean`.

The norm-group identity `normGroup F ↥(restrictLevel L hL) = ⟨π^{m+1}⟩ ⊔ higherUnits F (n+1)`:

* `⊆`: `normGroup F ↥L ≤ normGroup F ↥E' = ⟨π^{m+1}⟩ ⊔ higherUnits F 0` and
  `normGroup F ↥L ≤ normGroup F ↥K' = ⟨π⟩ ⊔ higherUnits F (n+1)`
  (`NK.LocalReciprocity.normGroup_le_of_tower`, transitivity of the norm), and
  `Tools.inf_sup_zpowers_pow_eq` computes the intersection.
* `⊇` (index squeeze): `[Fˣ : normGroup F ↥L] = [L : F]` by
  `NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q` (a *theorem* of this
  chapter) together with `normGroup_restrictLevel`; and
  `[L : F] ≤ [E^{ur}_{m+1} : F] * [K_{n+1} : F] = (m+1) * ((residueCard F - 1) * residueCard F ^ n)`
  by `IntermediateField.finrank_sup_le`, `finrank_LTLevel_eq_of_isUniformizer` (in `Tools.lean`),
  `hfinrank` and `normGroup_eq_of_algEquiv`.  The right-hand side is
  `[Fˣ : ⟨π^{m+1}⟩ ⊔ higherUnits F (n+1)]`, which equals
  `Nat.card (Fˣ ⧸ (⟨π^{m+1}⟩ ⊔ higherUnits F (n+1)))`
  (`Subgroup.index_eq_card`), and
  `NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits F π hπ m n`
  computes it.  Since `normGroup F ↥L ≤ ⟨π^{m+1}⟩ ⊔ higherUnits F (n+1)`, the index of the latter
  is at most `[Fˣ : normGroup F ↥L]`; the two bounds give equality of the subgroups.

Note that `LubinTateTower` has exactly five fields (`level`, `finiteDimensional`, `normal`,
`commutative`, `normGroup_eq`); `exhaust` was removed from the structure.) -/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-- **Commutativity of a Galois group transports along an `F`-algebra isomorphism.** -/
private theorem commutative_of_algEquiv {F : Type*} {Ω Ω' : Type*} [Field F] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F Ω'] (e : Ω ≃ₐ[F] Ω')
    (h : ∀ σ τ : Ω ≃ₐ[F] Ω, σ * τ = τ * σ) :
    ∀ σ τ : Ω' ≃ₐ[F] Ω', σ * τ = τ * σ := by
  intro σ τ
  apply (AlgEquiv.autCongr e.symm).injective
  rw [map_mul, map_mul]
  exact h _ _

/-- **The group-theoretic index squeeze.**  If `N ≤ A` are subgroups of a group, `N` has finite
index and `[G : N] ≤ [G : A]`, then `A ≤ N` (hence `N = A`): indeed the relative index
`[A : N]` divides the quotient, so it must be `1`. -/
private theorem le_of_le_of_index_eq {G : Type*} [Group G] {N A : Subgroup G}
    (h : N ≤ A) (hN : N.index ≠ 0) (hcard : N.index ≤ A.index) : A ≤ N := by
  haveI : N.FiniteIndex := Subgroup.finiteIndex_iff.mpr hN
  have hA : A.index ≠ 0 := (Subgroup.finiteIndex_of_le h).index_ne_zero
  have hidx : A.index ≤ N.index := Subgroup.index_antitone h
  have hidxeq : N.index = A.index := le_antisymm hcard hidx
  have hrel : N.relIndex A = 1 := by
    have h1 : N.relIndex A * A.index = A.index := by
      rw [Subgroup.relIndex_mul_index h, hidxeq]
    have h2 : N.relIndex A * A.index = 1 * A.index := by
      rw [one_mul]
      exact h1
    exact mul_right_cancel₀ hA h2
  exact Subgroup.relIndex_eq_one.mp hrel

theorem nonempty_lubinTateTower_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    (hH : NK.LocalReciprocityLubinTate.HondaReciprocity (Q.adicCompletion K) π
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K))) :
    Nonempty (NK.LocalReciprocityLubinTate.LubinTateTower (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K))) := by
  classical
  let F := Q.adicCompletion K
  let F' := SeparableClosure (Q.adicCompletion K)
  have key : ∀ m n : ℕ,
      ∃ L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'),
        FiniteDimensional F ↥L ∧ Normal F ↥L ∧
        (∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) ∧
        NK.LocalReciprocity.normGroup F ↥L =
          Subgroup.zpowers (π ^ (m + 1)) ⊔ higherUnits F (n + 1) := by
    intro m n
    have hq : 2 ≤ residueCard F := two_le_residueCard F
    -- ## 1. The unramified level of degree `m + 1`, inside `AlgebraicClosure F`.
    obtain ⟨E, -, -, hEfd, hEgal, hEcomm, hErank, hEnorm⟩ :=
      NK.Unramified.exists_unramified_level_adicCompletion K Q (m + 1) (by omega)
    haveI : FiniteDimensional F ↥E := hEfd
    haveI : IsGalois F ↥E := hEgal
    -- ## 2. The Lubin–Tate level `K_{n+1}`, inside `AlgebraicClosure F`.
    haveI : FiniteDimensional F ↥(LTLevel F (π : F) (residueCard F) (n + 1)) :=
      LubinTate.finiteDimensional_LTLevel F (π : F) (residueCard F) (n + 1) hq
    haveI : IsGalois F ↥(LTLevel F (π : F) (residueCard F) (n + 1)) :=
      LubinTate.isGalois_LTLevel F (π : F) (residueCard F) (n + 1) hq
    -- ## 3. Transport both factors into `F'`.
    obtain ⟨E', ⟨eE⟩⟩ :=
      exists_intermediateField_algEquiv_of_isSepClosed (F := F) (F' := F') E
    obtain ⟨K', ⟨eK⟩⟩ :=
      exists_intermediateField_algEquiv_of_isSepClosed (F := F) (F' := F')
        (LTLevel F (π : F) (residueCard F) (n + 1))
    haveI hE'fd : FiniteDimensional F ↥E' :=
      FiniteDimensional.of_surjective eE.toLinearEquiv.toLinearMap eE.toLinearEquiv.surjective
    haveI hE'gal : IsGalois F ↥E' := IsGalois.of_algEquiv eE
    haveI hK'fd : FiniteDimensional F ↥K' :=
      FiniteDimensional.of_surjective eK.toLinearEquiv.toLinearMap eK.toLinearEquiv.surjective
    haveI hK'gal : IsGalois F ↥K' := IsGalois.of_algEquiv eK
    have hE'comm : ∀ σ τ : ↥E' ≃ₐ[F] ↥E', σ * τ = τ * σ :=
      commutative_of_algEquiv eE hEcomm
    have hK'comm : ∀ σ τ : ↥K' ≃ₐ[F] ↥K', σ * τ = τ * σ :=
      commutative_of_algEquiv eK
        (LTLevel_commutative_of_isUniformizer F π hπ (n + 1) (by omega))
    have hE'norm : NK.LocalReciprocity.normGroup F ↥E' =
        Subgroup.zpowers (π ^ (m + 1)) ⊔ higherUnits F 0 := by
      rw [← NK.LocalReciprocity.normGroup_eq_of_algEquiv eE, hEnorm,
        unramifiedNormGroup_eq_zpowers_sup Q π hπ (m + 1)]
    have hK'norm : NK.LocalReciprocity.normGroup F ↥K' =
        Subgroup.zpowers π ⊔ higherUnits F (n + 1) := by
      rw [← NK.LocalReciprocity.normGroup_eq_of_algEquiv eK]
      exact hH (n + 1) (by omega)
    have hE'rank : Module.finrank F ↥E' = m + 1 := by
      rw [← LinearEquiv.finrank_eq eE.toLinearEquiv]
      exact hErank
    have hK'rank : Module.finrank F ↥K' = (residueCard F - 1) * residueCard F ^ n := by
      rw [← LinearEquiv.finrank_eq eK.toLinearEquiv,
        finrank_LTLevel_eq_of_isUniformizer F π hπ (n + 1) (by omega), Nat.add_sub_cancel]
    -- ## 4. The compositum `L = E' ⊔ K'`.
    let L : IntermediateField F F' := E' ⊔ K'
    haveI hLfd : FiniteDimensional F ↥L :=
      (inferInstance : FiniteDimensional F ↥(E' ⊔ K'))
    have hsup := isGalois_sup_of_commutative E' K' hE'comm hK'comm
    haveI hLgal : IsGalois F ↥L := hsup.2.1
    haveI hLnormal : Normal F ↥L := inferInstance
    have hLcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ := hsup.2.2
    have hLsub : L ≤ NK.LocalReciprocity.maxAbelianSubext F F' :=
      NK.LocalReciprocity.le_maxAbelianSubext_of_commutative L hLcomm
    -- ## 5. The norm-group identity for `L`.
    have hleE : NK.LocalReciprocity.normGroup F ↥L ≤
        NK.LocalReciprocity.normGroup F ↥E' := by
      letI : Algebra ↥E' ↥L :=
        RingHom.toAlgebra (IntermediateField.inclusion (show E' ≤ L from le_sup_left) :
          ↥E' →+* ↥L)
      haveI : IsScalarTower F ↥E' ↥L := IsScalarTower.of_algebraMap_eq fun x =>
        (IntermediateField.inclusion (show E' ≤ L from le_sup_left)).commutes x
      exact NK.LocalReciprocity.normGroup_le_of_tower
    have hleK : NK.LocalReciprocity.normGroup F ↥L ≤
        NK.LocalReciprocity.normGroup F ↥K' := by
      letI : Algebra ↥K' ↥L :=
        RingHom.toAlgebra (IntermediateField.inclusion (show K' ≤ L from le_sup_right) :
          ↥K' →+* ↥L)
      haveI : IsScalarTower F ↥K' ↥L := IsScalarTower.of_algebraMap_eq fun x =>
        (IntermediateField.inclusion (show K' ≤ L from le_sup_right)).commutes x
      exact NK.LocalReciprocity.normGroup_le_of_tower
    have hleA : NK.LocalReciprocity.normGroup F ↥L ≤
        Subgroup.zpowers (π ^ (m + 1)) ⊔ higherUnits F (n + 1) := by
      rw [← inf_sup_zpowers_pow_eq F π hπ m n]
      exact le_inf (hleE.trans (le_of_eq hE'norm)) (hleK.trans (le_of_eq hK'norm))
    -- ## 6. The index squeeze.
    have hNindex : (NK.LocalReciprocity.normGroup F ↥L).index = Module.finrank F ↥L := by
      rw [← normGroup_restrictLevel L hLsub,
        NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q
          (restrictLevel L hLsub)]
      exact (LinearEquiv.finrank_eq (restrictLevelEquiv L hLsub).toLinearEquiv).symm
    have hNpos : (NK.LocalReciprocity.normGroup F ↥L).index ≠ 0 := by
      rw [hNindex]
      exact (Module.finrank_pos (R := F) (M := ↥L)).ne'
    have hcard : (NK.LocalReciprocity.normGroup F ↥L).index ≤
        (Subgroup.zpowers (π ^ (m + 1)) ⊔ higherUnits F (n + 1)).index := by
      rw [hNindex, Subgroup.index_eq_card]
      calc Module.finrank F ↥L
          ≤ Module.finrank F ↥E' * Module.finrank F ↥K' :=
            IntermediateField.finrank_sup_le (E1 := E') (E2 := K')
        _ = (m + 1) * ((residueCard F - 1) * residueCard F ^ n) := by rw [hE'rank, hK'rank]
        _ = Nat.card (Fˣ ⧸ (Subgroup.zpowers (π ^ (m + 1)) ⊔ higherUnits F (n + 1))) := by
              rw [NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits
                F π hπ m n]
              exact (Nat.mul_assoc _ _ _).symm
    have hAleN : Subgroup.zpowers (π ^ (m + 1)) ⊔ higherUnits F (n + 1) ≤
        NK.LocalReciprocity.normGroup F ↥L :=
      le_of_le_of_index_eq hleA hNpos hcard
    -- ## 7. Assemble the level of the tower.
    refine ⟨restrictLevel L hLsub, ?_, ?_, ?_, ?_⟩
    · infer_instance
    · infer_instance
    · exact commutative_restrictLevel L hLsub hLcomm
    · rw [normGroup_restrictLevel L hLsub]
      exact le_antisymm hleA hAleN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun m n => (key m n).choose
  · exact fun m n => (key m n).choose_spec.1
  · exact fun m n => (key m n).choose_spec.2.1
  · exact fun m n => (key m n).choose_spec.2.2.1
  · exact fun m n => (key m n).choose_spec.2.2.2

end

end NK.LocalReciprocityLubinTate.Unramified
