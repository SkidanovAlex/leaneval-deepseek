import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_pow_residueCard_sub_one_eq_of_mem_higherUnits_one
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.LubinTate.norm_root_LTpolyEis

namespace NK.LocalReciprocityLubinTate.Unramified

/-! ### Plan for the prover

**Honda's reciprocity law at level one**, `N_{K_1/F}K_1ˣ = ⟨π⟩·U¹`, for `F = Q.adicCompletion K`.
This is the first case of the norm-group description that item 3 of the specification asks for; the
case `residueCard F = 2` (where both sides are everything) is already the audit
`NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_level_one_residueCard_two`.

Write `F = Q.adicCompletion K`, `q = residueCard F`, `πu` the uniformiser, and
`K_1 = LTLevel F (πu : F) q 1`, `N = normGroup F ↥K_1`.

1. **`q ≥ 2`** (`NK.LocalReciprocityLubinTate.two_le_residueCard`), and `K_1 = F(α)` where
   `α^{q-1} = -πu`: `LTpolyIter π q 1 = LTpoly π q = X(X^{q-1} + π)`
   (`LubinTate/Division.lean` and the definition of `LTpoly`), and `LTLevel` is the adjoin of the
   root set.  In particular `[K_1 : F] = q - 1` (`NK.LocalReciprocityLubinTate.finrank_LTLevel_eq`,
   using `NK.LocalReciprocityLubinTate.Unramified.exists_irreducible_natCast_of_isUniformizer` to
   pass from the unit `πu` to an irreducible element of `𝒪[F]`).
2. **`πu ∈ N`.**  `NK.LocalReciprocityLubinTate.LubinTate.norm_root_LTpolyEis F P hP q 0` gives
   `Algebra.norm F (AdjoinRoot.root (LTpolyEis (P:F) q 0)) = (-1)^{q-1}·P`, and
   `LTpolyEis π q 0 = X^{q-1} + π` (`LTpolyEis_zero`); transport this across an `F`-algebra
   isomorphism `AdjoinRoot (LTpolyEis (P:F) q 0) ≃ₐ[F] ↥K_1` (both are the adjoin of a root of the
   same irreducible polynomial — use `AdjoinRoot.lift` combined with the identification of
   `IntermediateField.adjoin F {root}` with `AdjoinRoot`, as in
   `LubinTate/norm_root_LTpolyEis.lean` / `LubinTate/finrank_adjoin_root_LTpolyEis.lean`) and use
   `NK.LocalReciprocity.normGroup_eq_of_algEquiv`.  Since `(-1)^{q-1}` is itself a norm
   (`Nm(-1) = (-1)^{q-1}`), this gives `πu ∈ N`, hence `⟨πu⟩ ⊆ N`, with no sign case split.
3. **`N = ⟨πu⟩ · W` with `W := N ∩ 𝒪[F]ˣ`.**  Since `πu ∈ N` and
   `Fˣ = ⟨πu⟩ · (unitsIncl F).range`, the quotient `N / (N ∩ 𝒪[F]ˣ)` is a subgroup of
   `Fˣ/𝒪[F]ˣ ≅ ℤ` containing the image of `πu`, hence is everything.
4. **`[𝒪[F]ˣ : W] = q - 1`.**  `[Fˣ : N] = [K_1 : F] = q - 1` by the norm index theorem — this is
   a *theorem* of the workspace for `F = Q.adicCompletion K`
   (`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q`); it is stated for levels
   of `maxAbelianSubext F (SeparableClosure F)`, so transport `K_1` into the separable closure
   exactly as `Unramified/nonempty_lubinTateTower_adicCompletion.lean` does
   (`Unramified.exists_intermediateField_algEquiv_of_isSepClosed`,
   `NK.LocalReciprocity.le_maxAbelianSubext_of_commutative`,
   `Unramified.restrictLevel`/`normGroup_restrictLevel`, `normGroup_eq_of_algEquiv`) — that file is
   the template.  And `[Fˣ : N] = [𝒪[F]ˣ : W]` because `Fˣ/N ≅ 𝒪[F]ˣ/W` (step 3).
5. **`W = U¹`.**  `W ⊇ (𝒪[F]ˣ)^{q-1}` by Lagrange in the finite group `𝒪[F]ˣ/W` of order `q-1`,
   and `(𝒪[F]ˣ)^{q-1} = U¹ = higherUnits F 1`: `⊆` because `𝒪[F]ˣ/U¹ ≅ 𝓀[F]ˣ` has order `q-1`, and
   `⊇` by `NK.LocalReciprocityLubinTate.Unramified.exists_pow_residueCard_sub_one_eq_of_mem_higherUnits_one`.
   As `[𝒪[F]ˣ : U¹] = q - 1 = [𝒪[F]ˣ : W]`
   (`NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits` with `m = 0`,
   `n = 0`), we get `W = U¹`, i.e. `N = ⟨πu⟩ ⊔ higherUnits F 1`. -/



open scoped ValuativeRel

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

universe u

noncomputable section

open Polynomial

/-! ## Auxiliary lemmas for the level-one reciprocity law -/

/-- **Commutativity of a Galois group transports along an `F`-algebra isomorphism.** -/
private theorem commutative_of_algEquiv' {F : Type*} {Ω Ω' : Type*} [Field F] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F Ω'] (e : Ω ≃ₐ[F] Ω')
    (h : ∀ σ τ : Ω ≃ₐ[F] Ω, σ * τ = τ * σ) :
    ∀ σ τ : Ω' ≃ₐ[F] Ω', σ * τ = τ * σ := by
  intro σ τ
  apply (AlgEquiv.autCongr e.symm).injective
  rw [map_mul, map_mul]
  exact h _ _

/-- **The group-theoretic index squeeze.**  If `N ≤ A` are subgroups of a group, `N` has finite
index and `[G : N] ≤ [G : A]`, then `A ≤ N` (hence `N = A`). -/
private theorem le_of_le_of_index_eq' {G : Type*} [Group G] {N A : Subgroup G}
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

/-- **The level-one division polynomial is `X` times the Eisenstein factor**:
`f^{(1)}(T) = X · (X^{q-1} + π)`. -/
theorem LTpolyIter_one_eq_X_mul_LTpolyEis_zero (F : Type u) [Field F] (π : F) (q : ℕ)
    (hq : 1 ≤ q) :
    LTpolyIter π q 1 = Polynomial.X * LTpolyEis π q 0 := by
  rw [LTpolyIter_succ, LTpolyIter_zero, Polynomial.X_comp, LTpolyEis_zero, LTpolyFactor, LTpoly]
  rw [mul_add, mul_comm Polynomial.X (Polynomial.C π), ← pow_succ', Nat.sub_add_cancel hq]
  ring

/-- **The level-one Lubin–Tate level is generated by the root of the Eisenstein factor**:
`K_1 = F(Λ_1) = F(α)` for any root `α` of `X^{q-1} + π` in the algebraic closure, and
`AdjoinRoot (X^{q-1} + π) ≃ₐ[F] K_1`. -/
theorem nonempty_algEquiv_adjoinRoot_LTpolyEis_zero_LTLevel_one (F : Type u) [Field F]
    [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : Fˣ) (hπ : IsUniformizer F (π : F)) :
    Nonempty (AdjoinRoot (LTpolyEis (π : F) (residueCard F) 0) ≃ₐ[F]
      ↥(LTLevel F (π : F) (residueCard F) 1)) := by
  classical
  have hq2 : 2 ≤ residueCard F := two_le_residueCard F
  haveI : FiniteDimensional F ↥(LTLevel F (π : F) (residueCard F) 1) :=
    LubinTate.finiteDimensional_LTLevel F (π : F) (residueCard F) 1 hq2
  obtain ⟨P, hPirr, hPcoe⟩ := exists_irreducible_natCast_of_isUniformizer F π hπ
  have hirr : Irreducible (LTpolyEis (π : F) (residueCard F) 0) := by
    rw [← hPcoe]
    exact irreducible_LTpolyEis F P hPirr (residueCard F) 0 hq2
  obtain ⟨hmon, hnat, -⟩ :=
    LubinTate.LTpolyEis_monic_natDegree_coeff_zero (π : F) (residueCard F) 0 hq2
  have hQnat : (LTpolyEis (π : F) (residueCard F) 0).natDegree = residueCard F - 1 := by
    rw [hnat, pow_zero, mul_one]
  have hdeg : (LTpolyEis (π : F) (residueCard F) 0).degree ≠ 0 := by
    have hpos : 0 < (LTpolyEis (π : F) (residueCard F) 0).natDegree := by rw [hQnat]; omega
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨α, hα⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F)
      (LTpolyEis (π : F) (residueCard F) 0) hdeg
  have hαmem : α ∈ LTLevel F (π : F) (residueCard F) 1 := by
    rw [LTLevel]
    refine IntermediateField.subset_adjoin F _ ?_
    rw [mem_LTdivisionSet_iff (π : F) (residueCard F) 1 hq2,
      LTpolyIter_one_eq_X_mul_LTpolyEis_zero F (π : F) (residueCard F) (by omega),
      Polynomial.aeval_mul, Polynomial.aeval_X, hα, mul_zero]
  have hmin : minpoly F α = LTpolyEis (π : F) (residueCard F) 0 :=
    (minpoly.eq_of_irreducible_of_monic hirr hα hmon).symm
  have hspan : IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F)) =
      LTLevel F (π : F) (residueCard F) 1 := by
    refine IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.mpr hαmem) ?_
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hmin, hQnat,
      finrank_LTLevel_eq_of_isUniformizer F π hπ 1 le_rfl]
    simp
  exact ⟨(hmin ▸ IntermediateField.adjoinRootEquivAdjoin F
      (Algebra.IsIntegral.isIntegral α)).trans (IntermediateField.equivOfEq hspan)⟩

/-- **`π` is a norm from the level-one Lubin–Tate level.**

The root `α` of the Eisenstein polynomial `X^{q-1} + π` has norm `(-1)^{q-1} π`; since `-1` has norm
`(-1)^{[K_1:F]} = (-1)^{q-1}`, the element `-α` has norm `π`, so `π` is a norm. -/
theorem mem_normGroup_LTLevel_one_of_isUniformizer (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : Fˣ) (hπ : IsUniformizer F (π : F)) :
    π ∈ NK.LocalReciprocity.normGroup F ↥(LTLevel F (π : F) (residueCard F) 1) := by
  classical
  have hq2 : 2 ≤ residueCard F := two_le_residueCard F
  haveI hfree : Module.Free F ↥(LTLevel F (π : F) (residueCard F) 1) :=
    Module.Free.of_divisionRing F ↥(LTLevel F (π : F) (residueCard F) 1)
  haveI hfin : Module.Finite F ↥(LTLevel F (π : F) (residueCard F) 1) :=
    LubinTate.finiteDimensional_LTLevel F (π : F) (residueCard F) 1 hq2
  obtain ⟨P, hPirr, hPcoe⟩ := exists_irreducible_natCast_of_isUniformizer F π hπ
  obtain ⟨e⟩ := nonempty_algEquiv_adjoinRoot_LTpolyEis_zero_LTLevel_one F π hπ
  have hnormroot : Algebra.norm F (e (AdjoinRoot.root (LTpolyEis (π : F) (residueCard F) 0))) =
      (-1) ^ (residueCard F - 1) * (π : F) := by
    rw [Algebra.norm_eq_of_algEquiv e, ← hPcoe]
    simpa using LubinTate.norm_root_LTpolyEis F P hPirr (residueCard F) 0 hq2
  have hfd : Module.finrank F ↥(LTLevel F (π : F) (residueCard F) 1) = residueCard F - 1 := by
    rw [finrank_LTLevel_eq_of_isUniformizer F π hπ 1 le_rfl]
    simp
  have hnormneg : Algebra.norm F
      (algebraMap F ↥(LTLevel F (π : F) (residueCard F) 1) (-1)) =
      (-1 : F) ^ (residueCard F - 1) := by
    rw [Algebra.norm_algebraMap, hfd]
  have hprod : Algebra.norm F
      (algebraMap F ↥(LTLevel F (π : F) (residueCard F) 1) (-1) *
        e (AdjoinRoot.root (LTpolyEis (π : F) (residueCard F) 0))) = (π : F) := by
    rw [map_mul, hnormneg, hnormroot]
    have h2 : (-1 : F) ^ (residueCard F - 1) * (-1 : F) ^ (residueCard F - 1) = 1 := by
      rw [← pow_add]
      have hcast : residueCard F - 1 + (residueCard F - 1) = 2 * (residueCard F - 1) := by ring
      rw [hcast, pow_mul, neg_one_sq, one_pow]
    rw [← mul_assoc, h2, one_mul]
  have hne : algebraMap F ↥(LTLevel F (π : F) (residueCard F) 1) (-1) *
      e (AdjoinRoot.root (LTpolyEis (π : F) (residueCard F) 0)) ≠ 0 := by
    intro h0
    have hzero : Algebra.norm F
        (algebraMap F ↥(LTLevel F (π : F) (residueCard F) 1) (-1) *
          e (AdjoinRoot.root (LTpolyEis (π : F) (residueCard F) 0))) = 0 := by
      rw [h0, Algebra.norm_zero]
    rw [hprod] at hzero
    exact Units.ne_zero π hzero
  refine (NK.LocalReciprocity.mem_normGroup_iff π).mpr ⟨Units.mk0 _ hne, ?_⟩
  exact hprod

/-- **The index of the norm group of the level-one Lubin–Tate level** of `Q.adicCompletion K` is
`q - 1`: the norm index theorem at the level `K_1`, transported into the separable closure. -/
theorem index_normGroup_LTLevel_one_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (Q.adicCompletion K)ˣ)
    (hπ : IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)) :
    (NK.LocalReciprocity.normGroup (Q.adicCompletion K)
      ↥(LTLevel (Q.adicCompletion K) (π : Q.adicCompletion K)
        (residueCard (Q.adicCompletion K)) 1)).index =
      residueCard (Q.adicCompletion K) - 1 := by
  classical
  let F := Q.adicCompletion K
  change (NK.LocalReciprocity.normGroup F ↥(LTLevel F (π : F) (residueCard F) 1)).index =
    residueCard F - 1
  let F' := SeparableClosure F
  have hq2 : 2 ≤ residueCard F := two_le_residueCard F
  haveI : FiniteDimensional F ↥(LTLevel F (π : F) (residueCard F) 1) :=
    LubinTate.finiteDimensional_LTLevel F (π : F) (residueCard F) 1 hq2
  haveI : IsGalois F ↥(LTLevel F (π : F) (residueCard F) 1) :=
    LubinTate.isGalois_LTLevel F (π : F) (residueCard F) 1 hq2
  obtain ⟨K', ⟨eK⟩⟩ := exists_intermediateField_algEquiv_of_isSepClosed (F := F) (F' := F')
    (LTLevel F (π : F) (residueCard F) 1)
  haveI hK'fd : FiniteDimensional F ↥K' :=
    FiniteDimensional.of_surjective eK.toLinearEquiv.toLinearMap eK.toLinearEquiv.surjective
  haveI hK'gal : IsGalois F ↥K' := IsGalois.of_algEquiv eK
  have hK'comm : ∀ σ τ : ↥K' ≃ₐ[F] ↥K', σ * τ = τ * σ :=
    commutative_of_algEquiv' eK (LTLevel_commutative_of_isUniformizer F π hπ 1 le_rfl)
  have hsub : K' ≤ NK.LocalReciprocity.maxAbelianSubext F F' :=
    NK.LocalReciprocity.le_maxAbelianSubext_of_commutative K' hK'comm
  have h1 : (NK.LocalReciprocity.normGroup F ↥(LTLevel F (π : F) (residueCard F) 1)).index =
      Module.finrank F ↥(LTLevel F (π : F) (residueCard F) 1) := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv eK,
      ← normGroup_restrictLevel K' hsub,
      NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q (restrictLevel K' hsub),
      LinearEquiv.finrank_eq eK.toLinearEquiv]
    exact (LinearEquiv.finrank_eq (restrictLevelEquiv K' hsub).toLinearEquiv).symm
  rw [h1, finrank_LTLevel_eq_of_isUniformizer F π hπ 1 le_rfl]
  simp

/-- **The principal units are norms from the level-one Lubin–Tate level.**

`U¹ = 1 + 𝔪[F] ⊆ K_1` consists of `(q-1)`-st powers, and every `(q-1)`-st power of a unit is a
norm because `[Fˣ : N] = q - 1`. -/
theorem higherUnits_one_le_normGroup_LTLevel_one_of_index (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : Fˣ) (hπ : IsUniformizer F (π : F))
    (hidx : (NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) 1)).index = residueCard F - 1) :
    higherUnits F 1 ≤ NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) 1) := by
  intro x hx
  obtain ⟨y, -, hyx⟩ :=
    exists_pow_residueCard_sub_one_eq_of_mem_higherUnits_one F x hx
  have hpow : y ^ (residueCard F - 1) ∈ NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) 1) := by
    have h := Subgroup.pow_index_mem (NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) 1)) y
    rwa [hidx] at h
  rwa [hyx] at hpow

/-- **Honda's reciprocity law at level one**, in the general form: if the index of the norm group of
`K_1 = F(Λ_1)` is `q - 1`, then `N_{K_1/F} K_1ˣ = ⟨π⟩ · U¹`. -/
theorem normGroup_LTLevel_one_eq_of_index (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : Fˣ) (hπ : IsUniformizer F (π : F))
    (hidx : (NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) 1)).index = residueCard F - 1) :
    NK.LocalReciprocity.normGroup F ↥(LTLevel F (π : F) (residueCard F) 1) =
      Subgroup.zpowers π ⊔ higherUnits F 1 := by
  have hle : (Subgroup.zpowers π ⊔ higherUnits F 1) ≤ NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (π : F) (residueCard F) 1) :=
    sup_le (Subgroup.zpowers_le.mpr (mem_normGroup_LTLevel_one_of_isUniformizer F π hπ))
      (higherUnits_one_le_normGroup_LTLevel_one_of_index F π hπ hidx)
  have hRidx : (Subgroup.zpowers π ⊔ higherUnits F 1).index = residueCard F - 1 := by
    rw [Subgroup.index_eq_card,
      NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits F π hπ 1 le_rfl]
    simp
  refine le_antisymm ?_ hle
  refine le_of_le_of_index_eq' hle ?_ ?_
  · rw [hRidx]
    exact Nat.sub_ne_zero_of_lt (two_le_residueCard F)
  · rw [hRidx, hidx]


/-- **Honda's reciprocity law at level one**: `N_{K_1/F} K_1ˣ = ⟨π⟩ · U¹` for
`F = Q.adicCompletion K`. -/
theorem normGroup_LTLevel_one_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (πu : (Q.adicCompletion K)ˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K)
      (πu : Q.adicCompletion K)) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K)
        ↥(NK.LocalReciprocityLubinTate.LTLevel (Q.adicCompletion K)
          (πu : Q.adicCompletion K)
          (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)) 1) =
      Subgroup.zpowers πu ⊔
        NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K) 1 :=
  normGroup_LTLevel_one_eq_of_index (Q.adicCompletion K) πu hπ
    (index_normGroup_LTLevel_one_adicCompletion Q πu hπ)

end

end NK.LocalReciprocityLubinTate.Unramified
