import Submission.NK.NUV2.LC.hilbertSymbolNormCriterion
import Submission.NK.LocalReciprocity.MaxAbelianSetup

/-!
# The norm group determines the abelian level

For a field `F` with a Galois extension `F'` and a **reciprocity datum**
`R : NK.LocalArtin.ReciprocityMap F F'` — a single Artin map `Fˣ →* Gal(F^{ab}/F)` whose
composite with the restriction to every finite abelian level `L ≤ F^{ab}` is *surjective with
kernel the norm group* `N_{L/F}Lˣ` (the local reciprocity law in the form supplied by
`NK.NUV2.KCAll` through `NK.NUV2.LC.reciprocityMapAtCompletion`) — this file proves:

* `ker_levelRestrict` — the kernel of the restriction `Gal(F^{ab}/F) →* Gal(L/F)` is the fixing
  subgroup of `L`;
* `normGroup_eq_comap_fixingSubgroup` — `N_{L/F}Lˣ = artin⁻¹(Gal(F^{ab}/L))`;
* `index_normGroup_eq_finrank` — `[Fˣ : N_{L/F}Lˣ] = [L : F]`;
* **`normGroup_injective`** — **the norm group determines the level**:
  `N_{L/F}Lˣ = N_{L'/F}L'ˣ ⟹ L = L'` for finite normal levels `L, L' ≤ F^{ab}`;
* its quadratic case `normGroup_quadLevel_eq_iff`;
* **`hilbertSymbolAt_forall_eq_one_iff_isSquare`** — **the `p = 2` Hilbert pairing is
  non-degenerate in the second variable**: `(a,b) = 1` for all `a` if and only if `b` is a square.

## Why this matters

The map `L ↦ N_{L/F}Lˣ` being *injective* is the injective half of the norm-subgroup
correspondence, and in its quadratic case it is exactly the classical statement that *distinct
quadratic levels have distinct norm groups*, i.e. the non-degeneracy of the Kummer/Hilbert pairing
`Fˣ/(Fˣ)² × Fˣ/(Fˣ)² → {±1}` (Serre, *Local Fields*, Ch. XV §5.2; Iwasawa, *Local Class Field
Theory*, Thm. 6.9, in its smallest case).  That statement is the local input consumed by the
canonicity of the Artin symbol, and hence by Hilbert reciprocity `Σ_v inv_v = 0`; here it is
*derived* from the reciprocity datum `R` (in particular from the level-kernel property), which is
the hypothesis under which the `p = 2` local chapter of this development works.

## Method

The three levels `L`, `L'` and `L ⊔ L'` are compared.  From
`normGroup_eq_comap_fixingSubgroup` and `IntermediateField.fixingSubgroup_sup`,
`N_{L⊔L'} = N_L ⊓ N_{L'}`; hence `N_L = N_{L'}` forces `N_{L⊔L'} = N_L`, and then
`index_normGroup_eq_finrank` gives `[L ⊔ L' : F] = [L : F]`, so `L' ≤ L`; symmetrically
`L ≤ L'`.  No canonicity of the Artin map beyond its level kernels is used.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace NK.NUV2.LC

open NK.LocalArtin

section General

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The kernel of the restriction to a level is the fixing subgroup.** -/
theorem ker_levelRestrict (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] :
    MonoidHom.ker (levelRestrict L) = L.fixingSubgroup := by
  change MonoidHom.ker (AlgEquiv.restrictNormalHom (F := F)
    (K₁ := NK.LocalReciprocity.maxAbelianSubext F F') L) = L.fixingSubgroup
  exact IntermediateField.restrictNormalHom_ker L

/-- **`Gal(L/F)` is commutative for every normal level `L ≤ F^{ab}`**: it is a quotient of the
commutative group `Gal(F^{ab}/F)`. -/
theorem commutative_level (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] :
    ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ := by
  intro σ τ
  obtain ⟨σ₀, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L)
    (E := NK.LocalReciprocity.maxAbelianSubext F F') σ
  obtain ⟨τ₀, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L)
    (E := NK.LocalReciprocity.maxAbelianSubext F F') τ
  rw [← map_mul, ← map_mul, NK.LocalReciprocity.commutative_gal_maxAbelianSubext τ₀ σ₀]

/-- **The norm group as the preimage of the fixing subgroup**:
`N_{L/F}Lˣ = artin⁻¹(Gal(F^{ab}/L))`.  This is the reciprocity law at the level `L` rewritten
through `ker_levelRestrict`. -/
theorem normGroup_eq_comap_fixingSubgroup (R : ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] :
    NK.LocalReciprocity.normGroup F ↥L = L.fixingSubgroup.comap R.artin := by
  have h := (R.isLevelIso L (commutative_level L)).2
  have h2 : ((levelRestrict L).comp R.artin).ker = L.fixingSubgroup.comap R.artin := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_levelRestrict L,
      Subgroup.mem_comap]
  exact h.symm.trans h2

/-- **The norm index theorem at a level, from the reciprocity datum**:
`[Fˣ : N_{L/F}Lˣ] = [L : F]`. -/
theorem index_normGroup_eq_finrank (R : ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] :
    (NK.LocalReciprocity.normGroup F ↥L).index = Module.finrank F ↥L := by
  have hsurj := (R.isLevelIso L (commutative_level L)).1
  have hker := (R.isLevelIso L (commutative_level L)).2
  set f : Fˣ →* (↥L ≃ₐ[F] ↥L) := (levelRestrict L).comp R.artin with hf
  have hk : f.ker = NK.LocalReciprocity.normGroup F ↥L := hker
  haveI : (NK.LocalReciprocity.normGroup F ↥L).FiniteIndex := by
    rw [← hk]; exact Subgroup.finiteIndex_ker f
  rw [Subgroup.index_eq_card, ← hk,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv,
    IsGalois.card_aut_eq_finrank F ↥L]

/-- **The norm group determines the level** (the injective half of the norm-subgroup
correspondence, in the form in which the local reciprocity law supplies it): for finite normal
levels `L, L' ≤ F^{ab}`, `N_{L/F}Lˣ = N_{L'/F}L'ˣ` implies `L = L'`. -/
theorem normGroup_injective (R : ReciprocityMap F F')
    (L L' : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] [FiniteDimensional F L'] [Normal F L']
    (h : NK.LocalReciprocity.normGroup F ↥L = NK.LocalReciprocity.normGroup F ↥L') :
    L = L' := by
  haveI : FiniteDimensional F ↥(L ⊔ L') := inferInstance
  haveI : Normal F ↥(L ⊔ L') := inferInstance
  -- `N_{L ⊔ L'} = N_L ⊓ N_{L'}`
  have hinf : NK.LocalReciprocity.normGroup F ↥(L ⊔ L') =
      NK.LocalReciprocity.normGroup F ↥L ⊓ NK.LocalReciprocity.normGroup F ↥L' := by
    rw [normGroup_eq_comap_fixingSubgroup R (L ⊔ L'),
      normGroup_eq_comap_fixingSubgroup R L, normGroup_eq_comap_fixingSubgroup R L',
      IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf]
  have hsup : NK.LocalReciprocity.normGroup F ↥(L ⊔ L') =
      NK.LocalReciprocity.normGroup F ↥L := by
    rw [hinf, h, inf_idem]
  -- the finranks agree, so `L ⊔ L' = L`
  have hfin : Module.finrank F ↥(L ⊔ L') = Module.finrank F ↥L := by
    rw [← index_normGroup_eq_finrank R (L ⊔ L'), hsup, index_normGroup_eq_finrank R L]
  have hle : L ≤ L ⊔ L' := le_sup_left
  have hEq : L ⊔ L' = L :=
    (IntermediateField.eq_of_le_of_finrank_le hle (by rw [hfin])).symm
  have hL' : L' ≤ L := by
    have : L' ≤ L ⊔ L' := le_sup_right
    rw [hEq] at this
    exact this
  -- symmetrically `L ≤ L'`
  have hL : L ≤ L' := by
    have h' : NK.LocalReciprocity.normGroup F ↥L' = NK.LocalReciprocity.normGroup F ↥L :=
      h.symm
    have hinf' : NK.LocalReciprocity.normGroup F ↥(L' ⊔ L) =
        NK.LocalReciprocity.normGroup F ↥L' ⊓ NK.LocalReciprocity.normGroup F ↥L := by
      rw [normGroup_eq_comap_fixingSubgroup R (L' ⊔ L),
        normGroup_eq_comap_fixingSubgroup R L', normGroup_eq_comap_fixingSubgroup R L,
        IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf]
    have hsup' : NK.LocalReciprocity.normGroup F ↥(L' ⊔ L) =
        NK.LocalReciprocity.normGroup F ↥L' := by
      rw [hinf', h', inf_idem]
    have hfin' : Module.finrank F ↥(L' ⊔ L) = Module.finrank F ↥L' := by
      rw [← index_normGroup_eq_finrank R (L' ⊔ L), hsup', index_normGroup_eq_finrank R L']
    have hle' : L' ≤ L' ⊔ L := le_sup_left
    have hEq' : L' ⊔ L = L' :=
      (IntermediateField.eq_of_le_of_finrank_le hle' (by rw [hfin'])).symm
    have : L ≤ L' ⊔ L := le_sup_right
    rw [hEq'] at this
    exact this
  exact le_antisymm hL hL'

end General

section Quadratic
variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
variable [NeZero (2 : F)]

/-- The element `√b` of the quadratic level `F(√b)`, as an element of the level itself. -/
noncomputable def quadRoot (y : F') (b : F) (hy : y * y = algebraMap F F' b) :
    ↥(quadLevel y b hy) :=
  ⟨⟨y, mem_maxAbelianSubext_of_sq y b hy⟩,
    IntermediateField.subset_adjoin F _ (Set.mem_singleton _)⟩

@[simp]
theorem quadRoot_coe (y : F') (b : F) (hy : y * y = algebraMap F F' b) :
    ((quadRoot y b hy : ↥(quadLevel y b hy)) : ↥(NK.LocalReciprocity.maxAbelianSubext F F')) =
      ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ := rfl

theorem quadRoot_mul_self (y : F') (b : F) (hy : y * y = algebraMap F F' b) :
    quadRoot y b hy * quadRoot y b hy = algebraMap F ↥(quadLevel y b hy) b :=
  Subtype.ext (quadLevel_coe_mul_self y b hy)



variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
variable [NeZero (2 : F)]

/-- **The quadratic level is trivial exactly when `b` is a square**: if `b = c²` with `c ∈ F`, then
`F(√b) = F`. -/
theorem quadLevel_eq_bot_of_isSquare (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    (hysq : ∃ c : F, c * c = b) :
    quadLevel y b hy = ⊥ := by
  obtain ⟨c, hc⟩ := hysq
  have hyc : (⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) *
        ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ =
      (algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) *
        (algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) := by
    rw [← map_mul, hc]
    exact quadLevel_coe_mul_self y b hy
  have hz : ((⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) -
        algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) *
      ((⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) +
        algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) = 0 := by
    have hsub : ((⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) -
        algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) *
      ((⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) +
        algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) =
        (⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
          ↥(NK.LocalReciprocity.maxAbelianSubext F F')) *
          ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ -
        (algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) *
          (algebraMap F ↥(NK.LocalReciprocity.maxAbelianSubext F F') c) := by
      ring
    rw [hsub, hyc, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · have hybot : (⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) ∈
        (⊥ : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F')) := by
      rw [IntermediateField.mem_bot]
      exact ⟨c, (sub_eq_zero.mp h).symm⟩
    exact le_antisymm (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hybot))
      bot_le
  · have hybot : (⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) ∈
        (⊥ : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F')) := by
      rw [IntermediateField.mem_bot]
      refine ⟨-c, ?_⟩
      rw [map_neg]
      exact (add_eq_zero_iff_eq_neg.mp h).symm
    exact le_antisymm (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hybot))
      bot_le

/-- **The norm group of a quadratic level determines the level** (the quadratic case of
`normGroup_injective`, the non-degeneracy of the `p = 2` Hilbert pairing in the level variable). -/
theorem normGroup_quadLevel_eq_iff (R : ReciprocityMap F F')
    (y y' : F') (b b' : F) (hy : y * y = algebraMap F F' b)
    (hy' : y' * y' = algebraMap F F' b') :
    NK.LocalReciprocity.normGroup F ↥(quadLevel y b hy) =
        NK.LocalReciprocity.normGroup F ↥(quadLevel y' b' hy') ↔
      quadLevel y b hy = quadLevel y' b' hy' := by
  haveI := quadLevel_finiteDimensional y b hy
  haveI := quadLevel_normal y b hy
  haveI := quadLevel_finiteDimensional y' b' hy'
  haveI := quadLevel_normal y' b' hy'
  exact ⟨fun h => normGroup_injective R _ _ h, fun h => by rw [h]⟩

/-- **The `p = 2` Hilbert pairing is non-degenerate in the second variable**: `(a,b) = 1` for every
`a : Fˣ` if and only if `b` is a square in `F`.

The direction `⟸` is formal (a square gives the trivial level); the direction `⟹` is the
non-degeneracy statement, proved from the reciprocity datum by
`index_normGroup_eq_finrank` + `quadLevel_eq_bot_of_isSquare`. -/
theorem hilbertSymbolAt_forall_eq_one_iff_isSquare (R : ReciprocityMap F F')
    (y : F') (b : F) (hy : y * y = algebraMap F F' b) :
    (∀ a : Fˣ, hilbertSymbolAt R y b hy a = 1) ↔ ∃ c : F, c * c = b := by
  constructor
  · intro h
    haveI := quadLevel_finiteDimensional y b hy
    haveI := quadLevel_normal y b hy
    have hN : NK.LocalReciprocity.normGroup F ↥(quadLevel y b hy) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro a
      rw [← hilbertSymbolAt_eq_one_iff R y b hy a]
      exact h a
    have hidx : (NK.LocalReciprocity.normGroup F ↥(quadLevel y b hy)).index = 1 := by
      rw [hN, Subgroup.index_top]
    have hfr : Module.finrank F ↥(quadLevel y b hy) = 1 := by
      rw [← index_normGroup_eq_finrank R (quadLevel y b hy), hidx]
    have hbot : quadLevel y b hy = ⊥ :=
      (IntermediateField.eq_of_le_of_finrank_le bot_le (by
        rw [hfr, IntermediateField.finrank_bot])).symm
    have hmem : (⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')) ∈
        (⊥ : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F')) := by
      rw [← hbot]
      exact IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
    refine ⟨c, ?_⟩
    have hcy : (algebraMap F F') c = y := by
      simpa using congrArg (Subtype.val) hc
    have h2 : (algebraMap F F') (c * c) = (algebraMap F F') b := by
      rw [map_mul, hcy, hy]
    exact (algebraMap F F').injective h2
  · rintro ⟨c, hc⟩
    haveI := quadLevel_finiteDimensional y b hy
    haveI := quadLevel_normal y b hy
    have hbot : quadLevel y b hy = ⊥ := quadLevel_eq_bot_of_isSquare y b hy ⟨c, hc⟩
    haveI : Subsingleton (↥(quadLevel y b hy) ≃ₐ[F] ↥(quadLevel y b hy)) := by
      rw [hbot]
      refine ⟨fun σ τ => AlgEquiv.ext fun x => ?_⟩
      obtain ⟨d, hd⟩ := IntermediateField.mem_bot.mp x.2
      have hxd : x = algebraMap F ↥(⊥ : IntermediateField F
          ↥(NK.LocalReciprocity.maxAbelianSubext F F')) d := Subtype.ext hd.symm
      calc σ x = σ (algebraMap F _ d) := by rw [hxd]
        _ = algebraMap F _ d := AlgEquiv.commutes σ d
        _ = τ (algebraMap F _ d) := (AlgEquiv.commutes τ d).symm
        _ = τ x := by rw [hxd]
    intro a
    rw [hilbertSymbolAt_apply, if_pos (Subsingleton.elim _ _)]

end Quadratic


end NK.NUV2.LC
