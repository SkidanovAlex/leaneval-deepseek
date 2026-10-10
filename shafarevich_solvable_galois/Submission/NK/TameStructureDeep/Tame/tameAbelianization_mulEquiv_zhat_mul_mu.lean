import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.TameStructureDeep.Tame.TameQuotientKummer
import Submission.NK.TameStructureDeep.Tame.closure_pow_mem_abelianization_ker
import Submission.NK.TameStructureDeep.Tame.mu_residueCard_sub_one
import Submission.NK.TameStructureDeep.Tame.natCard_quotient_fixingSubgroup_eq_finrank

open scoped Classical
open IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- The residue field cardinality `q = residueCard K 𝔭` of a `𝔭`-adic completion is at least `2`:
it is `p ^ f` with `p` prime and `f > 0`. -/
theorem one_lt_residueCard_adicCompletion :
    1 < NK.LocalStructure.residueCard K 𝔭 := by
  obtain ⟨f, hf, hqf⟩ := NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭
    (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭)
    (NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭)
  rw [hqf]
  exact Nat.one_lt_pow hf.ne' (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭).one_lt

/-- The residue characteristic `p` does not divide `q - 1`. -/
theorem not_dvd_residueCard_sub_one :
    ¬ (resCharAt 𝔭) ∣ NK.LocalStructure.residueCard K 𝔭 - 1 := by
  have hp := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hchar := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨f, hf, hqf⟩ := NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hchar
  intro hdiv
  have hdvdq : resCharAt 𝔭 ∣ NK.LocalStructure.residueCard K 𝔭 := by
    rw [hqf]
    exact dvd_pow_self _ hf.ne'
  have hone : resCharAt 𝔭 ∣ 1 := by
    have h := Nat.dvd_sub hdvdq hdiv
    have he : NK.LocalStructure.residueCard K 𝔭 - (NK.LocalStructure.residueCard K 𝔭 - 1) = 1 := by
      have hq1 : 1 ≤ NK.LocalStructure.residueCard K 𝔭 :=
        le_of_lt (one_lt_residueCard_adicCompletion 𝔭)
      omega
    rwa [he] at h
  exact hp.not_dvd_one hone

/-- `primeToPart 𝔭 (q - 1) = q - 1`: the prime-to-`p` part of `q - 1` is `q - 1` itself. -/
theorem primeToPart_residueCard_sub_one :
    primeToPart 𝔭 (NK.LocalStructure.residueCard K 𝔭 - 1) =
      NK.LocalStructure.residueCard K 𝔭 - 1 := by
  have hnot : ¬ (resCharAt 𝔭) ∣ NK.LocalStructure.residueCard K 𝔭 - 1 :=
    not_dvd_residueCard_sub_one 𝔭
  rw [primeToPart, Nat.factorization_eq_zero_of_not_dvd hnot, pow_zero, Nat.div_one]

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-- **The abelianised tame quotient at a place: `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`.**

This is the `abelianisation` field of `NK.TameStructureDeep.TameRamificationResidual`: the only
remaining unproved field of the local structure chapter.  It is a *group-theoretic* statement, not
local class field theory: everything below is already in this directory.

* `tameQuotient ≃* Gal(κ^{tr}/κ)`, so `tameAbelianization p = (G_κ/V_κ)^{ab} ≅ Gal(κ^{tr}/κ)^{ab}`
  (transport along `Abelianization.congr`/`MulEquiv`).
* `T = Gal(κ^{tr}/κ^{ur}) = I_κ/V_κ`, `G = Gal(κ^{tr}/κ)`, `G/T ≅ Gal(κ^{ur}/κ) ≅ Ẑ`.
  By `NK.TameStructureDeep.exists_frobenius_adicCompletion` there is `F` with
  `NK.LocalAnabelian.IsFrobeniusFor p q F`; its image in `G/T` is the generator `1 ∈ Ẑ`, and
  `G = ⟨F⟩ · T`, `⟨F⟩ ∩ T = 1`, so `G` is the semidirect product of the procyclic `⟨F⟩` by `T`.
* `Tame.isTameFrobeniusLift_correctedWildInertia` says conjugation by `F` on the tame inertia is
  the `q`-th power map: `F τ F⁻¹ = τ ^ q`.  Hence the commutators `[F, τ] = τ ^ (q-1)` generate
  the abstract commutator subgroup of `G`.
* The Kummer layer at `n = q - 1`: with `γ` a `(q-1)`-th root of `π` inside `κ^{tr}`, `powSpanSub`
  with `m = q-1` has fixed field `κ^{ur}(γ)`, and `finrank_adjoin_urCl` gives
  `[κ^{ur}(γ) : κ^{ur}] = q-1`, whence `T/⟨τ^{q-1}⟩ ≅ μ_{q-1}`.
* `F` acts trivially on `T/⟨τ^{q-1}⟩` because `q ≡ 1 mod (q-1)` and that quotient is annihilated by
  `q-1`; hence `G^{ab} = G/⟨τ^{q-1}⟩ ≅ ⟨F⟩ × (T/⟨τ^{q-1}⟩) ≅ Ẑ × μ_{q-1}`.
* `NK.LocalAnabelian.Zhat` is the model of `Ẑ`; `μ_{q-1} ≅ Multiplicative (ZMod (q-1))` via the
  cyclic group of order `q - 1`.

With this lemma, `Tame.tameRamificationResidual_of_abelianisation` closes the residual at every
place and the chapter's boundary `NK.TameStructureDeep.localStructureData_of` becomes
hypothesis-free. -/
theorem tameAbelianization_mulEquiv_zhat_mul_mu (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    Nonempty (NK.LocalTame.tameAbelianization (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ≃*
      (NK.LocalAnabelian.Zhat ×
        Multiplicative (ZMod (NK.LocalStructure.residueCard K 𝔭 - 1)))) := by
  classical
  have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hq2 : 1 < NK.LocalStructure.residueCard K 𝔭 := one_lt_residueCard_adicCompletion 𝔭
  have hpt : primeToPart 𝔭 (NK.LocalStructure.residueCard K 𝔭 - 1) =
      NK.LocalStructure.residueCard K 𝔭 - 1 := primeToPart_residueCard_sub_one 𝔭
  have hcop : Nat.Coprime (NK.LocalStructure.residueCard K 𝔭 - 1) (resCharAt 𝔭) := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_residueCard_sub_one 𝔭)
  obtain ⟨π, hπ⟩ := exists_isUniformizerAt 𝔭
  obtain ⟨F, hF⟩ := NK.TameStructureDeep.exists_frobenius_adicCompletion (K := K) (K' := K') 𝔭
  obtain ⟨γ, hγpow0, hγtr⟩ := exists_root_primeToPart (K' := K') 𝔭
    (m := NK.LocalStructure.residueCard K 𝔭 - 1) (by omega) hπ
  have hγpow : γ ^ (NK.LocalStructure.residueCard K 𝔭 - 1) =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
    rw [← hpt]; exact hγpow0
  have hπne : algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) ≠ 0 :=
    uniformizer_algebraMap_ne_zero 𝔭 hπ
  have hγne : γ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : NK.LocalStructure.residueCard K 𝔭 - 1 ≠ 0)] at hγpow
    exact hπne hγpow.symm
  -- ### the intermediate fields
  let L : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
  let M : IntermediateField (𝔭.adicCompletion K) K' :=
    L ⊔ IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')
  have hLM : L ≤ M := le_sup_left
  haveI hgalK : IsGalois (𝔭.adicCompletion K) K' := inferInstance
  haveI hgalL : IsGalois (𝔭.adicCompletion K) ↥L :=
    NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure (κ := 𝔭.adicCompletion K)
      (K' := K') (resCharAt 𝔭)
  haveI hnormalL : Normal (𝔭.adicCompletion K) ↥L := hgalL.to_normal
  -- ### the fixed field of `powSpanSub` at `m = q - 1`
  have hMfix : M.fixingSubgroup =
      NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) (π : 𝔭.adicCompletion K) ⊔ Subgroup.closure
        (Set.range fun x : ↥(Isub 𝔭 K') =>
          (x : Gal(K'/(𝔭.adicCompletion K))) ^ (NK.LocalStructure.residueCard K 𝔭 - 1)) := by
    have hclosed := isClosed_powSpanSub 𝔭 K' hπ (NK.LocalStructure.residueCard K 𝔭 - 1)
    have hff := fixedField_powSpanSub 𝔭 K' (m := NK.LocalStructure.residueCard K 𝔭 - 1)
      (by omega) hπ γ hγpow0 hγtr
    have hfix := InfiniteGalois.fixingSubgroup_fixedField (K := K')
      (show ClosedSubgroup (Gal(K'/(𝔭.adicCompletion K))) from
        ⟨powSpanSub 𝔭 K' π (NK.LocalStructure.residueCard K 𝔭 - 1), hclosed⟩)
    rw [hff] at hfix
    exact hfix
  -- ### the Kummer character `χ : G →* μ_{q-1}(K')`
  obtain ⟨hmu_card, hmu_fix⟩ := mu_residueCard_sub_one K 𝔭 (K' := K')
  haveI hne : NeZero (NK.LocalStructure.residueCard K 𝔭 - 1) := ⟨by omega⟩
  have hχpow : ∀ σ : Gal(K'/(𝔭.adicCompletion K)),
      (σ γ / γ) ^ (NK.LocalStructure.residueCard K 𝔭 - 1) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hγpow, AlgEquiv.commutes]
    exact div_self hπne
  let χ : Gal(K'/(𝔭.adicCompletion K)) →*
      ↥(rootsOfUnity (NK.LocalStructure.residueCard K 𝔭 - 1) K') :=
    MonoidHom.mk' (fun σ => rootsOfUnity.mkOfPowEq (σ γ / γ) (hχpow σ)) (by
      intro σ τ
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, rootsOfUnity.coe_mkOfPowEq,
        rootsOfUnity.coe_mkOfPowEq, rootsOfUnity.coe_mkOfPowEq]
      have hz : Units.mk0 (τ γ / γ) (div_ne_zero ((map_ne_zero τ).mpr hγne) hγne) ∈
          rootsOfUnity (NK.LocalStructure.residueCard K 𝔭 - 1) K' :=
        (mem_rootsOfUnity' _ _).mpr (hχpow τ)
      have hfix : σ (τ γ / γ) = τ γ / γ := hmu_fix σ _ hz
      calc (σ * τ) γ / γ = σ (τ γ) / γ := by rw [AlgEquiv.mul_apply]
        _ = σ ((τ γ / γ) * γ) / γ := by rw [div_mul_cancel₀ (τ γ) hγne]
        _ = ((τ γ / γ) * σ γ) / γ := by rw [map_mul, hfix]
        _ = (σ γ / γ) * (τ γ / γ) := by
              rw [div_mul_eq_mul_div, div_div, div_mul_div_comm, mul_comm (τ γ) (σ γ)])
  have hχ_coe : ∀ σ, ((χ σ : K'ˣ) : K') = σ γ / γ := by
    intro σ
    simpa only [χ, MonoidHom.mk'_apply] using rootsOfUnity.coe_mkOfPowEq (hχpow σ)
  have hχ_ker : χ.ker =
      (IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')).fixingSubgroup := by
    ext σ
    rw [MonoidHom.mem_ker, NK.LocalAnabelian.ResidueField.mem_fixingSubgroup_adjoin_singleton_iff]
    constructor
    · intro h
      have h' : ((χ σ : K'ˣ) : K') = 1 := by rw [h]; rfl
      rw [hχ_coe σ] at h'
      exact (div_eq_one_iff_eq hγne).mp h'
    · intro h
      apply Subtype.ext
      apply Units.ext
      rw [hχ_coe σ, h, div_self hγne]
      simp
  -- ### the restriction to `κ^{ur}`
  let ρ : Gal(K'/(𝔭.adicCompletion K)) →* Gal(↥L/(𝔭.adicCompletion K)) :=
    AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') ↥L
  have hρker : ρ.ker = Isub 𝔭 K' :=
    IntermediateField.restrictNormalHom_ker L
  have hρsurj : Function.Surjective ρ :=
    AlgEquiv.restrictNormalHom_surjective (F := 𝔭.adicCompletion K) (K₁ := ↥L) (E := K')
  -- ### the two structure isomorphisms
  obtain ⟨e₁⟩ := NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv (K := K) 𝔭 (K' := K')
  obtain ⟨e₂⟩ := NK.TameStructureDeep.Units.nonempty_mulEquiv_multiplicative_zmod_of_isCyclic
    ↥(rootsOfUnity (NK.LocalStructure.residueCard K 𝔭 - 1) K') (inferInstance) hmu_card
  -- ### the map `Ω`
  let Ω : Gal(K'/(𝔭.adicCompletion K)) →*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (NK.LocalStructure.residueCard K 𝔭 - 1))) :=
    MonoidHom.prod (e₁.toMonoidHom.comp ρ) (e₂.toMonoidHom.comp χ)
  -- ### `V_κ ≤ ker Ω`
  have hVle : NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K)
      (K' := K') (resCharAt 𝔭) (π : 𝔭.adicCompletion K) ≤ Ω.ker := by
    intro v hv
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one]
    constructor
    · have hv1 : ρ v = 1 := by
        rw [← MonoidHom.mem_ker, hρker]
        exact Vsub_le_Isub 𝔭 K' hv
      rw [MonoidHom.comp_apply, hv1, map_one]
    · have hv2 : χ v = 1 := by
        rw [← MonoidHom.mem_ker, hχ_ker,
          NK.LocalAnabelian.ResidueField.mem_fixingSubgroup_adjoin_singleton_iff]
        exact (IntermediateField.mem_fixingSubgroup_iff _ v).mp hv γ hγtr
      rw [MonoidHom.comp_apply, hv2, map_one]
  have hVeq : NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K)
      (K' := K') (resCharAt 𝔭) (π : 𝔭.adicCompletion K) =
      NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) :=
    (wildInertiaSubgroup_eq_correctedWildInertia 𝔭 hπ).symm
  -- ### the kernel of `Ω`
  have hkerΩ : Ω.ker = NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K)
        (K' := K') (resCharAt 𝔭) ⊔ Subgroup.closure
      (Set.range fun x : ↥(Isub 𝔭 K') =>
        (x : Gal(K'/(𝔭.adicCompletion K))) ^ (NK.LocalStructure.residueCard K 𝔭 - 1)) := by
    rw [← hVeq, ← hMfix]
    have h1 : (e₁.toMonoidHom.comp ρ).ker = L.fixingSubgroup := by
      have hh : (e₁.toMonoidHom.comp ρ).ker = ρ.ker := by
        ext σ
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact MulEquiv.map_eq_one_iff e₁
      rw [hh, hρker]
    have h2 : (e₂.toMonoidHom.comp χ).ker =
        (IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')).fixingSubgroup := by
      have hh : (e₂.toMonoidHom.comp χ).ker = χ.ker := by
        ext σ
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact MulEquiv.map_eq_one_iff e₂
      rw [hh, hχ_ker]
    rw [MonoidHom.ker_prod, h1, h2, ← IntermediateField.fixingSubgroup_sup]
  -- ### the finrank of the Kummer layer `κ^{ur}(γ)` over `κ^{ur}`
  have hext : IntermediateField.extendScalars hLM =
      (IntermediateField.adjoin ↥L ({γ} : Set K') : IntermediateField ↥L K') := by
    apply le_antisymm
    · rw [IntermediateField.extendScalars_le_iff]
      show L ⊔ IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K') ≤
        (IntermediateField.restrictScalars (𝔭.adicCompletion K)
          (IntermediateField.adjoin ↥L ({γ} : Set K')) : IntermediateField (𝔭.adicCompletion K) K')
      refine sup_le ?_ ?_
      · intro y hy
        exact (IntermediateField.mem_restrictScalars (𝔭.adicCompletion K)).mpr
          ((IntermediateField.adjoin ↥L ({γ} : Set K')).algebraMap_mem (⟨y, hy⟩ : ↥L))
      · rw [IntermediateField.adjoin_le_iff]
        intro y hy
        have hy' : y = γ := Set.mem_singleton_iff.mp hy
        rw [hy']
        exact (IntermediateField.mem_restrictScalars (𝔭.adicCompletion K)).mpr
          (IntermediateField.subset_adjoin ↥L ({γ} : Set K') (Set.mem_singleton γ))
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y = γ := Set.mem_singleton_iff.mp hy
      rw [hy']
      show γ ∈ (IntermediateField.extendScalars hLM : Set K')
      rw [IntermediateField.coe_extendScalars]
      exact (le_sup_right : (IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')) ≤
        (L ⊔ IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')))
        (IntermediateField.subset_adjoin (𝔭.adicCompletion K) ({γ} : Set K') (Set.mem_singleton γ))
  have hfr : Module.finrank ↥L (IntermediateField.extendScalars hLM) =
      NK.LocalStructure.residueCard K 𝔭 - 1 := by
    rw [hext]
    exact finrank_adjoin_urCl 𝔭 (by omega) hcop hπ hγpow
  have hker : (χ.comp (Isub 𝔭 K').subtype).ker =
      (M.fixingSubgroup).subgroupOf (Isub 𝔭 K') := by
    have hMfix' : M.fixingSubgroup = Isub 𝔭 K' ⊓
        (IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')).fixingSubgroup := by
      change (L ⊔ IntermediateField.adjoin (𝔭.adicCompletion K) ({γ} : Set K')).fixingSubgroup = _
      rw [IntermediateField.fixingSubgroup_sup]
    rw [hMfix', Subgroup.inf_subgroupOf_left]
    ext x
    rw [Subgroup.mem_subgroupOf, ← hχ_ker, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker]
    rfl
  -- ### the range of `χ` on the inertia
  have hχI : (χ.comp (Isub 𝔭 K').subtype).range = ⊤ := by
    have hcard : Nat.card (↥(Isub 𝔭 K') ⧸ (M.fixingSubgroup).subgroupOf (Isub 𝔭 K')) =
        NK.LocalStructure.residueCard K 𝔭 - 1 := by
      rw [natCard_quotient_fixingSubgroup_eq_finrank (F := 𝔭.adicCompletion K) (E := K') hLM]
      exact hfr
    have hrange : Nat.card ↥((χ.comp (Isub 𝔭 K').subtype).range) =
        NK.LocalStructure.residueCard K 𝔭 - 1 := by
      have he : Nat.card (↥(Isub 𝔭 K') ⧸ (χ.comp (Isub 𝔭 K').subtype).ker) =
          Nat.card ↥((χ.comp (Isub 𝔭 K').subtype).range) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
      rw [← he, hker]
      exact hcard
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hrange, hmu_card]
  -- ### surjectivity of `Ω`
  have hΩsurj : Function.Surjective Ω := by
    rintro ⟨z, b⟩
    obtain ⟨σ₀, hσ₀⟩ := hρsurj (e₁.symm z)
    have hz : e₁.toMonoidHom (ρ σ₀) = z := by
      rw [show e₁.toMonoidHom (ρ σ₀) = e₁ (ρ σ₀) from rfl, hσ₀, MulEquiv.apply_symm_apply]
    have hmem : e₂.symm ((e₂ (χ σ₀))⁻¹ * b) ∈ (χ.comp (Isub 𝔭 K').subtype).range := by
      rw [hχI]; exact Subgroup.mem_top _
    obtain ⟨ι, hι⟩ := hmem
    refine ⟨σ₀ * ι, ?_⟩
    have hρi : ρ (ι : Gal(K'/(𝔭.adicCompletion K))) = 1 := by
      rw [← MonoidHom.mem_ker, hρker]; exact ι.2
    have hχi : e₂.toMonoidHom (χ (ι : Gal(K'/(𝔭.adicCompletion K)))) =
        (e₂.toMonoidHom (χ σ₀))⁻¹ * b := by
      have h := congrArg e₂ hι
      simp only [MonoidHom.comp_apply, MulEquiv.apply_symm_apply] at h
      exact h
    have h1 : (e₁.toMonoidHom.comp ρ) (σ₀ * ι) = z := by
      simp only [MonoidHom.comp_apply, map_mul, hρi, map_one, mul_one, hz]
    have h2 : (e₂.toMonoidHom.comp χ) (σ₀ * ι) = b := by
      simp only [MonoidHom.comp_apply, map_mul, hχi, mul_inv_cancel_left]
    rw [MonoidHom.prod_apply, h1, h2]
  -- ### the composite `G ⧸ W → Abelianization (G ⧸ W)`
  have hIeq : (Isub 𝔭 K') = NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K)
      (K' := K') (resCharAt 𝔭) :=
    (NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
      (K' := K') (resCharAt 𝔭)).symm
  let W : Subgroup (Gal(K'/(𝔭.adicCompletion K))) :=
    NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
  have hVleW : W ≤ Ω.ker := by
    rw [show W = NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K)
      (K' := K') (resCharAt 𝔭) (π : 𝔭.adicCompletion K) from hVeq.symm]
    exact hVle
  have hkerW : Ω.ker = W ⊔ Subgroup.closure (Set.range fun x : ↥(Isub 𝔭 K') =>
      (x : Gal(K'/(𝔭.adicCompletion K))) ^ (NK.LocalStructure.residueCard K 𝔭 - 1)) :=
    hkerΩ
  let Ωbar : Gal(K'/(𝔭.adicCompletion K)) ⧸ W →*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (NK.LocalStructure.residueCard K 𝔭 - 1))) :=
    QuotientGroup.lift W Ω hVleW
  let Ψ : Gal(K'/(𝔭.adicCompletion K)) →* Abelianization (Gal(K'/(𝔭.adicCompletion K)) ⧸ W) :=
    Abelianization.of.comp (QuotientGroup.mk' W)
  have hΨsurj : Function.Surjective Ψ := by
    have hof : Function.Surjective (Abelianization.of : (Gal(K'/(𝔭.adicCompletion K)) ⧸ W) →
        Abelianization (Gal(K'/(𝔭.adicCompletion K)) ⧸ W)) := by
      intro x
      refine Quotient.inductionOn x ?_
      intro y
      exact ⟨y, rfl⟩
    exact hof.comp (QuotientGroup.mk'_surjective W)
  have hΦΨ : ∀ g, (Abelianization.lift Ωbar) (Ψ g) = Ω g := by
    intro g
    show (Abelianization.lift Ωbar) (Abelianization.of (QuotientGroup.mk' W g)) = Ω g
    rw [Abelianization.lift_apply_of]
    exact QuotientGroup.lift_mk' W hVleW g
  have hKsub : (W ⊔ Subgroup.closure (Set.range fun x : ↥(Isub 𝔭 K') =>
      (x : Gal(K'/(𝔭.adicCompletion K))) ^ (NK.LocalStructure.residueCard K 𝔭 - 1))) ≤
      Ψ.ker := by
    refine sup_le ?_ ?_
    · intro w hw
      exact MonoidHom.mem_ker.mpr (by
        show Abelianization.of (QuotientGroup.mk' W w) = 1
        rw [show QuotientGroup.mk' W w = 1 from (QuotientGroup.eq_one_iff w).mpr hw]
        exact map_one _)
    · rw [show Subgroup.closure (Set.range fun x : ↥(Isub 𝔭 K') =>
            (x : Gal(K'/(𝔭.adicCompletion K))) ^ (NK.LocalStructure.residueCard K 𝔭 - 1))
          = Subgroup.closure (Set.range fun x : ↥(NK.LocalAnabelian.inertiaSubgroup
              (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)) =>
            (x : Gal(K'/(𝔭.adicCompletion K))) ^ (NK.LocalStructure.residueCard K 𝔭 - 1))
        from by rw [hIeq]]
      exact closure_pow_mem_abelianization_ker K 𝔭 hπ hF
  have hΦbij : Function.Bijective (Abelianization.lift Ωbar) := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨y, rfl⟩ := hΨsurj x
      rw [hΦΨ y] at hx
      exact MonoidHom.mem_ker.mp
        (hKsub (by rw [← hkerW]; exact MonoidHom.mem_ker.mpr hx))
    · intro a
      obtain ⟨g, hg⟩ := hΩsurj a
      refine ⟨Abelianization.of (QuotientGroup.mk' W g), ?_⟩
      rw [show Abelianization.of (QuotientGroup.mk' W g) = Ψ g from rfl, hΦΨ g, hg]
  exact ⟨MulEquiv.ofBijective (Abelianization.lift Ωbar) hΦbij⟩

end

end NK.TameStructureDeep.Tame


