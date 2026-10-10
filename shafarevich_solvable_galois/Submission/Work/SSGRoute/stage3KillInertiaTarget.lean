import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.Work.SSGRoute.exists_localTarget_of_splitting
import Submission.Work.SSGRoute.exists_openSubgroup_comap_le
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.step4_local_target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas -/

/-- The level projection `Γ_{τ+1} →* Γ_τ` is surjective. -/
theorem stage3_flowGroupProj_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowGroupProj p G m i j) := by
  intro γ
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) γ.left
  refine ⟨SemidirectProduct.mk (QuotientGroup.mk'
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y) γ.right, ?_⟩
  rw [flowGroupProj_mk, flowQuotientProj_mk]
  exact SemidirectProduct.ext hy rfl

/-- If `y ∈ H` and `↥H` is finite, then `y ^ Nat.card ↥H = 1`. -/
theorem stage3_pow_natCard_eq_one {X : Type*} [Group X] (H : Subgroup X) [Finite ↥H]
    (y : X) (hy : y ∈ H) : y ^ Nat.card ↥H = 1 := by
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  have h : (⟨y, hy⟩ : ↥H) ^ Nat.card ↥H = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  exact Subtype.ext_iff.mp h

/-- A lift of an element of finite exponent has finite exponent: `x ^ k` lies in the kernel
`flowEKer = E(m,τ)` of the level projection, which has exponent `p`. -/
theorem stage3_pow_mul_p_eq_one_of_flowGroupProj_eq (p : ℕ) (G : Type*) [Group G] {m i j : ℕ}
    (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) (y : flowGroup p G m i j)
    (hxy : flowGroupProj p G m i j x = y) (k : ℕ) (hy : y ^ k = 1) : x ^ (k * p) = 1 := by
  have hmem : x ^ k ∈ flowEKer p G m i j := by
    rw [flowEKer, MonoidHom.mem_ker, map_pow, hxy, hy]
  obtain ⟨v, hv⟩ := (show x ^ k ∈ (gradeInl p G m i j).range from by
    rw [← localTargetOfSplitting_flowEKer_eq_range_gradeInl]
    exact hmem)
  rw [pow_mul, ← hv]
  exact gradeInl_pow_p p G m i j v

/-- **A twisted homomorphism gives a `1`-cocycle.**  If `Ψ : D_A →* Γ_{τ+1}` is a homomorphism
with `gradeInl (α σ) · ψm σ = Ψ σ` for all `σ ∈ H`, then `α` is a `1`-cocycle on `H` for the
action through `restrict K`: this is the conjugation formula `gradeInl_conj`. -/
theorem stage3_isCocycleOn_of_twistHom (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (m i j : ℕ)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (hquot : ∀ σ : SSGRoute.GalQ,
      flowQuot p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 (ψm σ) = restrict K σ)
    (H : Subgroup SSGRoute.GalQ)
    (Ψ : ↥H →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (hα : ∀ σ : ↥H, gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α ↑σ)) * ψm ↑σ = Ψ σ) :
    SSGRoute.IsCocycleOn (restrict K) H α := by
  have key : ∀ (σ : SSGRoute.GalQ) (hσ : σ ∈ H),
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α σ)) = Ψ ⟨σ, hσ⟩ * (ψm σ)⁻¹ := by
    intro σ hσ
    rw [← hα ⟨σ, hσ⟩]
    group
  have hsmul : ∀ (g : K ≃ₐ[ℚ] K) (x : E p (K ≃ₐ[ℚ] K) m i j),
      Additive.toMul (g • x) = g • Additive.toMul x := fun g x => rfl
  intro g hg h hh
  apply Additive.toMul.injective
  apply gradeInl_injective p (K ≃ₐ[ℚ] K) m i j
  rw [toMul_add, hsmul, map_mul]
  rw [key (g * h) (H.mul_mem hg hh), key g hg,
    ← gradeInl_conj p K m i j ψm g (hquot g) (Additive.toMul (α h)), key h hh]
  rw [show (⟨g * h, H.mul_mem hg hh⟩ : ↥H) = ⟨g, hg⟩ * ⟨h, hh⟩ from Subtype.ext rfl,
    map_mul, map_mul]
  group

/-- **At the non-finite (trivial) place of `ℚ̄` the inertia is trivial.** -/
theorem stage3_isInertia_eq_one_of_not_isFinPlace (A : ValuationSubring SSGRoute.QBar)
    (hA : ¬ SSGRoute.IsFinPlace ℚ A) {σ : SSGRoute.GalQ} (hσ : SSGRoute.IsInertia ℚ A σ) :
    σ = 1 := by
  haveI hAlg : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  have hcomap : A.comap (algebraMap ℚ SSGRoute.QBar) = ⊤ := by
    by_contra h
    exact hA h
  have halg : Algebra.IsAlgebraic ℚ SSGRoute.QBar := inferInstance
  have htop : A = ⊤ :=
    Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A halg hcomap
  have htriv : ∀ y : SSGRoute.QBar, (⊤ : ValuationSubring SSGRoute.QBar).valuation y < 1 →
      y = 0 := by
    intro y hy
    by_contra hne
    have hunit : IsUnit (⟨y, ValuationSubring.mem_top y⟩ :
        ↥(⊤ : ValuationSubring SSGRoute.QBar)) := by
      refine ⟨⟨⟨y, ValuationSubring.mem_top y⟩, ⟨y⁻¹, ValuationSubring.mem_top _⟩, ?_, ?_⟩, rfl⟩
      · ext; simp [mul_inv_cancel₀ hne]
      · ext; simp [inv_mul_cancel₀ hne]
    exact (valuation_lt_one_iff_not_isUnit
      (⊤ : ValuationSubring SSGRoute.QBar) ⟨y, ValuationSubring.mem_top y⟩).mp hy hunit
  subst htop
  refine AlgEquiv.ext fun x => ?_
  by_contra hx
  have h1 : (⊤ : ValuationSubring SSGRoute.QBar).valuation (σ x - x) < 1 :=
    hσ.2 x (ValuationSubring.mem_top x)
  exact hx (sub_eq_zero.mp (htriv (σ x - x) h1))

/-! ## The local construction at a finite place -/

/-- **The "kill the inertia" local target at a finite place.** -/
theorem stage3_killInertia_of_isFinPlace (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m i j : ℕ}
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ, flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ) = φm σ)
    (hquot : ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2 (ψm σ) = restrict K σ)
    (hopen : IsOpen (ψm.ker : Set SSGRoute.GalQ))
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A)
    (hφ : ∀ σ ∈ SSGRoute.decomp ℚ A, SSGRoute.IsInertia ℚ A σ → φm σ = 1) :
    ∃ α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j,
      SSGRoute.IsCocycleOn (restrict K) (SSGRoute.decomp ℚ A) α ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) α ∧
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
        gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α σ)) = (ψm σ)⁻¹ := by
  classical
  set A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar := ⟨A, hA⟩ with hA'def
  set F : ↥(SSGRoute.decomp ℚ A) := SSGRoute.localFrobElem A' with hFdef
  -- (1) the factorisation of `φm|_D` through the unramified quotient `Ẑ`
  have hker_le : (SSGRoute.localZhatHom A').ker ≤
      (φm.comp (Subgroup.subtype (SSGRoute.decomp ℚ A))).ker := by
    rw [SSGRoute.localZhatHom_ker]
    refine (Subgroup.closure_le _).mpr ?_
    intro σ hσ
    exact MonoidHom.mem_ker.mpr (hφ (σ : SSGRoute.GalQ) σ.2 hσ)
  set φbar : NK.LocalAnabelian.Zhat →* flowGroup p (K ≃ₐ[ℚ] K) m i j :=
    (QuotientGroup.lift _ (φm.comp (Subgroup.subtype (SSGRoute.decomp ℚ A))) hker_le).comp
      (QuotientGroup.quotientKerEquivOfSurjective (SSGRoute.localZhatHom A')
        (SSGRoute.localZhatHom_surjective A')).symm.toMonoidHom with hφbardef
  have hφbar_apply : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      φbar (SSGRoute.localZhatHom A' σ) = φm ↑σ := by
    intro σ
    show QuotientGroup.lift _ (φm.comp (Subgroup.subtype (SSGRoute.decomp ℚ A))) hker_le
      ((QuotientGroup.quotientKerEquivOfSurjective (SSGRoute.localZhatHom A')
        (SSGRoute.localZhatHom_surjective A')).symm (SSGRoute.localZhatHom A' σ)) = φm ↑σ
    have he : (QuotientGroup.quotientKerEquivOfSurjective (SSGRoute.localZhatHom A')
        (SSGRoute.localZhatHom_surjective A'))
        (QuotientGroup.mk' (SSGRoute.localZhatHom A').ker σ) = SSGRoute.localZhatHom A' σ := by
      change QuotientGroup.kerLift (SSGRoute.localZhatHom A')
        (QuotientGroup.mk' (SSGRoute.localZhatHom A').ker σ) = SSGRoute.localZhatHom A' σ
      rw [QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk]
    rw [← he, MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk' _ _ σ
  have hφbar_gen : φbar NK.TowerRank.zhatGen = φm (F : SSGRoute.GalQ) := by
    rw [show NK.TowerRank.zhatGen = SSGRoute.localZhatHom A' F from
      (SSGRoute.localZhatHom_localFrobElem A').symm]
    exact hφbar_apply F
  -- (2) the exponent killing the image of `φm`
  have hopenφ : IsOpen (φm.ker : Set SSGRoute.GalQ) := by
    refine isOpen_subgroup_of_le_isOpen (φm.ker) hopen (Subgroup.one_mem _) ?_
    intro σ hσ
    exact MonoidHom.mem_ker.mpr (by rw [← hproj σ, MonoidHom.mem_ker.mp hσ, map_one])
  have hfinrange : Finite ↥(MonoidHom.range φm) :=
    finite_range_of_finiteIndex φm (finiteIndex_ker_of_isOpen φm hopenφ)
  haveI := hfinrange
  set mcard : ℕ := Nat.card ↥(MonoidHom.range φm) with hmcard
  haveI hne : Nonempty ↥(MonoidHom.range φm) :=
    ⟨⟨φm 1, MonoidHom.mem_range.mpr ⟨1, rfl⟩⟩⟩
  have hmcard_pos : 0 < mcard := by
    rw [hmcard]
    exact Nat.card_pos
  have hmcard_pow : (φm (F : SSGRoute.GalQ)) ^ mcard = 1 :=
    stage3_pow_natCard_eq_one (MonoidHom.range φm) _ (MonoidHom.mem_range.mpr ⟨F, rfl⟩)
  -- (3) a lift of the value at the Frobenius
  obtain ⟨x₀, hx₀⟩ := stage3_flowGroupProj_surjective p (K ≃ₐ[ℚ] K) m i j
    (φm (F : SSGRoute.GalQ))
  have hx₀_pow : x₀ ^ (mcard * p) = 1 :=
    stage3_pow_mul_p_eq_one_of_flowGroupProj_eq p (K ≃ₐ[ℚ] K) x₀ (φm (F : SSGRoute.GalQ))
      hx₀ mcard hmcard_pow
  have hd_pos : 0 < mcard * p := Nat.mul_pos hmcard_pos (Fact.out : p.Prime).pos
  have hd_ne : (mcard * p) ≠ 0 := hd_pos.ne'
  -- (4) the homomorphism `L : Ẑ →* Γ_{τ+1}` with `L zhatGen = x₀`, factoring through `ℤ ⧸ dℤ`
  have hkercond : (NK.TameStructure.ProCyclic.mZ (mcard * p) hd_ne).toSubgroup ≤
      (zpowersHom (flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2) x₀).ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hz' : Multiplicative.ofAdd z.toAdd ∈
        (NK.TameStructure.ProCyclic.mZ (mcard * p) hd_ne).toSubgroup := by
      rwa [ofAdd_toAdd]
    have hdiv : (((mcard * p : ℕ)) : ℤ) ∣ z.toAdd :=
      (NK.TameStructure.ProCyclic.mem_mZ (mcard * p) hd_ne z.toAdd).mp hz'
    obtain ⟨c, hc⟩ := hdiv
    rw [zpowersHom_apply, hc, zpow_mul]
    have h1 : x₀ ^ ((((mcard * p : ℕ)) : ℤ)) = 1 := by
      rw [zpow_natCast, hx₀_pow]
    rw [h1, one_zpow]
  set L : NK.LocalAnabelian.Zhat →*
      flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 :=
    (QuotientGroup.lift (NK.TameStructure.ProCyclic.mZ (mcard * p) hd_ne).toSubgroup
      (zpowersHom _ x₀) hkercond).comp
      (NK.TameStructure.ProCyclic.compHom (mcard * p) hd_ne) with hLdef
  have hL_gen : L NK.TowerRank.zhatGen = x₀ := by
    rw [hLdef, MonoidHom.comp_apply, compHom_zhatGen_eq (mcard * p) hd_ne,
      QuotientGroup.lift_mk', zpowersHom_apply, toAdd_ofAdd, zpow_one]
  have hL_ker : NK.TowerRank.powSubgroup (mcard * p) ≤ L.ker := by
    intro z hz
    rw [hLdef, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp (powSubgroup_le_ker_compHom (mcard * p) hd_ne hz), map_one]
  -- (5) `Ψ := flowGroupProj ∘ L` agrees with `φbar`
  set Ψ : NK.LocalAnabelian.Zhat →* flowGroup p (K ≃ₐ[ℚ] K) m i j :=
    (flowGroupProj p (K ≃ₐ[ℚ] K) m i j).comp L with hΨdef
  have hΨ_gen : Ψ NK.TowerRank.zhatGen = φbar NK.TowerRank.zhatGen := by
    rw [hΨdef, MonoidHom.comp_apply, hL_gen, hx₀, hφbar_gen]
  have hφbar_ker : NK.TowerRank.powSubgroup mcard ≤ φbar.ker := by
    intro z hz
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp
      (show z ∈ (NK.TowerRank.powHom mcard).range from hz)
    change φbar (w ^ mcard) = 1
    rw [map_pow]
    obtain ⟨σ, hσ⟩ := SSGRoute.localZhatHom_surjective A' w
    rw [← hσ, hφbar_apply σ]
    exact stage3_pow_natCard_eq_one (MonoidHom.range φm) (φm ↑σ)
      (MonoidHom.mem_range.mpr ⟨↑σ, rfl⟩)
  have hΨφbar : Ψ = φbar := by
    have hq : 0 < mcard * p * mcard := Nat.mul_pos hd_pos hmcard_pos
    have htop := zpowers_zhatGen_sup_powSubgroup (mcard * p * mcard) hq
    have hkerΨ : NK.TowerRank.powSubgroup (mcard * p * mcard) ≤ Ψ.ker := by
      intro z hz
      rw [hΨdef, MonoidHom.mem_ker, MonoidHom.comp_apply,
        MonoidHom.mem_ker.mp (hL_ker (powSubgroup_le_powSubgroup
          (dvd_mul_right (mcard * p) mcard) hz)), map_one]
    have hkerφbar : NK.TowerRank.powSubgroup (mcard * p * mcard) ≤ φbar.ker :=
      le_trans (powSubgroup_le_powSubgroup (dvd_mul_left mcard (mcard * p))) hφbar_ker
    refine MonoidHom.ext fun z => ?_
    have hz : z ∈ (⊤ : Subgroup NK.LocalAnabelian.Zhat) := Subgroup.mem_top z
    rw [← htop] at hz
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hz
    rw [← hab, map_mul, map_mul]
    congr 1
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [map_zpow, map_zpow, hΨ_gen]
    · rw [show Ψ b = 1 from MonoidHom.mem_ker.mp (hkerΨ hb),
        show φbar b = 1 from MonoidHom.mem_ker.mp (hkerφbar hb)]
  -- (6) the lift on the decomposition group
  set Ψ' : ↥(SSGRoute.decomp ℚ A) →*
      flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 :=
    L.comp (SSGRoute.localZhatHom A') with hΨ'def
  have hΨ'_proj : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      flowGroupProj p (K ≃ₐ[ℚ] K) m i j (Ψ' σ) = φm ↑σ := by
    intro σ
    change Ψ (SSGRoute.localZhatHom A' σ) = φm ↑σ
    rw [hΨφbar, hφbar_apply σ]
  have hmemE : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      Ψ' σ * (ψm ↑σ)⁻¹ ∈ flowEKer p (K ≃ₐ[ℚ] K) m i j := by
    intro σ
    rw [flowEKer, MonoidHom.mem_ker, map_mul, map_inv, hΨ'_proj σ, hproj ↑σ, mul_inv_cancel]
  have hchoice : ∀ σ : ↥(SSGRoute.decomp ℚ A), ∃ v : E p (K ≃ₐ[ℚ] K) m i j,
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul v) = Ψ' σ * (ψm ↑σ)⁻¹ := by
    intro σ
    obtain ⟨v, hv⟩ := (localTargetOfSplitting_mem_flowEKer_iff_exists_gradeInl
      p (K ≃ₐ[ℚ] K) m i j (Ψ' σ * (ψm ↑σ)⁻¹)).mp (hmemE σ)
    exact ⟨Additive.ofMul v, hv⟩
  let αD : ↥(SSGRoute.decomp ℚ A) → E p (K ≃ₐ[ℚ] K) m i j := fun σ => (hchoice σ).choose
  have hαD : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (αD σ)) = Ψ' σ * (ψm ↑σ)⁻¹ :=
    fun σ => (hchoice σ).choose_spec
  have hαD' : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (αD σ)) * ψm ↑σ = Ψ' σ := by
    intro σ
    rw [hαD σ]
    group
  let α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j :=
    fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0
  have hα_eq : ∀ (σ : SSGRoute.GalQ) (h : σ ∈ SSGRoute.decomp ℚ A), α σ = αD ⟨σ, h⟩ := by
    intro σ h
    show (if h' : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h'⟩ else 0) = αD ⟨σ, h⟩
    rw [dif_pos h]
  refine ⟨α, ?_, ?_, ?_⟩
  · exact stage3_isCocycleOn_of_twistHom p K m i j ψm hquot (SSGRoute.decomp ℚ A) Ψ' α
      (fun σ => by rw [hα_eq ↑σ σ.2]; exact hαD' σ)
  · -- local constancy
    have hpre : IsOpen ((Subgroup.comap (SSGRoute.localZhatHom A')
        (NK.TowerRank.powSubgroup (mcard * p)) : Subgroup ↥(SSGRoute.decomp ℚ A)) :
          Set ↥(SSGRoute.decomp ℚ A)) :=
      SSGRoute.localZhatHom_preimage_powSubgroup_isOpen A' (mcard * p) hd_pos
    obtain ⟨U₀, hU₀open, hU₀⟩ := exists_openSubgroup_comap_le (SSGRoute.decomp ℚ A)
      (Subgroup.comap (SSGRoute.localZhatHom A') (NK.TowerRank.powSubgroup (mcard * p))) hpre
    refine ⟨U₀ ⊓ ψm.ker, hU₀open.inter hopen, ?_⟩
    intro g hg u hu huH
    rw [Subgroup.mem_inf] at hu
    obtain ⟨hu₀, huψ⟩ := hu
    have hgu : g * u ∈ SSGRoute.decomp ℚ A := Subgroup.mul_mem _ hg huH
    rw [hα_eq (g * u) hgu, hα_eq g hg]
    apply Additive.toMul.injective
    apply gradeInl_injective p (K ≃ₐ[ℚ] K) m i j
    rw [hαD ⟨g * u, hgu⟩, hαD ⟨g, hg⟩]
    rw [show (⟨g * u, hgu⟩ : ↥(SSGRoute.decomp ℚ A)) = ⟨g, hg⟩ * ⟨u, huH⟩ from
      Subtype.ext rfl]
    rw [map_mul, Subgroup.coe_mul, map_mul]
    have hΨ'u : Ψ' ⟨u, huH⟩ = 1 := by
      rw [hΨ'def, MonoidHom.comp_apply]
      exact MonoidHom.mem_ker.mp (hL_ker (hU₀ (Subgroup.mem_comap.mpr hu₀)))
    rw [hΨ'u, MonoidHom.mem_ker.mp huψ]
    group
  · -- the values on the inertia
    intro σ hσ
    have hσD : σ ∈ SSGRoute.decomp ℚ A := hσ.1
    rw [hα_eq σ hσD, hαD ⟨σ, hσD⟩]
    have hΨ'I : Ψ' ⟨σ, hσD⟩ = 1 := by
      rw [hΨ'def, MonoidHom.comp_apply]
      have h1 : SSGRoute.localZhatHom A' ⟨σ, hσD⟩ = 1 := by
        rw [← MonoidHom.mem_ker, SSGRoute.localZhatHom_ker]
        exact Subgroup.subset_closure hσ
      rw [h1, map_one]
    rw [hΨ'I, one_mul]
/-- **The "kill the inertia" local target of Step 3 of Schmidt–Wingberg's Theorem 15.**

Let `ψm : G_ℚ →* Γ_{τ+1}(m)` be a lift of the level-`τ` map `φm` (`hproj`), continuous (`hopen`),
with `flowQuot ∘ ψm = res` (`hquot`).  Let `A` be a finite place whose inertia is contained in
`G_K` (`hu`) and which is **unramified in `N_m` over `K`** (`hφ`).  Then there is a `1`-cocycle
`α : G_ℚ → E(m,τ)` (for the action through `Gal(K/ℚ)`), locally constant on `D_A`, whose values on
the inertia are the *inverses* of those of `ψm`:

  `gradeInl (α σ) = (ψm σ)⁻¹`  for every `σ ∈ I_A`.

Consequently (by the naturality `flowGroupMap_gradeInl` of the graded piece under the rank change
`Φ`) the twist `flowTwistE p K n i j ε ((flowGroupMap Φ) ∘ ψm)` is **trivial on `I_A`** for
`ε σ = gradedMapLin Φ (α σ)`: the two factors cancel.  This is the local target which removes the
new ramification of `ψm` (the paper's `T³` mark "subtract the unramified part", at the places which
are unramified over `K` but where the level-`τ+1` field is tamely ramified).

**Proof.**  On `σ ∈ I_A` one has `φm σ = 1` by `hφ`, so `ψm σ ∈ ker(flowGroupProj) = flowEKer(m)`,
which is the injective image of `E(m,τ)` under `gradeInl`; define the prescribed values
`α σ := - v σ` where `gradeInl (v σ) = ψm σ`.  For `σ, τ ∈ I_A` the multiplicativity of `gradeInl`
and of `ψm` give `v (σ τ) = v σ + v τ`, so the prescribed values form an additive function on
`I_A`; and they are `D_A`-equivariant, `v (σ τ σ⁻¹) = (restrict K σ) • v τ`, because
`gradeInl_conj` identifies `ψm (σ τ σ⁻¹) = ψm σ · gradeInl (v τ) · (ψm σ)⁻¹` with
`gradeInl ((restrict K σ) • v τ)`.  Since `D_A/I_A ≅ Ẑ` has cohomological dimension `1`
(`Work.SSGRoute.localZhatHom`, `Work.SSGRoute.localZhatHom_ker`), the restriction map
`H¹(D_A, E(m,τ)) → H¹(I_A, E(m,τ))^{D_A}` is surjective (`hu` makes `I_A ⊆ G_K`, so
`E(m,τ)^{I_A} = E(m,τ)`), so the equivariant additive function on `I_A` extends to a `1`-cocycle
`α` on `D_A`; extending by `0` off `D_A` gives the required function.  (`α` is a genuine *continuous*
cocycle: take the same construction for the profinite `H¹`, and note that `H¹(D_A, E)` of the
*discrete* module `E` — with the whole group acting — is the same group, and that the extension is
obtained from the cocycle on the open normal `I_A`; the resulting `α` is locally constant on `D_A`
because `α` is constant on the cosets of an open subgroup refining `ψm.ker ∩ D_A`.) -/
theorem stage3KillInertiaTarget (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] {m i j : ℕ}
    (φm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ, Work.SSGRoute.flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ) = φm σ)
    (hquot : ∀ σ : SSGRoute.GalQ, Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2
        (ψm σ) = Work.SSGRoute.restrict K σ)
    (hopen : IsOpen (ψm.ker : Set SSGRoute.GalQ))
    (A : ValuationSubring SSGRoute.QBar)
    (hu : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup)
    (hφ : ∀ σ ∈ SSGRoute.decomp ℚ A, SSGRoute.IsInertia ℚ A σ → φm σ = 1) :
    ∃ α : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j,
      SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) α ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) α ∧
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
        gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α σ)) = (ψm σ)⁻¹ := by
  by_cases hA : SSGRoute.IsFinPlace ℚ A
  · exact stage3_killInertia_of_isFinPlace p K φm ψm hproj hquot hopen A hA hφ
  · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro g hg h hh
      simp
    · exact ⟨⊤, isOpen_univ, fun g hg u hu huH => rfl⟩
    · intro σ hσ
      have h1 : σ = 1 := stage3_isInertia_eq_one_of_not_isFinPlace A hA hσ
      subst h1
      simp

end Work.SSGRoute
