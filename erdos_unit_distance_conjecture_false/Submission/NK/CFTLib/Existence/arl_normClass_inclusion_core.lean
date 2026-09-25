import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.ARL.IdeleCongruenceLift
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.Existence.ideleInclusion_congruenceSubgroup
import Submission.NK.CFTLib.Existence.count_idealOf_ideleInclusion
import Submission.NK.CFTLib.Existence.artinSym_map_eq_one_of_unramified
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-! ## Two elementary group-theoretic lemmas -/

/-- A cyclic group is commutative. -/
theorem mul_comm_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm]

/-- The elementary cancellation `(x * a) * (x * b)⁻¹ = a * b⁻¹` in a commutative group. -/
theorem mul_mul_inv_eq' {G : Type*} [CommGroup G] (x a b : G) :
    (x * a) * (x * b)⁻¹ = a * b⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]
  rw [mul_comm x (a * (b⁻¹ * x⁻¹))]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-! ## The commutativity of `Gal(Ω/L)` from a cyclic complement -/

/-- If `Ω = L·M` with `M/K` cyclic, then `Gal(Ω/L) ≅ Gal(M/K)` is commutative. -/
theorem galComm_of_isCyclic_complement {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (L M : IntermediateField K Ω) [FiniteDimensional K ↥L] [FiniteDimensional K ↥M]
    [IsGalois K ↥M] [IsCyclic (↥M ≃ₐ[K] ↥M)]
    (hML : M ⊓ L = ⊥) (hsup : M ⊔ L = ⊤) :
    ∀ a b : Ω ≃ₐ[↥L] Ω, a * b = b * a := by
  have hml : L ⊓ M = ⊥ := by rw [inf_comm]; exact hML
  have hsp : L ⊔ M = ⊤ := by rw [sup_comm]; exact hsup
  have hinj : Function.Injective (NK.CFTLib.Arl.restrictGalEquiv (K := K) L M) :=
    NK.CFTLib.Arl.restrictGalEquiv_injective L M hml hsp
  intro a b
  refine hinj ?_
  rw [map_mul, map_mul]
  exact mul_comm_of_isCyclic _ _

/-! ## Adjustment independence of the Artin symbol -/

/-- The Artin symbol of the ideal attached to `x * (b)` does not depend on the adjustment
`b` with `x * (b) ∈ U`, as long as the Artin symbol of the principal ideal of every idèle of `U`
is trivial. -/
theorem artinSym_idealOf_congr {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) {U : Subgroup (𝕀[K])}
    (hU : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U) {x : 𝕀[K]} {b b' : Kˣ}
    (hb : x * Idele.principalIdele K b ∈ U) (hb' : x * Idele.principalIdele K b' ∈ U) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (Idele.idealOf (x * Idele.principalIdele K b))
      = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (Idele.idealOf (x * Idele.principalIdele K b')) := by
  classical
  have hmem : Idele.principalIdele K (b * b'⁻¹) ∈ U := by
    have h1 : (x * Idele.principalIdele K b) * (x * Idele.principalIdele K b')⁻¹ ∈ U :=
      U.mul_mem hb (U.inv_mem hb')
    have h2 : (x * Idele.principalIdele K b) * (x * Idele.principalIdele K b')⁻¹
        = Idele.principalIdele K (b * b'⁻¹) := by
      rw [map_mul, map_inv]
      rw [show (x * Idele.principalIdele K b) * (x * Idele.principalIdele K b')⁻¹
          = Idele.principalIdele K b * (Idele.principalIdele K b')⁻¹ from
        mul_mul_inv_eq' x _ _]
    rwa [h2] at h1
  have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b * b'⁻¹ : Kˣ) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
  have hid : Idele.idealOf (x * Idele.principalIdele K b)
      = Idele.idealOf (x * Idele.principalIdele K b')
        * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b * b'⁻¹ : Kˣ) : K) := by
    have hbval : (b : K) = (b' : K) * ((b * b'⁻¹ : Kˣ) : K) := by
      rw [← Units.val_mul]
      congr 1
      rw [← mul_assoc, mul_inv_cancel_comm]
    rw [Idele.idealOf_mul, Idele.idealOf_mul, Idele.idealOf_principalIdele,
      Idele.idealOf_principalIdele, hbval, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    ac_rfl
  rw [hid, NK.CFTLib.Arl.artinSym_mul hcomm (Idele.idealOf_ne_zero _) hsp,
    hU (b * b'⁻¹) hmem, mul_one]

/-- The value of the idèlic Artin map at any valid adjustment. -/
theorem ideleArtin_eq_artinSym {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) {U : Subgroup (𝕀[K])}
    (hU : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U)
    (hadj : ∀ x : 𝕀[K], ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U) (x : 𝕀[K]) {b : Kˣ}
    (hb : x * Idele.principalIdele K b ∈ U) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj x
      = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
          (Idele.idealOf (x * Idele.principalIdele K b)) := by
  rw [NK.CFTLib.Arl.ideleArtin]
  exact artinSym_idealOf_congr hcomm hU (NK.CFTLib.Arl.adjust_spec U hadj x) hb

/-! ## The transfer statement -/

/-- **The transfer statement.**  For a tower `K ≤ L ≤ Ω` with a cyclic complement `M/K` of degree
`[L : K]`, the inclusion `C_K → C_Ω` lands in the image of the norm subgroup `N_{Ω/L}C_Ω`. -/
theorem arl_normClass_inclusion_core (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (L M : IntermediateField K Ω) [FiniteDimensional K ↥L] [FiniteDimensional K ↥M]
    [NumberField ↥L] [NumberField ↥M]
    [IsGalois K ↥L] [IsGalois K ↥M] [IsCyclic (↥M ≃ₐ[K] ↥M)]
    (hML : M ⊓ L = ⊥) (hsup : M ⊔ L = ⊤)
    (hn : Module.finrank K ↥M = Module.finrank K ↥L)
    {u₀ : Place ↥L → Place K} {hu₀ : ∀ w, Place.LiesOver w (u₀ w)}
    {φ₀ : Idele K →* Idele ↥L}
    {hφ₀ : ∀ (x : Idele K) (w : Place ↥L),
      φ₀ x w = Place.localAlgebraMapUnits w (u₀ w) (hu₀ w) (x (u₀ w))}
    {u₂ : Place Ω → Place ↥L} {hu₂ : ∀ w, Place.LiesOver w (u₂ w)}
    {φ₂ : Idele ↥L →* Idele Ω}
    {hφ₂ : ∀ (x : Idele ↥L) (w : Place Ω),
      φ₂ x w = Place.localAlgebraMapUnits w (u₂ w) (hu₂ w) (x (u₂ w))}
    {ψ₂ : IdeleClassGroup ↥L →* IdeleClassGroup Ω}
    {hψ₂ : ∀ x : Idele ↥L, ψ₂ (IdeleClassGroup.mk ↥L x) = IdeleClassGroup.mk Ω (φ₂ x)}
    {u₁ : Place Ω → Place K} {hu₁ : ∀ w, Place.LiesOver w (u₁ w)}
    {φ₁ : Idele K →* Idele Ω}
    {hφ₁ : ∀ (x : Idele K) (w : Place Ω),
      φ₁ x w = Place.localAlgebraMapUnits w (u₁ w) (hu₁ w) (x (u₁ w))}
    {ψ₁ : IdeleClassGroup K →* IdeleClassGroup Ω}
    {hψ₁ : ∀ x : Idele K, ψ₁ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk Ω (φ₁ x)}
    (hcomp : ∀ x : Idele K, φ₁ x = φ₂ (φ₀ x)) :
    ∀ x : IdeleClassGroup K,
      ψ₁ x ∈ (Idele.normClassSubgroup ↥L Ω).map ψ₂ := by
  classical
  haveI : FiniteDimensional ↥L Ω := inferInstance
  haveI : IsGalois ↥L Ω := inferInstance
  have hcomm : ∀ a b : Ω ≃ₐ[↥L] Ω, a * b = b * a :=
    galComm_of_isCyclic_complement L M hML hsup
  -- ### the two reciprocity laws
  obtain ⟨m, hm, hram, hprinc⟩ := h ↥L Ω hcomm
  obtain ⟨m₂, hm₂, hramM, _hprincM⟩ := h K ↥M (fun a b => mul_comm_of_isCyclic a b)
  -- ### the enlarged modulus
  set m₀ : ℕ := m * m₂ with hm₀def
  have hm₀ : 0 < m₀ := Nat.mul_pos hm hm₂
  have hram₀ : ∀ 𝔮 : HeightOneSpectrum (𝓞 ↥L), (m₀ : 𝓞 ↥L) ∉ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 Ω) = 1 := by
    intro 𝔮 h𝔮
    refine hram 𝔮 (fun hmc => h𝔮 ?_)
    have hmem : (m : 𝓞 ↥L) * (m₂ : 𝓞 ↥L) ∈ 𝔮.asIdeal := Ideal.mul_mem_right _ 𝔮.asIdeal hmc
    simpa [m₀, Nat.cast_mul] using hmem
  have hramM₀ : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m₀ : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 ↥M) = 1 := by
    intro 𝔭 h𝔭
    refine hramM 𝔭 (fun hmc => h𝔭 ?_)
    have hmem : (m₂ : 𝓞 K) * (m : 𝓞 K) ∈ 𝔭.asIdeal := Ideal.mul_mem_right _ 𝔭.asIdeal hmc
    simpa [m₀, Nat.cast_mul, mul_comm] using hmem
  have hprinc₀ : NK.CFTLib.artinKillsPrincipal ↥L Ω m₀ :=
    NK.CFTLib.artinKillsPrincipal.mono hprinc (dvd_mul_right m m₂)
  -- ### congruence subgroups and adjustments
  have hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := ↥L) m₀
      (NK.CFTLib.Arl.congruenceSubgroup ↥L m₀) :=
    ⟨fun x => Iff.rfl, fun b => ⟨fun h => h, fun h => h⟩⟩
  have hadj : ∀ x : 𝕀[↥L], ∃ b : (↥L)ˣ,
      x * Idele.principalIdele ↥L b ∈ NK.CFTLib.Arl.congruenceSubgroup ↥L m₀ :=
    fun x => NK.CFTLib.ARL.exists_adjust_congruenceSubgroup ↥L m₀ hm₀ x
  have hUK : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m₀
      (NK.CFTLib.Arl.congruenceSubgroup K m₀) :=
    ⟨fun x => Iff.rfl, fun b => ⟨fun h => h, fun h => h⟩⟩
  have hadjK : ∀ x : 𝕀[K], ∃ b : Kˣ,
      x * Idele.principalIdele K b ∈ NK.CFTLib.Arl.congruenceSubgroup K m₀ :=
    fun x => NK.CFTLib.ARL.exists_adjust_congruenceSubgroup K m₀ hm₀ x
  -- ### the idèlic Artin map
  obtain ⟨art, hart, hart_prin, _hart_frob, hart_surj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := ↥L) (L := Ω) hcomm m₀ hm₀ hram₀ hprinc₀
      (NK.CFTLib.Arl.congruenceSubgroup ↥L m₀) hU hadj
  have hcrux : NK.CFTLib.Arl.Crux (K := ↥L) (L := Ω) hcomm
      (NK.CFTLib.Arl.congruenceSubgroup ↥L m₀) := fun b hb =>
    NK.CFTLib.Arl.artinSym_spanSingleton_eq_one (K := ↥L) (L := Ω) hcomm m₀ hm₀ hram₀ hprinc₀ b
      ((hU.2 b).mp hb).1 ((hU.2 b).mp hb).2
  -- ### the Artin map kills the norms
  have hadjN : ∀ y : 𝕀[Ω], ∃ d : Ωˣ,
      Idele.normIdeleHom ↥L Ω (y * Idele.principalIdele Ω d)
        ∈ NK.CFTLib.Arl.congruenceSubgroup ↥L m₀ := by
    intro y
    obtain ⟨d, hd⟩ := NK.CFTLib.ARL.exists_adjust_congruenceSubgroup Ω m₀ hm₀ y
    exact ⟨d, NK.CFTLib.Arl.normIdeleHom_mem_congruenceSubgroup m₀ hm₀ hd⟩
  have hkills : ∀ y : 𝕀[Ω], art (Idele.normIdeleHom ↥L Ω y) = 1 := by
    intro y
    rw [hart (Idele.normIdeleHom ↥L Ω y)]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcomm m₀ hm₀ hram₀ hprinc₀
      (NK.CFTLib.Arl.congruenceSubgroup ↥L m₀) hU hadj hadjN y
  -- ### descent to `C_L` and identification of the kernel
  have hker : Idele.principalSubgroup ↥L ≤ art.ker := by
    intro z hz
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hz
    exact MonoidHom.mem_ker.mpr (hart_prin a)
  let artbar : IdeleClassGroup ↥L →* Gal(Ω/↥L) := QuotientGroup.lift _ art hker
  have hartbar : ∀ y : 𝕀[↥L], artbar (IdeleClassGroup.mk ↥L y) = art y :=
    fun y => QuotientGroup.lift_mk' _ _ y
  have hN_le : Idele.normClassSubgroup ↥L Ω ≤ artbar.ker := by
    intro q hq
    rw [Idele.mem_normClassSubgroup] at hq
    obtain ⟨y, rfl⟩ := hq
    rw [MonoidHom.mem_ker]
    obtain ⟨y', rfl⟩ := IdeleClassGroup.mk_surjective Ω y
    rw [IdeleClassGroup.normClassHom_mk, hartbar]
    exact hkills y'
  have hartbar_surj : Function.Surjective artbar := by
    intro σ
    obtain ⟨y, hy⟩ := hart_surj σ
    exact ⟨IdeleClassGroup.mk ↥L y, by rw [hartbar, hy]⟩
  have hker_index : artbar.ker.index = Nat.card (Ω ≃ₐ[↥L] Ω) := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange artbar).toEquiv,
      MonoidHom.range_eq_top.mpr hartbar_surj,
      Nat.card_congr (Subgroup.topEquiv (G := Ω ≃ₐ[↥L] Ω)).toEquiv]
  have hcard1 : Nat.card (IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω)
      = Nat.card (Ω ≃ₐ[↥L] Ω) := by
    rw [← Subgroup.index_eq_card (Idele.normClassSubgroup ↥L Ω)]
    refine le_antisymm ?_ ?_
    · rw [IsGalois.card_aut_eq_finrank (F := ↥L) (E := Ω)]
      exact NK.GlobalCFTdeep.index_le_finrank_of_isGalois (K := ↥L) (L := Ω)
    · haveI : (Idele.normClassSubgroup ↥L Ω).FiniteIndex :=
        Subgroup.finiteIndex_iff.mpr
          (NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := ↥L) (L := Ω))
      rw [← hker_index]
      exact Subgroup.index_antitone hN_le
  have hN_eq_ker : Idele.normClassSubgroup ↥L Ω = artbar.ker := by
    let f : (IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω) →* Gal(Ω/↥L) :=
      QuotientGroup.lift _ artbar hN_le
    have hf_surj : Function.Surjective f := by
      intro σ
      obtain ⟨q, rfl⟩ := hartbar_surj σ
      exact ⟨QuotientGroup.mk' _ q, QuotientGroup.lift_mk' _ _ q⟩
    have hf_inj : Function.Injective f := by
      refine (MonoidHom.ker_eq_bot_iff f).mp ?_
      have hcardker : Nat.card ↥(f.ker) = 1 := by
        have h := f.ker.card_mul_index
        have hidx : f.ker.index = Nat.card (IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω) := by
          rw [Subgroup.index_eq_card,
            Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
            MonoidHom.range_eq_top.mpr hf_surj,
            Nat.card_congr (Subgroup.topEquiv (G := Ω ≃ₐ[↥L] Ω)).toEquiv, ← hcard1]
        rw [hidx] at h
        have hpos : 0 < Nat.card (IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω) := by
          rw [hcard1, IsGalois.card_aut_eq_finrank (F := ↥L) (E := Ω)]
          exact Module.finrank_pos
        exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, one_mul])
      exact Subgroup.eq_bot_of_card_eq _ hcardker
    refine le_antisymm hN_le ?_
    intro q hq
    have h1 : f (↑q : IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω) = 1 := by
      show (QuotientGroup.lift (Idele.normClassSubgroup ↥L Ω) artbar hN_le)
          (↑q : IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω) = 1
      rw [QuotientGroup.lift_mk' (Idele.normClassSubgroup ↥L Ω) hN_le q]
      exact MonoidHom.mem_ker.mp hq
    have h2 : (↑q : IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω) = 1 := by
      have h3 : f (↑q : IdeleClassGroup ↥L ⧸ Idele.normClassSubgroup ↥L Ω) = f 1 := by
        rw [h1, map_one]
      exact hf_inj h3
    exact (QuotientGroup.eq_one_iff q).mp h2
  -- ### the main argument
  intro x
  obtain ⟨xt, rfl⟩ := IdeleClassGroup.mk_surjective K x
  refine Subgroup.mem_map.mpr ⟨IdeleClassGroup.mk ↥L (φ₀ xt), ?_, ?_⟩
  · rw [hN_eq_ker]
    show artbar (IdeleClassGroup.mk ↥L (φ₀ xt)) = 1
    rw [hartbar]
    obtain ⟨bt, hbt⟩ := hadjK xt
    have hpb : φ₀ (xt * Idele.principalIdele K bt)
        = φ₀ xt * Idele.principalIdele ↥L (Units.map (algebraMap K ↥L).toMonoidHom bt) := by
      rw [map_mul,
        NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele u₀ hu₀ φ₀ hφ₀ bt]
    rw [hart (φ₀ xt)]
    rw [ideleArtin_eq_artinSym hcomm hcrux hadj (φ₀ xt)
      (b := Units.map (algebraMap K ↥L).toMonoidHom bt) ?_]
    · rw [← hpb]
      refine artinSym_map_eq_one_of_unramified (K := K) (E := Ω) L M
        (by rw [inf_comm]; exact hML) (by rw [sup_comm]; exact hsup) ?_ hcomm
        (Idele.idealOf (xt * Idele.principalIdele K bt))
        (Idele.idealOf (φ₀ (xt * Idele.principalIdele K bt))) ?_ ?_ ?_
      · intro σ
        have h₁ : Module.finrank K ↥L = Nat.card (↥M ≃ₐ[K] ↥M) :=
          hn.symm.trans (IsGalois.card_aut_eq_finrank K ↥M).symm
        rw [h₁, Nat.card_eq_fintype_card]
        exact pow_card_eq_one
      · intro 𝔮 𝔭 h𝔮
        exact count_idealOf_ideleInclusion u₀ hu₀ φ₀ hφ₀ _ 𝔭 𝔮 h𝔮
      · intro 𝔭 h𝔭 𝔔 h𝔔
        haveI : 𝔔.asIdeal.LiesOver 𝔭.asIdeal := h𝔔
        letI hMSA : MulSemiringAction (↥M ≃ₐ[K] ↥M) (𝓞 ↥M) :=
          IsIntegralClosure.MulSemiringAction (𝓞 K) K ↥M (𝓞 ↥M)
        haveI hGG : IsGaloisGroup (↥M ≃ₐ[K] ↥M) (𝓞 K) (𝓞 ↥M) :=
          IsGaloisGroup.of_isFractionRing (↥M ≃ₐ[K] ↥M) (𝓞 K) (𝓞 ↥M) K ↥M
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 ↥M)
          𝔭.asIdeal 𝔔.asIdeal (↥M ≃ₐ[K] ↥M)]
        exact hramM₀ 𝔭 (fun hmc =>
          h𝔭 (NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence hbt 𝔭 hmc))
      · intro 𝔭 h𝔭 𝔮 h𝔮 𝔔 h𝔔
        haveI h𝔮lies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal :=
          (Place.mem_primesOverFinite (K := K) (L := ↥L) (Q := 𝔭) (q := 𝔮)).mp h𝔮
        haveI : 𝔔.asIdeal.LiesOver 𝔮.asIdeal := h𝔔
        letI hMSA : MulSemiringAction (Ω ≃ₐ[↥L] Ω) (𝓞 Ω) :=
          IsIntegralClosure.MulSemiringAction (𝓞 ↥L) ↥L Ω (𝓞 Ω)
        haveI hGG : IsGaloisGroup (Ω ≃ₐ[↥L] Ω) (𝓞 ↥L) (𝓞 Ω) :=
          IsGaloisGroup.of_isFractionRing (Ω ≃ₐ[↥L] Ω) (𝓞 ↥L) (𝓞 Ω) ↥L Ω
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 ↥L) (B := 𝓞 Ω)
          𝔮.asIdeal 𝔔.asIdeal (Ω ≃ₐ[↥L] Ω)]
        refine hram₀ 𝔮 (fun hmc => h𝔭 ?_)
        have h2 : (m₀ : 𝓞 K) ∈ 𝔭.asIdeal :=
          (Ideal.mem_of_liesOver 𝔮.asIdeal 𝔭.asIdeal (m₀ : 𝓞 K)).mpr (by simpa using hmc)
        exact NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence hbt 𝔭 h2
    · rw [← hpb]
      exact NK.CFTLib.Existence.ideleInclusion_congruenceSubgroup u₀ hu₀ φ₀ hφ₀ m₀ _
        hbt

  · rw [hψ₂, hψ₁]
    exact congrArg (fun z => IdeleClassGroup.mk Ω z) (hcomp xt).symm

end NK.CFTLib.Existence
