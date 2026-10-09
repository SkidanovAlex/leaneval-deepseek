import Mathlib
import Submission.NK.CFTLib.Existence.arl_normClass_inclusion_core
import Submission.NK.CFTLib.Existence.exists_ideleInclusion_data
import Submission.NK.CFTLib.Existence.res_subtype_eq_rep_fixedField
import Submission.NK.CFTLib.Existence.arl_groupData
import Submission.NK.GlobalCFT.H0Computation
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `arl_invariants_via_core` — the `H⁰` arithmetic input, proved from the transfer core

The statement is the arithmetic input of Route B:

  `(C_Ω)^{Gal(Ω/K)} ≤ range (norm of the restriction of `C_Ω` to `Nsub`)`.

It is proved **without** importing the modules `arl_dev` / `arl_kill` / `arl_invariants`, which
transitively import the consumer `rep_invariants_le_range_norm_of_auxiliary` of this statement (a
build cycle).  The only arithmetic input is the transfer (Verlagerung) statement
`NK.CFTLib.Existence.arl_normClass_inclusion_core`, which *is* importable.

The ingredient that lives in a cyclic module is `NK.CFTLib.Existence.invariant_isNorm` (the
`C_K ⊆ N_{Ω/L'}C_Ω` form of the arithmetic input); here it is replaced by
`invariant_isNorm_via_core`, derived from the transfer core.

`arl_normClass_inclusion_core_data` below is the transfer core with the unused argument
`u₁ : Place Ω → Place K`, its proof `hu₁ : ∀ w, Place.LiesOver w (u₁ w)` and the accompanying
local-component hypothesis `hφ₁` removed (the monoid hom `φ₁` itself is kept: it is determined by
`hcomp` from `φ₂` and `φ₀`).  The proof of `arl_normClass_inclusion_core` never mentions `u₁`,
`hu₁` or `hφ₁`, so the same proof applies verbatim.  In the present application the natural
candidate `u₁ := u₀ ∘ u₂` would require the transitivity of `Place.LiesOver` and the composition of
the local maps `localAlgebraMapUnits`, which is irrelevant to the statement — dropping the
arguments removes the need for that glue.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct Pointwise
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-! ## The transfer core with the unused place-map arguments removed -/

theorem arl_normClass_inclusion_core_data (h : NK.CFTLib.ArtinReciprocityIdeal)
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
    {φ₁ : Idele K →* Idele Ω}
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


/-! ## The `H⁰` input in the `C_{Ω^{Nsub}}` form -/

/-- **The arithmetic input of Route B, in the form `C_K`-fixed classes of `C_{Ω^{Nsub}}` are
norms.**  This is `NK.CFTLib.Existence.invariant_isNorm` (which lives in a module importing the
consumer of the present file) with its idèlic Artin-map computation replaced by the transfer core
`arl_normClass_inclusion_core_data`.

For the tower `K ≤ L' := Ω^{Nsub} ≤ Ω` with the cyclic complement `M' := Ω^{Msub}` of the same
degree, every class of `C_{L'}` fixed by `Gal(L'/K)` is a norm from `C_Ω`: the inclusion data of
`exists_ideleInclusion_data` identifies the invariants of `C_{L'}` with the image of `C_K`, and the
transfer core puts that image inside the image of the norm subgroup `N_{Ω/L'}C_Ω`, whence the
conclusion by injectivity of `C_{L'} → C_Ω`. -/
theorem invariant_isNorm_via_core (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] [Fintype Nsub]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    ∀ q : IdeleClassGroup ↥(IntermediateField.fixedField Nsub),
      (∀ τ : Gal(↥(IntermediateField.fixedField Nsub)/K), τ • q = q) →
      q ∈ Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω := by
  classical
  intro q hq
  haveI hgalL : IsGalois K ↥(IntermediateField.fixedField Nsub) :=
    IsGalois.of_fixedField_normal_subgroup Nsub
  haveI hgalM : IsGalois K ↥(IntermediateField.fixedField Msub) :=
    IsGalois.of_fixedField_normal_subgroup Msub
  haveI hfdL : FiniteDimensional K ↥(IntermediateField.fixedField Nsub) := inferInstance
  haveI hfdM : FiniteDimensional K ↥(IntermediateField.fixedField Msub) := inferInstance
  haveI hnumL : NumberField ↥(IntermediateField.fixedField Nsub) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  haveI hnumM : NumberField ↥(IntermediateField.fixedField Msub) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  haveI hcycM : IsCyclic (↥(IntermediateField.fixedField Msub) ≃ₐ[K]
      ↥(IntermediateField.fixedField Msub)) :=
    (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient Msub)).mp hcyc
  obtain ⟨-, -, ⟨eN⟩, ⟨eM⟩, -, hcardN, hcardM⟩ :=
    arl_groupData (K := K) (L := L) (Ω := Ω) Msub Nsub hN hM hcyc hdisj hsup
  have hMcard : Nat.card (↥(IntermediateField.fixedField Msub) ≃ₐ[K]
      ↥(IntermediateField.fixedField Msub)) = Nat.card Gal(L/K) :=
    (Nat.card_congr (IsGalois.normalAutEquivQuotient Msub).toEquiv).symm.trans
      ((Nat.card_congr eN.toEquiv).symm.trans hcardN)
  have hLcard : Nat.card (↥(IntermediateField.fixedField Nsub) ≃ₐ[K]
      ↥(IntermediateField.fixedField Nsub)) = Nat.card Gal(L/K) :=
    (Nat.card_congr (IsGalois.normalAutEquivQuotient Nsub).toEquiv).symm.trans
      ((Nat.card_congr eM.toEquiv).symm.trans hcardM)
  have hnM : Module.finrank K ↥(IntermediateField.fixedField Msub) = Nat.card Gal(L/K) := by
    rw [← IsGalois.card_aut_eq_finrank K ↥(IntermediateField.fixedField Msub)]
    exact hMcard
  have hnL : Module.finrank K ↥(IntermediateField.fixedField Nsub) = Nat.card Gal(L/K) := by
    rw [← IsGalois.card_aut_eq_finrank K ↥(IntermediateField.fixedField Nsub)]
    exact hLcard
  have hn : Module.finrank K ↥(IntermediateField.fixedField Msub)
      = Module.finrank K ↥(IntermediateField.fixedField Nsub) := hnM.trans hnL.symm
  obtain ⟨u₀, hu₀, φ₀, ι, u₂, hu₂, φ₂, ψ₂, φ₁, ψ₁, hφ₀, hι, hφ₂, hψ₂, hcomp, hψ₁⟩ :=
    exists_ideleInclusion_data (K := K) (Ω := Ω) (IntermediateField.fixedField Nsub)
  have hcore : ∀ x : IdeleClassGroup K,
      ψ₁ x ∈ (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).map ψ₂ :=
    fun x => arl_normClass_inclusion_core_data (h := h)
      (IntermediateField.fixedField Nsub) (IntermediateField.fixedField Msub)
      hdisj hsup hn (u₀ := u₀) (hu₀ := hu₀) (φ₀ := φ₀) (hφ₀ := hφ₀)
      (u₂ := u₂) (hu₂ := hu₂) (φ₂ := φ₂) (hφ₂ := hφ₂) (ψ₂ := ψ₂) (hψ₂ := hψ₂)
      (φ₁ := φ₁) (ψ₁ := ψ₁) (hψ₁ := hψ₁) (hcomp := hcomp) x
  obtain ⟨x, hx⟩ := (NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
    (K := K) (L := ↥(IntermediateField.fixedField Nsub)) u₀ hu₀ φ₀ hφ₀ ι hι q).mp hq
  obtain ⟨xt, rfl⟩ := IdeleClassGroup.mk_surjective K x
  have hψ₂q : ψ₂ q = ψ₁ (IdeleClassGroup.mk K xt) := by
    rw [← hx, hψ₁ xt, hι xt, hψ₂ (φ₀ xt), hcomp xt]
  have hmem : ψ₂ q ∈ (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).map ψ₂ := by
    rw [hψ₂q]
    exact hcore (IdeleClassGroup.mk K xt)
  obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp hmem
  have hyq' : y = q :=
    (NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
      (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) u₂ hu₂ φ₂ hφ₂ ψ₂ hψ₂) hyq
  rw [hyq'] at hy
  exact hy


/-! ## The main statement -/

theorem arl_invariants_via_core (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] [Fintype Nsub]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ.invariants ≤
      LinearMap.range ((Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ.norm) := by
  classical
  haveI : IsGalois K ↥(IntermediateField.fixedField Nsub) :=
    IsGalois.of_fixedField_normal_subgroup Nsub
  haveI : FiniteDimensional K ↥(IntermediateField.fixedField Nsub) := inferInstance
  haveI : IsGalois ↥(IntermediateField.fixedField Nsub) Ω := inferInstance
  haveI : FiniteDimensional ↥(IntermediateField.fixedField Nsub) Ω := inferInstance
  obtain ⟨hsupMN, -, -, -, -, -, -⟩ :=
    arl_groupData (K := K) (L := L) (Ω := Ω) Msub Nsub hN hM hcyc hdisj hsup
  intro v hv
  obtain ⟨q, rfl⟩ : ∃ q : NK.GlobalCFT.IdeleClassGroup Ω, Additive.ofMul q = v :=
    ⟨Additive.toMul v, rfl⟩
  have hqm : ∀ σ : Gal(Ω/K), σ • q = q :=
    (NK.GlobalCFT.Cohomology.mem_rep_invariants_iff (K := K) (L := Ω)).mp hv
  have hqN : ∀ σ : ↥Nsub, σ.1 • q = q := fun σ => hqm σ.1
  have hqF : ∀ τ : Ω ≃ₐ[↥(IntermediateField.fixedField Nsub)] Ω, τ • q = q :=
    (NK.HassePrinciple.forall_smul_eq_self_subgroup_iff Nsub q).mp hqN
  -- the inclusion `C_{Ω^{Nsub}} →* C_Ω` and its properties
  let u : NK.GlobalCFT.Place Ω →
      NK.GlobalCFT.Place ↥(IntermediateField.fixedField Nsub) :=
    fun w => Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
      (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) w)
  have hu : ∀ w : NK.GlobalCFT.Place Ω, NK.GlobalCFT.Place.LiesOver w (u w) :=
    fun w => Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
      (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) w)
  obtain ⟨φΩ, hφΩ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
    (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) u hu
  obtain ⟨ψ, hψ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
    (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) u hu φΩ hφΩ
  have hψinj : Function.Injective ψ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
      (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) u hu φΩ hφΩ ψ hψ
  have hψrange : ∀ r : NK.GlobalCFT.IdeleClassGroup Ω,
      (∀ τ : Ω ≃ₐ[↥(IntermediateField.fixedField Nsub)] Ω, τ • r = r) ↔ r ∈ ψ.range :=
    fun r => NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
      (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) u hu φΩ hφΩ ψ hψ r
  have hψnorm : ∀ r : NK.GlobalCFT.IdeleClassGroup Ω,
      ψ (NK.GlobalCFT.IdeleClassGroup.normClassHom ↥(IntermediateField.fixedField Nsub) Ω r) =
        ∏ σ : Ω ≃ₐ[↥(IntermediateField.fixedField Nsub)] Ω, σ • r :=
    fun r => NK.GlobalCFT.globalCFT_normClassHom_eq_prod_smul
      (K := ↥(IntermediateField.fixedField Nsub)) (L := Ω) u hu φΩ hφΩ ψ hψ r
  obtain ⟨q', hq'⟩ := (hψrange q).mp hqF
  -- the inclusion is equivariant for `Gal(Ω/K)`
  have hψeq : ∀ (m : Gal(Ω/K)) (y : NK.GlobalCFT.IdeleClassGroup
      ↥(IntermediateField.fixedField Nsub)),
      m • ψ y = ψ ((IsGalois.normalAutEquivQuotient Nsub)
        (QuotientGroup.mk' Nsub m) • y) := by
    intro m y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y
    rw [← hx]
    change m • ψ (NK.GlobalCFT.IdeleClassGroup.mk
        ↥(IntermediateField.fixedField Nsub) x) =
      ψ ((IsGalois.normalAutEquivQuotient Nsub) (QuotientGroup.mk' Nsub m) •
        (NK.GlobalCFT.IdeleClassGroup.mk ↥(IntermediateField.fixedField Nsub) x))
    rw [hψ x]
    rw [show m • NK.GlobalCFT.IdeleClassGroup.mk Ω (φΩ x) =
        NK.GlobalCFT.IdeleClassGroup.mk Ω (m • φΩ x) from
      NK.GlobalCFT.IdeleClassGroup.smul_mk m (φΩ x)]
    rw [show (IsGalois.normalAutEquivQuotient Nsub) (QuotientGroup.mk' Nsub m) •
        NK.GlobalCFT.IdeleClassGroup.mk ↥(IntermediateField.fixedField Nsub) x =
        NK.GlobalCFT.IdeleClassGroup.mk ↥(IntermediateField.fixedField Nsub)
          ((IsGalois.normalAutEquivQuotient Nsub) (QuotientGroup.mk' Nsub m) • x) from
      NK.GlobalCFT.IdeleClassGroup.smul_mk _ x]
    rw [hψ]
    congr 1
    rw [show (IsGalois.normalAutEquivQuotient Nsub) (QuotientGroup.mk' Nsub m) =
        AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField Nsub) m from
      IsGalois.normalAutEquivQuotient_apply Nsub m]
    exact NK.HassePrinciple.ideleInclusion_smul_restrict u hu φΩ hφΩ m x
  -- `q'` is fixed by `Gal(Ω^{Nsub}/K)`, because `Msub → Gal(Ω^{Nsub}/K)` is surjective
  have hq'inv : ∀ τ : Gal(↥(IntermediateField.fixedField Nsub)/K), τ • q' = q' := by
    intro τ
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective Nsub
      ((IsGalois.normalAutEquivQuotient Nsub).symm τ)
    have hσmem : σ ∈ (Msub : Set (Gal(Ω/K))) * (Nsub : Set (Gal(Ω/K))) := by
      rw [← Subgroup.mul_normal Msub Nsub, hsupMN]
      exact Subgroup.mem_top σ
    obtain ⟨m, hm, n, hn, hmn⟩ := Set.mem_mul.mp hσmem
    have hτm : (IsGalois.normalAutEquivQuotient Nsub) (QuotientGroup.mk' Nsub m) = τ := by
      have hcoset : QuotientGroup.mk' Nsub m = QuotientGroup.mk' Nsub σ := by
        rw [← hmn, map_mul, show QuotientGroup.mk' Nsub n = 1 from
          (QuotientGroup.eq_one_iff (x := n)).mpr hn, mul_one]
      rw [hcoset, hσ, MulEquiv.apply_symm_apply]
    have h1 : ψ (τ • q') = m • ψ q' := by
      rw [← hτm]
      exact (hψeq m q').symm
    refine hψinj ?_
    rw [h1, hq', hqm m]
  -- hence `q'` is a norm from `C_Ω`
  have hq'norm : q' ∈ NK.GlobalCFT.Idele.normClassSubgroup
      ↥(IntermediateField.fixedField Nsub) Ω :=
    invariant_isNorm_via_core h Msub Nsub hN hM hcyc hdisj hsup q' hq'inv
  obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normClassSubgroup.mp hq'norm
  have key : ((NK.GlobalCFT.IdeleClassGroup.rep
        ↥(IntermediateField.fixedField Nsub) Ω).ρ.norm) (Additive.ofMul y)
      = Additive.ofMul q := by
    rw [NK.GlobalCFT.Cohomology.rep_norm_ofMul, ← hψnorm y, hy, hq']
  exact ⟨Additive.ofMul y,
    (LinearMap.congr_fun (res_subtype_eq_rep_fixedField Nsub).2 (Additive.ofMul y)).trans key⟩

end NK.CFTLib.Existence
