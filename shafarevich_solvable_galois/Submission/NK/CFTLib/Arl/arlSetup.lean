import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.Existence.arl_dev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois-theoretic setup and the arithmetic core of `NK.CFTLib.Arl.arl_invariants`

This file collects the two ingredients of the proof of `NK.CFTLib.Arl.arl_invariants`:

* `NK.CFTLib.Arl.galoisSetup_of_subgroups`: the Galois-theoretic bookkeeping for a
  complementary pair of normal subgroups `Msub, Nsub ⊴ Gal(Ω/K)` with `Msub ⊔ Nsub = ⊤`,
  `Msub ⊓ Nsub = ⊥`, `|Nsub| = |Msub|`, `Nsub` cyclic.
* `NK.CFTLib.Arl.exists_art_kills_congruence`: the existence of a modulus `M`, an idèle
  inclusion `φ : 𝕀 K → 𝕀 L` (`L = Ω^Nsub`) and an idèlic Artin map `art : 𝕀 L → Gal(Ω/L)`
  (built from the ideal-theoretic reciprocity law) which kills the principal idèles, kills the
  norms from `Ω`, is surjective, and kills `φ(𝕀 K)`.

The second statement is the Verlagerung/transfer input; the constructive content is the
computation `art (φ x) = artinSym (idealOf (φ x)) = ∏_{𝔭} (∏_{𝔮 | 𝔭} Frob_𝔮^{e(𝔮|𝔭)})^{v_𝔭(x)} = 1`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NumberField Pointwise nonZeroDivisors
open NumberField IntermediateField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.GlobalCFT

/-- **The Galois-theoretic setup of the auxiliary tower from the subgroup data.** -/
theorem galoisSetup_of_subgroups {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hMN : Msub ⊔ Nsub = ⊤) (hdisj : Msub ⊓ Nsub = ⊥)
    (hcard : Nat.card ↥Nsub = Nat.card ↥Msub) (hcyc : IsCyclic ↥Nsub) :
    (IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥) ∧
    (IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) ∧
    (Module.finrank K ↥(IntermediateField.fixedField Nsub) = Nat.card (Gal(Ω/K) ⧸ Nsub)) ∧
    (Nat.card (Gal(Ω/↥(IntermediateField.fixedField Nsub))) = Nat.card (Gal(Ω/K) ⧸ Msub)) ∧
    (Nat.card (Gal(↥(IntermediateField.fixedField Msub)/K)) = Nat.card (Gal(Ω/K) ⧸ Msub)) ∧
    (Nat.card ↥Nsub = Nat.card (Gal(Ω/K) ⧸ Msub)) ∧
    (Nat.card ↥Msub = Nat.card (Gal(Ω/K) ⧸ Nsub)) ∧
    (∀ σ : Gal(↥(IntermediateField.fixedField Msub)/K),
      σ ^ Module.finrank K ↥(IntermediateField.fixedField Nsub) = 1) ∧
    (IsMulCommutative Gal(↥(IntermediateField.fixedField Msub)/K)) ∧
    (IsCyclic (Gal(Ω/↥(IntermediateField.fixedField Nsub))) ∧
      (∀ a b : Gal(Ω/↥(IntermediateField.fixedField Nsub)), a * b = b * a)) := by
  classical
  have hdisj' : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥ := by
    rw [← NK.CFTLib.Existence.fixedField_sup_eq Msub Nsub, hMN, IsGalois.fixedField_top]
  have hsup' : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤ := by
    rw [← NK.CFTLib.Existence.fixedField_inf_eq Msub Nsub, hdisj,
      IntermediateField.fixedField_bot]
  have hcardN : Nat.card ↥Nsub = Nat.card (Gal(Ω/K) ⧸ Msub) :=
    NK.CFTLib.Existence.card_nsub_eq_card_quotient Msub Nsub hdisj' hsup'
  have hcardM : Nat.card ↥Msub = Nat.card (Gal(Ω/K) ⧸ Nsub) :=
    NK.CFTLib.Existence.card_nsub_eq_card_quotient Nsub Msub
      (by rw [inf_comm]; exact hdisj') (by rw [sup_comm]; exact hsup')
  have hgalMid : Nat.card (Gal(↥(IntermediateField.fixedField Msub)/K)) =
      Nat.card (Gal(Ω/K) ⧸ Msub) :=
    (Nat.card_congr (IsGalois.normalAutEquivQuotient Msub).toEquiv).symm
  have hgalL : Nat.card (Gal(Ω/↥(IntermediateField.fixedField Nsub))) =
      Nat.card (Gal(Ω/K) ⧸ Msub) := by
    obtain ⟨e⟩ := galois_fixedField_equiv (K := K) (Ω := Ω) Nsub
    rw [Nat.card_congr e.toEquiv, hcardN]
  have hfrL : Module.finrank K ↥(IntermediateField.fixedField Nsub) =
      Nat.card (Gal(Ω/K) ⧸ Nsub) := by
    rw [← IsGalois.card_aut_eq_finrank K ↥(IntermediateField.fixedField Nsub)]
    exact (Nat.card_congr (IsGalois.normalAutEquivQuotient Nsub).toEquiv).symm
  have hexp : ∀ σ : Gal(↥(IntermediateField.fixedField Msub)/K),
      σ ^ Module.finrank K ↥(IntermediateField.fixedField Nsub) = 1 := by
    intro σ
    have h1 : Module.finrank K ↥(IntermediateField.fixedField Nsub) =
        Nat.card (Gal(↥(IntermediateField.fixedField Msub)/K)) := by
      rw [hfrL, hgalMid, ← hcardM, ← hcard, hcardN]
    rw [h1]
    exact pow_card_eq_one'
  have hcommMid : IsMulCommutative Gal(↥(IntermediateField.fixedField Msub)/K) := by
    haveI hcycQ : IsCyclic (Gal(Ω/K) ⧸ Msub) :=
      (MulEquiv.isCyclic (NK.CFTLib.Existence.mulEquivQuotientOfDisjoint Msub Nsub
        hMN hdisj)).mp hcyc
    haveI : IsCyclic Gal(↥(IntermediateField.fixedField Msub)/K) :=
      (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient Msub)).mp hcycQ
    exact IsCyclic.isMulCommutative
  have hcycL : IsCyclic (Gal(Ω/↥(IntermediateField.fixedField Nsub))) := by
    obtain ⟨e⟩ := galois_fixedField_equiv (K := K) (Ω := Ω) Nsub
    exact (MulEquiv.isCyclic e).mpr hcyc
  exact ⟨hdisj', hsup', hfrL, hgalL, hgalMid, hcardN, hcardM, hexp, hcommMid, hcycL,
    (fun a b => mul_comm' a b)⟩

/-- **The arithmetic core: the idèlic Artin map of the middle level kills the idèle inclusion.**

There are a modulus `M > 0`, a choice `u` of places of `K` below the places of `L = Ω^Nsub`,
the associated idèle inclusion `φ : 𝕀 K →* 𝕀 L`, and an idèlic Artin map
`art : 𝕀 L →* Gal(Ω/L)` (built from the ideal-theoretic reciprocity law `h` at the extension
`Ω/L`) such that `art` kills the principal idèles of `L`, kills the norms from `Ω`, is surjective,
and kills `φ x` for every `x` in the congruence subgroup `U_K(M)`. -/
theorem exists_art_kills_congruence (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hMN : Msub ⊔ Nsub = ⊤) (hdisj : Msub ⊓ Nsub = ⊥)
    (hcard : Nat.card ↥Nsub = Nat.card ↥Msub) (hcyc : IsCyclic ↥Nsub) :
    ∃ (M : ℕ) (_ : 0 < M) (u : NK.GlobalCFT.Place ↥(IntermediateField.fixedField Nsub) →
        NK.GlobalCFT.Place K)
      (hu : ∀ w : NK.GlobalCFT.Place ↥(IntermediateField.fixedField Nsub),
        NK.GlobalCFT.Place.LiesOver w (u w))
      (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele ↥(IntermediateField.fixedField Nsub))
      (_ : ∀ (x : NK.GlobalCFT.Idele K)
        (w : NK.GlobalCFT.Place ↥(IntermediateField.fixedField Nsub)),
        φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
      (art : NK.GlobalCFT.Idele ↥(IntermediateField.fixedField Nsub) →*
        Gal(Ω/↥(IntermediateField.fixedField Nsub))),
      (∀ c : (↥(IntermediateField.fixedField Nsub))ˣ,
        art (NK.GlobalCFT.Idele.principalIdele _ c) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele Ω,
        art (NK.GlobalCFT.Idele.normIdeleHom ↥(IntermediateField.fixedField Nsub) Ω y) = 1) ∧
      Function.Surjective art ∧
      (∀ x : NK.GlobalCFT.Idele K, x ∈ NK.CFTLib.Arl.congruenceSubgroup K M →
        art (φ x) = 1) := by
  classical
  obtain ⟨hdisj', hsup', hfrL, hgalL, hgalMid, hcardN, hcardM, hexp, hcommMid, hcycL,
    hcommL⟩ := galoisSetup_of_subgroups Msub Nsub hMN hdisj hcard hcyc
  set L : IntermediateField K Ω := IntermediateField.fixedField Nsub with hLdef
  set Mid : IntermediateField K Ω := IntermediateField.fixedField Msub with hMiddef
  haveI hgalKL : IsGalois K ↥L := by
    rw [hLdef]; exact IsGalois.of_fixedField_normal_subgroup Nsub
  haveI hgalKMid : IsGalois K ↥Mid := by
    rw [hMiddef]; exact IsGalois.of_fixedField_normal_subgroup Msub
  have hdisjL : L ⊓ Mid = ⊥ := by rw [hLdef, hMiddef, inf_comm]; exact hdisj'
  have hsupL : L ⊔ Mid = ⊤ := by rw [hLdef, hMiddef, sup_comm]; exact hsup'
  -- the modulus
  obtain ⟨m, hm, hram, hprinc⟩ := h ↥L Ω hcommL
  set mr : ℕ := Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) with hmrdef
  have hmr : 0 < mr := by rw [hmrdef]; exact NK.CFTLib.Arl.absNorm_differentIdeal_pos
  set M : ℕ := m * mr with hMdef
  have hMpos : 0 < M := Nat.mul_pos hm hmr
  have hramM : ∀ p : NK.Chebotarev.PrimeIdeal ↥L, (M : 𝓞 ↥L) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1 := by
    intro p hp
    refine hram p fun hmem => hp ?_
    rw [hMdef, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hprincM : NK.CFTLib.artinKillsPrincipal ↥L Ω M :=
    NK.CFTLib.artinKillsPrincipal.mono hprinc ⟨mr, by rw [hMdef]⟩
  -- the Artin map
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust ↥L M hMpos
  obtain ⟨art, hart, hart_prin, hart_frob, hart_surj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin hcommL M hMpos hramM hprincM U hU hadj
  have hart_norm : ∀ y : NK.GlobalCFT.Idele Ω,
      art (NK.GlobalCFT.Idele.normIdeleHom ↥L Ω y) = 1 := by
    intro y
    rw [hart]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcommL M hMpos hramM hprincM U hU hadj
      (NK.NUV2.ARL.normAdjustment (K := ↥L) (L := Ω) M hMpos hramM U hU) y
  -- the idèle inclusion
  obtain ⟨u, hu⟩ : ∃ u : NK.GlobalCFT.Place ↥L → NK.GlobalCFT.Place K,
      ∀ w, NK.GlobalCFT.Place.LiesOver w (u w) :=
    ⟨fun w => Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder w),
      fun w => Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder w)⟩
  obtain ⟨φ, hφ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists u hu
  refine ⟨M, hMpos, u, hu, φ, hφ, art, hart_prin, hart_norm, hart_surj, ?_⟩
  -- the transfer
  intro x hx
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup ↥L M :=
    SetLike.ext fun y => (hU.1 y).trans Iff.rfl
  have hφx : φ x ∈ U := by
    rw [hUeq]
    exact NK.CFTLib.Existence.ideleInclusion_congruenceSubgroup u hu φ hφ M x hx
  have hadjU : NK.GlobalCFT.Idele.principalIdele ↥L
      (NK.CFTLib.Arl.adjust U hadj (φ x)) ∈ U := by
    have h1 := NK.CFTLib.Arl.adjust_spec U hadj (φ x)
    have h2 := U.mul_mem (U.inv_mem hφx) h1
    rwa [inv_mul_cancel_left] at h2
  have hcrux : NK.CFTLib.Arl.artinSym hcommL
      (FractionalIdeal.spanSingleton (𝓞 ↥L)⁰
        ((NK.CFTLib.Arl.adjust U hadj (φ x) : Units ↥L) : ↥L)) = 1 :=
    NK.CFTLib.Arl.artinSym_spanSingleton_eq_one hcommL M hMpos hramM hprincM
      _ ((hU.2 _).mp hadjU).1 ((hU.2 _).mp hadjU).2
  have hartφ : art (φ x) = NK.CFTLib.Arl.artinSym hcommL
      (NK.GlobalCFT.Idele.idealOf (φ x)) := by
    rw [hart]
    show NK.CFTLib.Arl.artinSym hcommL
      (NK.GlobalCFT.Idele.idealOf (φ x * NK.GlobalCFT.Idele.principalIdele ↥L
        (NK.CFTLib.Arl.adjust U hadj (φ x)))) = _
    rw [NK.GlobalCFT.Idele.idealOf_mul, NK.GlobalCFT.Idele.idealOf_principalIdele,
      NK.CFTLib.Arl.artinSym_mul hcommL (NK.GlobalCFT.Idele.idealOf_ne_zero _)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)), hcrux, mul_one]
  rw [hartφ]
  refine NK.CFTLib.Arl.artinSym_idealOf_ideleInclusion_eq_one (K := K) (L := ↥L) (E := Ω)
    hcommL u hu φ hφ M ?_ x ?_
  · -- the per-prime Frobenius product is trivial
    intro 𝔭 h𝔭M
    have hcardLM : Nat.card Gal(↥L/K) = Nat.card Gal(↥Mid/K) := by
      rw [IsGalois.card_aut_eq_finrank K ↥L, hfrL, hgalMid, ← hcardN, hcard, hcardM]
    have hexpM : ∀ σ : Gal(↥Mid/K), σ ^ Module.finrank K ↥L = 1 := hexp
    have hunrK : ∀ 𝔓 : NK.Chebotarev.PrimeIdeal Ω,
        𝔓.asIdeal.LiesOver 𝔭.asIdeal → 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro 𝔓 h𝔓
      have h2 : Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 Ω) = 1 := by
        by_contra hne
        have h3 : ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal :=
          NK.CFTLib.Arl.absNorm_differentIdeal_mem_of_ramified hne
        refine h𝔭M ?_
        rw [hMdef, Nat.cast_mul]
        exact Ideal.mul_mem_left _ _ h3
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal 𝔓.asIdeal (Gal(Ω/K))]
      exact h2
    exact NK.CFTLib.Arl.prod_frobAtPrime_pow_eq_one_of_unramified L Mid hdisjL hsupL
      hcardLM hexpM 𝔭 hunrK
  · -- the ideal of `φ x` is supported away from `(M)`
    intro 𝔮 h𝔮
    by_contra hmem
    have hx0 : NK.GlobalCFT.Idele.exp (𝔮.under (𝓞 K)) x = 0 :=
      NK.CFTLib.Arl.exp_eq_zero_of_mem_congruence M (NK.CFTLib.Arl.congruenceSubgroup K M)
        ⟨fun y => Iff.rfl, fun b => Iff.rfl⟩ x hx (𝔮.under (𝓞 K)) hmem
    have hcount : (NK.CFTLib.Arl.exps (NK.GlobalCFT.Idele.idealOf (φ x))) 𝔮 ≠ 0 :=
      (Finsupp.mem_support_iff).mp h𝔮
    rw [NK.CFTLib.Arl.exps_apply] at hcount
    rw [NK.CFTLib.Existence.count_idealOf_ideleInclusion u hu φ hφ x (𝔮.under (𝓞 K)) 𝔮
      (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal];
          exact Ideal.over_under 𝔮.asIdeal)] at hcount
    rw [NK.GlobalCFT.Idele.count_idealOf, hx0, mul_zero] at hcount
    exact hcount rfl

end NK.CFTLib.Arl
