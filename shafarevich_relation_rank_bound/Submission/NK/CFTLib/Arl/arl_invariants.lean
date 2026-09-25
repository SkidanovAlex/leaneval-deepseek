import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFTdeep.H1All
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.Arl.isCyclic_normClassQuotient_of_idelicArtinMap
import Submission.NK.CFTLib.Arl.arlSetup
import Submission.NK.CFTLib.Existence.arl_dev
import Submission.NK.CFTLib.Existence.arl_groupData
import Submission.NK.CFTLib.Existence.res_inf_le_ker_res_of_auxiliary
import Submission.NK.CFTLib.Existence.ideleInclusion_congruenceSubgroup
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFT.Cohomology.globalCFT_H0Computation_of_invariants_and_norm
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.NUV2.ARL.normAdjustment
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField

open scoped NumberField Pointwise nonZeroDivisors
open NumberField IntermediateField IsDedekindDomain

noncomputable section

open NK.GlobalCFT.Inclusion
open NK.GlobalCFT

namespace NK.CFTLib.Arl

/-- **The arithmetic input of Route B for the global fundamental class, in `H⁰` form.**

Let `G := Gal(Ω/K)`, `A := C_Ω` (the idèle class group of `Ω`, a `ℤ[G]`-module via
`NK.GlobalCFT.IdeleClassGroup.rep`), `M := Msub`, `N := Nsub`.  The hypotheses say `G = M × N`
(`M ⊓ N = ⊥`, `M ⊔ N = ⊤`), `N` cyclic, `|M| = |N| =: n`.  The conclusion `A^G ⊆ range(N_N)` is
the same as `C_K ⊆ N_{Ω/L}C_Ω` for `L = fixedField N`.

It is TRUE and is the only gap in `Submission/Work/CFTLib/fcElement_of_arl.lean`.

## Route as specified by the project lead (use this)

Write `L := fixedField N`, `Mid := fixedField M`; both `Ω/L` and `Mid/K` are cyclic of degree `n`,
`Ω = L·Mid`, `L ∩ Mid = K`, and restriction gives `Gal(Ω/L) ≅ Gal(Mid/K)`.  Let
`ψ := art : 𝕀_L →* Gal(Ω/L)` be the idèlic Artin map of the abelian extension `Ω/L` built from `h`
by `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` (a monoid hom with `art(Lˣ) = 1`,
`art(ideleOfPrime 𝔮) = frobAtPrime 𝔮` at unramified `𝔮`, surjective, and
`art(y) = artinSym (idealOf (y · b_y))` for the congruence adjustment `b_y`), and let
`Ψ : 𝕀_K →* Gal(Mid/K)` be the Artin map of the cyclic extension `Mid/K`.

1. `[C_L : N_{Ω/L}C_Ω] = n` (`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`, unconditional for
   cyclic levels) and `[C_L : ker ψ] = n` (surjectivity of `ψ`), so `ker ψ = N_{Ω/L}C_Ω` **as soon
   as one inclusion is known**.  The easy inclusion is `P_{m,+}·N(I_Ω) ⊆ ker ψ`: `P_{m,+} ⊆ ker ψ`
   is the ideal-theoretic reciprocity law `h` itself (via
   `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence`, proved) and norms are killed
   by `NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_relNorm_eq_one` (proved); the equality of
   indices is the idèle–ideal dictionary ("an idèle is a principal idèle times a unit idèle times
   an ideal idèle").  (This is the one substantial piece of bookkeeping.)
2. Hence it suffices to show `i(C_K) ⊆ ker ψ`, i.e. `ψ(i x) = 1` for `x : 𝕀_K`, where `i` is the
   natural inclusion `𝕀_K →* 𝕀_L`.  **No ramified local–global compatibility is needed.**  Fix
   `x` and replace it by a principal multiple `a·x` (`a ∈ Kˣ`) chosen by *weak approximation* so
   that `(a x)_w ∈ N_{Ω_w/L_w}(Ω_wˣ)` at every place `w` of `L` that is ramified in `Ω` and at
   every place dividing the modulus `m` (the local norm groups are open of finite index, so this is
   a finite set of open conditions; `a x` and `x` have the same class in `C_K` and `ψ` kills
   `Lˣ`, so this is free).  Then `x`'s obstruction lives in the ideal part `𝔟` (an ideal of `K`
   prime to the ramified set), and
   `ψ(𝔟𝒪_L) = ψ_{Mid/K}(N_{L/K}(𝔟𝒪_L)) = ψ_{Mid/K}(𝔟)^n = 1` by *unramified* Frobenius
   functoriality — the Frobenius of `𝔓 | 𝔭` restricts to `Frob_𝔭^{f}`, so
   `∏_{𝔮|𝔭} Frob_𝔮(Ω/L)^{e(𝔮|𝔭)} = Frob_𝔭(Ω/K)^{[L:K]} = 1` — which is exactly the *proved*
   `NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one`, together with `n = [M:K]` killing
   `Gal(Mid/K)`.  Then `𝔟 ∈ ker ψ_{Ω/L} = P_{m,+}·N(I_Ω)` puts `x` in the norm group.
3. Hence `i(C_K) ⊆ ker ψ = N_{Ω/L}C_Ω`, which is the conclusion in `H⁰` form.

Useful proved ingredients available: `NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust`,
`NK.CFTLib.Arl.artinSym` with `artinSym_mul`/`artinSym_one`, and the transfer lemma
`NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one`. -/
theorem arl_invariants (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] [Fintype ↥Nsub]
    (hcyc : IsCyclic ↥Nsub) (hMN : Msub ⊔ Nsub = ⊤) (hdisj : Msub ⊓ Nsub = ⊥)
    (hcard : Nat.card ↥Nsub = Nat.card ↥Msub) :
    ∀ a : (NK.GlobalCFT.IdeleClassGroup.rep K Ω).V,
      (∀ g : Gal(Ω/K), (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ g a = a) →
      ∃ b : (NK.GlobalCFT.IdeleClassGroup.rep K Ω).V,
        (∑ n : ↥Nsub, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K)) b) = a := by
  classical
  intro a ha
  -- ## 0. the Galois setup and the arithmetic core
  obtain ⟨hdisj', hsup', hfrL, hgalL, hgalMid, hcardN, hcardM, hexp, hcommMid, hcycL, hcommL⟩ :=
    NK.CFTLib.Arl.galoisSetup_of_subgroups Msub Nsub hMN hdisj hcard hcyc
  obtain ⟨M, hMpos, u, hu, φ, hφ, art, hart_prin, hart_norm, hart_surj, hart_kill⟩ :=
    NK.CFTLib.Arl.exists_art_kills_congruence h Msub Nsub hMN hdisj hcard hcyc
  haveI hgalKL : IsGalois K ↥(IntermediateField.fixedField Nsub) :=
    IsGalois.of_fixedField_normal_subgroup Nsub
  -- ## 1. the idèle and idèle class group inclusions
  obtain ⟨ψ₁, hψ₁⟩ := globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  have hψ₁_inj : Function.Injective ψ₁ :=
    globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ₁ hψ₁
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : Place Ω → Place ↥(IntermediateField.fixedField Nsub), ∀ w, Place.LiesOver w (u₂ w) :=
    ⟨fun w => Classical.choose (globalCFT_exists_placeUnder w),
      fun w => Classical.choose_spec (globalCFT_exists_placeUnder w)⟩
  obtain ⟨φ₂, hφ₂⟩ := globalCFT_ideleInclusion_exists u₂ hu₂
  obtain ⟨ψ₂, hψ₂⟩ := globalCFT_ideleClassGroup_inclusion_exists u₂ hu₂ φ₂ hφ₂
  have hψ₂_inj : Function.Injective ψ₂ :=
    globalCFT_ideleClassGroup_inclusion_injective u₂ hu₂ φ₂ hφ₂ ψ₂ hψ₂
  have hinv₂ : ∀ q : C[Ω], (∀ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • q = q) ↔ q ∈ ψ₂.range :=
    globalCFT_invariants_ideleClassGroup u₂ hu₂ φ₂ hφ₂ ψ₂ hψ₂
  have hinv₁ : ∀ q : C[↥(IntermediateField.fixedField Nsub)], (∀ σ : Gal(↥(IntermediateField.fixedField Nsub)/K), σ • q = q) ↔ q ∈ ψ₁.range :=
    globalCFT_invariants_ideleClassGroup u hu φ hφ ψ₁ hψ₁
  -- ## 2. `a` is `Gal(Ω/K)`-fixed, hence `Gal(Ω/L)`-fixed and in the range of `ψ₂`
  set q : C[Ω] := Additive.toMul a with hq
  have hainv : Additive.ofMul q ∈ (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ.invariants := by
    rw [show Additive.ofMul q = a from by rw [hq]; exact ofMul_toMul a]
    exact (Representation.mem_invariants _ a).mpr ha
  have haq : ∀ σ : Gal(Ω/K), σ • q = q :=
    NK.GlobalCFT.Cohomology.mem_rep_invariants_iff.mp hainv
  have haqL : ∀ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • q = q := by
    intro σ
    have key : σ • q = (((IntermediateField.subgroupEquivAlgEquiv Nsub).symm σ : ↥Nsub) :
        Gal(Ω/K)) • q := by
      rw [← MulEquiv.apply_symm_apply (IntermediateField.subgroupEquivAlgEquiv Nsub) σ]
      rfl
    rw [key]
    exact haq _
  obtain ⟨q', hq'⟩ := MonoidHom.mem_range.mp ((hinv₂ q).mp haqL)
  -- ## 3. `q'` is fixed by `Gal(L/K)`
  have hequiv : ∀ (τ : Gal(Ω/K)) (z : C[↥(IntermediateField.fixedField Nsub)]),
      ψ₂ (AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField Nsub) τ • z) = τ • ψ₂ z := by
    intro τ z
    obtain ⟨v, rfl⟩ := IdeleClassGroup.mk_surjective ↥(IntermediateField.fixedField Nsub) z
    rw [IdeleClassGroup.smul_mk, hψ₂, hψ₂, IdeleClassGroup.smul_mk,
      NK.HassePrinciple.ideleInclusion_smul_restrict u₂ hu₂ φ₂ hφ₂ τ v]
  have hq'fix : ∀ g : Gal(↥(IntermediateField.fixedField Nsub)/K), g • q' = q' := by
    intro g
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := ↥(IntermediateField.fixedField Nsub))
      Ω g
    have heq : ψ₂ (g • q') = ψ₂ q' := by
      rw [← hτ, hequiv τ q', hq']
      exact haq τ
    exact hψ₂_inj heq
  -- ## 4. `q'` is in the range of the inclusion `C_K → C_L`
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ((hinv₁ q').mp hq'fix)
  -- ## 5. the arithmetic: `ψ₁ x` is a norm from `C_Ω`
  have hkillι : ∀ w : NK.GlobalCFT.Idele K, art (φ w) = 1 := by
    intro w
    obtain ⟨UK, hUK, hadjK⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K M hMpos
    have hUKeq : UK = NK.CFTLib.Arl.congruenceSubgroup K M :=
      SetLike.ext fun y => (hUK.1 y).trans Iff.rfl
    obtain ⟨b, hb⟩ := hadjK w
    have hb' : w * Idele.principalIdele K b ∈ NK.CFTLib.Arl.congruenceSubgroup K M := by
      rw [← hUKeq]; exact hb
    have h1 := hart_kill (w * Idele.principalIdele K b) hb'
    rw [map_mul, globalCFT_ideleInclusion_principalIdele u hu φ hφ b, map_mul,
      hart_prin] at h1
    simpa using h1
  have hprin_le : Idele.principalSubgroup ↥(IntermediateField.fixedField Nsub) ≤ art.ker := by
    intro c hc
    obtain ⟨b, rfl⟩ := hc
    exact MonoidHom.mem_ker.mpr (hart_prin b)
  let art₁ : C[↥(IntermediateField.fixedField Nsub)] →* Gal(Ω/↥(IntermediateField.fixedField Nsub)) :=
    QuotientGroup.lift (Idele.principalSubgroup ↥(IntermediateField.fixedField Nsub)) art hprin_le
  have hart₁ : ∀ y : NK.GlobalCFT.Idele ↥(IntermediateField.fixedField Nsub), art₁ (IdeleClassGroup.mk ↥(IntermediateField.fixedField Nsub) y) = art y := fun y =>
    QuotientGroup.lift_mk' (Idele.principalSubgroup ↥(IntermediateField.fixedField Nsub)) hprin_le y
  have hsurj₁ : Function.Surjective art₁ := by
    intro g
    obtain ⟨w, hw⟩ := hart_surj g
    exact ⟨IdeleClassGroup.mk ↥(IntermediateField.fixedField Nsub) w, by rw [hart₁, hw]⟩
  have hkerArt : art₁.ker = Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω := by
    have hle : Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω ≤ art₁.ker := by
      intro z hz
      obtain ⟨y, hy⟩ := Idele.mem_normClassSubgroup.mp hz
      rw [← hy, MonoidHom.mem_ker]
      obtain ⟨v, rfl⟩ := IdeleClassGroup.mk_surjective Ω y
      rw [IdeleClassGroup.normClassHom_mk, hart₁, hart_norm v]
    refine le_antisymm ?_ hle
    have hidxN : (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).index = Module.finrank ↥(IntermediateField.fixedField Nsub) Ω :=
      NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic
    have hidxker : art₁.ker.index = Nat.card Gal(Ω/↥(IntermediateField.fixedField Nsub)) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj₁, Subgroup.card_top]
    have hcardG : Nat.card Gal(Ω/↥(IntermediateField.fixedField Nsub)) = Module.finrank ↥(IntermediateField.fixedField Nsub) Ω :=
      IsGalois.card_aut_eq_finrank ↥(IntermediateField.fixedField Nsub) Ω
    have hidx : (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).index = art₁.ker.index := by
      rw [hidxN, hidxker, hcardG]
    have hne : art₁.ker.index ≠ 0 := by
      rw [hidxker, hcardG]
      exact (Module.finrank_pos (R := ↥(IntermediateField.fixedField Nsub)) (M := Ω)).ne'
    have hrel : (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).relIndex art₁.ker = 1 := by
      have hmul := Subgroup.relIndex_mul_index hle
      rw [hidx] at hmul
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by rw [hmul, one_mul])
    exact (Subgroup.relIndex_eq_one (H := Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω)
      (K := art₁.ker)).mp hrel
  have hx_norm : ψ₁ x ∈ Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω := by
    rw [← hkerArt, MonoidHom.mem_ker]
    obtain ⟨w, rfl⟩ := IdeleClassGroup.mk_surjective K x
    rw [hψ₁ w, hart₁, hkillι w]
  obtain ⟨y, hy⟩ := Idele.mem_normClassSubgroup.mp hx_norm
  -- ## 6. the answer
  refine ⟨Additive.ofMul y, ?_⟩
  have hq_eq : q = ∏ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • y := by
    rw [← hq', ← hx, ← hy]
    obtain ⟨v, rfl⟩ := IdeleClassGroup.mk_surjective Ω y
    rw [IdeleClassGroup.normClassHom_mk, hψ₂]
    rw [show (∏ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • IdeleClassGroup.mk Ω v)
        = IdeleClassGroup.mk Ω (∏ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • v) from by
      have key : ∀ s : Finset (Gal(Ω/↥(IntermediateField.fixedField Nsub))),
          (∏ σ ∈ s, σ • IdeleClassGroup.mk Ω v)
            = IdeleClassGroup.mk Ω (∏ σ ∈ s, σ • v) := by
        intro s
        induction s using Finset.induction with
        | empty => rfl
        | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, IdeleClassGroup.smul_mk, map_mul]
      simpa using key Finset.univ]
    rw [globalCFT_prod_smul_eq_inclusion_normIdeleHom u₂ hu₂ φ₂ hφ₂ v]
  have hsum : (∑ n : ↥Nsub, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K))
        (Additive.ofMul y)) = Additive.ofMul q := by
    rw [hq_eq]
    have key : ∀ s : Finset ↥Nsub,
        (∑ n ∈ s, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K)) (Additive.ofMul y))
          = Additive.ofMul (∏ n ∈ s, (n : Gal(Ω/K)) • y) := by
      intro s
      induction s using Finset.induction with
      | empty => rfl
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.prod_insert ha, ih]
          change (Representation.ofMulDistribMulAction (Ω ≃ₐ[K] Ω) (IdeleClassGroup Ω)
              (a : Gal(Ω/K))) (Additive.ofMul y) + Additive.ofMul (∏ n ∈ s, (n : Gal(Ω/K)) • y)
            = Additive.ofMul ((a : Gal(Ω/K)) • y * ∏ n ∈ s, (n : Gal(Ω/K)) • y)
          rw [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]
          rfl
    rw [show (∑ n : ↥Nsub, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K))
          (Additive.ofMul y))
        = ∑ n ∈ (Finset.univ : Finset ↥Nsub),
            (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K)) (Additive.ofMul y) from rfl,
      key Finset.univ]
    congr 1
    exact Fintype.prod_equiv (IntermediateField.subgroupEquivAlgEquiv Nsub)
      (fun n : ↥Nsub => (n : Gal(Ω/K)) • y)
      (fun σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)) => σ • y) (fun n => rfl)
  rw [hsum]
  exact (show a = Additive.ofMul q from by rw [hq]; exact ofMul_toMul a).symm


end NK.CFTLib.Arl
