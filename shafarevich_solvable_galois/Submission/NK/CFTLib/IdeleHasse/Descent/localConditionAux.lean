import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSandwich
import Submission.NK.CFTLib.IdeleHasse.Descent.finrank_adicCompletion_ramificationIdx_of_compositum
import Submission.NK.CFTLib.IdeleHasse.Descent.localDictionaryAux
import Submission.NK.CFTLib.IdeleHasse.Descent.indexSupNormGroupUnramified
import Submission.NK.NUV2.ChebAux.auxLocalCondition
import Submission.NK.Unramified.normGroup_eq_unramifiedNormGroup
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.LocalKW.isGalois_and_isMulCommutative_gal_sup
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliaries for the odd local condition at a finite place

`NK.CFTLib.IdeleHasse.Descent.localConditionOdd` needs, at a finite place `v₀ = ofFinite Q` of
`K` and for an auxiliary cyclotomic field `M = K(ζ_q)`, `q ∤ NQ`, the statement that every
`x ∈ Kˣ` is a local norm from `E = L·M` over `M_w` at every `w | Q`.

The mathematical content is Milne, *CFT*, Lemma III.3.6/VII.7.3 (the local base change): the
hypothesis is `[L_r : K_v] ∣ [M_w : K_v]`.  The proof implemented here is the *index sandwich*
`NK.CFTLib.IdeleHasse.normGroup_index_sandwich`, whose inputs are, with
`F = K_v`, `C = L_r`, `F' = M_w`, `E' = E_q` and `f = f(r|Q)`:

* `[Fˣ : N_{C/F}] = [C : F]` and `[Fˣ : N_{E'/F}] = [E' : F]` and `[F'ˣ : N_{E'/F'}] = [E' : F']`
  (the local norm index theorem, `Commons.…abelian_local_norm_index_at_base`);
* the compositum degree `[E' : F'] = e(r|Q) = [C:F]/f`
  (`Descent.finrank_adicCompletion_ramificationIdx_of_compositum`);
* `f | [C:F]`;
* `[Fˣ : N_{F'/F} ⊔ N_{C/F}] = f`, i.e. the join of the two norm groups is the unramified norm
  group of degree `f` (`indexSupNormGroupUnramified`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.IdeleHasse.Descent

/-- **The local norm index theorem at a pair of places.**  For a finite Galois extension `L/K` of
number fields with abelian Galois group and `q | Q`, the norm group of the local extension
`L_q / K_Q` has index the local degree. -/
theorem index_normGroup_adicCompletion {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    (NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L)).index =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  haveI hmc : IsMulCommutative ((q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L)) :=
    NK.NUV2.ArtinBridge.isMulCommutative_adicCompletion_of_isGalois Q q hq
  have hcomm : ∀ a b : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L),
      a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  rw [NK.LocalReciprocity.normGroup_eq_range, Subgroup.index_eq_card,
    Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base
      (K := K) Q hcomm]
  exact IsGalois.card_aut_eq_finrank (Q.adicCompletion K) (q.adicCompletion L)


/-- The inertia degree of a prime of `L` above `Q` divides `[L : K]` (for `L/K` Galois). -/
theorem inertiaDeg_dvd_finrank {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (r : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hr : r.asIdeal.LiesOver Q.asIdeal) :
    r.asIdeal.inertiaDeg (𝓞 K) ∣ Module.finrank K L := by
  haveI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := inferInstance
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    Q.asIdeal (𝓞 L) Gal(L/K)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal r.asIdeal Gal(L/K),
    IsGalois.card_aut_eq_finrank] at h
  exact ⟨(Ideal.primesOver Q.asIdeal (𝓞 L)).ncard *
      Ideal.ramificationIdxIn Q.asIdeal (𝓞 L), by rw [← h]; ring⟩

/-- **The Galois group of a compositum of two normal abelian subextensions is commutative.** -/
theorem isMulCommutative_gal_adjoin {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (M ≃ₐ[K] M)]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) :
    IsMulCommutative (E ≃ₐ[K] E) := by
  classical
  haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  let fL : L →ₐ[K] E := IsScalarTower.toAlgHom K L E
  let fM : M →ₐ[K] E := IsScalarTower.toAlgHom K M E
  let L' : IntermediateField K E := fL.fieldRange
  let M' : IntermediateField K E := fM.fieldRange
  have hL'gen : L' = IntermediateField.adjoin K (Set.range (algebraMap L E)) := by
    refine le_antisymm ?_ ?_
    · intro y hy
      rw [AlgHom.mem_fieldRange] at hy
      obtain ⟨z, rfl⟩ := hy
      exact IntermediateField.subset_adjoin K _ (Set.mem_range_self z)
    · rw [IntermediateField.adjoin_le_iff]
      rintro y ⟨z, rfl⟩
      exact AlgHom.mem_fieldRange.mpr ⟨z, rfl⟩
  have hM'gen : M' = IntermediateField.adjoin K (Set.range (algebraMap M E)) := by
    refine le_antisymm ?_ ?_
    · intro y hy
      rw [AlgHom.mem_fieldRange] at hy
      obtain ⟨z, rfl⟩ := hy
      exact IntermediateField.subset_adjoin K _ (Set.mem_range_self z)
    · rw [IntermediateField.adjoin_le_iff]
      rintro y ⟨z, rfl⟩
      exact AlgHom.mem_fieldRange.mpr ⟨z, rfl⟩
  have hsup : L' ⊔ M' = ⊤ := by
    rw [hL'gen, hM'gen, ← IntermediateField.adjoin_union]
    refine IntermediateField.toSubalgebra_inj.mp ?_
    rw [IntermediateField.adjoin_toSubalgebra, hgen]
    exact Subalgebra.ext fun x => Iff.rfl
  have hL' : ∀ σ τ : ↥L' ≃ₐ[K] ↥L', σ * τ = τ * σ := by
    intro σ τ
    have F : (L ≃ₐ[K] L) ≃* (↥L' ≃ₐ[K] ↥L') := AlgEquiv.autCongr (AlgEquiv.ofInjectiveField fL)
    have h2 : F.symm (σ * τ) = F.symm (τ * σ) := by
      rw [map_mul, map_mul, IsMulCommutative.is_comm.comm (F.symm σ) (F.symm τ)]
    exact F.symm.injective h2
  have hM' : ∀ σ τ : ↥M' ≃ₐ[K] ↥M', σ * τ = τ * σ := by
    intro σ τ
    have F : (M ≃ₐ[K] M) ≃* (↥M' ≃ₐ[K] ↥M') := AlgEquiv.autCongr (AlgEquiv.ofInjectiveField fM)
    have h2 : F.symm (σ * τ) = F.symm (τ * σ) := by
      rw [map_mul, map_mul, IsMulCommutative.is_comm.comm (F.symm σ) (F.symm τ)]
    exact F.symm.injective h2
  haveI hNL' : Normal K ↥L' := Normal.of_algEquiv (AlgEquiv.ofInjectiveField fL)
  haveI hNM' : Normal K ↥M' := Normal.of_algEquiv (AlgEquiv.ofInjectiveField fM)
  obtain ⟨-, hcomm⟩ :=
    NK.LocalKW.isGalois_and_isMulCommutative_gal_sup (F := K) (Ω := E) L' M' hL' hM'
  haveI hcommI : IsMulCommutative (↥(L' ⊔ M') ≃ₐ[K] ↥(L' ⊔ M')) :=
    IsMulCommutative.of_comm hcomm
  have e : (↥(L' ⊔ M') ≃ₐ[K] ↥(L' ⊔ M')) ≃* (E ≃ₐ[K] E) :=
    AlgEquiv.autCongr ((IntermediateField.equivOfEq hsup).trans IntermediateField.topEquiv)
  refine IsMulCommutative.of_comm fun σ τ => ?_
  have h2 : e.symm (σ * τ) = e.symm (τ * σ) := by
    rw [map_mul, map_mul, IsMulCommutative.is_comm.comm (e.symm σ) (e.symm τ)]
  exact e.symm.injective h2

/-- The local degree `[L_r : K_Q] = e · f` divides `[L : K]`. -/
theorem finrank_adicCompletion_dvd_finrank {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (r : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hr : r.asIdeal.LiesOver Q.asIdeal) :
    Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣ Module.finrank K L := by
  letI : Algebra (Q.adicCompletion K) (r.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q r hr)
  have hfin := Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    Q r hr
  rw [← hfin]
  haveI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := inferInstance
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    Q.asIdeal (𝓞 L) Gal(L/K)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal r.asIdeal Gal(L/K),
    Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) Q.asIdeal r.asIdeal
      (Gal(L/K)),
    IsGalois.card_aut_eq_finrank] at h
  exact ⟨(Ideal.primesOver Q.asIdeal (𝓞 L)).ncard, by rw [← h]; ring⟩

/-- **The local condition at a finite place over `Q`, for the cyclotomic auxiliary field.**

`M = K(ζ_q)` with `q ∤ NQ` is unramified at `Q`, `E = L·M`, and `[L : K] ∣ f(wl|Q)`; then every
`x ∈ Kˣ` is a local norm from `E` over `M_wl` at `ql | wl` (Milne, *CFT*, VII.7.3 / III.3.6). -/
theorem mem_localNormFinite_of_cyclotomicAux
    {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
    [NumberField M] [Field E] [NumberField E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    [IsCyclic (L ≃ₐ[K] L)] [IsCyclic (M ≃ₐ[K] M)]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    {q : ℕ} (hq : q.Prime)
    [IsCyclotomicExtension {q} K M] [IsCyclotomicExtension {q} L E]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hcop : Nat.Coprime (Ideal.absNorm Q.asIdeal) q)
    (wl : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hwl : wl.asIdeal.LiesOver Q.asIdeal)
    (hdvdL : Module.finrank K L ∣ wl.asIdeal.inertiaDeg (𝓞 K))
    (ql : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (hql : ql.asIdeal.LiesOver wl.asIdeal)
    (x : Kˣ) :
    Units.map (algebraMap M (wl.adicCompletion M)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
      (NK.GlobalCFT.Place.localNormFinite ql wl hql).range := by
  classical
  -- ## `q` does not lie in `Q`
  have hlQ : (q : 𝓞 K) ∉ Q.asIdeal := by
    intro hmem
    have hle : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) ≤ Q.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem]; exact hmem
    have hdvd : Ideal.absNorm Q.asIdeal ∣ Ideal.absNorm (Ideal.span ({(q : 𝓞 K)})) :=
      Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_natCast] at hdvd
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := Ideal.absNorm Q.asIdeal)
      (by have h0 : Ideal.absNorm Q.asIdeal ≠ 0 :=
            fun hc => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc)
          have h1 : Ideal.absNorm Q.asIdeal ≠ 1 :=
            fun hc => Q.isMaximal.ne_top (Ideal.absNorm_eq_one_iff.mp hc)
          omega)
    have hpq : p = q :=
      (hq.eq_one_or_self_of_dvd p (hp.dvd_of_dvd_pow (hpdvd.trans hdvd))).resolve_left hp.ne_one
    have hq_dvd : q ∣ Ideal.absNorm Q.asIdeal := hpq ▸ hpdvd
    have h1 : q ∣ Nat.gcd (Ideal.absNorm Q.asIdeal) q := Nat.dvd_gcd hq_dvd (dvd_refl q)
    rw [hcop.gcd_eq_one] at h1
    exact hq.not_dvd_one h1
  -- ## the prime of `L` below `ql`
  have hqK : ql.asIdeal.under (𝓞 K) = wl.asIdeal.under (𝓞 K) := by
    rw [hql.over, Ideal.under_under]
  have hQunder : Q.asIdeal = (ql.asIdeal.under (𝓞 L)).under (𝓞 K) := by
    rw [hwl.over, ← hqK, Ideal.under_under]
  haveI hLies : (ql.asIdeal.under (𝓞 L)).LiesOver Q.asIdeal := ⟨hQunder⟩
  have hneL : ql.asIdeal.under (𝓞 L) ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot Q.ne_bot (ql.asIdeal.under (𝓞 L))
  let rl : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    ⟨ql.asIdeal.under (𝓞 L), inferInstance, hneL⟩
  have hrl : rl.asIdeal.LiesOver Q.asIdeal := hLies
  have hrl' : ql.asIdeal.LiesOver rl.asIdeal := ⟨rfl⟩
  have hqQ : ql.asIdeal.LiesOver Q.asIdeal := ⟨by rw [hQunder, Ideal.under_under]⟩
  -- ## the local fields and their algebra structures
  letI : Algebra (Q.adicCompletion K) (wl.adicCompletion M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q wl hwl)
  letI : Algebra (Q.adicCompletion K) (rl.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q rl hrl)
  letI : Algebra (Q.adicCompletion K) (ql.adicCompletion E) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q ql hqQ)
  letI : Algebra (wl.adicCompletion M) (ql.adicCompletion E) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap wl ql hql)
  letI : Algebra (rl.adicCompletion L) (ql.adicCompletion E) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap rl ql hrl')
  haveI hst1 : IsScalarTower (Q.adicCompletion K) (wl.adicCompletion M)
      (ql.adicCompletion E) := by
    refine IsScalarTower.of_algebraMap_eq (fun y => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    simpa [RingHom.comp_apply] using (RingHom.congr_fun
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q wl ql
        hwl hql hqQ) y).symm
  haveI hst2 : IsScalarTower (Q.adicCompletion K) (rl.adicCompletion L)
      (ql.adicCompletion E) := by
    refine IsScalarTower.of_algebraMap_eq (fun y => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    simpa [RingHom.comp_apply] using (RingHom.congr_fun
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q rl ql
        hrl hrl' hqQ) y).symm
  haveI hfd1 : FiniteDimensional (Q.adicCompletion K) (wl.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q wl hwl
  haveI hfd2 : FiniteDimensional (Q.adicCompletion K) (rl.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q rl hrl
  haveI hfd3 : FiniteDimensional (Q.adicCompletion K) (ql.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q ql hqQ
  haveI hfd4 : FiniteDimensional (wl.adicCompletion M) (ql.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion wl ql hql
  -- ## commutativity of the relevant Galois groups
  haveI hcycL' : IsMulCommutative (L ≃ₐ[K] L) := IsCyclic.isMulCommutative
  haveI hcycM' : IsMulCommutative (M ≃ₐ[K] M) := IsCyclic.isMulCommutative
  haveI hEK : IsMulCommutative (E ≃ₐ[K] E) := isMulCommutative_gal_adjoin hgen
  haveI hEM : IsMulCommutative (E ≃ₐ[M] E) := by
    refine IsMulCommutative.of_comm fun σ τ => ?_
    refine AlgEquiv.restrictScalars_injective K ?_
    show (AlgEquiv.restrictScalars K σ) * (AlgEquiv.restrictScalars K τ) =
      (AlgEquiv.restrictScalars K τ) * (AlgEquiv.restrictScalars K σ)
    exact IsMulCommutative.is_comm.comm _ _
  haveI hgalME : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  -- ## the norm index theorems
  have hidxE' : (NK.LocalReciprocity.normGroup (wl.adicCompletion M)
        (ql.adicCompletion E)).index =
      Module.finrank (wl.adicCompletion M) (ql.adicCompletion E) :=
    index_normGroup_adicCompletion wl ql hql
  have hidxN : (NK.LocalReciprocity.normGroup (Q.adicCompletion K)
        (rl.adicCompletion L)).index =
      Module.finrank (Q.adicCompletion K) (rl.adicCompletion L) :=
    index_normGroup_adicCompletion Q rl hrl
  -- ## the local degree of `M/K` at `Q`
  obtain ⟨heM, -⟩ := cyclotomicLocalDegree Q q hq hlQ wl hwl
  have hfpos : 0 < rl.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos rl.asIdeal (𝓞 K)
  -- ## explicit forms of the local degrees
  have hE' : @Module.finrank (wl.adicCompletion M) (ql.adicCompletion E) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap wl ql hql)).toModule =
      rl.asIdeal.ramificationIdx (𝓞 K) :=
    finrank_adicCompletion_ramificationIdx_of_compositum (K := K) (L := L) (M := M) (E := E)
      hgen hq Q hcop wl hwl hdvdL ql hql
  have hC : @Module.finrank (Q.adicCompletion K) (rl.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q rl hrl)).toModule =
      rl.asIdeal.ramificationIdx (𝓞 K) * rl.asIdeal.inertiaDeg (𝓞 K) :=
    (Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q rl hrl).symm
  have hF' : @Module.finrank (Q.adicCompletion K) (wl.adicCompletion M) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q wl hwl)).toModule =
      wl.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q wl hwl, heM, one_mul]
  -- ## the index of the join
  have hf_dvd_d : rl.asIdeal.inertiaDeg (𝓞 K) ∣ wl.asIdeal.inertiaDeg (𝓞 K) :=
    (inertiaDeg_dvd_finrank Q rl hrl).trans hdvdL
  have hP : (NK.LocalReciprocity.normGroup (Q.adicCompletion K) (wl.adicCompletion M) ⊔
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) (rl.adicCompletion L)).index =
      rl.asIdeal.inertiaDeg (𝓞 K) := by
    rw [NK.Unramified.normGroup_eq_unramifiedNormGroup Q wl hwl heM]
    exact indexSupNormGroupUnramified Q rl hrl (wl.asIdeal.inertiaDeg (𝓞 K)) hf_dvd_d
  -- ## the degree identity
  have hdeg : @Module.finrank (wl.adicCompletion M) (ql.adicCompletion E) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap wl ql hql)).toModule =
      @Module.finrank (Q.adicCompletion K) (rl.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q rl hrl)).toModule /
        rl.asIdeal.inertiaDeg (𝓞 K) := by
    rw [hE', hC]
    exact (Nat.mul_div_cancel _ hfpos).symm
  -- ## divisibility of the degrees
  have hdvd : @Module.finrank (Q.adicCompletion K) (rl.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q rl hrl)).toModule ∣
      @Module.finrank (Q.adicCompletion K) (wl.adicCompletion M) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q wl hwl)).toModule := by
    have h1 : @Module.finrank (Q.adicCompletion K) (rl.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q rl hrl)).toModule ∣
        wl.asIdeal.inertiaDeg (𝓞 K) :=
      (finrank_adicCompletion_dvd_finrank Q rl hrl).trans hdvdL
    rw [hC, hF', ← hC]
    exact h1
  -- ## the index sandwich
  have hmem := NK.CFTLib.IdeleHasse.normGroup_index_sandwich
    (F := Q.adicCompletion K) (F' := wl.adicCompletion M) (C := rl.adicCompletion L)
    (E' := ql.adicCompletion E) (rl.asIdeal.inertiaDeg (𝓞 K)) hfpos hidxE' hidxN hP hdeg hdvd
  have hx := hmem (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x)
  -- ## rewrite the element
  have helem : Units.map (algebraMap (Q.adicCompletion K) (wl.adicCompletion M)).toMonoidHom
        (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x) =
      Units.map (algebraMap M (wl.adicCompletion M)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) := by
    apply Units.ext
    change Commons.RingTheory.Henselian.adicCompletionMap Q wl hwl
        (algebraMap K (Q.adicCompletion K) (x : K)) =
      algebraMap M (wl.adicCompletion M) (algebraMap K M (x : K))
    rw [show algebraMap K (Q.adicCompletion K) (x : K) = ((x : K) : Q.adicCompletion K)
        from algebraMap_adicCompletion_eq_coe Q (x : K),
      Commons.RingTheory.Henselian.adicCompletionMap_apply]
    exact (algebraMap_adicCompletion_eq_coe wl (algebraMap K M (x : K))).symm
  rw [helem] at hx
  exact hx
