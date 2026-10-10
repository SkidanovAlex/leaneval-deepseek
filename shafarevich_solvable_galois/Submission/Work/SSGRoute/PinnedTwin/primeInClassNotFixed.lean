import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.PinnedTwin.congSubgroup_smul_mem
import Submission.Work.SSGRoute.PinnedTwin.exists_asym_ideal
import Submission.Work.SSGRoute.PinnedTwin.ideleOfIdeal_smul_cong
import Submission.Work.SSGRoute.PinnedTwin.rhoIdeal_smul_cong
import Submission.Work.SSGRoute.ges_escape_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A prime in a prescribed ideal class which is not fixed by an involution

`Work.SSGRoute.PinnedTwin.primeInClassNotFixed`: for a Galois extension `k ⊆ K` of number fields, an
involution `ρ` of `K` over `k` moving a place `𝔮`, and any nonzero fractional ideal `A`, there is a
prime `Q'` in the ideal class of `A`, not fixed by `ρ`, and different from `ρ𝔮`.

The strategy is described in the proof of the theorem below.
-/

namespace Work.SSGRoute.PinnedTwin

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

section Basic

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- `ρ` acts on ideals as an involution. -/
theorem rhoIdeal_rhoIdeal (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (I : Ideal (𝓞 K)) :
    rhoIdeal ρ (rhoIdeal ρ I) = I := by
  rw [rhoIdeal, rhoIdeal, Ideal.map_map]
  conv_rhs => rw [← Ideal.map_id I]
  congr 1
  ext x
  simpa using rhoRing_mul_self ρ hρ2 x

/-- The subgroup `Kˣ · U(𝔪)` of the idèles is stable under the action of `ρ`, when `𝔪` is
stable (support and positivity) under `ρ`. -/
theorem smul_mem_sup_principal_congSubgroup (ρ : K ≃ₐ[k] K) (𝔪 : NK.NUV2.RouteB.Modulus K)
    (hpos : 𝔪.pos = ∅)
    (hstab : ∀ q : HeightOneSpectrum (𝓞 K),
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q)
    {x : NK.GlobalCFT.Idele K}
    (hx : x ∈ NK.GlobalCFT.Idele.principalSubgroup K ⊔
      NK.NUV2.RouteB.CongSubgroup K 𝔪) :
    ρ • x ∈ NK.GlobalCFT.Idele.principalSubgroup K ⊔
      NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  obtain ⟨a, ha, u, hu, rfl⟩ := Subgroup.mem_sup.mp hx
  obtain ⟨y, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp ha
  refine Subgroup.mem_sup.mpr ⟨NK.GlobalCFT.Idele.principalIdele K (Units.map ρ.toMonoidHom y),
    NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨Units.map ρ.toMonoidHom y, rfl⟩,
    ρ • u, congSubgroup_smul_mem ρ 𝔪 hpos hstab hu, ?_⟩
  rw [MulDistribMulAction.smul_mul, NK.GlobalCFT.Galois.globalCFT_smul_principalIdele]

end Basic

section KeyLemma

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **A prime which is fixed by `ρ` has a `ρ`-symmetric ray class.**  If `Q` is a prime, coprime to
a `ρ`-stable modulus `𝔪`, fixed by `ρ`, and `I` is an ideal coprime to `𝔪` whose ray class mod `𝔪`
equals the ray class of `Q`, then the ray class of `ρI` equals that of `I`. -/
theorem classOfIdeal_rhoIdeal_eq_of_fixed (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (𝔪 : NK.NUV2.RouteB.Modulus K) (hpos : 𝔪.pos = ∅)
    (hstab : ∀ q : HeightOneSpectrum (𝓞 K),
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q)
    (Q : HeightOneSpectrum (𝓞 K)) (hQ : 𝔪.exps Q = 0)
    (hQfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q = Q)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hIcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I)
    (hcl : NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) Q.asIdeal =
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I) :
    NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) (rhoIdeal ρ I) =
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I := by
  classical
  have hcl' : (QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K Q.asIdeal) :
        NK.GlobalCFT.Idele K ⧸ (NK.GlobalCFT.Idele.principalSubgroup K ⊔
          NK.NUV2.RouteB.CongSubgroup K 𝔪))
      = QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K I) := hcl
  have hmem : (NK.HeckeL.ideleOfIdeal K Q.asIdeal)⁻¹ * (NK.HeckeL.ideleOfIdeal K I)
      ∈ NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.NUV2.RouteB.CongSubgroup K 𝔪 := (QuotientGroup.eq).mp hcl'
  -- apply `ρ` to the relation
  have hmemρ : (ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal)⁻¹ *
      (ρ • NK.HeckeL.ideleOfIdeal K I)
      ∈ NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
    have h1 := smul_mem_sup_principal_congSubgroup ρ 𝔪 hpos hstab hmem
    have h2 : ρ • (NK.HeckeL.ideleOfIdeal K Q.asIdeal)⁻¹
        = (ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← MulDistribMulAction.smul_mul, inv_mul_cancel,
        MulDistribMulAction.smul_one]
    rw [MulDistribMulAction.smul_mul, h2] at h1
    exact h1
  -- the prime relation transported by `ρ`
  have hQ'' : (ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal) *
      (NK.HeckeL.ideleOfIdeal K Q.asIdeal)⁻¹ ∈
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
    have h := ideleOfIdeal_smul_cong ρ 𝔪 hpos hstab Q hQ
    rw [hQfix] at h
    exact Subgroup.mem_sup_right h
  -- the class of `ρ • id Q` equals that of `id Q`
  have hρQ : (QuotientGroup.mk (ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal) :
        NK.GlobalCFT.Idele K ⧸ (NK.GlobalCFT.Idele.principalSubgroup K ⊔
          NK.NUV2.RouteB.CongSubgroup K 𝔪))
      = QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K Q.asIdeal) :=
    (QuotientGroup.eq).mpr (by
      have h := Subgroup.inv_mem _ hQ''
      rw [mul_inv_rev, inv_inv, mul_comm] at h
      exact h)
  -- the class of `ρ • id I` equals that of `id I`
  have hρI : (QuotientGroup.mk (ρ • NK.HeckeL.ideleOfIdeal K I) :
        NK.GlobalCFT.Idele K ⧸ (NK.GlobalCFT.Idele.principalSubgroup K ⊔
          NK.NUV2.RouteB.CongSubgroup K 𝔪))
      = QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K I) :=
    ((QuotientGroup.eq).mpr hmemρ).symm.trans (hρQ.trans hcl')
  -- the class of the idèle of `ρI` equals that of `ρ • id I`
  have hcongP : (ρ • NK.HeckeL.ideleOfIdeal K I) *
      (NK.HeckeL.ideleOfIdeal K (rhoIdeal ρ I))⁻¹ ∈
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 :=
    Subgroup.mem_sup_right (rhoIdeal_smul_cong ρ 𝔪 hpos hstab I hI hIcop)
  have hρI' : (QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K (rhoIdeal ρ I)) :
        NK.GlobalCFT.Idele K ⧸ (NK.GlobalCFT.Idele.principalSubgroup K ⊔
          NK.NUV2.RouteB.CongSubgroup K 𝔪))
      = QuotientGroup.mk (ρ • NK.HeckeL.ideleOfIdeal K I) :=
    ((QuotientGroup.eq).mpr (by
      have h := Subgroup.inv_mem _ hcongP
      rw [mul_inv_rev, inv_inv, mul_comm] at h
      exact h)).symm
  rw [NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_mk (K := K)
      (NK.NUV2.RouteB.CongSubgroup K 𝔪) (rhoIdeal ρ I),
    NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_mk (K := K)
      (NK.NUV2.RouteB.CongSubgroup K 𝔪) I,
    hρI', hρI]

end KeyLemma

section Assembly

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- The congruence subgroup of a modulus consists of idèles which are local units at every finite
place. -/
private lemma congSubgroup_le_integralIdeles (𝔪 : NK.NUV2.RouteB.Modulus K) :
    NK.NUV2.RouteB.CongSubgroup K 𝔪 ≤ NK.GlobalCFT.Idele.integralIdeles K := by
  intro x hx
  rw [NK.GlobalCFT.Idele.mem_integralIdeles]
  intro v hv
  rw [NK.GlobalCFT.Place.isFinite_iff] at hv
  obtain ⟨q, rfl⟩ := hv
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  exact ((NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff.mp hx).1 q).1

/-- Congruence subgroups are anti-monotone in the modulus: a larger modulus describes a smaller
subgroup. -/
private lemma congSubgroup_antitone {𝔪 𝔪' : NK.NUV2.RouteB.Modulus K}
    (hexp : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≤ 𝔪'.exps q)
    (hpos : 𝔪.pos ⊆ 𝔪'.pos) :
    NK.NUV2.RouteB.CongSubgroup K 𝔪' ≤ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  intro x hx
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff] at hx ⊢
  refine ⟨fun q => ⟨(hx.1 q).1, ?_⟩, fun w hw hmem => hx.2 w hw (hpos hmem)⟩
  have h := (hx.1 q).2
  have h' : Valued.v (((x (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
      q.adicCompletion K) - 1) ≤ WithZero.exp (-(𝔪'.exps q : ℤ)) := h
  exact h'.trans (WithZero.exp_le_exp.mpr (by have h2 := hexp q; omega))

/-- An equality of ray classes descends along an inclusion of congruence subgroups. -/
private lemma classOfIdeal_eq_of_le {𝔪 𝔪' : NK.NUV2.RouteB.Modulus K}
    (hle : NK.NUV2.RouteB.CongSubgroup K 𝔪' ≤ NK.NUV2.RouteB.CongSubgroup K 𝔪)
    {I J : Ideal (𝓞 K)}
    (h : NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪') I =
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪') J) :
    NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I =
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) J := by
  rw [NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_mk] at h ⊢
  refine (QuotientGroup.eq).mpr ?_
  exact (sup_le le_sup_left (le_trans hle le_sup_right)) ((QuotientGroup.eq).mp h)

/-- The idèle attached to an ideal realises that ideal. -/
private lemma idealOf_ideleOfIdeal (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    NK.GlobalCFT.Idele.idealOf (NK.HeckeL.ideleOfIdeal K I) =
      (I : FractionalIdeal (𝓞 K)⁰ K) := by
  refine NK.GlobalCFT.IdeleClassGroup.fractionalIdeal_eq_of_count_eq
    (NK.GlobalCFT.Idele.idealOf_ne_zero _) (FractionalIdeal.coeIdeal_ne_zero.mpr hI) (fun q => ?_)
  rw [NK.GlobalCFT.Idele.count_idealOf, NK.HeckeL.ideleOfIdeal,
    NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]

/-- The ideal class of the idèle of an ideal is the class of that ideal. -/
private lemma idealClassMap_ideleOfIdeal (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    NK.GlobalCFT.IdeleClassGroup.idealClassMap K (NK.HeckeL.ideleOfIdeal K I) =
      ClassGroup.mk K (Units.mk0 ((I : FractionalIdeal (𝓞 K)⁰ K))
        (FractionalIdeal.coeIdeal_ne_zero.mpr hI)) := by
  rw [NK.GlobalCFT.IdeleClassGroup.idealClassMap_apply]
  congr 1
  exact Units.ext (by
    rw [Units.val_mk0, Units.val_mk0]
    exact idealOf_ideleOfIdeal I hI)

/-- The trivial modulus. -/
private noncomputable def trivialModulus (K : Type) [Field K] [NumberField K] :
    NK.NUV2.RouteB.Modulus K where
  exps := fun _ => 0
  finite_support := Filter.Eventually.of_forall (fun _ => rfl)
  pos := ∅

/-- Adjoin two primes to the support of a modulus, at level `1`. -/
private noncomputable def augmentModulus (𝔪 : NK.NUV2.RouteB.Modulus K)
    (𝔮₁ 𝔮₂ : HeightOneSpectrum (𝓞 K)) : NK.NUV2.RouteB.Modulus K := by
  classical
  exact
    { exps := fun q => 𝔪.exps q + (if q = 𝔮₁ then 1 else 0) + (if q = 𝔮₂ then 1 else 0)
      finite_support := by
        rw [NK.NUV2.RouteB.HasFiniteSupport, Filter.eventually_cofinite]
        refine (𝔪.supportFinset.finite_toSet.union
          ((Set.finite_singleton 𝔮₁).union (Set.finite_singleton 𝔮₂))).subset ?_
        intro q hq
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff] at hq ⊢
        by_cases h1 : q = 𝔮₁
        · exact Or.inr (Or.inl h1)
        by_cases h2 : q = 𝔮₂
        · exact Or.inr (Or.inr h2)
        exact Or.inl (𝔪.mem_supportFinset (by simpa [h1, h2] using hq))
      pos := ∅ }

private lemma augmentModulus_self_ne_zero (𝔪 : NK.NUV2.RouteB.Modulus K)
    (𝔮₁ 𝔮₂ : HeightOneSpectrum (𝓞 K)) : (augmentModulus 𝔪 𝔮₁ 𝔮₂).exps 𝔮₂ ≠ 0 := by
  classical
  have h : (augmentModulus 𝔪 𝔮₁ 𝔮₂).exps 𝔮₂ =
      𝔪.exps 𝔮₂ + (if 𝔮₂ = 𝔮₁ then 1 else 0) + 1 := by
    simp [augmentModulus]
  rw [h]
  omega

private lemma le_augmentModulus (𝔪 : NK.NUV2.RouteB.Modulus K)
    (𝔮₁ 𝔮₂ : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 K)) :
    𝔪.exps q ≤ (augmentModulus 𝔪 𝔮₁ 𝔮₂).exps q := by
  classical
  show 𝔪.exps q ≤ 𝔪.exps q + (if q = 𝔮₁ then 1 else 0) + (if q = 𝔮₂ then 1 else 0)
  omega

/-- The augmentation is stable under an involution exchanging the two added primes. -/
private lemma augmentModulus_stable (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    {𝔪 : NK.NUV2.RouteB.Modulus K}
    (hstab : ∀ q : HeightOneSpectrum (𝓞 K),
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q)
    (𝔮 : HeightOneSpectrum (𝓞 K)) :
    ∀ q : HeightOneSpectrum (𝓞 K),
      (augmentModulus 𝔪 𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)).exps
          (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q)
        = (augmentModulus 𝔪 𝔮
            (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)).exps q := by
  intro q
  have hρρ : ρ * ρ = 1 := by rw [← pow_two]; exact hρ2
  have h1 : (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q = 𝔮) ↔
      (q = Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) := by
    constructor
    · intro h
      have hh := congrArg (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) h
      rwa [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, hρρ,
        Commons.NumberTheory.NumberField.Completion.placeSmul_one] at hh
    · intro h
      rw [h]
      exact placeSmul_placeSmul ρ hρ2 𝔮
  have h2 : (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q =
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ↔ (q = 𝔮) := by
    constructor
    · intro h
      have hh := congrArg (Commons.NumberTheory.NumberField.Completion.placeSmul ρ) h
      rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, hρρ,
        Commons.NumberTheory.NumberField.Completion.placeSmul_one,
        ← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, hρρ,
        Commons.NumberTheory.NumberField.Completion.placeSmul_one] at hh
      exact hh
    · intro h; rw [h]
  classical
  simp only [augmentModulus, hstab q, h1, h2]
  ring

/-- **The main step.**  Assuming the asymmetric ideal of
`Work.SSGRoute.PinnedTwin.exists_asym_ideal` (stated here as a hypothesis), a prime in the
prescribed ideal class which is not fixed by the involution exists. -/
private theorem primeInClassNotFixed_aux (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (h_asym : ∀ (A₀ : Ideal (𝓞 K)) (hA₀ : A₀ ≠ 0) (u₀ : Kˣ),
      ((rhoIdeal ρ A₀ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        (A₀ : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (u₀ : K) →
      ∃ (𝔪 : NK.NUV2.RouteB.Modulus K) (I : Ideal (𝓞 K)),
        𝔪.pos = ∅ ∧
        (∀ q : HeightOneSpectrum (𝓞 K),
          𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) ∧
        I ≠ 0 ∧
        (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I) ∧
        (∃ y : Kˣ, (I : FractionalIdeal (𝓞 K)⁰ K) = (A₀ : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K)) ∧
        NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) (rhoIdeal ρ I) ≠
          NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I)
    (A : FractionalIdeal (𝓞 K)⁰ K) (hA : A ≠ 0)
    (𝔮 : HeightOneSpectrum (𝓞 K))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ (Q' : HeightOneSpectrum (𝓞 K)) (y : Kˣ),
      Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' ∧
      Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∧
      ((Q'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = A *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K)) := by
  classical
  -- ## the numerator, the denominator, and the coprimality of `A.den`
  set d : K := ((A.den : 𝓞 K) : K) with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef]
    exact fun h => nonZeroDivisors.ne_zero A.den.2
      ((IsFractionRing.injective (𝓞 K) K) (by simpa using h))
  have hA₀ : A.num ≠ 0 := fun h => hA ((FractionalIdeal.num_eq_zero_iff).mp h)
  have hA_num : ((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      A * FractionalIdeal.spanSingleton (𝓞 K)⁰ d := by
    have h := FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 K)) K A
    have hd : (algebraMap (𝓞 K) K) (↑A.den : 𝓞 K) = d := by rw [hddef]
    rw [hd] at h
    rw [← h, mul_comm]
  have hρA₀ : rhoIdeal ρ A.num ≠ 0 := by
    intro h
    have hmap : A.num.map (rhoRing ρ : 𝓞 K →+* 𝓞 K) = ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact h
    exact hA₀ ((Ideal.map_eq_bot_iff_of_injective
      (f := (rhoRing ρ : 𝓞 K →+* 𝓞 K)) (rhoRing ρ).injective).mp hmap)
  -- ## the asymmetric ideal: two cases
  have hmain : ∃ (𝔪 : NK.NUV2.RouteB.Modulus K) (I : Ideal (𝓞 K)),
      𝔪.pos = ∅ ∧
      (∀ q : HeightOneSpectrum (𝓞 K),
        𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) ∧
      I ≠ 0 ∧
      (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I) ∧
      (∃ y : Kˣ, (I : FractionalIdeal (𝓞 K)⁰ K) =
        ((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K)) ∧
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) (rhoIdeal ρ I) ≠
        NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I := by
    by_cases hcase : ClassGroup.mk0
          ⟨rhoIdeal ρ A.num, mem_nonZeroDivisors_of_ne_zero hρA₀⟩ =
        ClassGroup.mk0 ⟨A.num, mem_nonZeroDivisors_of_ne_zero hA₀⟩
    · -- ## case 1: `ρ` fixes the ideal class of `A`
      obtain ⟨x, hx0, hx⟩ := (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mp hcase
      refine h_asym A.num hA₀ (Units.mk0 x⁻¹ (inv_ne_zero hx0)) ?_
      have hux : (((Units.mk0 x⁻¹ (inv_ne_zero hx0) : Kˣ)) : K) = x⁻¹ := Units.val_mk0 _
      rw [hux]
      have h := congrArg (fun z => FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ * z) hx
      rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hx0,
        FractionalIdeal.spanSingleton_one, one_mul] at h
      exact h.trans (mul_comm _ _)
    · -- ## case 2: the class of `ρ · A` differs from that of `A`
      refine ⟨trivialModulus K, A.num, rfl, fun q => rfl, hA₀, fun q hq => absurd rfl hq,
        ⟨1, by rw [Units.val_one, FractionalIdeal.spanSingleton_one, mul_one]⟩, ?_⟩
      intro heq
      have hcrit := NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff K (trivialModulus K)
        (rhoIdeal ρ A.num) A.num hρA₀ hA₀ (fun q hq => absurd rfl hq)
        (fun q hq => absurd rfl hq)
      obtain ⟨α, hα0, _hαcong, hαeq⟩ := hcrit.mp heq
      apply hcase
      refine (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mpr
        ⟨α⁻¹, inv_ne_zero hα0, ?_⟩
      rw [hαeq, mul_left_comm, FractionalIdeal.spanSingleton_mul_spanSingleton,
        inv_mul_cancel₀ hα0, FractionalIdeal.spanSingleton_one, mul_one]
  obtain ⟨𝔪, I, hpos, hstab, hIne, hIcop, ⟨yI, hIy⟩, hasym⟩ := hmain
  -- ## augment the modulus by `𝔮` and `ρι𝔮`
  set 𝔪' : NK.NUV2.RouteB.Modulus K :=
    augmentModulus 𝔪 𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) with h𝔪'def
  have hpos' : 𝔪'.pos = ∅ := rfl
  have hstab' : ∀ q : HeightOneSpectrum (𝓞 K),
      𝔪'.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪'.exps q :=
    augmentModulus_stable ρ hρ2 hstab 𝔮
  have hsupp' : 𝔪'.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ≠ 0 :=
    augmentModulus_self_ne_zero 𝔪 𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
  have hle : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≤ 𝔪'.exps q :=
    fun q => le_augmentModulus 𝔪 𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) q
  have hUle : NK.NUV2.RouteB.CongSubgroup K 𝔪' ≤ NK.NUV2.RouteB.CongSubgroup K 𝔪 :=
    congSubgroup_antitone hle (by rw [hpos', hpos])
  -- ## Čebotarev in the ray class group of the augmented modulus
  obtain ⟨Q', hQ'm', hQ'c'⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass (K := K) 𝔪'
      (NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪') I)
  have hQ'm : 𝔪.exps Q' = 0 := by
    have h := hle Q'
    rw [hQ'm'] at h
    omega
  have hQ'ne : Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 := by
    intro h
    rw [h] at hQ'm'
    exact hsupp' hQ'm'
  -- ## the ray class equality descends to the original modulus
  have hcl : NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) Q'.asIdeal =
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I :=
    classOfIdeal_eq_of_le hUle hQ'c'
  -- ## `Q'` is not fixed by `ρ`
  have hnonfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' := by
    intro hfix
    exact hasym
      (classOfIdeal_rhoIdeal_eq_of_fixed ρ hρ2 𝔪 hpos hstab Q' hQ'm hfix I hIne hIcop hcl)
  -- ## the ideal class of `Q'` is the class of `A`
  have hQ'IA : ClassGroup.mk0 ⟨Q'.asIdeal, mem_nonZeroDivisors_of_ne_zero Q'.ne_bot⟩ =
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hIne⟩ := by
    have h2 : ClassGroup.mk K (Units.mk0 ((Q'.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
        (FractionalIdeal.coeIdeal_ne_zero.mpr Q'.ne_bot)) =
        ClassGroup.mk K (Units.mk0 ((I : FractionalIdeal (𝓞 K)⁰ K))
          (FractionalIdeal.coeIdeal_ne_zero.mpr hIne)) := by
      rw [← idealClassMap_ideleOfIdeal Q'.asIdeal Q'.ne_bot,
        ← idealClassMap_ideleOfIdeal I hIne]
      have hmem : (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * (NK.HeckeL.ideleOfIdeal K I) ∈
          NK.GlobalCFT.Idele.principalSubgroup K ⊔
            NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
        rw [NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_mk] at hcl
        exact (QuotientGroup.eq).mp hcl
      have hker : NK.GlobalCFT.Idele.principalSubgroup K ⊔
          NK.NUV2.RouteB.CongSubgroup K 𝔪 ≤
          (NK.GlobalCFT.IdeleClassGroup.idealClassMap K).ker := by
        rw [NK.GlobalCFT.IdeleClassGroup.ker_idealClassMap]
        exact sup_le le_sup_right (le_trans (congSubgroup_le_integralIdeles 𝔪) le_sup_left)
      have h1 : NK.GlobalCFT.IdeleClassGroup.idealClassMap K
          ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * (NK.HeckeL.ideleOfIdeal K I)) = 1 :=
        hker hmem
      rw [map_mul, map_inv] at h1
      exact inv_mul_eq_one.mp h1
    rw [← ClassGroup.mk_mk0 K ⟨Q'.asIdeal, mem_nonZeroDivisors_of_ne_zero Q'.ne_bot⟩,
      ← ClassGroup.mk_mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero hIne⟩]
    exact h2
  have hIA : ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hIne⟩ =
      ClassGroup.mk0 ⟨A.num, mem_nonZeroDivisors_of_ne_zero hA₀⟩ := by
    refine (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mpr
      ⟨(((yI : Kˣ) : K))⁻¹, inv_ne_zero (Units.ne_zero yI), ?_⟩
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (((yI : Kˣ) : K))⁻¹ *
          ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ (((yI : Kˣ) : K))⁻¹ *
          (((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            FractionalIdeal.spanSingleton (𝓞 K)⁰ ((yI : Kˣ) : K)) := by rw [hIy]
      _ = ((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (((yI : Kˣ) : K))⁻¹ *
            FractionalIdeal.spanSingleton (𝓞 K)⁰ ((yI : Kˣ) : K)) := by rw [mul_left_comm]
      _ = ((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * 1 := by
            rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
              inv_mul_cancel₀ (Units.ne_zero yI), FractionalIdeal.spanSingleton_one]
      _ = ((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by rw [mul_one]
  have hQ'A : ClassGroup.mk0 ⟨Q'.asIdeal, mem_nonZeroDivisors_of_ne_zero Q'.ne_bot⟩ =
      ClassGroup.mk0 ⟨A.num, mem_nonZeroDivisors_of_ne_zero hA₀⟩ :=
    hQ'IA.trans hIA
  -- ## the generator
  obtain ⟨x, hx0, hx⟩ := (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mp hQ'A
  refine ⟨Q', Units.mk0 (d * x⁻¹) (mul_ne_zero hd0 (inv_ne_zero hx0)), hnonfix, hQ'ne, ?_⟩
  rw [Units.val_mk0]
  have h1 : (Q'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
        ((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hx, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hx0,
      FractionalIdeal.spanSingleton_one, one_mul]
  calc (Q'.asIdeal : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
          ((A.num : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := h1
    _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
          (A * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) := by rw [hA_num]
    _ = A * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ d) := by
          rw [mul_left_comm]
    _ = A * FractionalIdeal.spanSingleton (𝓞 K)⁰ (x⁻¹ * d) := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ = A * FractionalIdeal.spanSingleton (𝓞 K)⁰ (d * x⁻¹) := by rw [mul_comm x⁻¹ d]

end Assembly

theorem primeInClassNotFixed {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (hA : A ≠ 0)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (y : Kˣ),
      Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' ∧
      Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∧
      ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        = A * FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (y : K)) := by
  classical
  have hρ1 : ρ ≠ 1 := by
    intro h
    exact hne (by rw [h, Commons.NumberTheory.NumberField.Completion.placeSmul_one])
  refine Work.SSGRoute.PinnedTwin.primeInClassNotFixed_aux ρ hρ2 (fun A₀ hA₀ u₀ hu₀ => ?_)
    A hA 𝔮 hne
  obtain ⟨𝔪, I, hpos, hstab, _hcopA, hIne, hIcop, hy, hasym⟩ :=
    Work.SSGRoute.PinnedTwin.exists_asym_ideal ρ hρ2 hρ1 A₀ hA₀ u₀ hu₀
  exact ⟨𝔪, I, hpos, hstab, hIne, hIcop, hy, hasym⟩

end Work.SSGRoute.PinnedTwin
