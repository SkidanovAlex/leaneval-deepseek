import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

/-! ### Elementary finite-place computations

The proof of `ideleOfIdeal_smul_cong` is a pointwise computation at the finite places: the two
idèles `ρ • 𝔦(Q)` and `𝔦(ρQ)` agree (`= 1`) at every finite place different from the conjugate
place `ρQ`, and at `ρQ` they differ by a *local unit* (the ratio of the two uniformizers), which is
congruent to `1` modulo the level `0` at that place.  The lemmas below isolate the three ingredients
of this computation: the `q`-adic count of a prime ideal, the trivial congruence condition at level
`0`, and the transport of the `Gal`-action on idèles through the canonical local isomorphism.
-/

/-- The `v`-adic count of the prime ideal of `w` is `1` at `v = w`. -/
private lemma count_asIdeal_self {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  classical
  rw [FractionalIdeal.count_maximal K v v, if_pos rfl]

/-- The `v`-adic count of the prime ideal of a *different* prime is `0`. -/
private lemma count_asIdeal_of_ne {K : Type} [Field K] [NumberField K]
    {v w : HeightOneSpectrum (𝓞 K)} (h : v ≠ w) :
    FractionalIdeal.count K v (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  rw [FractionalIdeal.count_maximal K v w, if_neg (fun hc => h hc.symm)]

/-- The idèle `1` is congruent to `1` modulo every level. -/
private lemma isCongAt_one {K : Type} [Field K] [NumberField K]
    (m : HeightOneSpectrum (𝓞 K) → ℕ) (q : HeightOneSpectrum (𝓞 K)) :
    NK.NUV2.RouteB.IsCongAt K m q (1 : (q.adicCompletion K)ˣ) := by
  rw [NK.NUV2.RouteB.IsCongAt]
  have hzero : Valued.v (((1 : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1) = 0 := by simp
  rw [hzero]
  exact zero_le

/-- A local *unit* at the finite place `q` (i.e. a unit of the valuation ring) is congruent to `1`
modulo the level `0`, since both `z` and `1` are integral and hence so is `z - 1`. -/
private lemma isCongAt_of_valued_eq_one {K : Type} [Field K] [NumberField K]
    (m : HeightOneSpectrum (𝓞 K) → ℕ) (q : HeightOneSpectrum (𝓞 K)) (hmq : m q = 0)
    (z : (q.adicCompletion K)ˣ) (hz : Valued.v (z : q.adicCompletion K) = 1) :
    NK.NUV2.RouteB.IsCongAt K m q z := by
  rw [NK.NUV2.RouteB.IsCongAt, hmq]
  have hzint : (z : q.adicCompletion K) ∈ q.adicCompletionIntegers K := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q]
    exact le_of_eq hz
  have hsub : (z : q.adicCompletion K) - 1 ∈ q.adicCompletionIntegers K :=
    sub_mem hzint (one_mem _)
  have h := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q).mp hsub
  simpa using h

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- **The value of `ρ • 𝔦(I)` at a finite place**, in terms of the local uniformizer at the
preimage place `ρ⁻¹q` (against which the canonical local isomorphism `K_q ≃+* K_{ρ⁻¹q}` is
applied).  This is `Idele.smul_apply` together with the definition of `ideleOfFun`. -/
private lemma smul_ideleOfIdeal_ofFinite (ρ : K ≃ₐ[k] K) (I : Ideal (𝓞 K))
    (q : HeightOneSpectrum (𝓞 K)) :
    (ρ • NK.HeckeL.ideleOfIdeal K I) (NK.GlobalCFT.Place.ofFinite q)
      = Units.map (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q)).symm.toMonoidHom
          (NK.GlobalCFT.IdeleClassGroup.unifUnit K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
            ^ (FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
                (I : FractionalIdeal (𝓞 K)⁰ K))) := by
  rw [NK.GlobalCFT.Idele.smul_apply]; rfl

/-- The canonical local isomorphism `q.adicCompletion K ≃+* (ρ⁻¹q).adicCompletion K` is an
isometry: it preserves the `Valued.v` (equivalently, the `q`-adic valuation). -/
private lemma valued_symm_adicCongr (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K))
    (y : (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K) :
    Valued.v ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y) = Valued.v y := by
  have h := NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_valued ρ⁻¹ q
    ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- The `q`-adic valuation of `ρ • 𝔦(I)` at the finite place `q` is `exp (-(count at ρ⁻¹q))`. -/
private lemma valued_smul_ideleOfIdeal (ρ : K ≃ₐ[k] K) (I : Ideal (𝓞 K))
    (q : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((ρ • NK.HeckeL.ideleOfIdeal K I) (NK.GlobalCFT.Place.ofFinite q)) :
        q.adicCompletion K)
      = WithZero.exp (-(FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
          (I : FractionalIdeal (𝓞 K)⁰ K))) := by
  rw [smul_ideleOfIdeal_ofFinite, Units.coe_map]
  refine (Eq.trans ?_ (NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow
    (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
    (FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
      (I : FractionalIdeal (𝓞 K)⁰ K))))
  exact valued_symm_adicCongr ρ q _

/-- The `Gal(K/k)`-action on finite places is compatible with the inverse. -/
private lemma smulHeightOneSpectrum_inv_self (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K)) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum ρ (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) = q := by
  rw [NK.GlobalCFT.Galois.smulHeightOneSpectrum_mul, mul_inv_cancel,
    NK.GlobalCFT.Inclusion.smulHeightOneSpectrum_one]

/-- The finite place of `Q` is the preimage of `Q` under `ρ` transported by `ρ⁻¹`. -/
private lemma smulHeightOneSpectrum_inv_Q (ρ : K ≃ₐ[k] K) (Q : HeightOneSpectrum (𝓞 K)) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q) = Q := by
  rw [NK.GlobalCFT.Galois.smulHeightOneSpectrum_mul, inv_mul_cancel,
    NK.GlobalCFT.Inclusion.smulHeightOneSpectrum_one]

theorem ideleOfIdeal_smul_cong {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (𝔪 : NK.NUV2.RouteB.Modulus K) (hpos : 𝔪.pos = ∅)
    (hstab : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hQ : 𝔪.exps Q = 0) :
    (ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal) *
      (NK.HeckeL.ideleOfIdeal K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q).asIdeal)⁻¹
      ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  classical
  -- Replace the `Commons`-version of the Galois transport of places by the `Place`-version, with
  -- which the idèle computations are set up.
  rw [NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ Q]
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff]
  refine ⟨fun q => ?_, ?_⟩
  · by_cases hq : q = NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q
    · -- ## The distinguished place `q = ρQ`
      subst hq
      have hQ' : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹
          (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q) = Q := smulHeightOneSpectrum_inv_Q ρ Q
      have hQexp : 𝔪.exps (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q) = 0 := by
        have h := hstab Q
        rw [NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ Q] at h
        exact h.trans hQ
      have hv1 : Valued.v (((ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal)
          (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q))) :
            (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).adicCompletion K) = WithZero.exp (-1) := by
        have h := valued_smul_ideleOfIdeal ρ Q.asIdeal
          (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q)
        rw [hQ', count_asIdeal_self] at h
        exact h
      have hv2 : Valued.v (((NK.HeckeL.ideleOfIdeal K
          (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).asIdeal)
          (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q))) :
            (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).adicCompletion K) = WithZero.exp (-1) := by
        change Valued.v (((NK.GlobalCFT.IdeleClassGroup.unifUnit K
              (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q)
              ^ (FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q)
                  ((NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).asIdeal : FractionalIdeal (𝓞 K)⁰ K))
              : ((NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).adicCompletion K)ˣ) :
            (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).adicCompletion K)) = WithZero.exp (-1)
        rw [count_asIdeal_self, zpow_one,
          NK.GlobalCFT.IdeleClassGroup.valued_unifUnit]
      have hv : Valued.v ((((ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal) *
            (NK.HeckeL.ideleOfIdeal K
              (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).asIdeal)⁻¹)
            (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q))) :
            (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).adicCompletion K) = 1 := by
        rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul, map_mul, NK.GlobalCFT.Idele.inv_apply,
          Units.val_inv_eq_inv_val, map_inv₀, hv1, hv2]
        exact mul_inv_cancel₀ (by simp)
      exact ⟨hv, isCongAt_of_valued_eq_one (𝔪.exps) _ hQexp _ hv⟩
    · -- ## Every other place: both factors are `1`
      have hq' : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q ≠ Q := by
        intro h
        apply hq
        rw [← smulHeightOneSpectrum_inv_self ρ q, h]
      have hP1 : (ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal)
          (NK.GlobalCFT.Place.ofFinite q) = 1 := by
        rw [smul_ideleOfIdeal_ofFinite, count_asIdeal_of_ne hq', zpow_zero, map_one]
      have hP2 : (NK.HeckeL.ideleOfIdeal K
          (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).asIdeal)
          (NK.GlobalCFT.Place.ofFinite q) = 1 := by
        change NK.GlobalCFT.IdeleClassGroup.unifUnit K q
            ^ (FractionalIdeal.count K q
              ((NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).asIdeal : FractionalIdeal (𝓞 K)⁰ K)) = 1
        rw [count_asIdeal_of_ne hq, zpow_zero]
      have hxq : ((ρ • NK.HeckeL.ideleOfIdeal K Q.asIdeal) *
            (NK.HeckeL.ideleOfIdeal K
              (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q).asIdeal)⁻¹)
            (NK.GlobalCFT.Place.ofFinite q) = 1 := by
        rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hP1, hP2,
          one_mul, inv_one]
      exact ⟨by rw [hxq, Units.val_one, map_one], by rw [hxq]; exact isCongAt_one (𝔪.exps) q⟩
  · -- ## The archimedean part is vacuous: `𝔪.pos = ∅`
    intro w hw hmem
    simp [hpos] at hmem

end Work.SSGRoute.PinnedTwin
