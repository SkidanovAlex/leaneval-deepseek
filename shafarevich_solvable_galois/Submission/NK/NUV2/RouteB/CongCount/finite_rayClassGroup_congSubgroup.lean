import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.NUV2.PrincipalUnitBall
import Submission.NK.NUV2.RouteB.RayModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the ray class group of a congruence subgroup

For a number field `K` and a modulus `𝔪` (finitely many congruence conditions at the finite
places, positivity at some real places) the ray class group

`𝕀 K ⧸ (Kˣ · U(𝔪))`

is finite, where `U(𝔪) = NK.NUV2.RouteB.CongSubgroup K 𝔪` is the congruence subgroup.

The proof is the classical one, organised as follows.

* The quotient of the idèles by the *integral* idèles `𝕌 = ∏_v 𝒪_vˣ` is the ideal class group
  (`NK.GlobalCFT.IdeleClassGroup.ker_idealClassMap`); the latter is finite.
* `U(𝔪)` has finite index in `𝕌`: the quotient `𝕌 ⧸ U(𝔪)` embeds into the finite group
  `∏_{q | 𝔪} (𝒪_qˣ ⧸ 1 + 𝔮^{𝔪_q}) × (SignTypeˣ)^{#pos}` (local principal units, and signs at the
  real places).
* Combining the two via the index multiplicativity
  `[𝕀 : Kˣ·U(𝔪)] = [Kˣ·𝕌 : Kˣ·U(𝔪)] · [𝕀 : Kˣ·𝕌]` gives the finiteness.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.NUV2.RouteB.CongCount

open NumberField IsDedekindDomain
open scoped Classical Pointwise ENNReal nonZeroDivisors NumberField
open NK.GlobalCFT (Idele IdeleClassGroup Place)

variable (K : Type) [Field K] [NumberField K]

/-! ## The local units as the units of `𝓞_q` -/

/-- The local units `𝒪_qˣ = ↥(Place.localUnits K (Place.ofFinite q))`, regarded as the ring units
of the ring of integers of the `q`-adic completion. -/
noncomputable def localUnitsToRingUnits (q : HeightOneSpectrum (𝓞 K)) :
    ↥(Place.localUnits K (Place.ofFinite q)) →* (q.adicCompletionIntegers K)ˣ :=
  (Submonoid.unitsEquivUnitsType ((q.adicCompletionIntegers K).toSubmonoid)).toMonoidHom.comp
    { toFun := fun u => ⟨(u : (q.adicCompletion K)ˣ), by
          show (u : (q.adicCompletion K)ˣ) ∈ ((q.adicCompletionIntegers K).toSubmonoid).units
          exact u.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }

@[simp] theorem coe_localUnitsToRingUnits (q : HeightOneSpectrum (𝓞 K))
    (u : ↥(Place.localUnits K (Place.ofFinite q))) :
    ((localUnitsToRingUnits K q u : (q.adicCompletionIntegers K)ˣ) : q.adicCompletion K)
      = (u : (q.adicCompletion K)ˣ) := rfl

/-- The `q`-component of an integral idèle, as a local unit. -/
noncomputable def localUnitsComponent (q : HeightOneSpectrum (𝓞 K)) :
    ↥(Idele.integralIdeles K) →* ↥(Place.localUnits K (Place.ofFinite q)) where
  toFun x := ⟨x.1 (Place.ofFinite q), x.2 (Place.ofFinite q) (Place.isFinite_ofFinite q)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- **Membership in the local congruence subgroup.**  An element of the local units is congruent
to `1` modulo the `m q`-th power of the maximal ideal iff it satisfies `IsCongAt`. -/
theorem mem_principalUnitBall_iff_isCongAt (m : HeightOneSpectrum (𝓞 K) → ℕ)
    (q : HeightOneSpectrum (𝓞 K)) {u : (q.adicCompletion K)ˣ}
    (hu : u ∈ Place.localUnits K (Place.ofFinite q)) :
    localUnitsToRingUnits K q ⟨u, hu⟩ ∈ NK.NUV2.principalUnitBall K q (m q)
      ↔ IsCongAt K m q u := by
  rw [NK.NUV2.mem_principalUnitBall_iff_val, IsCongAt]
  rw [coe_localUnitsToRingUnits]

/-- `IsCongAt` holds automatically at the primes outside the support of the modulus, for a local
unit. -/
theorem isCongAt_of_exp_eq_zero {m : HeightOneSpectrum (𝓞 K) → ℕ}
    {q : HeightOneSpectrum (𝓞 K)} (h0 : m q = 0) {u : (q.adicCompletion K)ˣ}
    (hu : Valued.v (u : q.adicCompletion K) = 1) : IsCongAt K m q u := by
  rw [IsCongAt, h0]
  refine le_trans (Valuation.map_sub _ _ _) (le_of_eq ?_)
  rw [hu, Valuation.map_one, max_self]
  norm_num

/-- The congruence subgroup of a modulus consists of idèles which are local units at every
finite place. -/
theorem congSubgroup_le_integralIdeles (𝔪 : Modulus K) :
    CongSubgroup K 𝔪 ≤ Idele.integralIdeles K := by
  intro x hx
  rw [Idele.mem_integralIdeles]
  intro v hv
  obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hv
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  exact ((Modulus.mem_congSubgroup_iff.mp hx).1 q).1

/-! ## Signs at the real places -/

/-- The sign of the component of an idèle at a real place, as a group homomorphism to the group
`SignTypeˣ = {±1}`. -/
noncomputable def signHomReal (w : InfinitePlace K) (hw : w.IsReal) : Idele K →* SignTypeˣ :=
  (Units.map (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    ((Units.map ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
        |>.toMonoidHom)).comp (Idele.eval (K := K) (Place.ofInfinite w)))

/-- Being in the kernel of `signHomReal` is positivity of the real component. -/
theorem mem_ker_signHomReal_iff (w : InfinitePlace K) (hw : w.IsReal) (x : Idele K) :
    x ∈ (signHomReal K w hw).ker ↔
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((x (Place.ofInfinite w) : w.Completion)) := by
  rw [MonoidHom.mem_ker, ← Units.val_eq_one]
  simp only [signHomReal, MonoidHom.comp_apply, Units.coe_map]
  exact sign_eq_one_iff

/-! ## The congruence homomorphism on the integral idèles -/

/-- The reduction of the `q`-component of an integral idèle modulo the `𝔪 q`-th power of the
maximal ideal, as a homomorphism to the units of the finite ring `𝓞_q ⧸ 𝔮^{𝔪 q}`. -/
noncomputable def quotientComponent (𝔪 : Modulus K) (q : HeightOneSpectrum (𝓞 K)) :
    ↥(Idele.integralIdeles K) →*
      ((q.adicCompletionIntegers K) ⧸
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ (𝔪.exps q))ˣ :=
  (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers K)
      ^ (𝔪.exps q))).toMonoidHom).comp
    ((localUnitsToRingUnits K q).comp (localUnitsComponent K q))

/-- The kernel of the reduction is the local congruence subgroup. -/
theorem quotientComponent_eq_one_iff (𝔪 : Modulus K) (q : HeightOneSpectrum (𝓞 K))
    (x : ↥(Idele.integralIdeles K)) :
    quotientComponent K 𝔪 q x = 1 ↔
      localUnitsToRingUnits K q (localUnitsComponent K q x) ∈
        NK.NUV2.principalUnitBall K q (𝔪.exps q) := by
  rw [NK.NUV2.principalUnitBall]
  exact MonoidHom.mem_ker.symm

/-- **The congruence homomorphism**: the residues of the local unit components of an integral idèle
at the primes dividing the modulus, together with the signs at the real places in `𝔪.pos`. -/
noncomputable def congHom (𝔪 : Modulus K) :
    ↥(Idele.integralIdeles K) →*
      ((∀ q : {q : HeightOneSpectrum (𝓞 K) // q ∈ 𝔪.supportFinset},
          ((q.1.adicCompletionIntegers K) ⧸
            IsLocalRing.maximalIdeal (q.1.adicCompletionIntegers K) ^ (𝔪.exps q.1))ˣ) ×
        (∀ w : {w : InfinitePlace K // w.IsReal ∧ w ∈ 𝔪.pos}, SignTypeˣ)) :=
  (MonoidHom.pi fun q : {q : HeightOneSpectrum (𝓞 K) // q ∈ 𝔪.supportFinset} =>
      quotientComponent K 𝔪 q.1).prod
    (MonoidHom.pi fun w : {v : InfinitePlace K // v.IsReal ∧ v ∈ 𝔪.pos} =>
      (signHomReal K w.1 w.2.1).comp (Idele.integralIdeles K).subtype)

/-- **The kernel of the congruence homomorphism**: the kernel of `congHom` on the integral idèles
is exactly the congruence subgroup `U(𝔪)`. -/
theorem ker_congHom (𝔪 : Modulus K) :
    (congHom K 𝔪).ker = (CongSubgroup K 𝔪).subgroupOf (Idele.integralIdeles K) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Modulus.mem_congSubgroup_iff]
  constructor
  · intro h
    have h1 : ∀ q : {q : HeightOneSpectrum (𝓞 K) // q ∈ 𝔪.supportFinset},
        IsCongAt K 𝔪.exps q.1 (x.1 (Place.ofFinite q.1)) := by
      intro q
      have hq : quotientComponent K 𝔪 q.1 x = 1 := by
        have h' : (congHom K 𝔪 x).1 = 1 := congrArg Prod.fst h
        exact congrFun h' q
      have := (quotientComponent_eq_one_iff K 𝔪 q.1 x).mp hq
      exact (mem_principalUnitBall_iff_isCongAt K 𝔪.exps q.1
        (x.2 (Place.ofFinite q.1) (Place.isFinite_ofFinite q.1))).mp this
    have h2 : ∀ w : {w : InfinitePlace K // w.IsReal ∧ w ∈ 𝔪.pos},
        0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal w.2.1)
          ((x.1 (Place.ofInfinite w.1) : w.1.Completion)) := by
      intro w
      have hw : signHomReal K w.1 w.2.1 (x.1) = 1 := by
        have h' : (congHom K 𝔪 x).2 = 1 := congrArg Prod.snd h
        exact congrFun h' w
      exact (mem_ker_signHomReal_iff K w.1 w.2.1 (x.1)).mp (MonoidHom.mem_ker.mpr hw)
    refine ⟨fun q => ⟨?_, ?_⟩, fun w hw hpos => ?_⟩
    · exact (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp
        (x.2 (Place.ofFinite q) (Place.isFinite_ofFinite q))
    · by_cases hq : q ∈ 𝔪.supportFinset
      · exact h1 ⟨q, hq⟩
      · exact isCongAt_of_exp_eq_zero K (Modulus.exps_eq_zero_of_not_mem 𝔪 hq)
          ((Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp
            (x.2 (Place.ofFinite q) (Place.isFinite_ofFinite q)))
    · exact h2 ⟨w, hw, hpos⟩
  · intro h
    have hq : ∀ q : {q : HeightOneSpectrum (𝓞 K) // q ∈ 𝔪.supportFinset},
        quotientComponent K 𝔪 q.1 x = 1 := by
      intro q
      rw [quotientComponent_eq_one_iff]
      exact (mem_principalUnitBall_iff_isCongAt K 𝔪.exps q.1
        (x.2 (Place.ofFinite q.1) (Place.isFinite_ofFinite q.1))).mpr (h.1 q.1).2
    have hw : ∀ w : {w : InfinitePlace K // w.IsReal ∧ w ∈ 𝔪.pos},
        signHomReal K w.1 w.2.1 (x.1) = 1 := by
      intro w
      exact MonoidHom.mem_ker.mp ((mem_ker_signHomReal_iff K w.1 w.2.1 (x.1)).mpr
        (h.2 w.1 w.2.1 w.2.2))
    show congHom K 𝔪 x = 1
    refine Prod.ext (funext fun q => hq q) (funext fun w => hw w)

/-! ## Finiteness -/

/-- The quotient of the idèles by the integral idèles and the principal idèles is the ideal class
group, hence finite. -/
theorem finite_quotient_integralIdeles :
    Finite (Idele K ⧸ (Idele.principalSubgroup K ⊔ Idele.integralIdeles K)) := by
  have h : Finite (Idele K ⧸ (IdeleClassGroup.idealClassMap K).ker) :=
    (QuotientGroup.quotientKerEquivRange (IdeleClassGroup.idealClassMap K)).finite_iff.mpr
      (inferInstance : Finite (IdeleClassGroup.idealClassMap K).range)
  simpa [IdeleClassGroup.ker_idealClassMap K, sup_comm] using h

/-- **The quotient of the integral idèles by the congruence subgroup is finite.** -/
theorem finite_quotient_integralIdeles_congSubgroup (𝔪 : Modulus K) :
    Finite (Idele.integralIdeles K ⧸ (CongSubgroup K 𝔪).subgroupOf (Idele.integralIdeles K)) := by
  classical
  haveI hfin : Finite ((∀ q : {q : HeightOneSpectrum (𝓞 K) // q ∈ 𝔪.supportFinset},
        ((q.1.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal (q.1.adicCompletionIntegers K) ^ (𝔪.exps q.1))ˣ) ×
      (∀ w : {w : InfinitePlace K // w.IsReal ∧ w ∈ 𝔪.pos}, SignTypeˣ)) := by
    haveI : Fintype {q : HeightOneSpectrum (𝓞 K) // q ∈ 𝔪.supportFinset} := inferInstance
    haveI : ∀ q : {q : HeightOneSpectrum (𝓞 K) // q ∈ 𝔪.supportFinset},
        Fintype (((q.1.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal (q.1.adicCompletionIntegers K) ^ (𝔪.exps q.1))ˣ) := by
      intro q
      haveI : Finite ((q.1.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal (q.1.adicCompletionIntegers K) ^ (𝔪.exps q.1)) :=
        Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
          K q.1 (𝔪.exps q.1)
      exact Fintype.ofFinite _
    exact Finite.of_fintype _
  have h : Finite (Idele.integralIdeles K ⧸ (congHom K 𝔪).ker) :=
    (QuotientGroup.quotientKerEquivRange (congHom K 𝔪)).finite_iff.mpr
      (inferInstance : Finite (congHom K 𝔪).range)
  simpa [ker_congHom K 𝔪] using h

/-- **Finiteness of the ray class group of a congruence subgroup.** -/
theorem finite_rayClassGroup_congSubgroup (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) :
    Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) := by
  classical
  set A : Subgroup (Idele K) := Idele.principalSubgroup K ⊔ CongSubgroup K 𝔪 with hA
  set K₀ : Subgroup (Idele K) := Idele.principalSubgroup K ⊔ Idele.integralIdeles K with hK₀
  show Finite (Idele K ⧸ (Idele.principalSubgroup K ⊔ CongSubgroup K 𝔪))
  rw [← hA]
  haveI h𝕌 : Finite (Idele.integralIdeles K ⧸
      (CongSubgroup K 𝔪).subgroupOf (Idele.integralIdeles K)) :=
    finite_quotient_integralIdeles_congSubgroup K 𝔪
  have hAK₀ : A ≤ K₀ := by
    rw [hA, hK₀]
    exact sup_le_sup le_rfl (congSubgroup_le_integralIdeles K 𝔪)
  -- The quotient `K₀ ⧸ (A ∩ K₀)` is finite: it is a quotient of `𝕌 ⧸ (U(𝔪) ∩ 𝕌)`.
  haveI hK₀A : Finite (↥K₀ ⧸ A.subgroupOf K₀) := by
    haveI : A.Normal := Subgroup.normal_of_isMulCommutative A
    let incl : ↥(Idele.integralIdeles K) →* ↥K₀ :=
      { toFun := fun x => ⟨x.1, by rw [hK₀]; exact Subgroup.mem_sup_right x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' _ _ := Subtype.ext rfl }
    let ψ : ↥(Idele.integralIdeles K) →* ↥K₀ ⧸ A.subgroupOf K₀ :=
      (QuotientGroup.mk' (A.subgroupOf K₀)).comp incl
    have hker : (CongSubgroup K 𝔪).subgroupOf (Idele.integralIdeles K) ≤ ψ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      refine (QuotientGroup.eq_one_iff (incl x)).mpr ?_
      rw [Subgroup.mem_subgroupOf]
      have hxA : x.1 ∈ A := by
        rw [hA]
        exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)
      exact hxA
    have hsurj : Function.Surjective ψ := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf K₀) y
      obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup.mp (by rw [← hK₀]; exact g.2)
      refine ⟨⟨u, hu⟩, ?_⟩
      have hmem : (incl ⟨u, hu⟩)⁻¹ * g ∈ A.subgroupOf K₀ := by
        rw [Subgroup.mem_subgroupOf]
        show (Subgroup.subtype K₀) ((incl ⟨u, hu⟩)⁻¹ * g) ∈ A
        have h1 : (Subgroup.subtype K₀) (incl ⟨u, hu⟩) = u := rfl
        have h2 : (Subgroup.subtype K₀) g = g.1 := rfl
        rw [map_mul, map_inv, h1, h2, ← hku]
        have h3 : u⁻¹ * (k * u) = k := by
          rw [mul_comm u⁻¹ (k * u), mul_assoc, mul_inv_cancel, mul_one]
        rw [h3, hA]
        exact Subgroup.mem_sup_left hk
      exact QuotientGroup.eq.mpr hmem
    exact Finite.of_surjective (QuotientGroup.lift _ ψ hker)
      (QuotientGroup.lift_surjective_of_surjective _ ψ hsurj hker)
  -- Index arithmetic: `[𝕀 : A] = [K₀ : A] · [𝕀 : K₀]`.
  have hK₀idx : K₀.index ≠ 0 :=
    (Subgroup.finiteIndex_iff_finite_quotient.mpr (by rw [hK₀]; exact finite_quotient_integralIdeles K)).index_ne_zero
  haveI : (A.subgroupOf K₀).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : A.IsFiniteRelIndex K₀ :=
    (Subgroup.isFiniteRelIndex_iff_finiteIndex (H := A) (K := K₀)).mpr inferInstance
  have hrel : A.relIndex K₀ ≠ 0 := Subgroup.relIndex_ne_zero
  have hidx : A.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (H := A) (K := K₀) hAK₀]
    exact mul_ne_zero hrel hK₀idx
  haveI : A.FiniteIndex := ⟨hidx⟩
  exact Subgroup.finite_quotient_of_finiteIndex

end NK.NUV2.RouteB.CongCount
