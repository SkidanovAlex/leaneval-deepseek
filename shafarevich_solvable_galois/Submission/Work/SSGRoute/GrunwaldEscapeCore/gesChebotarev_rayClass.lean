import Mathlib
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Work.SSGRoute.GrunwaldEscapeCore.NKRayClassImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.GesImports
import Submission.Work.SSGRoute.ssg8Chebotarev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev for the ray class group of a modulus

The target `Work.SSGRoute.GrunwaldEscapeCore.gesChebotarev_rayClass`: for every modulus `𝔪` of a
number field `K` and every class `c` in the ray class group `𝕀 K ⧸ (Kˣ · U(𝔪))` there is a prime
ideal `𝔮` with `𝔪.exps 𝔮 = 0` (i.e. `𝔮` does not divide the modulus) whose ray class is `c`.

This is Čebotarev's theorem applied to the ray class field of the modulus.  The route:

* `U(𝔪)` is open in `𝕀 K` (`ges_isOpen_congSubgroup`) and has finite index
  (`NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup`);
* the image `V = U(𝔪)·Kˣ/Kˣ` therefore has an *abelian* class field `L` with
  `N_{L/K} C_L = V` and `[L : K] = [C_K : V]` (`ges_exists_abelian_classField`);
* for an abelian `L/K` the idèlic Artin map `art : 𝕀 K →* Gal(L/K)` exists, kills `Kˣ` and the
  idèlic norms, is surjective and satisfies the Frobenius normalisation outside a finite set of
  primes (`ges_exists_artinMap_of_abelian`);
* Artin reciprocity identifies `𝕀 K ⧸ (Kˣ · art.ker)` (hence, since `N_{L/K}C_L = V`, also the ray
  class group of `𝔪`) with `Gal(L/K)`, and Čebotarev (`NK.Chebotarev`) produces a prime with the
  prescribed Frobenius.
-/

open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative

namespace Work.SSGRoute.GrunwaldEscapeCore

open NK.GlobalCFT

/-! ## The local congruence ball is open -/

theorem ges_isOpen_localCongBall {K : Type} [Field K] [NumberField K]
    (q : HeightOneSpectrum (RingOfIntegers K)) (e : ℕ) :
    IsOpen {u : (q.adicCompletion K)ˣ |
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((u : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)
        ≤ WithZero.exp (-(e : ℤ))} := by
  have hcont : Continuous fun u : (q.adicCompletion K)ˣ =>
      (((u : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1) :=
    Units.continuous_val.sub continuous_const
  rw [show {u : (q.adicCompletion K)ˣ |
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (((u : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)
          ≤ WithZero.exp (-(e : ℤ))}
      = (fun u : (q.adicCompletion K)ˣ =>
          (((u : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)) ⁻¹'
          {z : q.adicCompletion K |
            Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z
              ≤ WithZero.exp (-(e : ℤ))} from rfl]
  exact (NK.UchidaKummer.Approximation.isOpen_val_le_exp_neg (K := K) q e).preimage hcont

/-- A finite prime's congruence ball `{u | IsCongAt K m q u}` is open in `(K_q)ˣ`. -/
theorem ges_isOpen_congBall {K : Type} [Field K] [NumberField K]
    (m : HeightOneSpectrum (RingOfIntegers K) → ℕ)
    (q : HeightOneSpectrum (RingOfIntegers K)) :
    IsOpen {u : (q.adicCompletion K)ˣ | NK.NUV2.RouteB.IsCongAt K m q u} := by
  have h := ges_isOpen_localCongBall (K := K) q (m q)
  unfold NK.NUV2.RouteB.IsCongAt
  exact h

/-- A finite intersection of open sets, in "forall" form. -/
theorem ges_isOpen_forall_mem_finset {X : Type*} [TopologicalSpace X] {α : Type*}
    (s : Finset α) (f : α → Set X) (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen {x : X | ∀ i ∈ s, x ∈ f i} := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hset : {x : X | ∀ i ∈ insert a s, x ∈ f i} =
          f a ∩ {x : X | ∀ i ∈ s, x ∈ f i} := by
        ext x
        rw [Set.mem_setOf_eq, Finset.forall_mem_insert, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hset]
      exact (h a (Finset.mem_insert_self a s)).inter
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The congruence subgroup `U(𝔪)` is open in the idèle group.**  It contains the intersection
of three open sets: the local units at all finite places (`Work.SSGRoute.isOpen_idelesUnitsOutside`),
the finitely many congruence balls at the support of `𝔪` (`ges_isOpen_congBall`, a preimage of the
open ball `{z | v z ≤ exp (-e)}` under the continuous map `u ↦ u - 1`), and the finitely many
positivity conditions at the real places of `𝔪.pos`; being a subgroup, it is then open. -/
theorem ges_isOpen_congSubgroup {K : Type} [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) :
    IsOpen ((NK.NUV2.RouteB.CongSubgroup K 𝔪 : Subgroup (Idele K)) : Set (Idele K)) := by
  classical
  -- the three open pieces
  have h1 : IsOpen {x : Idele K |
      ∀ v : Place K, v ∉ {v : Place K | v.IsInfinite} → x v ∈ Place.localUnits K v} :=
    Work.SSGRoute.isOpen_idelesUnitsOutside (K := K) _
  have h2 : IsOpen {x : Idele K | ∀ q ∈ 𝔪.supportFinset,
      NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (x (Place.ofFinite q))} :=
    ges_isOpen_forall_mem_finset 𝔪.supportFinset _
      (fun q _ => (ges_isOpen_congBall (K := K) 𝔪.exps q).preimage
        (f := fun x : Idele K => x (Place.ofFinite q))
        (RestrictedProduct.continuous_eval (Place.ofFinite q)))
  let f : InfinitePlace K → Set (Idele K) := fun w =>
    if h : w.IsReal then
      {x : Idele K | 0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h)
        ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)}
    else ⊤
  let s : Finset (InfinitePlace K) := Finset.univ.filter (fun w => w.IsReal ∧ w ∈ 𝔪.pos)
  have hfopen : ∀ w ∈ s, IsOpen (f w) := by
    intro w _
    by_cases h : w.IsReal
    · rw [show f w = {x : Idele K |
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)} from dif_pos h]
      have hcont : Continuous fun x : Idele K =>
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) :=
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
            h).continuous.comp
          (Units.continuous_val.comp (RestrictedProduct.continuous_eval (Place.ofInfinite w)))
      exact isOpen_Ioi.preimage hcont
    · rw [show f w = ⊤ from dif_neg h]; exact isOpen_univ
  have h3 : IsOpen {x : Idele K | ∀ w ∈ s, x ∈ f w} :=
    ges_isOpen_forall_mem_finset s f hfopen
  -- the box is contained in `U(𝔪)` and contains `1`
  have hsub : ({x : Idele K | ∀ v : Place K, v ∉ {v : Place K | v.IsInfinite} →
        x v ∈ Place.localUnits K v} ∩
      ({x : Idele K | ∀ q ∈ 𝔪.supportFinset,
        NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (x (Place.ofFinite q))} ∩
       {x : Idele K | ∀ w ∈ s, x ∈ f w})) ⊆
      ((NK.NUV2.RouteB.CongSubgroup K 𝔪 : Subgroup (Idele K)) : Set (Idele K)) := by
    rintro x ⟨hx1, hx2, hx3⟩
    change x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪
    rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff]
    refine ⟨fun q => ⟨?_, ?_⟩, ?_⟩
    · have h := hx1 (Place.ofFinite q) (by simp)
      rwa [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h
    · by_cases hq : q ∈ 𝔪.supportFinset
      · exact hx2 q hq
      · have h0 := 𝔪.exps_eq_zero_of_not_mem hq
        have hu : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((x (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K)) = 1 := by
          have h := hx1 (Place.ofFinite q) (by simp)
          rwa [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h
        exact NK.NUV2.RouteB.CongCount.isCongAt_of_exp_eq_zero K h0 hu
    · intro w hw hpos
      have hws : w ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw, hpos⟩
      have hxw := hx3 w hws
      rw [show f w = {x : Idele K |
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)} from dif_pos hw] at hxw
      exact hxw
  have hone : (1 : Idele K) ∈ ({x : Idele K | ∀ v : Place K, v ∉ {v : Place K | v.IsInfinite} →
        x v ∈ Place.localUnits K v} ∩
      ({x : Idele K | ∀ q ∈ 𝔪.supportFinset,
        NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (x (Place.ofFinite q))} ∩
       {x : Idele K | ∀ w ∈ s, x ∈ f w})) := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rcases v with w | q
      · exact Place.mem_localUnits_ofInfinite
      · rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
        simp
    · intro q _
      unfold NK.NUV2.RouteB.IsCongAt
      simp
    · intro w hw
      obtain ⟨-, hwr, -⟩ := Finset.mem_filter.mp hw
      rw [show f w = {x : Idele K |
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hwr)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)} from dif_pos hwr]
      simp
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((h1.inter (h2.inter h3)).mem_nhds hone) hsub)

/-! ## The abelian class field of an open finite-index subgroup -/

/-- **The existence theorem of global class field theory in abelian form.**  Every open subgroup of
finite index of `C_K` is the norm subgroup `N_{L/K} C_L` of an *abelian* extension `L / K` of degree
`[L : K] = [C_K : V]`.  This is `Work.SSGRoute.CFTSide.classField_exists_of_index` together with
the abelian subextension `Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le`.

The statement is kept in the "anonymous instance binder" form of `classField_exists_of_index` so
that it can be consumed by `obtain ⟨L, _, _, _, _, _, _, hNorm, hrank⟩`. -/
theorem ges_exists_abelian_classField :
    ∀ {K : Type} [Field K] [NumberField K] (V : Subgroup (IdeleClassGroup K)),
      V.FiniteIndex → IsOpen (V : Set (IdeleClassGroup K)) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
        (_ : FiniteDimensional K L) (_ : IsGalois K L)
        (_ : IsMulCommutative (L ≃ₐ[K] L)),
        Idele.normClassSubgroup K L = V ∧ Module.finrank K L = V.index := by
  intro K _ _ V hVfin hVopen
  have hne : V.index ≠ 0 := Subgroup.finiteIndex_iff.mp hVfin
  obtain ⟨L, hFL, hNL, hAL, hFDL, hGalL, hNormL, hrankL⟩ :=
    Work.SSGRoute.CFTSide.classField_exists_of_index (K := K) V.index
      (Nat.pos_of_ne_zero hne) V hVfin hVopen rfl
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra K L := hAL
  letI : FiniteDimensional K L := hFDL
  haveI : IsGalois K L := hGalL
  obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
    Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
      NK.CFTLib.fundamentalClassElement (K := K) (L := L) V (le_of_eq hNormL)
  haveI : FiniteDimensional K ↥A := inferInstance
  haveI : NumberField ↥A := Commons.NumberTheory.NumberField.numberField_of_intermediateField A
  haveI : IsGalois K ↥A := hAgal
  haveI : IsMulCommutative (↥A ≃ₐ[K] ↥A) := hAcomm
  have hNA : Idele.normClassSubgroup K ↥A = V := by
    refine le_antisymm hAle ?_
    have h := Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥A) (M := L)
    rwa [hNormL] at h
  refine ⟨↥A, inferInstance, inferInstance, inferInstance, inferInstance, hAgal, hAcomm, hNA, ?_⟩
  rw [← hNA, NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
    NK.CFTLib.fundamentalClassElement (K := K) (L := ↥A)]
  exact (IsGalois.card_aut_eq_finrank K ↥A).symm.trans
    (Nat.card_congr (Abelianization.equivOfComm (H := (↥A ≃ₐ[K] ↥A))).toEquiv)

/-! ## The idèlic Artin map of an abelian extension -/

/-- **The idèlic Artin map of a finite abelian extension.**  There is a monoid homomorphism
`art : 𝕀 K →* Gal(L/K)` and a finite set `S` of primes of `K` such that

* every prime outside `S` is unramified in `L / K`,
* `art` kills the principal idèles,
* `art` kills the idèlic norms `N_{L/K} 𝕀 L`,
* `art` maps the idèle of a prime `𝔭 ∉ S` to the Frobenius at `𝔭`,
* `art` is surjective.

This is the public idèlic Artin map `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` (from the
ideal-theoretic reciprocity law `NK.CFTLib.artinReciprocityIdeal_proved`) with the norm clause
added, which is `NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin` together with
`NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup`. -/
theorem ges_exists_artinMap_of_abelian {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    ∃ (art : Idele K →* Gal(L/K)) (S : Finset (NK.HeckeL.PrimeIdeal K)),
      (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭 ∉ S →
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭) ∧
      (∀ a : Kˣ, art (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1) ∧
      (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭 ∉ S →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ∧
      Function.Surjective art := by
  obtain ⟨m, hm, hram, hprinc⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨art, hAgree, hPrin, hFrob, hSurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin hcomm m hm hram hprinc U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hadjN : ∀ y : Idele L, ∃ d : Lˣ,
      Idele.normIdeleHom K L (y * Idele.principalIdele L d) ∈ U := by
    intro y
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm y
    exact ⟨d, by rw [hUeq]; exact hd⟩
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hAgree]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcomm m hm hram hprinc U hU hadj hadjN y
  refine ⟨art, NK.CFTLib.Arl.primesDividing (K := K) m hm, ?_, hPrin, hnorm, ?_, hSurj⟩
  · intro 𝔭 h𝔭
    have hm𝔭 : (m : RingOfIntegers K) ∉ 𝔭.asIdeal :=
      fun h => h𝔭 ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm 𝔭).mpr h)
    intro 𝔮 _
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal 𝔮.asIdeal
      (Gal(L/K))]
    exact hram 𝔭 hm𝔭
  · intro 𝔭 h𝔭
    exact hFrob 𝔭 (fun h => h𝔭 ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm 𝔭).mpr h))

/-- Two subgroups, one contained in the other, with the same finite index, are equal. -/
theorem ges_eq_of_le_of_index_eq {G : Type*} [Group G] {H K : Subgroup G} (hle : H ≤ K)
    (hidx : H.index = K.index) (hne : K.index ≠ 0) : H = K := by
  have h1 : H.relIndex K * K.index = H.index := Subgroup.relIndex_mul_index hle
  rw [hidx] at h1
  have h2 : H.relIndex K * K.index = 1 * K.index := by rw [h1, one_mul]
  have h3 : H.relIndex K = 1 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h2
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h3)

/-- **Čebotarev for the ray class group of an open finite-index subgroup.**  For an open subgroup
`U ≤ 𝕀 K` with finite ray class group `𝕀 K ⧸ (Kˣ · U)`, every class of the ray class group is the
class of a prime ideal outside any prescribed finite set of primes.

This is Čebotarev's density theorem for the class field of `U`: by the existence theorem
(`ges_exists_abelian_classField`) `U` has an abelian class field `L` with `N_{L/K}C_L = U·Kˣ/Kˣ`,
the idèlic Artin map of `L/K` (`ges_exists_artinMap_of_abelian`) identifies `Gal(L/K)` with
`𝕀 K ⧸ (Kˣ · U)`, and Čebotarev (`NK.Chebotarev`) supplies a prime with the prescribed Frobenius
class. -/
theorem ges_exists_prime_class {K : Type} [Field K] [NumberField K]
    (U : Subgroup (Idele K)) (hUopen : IsOpen (U : Set (Idele K)))
    (hUfin : Finite (IdeleClassGroup.rayClassGroup K U))
    (T : Finset (HeightOneSpectrum (RingOfIntegers K)))
    (c : IdeleClassGroup.rayClassGroup K U) :
    ∃ 𝔮 : HeightOneSpectrum (RingOfIntegers K),
      𝔮 ∉ T ∧ NK.HeckeL.classOfIdeal K U 𝔮.asIdeal = c := by
  classical
  haveI : Finite (IdeleClassGroup.rayClassGroup K U) := hUfin
  set V : Subgroup (IdeleClassGroup K) := U.map (IdeleClassGroup.mk K) with hVdef
  have hVopen : IsOpen (V : Set (IdeleClassGroup K)) := by
    rw [hVdef, Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe (N := Idele.principalSubgroup K) _ hUopen
  let ψ : Idele K →* (IdeleClassGroup K ⧸ V) :=
    (QuotientGroup.mk' V).comp (IdeleClassGroup.mk K)
  -- the kernel of `ψ = U ⧸ (U ∩ Kˣ)` is `Kˣ · U`
  have hker_eq : ψ.ker = Idele.principalSubgroup K ⊔ U := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz1 : (QuotientGroup.mk' V) (IdeleClassGroup.mk K z) = 1 := hz
      have hmem : IdeleClassGroup.mk K z ∈ V := (QuotientGroup.eq_one_iff _).mp hz1
      obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hmem
      have hzu : IdeleClassGroup.mk K (u⁻¹ * z) = 1 := by
        rw [map_mul, map_inv, ← hu', inv_mul_cancel]
      have hmemA : u⁻¹ * z ∈ Idele.principalSubgroup K := (QuotientGroup.eq_one_iff _).mp hzu
      have h1 : u ∈ Idele.principalSubgroup K ⊔ U := Subgroup.mem_sup_right hu
      have h2 : u⁻¹ * z ∈ Idele.principalSubgroup K ⊔ U := Subgroup.mem_sup_left hmemA
      have hmul : u * (u⁻¹ * z) = z := by group
      rw [← hmul]
      exact Subgroup.mul_mem _ h1 h2
    · intro z hz
      obtain ⟨a, ha, u, hu, rfl⟩ := Subgroup.mem_sup.mp hz
      have ha1 : IdeleClassGroup.mk K a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      have hu1 : ψ u = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
      have hψa : ψ a = 1 := by
        show (QuotientGroup.mk' V) (IdeleClassGroup.mk K a) = 1
        rw [ha1, map_one]
      show ψ (a * u) = 1
      rw [map_mul, hψa, hu1, one_mul]
  have hker_le : Idele.principalSubgroup K ⊔ U ≤ ψ.ker := hker_eq ▸ le_rfl
  let ψbar : IdeleClassGroup.rayClassGroup K U →* (IdeleClassGroup K ⧸ V) :=
    QuotientGroup.lift (Idele.principalSubgroup K ⊔ U) ψ hker_le
  have hVfin : V.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    refine Finite.of_surjective ψbar ?_
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective V y
    obtain ⟨w, rfl⟩ := IdeleClassGroup.mk_surjective K z
    refine ⟨QuotientGroup.mk' (Idele.principalSubgroup K ⊔ U) w, ?_⟩
    rw [show ψbar (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ U) w) = ψ w from
      QuotientGroup.lift_mk _ hker_le w]
    rfl
  -- the abelian class field of `V`
  obtain ⟨L, hFL, hNL, hAL, hFDL, hGalL, hCommL, hNormL, hrankL⟩ :=
    ges_exists_abelian_classField (K := K) V hVfin hVopen
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra K L := hAL
  letI : FiniteDimensional K L := hFDL
  haveI : IsGalois K L := hGalL
  haveI : IsMulCommutative (L ≃ₐ[K] L) := hCommL
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => mul_comm' a b
  -- the idèlic Artin map
  obtain ⟨art, S, hSunr, hprin, hnorm, hfrob, hsurj⟩ :=
    ges_exists_artinMap_of_abelian (K := K) (L := L) hcomm
  have hAker : Idele.principalSubgroup K ≤ art.ker := by
    intro z hz
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hz
    exact MonoidHom.mem_ker.mpr (hprin a)
  let artBar : IdeleClassGroup K →* Gal(L/K) :=
    QuotientGroup.lift (Idele.principalSubgroup K) art hAker
  have hartBar : ∀ z : Idele K, artBar (IdeleClassGroup.mk K z) = art z :=
    fun z => QuotientGroup.lift_mk _ _ z
  have hartBarsurj : Function.Surjective artBar := by
    intro σ
    obtain ⟨z, hz⟩ := hsurj σ
    exact ⟨IdeleClassGroup.mk K z, (hartBar z).trans hz⟩
  -- the index of `art.ker` in `𝕀 K` is `[L : K]`
  have hidx_art : ((art.ker).map (IdeleClassGroup.mk K)).index = V.index := by
    rw [Subgroup.index_map_eq (art.ker) (IdeleClassGroup.mk_surjective K) (by
      rw [Work.SSGRoute.ker_mk_eq_principal]; exact hAker)]
    calc art.ker.index = Nat.card (Idele K ⧸ art.ker) := Subgroup.index_eq_card _
      _ = Nat.card ↥art.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange art).toEquiv
      _ = Nat.card (Gal(L/K)) := by
          rw [MonoidHom.range_eq_top.mpr hsurj]
          exact Nat.card_congr (Subgroup.topEquiv (G := Gal(L/K))).toEquiv
      _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
      _ = V.index := hrankL
  have hNle : V ≤ (art.ker).map (IdeleClassGroup.mk K) := by
    rw [← hNormL]
    intro n hn
    change n ∈ (Idele.normImage K L).map (IdeleClassGroup.mk K) at hn
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hz
    have hzy : z = Idele.normIdeleHom K L y :=
      Idele.ext fun v => (hy v).trans (Idele.normIdeleHom_apply (K := K) (L := L) y v).symm
    rw [hzy, hnorm y]
  have himg : (art.ker).map (IdeleClassGroup.mk K) = V :=
    (ges_eq_of_le_of_index_eq hNle hidx_art.symm (by
      rw [hidx_art]
      exact Subgroup.finiteIndex_iff.mp hVfin)).symm
  -- Artin reciprocity identifies `C_K ⧸ V` with `Gal(L/K)`
  have hVker : V ≤ artBar.ker := by
    intro v hv
    rw [← himg] at hv
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hv
    exact (hartBar z).trans (MonoidHom.mem_ker.mp hz)
  let Ψ : (IdeleClassGroup K ⧸ V) →* Gal(L/K) := QuotientGroup.lift V artBar hVker
  have hΨ_apply : ∀ z : Idele K, Ψ (QuotientGroup.mk (IdeleClassGroup.mk K z)) = art z :=
    fun z => (QuotientGroup.lift_mk V hVker (IdeleClassGroup.mk K z)).trans (hartBar z)
  have hΨker : Ψ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective V y
    obtain ⟨w, rfl⟩ := IdeleClassGroup.mk_surjective K z
    have hy1 : Ψ (QuotientGroup.mk (IdeleClassGroup.mk K w)) = 1 := MonoidHom.mem_ker.mp hy
    have hw : w ∈ art.ker := by
      rw [MonoidHom.mem_ker, ← hΨ_apply w]
      exact hy1
    exact (QuotientGroup.eq_one_iff (IdeleClassGroup.mk K w)).mpr
      (himg ▸ Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
  have hΨinj : Function.Injective Ψ := (MonoidHom.ker_eq_bot_iff Ψ).mp hΨker
  have hΨsurj : Function.Surjective Ψ := by
    intro σ
    obtain ⟨z, hz⟩ := hartBarsurj σ
    exact ⟨QuotientGroup.mk z, (QuotientGroup.lift_mk V hVker z).trans hz⟩
  let Ψe : (IdeleClassGroup K ⧸ V) ≃* Gal(L/K) := MulEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  have hΨe_apply : ∀ z : Idele K, Ψe (QuotientGroup.mk (IdeleClassGroup.mk K z)) = art z := by
    intro z
    exact (MulEquiv.ofBijective_apply Ψ ⟨hΨinj, hΨsurj⟩
      (QuotientGroup.mk (IdeleClassGroup.mk K z))).trans (hΨ_apply z)
  -- represent the class `c` and prescribe the Frobenius
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Idele.principalSubgroup K ⊔ U) c
  have hLF : NK.Chebotarev.AbelianLFunctions K L :=
    NK.NUV2.abelianLFunctions_of_freeInputs NK.NUV2.heckeInput_proved
      (NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal
        NK.CFTLib.artinReciprocityIdeal_proved) K L hcomm
  have hinf : ({𝔭 : HeightOneSpectrum (RingOfIntegers K) | NK.Chebotarev.IsFrobAtPrime
      (K := K) (L := L) 𝔭 (Ψe (QuotientGroup.mk (IdeleClassGroup.mk K x)))}).Infinite :=
    NK.Chebotarev.infinite_setOf_isFrobAtPrime_of_abelianLFunctions hcomm hLF _
  have hex : ∃ 𝔮 : HeightOneSpectrum (RingOfIntegers K), 𝔮 ∉ S ∧ 𝔮 ∉ T ∧
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔮
        (Ψe (QuotientGroup.mk (IdeleClassGroup.mk K x))) := by
    by_contra hcon
    refine hinf ((S ∪ T).finite_toSet.subset fun 𝔭 h𝔭 => ?_)
    by_contra h𝔭T
    exact hcon ⟨𝔭, (fun h => h𝔭T (Finset.mem_union_left T h)),
      (fun h => h𝔭T (Finset.mem_union_right S h)), h𝔭⟩
  obtain ⟨𝔮, h𝔮S, h𝔮T, h𝔮frob⟩ := hex
  refine ⟨𝔮, h𝔮T, ?_⟩
  have h𝔮unr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮 := by
    by_contra h
    exact h (hSunr 𝔮 h𝔮S)
  have hfrob𝔮 : NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔮 =
      Ψe (QuotientGroup.mk (IdeleClassGroup.mk K x)) :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔮 h𝔮unr _).mp h𝔮frob
  have h1 : Ψe (QuotientGroup.mk (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮))) =
      Ψe (QuotientGroup.mk (IdeleClassGroup.mk K x)) := by
    rw [hΨe_apply (NK.HeckeL.ideleOfPrime K 𝔮), hfrob 𝔮 h𝔮S, hfrob𝔮]
  have h2 : QuotientGroup.mk (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮)) =
      QuotientGroup.mk (IdeleClassGroup.mk K x) := hΨinj h1
  have hψ2 : ψ (NK.HeckeL.ideleOfPrime K 𝔮) = ψ x := h2
  have hmem : (NK.HeckeL.ideleOfPrime K 𝔮)⁻¹ * x ∈ Idele.principalSubgroup K ⊔ U := by
    rw [← hker_eq, MonoidHom.mem_ker]
    rw [map_mul, map_inv, hψ2, inv_mul_cancel]
  have hmul : (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ U)) ((NK.HeckeL.ideleOfPrime K 𝔮)⁻¹ * x) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  have hgoal : (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ U)) (NK.HeckeL.ideleOfPrime K 𝔮) =
      (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ U)) x := by
    have h1 : (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ U)) (NK.HeckeL.ideleOfPrime K 𝔮)⁻¹ *
        (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ U)) x = 1 := by
      rw [← map_mul]
      exact hmul
    rw [map_inv] at h1
    exact inv_mul_eq_one.mp h1
  rw [NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_mk,
    NK.GlobalCFTdeep.SecondInequality.ideleOfIdeal_prime_eq_ideleOfPrime]
  exact hgoal

theorem gesChebotarev_rayClass {K : Type} [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :
    ∃ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps 𝔮 = 0 ∧
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔮.asIdeal = c := by
  obtain ⟨𝔮, h𝔮T, h𝔮c⟩ := ges_exists_prime_class (K := K)
    (NK.NUV2.RouteB.CongSubgroup K 𝔪)
    (ges_isOpen_congSubgroup 𝔪)
    (NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup K 𝔪)
    𝔪.supportFinset c
  exact ⟨𝔮, 𝔪.exps_eq_zero_of_not_mem h𝔮T, h𝔮c⟩

end Work.SSGRoute.GrunwaldEscapeCore
