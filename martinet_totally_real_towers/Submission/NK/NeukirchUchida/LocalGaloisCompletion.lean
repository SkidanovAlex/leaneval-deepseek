import Mathlib
import Submission.NK.Mine.CompletionAPI
import Submission.NK.NeukirchUchida.exists_ringHom_adicCompletion_placeCompletion
import Submission.NK.NeukirchUchida.isSepClosed_completion
import Submission.NK.NeukirchUchida.rankOne_valuationSubringAtPrime_sepClosure
import Submission.NK.NeukirchUchida.rankOne_extensionValuation_completion

/-!
# The completion of a separable closure at a place: setup

Let `K` be a number field, `p` a finite place of `K`, `K'` a separable closure of `K` and `A` a
place of `K'` above `p` (a valuation subring whose restriction to `K` is the valuation ring of
`p`).  This file sets up the valued-field object used to compare the decomposition group of `A`
with the absolute Galois group of the `p`-adic completion of `K`:

* `placeCompletion A` : the completion of `K'` at the place `A`, a complete valued field (with
  value group `A.ValueGroup`) containing `K'` with dense image.
* `placeCompletionCoe A : K' →+* placeCompletion A` : the canonical embedding, whose underlying
  function is the coercion `(· : K' → placeCompletion A)`.
* `placeCompletionIntegers A` : the valuation ring of `placeCompletion A`.
* `isSepClosed_placeCompletion` : `placeCompletion A` is separably closed.
* `adicCompletionToPlaceCompletion p A hA : adicCompletion K p →+* placeCompletion A` : the
  canonical (continuous) ring homomorphism extending `K → K' → placeCompletion A`, where
  `hA : A.comap (algebraMap K K') = valuationSubringAtPrime K p`.
-/

open scoped Pointwise Valued

namespace NK.NeukirchUchida

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The completion of `K'` at the place `A`. -/
abbrev placeCompletion (A : ValuationSubring K') : Type _ :=
  Valuation.Completion A.valuation

/-- The canonical embedding of `K'` into its completion at `A`, as a ring homomorphism. -/
def placeCompletionCoe (A : ValuationSubring K') : K' →+* placeCompletion A :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv A.valuation).symm.toRingHom

@[simp]
theorem placeCompletionCoe_apply (A : ValuationSubring K') (x : K') :
    placeCompletionCoe A x = (x : placeCompletion A) := rfl

/-- The canonical `K'`-algebra structure on the completion of `K'` at `A`. -/
noncomputable instance instAlgebraPlaceCompletion (A : ValuationSubring K') :
    Algebra K' (placeCompletion A) :=
  (placeCompletionCoe A).toAlgebra

/-- The canonical `K`-algebra structure on the completion of `K'` at `A`. -/
noncomputable instance instAlgebraPlaceCompletionOverK (A : ValuationSubring K') :
    Algebra K (placeCompletion A) :=
  ((placeCompletionCoe A).comp (algebraMap K K')).toAlgebra

theorem algebraMap_placeCompletionCoe (A : ValuationSubring K') (c : K) :
    algebraMap K (placeCompletion A) c = placeCompletionCoe A (algebraMap K K' c) := rfl

/-- **In the completion of `K'` at `A`, the elements algebraic over `K` are exactly the
image of `K'`.**  (`K'` is a separable closure of `K`, so it is the algebraic closure of `K`
inside the completion.) -/
theorem isAlgebraic_iff_exists_placeCompletionCoe (A : ValuationSubring K')
    (x : placeCompletion A) :
    IsAlgebraic K x ↔ ∃ y : K', placeCompletionCoe A y = x := by
  haveI : IsSepClosed K' := IsSepClosure.sep_closed K
  have halg : algebraMap K (placeCompletion A) =
      (placeCompletionCoe A).comp (algebraMap K K') :=
    RingHom.ext (algebraMap_placeCompletionCoe A)
  constructor
  · intro hx
    have hint : IsIntegral K x := hx.isIntegral
    have hmonic : (minpoly K x).Monic := minpoly.monic hint
    have hsep : (minpoly K x).Separable :=
      PerfectField.separable_of_irreducible (minpoly.irreducible hint)
    have hroot : (minpoly K x).aeval x = 0 := minpoly.aeval K x
    have hq : ((minpoly K x).map (algebraMap K K')).Splits :=
      IsSepClosed.splits_codomain (f := algebraMap K K') (minpoly K x) hsep
    have hqc : (((minpoly K x).map (algebraMap K K')).map
        (placeCompletionCoe A)).Splits := hq.map _
    have hmonicc : (((minpoly K x).map (algebraMap K K')).map
        (placeCompletionCoe A)).Monic := (hmonic.map _).map _
    have heval : (((minpoly K x).map (algebraMap K K')).map
        (placeCompletionCoe A)).eval x = 0 := by
      rw [Polynomial.map_map, ← halg, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact hroot
    have hprod := hqc.eval_eq_prod_roots_of_monic hmonicc x
    rw [heval] at hprod
    obtain ⟨β, hβ, hxβ⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod.symm)
    rw [sub_eq_zero] at hxβ
    rw [hq.roots_map (placeCompletionCoe A)] at hβ
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.mp hβ
    exact ⟨y, hy.trans hxβ.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : IsAlgebraic K y := (Algebra.IsSeparable.isAlgebraic K K').isAlgebraic y
    obtain ⟨p, hp0, hp⟩ := hy
    refine ⟨p, hp0, ?_⟩
    rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map, ← Polynomial.map_map,
      Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hp, map_zero]

/-- The valuation ring of `placeCompletion A`. -/
abbrev placeCompletionIntegers (A : ValuationSubring K') : ValuationSubring (placeCompletion A) :=
  (Valued.v (R := placeCompletion A) (Γ₀ := A.ValueGroup)).valuationSubring

theorem mem_placeCompletionIntegers (A : ValuationSubring K') {x : placeCompletion A} :
    x ∈ placeCompletionIntegers A ↔
      Valued.v (R := placeCompletion A) (Γ₀ := A.ValueGroup) x ≤ 1 :=
  Iff.rfl

/-- The canonical embedding of `K'` into `placeCompletion A` has dense range. -/
theorem denseRange_placeCompletionCoe (A : ValuationSubring K') :
    DenseRange (placeCompletionCoe A) := by
  have h1 : DenseRange ((↑) : WithVal A.valuation → placeCompletion A) :=
    UniformSpace.Completion.denseRange_coe
  have h2 : Set.range ((↑) : WithVal A.valuation → placeCompletion A) =
      Set.range (placeCompletionCoe A) := by
    have hfun : (placeCompletionCoe A : K' → placeCompletion A) =
        (↑) ∘ (WithVal.equiv A.valuation).symm := rfl
    rw [hfun, Set.range_comp,
      Set.range_eq_univ.mpr (WithVal.equiv A.valuation).symm.surjective, Set.image_univ]
  simpa [DenseRange, h2] using h1

/-- `Valued.extensionValuation` on the completion of a valued ring has rank one as soon as the
valuation itself has rank one.  (Transfer of `RankOne` along the order isomorphism between the
value groups of `v` and of the valuation on `WithVal v`.) -/
def rankOne_withVal {R : Type*} [Field R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (h : v.RankOne) :
    (Valued.v (R := WithVal v) (Γ₀ := Γ₀)).RankOne := by
  haveI := h
  haveI hle : (Valued.v (R := WithVal v) (Γ₀ := Γ₀)).RankLeOne :=
    { hom' := (Valuation.RankOne.hom v).comp (WithVal.valueGroupOrderIso₀ v).toMonoidWithZeroHom
      strictMono' := (Valuation.RankOne.strictMono v).comp
        (WithVal.strictMono_valueGroupOrderIso₀ v) }
  haveI hnt : (Valued.v (R := WithVal v) (Γ₀ := Γ₀)).IsNontrivial := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial v
    refine ⟨WithVal.toVal v r, ?_, ?_⟩
    · rwa [WithVal.valued_toVal]
    · rwa [WithVal.valued_toVal]
  exact Valuation.RankOne.mk

/-- `placeCompletionIntegers A` contracts to `A` along the canonical embedding of `K'`. -/
theorem comap_placeCompletionIntegers (A : ValuationSubring K') :
    (placeCompletionIntegers A).comap (placeCompletionCoe A) = A := by
  ext x
  rw [ValuationSubring.mem_comap, mem_placeCompletionIntegers,
    ← ValuationSubring.valuation_le_one_iff A x]
  rw [show (placeCompletionCoe A x : placeCompletion A) =
      ((WithVal.toVal A.valuation x : WithVal A.valuation) : placeCompletion A) from rfl,
    Valued.valuedCompletion_apply (K := WithVal A.valuation) (Γ₀ := A.ValueGroup)
      (hv := (inferInstance : Valued (WithVal A.valuation) A.ValueGroup))
      (x := WithVal.toVal A.valuation x), WithVal.valued_toVal]

/-- `WithVal v` is separably closed if `R` is: the two are isomorphic as rings. -/
theorem isSepClosed_withVal {R : Type*} [Field R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [IsSepClosed R] : IsSepClosed (WithVal v) := by
  refine ⟨fun p hp => ?_⟩
  have h : (p.map (WithVal.equiv v).toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ (Polynomial.Separable.map hp)
  have h2 := h.map (WithVal.equiv v).symm.toRingHom
  rw [Polynomial.map_map,
    show ((WithVal.equiv v).symm.toRingHom.comp (WithVal.equiv v).toRingHom :
      WithVal v →+* WithVal v) = RingHom.id (WithVal v) from
      RingHom.ext fun x => (WithVal.equiv v).symm_apply_apply x,
    Polynomial.map_id] at h2
  exact h2

/-- **The completion of a separable closure at a place is separably closed.**
This is the only place where the rank one property of the extended place is used. -/
theorem isSepClosed_placeCompletion_of_rankOne [IsSepClosed K'] (A : ValuationSubring K')
    (h : Nonempty (Valuation.RankOne A.valuation)) : IsSepClosed (placeCompletion A) := by
  haveI : IsSepClosed (WithVal A.valuation) := isSepClosed_withVal A.valuation
  have h2 : (Valued.extensionValuation (K := WithVal A.valuation)
      (Γ₀ := A.ValueGroup)).RankOne :=
    (rankOne_extensionValuation_completion (rankOne_withVal A.valuation h.some)).some
  exact isSepClosed_completion (K := WithVal A.valuation) (Γ₀ := A.ValueGroup) h2

/-- **The completion of a separable closure at a place is separably closed.** -/
theorem isSepClosed_placeCompletion (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    IsSepClosed (placeCompletion A) :=
  haveI : IsSepClosed K' := IsSepClosure.sep_closed K
  isSepClosed_placeCompletion_of_rankOne A
    (rankOne_valuationSubringAtPrime_sepClosure p A hA)

/-- The comparison of the `p`-adic valuation of `K` with the restriction of `A`: the two
valuations of `K` have the same valuation ring. -/
theorem valuation_isEquiv_comap (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    (IsDedekindDomain.HeightOneSpectrum.valuation K p).IsEquiv
      (A.valuation.comap (algebraMap K K')) := by
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, ← hA]
  ext x
  simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
    ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]

/-- The map `K → K'` as a map of valued fields, `K` being given the `p`-adic valuation and `K'`
the valuation of the place `A`. -/
def placeWithValMap (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K') :
    WithVal (A.valuation.comap (algebraMap K K')) →+* WithVal A.valuation :=
  WithVal.map (A.valuation.comap (algebraMap K K')) A.valuation (algebraMap K K')

theorem valuation_placeWithValMap
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K') (x : WithVal (A.valuation.comap (algebraMap K K'))) :
    WithVal.valuation A.valuation (placeWithValMap p A x) =
      WithVal.valuation (A.valuation.comap (algebraMap K K')) x := by
  rw [placeWithValMap, WithVal.map_apply, WithVal.valuation_toVal, WithVal.valuation_apply_eq_ofVal]
  rfl

theorem uniformContinuous_placeWithValMap
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    UniformContinuous (placeWithValMap (K := K) (K' := K') p A) := by
  have halg : Algebra.IsAlgebraic K K' := Algebra.IsSeparable.isAlgebraic K K'
  refine Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal _
    (valuation_placeWithValMap (K := K) (K' := K') p A) ?_
  intro γ hγ
  obtain ⟨c, hc0, hcle⟩ :=
    exists_algebraMap_valuation_le_of_isAlgebraic A halg hγ
  exact ⟨WithVal.toVal _ c, by rw [WithVal.valuation_toVal]; exact (Valuation.pos_iff _).mpr hc0,
    by rw [WithVal.valuation_toVal]; exact hcle⟩

/-- The identity of `K` as a map of valued fields between two valuations with the same valuation
ring. -/
def placeWithValCongr (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K') :
    WithVal (IsDedekindDomain.HeightOneSpectrum.valuation K p) →+*
      WithVal (A.valuation.comap (algebraMap K K')) :=
  (WithVal.congr (IsDedekindDomain.HeightOneSpectrum.valuation K p)
    (A.valuation.comap (algebraMap K K')) (RingEquiv.refl K)).toRingHom

theorem uniformContinuous_placeWithValCongr
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    UniformContinuous (placeWithValCongr (K := K) (K' := K') p A) :=
  (valuation_isEquiv_comap p A hA).uniformContinuous_congr

/-- The completion map of a continuous ring homomorphism. -/
theorem continuous_completionMapRingHom {α β : Type*} [Ring α] [Ring β] [UniformSpace α]
    [UniformSpace β] [IsTopologicalRing α] [IsTopologicalRing β] [IsUniformAddGroup α]
    [IsUniformAddGroup β] (f : α →+* β) (hf : Continuous f) :
    Continuous (⇑(UniformSpace.Completion.mapRingHom (f := f) hf)) := by
  rw [UniformSpace.Completion.coe_mapRingHom]
  exact UniformSpace.Completion.continuous_map

/-- The canonical ring homomorphism from the `p`-adic completion of `K` to the completion of `K'`
at `A`.  It extends `K → K' → placeCompletion A` and is continuous for the two valuation
topologies. -/
noncomputable def adicCompletionToPlaceCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    IsDedekindDomain.HeightOneSpectrum.adicCompletion K p →+* placeCompletion A :=
  (UniformSpace.Completion.mapRingHom (f := placeWithValMap (K := K) (K' := K') p A)
      (uniformContinuous_placeWithValMap p A hA).continuous).comp
    ((UniformSpace.Completion.mapRingHom (f := placeWithValCongr (K := K) (K' := K') p A)
      (uniformContinuous_placeWithValCongr p A hA).continuous).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p).toRingHom)

theorem continuous_adicCompletionToPlaceCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    Continuous (adicCompletionToPlaceCompletion (K := K) (K' := K') p A hA) := by
  have h1 := continuous_completionMapRingHom (placeWithValMap (K := K) (K' := K') p A)
    (uniformContinuous_placeWithValMap p A hA).continuous
  have h2 := continuous_completionMapRingHom (placeWithValCongr (K := K) (K' := K') p A)
    (uniformContinuous_placeWithValCongr p A hA).continuous
  have h3 : Continuous
      (⇑(IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p).toRingHom) := by
    convert IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion
      (K := K) (v := p) using 1
    funext x
    exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply K p x
  have h4 : (⇑(adicCompletionToPlaceCompletion (K := K) (K' := K') p A hA)) =
      ⇑(UniformSpace.Completion.mapRingHom (f := placeWithValMap (K := K) (K' := K') p A)
          (uniformContinuous_placeWithValMap p A hA).continuous) ∘
        (⇑(UniformSpace.Completion.mapRingHom (f := placeWithValCongr (K := K) (K' := K') p A)
          (uniformContinuous_placeWithValCongr p A hA).continuous) ∘
        ⇑(IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p).toRingHom) := rfl
  rw [h4]
  exact h1.comp (h2.comp h3)

theorem adicCompletionToPlaceCompletion_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) (x : K) :
    adicCompletionToPlaceCompletion (K := K) (K' := K') p A hA
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) x) =
      placeCompletionCoe A (algebraMap K K' x) := by
  have hx1 : algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) x =
      (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  rw [hx1]
  have hF : ∀ y : WithVal (IsDedekindDomain.HeightOneSpectrum.valuation K p),
      (UniformSpace.Completion.mapRingHom (f := placeWithValCongr (K := K) (K' := K') p A)
        (uniformContinuous_placeWithValCongr p A hA).continuous) (↑y) =
        ↑(placeWithValCongr (K := K) (K' := K') p A y) := fun y =>
    UniformSpace.Completion.mapRingHom_coe _ y
  have hG : ∀ z : WithVal (A.valuation.comap (algebraMap K K')),
      (UniformSpace.Completion.mapRingHom (f := placeWithValMap (K := K) (K' := K') p A)
        (uniformContinuous_placeWithValMap p A hA).continuous) (↑z) =
        ↑(placeWithValMap (K := K) (K' := K') p A z) := fun z =>
    UniformSpace.Completion.mapRingHom_coe _ z
  have hcoe : (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p).toRingHom
      (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) =
      ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K p)).symm x) := by
    show (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p)
        (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) =
      ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K p)).symm x)
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_toCompletion, WithVal.equiv_symm_apply]
  have hcongr : ((WithVal.congr (IsDedekindDomain.HeightOneSpectrum.valuation K p)
        (A.valuation.comap (algebraMap K K')) (RingEquiv.refl K)).toRingHom)
        (WithVal.toVal (IsDedekindDomain.HeightOneSpectrum.valuation K p) x) =
      WithVal.toVal (A.valuation.comap (algebraMap K K')) x := by
    rw [show ((WithVal.congr (IsDedekindDomain.HeightOneSpectrum.valuation K p)
        (A.valuation.comap (algebraMap K K')) (RingEquiv.refl K)).toRingHom)
        (WithVal.toVal (IsDedekindDomain.HeightOneSpectrum.valuation K p) x) =
        WithVal.congr (IsDedekindDomain.HeightOneSpectrum.valuation K p)
          (A.valuation.comap (algebraMap K K')) (RingEquiv.refl K)
          (WithVal.toVal (IsDedekindDomain.HeightOneSpectrum.valuation K p) x) from rfl,
      WithVal.congr_apply, RingEquiv.refl_apply]
  show (UniformSpace.Completion.mapRingHom (f := placeWithValMap (K := K) (K' := K') p A)
        (uniformContinuous_placeWithValMap p A hA).continuous)
      ((UniformSpace.Completion.mapRingHom (f := placeWithValCongr (K := K) (K' := K') p A)
        (uniformContinuous_placeWithValCongr p A hA).continuous)
        ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p).toRingHom
          (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p))) =
      (placeCompletionCoe A (algebraMap K K' x) :
        Valuation.Completion A.valuation)
  rw [hcoe, hF, hG]
  simp only [placeWithValCongr, placeWithValMap, hcongr, WithVal.map_apply,
    WithVal.equiv_symm_apply, placeCompletionCoe_apply]

end

end NK.NeukirchUchida
