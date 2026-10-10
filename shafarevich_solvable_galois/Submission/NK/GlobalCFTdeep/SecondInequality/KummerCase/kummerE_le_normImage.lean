import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormFinite
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormInfinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `kummerE ≤ N_{L/K} 𝕀_L` in the Kummer case

Milne, *Class Field Theory*, VII §6: for `L / K` cyclic of prime degree `p` with `ζ_p ∈ K`, the
subgroup `E = ∏_{v ∈ S} K_v^{×p} · ∏_{q ∈ T} K_q^× · ∏_{v ∉ S ∪ T} U_v` of the idèle group is
contained in the norm group `N_{L/K} 𝕀_L`, where

* `S` contains the archimedean places, the places above `p`, and the ramified places, and
* the places `q ∈ T` split completely in `L`.

This file reduces the statement to its local ingredients.  For each place `v` of `K` we choose a
place `w` of `L` above it and a local unit `u` at `w` whose local norm is the `v`-component of the
given idèle; the resulting idèle of `L` has the prescribed norm.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The place of `K` below a place of `L`, and single-place idèles -/

/-- The place of `K` below a place of `L`. -/
noncomputable def placeUnder (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Place L → Place K
  | Sum.inl w => Sum.inl (w.comap (algebraMap K L))
  | Sum.inr q => Sum.inr (HeightOneSpectrum.under (𝓞 K) q)

@[simp] theorem placeUnder_ofInfinite (w : InfinitePlace L) :
    placeUnder K L (Place.ofInfinite w) = Place.ofInfinite (w.comap (algebraMap K L)) := rfl

@[simp] theorem placeUnder_ofFinite (q : HeightOneSpectrum (𝓞 L)) :
    placeUnder K L (Place.ofFinite q) =
      Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q) := rfl

theorem placeUnder_comap_liesOver (w : InfinitePlace L) :
    InfinitePlace.LiesOver w (w.comap (algebraMap K L)) := by
  rw [show InfinitePlace.LiesOver w (w.comap (algebraMap K L)) =
     AbsoluteValue.LiesOver w.1 (w.comap (algebraMap K L)).1 from rfl]
  exact AbsoluteValue.LiesOver.mk rfl

theorem placeUnder_asIdeal_liesOver (q : HeightOneSpectrum (𝓞 L)) :
    q.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) q).asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal]
  exact Ideal.LiesOver.mk rfl

theorem liesOver_placeUnder (w : Place L) : Place.LiesOver w (placeUnder K L w) := by
  cases w with
  | inl w' => exact Place.liesOver_ofInfinite (placeUnder_comap_liesOver w')
  | inr q => exact Place.liesOver_ofFinite (placeUnder_asIdeal_liesOver q)

theorem placeUnder_eq_of_liesOver {w : Place L} {v : Place K} (h : Place.LiesOver w v) :
    placeUnder K L w = v := by
  cases w with
  | inl w' =>
      cases v with
      | inl v' =>
          rcases h with ⟨w'', v'', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
          · obtain rfl := Sum.inl.inj h1
            obtain rfl := Sum.inl.inj h2
            haveI := h3
            rw [placeUnder_ofInfinite, InfinitePlace.LiesOver.comap_eq w' v']
          · exact absurd h1 Sum.inl_ne_inr
      | inr Q =>
          rcases h with ⟨w'', v'', h1, h2, h3⟩ | ⟨q, Q', h1, h2, h3⟩
          · exact absurd h2 Sum.inr_ne_inl
          · exact absurd h1 Sum.inl_ne_inr
  | inr q =>
      cases v with
      | inl v' =>
          rcases h with ⟨w'', v'', h1, h2, h3⟩ | ⟨q', Q, h1, h2, h3⟩
          · exact absurd h1 Sum.inr_ne_inl
          · exact absurd h2 Sum.inl_ne_inr
      | inr Q =>
          rcases h with ⟨w'', v'', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
          · exact absurd h1 Sum.inr_ne_inl
          · obtain rfl := Sum.inr.inj h1
            obtain rfl := Sum.inr.inj h2
            rw [placeUnder_ofFinite]
            congr 1
            exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, h3.over])

/-- The idèle of `L` which is `u` at the single place `w` and `1` everywhere else. -/
noncomputable def singleIdele (w : Place L) (u : (Place.localField L w)ˣ) : Idele L := by
  classical
  exact ⟨fun w' => if h : w' = w then h.symm ▸ u else 1, by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton w) ?_
    intro w' hw'
    by_cases h : w' = w
    · exact h ▸ Set.mem_singleton w
    · exact absurd (by simp only [dif_neg h]; exact Subgroup.one_mem _) hw'⟩

@[simp] theorem singleIdele_apply_self (w : Place L) (u : (Place.localField L w)ˣ) :
    singleIdele w u w = u := by
  classical
  show (if h : w = w then h.symm ▸ u else 1) = u
  rw [dif_pos rfl]

theorem singleIdele_apply_of_ne {w w' : Place L} (h : w' ≠ w) (u : (Place.localField L w)ˣ) :
    singleIdele w u w' = 1 := by
  classical
  show (if h : w' = w then h.symm ▸ u else 1) = 1
  rw [dif_neg h]

/-! ## The norm of a single-place idèle -/

theorem normIdeleFun_singleIdele_ofFinite (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (u : (q.adicCompletion L)ˣ) :
    Idele.normIdeleFun K L (singleIdele (Place.ofFinite q) u) (Place.ofFinite Q) =
      Place.localNormFinite q Q hq u := by
  classical
  rw [Idele.normIdeleFun_ofFinite]
  rw [Finset.prod_eq_single_of_mem
    ⟨q, (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q)).mpr hq⟩
    (Finset.mem_attach _ _) ?_]
  · rw [singleIdele_apply_self]
  · intro b _ hbne
    have hbq : b.1 ≠ q := fun h => hbne (Subtype.ext h)
    have hne : Place.ofFinite b.1 ≠ Place.ofFinite q :=
      fun h => hbq (Place.ofFinite_inj.mp h)
    rw [singleIdele_apply_of_ne hne u]
    exact map_one _

theorem normIdeleFun_singleIdele_ofInfinite (v : InfinitePlace K) (w : InfinitePlace L)
    [hw : w.LiesOver v] (u : w.Completionˣ) :
    Idele.normIdeleFun K L (singleIdele (Place.ofInfinite w) u) (Place.ofInfinite v) =
      Place.localNormInfinite w v u := by
  classical
  rw [Idele.normIdeleFun_ofInfinite]
  rw [Finset.prod_eq_single_of_mem
    ⟨w, (Place.mem_fiberInfinite (K := K) (L := L) (v := v) (w := w)).mpr hw⟩
    (Finset.mem_attach _ _) ?_]
  · rw [singleIdele_apply_self]
  · intro b _ hbne
    have hbw : b.1 ≠ w := fun h => hbne (Subtype.ext h)
    have hne : Place.ofInfinite b.1 ≠ Place.ofInfinite w :=
      fun h => hbw (Place.ofInfinite_inj.mp h)
    rw [singleIdele_apply_of_ne hne u]
    exact map_one _

/-- The norm of an idèle at a place `v` only depends on the components at the places of `L`
above `v`. -/
theorem normIdeleFun_congr_of_liesOver {y y' : Idele L} {v : Place K}
    (h : ∀ w : Place L, Place.LiesOver w v → y w = y' w) :
    Idele.normIdeleFun K L y v = Idele.normIdeleFun K L y' v := by
  cases v with
  | inl v' =>
      rw [Idele.normIdeleFun_ofInfinite, Idele.normIdeleFun_ofInfinite]
      refine Finset.prod_congr rfl fun b hb => ?_
      have hb' : (b.1 : InfinitePlace L).LiesOver v' :=
        (Place.mem_fiberInfinite (K := K) (L := L) (v := v') (w := b.1)).mp b.2
      rw [h (Place.ofInfinite b.1) (Place.liesOver_ofInfinite hb')]
  | inr Q =>
      rw [Idele.normIdeleFun_ofFinite, Idele.normIdeleFun_ofFinite]
      refine Finset.prod_congr rfl fun b hb => ?_
      have hb' : b.1.asIdeal.LiesOver Q.asIdeal :=
        (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := b.1)).mp b.2
      rw [h (Place.ofFinite b.1) (Place.liesOver_ofFinite hb')]


/-! ## The local surjectivity statements at the places outside `S` and inside `T` -/

section Surjective

variable [IsGalois K L]

/-- At a finite place `q` of `L` above `Q` at which the extension is unramified *and* of inertia
degree one (i.e. `q` splits completely over `Q`), the local norm `L_qˣ → K_Qˣ` is surjective. -/
theorem localNormFinite_surjective_of_ramificationIdx_eq_one_and_inertiaDeg_eq_one
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (he : q.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : q.asIdeal.inertiaDeg (𝓞 K) = 1)
    (x : (Q.adicCompletion K)ˣ) :
    ∃ u : (q.adicCompletion L)ˣ, Place.localNormFinite q Q hq u = x := by
  have hrange := Commons.NumberTheory.NumberField.Completion.norm_range_of_ramificationIdx_eq_one
    (K := K) (L := L) Q q hq he
  simp only [hf, pow_one] at hrange
  obtain ⟨y, hy⟩ : ∃ y : q.adicCompletion L,
      Algebra.norm (Q.adicCompletion K) y = (x : Q.adicCompletion K) := by
    rw [hrange]
    exact ⟨(x : Q.adicCompletion K), rfl⟩
  have hyne : y ≠ 0 := by
    haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
      Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
    haveI : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
      Module.Free.of_divisionRing (Q.adicCompletion K) (q.adicCompletion L)
    exact Algebra.norm_ne_zero_iff.mp (by rw [hy]; exact Units.ne_zero x)
  refine ⟨Units.mk0 y hyne, ?_⟩
  rw [Place.localNormFinite]
  refine Units.ext ?_
  rw [Units.coe_map, Units.val_mk0]
  exact hy

/-- At a finite place `q` of `L` above `Q` at which the extension is unramified, the local norm
maps the local units of `L_q` onto the local units of `K_Q`. -/
theorem localNormFinite_units_surjective_of_ramificationIdx_eq_one
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (x : (Q.adicCompletion K)ˣ) (hx : x ∈ Place.localUnits K (Place.ofFinite Q)) :
    ∃ u : (q.adicCompletion L)ˣ, u ∈ Place.localUnits L (Place.ofFinite q) ∧
      Place.localNormFinite q Q hq u = x := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at hx
  obtain ⟨x', hx'⟩ :=
    (Commons.NumberTheory.NumberField.Completion.norm_adicCompletionIntegers_surjective_of_ramificationIdx_eq_one
      Q q hq hunr x hx :
      ∃ x' : (q.adicCompletionIntegers L)ˣ,
        Algebra.norm (Q.adicCompletion K)
          ((x' : q.adicCompletionIntegers L) : q.adicCompletion L) =
          (x : Q.adicCompletion K))
  refine ⟨Units.map (algebraMap (q.adicCompletionIntegers L)
      (q.adicCompletion L)).toMonoidHom x', ?_, ?_⟩
  · rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    show Valued.v (R := q.adicCompletion L)
      (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
        (x' : q.adicCompletionIntegers L)) = 1
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (R := 𝓞 L) (K := L) (v := q) (a := (x' : q.adicCompletionIntegers L))).mp x'.isUnit
  · rw [Place.localNormFinite]
    refine Units.ext ?_
    simpa using hx'

end Surjective


/-! ## The assembled idèle of `L` -/

/-- The value at the place `w` of the single local contribution attached to the place `v` of `K`:
it is `hval v` at `g v` and `1` elsewhere. -/
noncomputable def yValueAt (g : Place K → Place L)
    (hval : (v : Place K) → (Place.localField L (g v))ˣ) (v : Place K) (w : Place L) :
    (Place.localField L w)ˣ := by
  classical
  exact if h : w = g v then h.symm ▸ hval v else 1

/-- The value at `w` of the idèle of `L` built from a choice of a place `g v` above each place
`v` of `K` and a local element `hval v` at that place. -/
noncomputable def yValue (g : Place K → Place L)
    (hval : (v : Place K) → (Place.localField L (g v))ˣ) (w : Place L) :
    (Place.localField L w)ˣ :=
  yValueAt g hval (placeUnder K L w) w

theorem yValueAt_self (g : Place K → Place L)
    (hval : (v : Place K) → (Place.localField L (g v))ˣ) (v : Place K) :
    yValueAt g hval v (g v) = hval v := by
  classical
  simp only [yValueAt]
  simp

theorem yValueAt_of_ne {g : Place K → Place L}
    {hval : (v : Place K) → (Place.localField L (g v))ˣ} {v : Place K} {w : Place L}
    (h : w ≠ g v) : yValueAt g hval v w = 1 := by
  classical
  simp only [yValueAt, dif_neg h]

theorem yValue_pickW {g : Place K → Place L}
    {hval : (v : Place K) → (Place.localField L (g v))ˣ}
    (hlies : ∀ v : Place K, Place.LiesOver (g v) v) (v : Place K) :
    yValue g hval (g v) = hval v := by
  rw [yValue, placeUnder_eq_of_liesOver (hlies v)]
  exact yValueAt_self g hval v

theorem yValue_eq_one_of_liesOver_ne {g : Place K → Place L}
    {hval : (v : Place K) → (Place.localField L (g v))ˣ} {w : Place L} {v : Place K}
    (hw : Place.LiesOver w v) (hne : w ≠ g v) : yValue g hval w = 1 := by
  rw [yValue, placeUnder_eq_of_liesOver hw]
  exact yValueAt_of_ne hne

theorem yValue_mem_localUnits_pickW {g : Place K → Place L}
    {hval : (v : Place K) → (Place.localField L (g v))ˣ} {S T' : Finset (Place K)}
    (hlies : ∀ v : Place K, Place.LiesOver (g v) v)
    (hunit : ∀ v : Place K, v ∉ S → v ∉ T' → hval v ∈ Place.localUnits L (g v))
    {v : Place K} (hvS : v ∉ S) (hvT : v ∉ T') :
    yValue g hval (g v) ∈ Place.localUnits L (g v) := by
  rw [yValue_pickW hlies v]
  exact hunit v hvS hvT

theorem finite_yValue_not_mem_localUnits {g : Place K → Place L}
    {hval : (v : Place K) → (Place.localField L (g v))ˣ} {S T' : Finset (Place K)}
    (hlies : ∀ v : Place K, Place.LiesOver (g v) v)
    (hunit : ∀ v : Place K, v ∉ S → v ∉ T' → hval v ∈ Place.localUnits L (g v)) :
    {w : Place L | yValue g hval w ∉ Place.localUnits L w}.Finite := by
  classical
  refine Set.Finite.subset ((S ∪ T').finite_toSet.image g) ?_
  intro w hw
  by_cases hex : ∃ v : Place K, g v = w
  · obtain ⟨v, hv⟩ := hex
    refine ⟨v, ?_, hv⟩
    by_contra hvnot
    have hvS : v ∉ S := fun h => hvnot (Finset.mem_union_left _ h)
    have hvT : v ∉ T' := fun h => hvnot (Finset.mem_union_right _ h)
    have hmem := yValue_mem_localUnits_pickW hlies hunit hvS hvT
    rw [hv] at hmem
    exact hw hmem
  · have h : ¬ (w = g (placeUnder K L w)) := by
      intro hh
      exact hex ⟨placeUnder K L w, hh.symm⟩
    have h1 : yValue g hval w = 1 := by
      rw [yValue]
      exact yValueAt_of_ne h
    exact absurd (by rw [h1]; exact Subgroup.one_mem _) hw


/-! ## The main statement -/

/-- **`kummerE ≤ N_{L/K} 𝕀_L`** in the Kummer case of the second inequality: for `L / K` cyclic
of prime degree `p` with `ζ_p ∈ K`, the subgroup `E` of Milne, *CFT* VII §6 is contained in the
norm subgroup.

Every component of an idèle `x ∈ E` is a local norm: at a place in `S` because it is a `p`-th
power and the local norm index divides the local degree, at a place `q ∈ T` because `q` splits
completely so the local norm is surjective, and at any other (finite, unramified) place because
it is a local unit and the norm on units is surjective for an unramified local extension.  The
idèle of `L` realising these local norms place by place is a unit at all but finitely many
places, since `S ∪ T` is finite. -/
theorem kummerE_le_normImage {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (hadj : IntermediateField.adjoin K {α} = ⊤)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (hSram : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∃ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L), Q.asIdeal.LiesOver q.asIdeal ∧
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hTdisj : ∀ q ∈ T, NK.GlobalCFT.Place.ofFinite q ∉ S)
    (hTsplit : ∀ q ∈ T, ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      Q.asIdeal.LiesOver q.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) :
    KummerCase.kummerE (K := K) p S (T.map (KummerCase.placeOfFiniteEmb K)) ≤
      NK.GlobalCFT.Idele.normImage K L := by
  intro x hx
  classical
  rw [Idele.mem_normImage]
  rw [mem_kummerE] at hx
  obtain ⟨hxS, hxU⟩ := hx
  -- ### The local data: a place of `L` above each place of `K`, and a local preimage
  have hhex : ∀ v : Place K, ∃ (w : Place L) (u : (Place.localField L w)ˣ),
      Place.LiesOver w v ∧ Idele.normIdeleFun K L (singleIdele w u) v = x v ∧
        (v ∉ S → v ∉ T.map (placeOfFiniteEmb K) → u ∈ Place.localUnits L w) := by
    intro v
    cases v with
    | inl v' =>
        obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v' :=
          InfinitePlace.comap_surjective v'
        have hwl : w.LiesOver v' := (Norm.liesOver_iff_comap_eq w v').mpr hw
        haveI : w.LiesOver v' := hwl
        obtain ⟨u, hu⟩ := localPow_mem_localNormInfinite (K := K) (L := L) hp hcard v' w
          (hxS (Place.ofInfinite v') (hSinf v'))
        refine ⟨Place.ofInfinite w, u, Place.liesOver_ofInfinite hwl, ?_, ?_⟩
        · rw [normIdeleFun_singleIdele_ofInfinite v' w u]
          exact hu
        · intro hvS _
          exact absurd (hSinf v') hvS
    | inr q =>
        obtain ⟨Ql, hQl⟩ :=
          Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) q
        by_cases hqS : Place.ofFinite q ∈ S
        · obtain ⟨u, hu⟩ := localPow_mem_localNormFinite (K := K) (L := L) hp hcard q Ql hQl
            (hxS (Place.ofFinite q) hqS)
          refine ⟨Place.ofFinite Ql, u, Place.liesOver_ofFinite hQl, ?_, ?_⟩
          · rw [normIdeleFun_singleIdele_ofFinite q Ql hQl u]
            exact hu
          · intro h _
            exact absurd hqS h
        · by_cases hqT : Place.ofFinite q ∈ T.map (placeOfFiniteEmb K)
          · obtain ⟨q₀, hq₀T, hq₀⟩ := Finset.mem_map.mp hqT
            have hq₀' : q₀ = q := by
              rw [placeOfFiniteEmb_apply] at hq₀
              exact Place.ofFinite_inj.mp hq₀
            rw [hq₀'] at hq₀T
            obtain ⟨he, hf⟩ := hTsplit q hq₀T Ql hQl
            obtain ⟨u, hu⟩ :=
              localNormFinite_surjective_of_ramificationIdx_eq_one_and_inertiaDeg_eq_one
                q Ql hQl he hf (x (Place.ofFinite q))
            refine ⟨Place.ofFinite Ql, u, Place.liesOver_ofFinite hQl, ?_, ?_⟩
            · rw [normIdeleFun_singleIdele_ofFinite q Ql hQl u]
              exact hu
            · intro _ h
              exact absurd hqT h
          · have hram : Ql.asIdeal.ramificationIdx (𝓞 K) = 1 := by
              by_contra hne
              exact hqS (hSram q ⟨Ql, hQl, hne⟩)
            obtain ⟨u, hu, hunorm⟩ :=
              localNormFinite_units_surjective_of_ramificationIdx_eq_one q Ql hQl hram
                (x (Place.ofFinite q)) (hxU (Place.ofFinite q) hqS hqT)
            refine ⟨Place.ofFinite Ql, u, Place.liesOver_ofFinite hQl, ?_, ?_⟩
            · rw [normIdeleFun_singleIdele_ofFinite q Ql hQl u]
              exact hunorm
            · intro _ _
              exact hu
  choose g hval hlies hnorm hunit using hhex
  -- ### The idèle of `L` realising the norms
  have hyeventually : ∀ᶠ w in Filter.cofinite, yValue g hval w ∈ Place.localUnits L w :=
    Filter.eventually_cofinite.mpr
      (finite_yValue_not_mem_localUnits (S := S) (T' := T.map (placeOfFiniteEmb K))
        hlies hunit)
  let y : Idele L := ⟨yValue g hval, hyeventually⟩
  refine ⟨y, fun v => ?_⟩
  have hsingle : ∀ w : Place L, Place.LiesOver w v →
      y w = singleIdele (g v) (hval v) w := by
    intro w hw
    by_cases h : w = g v
    · rw [h, show y (g v) = yValue g hval (g v) from rfl, yValue_pickW hlies v,
        singleIdele_apply_self]
    · rw [show y w = yValue g hval w from rfl, yValue_eq_one_of_liesOver_ne hw h,
        singleIdele_apply_of_ne (w' := w) h (hval v)]
  rw [← hnorm v]
  exact (normIdeleFun_congr_of_liesOver hsingle).symm

end NK.GlobalCFTdeep.SecondInequality.KummerCase
