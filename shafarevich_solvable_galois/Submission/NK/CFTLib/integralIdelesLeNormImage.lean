import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `∏_v 𝒪_v^× ≤ N_{L/K} 𝕀_L` for an extension unramified at every place

Let `L / K` be a finite Galois extension of number fields which is unramified at *every* place:
the different ideal is the unit ideal (`differentIdeal (𝓞 K) (𝓞 L) = ⊤`) and every infinite place
is unramified (`IsUnramifiedAtInfinitePlaces K L`).  Then every idèle of `K` which is a local
unit at every finite place is the norm of an idèle of `L`:

`Idele.integralIdeles K ≤ Idele.normImage K L`.

The proof is local at each place `v` of `K`: choose a place `w` of `L` above `v` and a local
preimage of `x v` under the local norm `N_{L_w/K_v}`.  The local norm on *units* is surjective
because the local extension is unramified:

* at a finite place, because `differentIdeal = ⊤` forces the ramification index `e = 1`
  (`ramificationIdx_eq_one_of_differentIdeal_eq_top` below), and for an unramified local
  extension the norm on the rings of integers is surjective
  (`KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one`);
* at an infinite place, because `IsUnramifiedAtInfinitePlaces` makes the local extension either
  `ℝ ⊂ ℝ` or `ℂ ⊂ ℂ`, where the norm on units is onto
  (`localNormInfinite_range_eq_top_of_isUnramified` below).

The local preimages assemble into an idèle of `L` which is a local unit at every place, using the
`T`-idèle machinery of `NK.GlobalCFTdeep.SecondInequality.KummerCase`.

## Main results

* `NK.CFTLib.integralIdelesLeNormImage` — the target statement;
* `NK.CFTLib.ramificationIdx_eq_one_of_differentIdeal_eq_top` — `e = 1` from `differentIdeal = ⊤`;
* `NK.CFTLib.localNormInfinite_range_eq_top_of_isUnramified` — the archimedean local input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT
open NK.GlobalCFTdeep.SecondInequality

/-! ### Two local inputs -/

/-- If the different ideal of `L/K` is the unit ideal, then the extension is unramified at every
finite place: the ramification index of every prime of `𝓞 L` over `𝓞 K` is `1`. -/
theorem ramificationIdx_eq_one_of_differentIdeal_eq_top
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (hfin : differentIdeal (𝓞 K) (𝓞 L) = ⊤) (Q : HeightOneSpectrum (𝓞 L)) :
    Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hndvd : ¬ Q.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    intro h
    rw [hfin] at h
    have hle : (⊤ : Ideal (𝓞 L)) ≤ Q.asIdeal := Ideal.dvd_iff_le.mp h
    exact Q.isPrime.ne_top (top_le_iff.mp hle)
  have hU : Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal := (not_dvd_differentIdeal_iff).mp hndvd
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-- At an infinite place `w` of `L` which is unramified over the place `v` of `K` below it (so
that the local extension is `ℝ ⊂ ℝ` or `ℂ ⊂ ℂ`), the local norm `L_wˣ → K_vˣ` is surjective. -/
theorem localNormInfinite_range_eq_top_of_isUnramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v]
    (hunr : NumberField.InfinitePlace.IsUnramified K w) :
    (Place.localNormInfinite w v).range = ⊤ := by
  rw [show Place.localNormInfinite w v
      = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl]
  rw [NumberField.InfinitePlace.isUnramified_iff,
    (NumberField.InfinitePlace.LiesOver.comap_eq w v)] at hunr
  rcases hunr with hR | hC
  · exact NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real
      (v := v) (w := w)
      ((NumberField.InfinitePlace.LiesOver.comap_eq w v) ▸
        InfinitePlace.IsReal.comap (algebraMap K L) hR) hR
  · exact NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex
      (v := v) (w := w) hC
      (InfinitePlace.IsComplex.of_comap (algebraMap K L)
        ((NumberField.InfinitePlace.LiesOver.comap_eq w v) ▸ hC))

/-! ### The main theorem -/

/-- **The integral idèles of `K` are norms from `L`** for an extension `L/K` that is unramified at
every place: `∏_v 𝒪_v^× ≤ N_{L/K} 𝕀_L`.

At each place `v` of `K` we pick a place `w` of `L` above it and a local preimage of `x v` under
the local norm, which exists because the norm on local *units* is surjective for an unramified
local extension; the local preimages are local units at all places, so they assemble into an
idèle of `L`. -/
theorem integralIdelesLeNormImage
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hfin : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces K L) :
    NK.GlobalCFT.Idele.integralIdeles K ≤ NK.GlobalCFT.Idele.normImage K L := by
  intro x hx
  classical
  haveI := hinf
  have hx' : ∀ v, Place.IsFinite v → x v ∈ Place.localUnits K v := hx
  have hram := ramificationIdx_eq_one_of_differentIdeal_eq_top (K := K) (L := L) hfin
  -- ### The local data: for each place `v` of `K` a place `w` of `L` above it together with a
  -- local preimage of `x v` which is a local unit.
  have hhex : ∀ v : Place K, ∃ (w : Place L) (u : (Place.localField L w)ˣ),
      Place.LiesOver w v ∧
        Idele.normIdeleFun K L (KummerCase.singleIdele w u) v = x v ∧
          u ∈ Place.localUnits L w := by
    intro v
    cases v with
    | inl v' =>
        obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v' :=
          InfinitePlace.comap_surjective v'
        have hwl : w.LiesOver v' := (Norm.liesOver_iff_comap_eq w v').mpr hw
        haveI : w.LiesOver v' := hwl
        have hsurj := localNormInfinite_range_eq_top_of_isUnramified (K := K) (L := L)
          (v := v') (w := w) (IsUnramifiedAtInfinitePlaces.isUnramified w)
        have hmem : x (Place.ofInfinite v') ∈ (Place.localNormInfinite w v').range := by
          rw [hsurj]
          exact Subgroup.mem_top _
        obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
        refine ⟨Place.ofInfinite w, u, Place.liesOver_ofInfinite hwl, ?_,
          Place.mem_localUnits_ofInfinite⟩
        rw [KummerCase.normIdeleFun_singleIdele_ofInfinite v' w u]
        exact hu
    | inr Q =>
        obtain ⟨Ql, hQl⟩ :=
          Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
        obtain ⟨u, hu, hunorm⟩ :=
          KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
            Q Ql hQl (hram Ql) (x (Place.ofFinite Q))
            (hx' (Place.ofFinite Q) (Place.isFinite_ofFinite Q))
        refine ⟨Place.ofFinite Ql, u, Place.liesOver_ofFinite hQl, ?_, hu⟩
        rw [KummerCase.normIdeleFun_singleIdele_ofFinite Q Ql hQl u]
        exact hunorm
  choose g hval hlies hnorm hunit using hhex
  -- ### The idèle of `L` realising the local norms
  have hyeventually : ∀ᶠ w in Filter.cofinite, KummerCase.yValue g hval w ∈ Place.localUnits L w :=
    Filter.eventually_cofinite.mpr
      (KummerCase.finite_yValue_not_mem_localUnits (S := ∅) (T' := ∅) hlies
        (fun v _ _ => hunit v))
  let y : Idele L := ⟨KummerCase.yValue g hval, hyeventually⟩
  refine ⟨y, fun v => ?_⟩
  -- the idèle `y` agrees with the single-place idèle at `g v` at every place above `v`
  have hsingle : ∀ w : Place L, Place.LiesOver w v →
      y w = KummerCase.singleIdele (g v) (hval v) w := by
    intro w hw
    by_cases h : w = g v
    · rw [h, show y (g v) = KummerCase.yValue g hval (g v) from rfl,
        KummerCase.yValue_pickW hlies v, KummerCase.singleIdele_apply_self]
    · rw [show y w = KummerCase.yValue g hval w from rfl,
        KummerCase.yValue_eq_one_of_liesOver_ne hw h,
        KummerCase.singleIdele_apply_of_ne (w' := w) h (hval v)]
  rw [← hnorm v]
  exact (KummerCase.normIdeleFun_congr_of_liesOver hsingle).symm

end NK.CFTLib
