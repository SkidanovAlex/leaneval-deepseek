import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.NUV2.ArtinBridge.pow_mem_normGroup_of_exponent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ArtinBridge

/-- **The local extension at a finite place is commutative.**

`L / K` is a finite Galois extension of number fields with commutative Galois group, `Q` a finite
place of `K` and `q` a place of `L` above `Q`.  Then the local Galois group `Gal(L_q / K_Q)` is
commutative: it is the decomposition group `D_q ≤ Gal(L/K)`, transported along
`decompositionSubgroupMulEquivLocalGalois`. -/
theorem isMulCommutative_adicCompletion_of_isGalois
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI := Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
    IsMulCommutative Gal(q.adicCompletion L/Q.adicCompletion K) := by
  letI := Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  refine IsMulCommutative.of_comm fun a b => ?_
  let e :=
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois Q q hq
  have h1 : ((e.symm a : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup q) :
        L ≃ₐ[K] L) *
      ((e.symm b : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup q) :
        L ≃ₐ[K] L) =
      ((e.symm b : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup q) :
        L ≃ₐ[K] L) *
      ((e.symm a : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup q) :
        L ≃ₐ[K] L) :=
    IsMulCommutative.is_comm.comm _ _
  have h2 : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h1
  calc a * b = e (e.symm a) * e (e.symm b) := by rw [e.apply_symm_apply, e.apply_symm_apply]
    _ = e ((e.symm a) * (e.symm b)) := by rw [map_mul]
    _ = e ((e.symm b) * (e.symm a)) := by rw [h2]
    _ = e (e.symm b) * e (e.symm a) := by rw [map_mul]
    _ = b * a := by rw [e.apply_symm_apply, e.apply_symm_apply]

/-- **The local Galois group at a finite place has exponent dividing `p`.**

Transported from the global hypothesis `∀ σ : Gal(L/K), σ ^ p = 1` along the identification of the
local Galois group with the decomposition subgroup. -/
theorem pow_eq_one_adicCompletion_of_isGalois
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {p : ℕ}
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ p = 1)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI := Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
    ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ ^ p = 1 := by
  letI := Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  intro σ
  let e :=
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois Q q hq
  have h : e.symm σ ^ p = 1 := by
    apply Subtype.ext
    show ((e.symm σ : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup q) :
      L ≃ₐ[K] L) ^ p = (1 : L ≃ₐ[K] L)
    rw [hexp]
  calc σ ^ p = e (e.symm σ) ^ p := by rw [e.apply_symm_apply]
    _ = e ((e.symm σ) ^ p) := by rw [map_pow]
    _ = e 1 := by rw [h]
    _ = 1 := map_one e

/-- **At a finite place of `S`, a local `p`-th power is a local norm.**

If `L / K` has commutative Galois group of exponent dividing `p` and `x ∈ K_Q^×` is a `p`-th power,
then `x` is a norm from `L_q` for every `q | Q`.  This is `pow_mem_normGroup_of_exponent`
(local Artin reciprocity: the Artin map has target of exponent `p`, hence kills `p`-th powers)
spelled out as a surjectivity statement for the local norm on units. -/
theorem localPow_mem_localNormFinite_of_isGalois_exp
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {p : ℕ}
    (hp : p.Prime) (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ p = 1)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (x : (Q.adicCompletion K)ˣ)
    (hx : x ∈ NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p
      (NK.GlobalCFT.Place.ofFinite Q)) :
    ∃ u : (q.adicCompletion L)ˣ, NK.GlobalCFT.Place.localNormFinite q Q hq u = x := by
  letI := Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  letI : Fact p.Prime := ⟨hp⟩
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  haveI : IsMulCommutative Gal(q.adicCompletion L/Q.adicCompletion K) :=
    isMulCommutative_adicCompletion_of_isGalois (K := K) (L := L) Q q hq
  have hexpl : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ ^ p = 1 :=
    pow_eq_one_adicCompletion_of_isGalois (K := K) (L := L) hexp Q q hq
  have hnorm := pow_mem_normGroup_of_exponent Q p hexpl
  obtain ⟨c, hc⟩ := hx
  have hxn : x ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) := by
    rw [← hc]
    exact hnorm c
  obtain ⟨y, hy⟩ := (NK.LocalReciprocity.mem_normGroup_iff x).mp hxn
  exact ⟨y, Units.ext hy⟩

theorem kummerE_le_normImage_of_isGalois_exp {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ p = 1) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSram : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        q.asIdeal.LiesOver Q.asIdeal ∧
          q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) →
      NK.GlobalCFT.Place.ofFinite Q ∈ S)
    (hInf : ∀ (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v],
      ∀ x ∈ NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p
        (NK.GlobalCFT.Place.ofInfinite v),
      ∃ u : w.Completionˣ, NK.GlobalCFT.Place.localNormInfinite w v u = x) :
    NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤
      NK.GlobalCFT.Idele.normImage K L := by
  intro x hx
  classical
  rw [NK.GlobalCFT.Idele.mem_normImage]
  rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.mem_kummerE] at hx
  obtain ⟨hxS, hxU⟩ := hx
  -- ### The local data: a place of `L` above each place of `K`, and a local preimage
  have hhex : ∀ v : NK.GlobalCFT.Place K,
      ∃ (w : NK.GlobalCFT.Place L) (u : (NK.GlobalCFT.Place.localField L w)ˣ),
      NK.GlobalCFT.Place.LiesOver w v ∧
        NK.GlobalCFT.Idele.normIdeleFun K L
          (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele w u) v = x v ∧
        (v ∉ S → v ∉ (∅ : Finset (NK.GlobalCFT.Place K)) →
          u ∈ NK.GlobalCFT.Place.localUnits L w) := by
    intro v
    cases v with
    | inl v' =>
        -- infinite place: it lies in `S`, where the local norms are surjective onto `p`-th powers
        obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace L,
            w.comap (algebraMap K L) = v' :=
          InfinitePlace.comap_surjective v'
        have hwl : w.LiesOver v' := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v').mpr hw
        haveI : w.LiesOver v' := hwl
        obtain ⟨u, hu⟩ := hInf v' w (x (NK.GlobalCFT.Place.ofInfinite v'))
          (hxS (NK.GlobalCFT.Place.ofInfinite v') (hSinf v'))
        exact ⟨NK.GlobalCFT.Place.ofInfinite w, u,
          NK.GlobalCFT.Place.liesOver_ofInfinite hwl,
          by
            rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite
              v' w u]
            exact hu,
          fun hvS _ => absurd (hSinf v') hvS⟩
    | inr Q =>
        obtain ⟨q, hq⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
          (K := K) (L := L) Q
        by_cases hQS : NK.GlobalCFT.Place.ofFinite Q ∈ S
        · -- `Q ∈ S`: `x` is a local `p`-th power, hence a local norm
          obtain ⟨u, hu⟩ := localPow_mem_localNormFinite_of_isGalois_exp (K := K) (L := L)
            hp hexp Q q hq (x (NK.GlobalCFT.Place.ofFinite Q))
            (hxS (NK.GlobalCFT.Place.ofFinite Q) hQS)
          refine ⟨NK.GlobalCFT.Place.ofFinite q, u,
            NK.GlobalCFT.Place.liesOver_ofFinite hq, ?_, ?_⟩
          · rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite
              Q q hq u]
            exact hu
          · intro h _
            exact absurd hQS h
        · -- `Q ∉ S`: the extension is unramified at `Q` and `x` is a local unit
          have hram : q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
            by_contra hne
            exact hQS (hSram Q ⟨q, hq, hne⟩)
          obtain ⟨u, hu, hunorm⟩ :=
            NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
              Q q hq hram (x (NK.GlobalCFT.Place.ofFinite Q))
              (hxU (NK.GlobalCFT.Place.ofFinite Q) hQS (by simp))
          refine ⟨NK.GlobalCFT.Place.ofFinite q, u,
            NK.GlobalCFT.Place.liesOver_ofFinite hq, ?_, ?_⟩
          · rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite
              Q q hq u]
            exact hunorm
          · intro _ _
            exact hu
  choose g hval hlies hnorm hunit using hhex
  -- ### The idèle of `L` realising the norms
  have hyeventually : ∀ᶠ w in Filter.cofinite,
      NK.GlobalCFTdeep.SecondInequality.KummerCase.yValue g hval w ∈
        NK.GlobalCFT.Place.localUnits L w :=
    Filter.eventually_cofinite.mpr
      (NK.GlobalCFTdeep.SecondInequality.KummerCase.finite_yValue_not_mem_localUnits
        (S := S) (T' := ∅) hlies hunit)
  let y : NK.GlobalCFT.Idele L :=
    ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.yValue g hval, hyeventually⟩
  refine ⟨y, fun v => ?_⟩
  have hsingle : ∀ w : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w v →
      y w = NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (g v) (hval v) w := by
    intro w hw
    by_cases h : w = g v
    · rw [h, show y (g v) =
          NK.GlobalCFTdeep.SecondInequality.KummerCase.yValue g hval (g v) from rfl,
        NK.GlobalCFTdeep.SecondInequality.KummerCase.yValue_pickW hlies v,
        NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_self]
    · rw [show y w =
          NK.GlobalCFTdeep.SecondInequality.KummerCase.yValue g hval w from rfl,
        NK.GlobalCFTdeep.SecondInequality.KummerCase.yValue_eq_one_of_liesOver_ne hw h,
        NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne (w' := w) h
          (hval v)]
  rw [← hnorm v]
  exact (NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_congr_of_liesOver
    hsingle).symm

end NK.NUV2.ArtinBridge
