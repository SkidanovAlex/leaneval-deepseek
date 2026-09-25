import Mathlib.Order.CompletePartialOrder
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver

/-!
# The ring homomorphism between adic completions preserves integrality

Let `L / K` be an extension of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height-one prime of `𝓞 L` lying over `Q`.  The map
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L`
extends the inclusion `K → L`; we show that it sends the ring of integers
`Q.adicCompletionIntegers K` of the `Q`-adic completion of `K` into the ring of integers
`q.adicCompletionIntegers L` of the `q`-adic completion of `L`.

The proof is analytic in spirit:
1. on elements of the base field `K` the statement reduces to the valuation identity
   `v_q (y) = v_Q (y) ^ e` for `y ∈ K` (`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`),
   so integrality at `Q` implies integrality at `q`;
2. the ring of integers of a (completed) valued field is clopen and `K` is dense in its
   completion, hence every integral element of the completion is a limit of integral elements
   of `K` (`Dense.open_subset_closure_inter`);
3. since `adicCompletionMap` is continuous and the integral elements of `L` form a closed set,
   the image of the closure lies in the closure of the image.
-/

open scoped NumberField
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.RingTheory.Henselian

open IsDedekindDomain.HeightOneSpectrum

/-- Integrality of an element of `K` at the prime `Q` transfers to its image at a prime `q`
of `L` lying over `Q`. -/
theorem adicCompletionMap_mem_integers_of_baseField
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (y : K)
    (hy : (y : Q.adicCompletion K) ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))) :
    ((algebraMap K L y : q.adicCompletion L) ∈ (q.adicCompletionIntegers L : Set (q.adicCompletion L))) := by
  -- integrality of `y` at `Q` means its `Q`-adic valuation is at most one
  have hK : IsDedekindDomain.HeightOneSpectrum.valuation K Q y ≤ 1 := by
    have hy' : Valued.v (y : Q.adicCompletion K) ≤ 1 := by
      simpa using (mem_adicCompletionIntegers (R := 𝓞 K) K Q).mp hy
    rw [valuedAdicCompletion_eq_valuation' Q y] at hy'
    exact hy'
  -- since `q` lies over `Q`, the `q`-valuation of the image is the `e`-th power of the
  -- `Q`-valuation of `y`, with `e : ℕ`; powers of elements at most one stay at most one
  have hL : IsDedekindDomain.HeightOneSpectrum.valuation L q (algebraMap K L y) ≤ 1 := by
    letI : q.asIdeal.LiesOver Q.asIdeal := hq
    rw [← valuation_liesOver (A := 𝓞 K) (B := 𝓞 L) L Q q y]
    exact Left.pow_le_one_of_le hK _
  -- integrality of the image at `q`
  apply (mem_adicCompletionIntegers (R := 𝓞 L) L q).mpr
  rw [valuedAdicCompletion_eq_valuation' q (algebraMap K L y)]
  exact hL

/-- The ring homomorphism between adic completions induced by a prime lying over is continuous. -/
theorem adicCompletionMap_continuous
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Continuous (adicCompletionMap Q q hq : Q.adicCompletion K → q.adicCompletion L) := by
  change Continuous (fun x : Q.adicCompletion K => adicCompletionMap Q q hq x)
  have hfun : (fun x : Q.adicCompletion K => adicCompletionMap Q q hq x) =
      (fun x : Q.adicCompletion K =>
        adicCompletion.ofCompletion (K := L) (v := q)
          (UniformSpace.Completion.map
            (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L)))
            (adicCompletion.toCompletion (K := K) (v := Q) x))) := by
    funext x
    rfl
  rw [hfun]
  exact Continuous.comp (adicCompletion.continuous_ofCompletion (K := L) (v := q))
    (Continuous.comp (UniformSpace.Completion.continuous_map)
      (adicCompletion.continuous_toCompletion (K := K) (v := Q)))

/-- `adicCompletionMap` maps the ring of integers of the completion of `K` at `Q` into the ring
of integers of the completion of `L` at `q`, whenever `q` lies over `Q`. -/
theorem adicCompletionMap_mem_integers
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {x : Q.adicCompletion K}
    (hx : x ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq x ∈
      (q.adicCompletionIntegers L : Set (q.adicCompletion L)) := by
  let S : Set (Q.adicCompletion K) := (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))
  let T : Set (q.adicCompletion L) := (q.adicCompletionIntegers L : Set (q.adicCompletion L))
  let D : Set (Q.adicCompletion K) := Set.range (algebraMap K (Q.adicCompletion K))
  let F : Q.adicCompletion K → q.adicCompletion L := fun x => (adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L) x
  change F x ∈ T
  -- the integral elements of a valued field form a closed set
  have hTclosed : IsClosed T := by
    simpa [T, adicCompletionIntegers] using (Valued.isClosed_valuationSubring (q.adicCompletion L))
  -- the map between completions is continuous
  have hF : Continuous F := by
    simpa [F] using adicCompletionMap_continuous Q q hq
  have hpre : IsClosed (F ⁻¹' T) := IsClosed.preimage hF hTclosed
  -- the integral elements form an open set, and `K` is dense in its completion, so every
  -- integral element is the limit of integral elements of `K`
  have hSopen : IsOpen S := by
    simpa [S, adicCompletionIntegers] using (Valued.isOpen_valuationSubring (Q.adicCompletion K))
  have hd : Dense D := by
    change DenseRange (algebraMap K (Q.adicCompletion K))
    exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q
  have hSdense : S ⊆ closure (S ∩ D) := Dense.open_subset_closure_inter (s := D) (t := S) hd hSopen
  have hxcl : x ∈ closure (S ∩ D) := hSdense hx
  -- on integral elements coming from `K`, the map lands in the integral elements of `L`
  have hsub : S ∩ D ⊆ F ⁻¹' T := by
    rintro z ⟨hzS, hzD⟩
    rcases hzD with ⟨y, hyz⟩
    rw [Set.mem_preimage]
    rw [← hyz] at hzS ⊢
    have hy0 : (y : Q.adicCompletion K) ∈ S := by
      exact hzS
    have hIm : ((algebraMap K L y : q.adicCompletion L) ∈ (q.adicCompletionIntegers L : Set (q.adicCompletion L))) :=
      adicCompletionMap_mem_integers_of_baseField Q q hq y (by exact hy0)
    have hFeq : F (algebraMap K (Q.adicCompletion K) y) = (algebraMap K L y : q.adicCompletion L) := by
      dsimp [F]
      have hbridge : adicCompletionMap Q q hq (algebraMap K (Q.adicCompletion K) y) =
          adicCompletionMap Q q hq (y : Q.adicCompletion K) := by
        congr 1
      rw [hbridge, adicCompletionMap_apply Q q hq y]
    rw [hFeq]
    exact hIm
  -- continuity of `F` then moves the limit through the closed set `T`
  have hmono : closure (S ∩ D) ⊆ closure (F ⁻¹' T) := closure_mono hsub
  have hcl : closure (F ⁻¹' T) ⊆ F ⁻¹' T := IsClosed.closure_subset hpre
  exact (hmono.trans hcl) hxcl

end Commons.RingTheory.Henselian