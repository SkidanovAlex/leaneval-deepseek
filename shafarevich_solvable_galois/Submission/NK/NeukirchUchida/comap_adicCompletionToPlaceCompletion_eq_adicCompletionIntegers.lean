import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.NeukirchUchida.LocalGaloisCompletion
import Submission.NK.NeukirchUchida.closure_algebraMap_le_one_eq_adicCompletionIntegers

/-!
# The integral structure of the `p`-adic completion inside the completion at a place

Let `K` be a number field, `p` a finite place of `K`, `K'` a separable closure of `K`, and `A` a
place of `K'` above `p` (a valuation subring of `K'` whose contraction to `K` is the valuation
ring of `p`).  Write

* `f : adicCompletion K p →+* placeCompletion A` for the canonical ring homomorphism from the
  `p`-adic completion of `K` to the completion of `K'` at `A` (`adicCompletionToPlaceCompletion`),
  extending `K → K' → placeCompletion A`;

then the contraction of the valuation ring of `placeCompletion A` along `f` is exactly the
valuation ring of the `p`-adic completion:

`(placeCompletionIntegers A).comap f = adicCompletionIntegers K p`.

This is the compatibility of the integral structures of the two completions which is needed to
compare the decomposition group of the place `A` with the absolute Galois group of `K_p`
(Neukirch–Schmidt–Wingberg, Chapter XII).

## Strategy

Both sides of the asserted equality are closed subsets of the `p`-adic completion `K_p` — a
valuation subring of a valued field is closed, and `f` is continuous — and both contain the image
of the "local integers" `{c : K | v_p c ≤ 1}`.  So it suffices to show that the closure of that
image is *all* of the ring of integers of the completion (`closure_algebraMap_le_one_eq_…`), and
then to identify the closure of the image with the contracted ring of integers.  The two
inclusions of the latter are the two halves of the key computation

`Valued.v (f c) = A.valuation (algebraMap K K' c)   (c : K)`,

which says that the extension of `A.valuation` to `placeCompletion A` evaluates on the image of
`K_p` exactly as the `p`-adic valuation does on `K`.
-/

open scoped Valued Pointwise

namespace NK.NeukirchUchida

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ### Value computations on the dense subfield -/

/-- The valuation of the completion `placeCompletion A` of `K'` at `A`, evaluated on the
canonical embedding of `K'`. -/
theorem valued_placeCompletionCoe (A : ValuationSubring K') (y : K') :
    Valued.v (placeCompletionCoe A y) = A.valuation y := by
  rw [placeCompletionCoe_apply, Valued.valuedCompletion_apply, WithVal.valued_toVal]
  try rfl

/-- The `p`-adic valuation of the completion, evaluated on the image of `K`. -/
theorem valued_algebraMap_adicCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    Valued.v (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) x) =
      IsDedekindDomain.HeightOneSpectrum.valuation K p x := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K p x

/-- The key value computation: on the image of `K`, the valuation of `placeCompletion A` agrees
with the restriction of `A.valuation`, i.e. with the `p`-adic valuation of `K`. -/
theorem valued_adicCompletionToPlaceCompletion_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) (x : K) :
    Valued.v (adicCompletionToPlaceCompletion p A hA
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) x)) =
      A.valuation (algebraMap K K' x) := by
  rw [adicCompletionToPlaceCompletion_algebraMap p A hA x, valued_placeCompletionCoe]

/-! ### The closure of the image of the local integers -/

/-- The closure of the image of the local integers `{c : K | v_p c ≤ 1}` in the completion of
`K'` at `A` is the contraction of the valuation ring of that completion. -/
theorem closure_algebraMap_le_one_eq_comap_adicCompletionToPlaceCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    closure ((algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) ''
        {c : K | IsDedekindDomain.HeightOneSpectrum.valuation K p c ≤ 1}) =
      ((placeCompletionIntegers A).comap (adicCompletionToPlaceCompletion p A hA) :
        Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) := by
  refine Set.Subset.antisymm ?_ ?_
  · -- every point of the closure is integral: the target is closed and contains the image
    refine closure_minimal ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      change adicCompletionToPlaceCompletion p A hA
          (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c) ∈
        placeCompletionIntegers A
      rw [mem_placeCompletionIntegers,
        valued_adicCompletionToPlaceCompletion_algebraMap p A hA c]
      exact (valuation_isEquiv_comap p A hA).le_one_iff_le_one.mp hc
    · change IsClosed ((adicCompletionToPlaceCompletion p A hA) ⁻¹'
        (placeCompletionIntegers A : Set (placeCompletion A)))
      exact (Valued.isClosed_valuationSubring (placeCompletion A)).preimage
        (continuous_adicCompletionToPlaceCompletion p A hA)
  · -- a point of the target lies in the closure: approximate it by an element of `K` that is
    -- close enough for the ultrametric inequality to apply
    intro x hx
    have hfx : Valued.v (adicCompletionToPlaceCompletion p A hA x) ≤ 1 := by
      change adicCompletionToPlaceCompletion p A hA x ∈ placeCompletionIntegers A at hx
      rwa [mem_placeCompletionIntegers] at hx
    rw [mem_closure_iff]
    intro o ho hxo
    have hball_open : IsOpen {w : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p |
        Valued.v ((adicCompletionToPlaceCompletion p A hA) (w - x)) < 1} := by
      have hcont : Continuous fun w : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p =>
          (adicCompletionToPlaceCompletion p A hA) (w - x) :=
        (continuous_adicCompletionToPlaceCompletion p A hA).comp
          (continuous_id.sub continuous_const)
      have hball : IsOpen {z : placeCompletion A | Valued.v z < 1} := by
        have h := Valued.isOpen_ball (placeCompletion A)
          (1 : ((Valued.v (R := placeCompletion A)
            (Γ₀ := A.ValueGroup)) : placeCompletion A →*₀ A.ValueGroup).ValueGroup₀)
        simpa only [Valuation.restrict_lt_one_iff] using h
      exact hball.preimage hcont
    have hxball : x ∈ {w : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p |
        Valued.v ((adicCompletionToPlaceCompletion p A hA) (w - x)) < 1} := by
      simp
    obtain ⟨c, hc⟩ := DenseRange.exists_mem_open
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K p)
      (ho.inter hball_open) ⟨x, hxo, hxball⟩
    refine ⟨algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c, hc.1, c, ?_, rfl⟩
    have hval : Valued.v (adicCompletionToPlaceCompletion p A hA
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c)) ≤ 1 := by
      have hsplit : adicCompletionToPlaceCompletion p A hA
          (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c) =
          adicCompletionToPlaceCompletion p A hA x +
            adicCompletionToPlaceCompletion p A hA
              (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c - x) := by
        rw [← map_add]
        congr 1
        ring
      calc Valued.v (adicCompletionToPlaceCompletion p A hA
              (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c))
          = Valued.v (adicCompletionToPlaceCompletion p A hA x +
              adicCompletionToPlaceCompletion p A hA
                (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c - x)) := by
            rw [hsplit]
        _ ≤ max (Valued.v (adicCompletionToPlaceCompletion p A hA x))
              (Valued.v (adicCompletionToPlaceCompletion p A hA
                (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) c - x))) :=
            Valuation.map_add _ _ _
        _ ≤ 1 := max_le hfx (le_of_lt hc.2)
    have hAu : A.valuation (algebraMap K K' c) ≤ 1 := by
      rw [← valued_adicCompletionToPlaceCompletion_algebraMap p A hA c]
      exact hval
    simpa using (valuation_isEquiv_comap p A hA).le_one_iff_le_one.mpr hAu

/-! ### The contracted valuation ring -/

theorem comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers {K K' : Type*} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p := by
  have h1 : ((placeCompletionIntegers A).comap (adicCompletionToPlaceCompletion p A hA) :
      Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) =
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p :
      Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) := by
    rw [← closure_algebraMap_le_one_eq_comap_adicCompletionToPlaceCompletion p A hA,
      ← closure_algebraMap_le_one_eq_adicCompletionIntegers (K := K) p]
  exact ValuationSubring.ext _ _ fun x => Set.ext_iff.mp h1 x

end

end NK.NeukirchUchida
