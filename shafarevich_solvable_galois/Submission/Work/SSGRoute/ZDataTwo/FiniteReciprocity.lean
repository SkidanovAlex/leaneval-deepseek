import Mathlib
import Submission.Work.HilbertSymbolGeneral.hilbertReciprocityTwo
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-place half of Hilbert reciprocity, in arithmetic (local-norm) form

The reciprocity clause `hrec` of the Poitou–Tate realisation is, at the level of arithmetic, the
Hilbert-symbol product formula: the sum of the local invariants of a pair of global classes vanishes.
For the `μ₂`/`p = 2` case of this development the local invariant of a pair of classes is the local
norm condition — `y` is a local norm at `v` from `K(√x)/K` exactly when the local pairing of the two
classes is trivial — and the *content* of the product formula restricted to a finite set `T` of
places is that the set of places where `y` fails to be a local norm is contained in the set of places
where the two classes are allowed to be ramified.

This file proves exactly that containment, with the "allowed to be ramified at `v`" condition split
into its two halves:

* `isLocalNorm_of_unramified_of_val_pow` — the *local* half, at a finite prime: if `L/K` is
  unramified at a prime `Q` of `K` (some `q | Q` with ramification index one) and `x ∈ Kˣ` has
  `v_Q(x) = v_Q(y)^{f(Q|q)}` for some `y` — the classical criterion "the valuation of `x` is an
  `f`-th power", which for `f ∈ {1,2}` and even valuations is automatic — then `x` is a local norm
  at `Q`.  This is the composition of the criterion
  `NK.NUV2.LC.localIncl_mem_range_localNormFinite_iff` (the unramified norm group is
  "`f` divides the valuation", `NK.Unramified.NormGroupEqUnramified`) with the idèle-side bridge
  `Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup`;
* `isLocalNorm_of_notMem_of_finite_unramified` — the same at every place outside `T`, given the
  archimedean cases;
* `badSet_subset_and_even` — **the product formula restricted to `T`**: the set of places at which
  `x` fails to be a local norm is contained in `T` and has even cardinality.  The evenness is
  Hilbert reciprocity (`Work.HilbertSymbolGeneral.hilbertReciprocityTwo`); the containment is the
  computation above.

This is the last ingredient of the arithmetic form of `hrec` at `p = 2`: with the archimedean half
(`Work.SSGRoute.ZDataTwo.archPair_two_kummer_eq_zero_iff`) both summands of the joint reciprocity
clause are now statements about local norms and signs.
-/

open scoped NumberField

namespace Work.SSGRoute.ZDataTwo

open NK.GlobalCFT

/-- **The unramified local norm criterion.**  If `L/K` is unramified at the finite prime `Q` of `K`
(some prime `q | Q` has ramification index one) and `x ∈ Kˣ` satisfies `v_Q(x) = v_Q(y)^f` for some
`y` and the inertia degree `f = f(q|Q)`, then `x` is a local norm at `Q` from `L/K`.  For `f = 1`
the hypothesis is automatic; for `f = 2` it says that `v_Q(x)` is a square in the value group, i.e.
that `x` is unramified there. -/
theorem isLocalNorm_of_unramified_of_val_pow
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) (x : Kˣ)
    (hdiv : ∃ y : (Q.adicCompletion K)ˣ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap K (Q.adicCompletion K) (x : K)) =
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (y : Q.adicCompletion K)) ^ (q.asIdeal.inertiaDeg (𝓞 K))) :
    NK.NUV2.LC.IsLocalNorm K L x (Place.ofFinite Q) := by
  rw [Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup x (Place.ofFinite Q),
    NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
  exact Subgroup.mem_iSup_of_mem ⟨q, hq⟩
    ((NK.NUV2.LC.localIncl_mem_range_localNormFinite_iff Q q hq hunr x).mpr hdiv)

/-- **The containment of the bad set, finite places.**  If `x` is a local norm at `L/K` outside a
finite set `T` of places of `K` — the finite places outside `T` being unramified in `L/K` with the
valuation of `x` an `f`-th power — then `x` is a local norm at every place outside `T`. -/
theorem isLocalNorm_of_notMem_of_finite_unramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x : Kˣ)
    (T : Finset (Place K))
    (hfin : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Place.ofFinite Q ∉ T →
        ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          q.asIdeal.LiesOver Q.asIdeal ∧ q.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
            ∃ y : (Q.adicCompletion K)ˣ,
              Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
                  (algebraMap K (Q.adicCompletion K) (x : K)) =
                (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
                  (y : Q.adicCompletion K)) ^ (q.asIdeal.inertiaDeg (𝓞 K)))
    (hinf : ∀ w : NumberField.InfinitePlace K, Place.ofInfinite w ∉ T →
      NK.NUV2.LC.IsLocalNorm K L x (Place.ofInfinite w)) :
    ∀ v : Place K, v ∉ T → NK.NUV2.LC.IsLocalNorm K L x v := by
  intro v hv
  rcases v with w | Q
  · exact hinf w hv
  · obtain ⟨q, hq, hunr, hdiv⟩ := hfin Q hv
    exact isLocalNorm_of_unramified_of_val_pow Q q hq hunr x hdiv

/-- **The product formula restricted to `T`.**  If the finite places outside `T` are unramified in
the quadratic extension `L/K` with the valuation of `x` an `f`-th power there, and `x` is a local
norm at the archimedean places outside `T`, then the set of places of `K` at which `x` fails to be a
local norm is contained in `T` and has even cardinality.

In the application `L = K(√b)` and `x = c` this says: if `b` and `c` are unramified outside `T`
(with the archimedean sign conditions), then the local pairings of the two classes are trivial at
every place outside `T` — so the reciprocity sum is the sum over `T`, and it vanishes by the
evenness of the bad set. -/
theorem badSet_subset_and_even
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x : Kˣ)
    (T : Finset (Place K))
    (hfin : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Place.ofFinite Q ∉ T →
        ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          q.asIdeal.LiesOver Q.asIdeal ∧ q.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
            ∃ y : (Q.adicCompletion K)ˣ,
              Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
                  (algebraMap K (Q.adicCompletion K) (x : K)) =
                (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
                  (y : Q.adicCompletion K)) ^ (q.asIdeal.inertiaDeg (𝓞 K)))
    (hinf : ∀ w : NumberField.InfinitePlace K, Place.ofInfinite w ∉ T →
      NK.NUV2.LC.IsLocalNorm K L x (Place.ofInfinite w)) :
    ∃ s : Finset (Place K), s ⊆ T ∧ (∀ v : Place K, v ∈ s ↔ ¬ NK.NUV2.LC.IsLocalNorm K L x v) ∧
      Even s.card := by
  obtain ⟨s, hs, heven⟩ := Work.HilbertSymbolGeneral.hilbertReciprocityTwo K L h2 x
  refine ⟨s, fun v hv => ?_, hs, heven⟩
  by_contra hvT
  exact (hs v).mp hv
    (isLocalNorm_of_notMem_of_finite_unramified h2 x T hfin hinf v hvT)

end Work.SSGRoute.ZDataTwo
