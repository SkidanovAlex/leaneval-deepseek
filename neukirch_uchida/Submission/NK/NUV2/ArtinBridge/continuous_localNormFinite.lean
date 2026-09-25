import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.NUV2.ArtinBridge.continuous_algebraNorm
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion

set_option linter.style.haveILetI false

/-!
# Continuity of the local norm `N_{L_q/K_Q}` on local units

For a finite extension of number fields `L / K`, a nonzero prime `q` of `𝓞 L` lying over the
prime `Q` of `𝓞 K`, the local norm

`N_{L_q/K_Q} : L_qˣ → K_Qˣ`   (`NK.GlobalCFT.Place.localNormFinite`)

is continuous.

Unfolding the definition, the local norm is `Units.map (Algebra.norm K_Q)` for the `K_Q`-algebra
structure on `L_q` induced by the continuous ring homomorphism
`Commons.RingTheory.Henselian.adicCompletionMap Q q h : K_Q →+* L_q`.  The two ingredients are:

* the algebra norm of a finite-dimensional normed algebra over a complete nontrivially normed
  field is continuous (`NK.NUV2.ArtinBridge.continuous_algebraNorm`), where
  `L_q` is a finite-dimensional `K_Q`-vector space
  (`Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion`) with continuous
  scalar multiplication (the algebra map `K_Q → L_q` is continuous,
  `Commons.RingTheory.Henselian.adicCompletionMap_continuous`);
* `Units.map` of a continuous monoid homomorphism is continuous on the groups of units
  (`Continuous.units_map`).

A technical remark on the proof: the type class instances are introduced with `letI` rather than
`haveI`.  The local `NontriviallyNormedField` instance shadows the canonical `Field` instance of
`K_Q` for instance search; with `letI` the shadowing data is definitionally equal to the original
one, so that the local norm computed with the local instances is *definitionally* the one appearing
in `NK.GlobalCFT.Place.localNormFinite`.
-/

namespace NK.NUV2.ArtinBridge

/-- **Continuity of the local norm at a finite place.** -/
theorem continuous_localNormFinite {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : q.asIdeal.LiesOver Q.asIdeal) :
    Continuous (NK.GlobalCFT.Place.localNormFinite q Q h) := by
  -- `K_Q` is a complete nontrivially normed field.
  letI nf : NontriviallyNormedField (Q.adicCompletion K) :=
    Valued.toNontriviallyNormedField (Q.adicCompletion K) (WithZero (Multiplicative ℤ))
  -- the `K_Q`-algebra structure on `L_q` via the (continuous) completion map
  letI alg : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q h).toAlgebra
  -- scalar multiplication is continuous, since the algebra map is continuous
  haveI hcs : ContinuousSMul (Q.adicCompletion K) (q.adicCompletion L) :=
    continuousSMul_of_algebraMap (Q.adicCompletion K) (q.adicCompletion L) (by
      rw [RingHom.algebraMap_toAlgebra]
      exact Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q h)
  -- `L_q` is a finite dimensional `K_Q`-vector space
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q h
  have key : Continuous (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)) :=
    (continuous_algebraNorm (𝕜 := Q.adicCompletion K)
      (A := q.adicCompletion L)).units_map (Algebra.norm (Q.adicCompletion K))
  rw [show NK.GlobalCFT.Place.localNormFinite q Q h = Units.map (Algebra.norm
      (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) from rfl]
  exact key

end NK.NUV2.ArtinBridge
