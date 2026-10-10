import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.NK.HassePrinciple.IdeleCocycle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A uniformizer fixed by the local automorphisms of the decomposition group

Let `L / K` be a finite Galois extension of number fields, `Q` a place of `K` and `q` a place of
`L` above `Q`.  The stabiliser `H_q = MulAction.stabilizer Gal(L/K) q` of the place `q` acts on
the local field `L_q` by the local automorphisms `localAutHom q`.

If `q` is unramified over `Q` (`ramificationIdx = 1`) then the local extension `L_q / K_Q` is
unramified, so the image of a uniformizer of `K_Q` under the canonical map
`K_Q →+* L_q` of adic completions is again a uniformizer of `L_q`; and since the action of `H_q`
on `L_q` is by `K_Q`-algebra automorphisms (the local automorphisms fix the image of the
completion of the base field), this uniformizer is fixed by every element of `H_q`.

This is the local ingredient for the vanishing of the `H¹` of the units of a single place, and
hence for the Hasse principle.

## Main results

* `NK.HassePrinciple.localAut_adicCompletionMap_fixed`: the local automorphisms attached to the
  stabiliser of a finite place fix the image of `K_Q` in `L_q`;
* `NK.HassePrinciple.exists_fixed_uniformizer_localAutHom`: an unramified place has a
  uniformizer fixed by the whole stabiliser.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.HassePrinciple

open NK.GlobalCFT

/-- **The local automorphisms attached to the stabiliser of a finite place fix the image of the
base local field.**  For `σ` in the stabiliser of `q`, the local automorphism `localAutHom q σ`
of `L_q` fixes the image of `K_Q` under the canonical map of adic completions.

The proof is a density argument: both sides are continuous, and they agree on the dense image of
`K` in `K_Q`, where the statement reduces to `localAut_algebraMap` and the fact that `σ` is a
`K`-algebra automorphism. -/
theorem localAut_adicCompletionMap_fixed {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q)) (y : Q.adicCompletion K) :
    localAut (Place.ofFinite q) σ
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq y)
      = Commons.RingTheory.Henselian.adicCompletionMap Q q hq y := by
  have hdense : DenseRange (algebraMap K (Q.adicCompletion K)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := NumberField.RingOfIntegers K) K Q
  have hcont : Continuous (fun y : Q.adicCompletion K =>
      localAut (Place.ofFinite q) σ
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq y)) :=
    (localAut_continuous (Place.ofFinite q) σ).comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq)
  have hEq : (fun y : Q.adicCompletion K => localAut (Place.ofFinite q) σ
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq y))
      = fun y : Q.adicCompletion K =>
          Commons.RingTheory.Henselian.adicCompletionMap Q q hq y := by
    refine DenseRange.equalizer hdense hcont
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq) ?_
    funext k
    simp only [Function.comp_apply]
    have hk : algebraMap K (Q.adicCompletion K) k = (k : Q.adicCompletion K) :=
      NK.GlobalCFT.Galois.globalCFT_algebraMap_eq_coe Q k
    rw [hk, Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq k]
    rw [← NK.GlobalCFT.Galois.globalCFT_algebraMap_eq_coe (q := q) (algebraMap K L k)]
    rw [localAut_algebraMap (Place.ofFinite q) σ (algebraMap K L k),
      AlgEquiv.commutes σ.1 k]
  exact congr_fun hEq y


/-- **An unramified finite place of a Galois extension has a uniformizer fixed by the whole
stabiliser.**  If the ramification index of `q` over `Q` is `1`, the image of a uniformizer of
`K_Q` under the map of adic completions is a uniformizer of `L_q` which is fixed by every local
automorphism attached to an element of the decomposition group of `q`. -/
theorem exists_fixed_uniformizer_localAutHom {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    ∃ π : (q.adicCompletion L)ˣ,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (π : q.adicCompletion L)
        = WithZero.exp (-1) ∧
      ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) (NK.GlobalCFT.Place.ofFinite q),
        (NK.HassePrinciple.localAutHom (NK.GlobalCFT.Place.ofFinite q) σ)
          (π : q.adicCompletion L) = (π : q.adicCompletion L) := by
  obtain ⟨c, hc, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one Q
  set z : q.adicCompletion L :=
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq (c : Q.adicCompletion K) with hz
  have hzval : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) z
      = WithZero.exp (-1) := by
    rw [hz, Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq, he,
      pow_one, hc]
  have hzne : z ≠ 0 := by
    intro h0
    have h1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) z = 0 := by
      rw [h0]
      exact map_zero _
    rw [hzval] at h1
    exact WithZero.exp_ne_zero h1
  refine ⟨Units.mk0 z hzne, ?_, ?_⟩
  · rw [Units.val_mk0]
    exact hzval
  · intro σ
    rw [Units.val_mk0]
    change localAut (NK.GlobalCFT.Place.ofFinite q) σ z = z
    rw [hz]
    exact localAut_adicCompletionMap_fixed Q q hq σ (c : Q.adicCompletion K)

end NK.HassePrinciple
