import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.NK.GlobalCFTdeep.Transport.IdeleTransport
import Submission.NK.GlobalCFTdeep.Transport.NormTransportAux
import Submission.NK.GlobalCFTdeep.Transport.fiberInfinite_map_placeEquiv
import Submission.NK.GlobalCFTdeep.Transport.primesOverFinite_map_placeEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle norm is natural for the transport along a compatible pair of ring equivalences

See the module docstring of `NormTransportAux.lean` for the construction of the local field
transport `localFieldIso`.  This file shows that the idèlic norm commutes with it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped NumberField RestrictedProduct WithZero WithZeroTopology
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

namespace NormTransport

open NK.GlobalCFT

/-! ## Elementary descriptions of the local algebra maps -/

theorem adicMap_coe {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (y : K) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K) =
      (algebraMap K L y : q.adicCompletion L) := by
  rw [Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq y]

theorem coe_eq_algebraMap_adic {K : Type*} [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) (y : K) :
    (y : Q.adicCompletion K) = algebraMap K (Q.adicCompletion K) y := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp

theorem adicMap_algebraMap {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (y : K) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq
        (algebraMap K (Q.adicCompletion K) y) =
      algebraMap L (q.adicCompletion L) (algebraMap K L y) := by
  rw [← coe_eq_algebraMap_adic Q y, adicMap_coe Q q hq y]
  exact coe_eq_algebraMap_adic q (algebraMap K L y)

theorem completionMap_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    {v : NumberField.InfinitePlace K} {w : NumberField.InfinitePlace L} [w.LiesOver v] (x : K) :
    NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion x) =
      algebraMap L w.Completion (algebraMap K L x) := by
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply,
    NumberField.LiesOver.completionMap_coe, WithAbs.algebraMap_left_apply,
    WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs,
    ← NumberField.InfinitePlace.Completion.algebraMap_apply]

/-! ## The local isomorphisms, on the image of the base field -/

theorem localFieldIso_algebraMap_finite {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    localFieldIso e (Place.ofFinite Q) (algebraMap K (Q.adicCompletion K) x) =
      algebraMap K' ((finitePlaceEquiv e Q).adicCompletion K') (e x) :=
  localFieldIso_algebraMap e (Place.ofFinite Q) x

theorem localFieldIso_algebraMap_infinite {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') (w : NumberField.InfinitePlace K) (x : K) :
    localFieldIso e (Place.ofInfinite w) (algebraMap K w.Completion x) =
      algebraMap K' (infinitePlaceEquiv e w).Completion (e x) :=
  localFieldIso_algebraMap e (Place.ofInfinite w) x

/-! ## The local isomorphisms commute with the local algebra maps -/

theorem localFieldIso_adicCompletionMap
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hq' : (finitePlaceEquiv eL q).asIdeal.LiesOver (finitePlaceEquiv eK Q).asIdeal) :
    ∀ x : Q.adicCompletion K,
      localFieldIso eL (Place.ofFinite q)
          (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x) =
        Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
          (finitePlaceEquiv eL q) hq' (localFieldIso eK (Place.ofFinite Q) x) := by
  have hg : Continuous (fun x : Q.adicCompletion K =>
      localFieldIso eL (Place.ofFinite q)
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x)) :=
    (localFieldIso_continuous eL (Place.ofFinite q)).comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq)
  have hh : Continuous (fun x : Q.adicCompletion K =>
      Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
        (finitePlaceEquiv eL q) hq' (localFieldIso eK (Place.ofFinite Q) x)) :=
    (Commons.RingTheory.Henselian.adicCompletionMap_continuous _ _ hq').comp
      (localFieldIso_continuous eK (Place.ofFinite Q))
  have hfun := DenseRange.equalizer
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q) hg hh (by
      funext y
      show localFieldIso eL (Place.ofFinite q)
          (Commons.RingTheory.Henselian.adicCompletionMap Q q hq
            (algebraMap K (Q.adicCompletion K) y)) =
        Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
          (finitePlaceEquiv eL q) hq'
          (localFieldIso eK (Place.ofFinite Q) (algebraMap K (Q.adicCompletion K) y))
      rw [adicMap_algebraMap Q q hq y,
        localFieldIso_algebraMap_finite eL q (algebraMap K L y), hcomp y,
        localFieldIso_algebraMap_finite eK Q y,
        adicMap_algebraMap (finitePlaceEquiv eK Q) (finitePlaceEquiv eL q) hq' (eK y)])
  intro x
  exact congrFun hfun x

theorem localFieldIso_completionMap
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K)
    (hw : w.LiesOver v)
    (hw' : (infinitePlaceEquiv eL w).LiesOver (infinitePlaceEquiv eK v)) :
    ∀ x : v.Completion,
      localFieldIso eL (Place.ofInfinite w)
          (NumberField.LiesOver.completionMap (v := v) (w := w) x) =
        NumberField.LiesOver.completionMap (v := infinitePlaceEquiv eK v)
          (w := infinitePlaceEquiv eL w)
          (localFieldIso eK (Place.ofInfinite v) x) := by
  letI : w.LiesOver v := hw
  letI : (infinitePlaceEquiv eL w).LiesOver (infinitePlaceEquiv eK v) := hw'
  have hdense : DenseRange (algebraMap K v.Completion) := by
    have h1 : DenseRange (fun x : K => (WithAbs.toAbs v.1 x : v.1.Completion)) :=
      DenseRange.comp (g := fun y : WithAbs v.1 => (y : v.1.Completion))
        (f := WithAbs.toAbs v.1)
        (UniformSpace.Completion.denseRange_coe (α := WithAbs v.1))
        (WithAbs.toAbs_bijective v.1).surjective.denseRange
        (UniformSpace.Completion.continuous_coe (WithAbs v.1))
    have h2 : DenseRange (fun x : K => (NumberField.InfinitePlace.Completion.ofCompletion (v := v)
          ((WithAbs.toAbs v.1 x : WithAbs v.1) : v.1.Completion))) :=
      DenseRange.comp (g := NumberField.InfinitePlace.Completion.ofCompletion (v := v))
        (f := fun x : K => (WithAbs.toAbs v.1 x : WithAbs v.1))
        (by simpa using (NumberField.InfinitePlace.Completion.ofCompletion_surjective v).denseRange)
        h1
        (NumberField.InfinitePlace.Completion.continuous_ofCompletion v)
    have hfun : ⇑(algebraMap K v.Completion) = fun x : K =>
        (NumberField.InfinitePlace.Completion.ofCompletion (v := v)
          ((WithAbs.toAbs v.1 x : WithAbs v.1) : v.1.Completion)) := by
      funext x
      rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
    rwa [hfun]
  have hg : Continuous (fun x : v.Completion =>
      localFieldIso eL (Place.ofInfinite w)
        (NumberField.LiesOver.completionMap (v := v) (w := w) x)) :=
    (localFieldIso_continuous eL (Place.ofInfinite w)).comp
      (NumberField.LiesOver.continuous_completionMap (v := v) (w := w))
  have hh : Continuous (fun x : v.Completion =>
      NumberField.LiesOver.completionMap (v := infinitePlaceEquiv eK v)
        (w := infinitePlaceEquiv eL w) (localFieldIso eK (Place.ofInfinite v) x)) :=
    (NumberField.LiesOver.continuous_completionMap (v := infinitePlaceEquiv eK v)
      (w := infinitePlaceEquiv eL w)).comp
      (localFieldIso_continuous eK (Place.ofInfinite v))
  have hfun := DenseRange.equalizer hdense hg hh (by
      funext y
      show localFieldIso eL (Place.ofInfinite w)
          (NumberField.LiesOver.completionMap (v := v) (w := w)
            (algebraMap K v.Completion y)) =
        NumberField.LiesOver.completionMap (v := infinitePlaceEquiv eK v)
          (w := infinitePlaceEquiv eL w)
          (localFieldIso eK (Place.ofInfinite v) (algebraMap K v.Completion y))
      rw [completionMap_algebraMap (v := v) (w := w) y,
        localFieldIso_algebraMap_infinite eL w (algebraMap K L y), hcomp y,
        localFieldIso_algebraMap_infinite eK v y,
        completionMap_algebraMap (v := infinitePlaceEquiv eK v)
          (w := infinitePlaceEquiv eL w) (eK y)])
  intro x
  exact congrFun hfun x

/-! ## The local norms commute with the local isomorphisms -/

theorem localNormFinite_commute
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hq' : (finitePlaceEquiv eL q).asIdeal.LiesOver (finitePlaceEquiv eK Q).asIdeal) :
    ∀ x : (Place.localField L (Place.ofFinite q))ˣ,
      Units.map (localFieldIso eK (Place.ofFinite Q)).toMonoidHom
          (Place.localNormFinite q Q hq x) =
        Place.localNormFinite (finitePlaceEquiv eL q) (finitePlaceEquiv eK Q) hq'
          (Units.map (localFieldIso eL (Place.ofFinite q)).toMonoidHom x) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  letI : Algebra ((finitePlaceEquiv eK Q).adicCompletion K')
      ((finitePlaceEquiv eL q).adicCompletion L') :=
    (Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
      (finitePlaceEquiv eL q) hq').toAlgebra
  let e₁ : Q.adicCompletion K ≃+* (finitePlaceEquiv eK Q).adicCompletion K' :=
    localFieldIso eK (Place.ofFinite Q)
  let e₂ : q.adicCompletion L ≃+* (finitePlaceEquiv eL q).adicCompletion L' :=
    localFieldIso eL (Place.ofFinite q)
  have hsquare : (Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
        (finitePlaceEquiv eL q) hq').comp
      (e₁ : Q.adicCompletion K →+* (finitePlaceEquiv eK Q).adicCompletion K') =
      (e₂ : q.adicCompletion L →+* (finitePlaceEquiv eL q).adicCompletion L').comp
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq) := by
    refine RingHom.ext fun y => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact (localFieldIso_adicCompletionMap eK eL hcomp q Q hq hq' y).symm
  intro x
  have hx := Algebra.norm_eq_of_equiv_equiv e₁ e₂ hsquare (x : q.adicCompletion L)
  have h := congrArg e₁ hx
  rw [RingEquiv.apply_symm_apply] at h
  rw [show Place.localNormFinite q Q hq =
        Units.map (Algebra.norm (Q.adicCompletion K)) from rfl,
    show Place.localNormFinite (finitePlaceEquiv eL q) (finitePlaceEquiv eK Q) hq' =
        Units.map (Algebra.norm ((finitePlaceEquiv eK Q).adicCompletion K')) from rfl]
  apply Units.ext
  change e₁ ((Algebra.norm (Q.adicCompletion K)) (x : q.adicCompletion L)) =
    (Algebra.norm ((finitePlaceEquiv eK Q).adicCompletion K')) (e₂ (x : q.adicCompletion L))
  exact h

theorem localNormInfinite_commute
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K)
    (hw : w.LiesOver v)
    (hw' : (infinitePlaceEquiv eL w).LiesOver (infinitePlaceEquiv eK v)) :
    ∀ x : (Place.localField L (Place.ofInfinite w))ˣ,
      Units.map (localFieldIso eK (Place.ofInfinite v)).toMonoidHom
          (Place.localNormInfinite w v x) =
        Place.localNormInfinite (infinitePlaceEquiv eL w) (infinitePlaceEquiv eK v)
          (Units.map (localFieldIso eL (Place.ofInfinite w)).toMonoidHom x) := by
  letI : w.LiesOver v := hw
  letI : (infinitePlaceEquiv eL w).LiesOver (infinitePlaceEquiv eK v) := hw'
  letI : Algebra (v.Completion) (w.Completion) :=
    (NumberField.LiesOver.completionMap (v := v) (w := w)).toAlgebra
  letI : Algebra ((infinitePlaceEquiv eK v).Completion) ((infinitePlaceEquiv eL w).Completion) :=
    (NumberField.LiesOver.completionMap (v := infinitePlaceEquiv eK v)
      (w := infinitePlaceEquiv eL w)).toAlgebra
  let e₁ : v.Completion ≃+* (infinitePlaceEquiv eK v).Completion :=
    localFieldIso eK (Place.ofInfinite v)
  let e₂ : w.Completion ≃+* (infinitePlaceEquiv eL w).Completion :=
    localFieldIso eL (Place.ofInfinite w)
  have hsquare : (NumberField.LiesOver.completionMap (v := infinitePlaceEquiv eK v)
        (w := infinitePlaceEquiv eL w)).comp
      (e₁ : v.Completion →+* (infinitePlaceEquiv eK v).Completion) =
      (e₂ : w.Completion →+* (infinitePlaceEquiv eL w).Completion).comp
        (NumberField.LiesOver.completionMap (v := v) (w := w)) := by
    refine RingHom.ext fun y => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact (localFieldIso_completionMap eK eL hcomp w v hw hw' y).symm
  intro x
  have hx := Algebra.norm_eq_of_equiv_equiv e₁ e₂ hsquare (x : w.Completion)
  have h := congrArg e₁ hx
  rw [RingEquiv.apply_symm_apply] at h
  rw [show Place.localNormInfinite w v =
        Units.map (Algebra.norm (v.Completion)) from rfl,
    show Place.localNormInfinite (infinitePlaceEquiv eL w) (infinitePlaceEquiv eK v) =
        Units.map (Algebra.norm ((infinitePlaceEquiv eK v).Completion)) from rfl]
  apply Units.ext
  change e₁ ((Algebra.norm (v.Completion)) (x : w.Completion)) =
    (Algebra.norm ((infinitePlaceEquiv eK v).Completion)) (e₂ (x : w.Completion))
  exact h

/-! ## The local norms commute with the local isomorphisms -/

end NormTransport

end NK.GlobalCFTdeep.Transport
