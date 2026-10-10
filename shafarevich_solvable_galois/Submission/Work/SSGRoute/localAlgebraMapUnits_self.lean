import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.LocalInputs.Inputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local algebra map at the trivial extension `K / K`

For a finite extension `L / K` of number fields and places `w | v` the canonical local embedding
`NK.GlobalCFT.Place.localAlgebraMapUnits w v h : K_vˣ →* L_wˣ` is the completion of the inclusion
`K → L`.  For the trivial extension `L = K` the place lies over itself and the local embedding is
the identity, at every place: `Work.SSGRoute.localAlgebraMapUnits_self`.

Since `NK.GlobalCFT.Place.localAlgebraMapUnits` is defined by a case distinction on the two
places, the statement reduces to the two "self" statements for the two completion maps:

* `Work.SSGRoute.completionMap_self` — the archimedean case: the map `K_v →+* K_v` induced by the
  identity `K → K` is the identity of `K_v`;
* `Work.SSGRoute.adicCompletionMap_self` — the nonarchimedean case: the map `K_Q →+* K_Q` induced
  by the identity `K → K` is the identity of `K_Q`.

Both are proved by density: the two maps agree on the dense image of `K` and are continuous ring
homomorphisms into a Hausdorff field.

(Public versions of these two identities are needed here because the copies appearing in
`NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self` are `private`.)
-/

namespace Work.SSGRoute

open NumberField IsDedekindDomain

/-- **The archimedean self case.** For the trivial extension `K / K` the ring homomorphism
`K_v →+* K_v` induced by the identity of `K` is the identity of the completion `K_v`. -/
lemma completionMap_self (K : Type) [Field K] [NumberField K] (w : InfinitePlace K)
    (h : NumberField.InfinitePlace.LiesOver (K := K) (L := K) w w) :
    @NumberField.LiesOver.completionMap K K _ _ _ w w h = RingHom.id w.Completion := by
  apply RingHom.ext
  intro x
  induction x using NumberField.InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq (NumberField.LiesOver.continuous_completionMap) continuous_id
  | ih a =>
      rw [NumberField.LiesOver.completionMap_coe]
      rfl

/-- **The nonarchimedean self case.** For the trivial extension `K / K` the ring homomorphism
`K_Q →+* K_Q` induced by the identity of `K` is the identity of the `Q`-adic completion. -/
lemma adicCompletionMap_self (K : Type) [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) (h : Q.asIdeal.LiesOver Q.asIdeal) :
    Commons.RingTheory.Henselian.adicCompletionMap Q Q h = RingHom.id (Q.adicCompletion K) := by
  apply RingHom.ext
  intro x
  have hclosed : IsClosed {x : Q.adicCompletion K |
      Commons.RingTheory.Henselian.adicCompletionMap Q Q h x = x} :=
    isClosed_eq (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q Q h) continuous_id
  have hd : DenseRange (algebraMap K (Q.adicCompletion K)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q
  refine hd.induction_on x hclosed ?_
  intro a
  exact Commons.RingTheory.Henselian.adicCompletionMap_apply Q Q h a

/-- The canonical local algebra map `K_wˣ →* K_wˣ` at the trivial extension `K / K` is the
identity. -/
theorem localAlgebraMapUnits_self (K : Type) [Field K] [NumberField K]
    (w : NK.GlobalCFT.Place K) (hw : NK.GlobalCFT.Place.LiesOver w w)
    (u : (NK.GlobalCFT.Place.localField K w)ˣ) :
    NK.GlobalCFT.Place.localAlgebraMapUnits w w hw u = u := by
  rcases w with w | q
  · -- archimedean place: `localAlgebraMapUnits` is the units map of `completionMap`
    have h : NumberField.InfinitePlace.LiesOver (K := K) (L := K) w w := by
      rcases hw with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · obtain rfl := Sum.inl_injective h1
        obtain rfl := Sum.inl_injective h2
        exact h3
      · exact (Sum.inl_ne_inr h1).elim
    have key : NK.GlobalCFT.Place.localAlgebraMapUnits (Sum.inl w) (Sum.inl w) hw
        = Units.map (@NumberField.LiesOver.completionMap K K _ _ _ w w h).toMonoidHom := by
      simp only [NK.GlobalCFT.Place.localAlgebraMapUnits]
      rw [dif_pos h]
    rw [key]
    apply Units.ext
    simp only [Units.coe_map]
    rw [completionMap_self K w h]
    rfl
  · -- nonarchimedean place: `localAlgebraMapUnits` is the units map of `adicCompletionMap`
    have hmem := hw
    rcases hmem with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact (Sum.inr_ne_inl h1).elim
    · obtain rfl := Sum.inr_injective h1
      obtain rfl := Sum.inr_injective h2
      have h := h3
      have key : NK.GlobalCFT.Place.localAlgebraMapUnits (Sum.inr q) (Sum.inr q) hw
          = Units.map (Commons.RingTheory.Henselian.adicCompletionMap q q h).toMonoidHom := by
        simp only [NK.GlobalCFT.Place.localAlgebraMapUnits]
        rw [dif_pos h]
      rw [key]
      apply Units.ext
      simp only [Units.coe_map]
      rw [adicCompletionMap_self K q h]
      rfl

end Work.SSGRoute
