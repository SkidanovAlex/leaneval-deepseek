import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits

/-!
# Continuity of the inclusion of idèles

For `L / K` a finite extension of number fields, a choice of a place `u w` of `K` above every
place `w` of `L`, and the induced local embeddings `K_{u w}ˣ →* L_wˣ`, the diagonal of these local
embeddings assembles into a continuous monoid homomorphism of idèle groups
`𝕀 K →* 𝕀 L`, whose `w`-th component is the local embedding.

The algebraic half (existence of the monoid homomorphism with the prescribed components) is
`NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists`; the content here is the *continuity*
of the local maps, hence of the restricted product map
(`RestrictedProduct.mapAlong_continuous`).

## Main results

* `NK.NUV2.continuous_localAlgebraMapUnits`: the local map `K_vˣ →* L_wˣ` is continuous.
* `NK.NUV2.exists_continuous_ideleIncl`: the idèle inclusion is continuous.
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2

open NK.GlobalCFT

/-- The canonical local map `K_vˣ →* L_wˣ` attached to a place `w` of `L` lying over a place `v`
of `K` is continuous.  At an archimedean place it is induced by the (continuous) map of
completions `K_v → L_w`; at a nonarchimedean place by the (continuous) map of adic completions;
in the two mixed cases the hypothesis `LiesOver` is contradictory. -/
theorem continuous_localAlgebraMapUnits {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {w : Place L} {v : Place K} (h : Place.LiesOver w v) :
    Continuous (Place.localAlgebraMapUnits w v h) := by
  classical
  rcases w with w | q <;> rcases v with v | Q
  · -- both places archimedean: the map of completions is continuous
    have hL : w.LiesOver v := by
      rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · rw [Place.ofInfinite_inj] at h1 h2
        rw [← h1, ← h2] at h3
        exact h3
      · exact absurd h1 (Place.ofInfinite_ne_ofFinite w q')
    dsimp only [Place.localAlgebraMapUnits]
    rw [dif_pos hL]
    exact (NumberField.LiesOver.continuous_completionMap (v := v) (w := w)).units_map _
  · -- `w` archimedean, `v` finite: impossible
    exact absurd h (by
      intro hh
      rcases (Place.liesOver_iff _ _).mp hh with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact (Place.ofInfinite_ne_ofFinite v' Q) h2.symm
      · exact (Place.ofInfinite_ne_ofFinite w q') h1)
  · -- `w` finite, `v` archimedean: impossible
    exact absurd h (by
      intro hh
      rcases (Place.liesOver_iff _ _).mp hh with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact (Place.ofInfinite_ne_ofFinite w' q) h1.symm
      · exact (Place.ofInfinite_ne_ofFinite v Q') h2)
  · -- both places finite: the map of adic completions is continuous
    have hq : q.asIdeal.LiesOver Q.asIdeal := by
      rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w' q)
      · rw [Place.ofFinite_inj] at h1 h2
        rw [← h1, ← h2] at h3
        exact h3
    dsimp only [Place.localAlgebraMapUnits]
    rw [dif_pos hq]
    exact (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq).units_map _

/-- **The idèle inclusion is continuous.**  For `L / K` a finite extension of number fields and a
choice `u` of a place of `K` above every place of `L`, the diagonal of the local embeddings
`K_{u w}ˣ →* L_wˣ` is a continuous monoid homomorphism `𝕀 K →* 𝕀 L` with the prescribed
components. -/
theorem exists_continuous_ideleIncl {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K)
    (hu : ∀ w, NK.GlobalCFT.Place.LiesOver w (u w)) :
    ∃ φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele L, Continuous φ ∧
      ∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L),
        φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)) := by
  classical
  -- the map on places is cofinite-to-cofinite: only finitely many places lie over a given one
  have htend : Filter.Tendsto u Filter.cofinite Filter.cofinite :=
    Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v =>
      (Inclusion.globalCFT_liesOver_fiber_finite (K := K) (L := L) v).subset fun w hw => by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
        rw [← hw]
        exact hu w
  let R₁ : Place K → Type _ := fun v => (Place.localField K v)ˣ
  let R₂ : Place L → Type _ := fun w => (Place.localField L w)ˣ
  let B₁ : (v : Place K) → Subgroup (R₁ v) := fun v => Place.localUnits K v
  let B₂ : (w : Place L) → Subgroup (R₂ w) := fun w => Place.localUnits L w
  let Ψ : ∀ w : Place L, R₁ (u w) →* R₂ w :=
    fun w => Place.localAlgebraMapUnits w (u w) (hu w)
  have hΨ : ∀ᶠ w in Filter.cofinite, Set.MapsTo (Ψ w) (B₁ (u w)) (B₂ w) :=
    Filter.Eventually.of_forall fun w =>
      Inclusion.globalCFT_localAlgebraMapUnits_mapsTo_localUnits (hu w)
  -- the restricted product map, as a monoid homomorphism
  let Φ : (Πʳ i : Place K, [R₁ i, B₁ i]) →* (Πʳ j : Place L, [R₂ j, B₂ j]) :=
    RestrictedProduct.mapAlongMonoidHom R₁ R₂ u htend Ψ hΨ
  -- and its continuity, from the continuity of the local maps
  have hcont : Continuous (RestrictedProduct.mapAlong
      (A₁ := fun v => ↑(B₁ v)) (A₂ := fun w => ↑(B₂ w)) R₁ R₂ u htend
      (fun w r => Ψ w r) hΨ) :=
    RestrictedProduct.mapAlong_continuous (A₁ := fun v => ↑(B₁ v)) (A₂ := fun w => ↑(B₂ w))
      R₁ R₂ u htend (fun w r => Ψ w r) hΨ
      (fun w => continuous_localAlgebraMapUnits (hu w))
  let F : Idele K → Idele L := ⇑Φ
  have hcontF : Continuous F := hcont
  have hF1 : F 1 = 1 := map_one Φ
  have hF2 : ∀ x y, F (x * y) = F x * F y := fun x y => map_mul Φ x y
  let φ : Idele K →* Idele L :=
    { toFun := F, map_one' := hF1, map_mul' := hF2 }
  refine ⟨φ, hcontF, ?_⟩
  intro x w
  rfl

end NK.NUV2
