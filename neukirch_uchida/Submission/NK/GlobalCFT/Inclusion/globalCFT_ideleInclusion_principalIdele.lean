import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists

/-!
# The idèle inclusion respects principal idèles

For a finite extension `L / K` of number fields and a map `u : Place L → Place K` sending each
place of `L` to a place of `K` below it, any monoid homomorphism `φ : 𝕀[K] →* 𝕀[L]` whose
`w`-component is the local embedding `K_{u w}ˣ →* L_wˣ` sends the principal idèle `(y)` of
`K` to the principal idèle `(y)` of `L`.

This is the "diagonal" compatibility of the local embeddings with the diagonal embeddings
of the global units, and it is what makes the inclusion `C_K → C_L^Gal(L/K)` well defined.

## Main result

* `NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele`.
-/

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.GlobalCFT.Inclusion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Unfolding the local unit embeddings

The definition of `Place.localAlgebraMapUnits` is a case distinction, and the third argument (the
proof that `w` lies over `v`) is never used: the value only depends on the *types* of the places.
The following lemmas compute it in the two nontrivial cases. -/

private theorem localAlgebraMapUnits_congr (w : Place L) (v : Place K)
    (h h' : Place.LiesOver w v) :
    Place.localAlgebraMapUnits w v h = Place.localAlgebraMapUnits w v h' := rfl

private theorem localAlgebraMapUnits_ofInfinite (w : InfinitePlace L) (v : InfinitePlace K)
    [hwv : w.LiesOver v] (h : Place.LiesOver (Place.ofInfinite w) (Place.ofInfinite v)) :
    Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v) h =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  rw [localAlgebraMapUnits_congr (Place.ofInfinite w) (Place.ofInfinite v) h
    (Place.liesOver_ofInfinite hwv)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hwv]

private theorem localAlgebraMapUnits_ofFinite (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
  rw [localAlgebraMapUnits_congr (Place.ofFinite q) (Place.ofFinite Q) h
    (Place.liesOver_ofFinite hqQ)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hqQ]

/-! ### Compatibility of the local algebraic embeddings with the global algebra maps

At a finite place this is `adicCompletionMap_apply`; at an infinite place we combine the
scalar tower `K → K_v → L_w` (which is the defining property of `completionMap`) with the
scalar tower `K → L → L_w`. -/

private theorem adicCompletionMap_algebraMap (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) (h : q.asIdeal.LiesOver Q.asIdeal) (x : K) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q h (algebraMap K (Q.adicCompletion K) x) =
      algebraMap L (q.adicCompletion L) (algebraMap K L x) := by
  have h1 : algebraMap K (Q.adicCompletion K) x = (x : Q.adicCompletion K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  have h2 : (algebraMap K L x : q.adicCompletion L) =
      algebraMap L (q.adicCompletion L) (algebraMap K L x) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  rw [h1, ← h2, Commons.RingTheory.Henselian.adicCompletionMap_apply]

private theorem completionMap_algebraMap (w : InfinitePlace L) (v : InfinitePlace K)
    [hwv : w.LiesOver v] (x : K) :
    NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion x) =
      algebraMap L w.Completion (algebraMap K L x) := by
  -- the scalar tower `K → L → L_w`
  haveI hST : IsScalarTower K L w.Completion := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have e2 := NumberField.InfinitePlace.Completion.algebraMap_toCompletion (v := w)
      (R := L) (algebraMap K L a)
    have e3 := NumberField.InfinitePlace.Completion.algebraMap_toCompletion (v := w) (R := K) a
    apply NumberField.InfinitePlace.Completion.ext
    rw [e3, e2, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def]
    simp [WithAbs.algebraMap_right_apply]
  rw [← RingHom.algebraMap_toAlgebra (NumberField.LiesOver.completionMap (v := v) (w := w))]
  rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion x]
  exact IsScalarTower.algebraMap_apply K L w.Completion x

/-! ### The componentwise statement -/

private theorem principalIdele_comp (w : Place L) (v : Place K) (h : Place.LiesOver w v)
    (y : Kˣ) :
    Place.localAlgebraMapUnits w v h (Units.map (algebraMap K (Place.localField K v)) y)
      = Units.map (algebraMap L (Place.localField L w))
          (Units.map (algebraMap K L).toMonoidHom y) := by
  rcases w with w' | q <;> rcases v with v' | Q
  · rcases h with ⟨w'', v'', hw, hv, hL⟩ | ⟨q', Q', hw, hv, hQ⟩
    · have hL' : w'.LiesOver v' := by
        rw [← Place.ofInfinite_inj.mp hw, ← Place.ofInfinite_inj.mp hv] at hL
        exact hL
      haveI := hL'
      rw [localAlgebraMapUnits_ofInfinite w' v' (Or.inl ⟨w'', v'', hw, hv, hL⟩)]
      apply Units.ext
      simp only [Units.coe_map]
      exact completionMap_algebraMap w' v' (y : K)
    · exact absurd hw (by simp)
  · rcases h with ⟨w'', v'', hw, hv, hL⟩ | ⟨q', Q', hw, hv, hQ⟩
    · exact absurd hv (by simp)
    · exact absurd hw (by simp)
  · rcases h with ⟨w'', v'', hw, hv, hL⟩ | ⟨q', Q', hw, hv, hQ⟩
    · exact absurd hw (by simp)
    · exact absurd hv (by simp)
  · rcases h with ⟨w'', v'', hw, hv, hL⟩ | ⟨q', Q', hw, hv, hQ⟩
    · exact absurd hw (by simp)
    · have hQ' : q.asIdeal.LiesOver Q.asIdeal := by
        rw [← Place.ofFinite_inj.mp hw, ← Place.ofFinite_inj.mp hv] at hQ
        exact hQ
      haveI := hQ'
      rw [localAlgebraMapUnits_ofFinite q Q (Or.inr ⟨q', Q', hw, hv, hQ⟩)]
      apply Units.ext
      simp only [Units.coe_map]
      exact adicCompletionMap_algebraMap q Q hQ' (y : K)

/-! ### The theorem -/

theorem globalCFT_ideleInclusion_principalIdele {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) (y : Kˣ) :
    φ (Idele.principalIdele K y) =
      Idele.principalIdele L (Units.map (algebraMap K L).toMonoidHom y) := by
  apply Idele.ext
  intro w
  rw [hφ]
  simp only [Idele.principalIdele_apply]
  exact principalIdele_comp w (u w) (hu w) y

end NK.GlobalCFT.Inclusion
