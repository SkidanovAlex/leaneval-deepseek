/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_finite
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localUnits_iff_localAlgebraMapUnits
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver

/-!
# The Galois-fixed idèles are the idèles of the base field

For `L / K` a finite Galois extension of number fields, the inclusion of idèle groups
`φ : 𝕀[K] →* 𝕀[L]` whose `w`-component is the canonical local embedding
`K_{u w}ˣ →* L_wˣ` has as its range exactly the subgroup of `Gal(L/K)`-invariant idèles of `L`:

`NK.GlobalCFT.Inclusion.globalCFT_fixed_idele_mem_range` (the direction proved here) and
`NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_smul` (the converse).

This is the `H⁰`-computation `𝕀[K] = (𝕀[L])^{Gal(L/K)}` for idèles, the local-global input of the
identification `C_K ≅ (C_L)^{Gal(L/K)}` of idèle class groups (CoNF I §4, or Neukirch's
*Algebraic Number Theory* VI §1).

## The proof

Let `x : 𝕀[L]` be fixed by `Gal(L/K)`.  The argument has three steps.

* *Componentwise lifting.*  A fixed idèle is equivariant for the canonical local isomorphisms
  `Place.localRingEquiv σ w : L_w ≃+* L_{σ w}` (`globalCFT_fixed_component_equivariant`), so its
  component at `w` is fixed by the decomposition group `D_w`; by the local fixed-field theorem --
  the decomposition group *is* the local Galois group
  (`Galois.globalCFT_localFixed_finite`, `Galois.globalCFT_localFixed_infinite`) -- that component
  lies in the image of the local algebra map (`globalCFT_fixed_component_mem_range`).

* *Descent to the base.*  Choosing one place `w₀ v` of `L` above each place `v` of `K` and a local
  preimage `y v` of `x (w₀ v)` gives a family `y` on the places of `K`; transitivity of the Galois
  action on the places above `v` (`globalCFT_exists_smul_eq_of_liesOver`) together with the
  equivariance of the local algebra maps
  (`Galois.globalCFT_localRingEquiv_localAlgebraMapUnits`) shows that `y v` is a local preimage of
  `x w` at *every* place `w` of `L` above `v` (`hy_eq`).

* *The restricted-product condition.*  If `y v` were not a local unit, then `x (w₀ v)` would not be
  a local unit either (`globalCFT_localUnits_iff_localAlgebraMapUnits`), so the set of places `v`
  where `y` fails to be a local unit is contained in the image under `u` of the finite set of
  places where `x` fails to be a local unit.  Hence `y` is an idèle (`hy_mem`), and `φ y = x` by
  the defining property of `φ`.
-/

-- the idèle group is a `def` unfolding to a restricted product, and the coercion of the local
-- units to a `Set` is only definitionally equal to the subgroup membership appearing in that
-- unfolding; the assembly below needs that unfolding to be transparent for `isDefEq`.
set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ### Elementary idèle bookkeeping -/

/-- Transport of an idèle component along an equality of places: `x b` is the transport of `x a`
along `a = b`.  (This is the form in which equalities of places of `L` are compared, the type
`Place.localField L ·` being a `match` on the place.) -/
theorem globalCFT_ideles_component_transport (x : Idele K) {a b : Place K} (h : a = b) :
    x b = h ▸ x a := by
  cases h
  rfl

/-- Every place of `K` has a place of `L` above it. -/
theorem globalCFT_exists_placeOver_of_finiteDimensional (v : Place K) :
    ∃ w : Place L, Place.LiesOver w v := by
  rcases v with v | Q
  · haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
    refine ⟨Place.ofInfinite w, Place.liesOver_ofInfinite ⟨?_⟩⟩
    have hh : (w.comap (algebraMap K L)).1 = v.1 := congrArg Subtype.val hw
    rw [← hh]
    rfl
  · obtain ⟨q, hq⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
      (K := K) (L := L) Q
    exact ⟨Place.ofFinite q, Place.liesOver_ofFinite hq⟩

/-! ### Step 1: the components of a fixed idèle are equivariant for the local isomorphisms -/

/-- **Equivariance of the components of a fixed idèle.**  If `x : 𝕀[L]` is fixed by `Gal(L/K)`,
then for every `σ` and every place `w` the local isomorphism `Place.localRingEquiv σ w` carries
the component `x w` to the component at `σ • w`. -/
theorem globalCFT_fixed_component_equivariant (x : Idele L) (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (σ : L ≃ₐ[K] L) (w : Place L) :
    Units.map (Place.localRingEquiv σ w).toMonoidHom (x w) = x (σ • w) := by
  have h := congrArg (fun y : Idele L => y w) (hx σ⁻¹)
  rw [Idele.smul_apply] at h
  rw [inv_inv] at h
  rw [← h]
  ext
  simp

/-- At a place `w` fixed by `σ`, the component of a fixed idèle is fixed by the local isomorphism
attached to `σ`.  This is the "fixed vector of the decomposition group" hypothesis of the local
fixed-field lemma. -/
theorem globalCFT_fixed_stabilizer_unit (x : Idele L) (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (σ : L ≃ₐ[K] L) (w : Place L) (hσ : σ • w = w) :
    Units.map (Place.localRingEquiv σ w).toMonoidHom (x w) = hσ.symm ▸ x w := by
  rw [globalCFT_fixed_component_equivariant x hx σ w]
  exact globalCFT_ideles_component_transport x hσ.symm

/-! ### Step 1 (continued): componentwise lifting to the local fields of `K` -/

/-- **Componentwise lifting.**  The component at `w` of a `Gal(L/K)`-fixed idèle is in the image
of the local algebra map `K_vˣ →* L_wˣ`, where `v` is the place of `K` below `w`.

The archimedean and the nonarchimedean cases are the local fixed-field theorems
`Galois.globalCFT_localFixed_infinite` and `Galois.globalCFT_localFixed_finite`; the mixed cases
are impossible because a place cannot be both archimedean and nonarchimedean
(`Place.isFinite_of_liesOver`). -/
theorem globalCFT_fixed_component_mem_range (x : Idele L) (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    {w : Place L} {v : Place K} (h : Place.LiesOver w v) :
    ∃ a : (Place.localField K v)ˣ, Place.localAlgebraMapUnits w v h a = x w := by
  rcases w with w | q <;> rcases v with v | Q
  · have hwv : w.LiesOver v := (Galois.globalCFT_liesOver_ofInfinite_iff w v).mp h
    exact Galois.globalCFT_localFixed_infinite hwv (x (Place.ofInfinite w))
      (fun σ hσ => globalCFT_fixed_stabilizer_unit x hx σ (Place.ofInfinite w) hσ)
  · rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h2 (Ne.symm (Place.ofInfinite_ne_ofFinite v' Q))
    · exact absurd h1 (Place.ofInfinite_ne_ofFinite w q')
  · rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h1 (Ne.symm (Place.ofInfinite_ne_ofFinite w' q))
    · exact absurd h2 (Place.ofInfinite_ne_ofFinite v Q')
  · have hqQ : q.asIdeal.LiesOver Q.asIdeal := by
      rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact absurd h1 (Ne.symm (Place.ofInfinite_ne_ofFinite w' q))
      · rw [Place.ofFinite_inj] at h1 h2
        rw [← h1, ← h2] at h3
        exact h3
    exact Galois.globalCFT_localFixed_finite hqQ (x (Place.ofFinite q))
      (fun σ hσ => globalCFT_fixed_stabilizer_unit x hx σ (Place.ofFinite q) hσ)

/-! ### The descent to the idèles of `K` -/

/-- **A Galois-fixed idèle is the image of an idèle of the base field.** -/
theorem globalCFT_fixed_idele_mem_range {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (x : 𝕀[L]) (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) : x ∈ φ.range := by
  classical
  -- choose one place of `L` above each place of `K`
  let w₀ : Place K → Place L :=
    fun v => Classical.choose (globalCFT_exists_placeOver_of_finiteDimensional (K := K) (L := L) v)
  have hw₀ : ∀ v : Place K, Place.LiesOver (w₀ v) v :=
    fun v => Classical.choose_spec (globalCFT_exists_placeOver_of_finiteDimensional (K := K) (L := L) v)
  have hfix : ∀ (σ : L ≃ₐ[K] L) (w : Place L),
      Units.map (Place.localRingEquiv σ w).toMonoidHom (x w) = x (σ • w) :=
    fun σ w => globalCFT_fixed_component_equivariant x hx σ w
  -- the local preimage of the component of `x` at the chosen place above `v`
  have hloc : ∀ v : Place K, ∃ a : (Place.localField K v)ˣ,
      Place.localAlgebraMapUnits (w₀ v) v (hw₀ v) a = x (w₀ v) :=
    fun v => globalCFT_fixed_component_mem_range x hx (hw₀ v)
  let yFun : (v : Place K) → (Place.localField K v)ˣ := fun v => Classical.choose (hloc v)
  have hyFun : ∀ v : Place K,
      Place.localAlgebraMapUnits (w₀ v) v (hw₀ v) (yFun v) = x (w₀ v) :=
    fun v => Classical.choose_spec (hloc v)
  -- `yFun` is an idèle: its local units are the local units of `x`, up to the finite set of
  -- places where `x` is not a local unit
  have hbad : {w : Place L | x w ∉ Place.localUnits L w}.Finite :=
    (Filter.eventually_cofinite).mp x.2
  have hy_mem : ∀ᶠ v in Filter.cofinite, yFun v ∈ Place.localUnits K v := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (hbad.image u) ?_
    rintro v hv
    refine ⟨w₀ v, ?_, ?_⟩
    · intro hxw
      exact hv ((globalCFT_localUnits_iff_localAlgebraMapUnits (K := K) (L := L) (hw₀ v)
        (yFun v)).mp (by rw [hyFun v]; exact hxw))
    · exact globalCFT_liesOver_unique (hu (w₀ v)) (hw₀ v)
  -- the value `yFun v` is a local preimage of `x w` at *every* place `w` of `L` above `v`:
  -- any two places above `v` are conjugate, and the local algebra maps are equivariant
  have hy_eq : ∀ (v : Place K) (w : Place L) (h : Place.LiesOver w v),
      Place.localAlgebraMapUnits w v h (yFun v) = x w := by
    intro v w h
    obtain ⟨σ, hσ⟩ := globalCFT_exists_smul_eq_of_liesOver (hw₀ v) h
    subst hσ
    have h1 := Galois.globalCFT_localRingEquiv_localAlgebraMapUnits σ (hw₀ v) h (yFun v)
    rw [hyFun v, hfix σ (w₀ v)] at h1
    exact h1.symm
  refine ⟨(⟨yFun, hy_mem⟩ : 𝕀[K]), ?_⟩
  apply Idele.ext
  intro w
  rw [hφ]
  exact hy_eq (u w) w (hu w)

end

end NK.GlobalCFT.Inclusion
