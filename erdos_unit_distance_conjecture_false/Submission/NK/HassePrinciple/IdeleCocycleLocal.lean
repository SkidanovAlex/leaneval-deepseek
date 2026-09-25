/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local solutions of the idèle cocycle at the places

For a `1`-cocycle `c : Gal(L/K) → 𝕀_L` and a place `w` of `L`, the components
`σ ↦ c σ w` (`σ` in the stabiliser `H_w` of `w`) form a `1`-cocycle for the action of `H_w` on
`L_wˣ` by field automorphisms (`local_cocycle`), so Hilbert 90 produces a local solution `u` with
`c σ w = σ • u / u`.  At places outside the finite "bad set" (`badSet`, the places where some
`c g` is not a local unit together with the ramified places) the solution can be chosen to be a
local unit, by `exists_mem_localUnits_div_of_forall_eq_div`.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv
import Submission.NK.HassePrinciple.exists_mem_localUnits_div_of_forall_eq_div
import Submission.NK.HassePrinciple.exists_fixed_uniformizer_localAutHom

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.HassePrinciple

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable {c : (L ≃ₐ[K] L) → Idele L}

open Classical in
/-- The set of places of `L` at which the local solution cannot be chosen to be a local unit: the
places where some `c g` is not a local unit, and the ramified finite places. -/
def badSet (c : (L ≃ₐ[K] L) → Idele L) : Set (Place L) :=
  {w | ∃ g : L ≃ₐ[K] L, c g w ∉ Place.localUnits L w} ∪
  {w | ∃ q : HeightOneSpectrum (𝓞 L), w = Place.ofFinite q ∧
        q.asIdeal.ramificationIdx (𝓞 K) ≠ 1}

theorem badSet_finite (c : (L ≃ₐ[K] L) → Idele L) : (badSet (K := K) c).Finite := by
  classical
  rw [badSet]
  refine Set.Finite.union ?_ ?_
  · have hfin : ∀ g : L ≃ₐ[K] L,
        ({w : Place L | c g w ∉ Place.localUnits L w}).Finite := fun g => by
      have hg : ∀ᶠ w in Filter.cofinite, c g w ∈ Place.localUnits L w := (c g).2
      rw [Filter.eventually_cofinite] at hg
      exact hg
    convert Set.Finite.biUnion (Set.finite_univ (α := L ≃ₐ[K] L)) (fun g _ => hfin g) using 1
    ext w; simp
  · refine ((Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
        (K := K) (L := L)).image Place.ofFinite).subset ?_
    rintro w ⟨q, rfl, hq⟩
    exact ⟨q, hq, rfl⟩

/-- **The local cocycle condition at a place.** -/
theorem local_cocycle (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (w : Place L)
    (σ τ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    c (σ.1 * τ.1) w = Units.map (localAut w σ).toMonoidHom (c τ.1 w) * c σ.1 w := by
  have h1 := hc σ.1 τ.1
  have h2 : (σ.1 • c τ.1) w = Units.map (localAut w σ).toMonoidHom (c τ.1 w) :=
    smul_apply_stabilizer w σ (c τ.1)
  rw [h1, Idele.mul_apply, h2]

/-- **Existence of a local solution** of the cocycle at a place (Hilbert 90). -/
theorem exists_local_sol (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (w : Place L) :
    ∃ u : (Place.localField L w)ˣ,
      ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w,
        c σ.1 w = Units.map (localAut w σ).toMonoidHom u / u := by
  haveI : Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w) := Fintype.ofFinite _
  exact exists_units_div_of_isMulCocycle_ringEquiv (localAutHom w) (localAutHom_injective w)
    (fun σ => c σ.1 w) (fun σ τ => local_cocycle hc w σ τ)

/-- The prime of `𝓞 K` below a finite place of `L`. -/
theorem exists_heightOneSpectrum_under (q : HeightOneSpectrum (𝓞 L)) :
    ∃ Q : HeightOneSpectrum (𝓞 K), q.asIdeal.LiesOver Q.asIdeal :=
  ⟨⟨q.asIdeal.under (𝓞 K), inferInstance,
      Ideal.under_ne_bot (A := 𝓞 K) (P := q.asIdeal) q.ne_bot⟩, ⟨rfl⟩⟩

/-- **Existence of a local solution which is a local unit outside the bad set.** -/
theorem exists_local_sol_units (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (w : Place L)
    (hw : w ∉ badSet (K := K) c) :
    ∃ u : (Place.localField L w)ˣ, u ∈ Place.localUnits L w ∧
      ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w,
        c σ.1 w = Units.map (localAut w σ).toMonoidHom u / u := by
  classical
  haveI : Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w) := Fintype.ofFinite _
  obtain ⟨u₀, hu₀⟩ := exists_local_sol (K := K) hc w
  rcases w with x | q
  · exact ⟨u₀, Place.mem_localUnits_ofInfinite, hu₀⟩
  · have hq : q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      by_contra h
      exact hw (Or.inr ⟨q, rfl, h⟩)
    have hunits : ∀ g : L ≃ₐ[K] L,
        c g (Place.ofFinite q) ∈ Place.localUnits L (Place.ofFinite q) := by
      intro g
      by_contra h
      exact hw (Or.inl ⟨g, h⟩)
    obtain ⟨Q, hQ⟩ := exists_heightOneSpectrum_under (K := K) q
    obtain ⟨π, hπ, hπfix⟩ := exists_fixed_uniformizer_localAutHom (K := K) (L := L) Q q hQ hq
    obtain ⟨u, hu, hueq⟩ := exists_mem_localUnits_div_of_forall_eq_div (L := L) q
      (localAutHom (K := K) (Place.ofFinite q)) π hπ hπfix
      (fun σ : MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q) => c σ.1 (Place.ofFinite q))
      (fun σ => hunits σ.1) u₀ (fun σ => hu₀ σ)
    exact ⟨u, hu, hueq⟩

/-- **The chosen local solution** at a place: a solution of the local cocycle equation, chosen to
be a local unit whenever the place is not in the bad set. -/
noncomputable def localSol (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (w : Place L) :
    (Place.localField L w)ˣ := by
  classical
  exact if hw : w ∈ badSet (K := K) c then
    Classical.choose (exists_local_sol (K := K) hc w)
  else
    Classical.choose (exists_local_sol_units (K := K) hc w hw)

theorem localSol_spec (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (w : Place L)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    c σ.1 w = Units.map (localAut w σ).toMonoidHom (localSol hc w) / localSol hc w := by
  classical
  by_cases hw : w ∈ badSet (K := K) c
  · rw [localSol, dif_pos hw]
    exact (Classical.choose_spec (exists_local_sol (K := K) hc w)) σ
  · rw [localSol, dif_neg hw]
    exact (Classical.choose_spec (exists_local_sol_units (K := K) hc w hw)).2 σ

theorem localSol_mem_localUnits (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g)
    (w : Place L) (hw : w ∉ badSet (K := K) c) :
    localSol hc w ∈ Place.localUnits L w := by
  classical
  rw [localSol, dif_neg hw]
  exact (Classical.choose_spec (exists_local_sol_units (K := K) hc w hw)).1

end NK.HassePrinciple
