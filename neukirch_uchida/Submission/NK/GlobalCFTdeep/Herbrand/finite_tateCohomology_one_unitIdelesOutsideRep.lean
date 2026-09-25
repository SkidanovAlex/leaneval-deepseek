/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.UnitIdelesDefs
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tIdeles_mul_eq_unitIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_supportedIdelesRep

/-!
# Finiteness of `Ĥ¹` of the unit idèles outside `T`

Let `L/K` be a finite Galois extension of number fields with cyclic Galois group `G = Gal(L/K)`
and let `T` be a `G`-stable set of places of `L` which is exactly the union of the fibres of the
places in a finite set `S` of places of `K`.  The unit idèles outside `T`,

  `unitIdelesOutside T = ∏_{w ∉ T} U_w`  (idèles which are `1` on `T` and local units elsewhere),

form the kernel of the natural surjection `𝕀_{L,T} ↠ ∏_{w ∈ T} L_wˣ` from the `T`-idèles onto the
idèles supported on `T` (Milne, *Class Field Theory*, III.2),

  `0 ⟶ ∏_{w ∉ T} U_w ⟶ 𝕀_{L,T} ⟶ ∏_{w ∈ T} L_wˣ ⟶ 0`.

The long exact sequence in Tate cohomology attached to this sequence contains

  `Ĥ⁰(G, ∏_{w ∈ T} L_wˣ) ⟶ Ĥ¹(G, ∏_{w ∉ T} U_w) ⟶ Ĥ¹(G, 𝕀_{L,T})`,

exact in the middle.  Both outer groups are finite in the situation at hand — the left one because
the idèles supported on `T` decompose as the *finite* product `∏_{v ∈ S} (∏_{w | v} L_wˣ)` of
fibres whose `Ĥ⁰` is finite, the right one by hypothesis — and hence so is `Ĥ¹(G, ∏_{w ∉ T} U_w)`.
This is the finiteness statement used when Herbrand quotients of global objects are compared
(Milne III.2.5), and it is the content of this file.

The two group-theoretic inputs are kept separate, so that they can be reused:

* `finite_of_range_eq_ker` — the middle term of an exact sequence `P → M → Q` of modules is finite
  as soon as `P` and `Q` are;
* `finite_tateCohomology_one_of_shortExact` — the abstract two-out-of-three finiteness for `Ĥ¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-! ## A finiteness criterion from an exact sequence -/

/-- **The middle term of an exact sequence of modules is finite when both ends are.**  If
`f : P ⟶ M` and `g : M ⟶ Q` satisfy `range f = ker g`, then `M` sits in the extension of the
finite group `range g = image of g ⊆ Q` by the finite group `range f = ker g`. -/
lemma finite_of_range_eq_ker {R : Type*} [Ring R] {P M Q : ModuleCat R}
    (f : P ⟶ M) (g : M ⟶ Q) (h : f.hom.range = g.hom.ker) [Finite ↥P] [Finite ↥Q] :
    Finite ↥M := by
  -- the kernel of `g` is the image of `f`, hence finite
  have hkerfin : Finite ↥(g.hom.ker) := by
    rw [← h]
    refine Finite.of_surjective
      (fun x : ↥P => (⟨f.hom x, ⟨x, rfl⟩⟩ : f.hom.range)) ?_
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  -- the quotient by the kernel is the image of `g`, a subquotient of the finite `Q`
  have hrangeFin : Finite ↥(g.hom.range) := inferInstance
  have hquotfin : Finite (↥M ⧸ g.hom.ker) :=
    Finite.of_equiv ↥(g.hom.range) (LinearMap.quotKerEquivRange g.hom).symm.toEquiv
  -- `Nat.card M = Nat.card (ker g) * Nat.card (M ⧸ ker g)` is then non-zero
  have hcard := Submodule.card_eq_card_quotient_mul_card (R := R) (M := ↥M) g.hom.ker
  have h1 : Nat.card ↥(g.hom.ker) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨0, (g.hom.ker).zero_mem⟩, hkerfin⟩
  have h2 : Nat.card (↥M ⧸ g.hom.ker) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨0⟩, hquotfin⟩
  exact (Nat.card_ne_zero.mp (by rw [hcard]; exact Nat.mul_ne_zero h1 h2)).2

/-! ## The two-out-of-three finiteness for `Ĥ¹` -/

/-- **Finiteness of `Ĥ¹` along a short exact sequence.**  For a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of `ℤ[G]`-modules with `G` a finite group, if `Ĥ⁰(G, X₃)` and
`Ĥ¹(G, X₂)` are finite, then so is `Ĥ¹(G, X₁)`: the long exact sequence in Tate cohomology
contains the exact segment `Ĥ⁰(G, X₃) → Ĥ¹(G, X₁) → Ĥ¹(G, X₂)`. -/
theorem finite_tateCohomology_one_of_shortExact {G : Type} [Group G] [Fintype G]
    (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (h₃ : Finite ↥(tateCohomology S.X₃ 0)) (h₂ : Finite ↥(tateCohomology S.X₂ 1)) :
    Finite ↥(tateCohomology S.X₁ 1) := by
  -- the long exact sequence in Tate cohomology, in degrees `0` and `1`
  have hex := TateCohomology.exact₁ (R := ℤ) (G := G) hS 0
  have hre : LinearMap.range (TateCohomology.δ hS 0).hom =
      LinearMap.ker ((tateCohomologyFunctor (R := ℤ) (G := G) 1).map S.f).hom :=
    hex.moduleCat_range_eq_ker
  exact finite_of_range_eq_ker _ _ hre

/-! ## The target -/

/-- **`Ĥ¹` of the unit idèles outside `T` is finite.**  With `S` a finite set of places of `K`
containing all the archimedean ones and `T` its preimage in `L`, the idèles which are `1` on `T`
and local units outside `T` have finite first Tate cohomology, provided the first Tate cohomology
of the `T`-idèles is finite and the zeroth Tate cohomology of each fibre `∏_{w | v} L_wˣ`
(`v ∈ S`) is finite. -/
theorem finite_tateCohomology_one_unitIdelesOutsideRep {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S)
    (hfinf : ∀ v : NK.GlobalCFT.Place K,
      NK.GlobalCFTdeep.FiniteTate (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v))
    (hfinT : ∀ (S' : Finset (NK.GlobalCFT.Place K)) (T' : Set (NK.GlobalCFT.Place L))
      (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃u : NK.GlobalCFT.Place L⦄, u ∈ T' → σ • u ∈ T')
      (hTS' : ∀ u : NK.GlobalCFT.Place L, u ∈ T' ↔ ∃ v ∈ S', NK.GlobalCFT.Place.LiesOver u v),
        NK.GlobalCFTdeep.FiniteTate (NK.GlobalCFTdeep.tIdelesRep (K := K) (L := L) T' hT')) :
    Finite ↥(tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) 1) := by
  -- `Ĥ⁰` of each fibre is finite, whence so is `Ĥ⁰` of the finite product of the fibres
  haveI hfib : ∀ v : S, Finite ↥(tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : NK.GlobalCFT.Place K)) 0) :=
    fun v => (hfinf (v : NK.GlobalCFT.Place K)).zero
  -- the idèles supported on `T` are the product of the fibres of the places of `S`
  have hC : Finite ↥(tateCohomology (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) 0) := by
    have hcard := natCard_tateCohomology_supportedIdelesRep (K := K) (L := L) S T hT hTS 0
    have hPi : Finite ((v : S) → ↥(tateCohomology
        (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : NK.GlobalCFT.Place K)) 0)) :=
      inferInstance
    have hne : Nat.card ((v : S) → ↥(tateCohomology
        (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : NK.GlobalCFT.Place K)) 0)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨fun _ => 0⟩, hPi⟩
    exact (Nat.card_ne_zero.mp (by rw [hcard]; exact hne)).2
  -- the long exact sequence of `0 → ∏_{w ∉ T} U_w → 𝕀_{L,T} → ∏_{w ∈ T} L_wˣ → 0`
  exact finite_tateCohomology_one_of_shortExact
    (NatCardSES.ses (L := L) T hT) (NatCardSES.ses_shortExact (L := L) T hT) hC
    (hfinT S T hT hTS).one

end NK.GlobalCFTdeep.Herbrand
