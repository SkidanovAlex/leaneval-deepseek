/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The right-coset decomposition of `G` over a subgroup `H`

For a subgroup `H ≤ G` the group splits as the disjoint union of the *right* cosets `H q`
(`h ↦ h * q`).  Correspondingly `ℓ²(G)` is the orthogonal Hilbert sum of the subspaces
`ℓ²(H q)`, each of which is isometric to `ℓ²(H)` by the lift `e q` of
`Submission.Work.ORVonNeumann.Rep.exists_cosetLiftIso`, and the right regular
representation of `G` permutes these cosets.

This is the geometric input to the diagonal embedding `N(H) → N(G)` (an element of `N(H)`
acts on each coset copy of `ℓ²(H)`) and to the Linnell independence of `U(H)` in `U(G)`.

## Main definitions

* `Work.ORVonNeumann.Rep.CosetData G H` — a choice of representatives `Q` of the right
  cosets together with the lifts `e q : ℓ²(H) →ₗᵢ[ℂ] ℓ²(G)`;
* `Work.ORVonNeumann.Rep.CosetData.hpart`, `...qpart` — the unique decomposition
  `g = hpart g * qpart g`;
* `Work.ORVonNeumann.Rep.CosetData.E` — the lift along the coset of an arbitrary `g : G`.

## Main results

* `Work.ORVonNeumann.Rep.CosetData.hpart_mul_qpart`, `...hpart_eq_of_mul_eq`,
  `...qpart_eq_of_mul_eq` — uniqueness of the decomposition;
* `Work.ORVonNeumann.Rep.CosetData.qpart_ne_of_not_mem` — distinct right cosets give
  distinct representatives;
* `Work.ORVonNeumann.Rep.CosetData.E_delta_self` — `E g (δ_{hpart g}) = δ_g`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep
import Submission.Work.ORVonNeumann.Rep.exists_leftCosetTransversal
import Submission.Work.ORVonNeumann.Rep.exists_cosetLiftIso

set_option autoImplicit false

universe u

namespace Work.ORVonNeumann.Rep

/-- **The right-coset decomposition of `G` over `H`.**  `Q` is a set of representatives of the
right cosets `H q` (`h ↦ h * q` is a bijection `H × Q → G`) and `e q` lifts `ℓ²(H)` into
`ℓ²(G)` along the coset `H q`, sending `δ_h` to `δ_{h q}`. -/
structure CosetData (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) where
  /-- the set of representatives of the right cosets `H q` -/
  Q : Set G
  /-- every `g` is `h * q` for a unique `h ∈ H`, `q ∈ Q` -/
  exists_unique : ∀ g : G, ∃! p : ↥H × Q, (p.1 : G) * ((p.2 : Q) : G) = g
  /-- the lift of `ℓ²(H)` into `ℓ²(G)` along the coset `H q` -/
  e : Q → Work.ORVonNeumann.l2 ↥H →ₗᵢ[ℂ] Work.ORVonNeumann.l2 G
  /-- the lift sends the basis vector `δ_h` to `δ_{h q}` -/
  e_delta : ∀ (q : Q) (h : ↥H), e q (deltaG h) = deltaG ((h : G) * ((q : Q) : G))

namespace CosetData

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G]
  [MeasurableSingletonClass G] [MeasurableMul G] {H : Subgroup G} (C : CosetData G H)

variable (g : G) in
/-- The `H`-component of `g` in the coset decomposition `g = hpart g * qpart g`. -/
noncomputable def hpart : ↥H := (Classical.choose (C.exists_unique g)).1

variable (g : G) in
/-- The representative of the right coset `H g`, i.e. the `Q`-component of
`g = hpart g * qpart g`. -/
noncomputable def qpart : C.Q := (Classical.choose (C.exists_unique g)).2

/-- The defining property of the coset decomposition. -/
theorem hpart_mul_qpart (g : G) : ((C.hpart g : ↥H) : G) * ((C.qpart g : C.Q) : G) = g :=
  (Classical.choose_spec (C.exists_unique g)).1

/-- Uniqueness in the coset decomposition. -/
theorem eq_hpart_qpart (g : G) {p : ↥H × C.Q}
    (hp : (p.1 : G) * ((p.2 : C.Q) : G) = g) : p = Classical.choose (C.exists_unique g) :=
  (Classical.choose_spec (C.exists_unique g)).2 p hp

/-- The representative of the coset of `h * q` is `q`. -/
theorem qpart_eq_of_mul_eq (g : G) {h : ↥H} {q : C.Q}
    (hg : (h : G) * ((q : C.Q) : G) = g) : C.qpart g = q :=
  (congrArg Prod.snd (C.eq_hpart_qpart g (p := (h, q)) hg)).symm

/-- The `H`-component of `h * q` is `h`. -/
theorem hpart_eq_of_mul_eq (g : G) {h : ↥H} {q : C.Q}
    (hg : (h : G) * ((q : C.Q) : G) = g) : C.hpart g = h :=
  (congrArg Prod.fst (C.eq_hpart_qpart g (p := (h, q)) hg)).symm

/-- **Distinct right cosets have distinct representatives.**  If `g * g'⁻¹ ∉ H` then `g` and
`g'` lie in different right cosets of `H`, hence their representatives differ. -/
theorem qpart_ne_of_not_mem (g g' : G) (h : g * g'⁻¹ ∉ H) : C.qpart g ≠ C.qpart g' := by
  intro hq
  refine h ?_
  have h1 := C.hpart_mul_qpart g
  have h2 := C.hpart_mul_qpart g'
  have h3 : (((C.hpart g : ↥H) : G) * ((C.qpart g : C.Q) : G)) *
      ((((C.hpart g' : ↥H) : G) * ((C.qpart g' : C.Q) : G)))⁻¹
      = ((C.hpart g : ↥H) : G) * (((C.hpart g' : ↥H) : G))⁻¹ := by
    rw [hq]; group
  rw [← h1, ← h2, h3]
  exact H.mul_mem (C.hpart g).2 (H.inv_mem (C.hpart g').2)

/-- The lift of `ℓ²(H)` into `ℓ²(G)` along the right coset of `g`. -/
noncomputable def E (g : G) : Work.ORVonNeumann.l2 ↥H →ₗᵢ[ℂ] Work.ORVonNeumann.l2 G :=
  C.e (C.qpart g)

/-- `E g` sends `δ_h` to `δ_{h * qpart g}`. -/
theorem E_delta (g : G) (h : ↥H) :
    C.E g (deltaG h) = deltaG ((h : G) * ((C.qpart g : C.Q) : G)) :=
  C.e_delta (C.qpart g) h

/-- `E g` sends `δ_{hpart g}` to `δ_g`: every basis vector of `ℓ²(G)` is the image of a basis
vector of `ℓ²(H)` under the lift along its own coset. -/
theorem E_delta_self (g : G) : C.E g (deltaG (C.hpart g)) = deltaG g := by
  rw [C.E_delta, C.hpart_mul_qpart]

/-- Every basis vector of `ℓ²(G)` lies in the range of the lift along its own coset. -/
theorem deltaG_mem_range_E (g : G) : deltaG g ∈ Set.range (C.E g) :=
  ⟨deltaG (C.hpart g), C.E_delta_self g⟩

end CosetData

end Work.ORVonNeumann.Rep
