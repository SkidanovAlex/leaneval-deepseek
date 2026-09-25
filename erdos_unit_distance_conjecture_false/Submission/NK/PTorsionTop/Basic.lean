/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The corrected `p`-torsion predicate: the *topological* abelianisation

The area `NK.LocalAnabelian` uses

  `HasPTorsionAbelianization p G := ∃ x : Abelianization G, x ≠ 1 ∧ x ^ p = 1`

(`Submission/Work/LocalAnabelian/Basic.lean`), where Mathlib's `Abelianization G` is the
quotient of `G` by the **abstract** commutator subgroup `commutator G = ⁅⊤, ⊤⁆` — the subgroup
*generated* by commutators, with no closure taken.  For `G = Gal(K'/κ)` with the Krull topology
this is the wrong group: the group that local class field theory computes is the *topological*
abelianisation `G ⧸ (commutator G).topologicalClosure` (Mathlib: `TopologicalAbelianization G`),
which by the Galois correspondence is `Gal(κ^{ab}/κ)` and which reciprocity identifies with
`κˣ^{∧}`.

This file introduces the corrected predicate

  `NK.PTorsionTop.HasPTorsionAbelianizationTop p G :=
     ∃ x : G ⧸ (commutator G).topologicalClosure, x ≠ 1 ∧ x ^ p = 1`

together with its elementary API.

## Notes on the formalisation

* The definition needs `IsTopologicalGroup G` (not merely `TopologicalSpace G`): the closure of a
  normal subgroup is normal only in a topological group, and `G ⧸ (commutator G).topologicalClosure`
  is a group quotient.  This is the only deviation from the prompt's literal signature.

* An abstract isomorphism `e : G ≃* H` of topological groups does **not** preserve the predicate in
  general (see `README.md` §"the verdict on invariance"): the closure of the commutator subgroup
  depends on the topology and an arbitrary group isomorphism need not be continuous.  What is
  proved here is invariance under a *two-sided continuous* isomorphism (`≃ₜ*`,
  `hasPTorsionAbelianizationTop_congr_iff`).  For **commutative** groups there is no such
  subtlety: the predicate is plain `p`-torsion, invariant under any `G ≃* H`.

## Main definitions

* `NK.PTorsionTop.HasPTorsionAbelianizationTop` — the corrected predicate;
* `NK.PTorsionTop.HasPTorsion` — plain `p`-torsion, which is what the corrected predicate
  computes for a commutative group.
-/
import Mathlib
import Submission.NK.LocalAnabelian.Basic

open scoped Classical

namespace NK.PTorsionTop

universe u v

noncomputable section

/-! ## The predicate -/

/-- **The corrected `p`-torsion predicate**: the *topological* (profinite) abelianisation
`G ⧸ (commutator G).topologicalClosure` has a non-trivial element of order dividing `p`.

For `G = Gal(K'/κ)` this quotient is `Gal(κ^{ab}/κ)`, whose `p`-torsion is `μ_p(κ)` by local
reciprocity — so the predicate detects `ζ_p ∈ κ`, which is what the `p_torsion_iff` fields of the
`NK.LocalAnabelian`/`NK.LocalInputs` bundles intended. -/
def HasPTorsionAbelianizationTop (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  ∃ x : G ⧸ (commutator G).topologicalClosure, x ≠ 1 ∧ x ^ p = 1

/-- **`p`-torsion, in the group itself**: `G` has a non-trivial element of order dividing `p`.
For a commutative group this is what `HasPTorsionAbelianizationTop` computes
(`hasPTorsionAbelianizationTop_iff_hasPTorsion_of_commutative`). -/
def HasPTorsion (p : ℕ) (G : Type u) [Group G] : Prop :=
  ∃ x : G, x ≠ 1 ∧ x ^ p = 1

/-! ## `HasPTorsion`: basic API -/

/-- `HasPTorsion` is invariant under group isomorphisms (no topology involved). -/
theorem hasPTorsion_congr {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) {p : ℕ}
    (h : HasPTorsion p G) : HasPTorsion p H := by
  obtain ⟨x, hx1, hxp⟩ := h
  exact ⟨e x, fun hc => hx1 (e.injective (by rw [hc, map_one])), by rw [← map_pow, hxp, map_one]⟩

/-- `HasPTorsion` is invariant under group isomorphisms, as an `iff`. -/
theorem hasPTorsion_congr_iff {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H)
    (p : ℕ) :
    HasPTorsion p G ↔ HasPTorsion p H :=
  ⟨fun h => hasPTorsion_congr e h, fun h => hasPTorsion_congr e.symm h⟩

/-- `HasPTorsion p` is monotone for injective homomorphisms. -/
theorem hasPTorsion_of_injective {G H : Type u} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {p : ℕ} (h : HasPTorsion p G) : HasPTorsion p H := by
  obtain ⟨x, hx1, hxp⟩ := h
  exact ⟨f x, fun hc => hx1 (hf (by rw [hc, map_one])), by rw [← map_pow, hxp, map_one]⟩

/-! ## The comparison with the abstract predicate -/

/-- The old (abstract) predicate is `p`-torsion in the quotient by the abstract commutator
subgroup; unwinding the definition. -/
theorem hasPTorsionAbelianization_iff (p : ℕ) (G : Type u) [Group G] :
    NK.LocalAnabelian.HasPTorsionAbelianization p G ↔
      ∃ x : G ⧸ commutator G, x ≠ 1 ∧ x ^ p = 1 :=
  Iff.rfl

/-- **For a commutative group the abstract commutator subgroup is trivial.** -/
theorem commutator_eq_bot_of_commutative (G : Type u) [CommGroup G] : commutator G = ⊥ := by
  rw [show commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ from rfl,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact fun x _ y _ => mul_comm y x

/-- **The topological closure of the trivial subgroup is trivial.** -/
theorem bot_topologicalClosure (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T1Space G] : (⊥ : Subgroup G).topologicalClosure = ⊥ := by
  refine le_antisymm (Subgroup.topologicalClosure_minimal ⊥ le_rfl ?_) bot_le
  rw [Subgroup.coe_bot]
  exact isClosed_singleton

/-- **For a commutative group, the abstract predicate is honestly `p`-torsion in the group.** -/
theorem hasPTorsionAbelianization_iff_hasPTorsion_of_commutative (p : ℕ) (G : Type u)
    [CommGroup G] :
    NK.LocalAnabelian.HasPTorsionAbelianization p G ↔ HasPTorsion p G := by
  change HasPTorsion p (G ⧸ commutator G) ↔ HasPTorsion p G
  exact hasPTorsion_congr_iff
    ((QuotientGroup.quotientMulEquivOfEq (commutator_eq_bot_of_commutative G)).trans
      (QuotientGroup.quotientBot (G := G))) p

/-- **For a commutative topological group the corrected predicate is `p`-torsion in the group**:
the commutator subgroup is trivial, so its topological closure is trivial as well. -/
theorem hasPTorsionAbelianizationTop_iff_hasPTorsion_of_commutative (p : ℕ) (G : Type u)
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G] :
    HasPTorsionAbelianizationTop p G ↔ HasPTorsion p G := by
  change HasPTorsion p (G ⧸ (commutator G).topologicalClosure) ↔ HasPTorsion p G
  have h : (commutator G).topologicalClosure = (⊥ : Subgroup G) := by
    rw [commutator_eq_bot_of_commutative G, bot_topologicalClosure]
  exact hasPTorsion_congr_iff
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientBot (G := G))) p

/-- **The old and the new predicate agree for commutative groups** (both are `p`-torsion). -/
theorem hasPTorsionAbelianization_iff_hasPTorsionAbelianizationTop_of_commutative (p : ℕ)
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G] :
    NK.LocalAnabelian.HasPTorsionAbelianization p G ↔ HasPTorsionAbelianizationTop p G :=
  (hasPTorsionAbelianization_iff_hasPTorsion_of_commutative p G).trans
    (hasPTorsionAbelianizationTop_iff_hasPTorsion_of_commutative p G).symm

/-- **For a group whose multiplication is commutative (as a bare fact) the corrected predicate is
`p`-torsion in the group.**  This is the form needed for the completions and Galois groups of the
main theorem, whose typeclass structure does not carry a `CommGroup` instance. -/
theorem hasPTorsionAbelianizationTop_iff_hasPTorsion_of_isMulCommutative (p : ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]
    (hcomm : ∀ x y : G, x * y = y * x) :
    HasPTorsionAbelianizationTop p G ↔ HasPTorsion p G := by
  change HasPTorsion p (G ⧸ (commutator G).topologicalClosure) ↔ HasPTorsion p G
  have hbot : commutator G = (⊥ : Subgroup G) := by
    rw [show commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ from rfl,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun x _ y _ => hcomm y x
  have h : (commutator G).topologicalClosure = (⊥ : Subgroup G) := by
    rw [hbot, bot_topologicalClosure]
  exact hasPTorsion_congr_iff
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientBot (G := G))) p

/-- A group isomorphism which is a homeomorphism is a *two-sided continuous* isomorphism. -/
noncomputable def continuousMulEquivOfIsHomeomorph {G : Type u} {H : Type v} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (e : G ≃* H) (he : IsHomeomorph e) : G ≃ₜ* H :=
  ContinuousMulEquiv.mk' (he.homeomorph (e : G → H)) (fun x y => map_mul e x y)

/-! ## Invariance of the corrected predicate under continuous isomorphisms -/

/-- A two-sided continuous isomorphism carries the closure of the commutator subgroup into the
closure of the commutator subgroup. -/
theorem map_topologicalClosure_commutator_le {A : Type u} {B : Type v} [Group A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T1Space A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [T1Space B] (f : A ≃ₜ* B) :
    ((commutator A).topologicalClosure).map (f : A →* B) ≤ (commutator B).topologicalClosure := by
  have hmap : (commutator A).map (f : A →* B) = commutator B := by
    rw [show commutator A = ⁅(⊤ : Subgroup A), ⊤⁆ from rfl,
      show commutator B = ⁅(⊤ : Subgroup B), ⊤⁆ from rfl, Subgroup.map_commutator]
    simp
  refine Subgroup.map_le_iff_le_comap.mpr (Subgroup.topologicalClosure_minimal _
    (fun x hx => ?_) ((Subgroup.isClosed_topologicalClosure _).preimage f.continuous_toFun))
  show f x ∈ (commutator B).topologicalClosure
  rw [← hmap]
  exact Subgroup.le_topologicalClosure _ (Subgroup.mem_map_of_mem _ hx)

/-- The topological closure of the commutator subgroup is carried onto the topological closure of
the commutator subgroup by a two-sided continuous isomorphism. -/
theorem map_topologicalClosure_commutator_eq {G : Type u} {H : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T1Space G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T1Space H] (e : G ≃ₜ* H) :
    ((commutator G).topologicalClosure).map (e : G →* H) = (commutator H).topologicalClosure := by
  refine le_antisymm (map_topologicalClosure_commutator_le e) ?_
  have h2 : (((commutator H).topologicalClosure).map (e.symm : H →* G)).map (e : G →* H) ≤
      ((commutator G).topologicalClosure).map (e : G →* H) :=
    Subgroup.map_mono (map_topologicalClosure_commutator_le (A := H) (B := G) e.symm)
  rw [Subgroup.map_map, show (e : G →* H).comp (e.symm : H →* G) = MonoidHom.id H from
    MonoidHom.ext fun x => e.apply_symm_apply x, Subgroup.map_id] at h2
  exact h2

/-- **Invariance of the corrected predicate under a two-sided continuous isomorphism.** -/
theorem hasPTorsionAbelianizationTop_congr_iff {G : Type u} {H : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T1Space G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T1Space H] (e : G ≃ₜ* H) (p : ℕ) :
    HasPTorsionAbelianizationTop p G ↔ HasPTorsionAbelianizationTop p H := by
  have h := hasPTorsion_congr_iff
    (QuotientGroup.congr ((commutator G).topologicalClosure) ((commutator H).topologicalClosure)
      (e : G ≃* H) (map_topologicalClosure_commutator_eq e)) p
  simpa only [HasPTorsionAbelianizationTop, HasPTorsion] using h

/-- **Invariance of the corrected predicate under a homeomorphic isomorphism.** -/
theorem hasPTorsionAbelianizationTop_congr_iff_of_isHomeomorph {G : Type u} {H : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T1Space H] (e : G ≃* H) (he : IsHomeomorph e) (p : ℕ) :
    HasPTorsionAbelianizationTop p G ↔ HasPTorsionAbelianizationTop p H :=
  hasPTorsionAbelianizationTop_congr_iff (continuousMulEquivOfIsHomeomorph e he) p

/-- **Invariance of the corrected predicate under a two-sided continuous isomorphism**
(one-directional form). -/
theorem hasPTorsionAbelianizationTop_congr {G : Type u} {H : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T1Space G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T1Space H] (e : G ≃ₜ* H) {p : ℕ} (h : HasPTorsionAbelianizationTop p G) :
    HasPTorsionAbelianizationTop p H :=
  (hasPTorsionAbelianizationTop_congr_iff e p).mp h

end

end NK.PTorsionTop
