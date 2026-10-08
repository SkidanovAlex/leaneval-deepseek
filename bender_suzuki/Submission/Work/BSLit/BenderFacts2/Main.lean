import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.BenderFacts2.isZassenhaus_map_mulEquiv
import Submission.Work.BSLit.BenderFacts2.pSL2_benderModelFacts2
import Submission.Work.BSLit.BenderFacts2.sz_benderModelFacts2
import Submission.Work.BSLit.BenderFacts2.psu3_benderModelFacts2
import Submission.Work.Models.Transport.stronglyEmbedded_map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderModelFacts2Prop`

The lead's clause `Submission.Blueprint.BenderModelFacts2Prop` (Peterfalvi I p. 184, facts 1°, 2°),
assembled from the three model instances

* `Work.BSLit.BenderFacts2.pSL2_benderModelFacts2` (`PSL(2, 2ⁿ)`, `n ≥ 2`),
* `Work.BSLit.BenderFacts2.sz_benderModelFacts2` (`Sz(2^(2n+1))`, `n ≥ 1`),
* `Work.BSLit.BenderFacts2.psu3_benderModelFacts2` (`PSU(3, 2ⁿ)`, `n ≥ 2`),

by transporting along the isomorphism `e : Y ≃* <model>` given by `IsSimpleBenderGroup Y`
(which is *defined* as "`Y` is isomorphic to one of the three models").

Main results:

* `Work.BSLit.benderModelFacts2_of_iso` — transport of the two clauses along `e`;
* `Work.BSLit.BenderModelFacts2Prop : Submission.Blueprint.BenderModelFacts2Prop`.
-/

set_option autoImplicit false

namespace Work.BSLit

open Classical

variable {Y Y' : Type*} [Group Y] [Finite Y] [Group Y'] [Finite Y']

/-- The centraliser of a singleton commutes with `Subgroup.map` along a group isomorphism. -/
theorem centralizer_singleton_map_mulEquiv (e : Y ≃* Y') (u : Y) :
    (Subgroup.centralizer ({u} : Set Y)).map e.toMonoidHom
      = Subgroup.centralizer ({e u} : Set Y') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] at hx ⊢
    simpa [map_mul] using congrArg e hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq] at hy ⊢
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

/-- The involutions of `H` and of its image under a group isomorphism have the same number. -/
theorem involutions_map_ncard (e : Y ≃* Y') (H : Subgroup Y) :
    (Submission.Blueprint.involutions (H : Set Y)).ncard
      = (Submission.Blueprint.involutions (H.map e.toMonoidHom : Set Y')).ncard := by
  have hset : Submission.Blueprint.involutions (H.map e.toMonoidHom : Set Y')
      = e '' Submission.Blueprint.involutions (H : Set Y) := by
    ext y
    constructor
    · rintro ⟨hy, hy2⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨x, ⟨hx, by rw [← MulEquiv.orderOf_eq e x]; exact hy2⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _ hx, by rw [MulEquiv.orderOf_eq]; exact hx2⟩
  rw [hset, Set.ncard_image_of_injective _ e.injective]

/-- The two clauses of `BenderModelFacts2Prop` transport along a group isomorphism. -/
theorem benderModelFacts2_of_iso (e : Y ≃* Y') (h : BenderModelFacts2For Y') :
    BenderModelFacts2For Y := by
  intro H hH
  have hH' : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H.map e.toMonoidHom) :=
    Work.Models.Transport.stronglyEmbedded_map e hH
  obtain ⟨h1, h2⟩ := h (H.map e.toMonoidHom) hH'
  constructor
  · intro x hx hk
    obtain ⟨k, hk⟩ := hk
    have hx' : e x ∈ H.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    have hk' : ∃ j : ℕ, orderOf (e x) = 2 ^ j := ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩
    have h4 := h1 (e x) hx' hk'
    have : e (x ^ 4) = 1 := by rw [map_pow]; exact h4
    exact e.injective (by rw [this, map_one])
  · intro hZ u hu t ht2 htn
    have hZ' : Submission.Blueprint.IsZassenhaus (H.map e.toMonoidHom) :=
      (Work.BSLit.BenderFacts2.isZassenhaus_map_mulEquiv H e).mp hZ
    have hu' : e u ∈ Submission.Blueprint.involutions (H.map e.toMonoidHom : Set Y') :=
      ⟨Subgroup.mem_map_of_mem _ hu.1, by rw [MulEquiv.orderOf_eq]; exact hu.2⟩
    have ht2' : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
    have htn' : e t ∉ H.map e.toMonoidHom := by
      rintro ⟨z, hz, hze⟩
      exact htn (e.injective hze ▸ hz)
    obtain ⟨hcyc, hinv, hcard⟩ := h2 hZ' (e u) hu' (e t) ht2' htn'
    have hce : (Subgroup.centralizer ({u * t} : Set Y)).map e.toMonoidHom
        = Subgroup.centralizer ({e u * e t} : Set Y') := by
      have h1 := centralizer_singleton_map_mulEquiv e (u * t)
      rw [map_mul] at h1
      exact h1
    have hiso : ↥(Subgroup.centralizer ({u * t} : Set Y))
        ≃* ↥(Subgroup.centralizer ({e u * e t} : Set Y')) :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hce)
    refine ⟨(MulEquiv.isCyclic hiso).mpr hcyc, ?_, ?_⟩
    · intro y hy
      have hy' : e y ∈ Subgroup.centralizer ({e u * e t} : Set Y') := by
        have hmem : e y ∈ (Subgroup.centralizer ({u * t} : Set Y)).map e.toMonoidHom :=
          Subgroup.mem_map_of_mem _ hy
        rwa [hce] at hmem
      have h := hinv (e y) hy'
      have h2' : e (u * y * u⁻¹) = e (y⁻¹) := by
        rw [map_mul, map_mul, map_inv, map_inv, h]
      exact e.injective (by rw [h2', map_inv])
    · intro h127
      have h127' : 127 ≤ (Submission.Blueprint.involutions (H.map e.toMonoidHom : Set Y')).ncard := by
        rw [← involutions_map_ncard e H]; exact h127
      have h6 := hcard h127'
      have hcard_eq : Nat.card ↥(Subgroup.centralizer ({u * t} : Set Y))
          = Nat.card ↥(Subgroup.centralizer ({e u * e t} : Set Y')) :=
        Nat.card_congr hiso.toEquiv
      rwa [hcard_eq]

/-- **`Submission.Blueprint.BenderModelFacts2Prop`** (Peterfalvi I p. 184, facts 1° and 2°),
assembled from the three model instances. -/
theorem BenderModelFacts2Prop : Submission.Blueprint.BenderModelFacts2Prop := by
  intro Y _ _ hY
  cases hY with
  | isPSL2 n hn e =>
      exact benderModelFacts2_of_iso e fun H hH => Work.BSLit.BenderFacts2.pSL2_benderModelFacts2 n hn H hH
  | isSuzuki n hn e =>
      exact benderModelFacts2_of_iso e fun H hH => Work.BSLit.BenderFacts2.sz_benderModelFacts2 n hn H hH
  | isPSU3 n hn e =>
      exact benderModelFacts2_of_iso e fun H hH => Work.BSLit.BenderFacts2.psu3_benderModelFacts2 n hn H hH

end Work.BSLit
