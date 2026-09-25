/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Pro-`p` topological groups

This file defines pro-`p` topological groups and proves the first closure properties of the
notion.  It is the base of the `NK.ProfiniteP` chapter, which supplies the
Frattini/rank calculus used in the local Galois theory part of Neukirch–Uchida
(CoNF XII (12.1.9)–(12.1.10)).

## Main definitions

* `IsProP p G` : every open normal subgroup of the topological group `G` has index a power of `p`.

## Main results

* `IsProP.isPGroup_quotient` : a quotient by an open normal subgroup is a `p`-group.
* `IsProP.isPGroup_of_continuous_surjective` : so is any finite continuous quotient.
* `isProP_iff_isPGroup` : for a finite discrete group, pro-`p` means `p`-group.
* `IsProP.of_continuous_surjective` : quotients of pro-`p` groups are pro-`p`.
* `normal_isPGroup_of_isProP` : a normal closed subgroup with a finite continuous quotient
  structure; see `Frattini.lean` for the Frattini calculus built on top.
-/

open Subgroup
open scoped IsMulCommutative

universe u v w

namespace OpenNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- The preimage of an open normal subgroup under a continuous homomorphism is open normal. -/
def preimage (U : OpenNormalSubgroup H) (f : G →* H) (hf : Continuous f) :
    OpenNormalSubgroup G :=
  ⟨U.toOpenSubgroup.comap f hf,
    Subgroup.Normal.comap (inferInstance : (U : Subgroup H).Normal) f⟩

@[simp]
theorem coe_preimage (U : OpenNormalSubgroup H) (f : G →* H) (hf : Continuous f) :
    ((U.preimage f hf : OpenNormalSubgroup G) : Subgroup G) = (U : Subgroup H).comap f := rfl

end OpenNormalSubgroup

namespace NK.ProfiniteP

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- A topological group `G` is **pro-`p`** if every open normal subgroup of `G` has index a
power of `p`.  For a profinite group this is equivalent to asking that every continuous finite
quotient is a `p`-group (see `IsProP.isPGroup_of_continuous_surjective` and
`isProP_iff_forall_isPGroup_quotient`). -/
def IsProP (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, ∃ n : ℕ, (U : Subgroup G).index = p ^ n

theorem isProP_def {G : Type u} [Group G] [TopologicalSpace G] (p : ℕ) :
    IsProP p G ↔ ∀ U : OpenNormalSubgroup G, ∃ n : ℕ, (U : Subgroup G).index = p ^ n :=
  Iff.rfl

namespace IsProP

theorem index_eq_pow (h : IsProP p G) (U : OpenNormalSubgroup G) :
    ∃ n : ℕ, (U : Subgroup G).index = p ^ n :=
  h U

/-- The trivial group is pro-`p` for every `p`. -/
theorem subsingleton [Subsingleton G] : IsProP p G := by
  intro U
  have hU : (U : Subgroup G) = ⊤ :=
    (Subgroup.eq_top_iff' (U : Subgroup G)).mpr fun x => by
      rw [Subsingleton.elim x 1]; exact U.one_mem
  exact ⟨0, by rw [hU, Subgroup.index_top, pow_zero]⟩

/-- The quotient of a pro-`p` group by an open normal subgroup is a `p`-group. -/
theorem isPGroup_quotient [Fact p.Prime] (h : IsProP p G) (U : OpenNormalSubgroup G) :
    IsPGroup p (G ⧸ (U : Subgroup G)) := by
  obtain ⟨n, hn⟩ := h U
  exact IsPGroup.of_card (by rw [← Subgroup.index_eq_card, hn])

/-- Every finite continuous quotient of a pro-`p` group is a `p`-group. -/
theorem isPGroup_of_continuous_surjective [Fact p.Prime] (h : IsProP p G) {f : G →* H}
    (hf : Continuous f) (hsurj : Function.Surjective f) [Finite H] [DiscreteTopology H] :
    IsPGroup p H := by
  have hopen : IsOpen ((f.ker : Subgroup G) : Set G) := by
    have hk : ((f.ker : Subgroup G) : Set G) = f ⁻¹' ({1} : Set H) := by
      ext x; simp [MonoidHom.mem_ker]
    rw [hk]
    exact (isOpen_discrete ({1} : Set H)).preimage hf
  obtain ⟨n, hn⟩ := h ⟨⟨f.ker, hopen⟩, inferInstance⟩
  refine IsPGroup.of_card (n := n) ?_
  have h1 : Nat.card H = (f.ker : Subgroup G).index := by
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hsurj, Subgroup.card_top]
  rw [h1, hn]

/-- A continuous quotient of a pro-`p` group is pro-`p`. -/
theorem of_continuous_surjective (h : IsProP p G) {f : G →* H} (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsProP p H := by
  intro U
  obtain ⟨n, hn⟩ := h (U.preimage f hf)
  refine ⟨n, ?_⟩
  rw [← hn, OpenNormalSubgroup.coe_preimage, Subgroup.index_comap_of_surjective _ hsurj]

/-- The property of being pro-`p` is invariant under continuous isomorphisms. -/
theorem congr {G' : Type v} [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (h : IsProP p G) :
    IsProP p G' :=
  h.of_continuous_surjective (f := (e : G →* G')) e.continuous fun x =>
    ⟨e.symm x, e.apply_symm_apply x⟩

end IsProP

/-- A finite discrete topological group is pro-`p` if and only if it is a `p`-group. -/
theorem isProP_iff_isPGroup [Finite G] [DiscreteTopology G] [Fact p.Prime] :
    IsProP p G ↔ IsPGroup p G := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hopen : IsOpen ((⊥ : Subgroup G) : Set G) := isOpen_discrete _
    obtain ⟨n, hn⟩ := h ⟨⟨⊥, hopen⟩, inferInstance⟩
    exact IsPGroup.of_card (n := n) (by rw [Subgroup.index_bot] at hn; exact hn)
  · intro U
    obtain ⟨n, hn⟩ :=
      (IsPGroup.iff_card (p := p) (G := G ⧸ (U : Subgroup G))).mp (h.to_quotient _)
    exact ⟨n, by rw [Subgroup.index_eq_card]; exact hn⟩

end NK.ProfiniteP
