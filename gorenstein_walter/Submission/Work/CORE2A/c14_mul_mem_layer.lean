/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.card_PGL2_eq_two_mul_card_PSL2

/-!
# CORE2A, pass 14, leaf P1: two elements of `SE ∖ E` multiply into `E`

Design leaf **P1** of `Submission/Work/_design_gw/Core14.lean` §2 (Bender 1981, p. 220, the
`PGL₂(q)`-bookkeeping of Theorem 2.6 step 2).

Let `E := E(Ĥ) = layerIn B.Hhat`, `SE = ⟨S, E⟩` and `q = p ^ k` an odd prime power, and let
`D : PGLData B p k` be the `PGL₂(q)`-quotient of `SE` with kernel `Z(E)` supplied by the
recognition input `Thm26bAutProp`:

* `D.φ : ↥(SE B) →* PGL(2,q)` is surjective with kernel `Z(E)`, and
* `D.mem_layer_iff` says that an element of `SE` lies in `E` **iff** its image lies in
  `L₂(q) = Lsub p k = toPGL '' PSL(2,q) ⊂ PGL(2,q)`.

The group `Lsub p k` has index `2` in `PGL(2,q)`: `|PGL(2,q)| = 2|PSL(2,q)|` by
`card_PGL2_eq_two_mul_card_PSL2`, while `toPGL : PSL(2,q) → PGL(2,q)` is injective, so the
image has the cardinality of `PSL(2,q)`.  The product of two elements outside a subgroup of
index `2` lies in it (`Subgroup.mul_mem_iff_of_index_two`), and transporting this along `φ`
(with `D.mem_layer_iff`) gives the claim: the product of two elements of `SE` outside the layer
`E` lies in `E`.

The hypothesis `hk : 5 ≤ p ^ k` only serves to exclude `k = 0` here (so that `q` is odd and the
index really is `2`, not `1`).
-/

namespace Work.CORE2A

/-- The image `Lsub p k = toPGL '' PSL(2,q)` of the projective special linear group in the
projective general linear group has the cardinality of `PSL(2,q)`, since `toPGL` is injective
(`Matrix.ProjectiveSpecialLinearGroup.toPGL_injective`). -/
theorem card_Lsub (p k : ℕ) [Fact p.Prime] :
    Nat.card ↥(Work.GW2.Lsub p k) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
  (Nat.card_congr (Equiv.ofInjective _
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective)).symm

/-- `|PGL(2,q) : L₂(q)| = 2` for `q = p ^ k` an odd prime power (`p` odd, `k ≠ 0`).

`Nat.card (PGL(2,q)) = 2 * Nat.card (PSL(2,q))` (`card_PGL2_eq_two_mul_card_PSL2`) and
`Nat.card (Lsub p k) = Nat.card (PSL(2,q))` (`card_Lsub`), so the index, which is the quotient
of the two cardinalities (`Subgroup.index_eq_card_div`), is `2`. -/
theorem index_Lsub_eq_two {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : k ≠ 0) :
    (Work.GW2.Lsub p k).index = 2 := by
  -- `PGL(2,q)` is a quotient of the finite group `GL(2,q)`, hence finite.
  have : Finite (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  have hpos : 0 < Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    Finite.card_pos
  have hidx : (Work.GW2.Lsub p k).index =
      Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) /
        Nat.card ↥(Work.GW2.Lsub p k) :=
    Subgroup.index_eq_card_div _
  rw [hidx, card_Lsub p k, card_PGL2_eq_two_mul_card_PSL2 (p := p) (k := k) hp hk,
    Nat.mul_div_cancel 2 hpos]

/-- **P1** (`c14_mul_mem_layer`): if `a, b ∈ SE` are both outside the layer `E = E(Ĥ)`, then
`a * b ∈ E`. -/
theorem c14_mul_mem_layer {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G} {p k : ℕ}
    [Fact p.Prime] (D : Work.GW2.PGLData B p k) (hp : Odd p) (hk : 5 ≤ p ^ k) {a b : G}
    (ha : a ∈ Work.GW2.SE B) (hb : b ∈ Work.GW2.SE B) (haE : a ∉ Work.GW2.layerIn B.Hhat)
    (hbE : b ∉ Work.GW2.layerIn B.Hhat) : a * b ∈ Work.GW2.layerIn B.Hhat := by
  -- `5 ≤ p ^ k` forces `k ≠ 0`.
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  -- `L₂(q)` has index `2` in `PGL(2,q)`.
  have hidx : (Work.GW2.Lsub p k).index = 2 := index_Lsub_eq_two hp hk0
  -- The images of `a` and `b` lie outside `L₂(q)` (`D.mem_layer_iff`).
  have hxa : D.φ ⟨a, ha⟩ ∉ Work.GW2.Lsub p k :=
    fun h => haE ((D.mem_layer_iff ⟨a, ha⟩).mpr h)
  have hxb : D.φ ⟨b, hb⟩ ∉ Work.GW2.Lsub p k :=
    fun h => hbE ((D.mem_layer_iff ⟨b, hb⟩).mpr h)
  -- Hence their product lies in `L₂(q)`: the non-members of an index-two subgroup form its
  -- nontrivial coset.
  have hiff : (D.φ ⟨a, ha⟩ ∈ Work.GW2.Lsub p k) ↔ (D.φ ⟨b, hb⟩ ∈ Work.GW2.Lsub p k) :=
    ⟨fun h => absurd h hxa, fun h => absurd h hxb⟩
  have hmem : D.φ (⟨a, ha⟩ * ⟨b, hb⟩) ∈ Work.GW2.Lsub p k := by
    rw [map_mul]
    exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr hiff
  -- Transport back along `D.mem_layer_iff`.
  exact (D.mem_layer_iff (⟨a, ha⟩ * ⟨b, hb⟩)).mpr hmem

end Work.CORE2A
