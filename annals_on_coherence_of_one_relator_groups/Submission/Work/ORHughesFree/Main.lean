/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The JZLA20 engine: main statements

This file records, as `Prop`-valued definitions and as explicit hypothesis interfaces, the main
statements of the JZLA20 algebraic engine (A. Jaikin-Zapirain and D. López-Álvarez,
arXiv:1810.12135) that the route design assigns to node **N6**:

* `JZLA20Thm61` : [JZLA20, Theorem 6.1] — a ∗-regular Hughes-free rank function on `K[G]` with an
  epic positive definite ∗-regular envelope has a division ring as envelope;
* `JZLA20Cor63` : [JZLA20, Corollary 6.3] — the division closure of `K[G]` in `R_{K[G]}` is a
  Hughes-free epic division `K[G]`-ring;
* `JZLA20Output` : the output of the engine, as a hypothesis interface for downstream nodes;
* `hughesFree_exists` : the deliverable statement of N6.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.HughesFree
import Submission.Work.ORHughesFree.JZLA20

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- The inclusion of `K[G]` into the division closure of `φ(K[G])` in `U`. -/
noncomputable def divisionClosureIncl {K : Type u} [Field K] {G : Type u} [Group G]
    {U : Type u} [Ring U] (φ : MonoidAlgebra K G →+* U) :
    MonoidAlgebra K G →+* ↥(divisionClosure (Set.range φ)) :=
  φ.codRestrict (divisionClosure (Set.range φ))
    (fun x => subset_divisionClosure (Set.range φ) ⟨x, rfl⟩)

/-- **[JZLA20, Theorem 6.1]**: let `G` be a locally indicable group, `K` a subfield of `ℂ`, and
`rk` a ∗-regular Hughes-free Sylvester rank function on `K[G]` with epic positive definite
∗-regular envelope `(U, φ)`.  Then `U` is a division ring.

`LocallyIndicable G` is a **necessary** hypothesis: the proof of Theorem 6.1 replaces a finitely
generated subquotient `H` by a decomposition `H = N ⋊ ⟨t⟩` with `H/N ≅ ℤ`, which local
indicability supplies and which cannot be recovered from the rank-function hypotheses (a finite
group such as `ℤ/2` has no f.g. subgroup with a `ℤ`-quotient at all, so that `IsHughesFreeRank` is
vacuous there, while `ℚ[ℤ/2] ≅ ℚ × ℚ` carries rank functions with epic positive definite
∗-regular envelopes and divisors of zero). -/
def JZLA20Thm61 {K : Type u} [Field K] {G : Type u} [Group G] [LocallyIndicable G]
    (rk : SylvesterRank (MonoidAlgebra K G)) : Prop :=
  IsHughesFreeRank rk → IsStarRegularRank rk →
    ∀ (U : Type u) (_ : Ring U) (_ : StarRing U) (_ : IsStarRegular U)
      (_ : IsPositiveDefiniteStarRegular U) (φ : MonoidAlgebra K G →+* U)
      (rkU : SylvesterRank U),
      IsEpic φ → rkU.IsFaithful →
      (∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)),
        rk.rk n m A = rkU.rk n m (A.map φ)) →
      IsDivisionRing U

/-- **[JZLA20, Corollary 6.3]**: for a locally indicable group `G` and a field `K` of characteristic
zero, the division closure of `K[G]` in the ∗-regular ring `R_{K[G]}` is a Hughes-free division ring
and an epic division `K[G]`-ring. -/
def JZLA20Cor63 (K : Type u) [Field K] (G : Type u) [Group G]
    (U : Type u) [Ring U] [StarRing U] [IsStarRegular U]
    (_hpos : IsPositiveDefiniteStarRegular U) (φ : MonoidAlgebra K G →+* U) : Prop :=
  ∃ (hD : IsDivisionRing ↥(divisionClosure (Set.range φ))),
    IsHughesFreeDivisionRing K G ↥(divisionClosure (Set.range φ)) hD (divisionClosureIncl φ)

/-- **The output of the JZLA20 algebraic engine** (nodes N6/N7 of the route design), packaged as an
explicit hypothesis interface for the downstream nodes: for a locally indicable group `G` and a
field `K ⊆ ℂ`, the division closure of `K[G]` inside a positive definite ∗-regular ring `U`
containing `K[G]` is a division ring, and it carries a Hughes-free epic division `K[G]`-ring
structure. -/
structure JZLA20Output (K : Type u) [Field K] (G : Type u) [Group G]
    (U : Type u) [Ring U] [StarRing U] [IsStarRegular U]
    (_hpos : IsPositiveDefiniteStarRegular U) (φ : MonoidAlgebra K G →+* U) : Prop where
  /-- the division closure of `K[G]` in `U` is a division ring -/
  isDivisionRing : IsDivisionRing ↥(divisionClosure (Set.range φ))
  /-- the division closure is a Hughes-free epic division `K[G]`-ring -/
  hughesFree : IsHughesFreeDivisionRing K G ↥(divisionClosure (Set.range φ)) isDivisionRing
    (divisionClosureIncl φ)

/-- **The deliverable statement of node N6** (`hughesFree_exists` in the route design): for a
locally indicable group `G` and a field `K` of characteristic zero, given the N5 interface — a
positive definite ∗-regular ring `U` containing `K[G]` with an epic ∗-homomorphism and a faithful
Hughes-free rank function — the division closure `D_{K[G],U}` is a division ring and is
Hughes-free. -/
def hughesFree_exists (K : Type u) [Field K] (G : Type u) [Group G]
    (U : Type u) [Ring U] [StarRing U] [IsStarRegular U]
    (hpos : IsPositiveDefiniteStarRegular U) (φ : MonoidAlgebra K G →+* U) : Prop :=
  JZLA20Cor63 K G U hpos φ

/-- The engine's output gives the N6 deliverable. -/
theorem hughesFree_exists_of_output (K : Type u) [Field K] (G : Type u) [Group G]
    (U : Type u) [Ring U] [StarRing U] [IsStarRegular U]
    (hpos : IsPositiveDefiniteStarRegular U) (φ : MonoidAlgebra K G →+* U)
    (h : JZLA20Output K G U hpos φ) : hughesFree_exists K G U hpos φ :=
  ⟨h.isDivisionRing, h.hughesFree⟩

/-- The N6 deliverable `hughesFree_exists`, phrased with the **N5 interface**
`StarRegularEnvelope`: the analytic input `(U, φ, rk)` for the locally indicable group `G` and the
field `K`. -/
def hughesFree_exists_of_starRegularEnvelope (K : Type u) [Field K] (G : Type u) [Group G]
    (U : Type u) [Ring U] [StarRing U] [IsStarRegular U] (hpos : IsPositiveDefiniteStarRegular U)
    (E : StarRegularEnvelope K G U hpos) : Prop :=
  hughesFree_exists K G U hpos E.φ

/-- The engine's output, together with the N5 interface, gives the N6 deliverable. -/
theorem hughesFree_exists_of_envelope_output {K : Type u} [Field K] {G : Type u} [Group G]
    {U : Type u} [Ring U] [StarRing U] [IsStarRegular U] {hpos : IsPositiveDefiniteStarRegular U}
    (E : StarRegularEnvelope K G U hpos) (h : JZLA20Output K G U hpos E.φ) :
    hughesFree_exists_of_starRegularEnvelope K G U hpos E :=
  ⟨h.isDivisionRing, h.hughesFree⟩

/-- The N6 deliverable `hughesFree_exists` in the form pinned by the route design: for a **locally
indicable** group `G` and a field `K ⊆ ℂ`, given the N5 data, the division closure of `K[G]` is a
Hughes-free division ring. -/
def hughesFree_exists_locallyIndicable (K : Type u) [Field K] (G : Type u) [Group G]
    [LocallyIndicable G] (U : Type u) [Ring U] [StarRing U] [IsStarRegular U]
    (hpos : IsPositiveDefiniteStarRegular U) (φ : MonoidAlgebra K G →+* U) : Prop :=
  hughesFree_exists K G U hpos φ

/-- The engine's output gives the N6 deliverable for a locally indicable group. -/
theorem hughesFree_exists_locallyIndicable_of_output {K : Type u} [Field K] {G : Type u}
    [Group G] [LocallyIndicable G] {U : Type u} [Ring U] [StarRing U] [IsStarRegular U]
    {hpos : IsPositiveDefiniteStarRegular U} {φ : MonoidAlgebra K G →+* U}
    (h : JZLA20Output K G U hpos φ) : hughesFree_exists_locallyIndicable K G U hpos φ :=
  ⟨h.isDivisionRing, h.hughesFree⟩

/-- The N6 deliverable `hughesFree_exists` in the **exact form of the route design**: for a
countable locally indicable group `G` and a field `K` (thought of as a subfield of `ℂ`, with the
∗-structure of `K[G]` supplied by the N5 data), the division closure of `K[G]` in `U` is a division
ring and a Hughes-free epic division `K[G]`-ring. -/
def hughesFree_exists_countable (K : Type u) [Field K] (G : Type u) [Group G] [LocallyIndicable G]
    [Countable G] (U : Type u) [Ring U] [StarRing U] [IsStarRegular U]
    (hpos : IsPositiveDefiniteStarRegular U) (φ : MonoidAlgebra K G →+* U) : Prop :=
  hughesFree_exists K G U hpos φ

/-- The engine's output gives the N6 deliverable in the exact form of the route design. -/
theorem hughesFree_exists_countable_of_output {K : Type u} [Field K] {G : Type u} [Group G]
    [LocallyIndicable G] [Countable G] {U : Type u} [Ring U] [StarRing U] [IsStarRegular U]
    {hpos : IsPositiveDefiniteStarRegular U} {φ : MonoidAlgebra K G →+* U}
    (h : JZLA20Output K G U hpos φ) : hughesFree_exists_countable K G U hpos φ :=
  ⟨h.isDivisionRing, h.hughesFree⟩

end Work.ORHughesFree
