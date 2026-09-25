import Mathlib
import Submission.Work.ShafarevichKoch.CoeffZ
import Submission.Work.ShafarevichKoch.Connecting2Def
import Submission.Work.ShafarevichKoch.exact_H2_C
import Submission.Work.ShafarevichKoch.exact_H3_A
import Submission.Work.ConCohomology.exact_H2_B

/-!
# `Work.ShafarevichKoch.CountZ` -- the cardinality count of the `ℤ`-power sequence

Hajir--Maire--Ramakrishna (`arXiv:2103.09508`, §1.2) read the relation count off the exact
sequence

```
0 → H²(G,ℤ)/p → H²(G,ℤ/p) → H³(G,ℤ)[p] → 0
```

attached to the coefficient sequence `0 → ℤ →^p ℤ → ℤ/p → 0`.  This module proves that sequence
for `p = 2` *in the workspace's own continuous cohomology* (`Work.ConCohomology`,
`Work.ShafarevichKoch.H3`) and draws the cardinality consequence

```
#H²(G,ℤ/2) = #(H²(G,ℤ)/2H²(G,ℤ)) · #(H³(G,ℤ)[2]) .
```

Everything is proved from three exactness statements:

* `Work.ConCohomology.exact_H2_B` (already in the workspace): the kernel of the coefficient map
  `H²(G,ℤ) → H²(G,ℤ/2)` is the image of multiplication by `2` on `H²(G,ℤ)`;
* `Work.ShafarevichKoch.exact_H2_C` and `Work.ShafarevichKoch.exact_H3_A` (this session): the
  kernel and the image of the connecting map `δ² : H²(G,ℤ/2) → H³(G,ℤ)`.

Since the coefficient map `H³(G,ℤ) → H³(G,ℤ/2)` is multiplication by `2`
(`Work.ShafarevichKoch.H3Map_zModTwoCoeffSES_f`), the sequence reads
`0 → H²(G,ℤ)/2H²(G,ℤ) → H²(G,ℤ/2) → H³(G,ℤ)[2] → 0`, and the cardinalities multiply.

## Main declarations

* `Work.ShafarevichKoch.ZSES`;
* `Work.ShafarevichKoch.natCard_H2_zmodTwo_eq`;
* `Work.ShafarevichKoch.natCard_H2_zmodTwo_le`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance instTwoActionC : DistribMulAction G (ZMod 2) := Work.RelatorRank.f2TrivialAction G
local instance instTwoDiscreteC : IsDiscreteGModule G (ZMod 2) := Work.RelatorRank.f2Discrete G

/-- The coefficient sequence `0 → ℤ --2--> ℤ --mod 2--> ℤ/2 → 0`, for the trivial `G`-action. -/
abbrev ZSES (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    CoeffSES G ℤ ℤ (ZMod 2) :=
  zModTwoCoeffSES (G := G)

/-- The subgroup `2·H²(G,ℤ) = {2x}` of `H²(G,ℤ)`, written as a closure so that it can be used
in the statements of the `ℤ`-power count. -/
abbrev twoMulH2 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G ℤ] [IsDiscreteGModule G ℤ] : AddSubgroup (H2 G ℤ) :=
  AddSubgroup.closure (Set.range (fun x : H2 G ℤ => (2 : ℕ) • x))

/-- The `2`-torsion of `H³(G,ℤ)`, as a subtype. -/
abbrev twoTorsionH3 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G ℤ] [IsDiscreteGModule G ℤ] : Type _ :=
  {x : H3 G ℤ // (2 : ℕ) • x = 0}

/-- **The kernel of `H²(G,ℤ) → H²(G,ℤ/2)` is `2·H²(G,ℤ)`** (`exact_H2_B` together with the
identification of the coefficient map as multiplication by `2`). -/
theorem ker_H2Map_eq_twoMulH2 :
    (H2Map (ZSES G).g).ker = twoMulH2 G := by
  have h2f : ∀ y : H2 G ℤ, H2Map (ZSES G).f y = (2 : ℕ) • y :=
    fun y => H2Map_zModTwoCoeffSES_f y
  have hrange : (H2Map (ZSES G).f).range = twoMulH2 G := by
    ext x
    constructor
    · intro hx
      rw [AddMonoidHom.mem_range] at hx
      obtain ⟨y, hy⟩ := hx
      rw [← hy, h2f y]
      exact AddSubgroup.subset_closure ⟨y, rfl⟩
    · intro hx
      have hle : twoMulH2 G ≤ (H2Map (ZSES G).f).range := by
        rw [twoMulH2, AddSubgroup.closure_le]
        rintro _ ⟨y, rfl⟩
        exact AddMonoidHom.mem_range.mpr ⟨y, h2f y⟩
      exact hle hx
  have hker : (H2Map (ZSES G).g).ker = (H2Map (ZSES G).f).range := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact exact_H2_B (ZSES G) x
  rw [hker, hrange]

/-- **The cardinality identity of the `ℤ`-power sequence**: the number of elements of
`H²(G,ℤ/2)` is the product of the number of elements of `H²(G,ℤ)/2H²(G,ℤ)` and of the
`2`-torsion of `H³(G,ℤ)`. -/
theorem natCard_H2_zmodTwo_eq :
    Nat.card (H2 G (ZMod 2)) = Nat.card (H2 G ℤ ⧸ twoMulH2 G) * Nat.card (twoTorsionH3 G) := by
  let δ : H2 G (ZMod 2) →+ H3 G ℤ := connecting2Map (ZSES G)
  have hspec : ∀ (z : Z2 G (ZMod 2)) (u : Cochain2 G ℤ),
      (∀ p : G × G, (ZSES G).g (u p) = (z : Cochain2 G (ZMod 2)) p) →
      ∃ w : Z3 G ℤ, H3.mk w = δ (H2.mk z) ∧
        (∀ p : G × G × G, (ZSES G).f ((w : G × G × G → ℤ) p) = d2Fun (u : G × G → ℤ) p) :=
    fun z u hu => connecting2Map_spec (ZSES G) z u hu
  have hex2 : ∀ x : H2 G (ZMod 2), δ x = 0 ↔ ∃ y : H2 G ℤ, H2Map (ZSES G).g y = x :=
    exact_H2_C (ZSES G) δ hspec
  have hex3 : ∀ x : H3 G ℤ, H3Map (ZSES G).f x = 0 ↔ ∃ y : H2 G (ZMod 2), δ y = x :=
    exact_H3_A (ZSES G) δ hspec
  have h3f : ∀ y : H3 G ℤ, H3Map (ZSES G).f y = (2 : ℕ) • y :=
    fun y => H3Map_zModTwoCoeffSES_f y
  -- The kernel of `δ` is the image of the coefficient map `H²(G,ℤ) → H²(G,ℤ/2)`.
  have hkerδ : δ.ker = (H2Map (ZSES G).g).range := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact hex2 x
  -- The image of `δ` is the `2`-torsion of `H³(G,ℤ)`.
  have hrangeδ : Nat.card δ.range = Nat.card (twoTorsionH3 G) := by
    have hset : ((δ.range : AddSubgroup (H3 G ℤ)) : Set (H3 G ℤ)) = {x | (2 : ℕ) • x = 0} := by
      ext x
      show x ∈ δ.range ↔ (2 : ℕ) • x = 0
      rw [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨y, rfl⟩
        rw [← h3f (δ y)]
        exact (hex3 (δ y)).mpr ⟨y, rfl⟩
      · intro hx
        rw [← h3f x] at hx
        exact (hex3 x).mp hx
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => Set.ext_iff.mp hset x))
  -- The cardinality of a group is that of its kernel times that of its range.
  have hcard : Nat.card (H2 G (ZMod 2)) = Nat.card δ.ker * Nat.card δ.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup δ.ker, mul_comm]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ).toEquiv
  -- The kernel of `δ` has the cardinality of `H²(G,ℤ)/2H²(G,ℤ)`.
  have hkerδcard : Nat.card δ.ker = Nat.card (H2 G ℤ ⧸ twoMulH2 G) := by
    rw [hkerδ, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (H2Map (ZSES G).g)).toEquiv,
      ker_H2Map_eq_twoMulH2]
  rw [hcard, hkerδcard, hrangeδ]

/-- **The relation count from the `ℤ`-power sequence**: if the `2`-rank of `H²(G,ℤ)` is at most
`5` (Wingberg's duality and the class group, `Work.ShafarevichKoch.WingbergDuality`) and the
`2`-torsion of `H³(G,ℤ)` has at most `2` elements (Wingberg's duality and the units of `𝓞 Kc`),
then `#H²(G,ℤ/2) ≤ 2^6`. -/
theorem natCard_H2_zmodTwo_le (hA : Nat.card (H2 G ℤ ⧸ twoMulH2 G) ≤ 2 ^ 5)
    (hB : Nat.card (twoTorsionH3 G) ≤ 2) :
    Nat.card (H2 G (ZMod 2)) ≤ 2 ^ 6 := by
  rw [natCard_H2_zmodTwo_eq]
  calc Nat.card (H2 G ℤ ⧸ twoMulH2 G) * Nat.card (twoTorsionH3 G) ≤ 2 ^ 5 * 2 :=
        Nat.mul_le_mul hA hB
    _ = 2 ^ 6 := by norm_num


end Work.ShafarevichKoch
