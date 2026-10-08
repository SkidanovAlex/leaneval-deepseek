import Submission.Blueprint.Interfaces
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The named literature inputs of area `ZassenhausTwoGroup`

This module fixes the *two* character-theoretic inputs that Feit's proof of Theorem 1 (the
Zassenhaus case) consumes, together with the displayed computations of his §3 that the area
derives from them.  All page references are to the vision transcription of

> W. Feit, *On a class of doubly transitive permutation groups*, Illinois J. Math. **4** (1960)
> 170–186,

in `REFS/vision/feit1960/p0006.md` … `p0015.md` (journal pages 175–184).

## Notation

In the rank-one Zassenhaus setting of the area (`IsSplitRankOne H Q t`, `IsZassenhaus H`) Feit's
letters are:

* `M = Q`, `m = |M| = |Q|` (the Frobenius kernel of the point stabiliser `H = Q ⋊ D`);
* `H_Feit = 1`, so Hypothesis II (p. 175) degenerates to conditions on `M = Q` alone;
* Feit's `Q` (= the two-point stabiliser, order `q`) is our `D = twoPoint H t`;
* `N(M) = N_G(Q) = H = Q ⋊ D` (proved in the area: `normalizer_Q_eq`), so Feit's
  `ζ̃_i = Ind_Q^{N(Q)} ζ_i` is `Ind_Q^H ζ_i`, and for `y ∈ Q ∖ 1` the values of `Ind_Q^G ζ_i`
  and `Ind_Q^H ζ_i` agree (both are `(1/m) ∑_{x ∈ H} ζ_i(x y x⁻¹)`), which is why the statements
  below can use `Work.Induction.indFun Q` (induction to `G`) also for the `H`-induced values.

## What is assumed here

* `FeitThm2Prop` — Feit's **Theorem 2** (p. 176) with **Corollary 2.1** (p. 178) and
  **Corollary 2.4** (p. 179), in the rank-one form.
* `BrauerFowlerProp` — Feit's **Lemma 3.4** and **Lemma 3.5** (pp. 181–182), whose proofs rest
  on the Brauer–Fowler counting theorems ([2, Lemma 3A, Corollary 2B, Theorem 2J]).
* `FeitSection3Prop` — the *displayed* character-theoretic consequences of §3 (pp. 182–184):
  the values `(18)`, the orthogonality `(19)`, the norm `(20)`, the value relation `(23)`/`(24)`
  (`χ₁(1) = q`) and the tensor-product statement `(27)`.

The area proves `FeitInequalityProp` (Feit's inequality `(28)`, `2q ≥ m - 1`) from
`FeitSection3Prop`; see `Count` and `Assembly`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.ZassenhausTwoGroup

/-- **Feit 1960, Theorem 2 (p. 176) with Corollaries 2.1 (p. 178) and 2.4 (p. 179).**

In a finite simple group `G` with rank-one Zassenhaus data `H = Q ⋊ D` (`D = twoPoint H t`)
in which `Q` is not a `2`-group — so that `Q` is nilpotent and not a `p`-group, and
Hypothesis II of Feit's §2 holds with `M = Q`, `h = 1` — for every choice of a non-trivial
irreducible character `ζ` of `Q` there is an *exceptional* irreducible character `χ ζ` of `G`,
with a global sign `ε = ±1` and a rational integer `c`, such that:

* **(1)** `z_{ζ'} · Ind_Q^G ζ - z_ζ · Ind_Q^G ζ' = ε (z_{ζ'} χ_ζ - z_ζ χ_{ζ'})` whenever
  `Ind_Q^H ζ ≠ Ind_Q^H ζ'` (i.e. `ζ, ζ'` lie in different `D`-orbits of `Irr Q`), where
  `z_ζ = ζ(1)`;
* **(Cor 2.1)** `z_{ζ'} χ_ζ - z_ζ χ_{ζ'}` vanishes on every element which is not conjugate to an
  element of `Q ∖ 1`;
* **(Cor 2.4)** `χ_ζ(y) = ε · Ind_Q^H ζ(y) + z_ζ · c` for `y ∈ Q ∖ 1`, and every irreducible
  character of `G` which is not one of the `χ_ζ` is constant on `Q ∖ 1`.

Hypotheses of Theorem 2 not repeated here: `q ≠ m - 1` is Feit's own proviso, and "`M` is not a
non-abelian `p`-group with `[M : M'] < 4q²`" is automatic because `Q` is not a `p`-group at all
(`|Q|` is even and `Q` is not a `2`-group). -/
def FeitThm2Prop : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G) (t : G),
    IsSplitRankOne H Q t → IsZassenhaus H → ¬ IsPGroup 2 Q →
    Nat.card (twoPoint H t) ≠ Nat.card Q - 1 →
    ∃ (ε : ℤ) (_ : ε = 1 ∨ ε = -1) (c : ℤ) (χ : (↥Q → ℂ) → G → ℂ),
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ ζ ∈ Work.CharCore.Irr G) ∧
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
        Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' →
        ∀ g : G, (ζ' 1) * Work.Induction.indFun Q ζ g
            - (ζ 1) * Work.Induction.indFun Q ζ' g
          = (ε : ℂ) * ((ζ' 1) * χ ζ g - (ζ 1) * χ ζ' g)) ∧
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
        Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' →
        ∀ g : G, (¬ ∃ x : G, x * g * x⁻¹ ∈ Q ∧ x * g * x⁻¹ ≠ 1) →
          (ζ' 1) * χ ζ g - (ζ 1) * χ ζ' g = 0) ∧
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ y : G, y ∈ Q → y ≠ 1 →
        χ ζ y = (ε : ℂ) * Work.Induction.indFun Q ζ y + (ζ 1) * (c : ℂ)) ∧
      (∀ φ ∈ Work.CharCore.Irr G, (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → φ ≠ χ ζ) →
        ∀ y : G, y ∈ Q → y ≠ 1 → ∀ y' : G, y' ∈ Q → y' ≠ 1 → φ y = φ y')

/-- **Feit 1960, Lemma 3.4 and Lemma 3.5 (pp. 181–182).**

* (Lemma 3.4) `G` has exactly one class of involutions.
* (Lemma 3.5) There are at least `q = |D|` conjugacy classes of `G` which contain no element of
  `Q^G`, i.e. no conjugate of an element of `Q`; equivalently `k(G) > q + 1`, i.e.
  `Nat.card (twoPoint H t) + 1 < Nat.card (ConjClasses G)`.

  (**Correction**, lead design note `NOTES_LEAD_probe1630.md` of 2026-10-03: an earlier version of
  this conjunct used `Nat.card Q` (= Feit's `m`) where Feit's Lemma 3.5 has `q = |D|`; that is
  inconsistent with the area's own route `k(G) ≤ q + 2` from display (20) and is unprovable along
  Feit's argument.  The statement below uses `|D|`.)

The proofs of these two lemmas are the only place where Feit uses the Brauer–Fowler counting
theorems ([2] = Brauer–Fowler, Ann. of Math. **62** (1955): Lemma 3A and Corollary 2B for 3.4,
Theorem 2J for 3.5).  They are what feeds the non-exceptional character count of Lemma 3.5 into
the constituent analysis `(21)`–`(24)` of §3. -/
def BrauerFowlerProp : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G) (t : G),
    IsSplitRankOne H Q t → IsZassenhaus H → ¬ IsPGroup 2 Q →
    (∃ u : G, orderOf u = 2 ∧ ∀ v : G, orderOf v = 2 → IsConj u v) ∧
    Nat.card (twoPoint H t) + 1 < Nat.card (ConjClasses G)

/-- **Feit 1960, §3, pp. 182–184: the displayed character-theoretic consequences.**

Feit's derivation in §3 produces, in the rank-one setting with `Q` not a `2`-group:

* **(18), (19)** — with `η_0, …, η_{q-1}` the irreducible characters of `H/Q ≅ D`
  (`η_0` trivial, `η_{i + (q-1)/2} = η̄_i`), the induced characters `η_i^* = Ind_H^G η_i`
  (`i ≥ 1`) are pairwise distinct irreducible characters of `G` of degree `m + 1 = |Q| + 1`;
* **(20)** — `‖ζ_1^*‖² = q + 1` for a non-trivial linear character `ζ_1` of `Q`;
* **(23), (24)** — there is an irreducible character `χ_1` of `G` — the exceptional character
  associated with `ζ_1` — of degree `q` (this is the only quantitative input the count needs
  from `(20)`–`(24)`);
* **(27)** — each `η_i^*` (`1 ≤ i ≤ (q-1)/2`) is a constituent of `χ_1 χ̄_1`.

The statements are combined into the existential form used by the count. -/
def FeitSection3Prop : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G) (t : G),
    IsSplitRankOne H Q t → IsZassenhaus H → ¬ IsPGroup 2 Q →
    ∃ (χ : G → ℂ) (η : Fin ((Nat.card (twoPoint H t) - 1) / 2) → G → ℂ),
      χ ∈ Work.CharCore.Irr G ∧ χ 1 = (Nat.card (twoPoint H t) : ℂ) ∧
      (∀ i, η i ∈ Work.CharCore.Irr G) ∧
      (∀ i, η i 1 = (Nat.card Q : ℂ) + 1) ∧
      Function.Injective η ∧
      (∀ i, Work.CharCore.cfInner (χ * fun g => star (χ g)) (η i) ≠ 0)

end Work.ZassenhausTwoGroup
