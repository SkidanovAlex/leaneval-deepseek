import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.CountingDefs
import Submission.Work.ZassenhausSuzuki.GenHypSetup
import Submission.Work.ZassenhausSuzuki.Q_suzuki_sq
import Submission.Work.ZassenhausSuzuki.numClasses_stronglyReal_general
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.normalizer_twoPoint
import Submission.Work.ZassenhausSuzuki.centralizer_twoPoint_eq
import Submission.Work.ZassenhausSuzuki.twoPoint_conj_inf_eq_bot
import Submission.Work.ZassenhausSuzuki.prime_dvd_twoPoint_gives_involution
import Submission.Work.ZassenhausSuzuki.QSZ_abelian_of_order_three
import Submission.Work.Higman.Main
import Submission.Work.Higman.card_eq_sq_or_cube

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vocabulary for `Odd.odd_isStronglyReal_of_suzuki`

The target of the area (`Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki`) is the
statement that in a finite **simple** group `G` with a split rank-one Zassenhaus datum
`H = Q ⋊ D` whose root group `Q` is a Suzuki `2`-group with `|Q| = |Z(Q)|²` (i.e. the
`Sz(2^{2n+1})` case), every element of odd order is a product of two involutions.

The proof follows Huppert–Blackburn III XI.11.6 (a) (the counting argument of Suzuki 1962
§10): with `ℱ = {C_G(x) : x strongly real, x ≠ 1, x² ≠ 1}` and

* `𝔄 = {x : x strongly real, orderOf x odd}` (`SRodd`),
* `B = {x : orderOf x odd, x ≠ 1, x not strongly real}` (`BadOdd`),

one has the two counting laws

* `Σ_{A ∈ ℱ} (|A| - 1) = |𝔄| - 1`                    (element count / disjoint union),
* `Σ_{A ∈ ℱ} |A| (|A| - 1) = |G| (q - 1)`            (class count, Suzuki Proposition 13),

together with the structural facts `[N_G(A) : A] ∈ {2,4}` (HB 11.4) for every `A ∈ ℱ` not
conjugate to `D = twoPoint H t`, `|A|` odd `≥ 5`, and the pairwise coprimality of the orders of
non-conjugate members of `ℱ`.  The numerics then force `B = ∅`.

This file fixes the vocabulary: the hypothesis bundle `SzOddHyp`, `q = |Z(Q)|`, the family
`IsCZ`/`FinsetCZ` of `ℱ`-subgroups, the index `kA A = [N_G(A) : A]`, and the sets `SRodd`,
`BadOdd`, `PowTwoOrder`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- The hypothesis bundle of `Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki`:
`G` simple, a split rank-one Zassenhaus datum `H = Q ⋊ D` with `Q` a non-abelian `2`-group
that is a Suzuki `2`-group of order `|Z(Q)|²`. -/
structure SzOddHyp (H Q : Subgroup G) (t : G) : Prop where
  hG : IsSimpleGroup G
  hsplit : IsSplitRankOne H Q t
  hzass : IsZassenhaus H
  h2 : IsPGroup 2 Q
  hSuz : IsSuzukiTwoGroup ↥Q
  hord : Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2
  hnab : ¬ IsAbelianSubgroup Q

/-- `q = |Z(Q)| = |Q₀sub H|`, the order of the centre of the Suzuki `2`-group `Q`; the root
group has order `q²` and the two-point stabiliser has order `q - 1`. -/
noncomputable def q (H : Subgroup G) : ℕ := Nat.card ↥(Work.ThmF.Q0sub H)

/-- `A` lies in the Bender–Suzuki family `ℱ`: `A` is the centraliser of a non-identity
*strongly real* element that is not an involution (equivalently, by Suzuki's Proposition 14, of
a non-identity element of odd order that is a product of two involutions). -/
def IsCZ (A : Subgroup G) : Prop :=
  ∃ x : G, IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1 ∧ Subgroup.centralizer ({x} : Set G) = A

/-- `kA A = [N_G(A) : A]`. -/
noncomputable def kA (A : Subgroup G) : ℕ :=
  (A.subgroupOf (Subgroup.normalizer (A : Set G))).index

/-- The finite set of `ℱ`-subgroups. -/
noncomputable def FinsetCZ : Finset (Subgroup G) :=
  letI := Fintype.ofFinite (Subgroup G)
  Finset.univ.filter IsCZ

/-- The `ℱ`-subgroups that are not conjugate to `D = twoPoint H t`. -/
noncomputable def FinsetCZ' (H : Subgroup G) (t : G) : Finset (Subgroup G) :=
  FinsetCZ.filter (fun A => ¬ ∃ g : G, A = conj g (twoPoint H t))

/-- The strongly real elements of odd order (this set contains `1`). -/
def SRodd (x : G) : Prop := IsStronglyReal x ∧ Odd (orderOf x)

/-- The odd-order elements that are *not* strongly real (`1` is not one of them). -/
def BadOdd (x : G) : Prop := Odd (orderOf x) ∧ x ≠ 1 ∧ ¬ IsStronglyReal x

/-- Elements of `2`-power order. -/
def PowTwoOrder (x : G) : Prop := ∃ k : ℕ, orderOf x = 2 ^ k

end Work.ZassenhausSuzuki.Odd
