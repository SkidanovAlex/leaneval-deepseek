import Submission.Work.Hering.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Permutation-group and Sylow vocabulary for the `Hering` area

`App II(5)` of Peterfalvi I (p. 204) is a general statement about a finite group acting doubly
transitively on a finite set: the normaliser of a Sylow `p`-subgroup of a two-point stabiliser is
again doubly transitive on the fixed points of that Sylow. This file fixes the vocabulary; the
statement itself is in `Work.Hering.Perm.AppII5`.

`IsSylowSubgroup p P K` is an unbundled "`P` is a Sylow `p`-subgroup of `K`", convenient because
our subgroups always live in a fixed ambient group.
-/

set_option autoImplicit false

namespace Work.Hering

/-- Conjugation action of `G` on a normal subgroup `V` (on the subtype `↥V`). -/
instance instMulActionConj {G : Type*} [Group G] (V : Subgroup G) [hV : V.Normal] :
    MulAction G ↥V where
  smul g v := ⟨g * (v : G) * g⁻¹, hV.conj_mem v v.2 g⟩
  one_smul v := by simp [HSMul.hSMul]
  mul_smul g h v := by simp [HSMul.hSMul, mul_assoc]

/-- `X` acts **doubly transitively** on the set `E` (elementwise form). -/
def IsTwoTransitiveAction (X : Type*) (E : Type*) [Group X] [MulAction X E] : Prop :=
  ∀ a b c d : E, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d

/-- `Y` is doubly transitive on the set of points of `E` fixed pointwise by `P`. -/
def IsTwoTransitiveOnFixed (X : Type*) (E : Type*) [Group X] [MulAction X E]
    (Y P : Subgroup X) : Prop :=
  ∀ c d c' d' : E, (∀ x ∈ P, x • c = c) → (∀ x ∈ P, x • d = d) →
    (∀ x ∈ P, x • c' = c') → (∀ x ∈ P, x • d' = d') →
    c ≠ d → c' ≠ d' → ∃ y ∈ Y, y • c = c' ∧ y • d = d'

/-- `P` is a **Sylow `p`-subgroup** of `K`: a `p`-subgroup of `K` maximal with that property. -/
def IsSylowSubgroup {G : Type*} [Group G] (p : ℕ) (P K : Subgroup G) : Prop :=
  P ≤ K ∧ IsPGroup p ↥P ∧ ∀ Q : Subgroup G, P ≤ Q → Q ≤ K → IsPGroup p ↥Q → Q = P

/-- The points of `V` fixed under conjugation by every element of `P`. -/
def conjFixed {G : Type*} [Group G] (P V : Subgroup G) : Set G :=
  {v | v ∈ V ∧ ∀ x ∈ P, x * v * x⁻¹ = v}

/-- **Appendix II(5) of Peterfalvi I (p. 204)**, as a `Prop`: if `X` acts doubly transitively on a
finite set `E` and `P` is a Sylow `p`-subgroup of a two-point stabiliser `X_a ⊓ X_b`, then the
normaliser `N_X(P)` is doubly transitive on the set of fixed points of `P`. -/
def AppII5Prop : Prop :=
  ∀ {X E : Type*} [Group X] [MulAction X E] [Fintype X] [Fintype E]
    (h2 : IsTwoTransitiveAction X E) {p : ℕ} (hp : p.Prime) {a b : E} (hab : a ≠ b)
    {P : Subgroup X}
    (hP : IsSylowSubgroup p P (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b)),
    IsTwoTransitiveOnFixed X E (Subgroup.normalizer (P : Set X)) P

end Work.Hering
