/-
Area `A7REC`: the **p11 bridge** (design pass 11, `_design_gw/Core11A7.lean` §1–§2), which turns
the involution-pair counts `i(π) = 4`, `i(z) = 8`, `i(zσ) = 6` into the three normalised rational
relations that `A7TableLemmaProp` consumes verbatim (constants `32/35`, `64/35`, `48/35`, with the
`1 +` for the principal character).

The statements are copied verbatim from `Core11A7.lean` (in namespace `Work.A7REC`); `A7CharSumProp`
and `A7SplitTrivialProp` come *proved* in that file and their proofs are reproduced here.
-/
import Submission.Work.A7REC.Excl
import Submission.Work.BSW.Char.invPairCount_eq_sum_characters
import Submission.OddOrder.GroupTheory.RepresentationTheory.SumCharacterInvariants

namespace Work.A7REC

open OddOrder.RepresentationTheory Subgroup
open scoped Classical

/-- `C7invPairCount` *is* BSW's `invPairCount` (identical bodies), so BSW's proved
`Work.BSW.Char.invPairCount_eq_sum_characters` applies to it without any work. -/
example {G : Type} [Group G] (x : G) :
    Work.A7REC.C7invPairCount x = Work.BSW.invPairCount G x := rfl

/-! ## B1 and B2 (proved in `Core11A7.lean`; proofs reproduced) -/

/-- **B1** (specialisation of BSW's proved formula).  `|G| = 2520`, `|C(z)| = 24` and one class of
involutions give `(8/35)·i(x) = Σ_{χ ∈ Irr G} χ(z)²χ(x)/χ(1)`. -/
def A7CharSumProp : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (z : G), Nat.card G = 2520 → orderOf z = 2 →
    Nat.card (centralizer ({z} : Set G)) = 24 → (∀ x : G, orderOf x = 2 → IsConj x z) →
    ∀ x : G, (8 / 35 : ℂ) * (Work.A7REC.C7invPairCount x : ℂ) =
      ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) z) ^ 2 * (χ : ClassFunction G ℂ) x / (χ : ClassFunction G ℂ) 1

/-- **B1**, proved. -/
theorem a7CharSum : A7CharSumProp := by
  intro G _ _ z hG hz hC hconj x
  have h := Work.BSW.Char.invPairCount_eq_sum_characters hz hconj x
  rw [show Work.A7REC.C7invPairCount x = Work.BSW.invPairCount G x from rfl, h, hG, hC]
  push_cast
  ring

/-- **B2** (the principal character).  The trivial irreducible contributes `1`, the rest is the sum
over the non-trivial irreducibles. -/
def A7SplitTrivialProp : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (z x : G),
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) z) ^ 2 * (χ : ClassFunction G ℂ) x / (χ : ClassFunction G ℂ) 1 =
      1 + ∑ χ ∈ Finset.univ.erase (trivialIrreducibleCharacter G),
        ((χ : ClassFunction G ℂ) z) ^ 2 * (χ : ClassFunction G ℂ) x / (χ : ClassFunction G ℂ) 1

/-- **B2**, proved. -/
theorem a7SplitTrivial : A7SplitTrivialProp := by
  intro G _ _ z x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (trivialIrreducibleCharacter G))]
  simp [IrreducibleCharacter.coe_trivialIrreducibleCharacter, trivialClassFunction_apply]

/-! ## B3 and the assembled bridge (statements; to be proved as the area's leaves) -/

/-- **B3** (reindexing to the table data).  `ι : Fin n → Irr G` enumerates injectively the
non-trivial irreducibles that occur in `Δ_π, Δ_A, Δ_B`; every other non-trivial irreducible has
`χ(z) = 0`, so its term vanishes. -/
def A7ReindexProp : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (z x : G) (n : ℕ) (ι : Fin n → IrreducibleCharacter G)
    (f : Fin n → ℕ) (a b v : Fin n → ℤ),
    Function.Injective ι → (∀ i, ι i ≠ trivialIrreducibleCharacter G) →
    (∀ χ : IrreducibleCharacter G, χ ≠ trivialIrreducibleCharacter G → χ ∉ Set.range ι →
      (χ : ClassFunction G ℂ) z = 0) →
    (∀ i, (ι i : ClassFunction G ℂ) 1 = f i) →
    (∀ i, (ι i : ClassFunction G ℂ) z = b i - 2 * a i) →
    (∀ i, (ι i : ClassFunction G ℂ) x = v i) →
    ∑ χ ∈ Finset.univ.erase (trivialIrreducibleCharacter G),
        ((χ : ClassFunction G ℂ) z) ^ 2 * (χ : ClassFunction G ℂ) x / (χ : ClassFunction G ℂ) 1 =
      ((∑ i, ((b i - 2 * a i) ^ 2 * v i : ℚ) / (f i : ℚ) : ℚ) : ℂ)

/-- **The p11 bridge.**  Hypotheses: the `A₇` numerics, one class of involutions, the three
involution counts, and the C1c indexing of the constituents.  Conclusion: the three rational
hypotheses of `A7TableLemmaProp`, **verbatim** (same expressions, same constants). -/
def A7BridgeProp : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (z π σ : G),
    Nat.card G = 2520 → orderOf z = 2 → Nat.card (centralizer ({z} : Set G)) = 24 →
    (∀ x : G, orderOf x = 2 → IsConj x z) →
    Work.A7REC.C7invPairCount π = 4 → Work.A7REC.C7invPairCount z = 8 →
    Work.A7REC.C7invPairCount (z * σ) = 6 →
    ∀ (n : ℕ) (ι : Fin n → IrreducibleCharacter G) (f : Fin n → ℕ) (e a b : Fin n → ℤ),
      Function.Injective ι → (∀ i, ι i ≠ trivialIrreducibleCharacter G) →
      (∀ χ : IrreducibleCharacter G, χ ≠ trivialIrreducibleCharacter G → χ ∉ Set.range ι →
        (χ : ClassFunction G ℂ) z = 0) →
      (∀ i, (ι i : ClassFunction G ℂ) 1 = f i) →
      (∀ i, (ι i : ClassFunction G ℂ) π = e i) →
      (∀ i, (ι i : ClassFunction G ℂ) z = b i - 2 * a i) →
      (∀ i, (ι i : ClassFunction G ℂ) (z * σ) = a i + b i) →
      1 + ∑ i, ((b i - 2 * a i) ^ 2 * e i : ℚ) / (f i : ℚ) = 32 / 35 ∧
      1 + ∑ i, ((b i - 2 * a i) ^ 3 : ℚ) / (f i : ℚ) = 64 / 35 ∧
      1 + ∑ i, ((b i - 2 * a i) ^ 2 * (a i + b i) : ℚ) / (f i : ℚ) = 48 / 35

end Work.A7REC
