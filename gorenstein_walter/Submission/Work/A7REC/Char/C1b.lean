/-
Area `A7REC`: **C1b** — the identification of the character table of `G` with the arithmetic data of
`A7TableLemmaProp` (design passes 6/7; statement approved by the lead, 22:40 UTC).

## The three induced generalised characters

With `G` satisfying `A7RecHyps G S z U V` and one class of involutions, fix `π ∈ S` of order `4`
with `C_G(π) = ⟨π⟩` and `σ ∈ U^#`.  The two *TI subsets* of the pass-6 design are

* `{π, π⁻¹} ⊆ S` (TI with normalizer `N_G(⟨π⟩) = S`, the proved `A7TIOrderFourProp`), and
* `zU = {zσ : σ ∈ U} ⊆ C_G(z)` (TI with normalizer `C_G(z)`, the proved `A7TIzUProp`);

`Δ_π` is the generalised character of `G` induced from the sum of the two faithful linear
characters of `⟨π⟩`, and `Δ_A`, `Δ_B` are the two generalised characters induced from the two
non-trivial classes of linear characters of `zU ≅ U` (see Suzuki 1959 §8, p. 270, and design
pass 6 §2 for the exact combinations; the library statement is
`OddOrder.RepresentationTheory.inner_induce_eq_of_isTISubset`).  Writing `χ = ι i` for the
non-trivial irreducible constituents, the design's indexing data are

`f i = χ(1)`, `e i = (χ, Δ_π)`, `a i = (χ, Δ_A)`, `b i = (χ, Δ_B)`, so that
`χ(π) = e i`, `χ(z) = b i - 2 a i` and `χ(zσ) = a i + b i`.

**This Prop** asserts the existence of that indexing together with the ten arithmetic relations of
`A7TableLemmaProp` *other than* the three rational ones (which are supplied by the proved bridge
`Work.A7REC.a7Bridge` from the proved involution counts `Work.A7REC.c13_counts`).
-/
import Submission.Work.A7REC.Excl
import Submission.Work.A7REC.Char.Bridge

namespace Work.A7REC

open OddOrder.RepresentationTheory Subgroup

/-- **C1b**: the indexing of the non-trivial irreducible characters of `G` occurring in the three
induced generalised characters, by the table data, with the norms, orthogonality, `Δ(1) = 0`, the
congruence, the degree bound of `A7TableLemmaProp`, **and the off-range vanishing** that the proved
bridge `Work.A7REC.a7Bridge` needs (a non-trivial irreducible outside the range of `ι` vanishes at
`z`, i.e. is orthogonal to all three `Δ`'s and hence vanishes on the `2`-singular elements). -/
def A7C1bProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G) (π σ : G),
    A7RecHyps G S z U V → OneInvClass G →
    σ ∈ U → σ ≠ 1 → π ∈ (S : Subgroup G) → orderOf π = 4 →
    centralizer ({π} : Set G) = zpowers π →
    ∃ (n : ℕ) (ι : Fin n → IrreducibleCharacter G) (f : Fin n → ℕ) (e a b : Fin n → ℤ),
      Function.Injective ι ∧
      (∀ i, ι i ≠ trivialIrreducibleCharacter G) ∧
      (∀ χ : IrreducibleCharacter G, χ ≠ trivialIrreducibleCharacter G → χ ∉ Set.range ι →
        (χ : ClassFunction G ℂ) z = 0) ∧
      (∀ i, (ι i : ClassFunction G ℂ) 1 = (f i : ℂ)) ∧
      (∀ i, (ι i : ClassFunction G ℂ) π = (e i : ℂ)) ∧
      (∀ i, (ι i : ClassFunction G ℂ) z = ((b i - 2 * a i : ℤ) : ℂ)) ∧
      (∀ i, (ι i : ClassFunction G ℂ) (z * σ) = ((a i + b i : ℤ) : ℂ)) ∧
      (∀ i, e i ≠ 0 ∨ a i ≠ 0 ∨ b i ≠ 0) ∧
      (∀ i, 2 ≤ f i) ∧
      (∀ i, (f i : ℤ) ∣ 2520) ∧
      (∑ i, e i ^ 2 = 3) ∧ (∑ i, a i ^ 2 = 4) ∧ (∑ i, b i ^ 2 = 7) ∧
      (∑ i, e i * a i = 0) ∧ (∑ i, e i * b i = -1) ∧ (∑ i, a i * b i = 0) ∧
      (1 + ∑ i, e i * (f i : ℤ) = 0) ∧ (∑ i, a i * (f i : ℤ) = 0) ∧
      (1 + ∑ i, b i * (f i : ℤ) = 0) ∧
      (∀ i, ((f i : ℤ) + 5 * (b i - 2 * a i) + 2 * e i) % 8 = 0) ∧
      1 + ∑ i, (f i) ^ 2 ≤ 2520

end Work.A7REC
