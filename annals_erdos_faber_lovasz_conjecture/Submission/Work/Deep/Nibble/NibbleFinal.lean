import Submission.Work.Deep.Nibble.NibbleR7
import Submission.Work.Deep.Nibble.relCoverStatement

/-!
# The Nibble Lemma — the unconditional `∃ N₀` form

`Work.Deep.Nibble.relCoverStatement` (`relCoverStatement.lean`) proves the family-nibble
interface, and `Work.Deep.Nibble.nibbleStatementFixed_of_relCover` (`NibbleR7.lean`)
converts it into the Nibble Lemma `lem:nibble2` in the **R7a** form agreed with the cone:
the constants are fixed first, and only then is the threshold `N₀` chosen.

The theorem below is therefore the chapter's headline, with **no leftover hypothesis**:
`Work.Deep.Nibble.nibbleStatementFixed`.

(The route, replacing the blocked direct family nibble: Kahn's soft colouring
(`Work.Deep.Kahn.kahnStatement`, proved) applied to a random balanced vertex partition,
then one uniformly random colour class per part — EGJ's construction with the weight
function `ω_S(e) = |e ∩ S|`; see the module documentation of `relCoverStatement.lean`
for why the direct nibble cannot start from `(1±κ)D`-regular data.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

/-- **`lem:nibble2` in the `∃ N₀` form, with no leftover hypothesis.** -/
theorem nibbleStatementFixed :
    ∀ (r : ℕ) (β γ ε ρ ξ : ℝ), MarginsConst r β γ ε ρ ξ →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : ℕ) (𝓗 𝓗' : MultiHypergraph n)
      (R : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) {𝓥 : Set (Set (Fin n))}
      {U S : Set (Fin n)} (M : Fin D → Set (Set (Fin n))),
      NibbleMarginsStrong n (D : ℝ) r β γ ε ρ ξ →
      U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε) →
      S ⊆ U →
      ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
        (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ)) →
      U ∈ 𝓥 → (Set.univ : Set (Fin n)) ∈ 𝓥 →
      IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ →
      𝓗.IsLinear →
      𝓗' ≤ 𝓗 →
      (∀ e ∈ 𝓗'.edges, e ∉ R) →
      𝓗'.IsLinear →
      (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
      (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
      (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
      (∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j)) →
      (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) →
      (∀ i, ∀ e ∈ M i, e ∉ R) →
      (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
      (∀ e ∈ 𝓗'.edgeSet,
        (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
      NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M :=
  nibbleStatementFixed_of_relCover relCoverStatement

/-- **A weaker constant bundle that §12 can supply without editing `NibbleMarginsStrong`.**
Same fields as `MarginsConst` except that the defect-D8 field `4000 ξ ≤ γ ρ²` is replaced
by `4·10^{-9} ε ≤ ρ`, which is *free* in §12's regime (`ρ = σ/2`, `ε = σ³/10^42`).  Together
with the bundle's `10^{12} ξ ≤ γ ρ ε` it implies D8. -/
structure MarginsConstWeak (r : ℕ) (β γ ε ρ ξ : ℝ) : Prop where
  hr : 2 ≤ r
  hr3 : 3 ≤ r
  hβ0 : 0 < β
  hγ0 : 0 < γ
  hε0 : 0 < ε
  hρ0 : 0 < ρ
  hξ0 : 0 < ξ
  hρ1 : ρ ≤ 1
  hrγ : 4 ≤ γ * (r : ℝ)
  hξγ : 4 * ξ ≤ γ
  hβγ : 16 * β ≤ γ ^ 2
  hγε : 4 * γ ≤ ε
  hγρ₀ : 4 * γ ≤ ρ
  hβ : 10 ^ 12 * β ≤ (γ * ρ * ε) ^ 2
  hβ4 : β ≤ γ ^ 4 / 10 ^ 12
  hξ : 10 ^ 12 * ξ ≤ γ * ρ * ε
  hξ2 : ξ ≤ γ ^ 2 / 10 ^ 8
  hr1 : 10 ^ 12 ≤ γ * ρ * ε * (r : ℝ)
  hr2 : 10 ^ 8 ≤ γ ^ 2 * (r : ℝ)
  hγρ : 10 ^ 6 * γ ≤ ρ
  hγρε : 10 * γ ≤ ρ * ε
  hε : 4000 * ε ≤ 1
  /-- the D8 inequality, in the form in which §12 can supply it -/
  hρε : 4 * (10 : ℝ) ^ (-9 : ℤ) * ε ≤ ρ

/-- The weak bundle plus the bundle's own `10^{12} ξ ≤ γ ρ ε` gives D8; every other field
is a projection. -/
theorem marginsConst_of_weak {r : ℕ} {β γ ε ρ ξ : ℝ} (h : MarginsConstWeak r β γ ε ρ ξ) :
    MarginsConst r β γ ε ρ ξ :=
  { hr := h.hr
    hr3 := h.hr3
    hβ0 := h.hβ0
    hγ0 := h.hγ0
    hε0 := h.hε0
    hρ0 := h.hρ0
    hξ0 := h.hξ0
    hρ1 := h.hρ1
    hrγ := h.hrγ
    hξγ := h.hξγ
    hβγ := h.hβγ
    hγε := h.hγε
    hγρ₀ := h.hγρ₀
    hβ := h.hβ
    hβ4 := h.hβ4
    hξ := h.hξ
    hξ2 := h.hξ2
    hr1 := h.hr1
    hr2 := h.hr2
    hγρ := h.hγρ
    hγρε := h.hγρε
    hε := h.hε
    hxi8 := by
      -- `4000 ξ ≤ 4·10^{-9} γ ρ ε ≤ γ ρ²`
      have h1 : 4000 * ξ ≤ 4 * (10 : ℝ) ^ (-9 : ℤ) * (γ * ρ * ε) := by
        have h2 : ξ ≤ γ * ρ * ε / 10 ^ 12 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 12)]
          nlinarith [h.hξ]
        have h3 : 4 * (10 : ℝ) ^ (-9 : ℤ) = 4000 / 10 ^ 12 := by norm_num
        rw [h3]
        nlinarith [h2]
      have h5 : 4 * (10 : ℝ) ^ (-9 : ℤ) * (γ * ρ * ε) ≤ γ * ρ ^ 2 := by
        have h6 : 4 * (10 : ℝ) ^ (-9 : ℤ) * γ * ε ≤ γ * ρ := by
          have h7 := h.hρε
          nlinarith [h7, h.hγ0]
        nlinarith [h6, h.hρ0]
      linarith [h1, h5] }

/-- **`lem:nibble2` in the `∃ N₀` form, from the bundle §12 can supply.** -/
theorem nibbleStatementFixed_weak :
    ∀ (r : ℕ) (β γ ε ρ ξ : ℝ), MarginsConstWeak r β γ ε ρ ξ →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : ℕ) (𝓗 𝓗' : MultiHypergraph n)
      (R : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) {𝓥 : Set (Set (Fin n))}
      {U S : Set (Fin n)} (M : Fin D → Set (Set (Fin n))),
      NibbleMarginsStrong n (D : ℝ) r β γ ε ρ ξ →
      U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε) →
      S ⊆ U →
      ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
        (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ)) →
      U ∈ 𝓥 → (Set.univ : Set (Fin n)) ∈ 𝓥 →
      IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ →
      𝓗.IsLinear →
      𝓗' ≤ 𝓗 →
      (∀ e ∈ 𝓗'.edges, e ∉ R) →
      𝓗'.IsLinear →
      (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
      (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
      (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
      (∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j)) →
      (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) →
      (∀ i, ∀ e ∈ M i, e ∉ R) →
      (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
      (∀ e ∈ 𝓗'.edgeSet,
        (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
      NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M :=
  fun r β γ ε ρ ξ h => nibbleStatementFixed r β γ ε ρ ξ (marginsConst_of_weak h)

end

end Work.Deep.Nibble
