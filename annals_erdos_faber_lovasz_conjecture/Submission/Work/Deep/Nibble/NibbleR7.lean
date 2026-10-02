import Submission.Work.Deep.Nibble.NibbleGlue
import Submission.Work.Deep.Nibble.RelCover
import Submission.Work.Deep.Nibble.embedStatement_at_r

/-!
# The Nibble Lemma in the `∃ N₀` form (repair R7a of defect D7)

The cone's `NibbleStatementFixed` quantifies the constants `β, γ, ε, ρ, ξ` (and
`r`) *inside* the statement, together with the whole margin bundle
`NibbleMarginsStrong` — including its field `hnbig`, a lower bound on `n` whose
right-hand side mentions only the constants.  Defect D7 (`HANDOFF.md`,
"SESSION 5") is that this lower bound is far too weak: the proof of the Nibble
Lemma needs `n` to dominate expressions such as `(r/(2βp))²`, `(30/κ)^40` and
`2r³` which involve `r` and the constants but are *not* bounded by `hnbig`.

The repair (`R7a`) is the honest asymptotic quantifier order of the paper: fix
the constants, and only then choose the threshold `N₀` — the statement below.
It is strictly stronger than what the §12 chain needs (which instantiates
`r, β, γ, ε, ρ, ξ` by fixed functions of `σ`), and it is exactly the shape in
which the proof can be given.

* `Work.Deep.Nibble.MarginsConst` — the `n`-free fields of the bundle (what one
  must fix before choosing `N₀`), *including* the defect-D8 field `4000 ξ ≤ γ ρ²`
  required by the crossing absorption (`Work.Deep.Nibble.crossingMargins_of_assemblyParams`).
* `Work.Deep.Nibble.nibbleStatementFixed_of_sparseMatching` — the repaired
  statement, conditional on `cor:sparse_egj` (`SparseMatchingStatement`).
* `Work.Deep.Nibble.nibbleStatementFixed_of_relCover` — the same, conditional on
  the family nibble's interface `RelCoverStatement`, from which this chapter
  derives `SparseMatchingStatement`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

local notation "Hypergraph" => ErdosFaberLovaszConjecture.Hypergraph

/-- **The `n`-free part of the margin bundle** (the constants of the Nibble
Lemma), together with the defect-D8 field `4000 ξ ≤ γ ρ²`. -/
structure MarginsConst (r : ℕ) (β γ ε ρ ξ : ℝ) : Prop where
  hr : 2 ≤ r
  /-- the proof of `lem:embed` and of `lem:pseudorandom_matching` need `3 ≤ r` -/
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
  /-- the defect-D8 field: the crossing absorption's `1000 ξ ≤ γp ρ²` at `γp = γ/4` -/
  hxi8 : 4000 * ξ ≤ γ * ρ ^ 2

/-- The `n`-free part of the cone's bundle. -/
theorem marginsConst_of_strong {n : ℕ} {D : ℝ} {r : ℕ} {β γ ε ρ ξ : ℝ}
    (hm : NibbleMarginsStrong n D r β γ ε ρ ξ) (hD8 : 4000 * ξ ≤ γ * ρ ^ 2)
    (hr3 : 3 ≤ r) :
    MarginsConst r β γ ε ρ ξ :=
  { hr := hm.base.hr
    hr3 := hr3
    hβ0 := hm.base.hβ0
    hγ0 := hm.base.hγ0
    hε0 := hm.base.hε0
    hρ0 := hm.base.hρ0
    hξ0 := hm.base.hξ0
    hρ1 := hm.base.hρ1
    hrγ := hm.base.hrγ
    hξγ := hm.base.hξγ
    hβγ := hm.base.hβγ
    hγε := hm.base.hγε
    hγρ₀ := hm.base.hγρ
    hβ := hm.hβ
    hβ4 := hm.hβ4
    hξ := hm.hξ
    hξ2 := hm.hξ2
    hr1 := hm.hr
    hr2 := hm.hr2
    hγρ := hm.hγρ
    hγρε := hm.hγρε
    hε := hm.hε
    hxi8 := hD8 }

/-- **The Nibble Lemma in the `∃ N₀` form, from `cor:sparse_egj`.** -/
theorem nibbleStatementFixed_of_sparseMatching (hS : SparseMatchingStatement) :
    ∀ (r : ℕ) (β γ ε ρ ξ : ℝ), MarginsConst r β γ ε ρ ξ →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : ℕ) (𝓗 𝓗' : MultiHypergraph n)
      (R : Hypergraph (Fin n)) {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)}
      (M : Fin D → Set (Set (Fin n))),
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
      NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M := by
  intro r β γ ε ρ ξ hc
  have hγ1 : γ ≤ 1 := by
    have h1 := hc.hγρ
    have h2 := hc.hρ1
    linarith
  -- the sparsified matching at the assembly's parameters
  have hr3 : 3 ≤ r := hc.hr3
  have hγ0 : 0 < γ := hc.hγ0
  obtain ⟨n₀, hn₀pos, hbody⟩ :=
    (sparseMatchingStatement_iff.mp hS) (r + 1) (by omega) (2 * (γ ^ 2 / 32000)) (γ / 4)
      (by positivity) (by nlinarith [hγ1]) (by positivity) (by nlinarith [hγ1])
  let A : ℕ := ⌈n₀⌉₊
  let B : ℕ := 2 * r ^ 3
  let C : ℕ := Nat.ceil ((r / (2 * (γ ^ 2 / 32000))) ^ 2 + 1)
  let E : ℕ := Nat.ceil ((30 / (γ ^ 2 / 3200)) ^ 40 + 1)
  let F : ℕ := Nat.ceil (Real.exp 2 + 1)
  let X : ℕ := max (max A 4) B
  let Y : ℕ := max (max C E) F
  refine ⟨max X Y, ?_⟩
  intro n hn
  have hX : X ≤ n := le_trans (Nat.le_max_left X Y) hn
  have hY : Y ≤ n := le_trans (Nat.le_max_right X Y) hn
  have hA : A ≤ n :=
    le_trans (le_trans (Nat.le_max_left A 4) (Nat.le_max_left (max A 4) B)) hX
  have h4 : 4 ≤ n :=
    le_trans (le_trans (Nat.le_max_right A 4) (Nat.le_max_left (max A 4) B)) hX
  have hB : B ≤ n := le_trans (Nat.le_max_right (max A 4) B) hX
  have hC : C ≤ n :=
    le_trans (le_trans (Nat.le_max_left C E) (Nat.le_max_left (max C E) F)) hY
  have hE : E ≤ n :=
    le_trans (le_trans (Nat.le_max_right C E) (Nat.le_max_left (max C E) F)) hY
  have hF : F ≤ n := le_trans (Nat.le_max_right (max C E) F) hY
  intro D 𝓗 𝓗' R 𝓥 U S M hm hU hSsub hC1 hU𝓥 huniv𝓥 habs hlinH hle hout hlin' hsize
    hdeg hMmatch hMdisj hMout hMR hMsz hMint
  have hSMA : SparseMatchingAbove A (r + 1) (2 * (γ ^ 2 / 32000)) (γ / 4) := by
    intro m hm'
    exact hbody m (le_trans (Nat.le_ceil n₀) (by exact_mod_cast hm'))
  have hnN₁ : A ≤ n := hA
  have hn2r3 : 2 * r ^ 3 ≤ n := hB
  have hnβp : (r / (2 * (γ ^ 2 / 32000))) ^ 2 + 1 ≤ (n : ℝ) := by
    have h1 : (r / (2 * (γ ^ 2 / 32000))) ^ 2 + 1 ≤ (C : ℝ) := Nat.le_ceil _
    have h2 : (C : ℝ) ≤ (n : ℝ) := by exact_mod_cast hC
    linarith
  have hnκ : (30 / (γ ^ 2 / 3200)) ^ 40 + 1 ≤ (n : ℝ) := by
    have h1 : (30 / (γ ^ 2 / 3200)) ^ 40 + 1 ≤ (E : ℝ) := Nat.le_ceil _
    have h2 : (E : ℝ) ≤ (n : ℝ) := by exact_mod_cast hE
    linarith
  have hne : Real.exp 2 + 1 ≤ (n : ℝ) := by
    have h1 : Real.exp 2 + 1 ≤ (F : ℝ) := Nat.le_ceil _
    have h2 : (F : ℝ) ≤ (n : ℝ) := by exact_mod_cast hF
    linarith
  exact nibbleConclusion_of_all (r := r) M hm hc.hxi8 hc.hr3
    (embedStatement_at_r hc.hr3) hSMA hnN₁ h4 hn2r3 hnβp hnκ hne hU hSsub hC1 hU𝓥 huniv𝓥
    habs hlinH hle hout hlin' hsize hdeg hMmatch hMdisj hMout hMR hMsz hMint

/-- **The Nibble Lemma in the `∃ N₀` form, from the family nibble's interface.** -/
theorem nibbleStatementFixed_of_relCover (h : RelCoverStatement) :
    ∀ (r : ℕ) (β γ ε ρ ξ : ℝ), MarginsConst r β γ ε ρ ξ →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : ℕ) (𝓗 𝓗' : MultiHypergraph n)
      (R : Hypergraph (Fin n)) {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)}
      (M : Fin D → Set (Set (Fin n))),
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
  nibbleStatementFixed_of_sparseMatching (sparseMatchingStatement_of_relCover h)

end

end Work.Deep.Nibble
