import Submission.Work.ConeSwitch.MathlibNoHG

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

section RoundDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree of `v` in the hypergraph `𝓖` (a family of finite subsets of `V`). -/
noncomputable def hd (𝓖 : Set (Set V)) (v : V) : ℕ := Nat.card {e : 𝓖 // v ∈ (e : Set V)}

/-- The set of edges of `𝓖` meeting `e` (other than `e` itself). -/
def meetFam (𝓖 : Set (Set V)) (e : Set V) : Set (Set V) := {f | f ∈ 𝓖 ∧ f ≠ e ∧ (f ∩ e).Nonempty}

/-- `𝓖` is linear. -/
def HLin (𝓖 : Set (Set V)) : Prop := 𝓖.Pairwise fun e₁ e₂ => (e₁ ∩ e₂).Subsingleton

/-- `𝓖` is `r`-uniform. -/
def HUnif (𝓖 : Set (Set V)) (r : ℕ) : Prop := ∀ e ∈ 𝓖, e.ncard = r

/-- The kept edges of an outcome `ω : 𝓖 → Bool`. -/
def kept (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) : Set (Set V) := {e | ∃ he : e ∈ 𝓖, ω ⟨e, he⟩ = true}

/-- The vertices covered by the kept edges. -/
def covX (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) : Set V := ⋃ e ∈ kept 𝓖 ω, e

/-- The isolated kept edges (a matching). -/
def isoFam (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) : Set 𝓖 :=
  {e | ω e = true ∧ ∀ f : 𝓖, f ≠ e → ω f = true → (f.1 ∩ e.1).Nonempty = False}

/-- The residual vertex set after a round. -/
def residV (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) : Set V := (covX 𝓖 ω)ᶜ

/-- The residual hypergraph after a round. -/
def residH (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) : Set (Set V) := {e ∈ 𝓖 | e ⊆ residV 𝓖 ω}

/-- The number of kept edges through `v`. -/
noncomputable def kAt (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (v : V) : ℕ :=
  Nat.card {e : 𝓖 // v ∈ (e : Set V) ∧ ω e = true}

/-- `S`: the collision multiplicity `∑_w k_w · 1[k_w ≥ 2]`. -/
noncomputable def collMult (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) : ℕ :=
  ∑ v : V, if 2 ≤ kAt 𝓖 ω v then kAt 𝓖 ω v else 0

/-- The "blocked" edges through `v`: those meeting a kept edge. -/
noncomputable def blk (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (v : V) : ℕ :=
  Nat.card {e : 𝓖 // v ∈ (e : Set V) ∧ ((e.1 : Set V) ∩ covX 𝓖 ω).Nonempty}


/-- **The conclusion of one round of the nibble**, as a predicate on the outcome `ω`
(a `Bool` for each edge of `𝓖`, `true` = the edge is kept).  `θ` is the expected number of
kept edges through a vertex, `D` the typical degree, `δ` the slack, `D'` the level of the
residual hypergraph and `ε'` the relative accuracy of the residual degrees. -/
noncomputable def RoundGood {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (r D : ℕ)
    (θ δ ε' D' : ℝ) (ω : 𝓖 → Bool) : Prop :=
  |(((kept 𝓖 ω).ncard : ℝ) - (𝓖.ncard : ℝ) * (θ / (D : ℝ)))|
      ≤ δ * ((𝓖.ncard : ℝ) * (θ / (D : ℝ)))
  ∧ |(((covX 𝓖 ω).ncard : ℝ) - (1 - Real.exp (-θ)) * (Fintype.card V : ℝ))|
      ≤ δ * (Fintype.card V : ℝ)
  ∧ (collMult 𝓖 ω : ℝ) ≤ (1 + δ) * (θ - θ * Real.exp (-θ)) * (Fintype.card V : ℝ)
  ∧ (∀ v : V, v ∉ covX 𝓖 ω → |((hd (residH 𝓖 ω) v : ℝ)) - D'| ≤ ε' * D')

end RoundDefs




end Work.Deep.Nibble
