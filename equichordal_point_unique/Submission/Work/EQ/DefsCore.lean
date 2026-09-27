import Submission.Work.EQ.Defs

/-! Core definitions for the equichordal Thm 6–8 route (design: Submission/Work/EQ/DESIGN_CORE.md; κ patch 2026-09-25). -/

namespace Work.EQ

open Complex Filter _root_.Topology

/-- Data of a bi-infinite chain of the equichordal relation: the orbit `n ↦ Pₙ ∈ ℂ²` in
rectangular coordinates `(x, y)`, then the stable linearising parameter `ψ₁` and the unstable
one `ψ₂`. -/
abbrev ChainData : Type := (ℤ → ℂ × ℂ) × ℂ × ℂ

/-- The closed (polynomial) equichordal relation in rectangular coordinates of `ℂ²`, with
`O₂ = (a/2, 0)`: `P + Q` is a unit vector (complex bilinear square norm) parallel to `P - O₂`.
The two local branches are `Q = -P ± (P - O₂)/ρ`, `ρ² = (x - a/2)² + y²`. -/
def EqRelC (a : ℝ) (P Q : ℂ × ℂ) : Prop :=
  (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = 1 ∧
    (Q.1 + P.1) * P.2 = (Q.2 + P.2) * (P.1 - ((a / 2 : ℝ) : ℂ))

/-- A regular pair of the equichordal relation: `EqRelC` and both local branches (forward at
`P`, backward at `Q`) are biholomorphic, i.e. `P` is off the isotropic lines through `O₂` and
`Q` is off the isotropic lines through `O₁ = (-a/2, 0)`. -/
def RegPair (a : ℝ) (P Q : ℂ × ℂ) : Prop :=
  EqRelC a P Q ∧ (P.1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2 ≠ 0 ∧
    (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 ≠ 0

/-- The local stable curve of `A₁ = (-1/2, 0)` in rectangular coordinates, in the linearising
parameter `u` (complex form of `germPt`, with the removable singularity at `u = 0` filled by
`dslope`): `x = a h(λu)/(h(λu) - h u) - a/2`, `y = a h u h(λu)/(h(λu) - h u)`. -/
noncomputable def germC (a : ℝ) (h : ℂ → ℂ) (u : ℂ) : ℂ × ℂ :=
  (a * dslope (fun v => h ((eqLam a : ℂ) * v)) 0 u /
      dslope (fun v => h ((eqLam a : ℂ) * v) - h v) 0 u - a / 2,
    a * u * dslope h 0 u * dslope (fun v => h ((eqLam a : ℂ) * v)) 0 u /
      dslope (fun v => h ((eqLam a : ℂ) * v) - h v) 0 u)

/-- The bisector reflection `(x, y) ↦ (-x, y)`; it conjugates the relation to its inverse. -/
noncomputable def eqMirror (P : ℂ × ℂ) : ℂ × ℂ := (-P.1, P.2)

/-- The local unstable curve of `A₂ = (1/2, 0)`: the mirror image of the stable one. -/
noncomputable def ugermC (a : ℝ) (h : ℂ → ℂ) (v : ℂ) : ℂ × ℂ := eqMirror (germC a h v)

/-- `p` is a complex heteroclinic chain: consecutive points form regular pairs, `ψ₁, ψ₂ ≠ 0`,
the forward tail is the stable germ at `λⁿ ψ₁`, the backward tail the unstable germ at `λⁿ ψ₂`. -/
def IsChain (a : ℝ) (h : ℂ → ℂ) (p : ChainData) : Prop :=
  (∀ n : ℤ, RegPair a (p.1 n) (p.1 (n + 1))) ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧
    (∀ᶠ n : ℕ in atTop, p.1 n = germC a h ((eqLam a : ℂ) ^ n * p.2.1)) ∧
    ∀ᶠ n : ℕ in atTop, p.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * p.2.2)

/-- Rychlik's unbranched connection surface `⁰H` (without its branch points and the chains
through points at infinity): chains that sit in a continuous one-parameter family of chains
parametrised by `ψ₁` itself. It carries the subspace topology of
`(ℤ → ℂ × ℂ) × ℂ × ℂ`. -/
def H0 (a : ℝ) (h : ℂ → ℂ) : Set ChainData :=
  {p | ∃ ε : ℝ, 0 < ε ∧ ∃ f : ℂ → ChainData, ContinuousOn f (Metric.ball p.2.1 ε) ∧
    f p.2.1 = p ∧ ∀ u ∈ Metric.ball p.2.1 ε, IsChain a h (f u) ∧ (f u).2.1 = u}

/-- The shift `σ` on chain data: `Pₙ ↦ Pₙ₊₁`, `ψ₁ ↦ λψ₁`, `ψ₂ ↦ ψ₂/λ`. The invariant
parameter `ψ₁ψ₂` is preserved (resonance `λ₁λ₂ = 1`). -/
noncomputable def hShift (a : ℝ) (p : ChainData) : ChainData :=
  (fun n => p.1 (n + 1), (eqLam a : ℂ) * p.2.1, p.2.2 / (eqLam a : ℂ))

/-- The backward local branch with sign `s`: `P = -Q ± (Q - O₁)/ρ'`, `ρ'² = (x + a/2)² + y²`,
principal square root. `invBranch a true` is the principal branch at `A₁`. -/
noncomputable def invBranch (a : ℝ) (s : Bool) (Q : ℂ × ℂ) : ℂ × ℂ :=
  (-Q.1 + (if s then (1 : ℂ) else -1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) /
      ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ),
    -Q.2 + (if s then (1 : ℂ) else -1) * Q.2 /
      ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ))

/-- Rychlik's stable fan (§5.13): for a finite branch word `ε` (followed by the principal
branch forever), `fan ε u` is the point whose forward orbit along `ε` lands on the stable germ
at `λ^{|ε|} u`. -/
noncomputable def fan (a : ℝ) (h : ℂ → ℂ) : List Bool → ℂ → ℂ × ℂ
  | [], u => germC a h u
  | s :: ε, u => invBranch a s (fan a h ε ((eqLam a : ℂ) * u))

/-- The characteristic value of a fan element returning to `A₁` (Rychlik (91)). -/
noncomputable def charVal (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) : ℂ :=
  deriv (fun u => (fan a h ε u).2) 0 / deriv (fun u => (germC a h u).2) 0

/-- Number of positions of the word at which the fan centre is not `A₁` (Rychlik (95)). -/
noncomputable def nonA1Count (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) : ℕ :=
  Set.ncard {k : ℕ | k < ε.length ∧ fan a h (ε.drop k) 0 ≠ ((-1 / 2 : ℂ), (0 : ℂ))}

/-- `e` parametrises a punctured neighbourhood of a puncture of `H0` (a branch point, a
critical point of `ψ₁`, or a chain through `O₁`, `O₂` or a point at infinity), with
`ψ₁ ∘ e = u₀ + κ ζᵏ` (`κ ≠ 0` a scale) and meromorphic chain coordinates. -/
def IsPuncturedChart (a : ℝ) (h : ℂ → ℂ) (e : ℂ → ChainData) (u₀ : ℂ) (k : ℕ) : Prop :=
  0 < k ∧ u₀ ≠ 0 ∧ ∃ κ : ℂ, κ ≠ 0 ∧
    (∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}, e ζ ∈ H0 a h ∧ (e ζ).2.1 = u₀ + κ * ζ ^ k) ∧
    Set.InjOn e (Metric.ball (0 : ℂ) 1 \ {0}) ∧ ContinuousOn e (Metric.ball (0 : ℂ) 1 \ {0}) ∧
    MeromorphicAt (fun ζ => (e ζ).2.2) 0 ∧
    ∀ n : ℤ, MeromorphicAt (fun ζ => ((e ζ).1 n).1) 0 ∧ MeromorphicAt (fun ζ => ((e ζ).1 n).2) 0

/-- `S ⊆ H0` is compact modulo finitely many punctures over every compact subset of `ℂ*`
(Rychlik Thm 8(2): `M/⟨σ⟩` compact once the branch points are adjoined). -/
def CompactModPunctures (a : ℝ) (h : ℂ → ℂ) (S : Set ChainData) : Prop :=
  ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
    ∃ C : Set ChainData, IsCompact C ∧ C ⊆ H0 a h ∧
      ∃ (m : ℕ) (e : Fin m → ℂ → ChainData) (u₀ : Fin m → ℂ) (k : Fin m → ℕ),
        (∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i)) ∧
        S ∩ {q | q.2.1 ∈ K} ⊆ C ∪ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})

end Work.EQ
