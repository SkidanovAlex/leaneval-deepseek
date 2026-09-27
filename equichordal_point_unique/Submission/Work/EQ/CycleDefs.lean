import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra

/-! # Definitions for the minimal regular cycle (Rychlik Theorem 8)

Support definitions for `Submission.Work.EQ.exists_compact_regular_cycle`.

* `Ann r₁ r₂` is the closed annulus `{z : r₁ ≤ ‖z‖ ≤ r₂}` on which chains are read.
* `bwdP a s P` is the `j`-th backward image of the point `P` along the sign list `s` (the
  inverse branch `invBranch a sⱼ` applied in order), i.e. the point at index `-j` of a chain whose
  index-`0` point is `P`.
* `RegValues a h` is the set of values of the invariant parameter `ψ = ψ₁ψ₂` on *regular*
  components of `H0` (Rychlik's `Σ`), `rhoStar a h` its infimum of moduli (Rychlik's `ρ*`), and
  `CharSet a h` the set `M ∪ {1}` of characteristic values of returning fan words (Rychlik
  Remark 3, `μ_max`).
* `candChain` is the explicit candidate chain attached to two fan ends, a sign list and a value:
  the object whose "good" parameters are exactly the chains of `H0` read over the annulus.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

open scoped Topology

noncomputable section

/-- The closed annulus `{z : r₁ ≤ ‖z‖ ≤ r₂}`. -/
def Ann (r₁ r₂ : ℝ) : Set ℂ := {z | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂}

/-- **The backward image along a sign list.** `bwdP a [σ₁,…,σ_m] P` is
`invBranch a σ_m (… (invBranch a σ₁ P))`, the point `m` steps backward (i.e. at index `-m`) of a
chain whose index-`0` point is `P`. -/
def bwdP (a : ℝ) (s : List Bool) (P : ℂ × ℂ) : ℂ × ℂ :=
  s.foldl (fun Q t => invBranch a t Q) P

@[simp] theorem bwdP_nil (a : ℝ) (P : ℂ × ℂ) : bwdP a [] P = P := rfl

theorem bwdP_cons (a : ℝ) (s : Bool) (l : List Bool) (P : ℂ × ℂ) :
    bwdP a (s :: l) P = bwdP a l (invBranch a s P) := rfl

theorem bwdP_append (a : ℝ) (l₁ l₂ : List Bool) (P : ℂ × ℂ) :
    bwdP a (l₁ ++ l₂) P = bwdP a l₂ (bwdP a l₁ P) := by
  simp [bwdP, List.foldl_append]

theorem bwdP_snoc (a : ℝ) (s : List Bool) (t : Bool) (P : ℂ × ℂ) :
    bwdP a (s ++ [t]) P = invBranch a t (bwdP a s P) := by
  rw [bwdP_append, bwdP_cons, bwdP_nil]

/-- **Backward pairs.** Consecutive backward images along a sign list satisfy the equichordal
relation, provided the backward step at the second point is nondegenerate. -/
theorem eqRelC_bwdP_step {a : ℝ} {s : List Bool} {t : Bool} {P : ℂ × ℂ}
    (h : ((bwdP a s P).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (bwdP a s P).2 ^ 2 ≠ 0) :
    EqRelC a (bwdP a (s ++ [t]) P) (bwdP a s P) := by
  rw [bwdP_snoc]
  exact eqRelC_invBranch t (by simpa [subO1, bsq, sq] using h)

/-- **The set of values of the invariant parameter on regular components of `H0`**
(Rychlik's `Σ`). -/
def RegValues (a : ℝ) (h : ℂ → ℂ) : Set ℂ :=
  {c | ∃ p ∈ H0 a h, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c}

/-- **Rychlik's `ρ*`**: the infimum of `|c|` over regular components. -/
def rhoStar (a : ℝ) (h : ℂ → ℂ) : ℝ := sInf {x : ℝ | ∃ c, c ∈ RegValues a h ∧ x = ‖c‖}

/-- **Rychlik's `M ∪ {1}`**: the set of characteristic values of fan words returning to `A₁`,
together with `1`. -/
def CharSet (a : ℝ) (h : ℂ → ℂ) : Set ℂ :=
  {1} ∪ {μ : ℂ | ∃ ε : List Bool, fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
    μ = charVal a h ε}

/-- The centre of a fan word: the `x`-coordinate (real) at which `fan a h ε` is centred. -/
def fanCentre (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) : ℂ := (fan a h ε 0).1

/-- **The candidate chain.** `candChain a h ε η s N c z` has `ψ₁ = z`, `ψ₂ = c/z`; its index-`0`
point is `fan ε z`; forward of index `0` it follows the fan of `ε` (`germC` beyond length `N`);
the `N` steps from index `-N` to `0` are the backward images along the sign list `s`; and at
indices `≤ -N` it follows the mirror of the fan of `η` with parameter `λ^N (c/z)`. -/
def candChain (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (c z : ℂ) : ChainData :=
  (fun j : ℤ =>
    if 0 ≤ j then
      (if (j.toNat ≤ N) then fan a h (ε.drop j.toNat) (((eqLam a : ℝ) : ℂ) ^ j * z)
       else germC a h (((eqLam a : ℝ) : ℂ) ^ j * z))
    else
      (if (-j).toNat ≤ N then bwdP a (s.take (-j).toNat) (fan a h ε z)
       else eqMirror (fan a h (η.drop ((-j).toNat - N))
              (((eqLam a : ℝ) : ℂ) ^ ((-j).toNat : ℤ) * (c / z)))), z, c / z)

@[simp] theorem candChain_psi1 (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (c z : ℂ) :
    (candChain a h ε η s N c z).2.1 = z := rfl

@[simp] theorem candChain_psi2 (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (c z : ℂ) :
    (candChain a h ε η s N c z).2.2 = c / z := rfl

end

end Work.EQ
namespace Work.EQ
open Complex Filter _root_.Topology
noncomputable section

/-- **A regular component of `⁰H` with its value.** `S` is a connected component of `H0 a h` on
which the invariant parameter `ψ = ψ₁ψ₂` is constantly `c`. -/
def IsRegComp (a : ℝ) (h : ℂ → ℂ) (S : Set ChainData) (c : ℂ) : Prop :=
  S ⊆ H0 a h ∧ (∃ p ∈ H0 a h, S = connectedComponentIn (H0 a h) p) ∧
    ∀ q ∈ S, q.2.1 * q.2.2 = c

/-- **The set of word pairs occurring over an annulus** for a set `S` of chains: the pairs
`(ε, η)` of words of length `N` such that some chain `q ∈ S` with `ψ₁ q ∈ Ann r₁ r₂` has stable
word `ε` and unstable word `η` at depth `N`, i.e. `q 0 = fan ε (ψ₁ q)` and
`q(-N) = mirror (fan η (λ^N ψ₂ q))`.  For a chain whose tails are the germs at depth `N` this
pair is unique (the branch of each backward step is determined by the point). -/
def WordSet (a : ℝ) (h : ℂ → ℂ) (S : Set ChainData) (r₁ r₂ : ℝ) (N : ℕ) :
    Set (List Bool × List Bool) :=
  {e | e.1.length = N ∧ e.2.length = N ∧
    ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂ ∧ q.1 0 = fan a h e.1 q.2.1 ∧
      q.1 (-(N : ℤ)) = eqMirror (fan a h e.2 (((eqLam a : ℝ) : ℂ) ^ N * q.2.2))}

end
end Work.EQ
