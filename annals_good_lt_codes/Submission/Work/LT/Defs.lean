import ChallengeDeps
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Shared definitions for the good-LTC route (orchestrator design: Submission/Work/LT/DESIGN.md). -/

namespace Work.LT

open GoodLTC NNReal

/-- Tensor code `C_A ⊗ C_B` inside `𝔽₂^{Δ×Δ}`: row `i` (fixed first index) lies in `CB`,
column `j` (fixed second index) lies in `CA`. -/
def tensorCode {Δ : ℕ} (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) :
    Submodule (ZMod 2) (Fin Δ × Fin Δ → ZMod 2) :=
  (⨅ i : Fin Δ, CB.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun j : Fin Δ => (i, j)))) ⊓
    (⨅ j : Fin Δ, CA.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin Δ => (i, j))))

/-- DELLM Definition 2.8 (agreement testability), in counting form: for `w1` with all rows in
`CB` and `w2` with all columns in `CA` there is `w ∈ CA ⊗ CB` with
`κ0 · Δ · (#rows where w1 ≠ w + #columns where w2 ≠ w) ≤ #{(i,j) | w1 (i,j) ≠ w2 (i,j)}`. -/
def agreementTestable {Δ : ℕ} (κ0 : ℝ) (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) : Prop :=
  ∀ w1 w2 : Fin Δ × Fin Δ → ZMod 2,
    (∀ i, (fun j => w1 (i, j)) ∈ CB) → (∀ j, (fun i => w2 (i, j)) ∈ CA) →
    ∃ w ∈ tensorCode CA CB,
      κ0 * Δ * (((Finset.univ.filter (fun i => ∃ j, w1 (i, j) ≠ w (i, j))).card : ℝ) +
          (Finset.univ.filter (fun j => ∃ i, w2 (i, j) ≠ w (i, j))).card) ≤
        (Finset.univ.filter (fun p => w1 p ≠ w2 p)).card

/-- Normalised one-sided-free spectral bound for the left walk `x ↦ (g ↦ avg_i x (A i * g))`:
on mean-zero `x` its `ℓ²` norm contracts by `μ`. -/
def leftExpander {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G) (μ : ℝ) : Prop :=
  ∀ x : G → ℝ, ∑ g, x g = 0 →
    ∑ g, ((∑ i, x (A i * g)) / Δ) ^ 2 ≤ μ ^ 2 * ∑ g, x g ^ 2

/-- Same for the right walk `x ↦ (g ↦ avg_j x (g * B j))`. -/
def rightExpander {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (μ : ℝ) : Prop :=
  ∀ x : G → ℝ, ∑ g, x g = 0 →
    ∑ g, ((∑ j, x (g * B j)) / Δ) ^ 2 ≤ μ ^ 2 * ∑ g, x g ^ 2

/-- Quadripartite left-right Cayley complex. Squares are `G × Fin Δ × Fin Δ`; the square
`(x, i, j)` has vertices `x` (type 00), `A i * x` (type 10), `x * B j` (type 01),
`A i * x * B j` (type 11), and is seen from each of them with local coordinates `(i, j)`.
`lrSq A B α β g i j` is the square whose type-`(α,β)` vertex is `g`, with coordinates `(i,j)`. -/
def lrSq {G : Type*} [Group G] {Δ : ℕ} (A B : Fin Δ → G) (α β : Fin 2) (g : G) (i j : Fin Δ) :
    G × Fin Δ × Fin Δ :=
  ((if α = 1 then (A i)⁻¹ else 1) * g * (if β = 1 then (B j)⁻¹ else 1), i, j)

/-- The local view of a word `f` at the type-`(α,β)` vertex `g`, as a linear map. -/
def lrView {G : Type*} [Group G] {Δ : ℕ} (A B : Fin Δ → G) (α β : Fin 2) (g : G) :
    (G × Fin Δ × Fin Δ → ZMod 2) →ₗ[ZMod 2] (Fin Δ × Fin Δ → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (fun ij : Fin Δ × Fin Δ => lrSq A B α β g ij.1 ij.2)

/-- The DELLM code on the quadripartite left-right Cayley complex: every local view at every
vertex (all four types) lies in `CA ⊗ CB`. Length `|G| Δ²`. -/
def lrCode {G : Type*} [Group G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) :
    Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2) :=
  ⨅ (α : Fin 2) (β : Fin 2) (g : G), (tensorCode CA CB).comap (lrView A B α β g)

/-- A-edge `(β, g, i)` joins the type-`(0,β)` vertex `g` and the type-`(1,β)` vertex `A i * g`;
it is in dispute for the local-view assignment `W` iff the two views differ on row `i`. -/
def disputeA {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (β : Fin 2) (g : G) (i : Fin Δ) : Prop :=
  ∃ j, W 0 β g (i, j) ≠ W 1 β (A i * g) (i, j)

/-- B-edge `(α, g, j)` joins the type-`(α,0)` vertex `g` and the type-`(α,1)` vertex `g * B j`;
in dispute iff the two views differ on column `j`. -/
def disputeB {G : Type*} [Group G] {Δ : ℕ} (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (α : Fin 2) (g : G) (j : Fin Δ) : Prop :=
  ∃ i, W α 0 g (i, j) ≠ W α 1 (g * B j) (i, j)

open Classical in
/-- Number of disputed edges (A-edges plus B-edges; there are `4 |G| Δ` edges in total). -/
noncomputable def dispCount {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : ℕ :=
  (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ => disputeA A W p.1 p.2.1 p.2.2)).card +
    (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ => disputeB B W p.1 p.2.1 p.2.2)).card

open Classical in
/-- `W` is a local minimum of `dispCount`: replacing one view by any tensor codeword does not
decrease the number of disputed edges (the end state of DELLM Algorithm 1). -/
def IsLocalOpt {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2))
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : Prop :=
  ∀ (α β : Fin 2) (g : G), ∀ w ∈ tensorCode CA CB,
    dispCount A B W ≤
      dispCount A B (fun α' β' g' => if α' = α ∧ β' = β ∧ g' = g then w else W α' β' g')

/-- Transport a code on a finite coordinate type `X` to `Fin n` along `e : X ≃ Fin n`. -/
def transportCode {X : Type*} {n : ℕ} (e : X ≃ Fin n) (C : Submodule (ZMod 2) (X → ZMod 2)) :
    BinaryCode n :=
  C.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) e)

/-- Elementary matrix `E_ij(t) = 1 + t e_ij` in `SL₃(ℤ/p)` (the identity when `i = j`). -/
def sl3E (p : ℕ) (i j : Fin 3) (t : ZMod p) : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) :=
  if h : i = j then 1 else ⟨Matrix.transvection i j t, Matrix.det_transvection_of_ne i j h t⟩

/-- The six off-diagonal positions. -/
def offDiag : Fin 6 → Fin 3 × Fin 3 := ![(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)]

/-- The 12 generators `E_ij(±1)`, `i ≠ j`, of `SL₃(ℤ/p)`. -/
def sl3Gen (p : ℕ) (k : Fin 6 × Bool) : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) :=
  sl3E p (offDiag k.1).1 (offDiag k.1).2 (if k.2 then 1 else -1)

end Work.LT
