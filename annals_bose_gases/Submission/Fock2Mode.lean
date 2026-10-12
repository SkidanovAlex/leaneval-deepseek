import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Real.Sqrt
import ChallengeDeps
import Submission.Bog2Mode
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5/6 — the two-mode bosonic Fock ground estimate (FS eq:BogIdentity, κ = 0)

Carrier: two-mode Fock space in the number basis, represented by functions
`φ : ℕ × ℕ → ℝ` with finite support in `[0,M]×[0,M]` (`vanishOn M φ`).  All
quadratic forms are finite double sums over the rectangle `[0, M+1]²`; the
`+1` head-room guarantees that the shifted arguments (creation/annihilation
move one index by ±1) stay inside the summation rectangle, while `vanishOn`
kills the boundary terms so every finite sum equals the corresponding infinite
ℓ² value.

Operators (mode 1 = first coordinate `p.1`, mode 2 = second coordinate `p.2`):
    (aUp φ)(m,n)    = √(m+1)·φ(m+1,n)     -- annihilation of mode 1
    (aUpDag φ)(m,n) = √m·φ(m-1,n)          -- creation of mode 1 (Nat sub)
    (aLo φ)(m,n)    = √(n+1)·φ(m,n+1)      -- annihilation of mode 2
    (aLoDag φ)(m,n) = √n·φ(m,n-1)          -- creation of mode 2
so `aUpDag ∘ aUp = N₁` (number of mode 1), `[aUp, aUpDag] = 1` elementwise, etc.
The pair Hamiltonian (relative to the condensate, per mode pair (k,-k) of the
box Bogoliubov Hamiltonian K^Bog of FS final_v2.tex thm:BogHamDiag) is
    H = A(N₁+N₂) + B(aUpDag·aLoDag + aUp·aLo),
whose quadratic form is `fsQuad A B M φ` (diagonal `A(m+n)`; pair term
`2B√((m+1)(n+1))·φ(m,n)·φ(m+1,n+1)`).

THEOREM (FS eq:BogIdentity with κ = 0; numerically verified):
with `s := bogS A B`, `D := bogD A B`, `α := bogAlpha A B`,
    ⟨φ,Hφ⟩ = D·(‖b₊φ‖² + ‖b₋φ‖²) − (A−s)·‖φ‖²
for `b₊ := aUp + α·aLoDag`, `b₋ := aLo + α·aUpDag`.
Corollary (eq:BogIneq, κ = 0):  ⟨φ,Hφ⟩ ≥ −(A−s)·‖φ‖².

Proof route for the child (fock_two_mode_identity):
1. Expand `rectNorm M (bPlus α φ)` by squaring the pointwise value
   `√(m+1)φ(m+1,n) + α√n·φ(m,n-1)`; do the same for `bMinus`.  Obtain
   BP = ΣΣ[(m+1)φ(m+1,n)² + α²·n·φ(m,n-1)² + 2α√((m+1)n)φ(m+1,n)φ(m,n-1)]
   and the mirror BM (roles of the two coordinates exchanged).
2. Change summation variables inside the rectangle `range (M+2)` (injective
   maps `m ↦ m+1`, `n ↦ n+1`, with `vanishOn` killing the boundary images at
   `M+1` and `M+2`).  Obtain
       ΣΣ(m+1)φ(m+1,n)² = ΣΣ m·φ(m,n)²
       ΣΣ n·φ(m,n-1)²   = ΣΣ (n+1)·φ(m,n)²     (shift n ↦ n-1)
   and the crossed two-coordinate identities
       Σ√((m+1)n)φ(m+1,n)φ(m,n-1) = S  and  its mirror = S,
   where S := ΣΣ√((m+1)(n+1))φ(m,n)φ(m+1,n+1)   (this is the lattice form of
   ⟨φ,aUpDag·aLoDag φ⟩ = ⟨φ,aUp·aLo φ⟩; both equal S by a reindexing).
3. Conclude BP + BM = (1+α²)·ΣΣ(m+n)φ(m,n)² + 2α²·ΣΣφ(m,n)² + 4α·S, so
   D·(BP+BM) = D(1+α²)·ΣΣ(m+n)φ² + 2Dα²·ΣΣφ² + 4Dα·S
   and apply the Bog2Mode coefficient identities
       bog_D_mul_one_add_alpha_sq : D(1+α²) = A,
       bog_alpha_mul_D           : 2Dα = B  (i.e. Dα = B/2),
       bog_A_sub_s_eq            : 2Dα² = A − s  (i.e. B²/(A+s) = A−s),
   which yields exactly `fsQuad A B M φ + (A − s)·rectNorm M φ`.
Use `Finset.sum_bij`/`sum_range` reindexing lemmas, `ring`, `nlinarith`,
`positivity`, and `simp [Real.mul_self_sqrt]`.  All sums are over the Finset
`range (M+2)` in each coordinate (the `M+2` makes room for one shift).
-/

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
namespace BoseGases

open scoped BigOperators

/-- A vector `φ : ℕ × ℕ → ℝ` (two-mode Fock wavefunction in the number basis) with
    finite support inside `[0,M] × [0,M]`. -/
def vanishOn (M : ℕ) (φ : ℕ × ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, M < m ∨ M < n → φ (m, n) = 0

/-- Squared norm ‖ψ‖² computed over the rectangle `[0, M+1]²` (equals the full ℓ² sum
    whenever `ψ` is a finite linear combination of the `vanishOn` type with this `M`). -/
noncomputable def rectNorm (M : ℕ) (ψ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2), (ψ (m, n)) ^ 2

/-- Annihilation operator of mode 1 (first coordinate): `(aUp φ)(m,n) = √(m+1)·φ(m+1,n)`. -/
noncomputable def aUp (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  Real.sqrt (((p.1 + 1 : ℕ) : ℝ)) * φ (p.1 + 1, p.2)

/-- Creation operator of mode 1: `(aUpDag φ)(m,n) = √m·φ(m−1,n)` (0 for `m = 0` by `Nat` sub). -/
noncomputable def aUpDag (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  Real.sqrt (((p.1 : ℕ) : ℝ)) * φ (p.1 - 1, p.2)

/-- Annihilation operator of mode 2 (second coordinate): `(aLo φ)(m,n) = √(n+1)·φ(m,n+1)`. -/
noncomputable def aLo (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  Real.sqrt (((p.2 + 1 : ℕ) : ℝ)) * φ (p.1, p.2 + 1)

/-- Creation operator of mode 2: `(aLoDag φ)(m,n) = √n·φ(m,n−1)`. -/
noncomputable def aLoDag (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  Real.sqrt (((p.2 : ℕ) : ℝ)) * φ (p.1, p.2 - 1)

/-- Quadratic form `⟨φ,Hφ⟩` of the pair Hamiltonian
    `H = A(N₁+N₂) + B(aUpDag·aLoDag + aUp·aLo)`, as a finite double sum over `[0,M+1]²`. -/
noncomputable def fsQuad (A B : ℝ) (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    (A * (((m : ℕ) : ℝ) + ((n : ℕ) : ℝ)) * (φ (m, n)) ^ 2 +
      2 * B * Real.sqrt ((((m + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ))) * φ (m, n) * φ (m + 1, n + 1))

/-- `b₊ := aUp + α·aLoDag`, the squeezing combination whose norm-square carries the
    positive part of the Bogoliubov form. -/
noncomputable def bPlus (α : ℝ) (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  Real.sqrt (((p.1 + 1 : ℕ) : ℝ)) * φ (p.1 + 1, p.2) +
    α * Real.sqrt (((p.2 : ℕ) : ℝ)) * φ (p.1, p.2 - 1)

/-- `b₋ := aLo + α·aUpDag`. -/
noncomputable def bMinus (α : ℝ) (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  Real.sqrt (((p.2 + 1 : ℕ) : ℝ)) * φ (p.1, p.2 + 1) +
    α * Real.sqrt (((p.1 : ℕ) : ℝ)) * φ (p.1 - 1, p.2)

/-- `‖ψ‖²` (rectangular truncation) is a sum of squares, hence nonnegative. -/
lemma rectNorm_nonneg (M : ℕ) (ψ : ℕ × ℕ → ℝ) : 0 ≤ rectNorm M ψ := by
  unfold rectNorm
  refine Finset.sum_nonneg ?_
  intro m hm
  refine Finset.sum_nonneg ?_
  intro n hn
  exact sq_nonneg (ψ (m, n))

/-- `aUpDag ∘ aUp = N₁` (number of quanta in mode 1), elementwise. -/
lemma fock_aUpDag_aUp (φ : ℕ × ℕ → ℝ) :
    aUpDag (aUp φ) = fun p => ((p.1 : ℕ) : ℝ) * φ p := by
  funext p
  rcases p with ⟨m, n⟩
  cases m with
  | zero => simp [aUpDag, aUp]
  | succ m =>
      have h : Nat.succ m - 1 + 1 = Nat.succ m := by omega
      calc
        aUpDag (aUp φ) (Nat.succ m, n)
            = Real.sqrt (↑(Nat.succ m) : ℝ) *
                (Real.sqrt (↑(Nat.succ m - 1 + 1) : ℝ) * φ (Nat.succ m - 1 + 1, n)) := by
                simp [aUpDag, aUp]
        _ = Real.sqrt (↑(Nat.succ m) : ℝ) *
                (Real.sqrt (↑(Nat.succ m) : ℝ) * φ (Nat.succ m, n)) := by
                rw [h]
        _ = (Real.sqrt (↑(Nat.succ m) : ℝ) * Real.sqrt (↑(Nat.succ m) : ℝ)) * φ (Nat.succ m, n) := by
                rw [mul_assoc]
        _ = (↑(Nat.succ m) : ℝ) * φ (Nat.succ m, n) := by
                rw [Real.mul_self_sqrt (by positivity : 0 ≤ (↑(Nat.succ m) : ℝ))]
        _ = ((Nat.succ m : ℕ) : ℝ) * φ (Nat.succ m, n) := rfl

/-- `aLoDag ∘ aLo = N₂` (number of quanta in mode 2), elementwise. -/
lemma fock_aLoDag_aLo (φ : ℕ × ℕ → ℝ) :
    aLoDag (aLo φ) = fun p => ((p.2 : ℕ) : ℝ) * φ p := by
  funext p
  rcases p with ⟨m, n⟩
  cases n with
  | zero => simp [aLoDag, aLo]
  | succ n =>
      have h : Nat.succ n - 1 + 1 = Nat.succ n := by omega
      calc
        aLoDag (aLo φ) (m, Nat.succ n)
            = Real.sqrt (↑(Nat.succ n) : ℝ) *
                (Real.sqrt (↑(Nat.succ n - 1 + 1) : ℝ) * φ (m, Nat.succ n - 1 + 1)) := by
                simp [aLoDag, aLo]
        _ = Real.sqrt (↑(Nat.succ n) : ℝ) *
                (Real.sqrt (↑(Nat.succ n) : ℝ) * φ (m, Nat.succ n)) := by
                rw [h]
        _ = (Real.sqrt (↑(Nat.succ n) : ℝ) * Real.sqrt (↑(Nat.succ n) : ℝ)) * φ (m, Nat.succ n) := by
                rw [mul_assoc]
        _ = (↑(Nat.succ n) : ℝ) * φ (m, Nat.succ n) := by
                rw [Real.mul_self_sqrt (by positivity : 0 ≤ (↑(Nat.succ n) : ℝ))]
        _ = ((Nat.succ n : ℕ) : ℝ) * φ (m, Nat.succ n) := rfl

/-- Canonical commutation relation of mode 1: `[aUp, aUpDag] = 1`, elementwise. -/
lemma fock_ccr_aUp (φ : ℕ × ℕ → ℝ) :
    aUp (aUpDag φ) = fun p => (((p.1 : ℕ) : ℝ) + 1) * φ p := by
  funext p
  rcases p with ⟨m, n⟩
  calc
    aUp (aUpDag φ) (m, n)
        = Real.sqrt (↑(m + 1) : ℝ) * (Real.sqrt (↑(m + 1) : ℝ) * φ (m, n)) := by
          simp [aUp, aUpDag]
    _ = (Real.sqrt (↑(m + 1) : ℝ) * Real.sqrt (↑(m + 1) : ℝ)) * φ (m, n) := by
          rw [mul_assoc]
    _ = (↑(m + 1) : ℝ) * φ (m, n) := by
          rw [Real.mul_self_sqrt (by positivity : 0 ≤ (↑(m + 1) : ℝ))]
    _ = (↑m + 1) * φ (m, n) := by norm_num

/-- Canonical commutation relation of mode 2: `[aLo, aLoDag] = 1`, elementwise. -/
lemma fock_ccr_aLo (φ : ℕ × ℕ → ℝ) :
    aLo (aLoDag φ) = fun p => (((p.2 : ℕ) : ℝ) + 1) * φ p := by
  funext p
  rcases p with ⟨m, n⟩
  calc
    aLo (aLoDag φ) (m, n)
        = Real.sqrt (↑(n + 1) : ℝ) * (Real.sqrt (↑(n + 1) : ℝ) * φ (m, n)) := by
          simp [aLo, aLoDag]
    _ = (Real.sqrt (↑(n + 1) : ℝ) * Real.sqrt (↑(n + 1) : ℝ)) * φ (m, n) := by
          rw [mul_assoc]
    _ = (↑(n + 1) : ℝ) * φ (m, n) := by
          rw [Real.mul_self_sqrt (by positivity : 0 ≤ (↑(n + 1) : ℝ))]
    _ = (↑n + 1) * φ (m, n) := by norm_num

/-- The two modes commute: `[aLo, aUp] = 0`, elementwise. -/
lemma fock_comm_aUp_aLo (φ : ℕ × ℕ → ℝ) : aLo (aUp φ) = aUp (aLo φ) := by
  funext p
  rcases p with ⟨m, n⟩
  simp [aUp, aLo, mul_left_comm, mul_assoc, mul_comm]

/-- `[aLoDag, aUp] = 0`, elementwise. -/
lemma fock_comm_aUp_aLoDag (φ : ℕ × ℕ → ℝ) : aLoDag (aUp φ) = aUp (aLoDag φ) := by
  funext p
  rcases p with ⟨m, n⟩
  simp [aUp, aLoDag, mul_left_comm, mul_assoc, mul_comm]

/-- `[aLoDag, aUpDag] = 0`, elementwise. -/
lemma fock_comm_aUpDag_aLoDag (φ : ℕ × ℕ → ℝ) : aLoDag (aUpDag φ) = aUpDag (aLoDag φ) := by
  funext p
  rcases p with ⟨m, n⟩
  simp [aLoDag, aUpDag, mul_left_comm, mul_assoc, mul_comm]


/-- one-dimensional reindexing: sum w(m+1) g(m+1) = sum w(m) g(m), weight w with w 0 = 0,
    g supported in [0, M]. -/
lemma sum_shiftUp_gen (M : ℕ) (w : ℕ → ℝ) {g : ℕ → ℝ}
    (hw0 : w 0 = 0) (hg : ∀ m, M < m → g m = 0) :
    (∑ m ∈ Finset.range (M + 2), w (m + 1) * g (m + 1)) =
    (∑ m ∈ Finset.range (M + 2), w m * g m) := by
  have h1 : (∑ m ∈ Finset.range (M + 2), w (m + 1) * g (m + 1))
      = (∑ j ∈ (Finset.range (M + 3)).erase 0, w j * g j) := by
    refine Finset.sum_bij (fun m _ => m + 1) ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_erase]
      constructor
      · omega
      · rw [Finset.mem_range]
        have hml : m < M + 2 := Finset.mem_range.mp hm
        omega
    · intro a ha b hb h
      omega
    · intro j hj
      have hj1 : j ≠ 0 := (Finset.mem_erase.mp hj).1
      have hjl : j < M + 3 := Finset.mem_range.mp ((Finset.mem_erase.mp hj).2)
      refine ⟨j - 1, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · omega
    · intro a ha
      rfl
  have h2 : (∑ j ∈ (Finset.range (M + 3)).erase 0, w j * g j)
      = (∑ j ∈ Finset.range (M + 3), w j * g j) := by
    have hmem : (0 : ℕ) ∈ Finset.range (M + 3) := by simp
    calc
      (∑ j ∈ (Finset.range (M + 3)).erase 0, w j * g j)
          = (∑ j ∈ (Finset.range (M + 3)).erase 0, w j * g j) + w 0 * g 0 := by
            simp [hw0]
      _ = ∑ j ∈ Finset.range (M + 3), w j * g j := by
          rw [Finset.sum_erase_add _ _ hmem]
  have hgbig : w (M + 2) * g (M + 2) = 0 := by
    have : g (M + 2) = 0 := hg (M + 2) (by omega)
    simp [this]
  calc
    (∑ m ∈ Finset.range (M + 2), w (m + 1) * g (m + 1))
        = ∑ j ∈ Finset.range (M + 3), w j * g j := by rw [h1, h2]
    _ = (∑ j ∈ Finset.range (M + 2), w j * g j) + w (M + 2) * g (M + 2) := by
        rw [Finset.sum_range_succ]
    _ = ∑ m ∈ Finset.range (M + 2), w m * g m := by rw [hgbig]; simp

/-- one-dimensional reindexing (down): sum w(n) g(n−1) = sum w(n+1) g(n), Nat subtraction. -/
lemma sum_shiftDown_gen (M : ℕ) (w : ℕ → ℝ) {g : ℕ → ℝ}
    (hw0 : w 0 = 0) (hg : ∀ m, M < m → g m = 0) :
    (∑ n ∈ Finset.range (M + 2), w n * g (n - 1)) =
    (∑ n ∈ Finset.range (M + 2), w (n + 1) * g n) := by
  have h0 : w 0 * g (0 - 1) = 0 := by simp [hw0]
  have heq : (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g (n - 1)) + w 0 * g (0 - 1)
      = ∑ n ∈ Finset.range (M + 2), w n * g (n - 1) := by
    exact Finset.sum_erase_add (Finset.range (M + 2)) (fun n => w n * g (n - 1)) (by simp)
  have h1 : (∑ n ∈ Finset.range (M + 2), w n * g (n - 1))
      = (∑ j ∈ Finset.range (M + 1), w (j + 1) * g j) := by
    calc
      (∑ n ∈ Finset.range (M + 2), w n * g (n - 1))
          = (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g (n - 1)) := by
              have hs : (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g (n - 1))
                  = ∑ n ∈ Finset.range (M + 2), w n * g (n - 1) := by
                calc
                  (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g (n - 1))
                      = (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g (n - 1)) + w 0 * g (0 - 1) := by
                          rw [h0]; simp
                  _ = ∑ n ∈ Finset.range (M + 2), w n * g (n - 1) := heq
              exact hs.symm
      _ = ∑ j ∈ Finset.range (M + 1), w (j + 1) * g j := by
          refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
          · intro n hn
            rw [Finset.mem_range]
            have hn0 : n ≠ 0 := (Finset.mem_erase.mp hn).1
            have hnl : n < M + 2 := Finset.mem_range.mp ((Finset.mem_erase.mp hn).2)
            omega
          · intro a ha b hb h
            have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
            have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
            omega
          · intro j hj
            have hjl : j < M + 1 := Finset.mem_range.mp hj
            refine ⟨j + 1, ?_, ?_⟩
            · rw [Finset.mem_erase]
              constructor
              · omega
              · rw [Finset.mem_range]
                omega
            · omega
          · intro n hn
            have hn0 : n ≠ 0 := (Finset.mem_erase.mp hn).1
            have hn1 : n - 1 + 1 = n := by omega
            rw [hn1]
  have hgM1 : g (M + 1) = 0 := hg (M + 1) (by omega)
  have h2 : (∑ j ∈ Finset.range (M + 1), w (j + 1) * g j)
      = (∑ n ∈ Finset.range (M + 2), w (n + 1) * g n) := by
    symm
    calc
      (∑ n ∈ Finset.range (M + 2), w (n + 1) * g n)
          = (∑ n ∈ Finset.range (M + 1), w (n + 1) * g n) + w (M + 2) * g (M + 1) := by
              rw [Finset.sum_range_succ]
      _ = ∑ j ∈ Finset.range (M + 1), w (j + 1) * g j := by simp [hgM1]
  exact h1.trans h2

/-- one-dimensional two-function reindexing for cross terms: sum w(n) g1(n) g2(n−1)
    = sum w(n+1) g1(n+1) g2(n). -/
lemma sum_crossDown_gen (M : ℕ) (w g1 g2 : ℕ → ℝ)
    (hw0 : w 0 = 0) (hg2 : ∀ m, M < m → g2 m = 0) :
    (∑ n ∈ Finset.range (M + 2), w n * g1 n * g2 (n - 1)) =
    (∑ n ∈ Finset.range (M + 2), w (n + 1) * g1 (n + 1) * g2 n) := by
  have h0 : w 0 * g1 0 * g2 (0 - 1) = 0 := by simp [hw0]
  have heq : (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g1 n * g2 (n - 1)) + w 0 * g1 0 * g2 (0 - 1)
      = ∑ n ∈ Finset.range (M + 2), w n * g1 n * g2 (n - 1) := by
    exact Finset.sum_erase_add (Finset.range (M + 2)) (fun n => w n * g1 n * g2 (n - 1)) (by simp)
  have h1 : (∑ n ∈ Finset.range (M + 2), w n * g1 n * g2 (n - 1))
      = (∑ j ∈ Finset.range (M + 1), w (j + 1) * g1 (j + 1) * g2 j) := by
    calc
      (∑ n ∈ Finset.range (M + 2), w n * g1 n * g2 (n - 1))
          = (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g1 n * g2 (n - 1)) := by
              have hs : (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g1 n * g2 (n - 1))
                  = ∑ n ∈ Finset.range (M + 2), w n * g1 n * g2 (n - 1) := by
                calc
                  (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g1 n * g2 (n - 1))
                      = (∑ n ∈ (Finset.range (M + 2)).erase 0, w n * g1 n * g2 (n - 1)) + w 0 * g1 0 * g2 (0 - 1) := by
                          rw [h0]; simp
                  _ = ∑ n ∈ Finset.range (M + 2), w n * g1 n * g2 (n - 1) := heq
              exact hs.symm
      _ = ∑ j ∈ Finset.range (M + 1), w (j + 1) * g1 (j + 1) * g2 j := by
          refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
          · intro n hn
            rw [Finset.mem_range]
            have hn0 : n ≠ 0 := (Finset.mem_erase.mp hn).1
            have hnl : n < M + 2 := Finset.mem_range.mp ((Finset.mem_erase.mp hn).2)
            omega
          · intro a ha b hb h
            have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
            have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
            omega
          · intro j hj
            have hjl : j < M + 1 := Finset.mem_range.mp hj
            refine ⟨j + 1, ?_, ?_⟩
            · rw [Finset.mem_erase]
              constructor
              · omega
              · rw [Finset.mem_range]
                omega
            · omega
          · intro n hn
            have hn0 : n ≠ 0 := (Finset.mem_erase.mp hn).1
            have hn1 : n - 1 + 1 = n := by omega
            rw [hn1]
  have hgM1 : g2 (M + 1) = 0 := hg2 (M + 1) (by omega)
  have h2 : (∑ j ∈ Finset.range (M + 1), w (j + 1) * g1 (j + 1) * g2 j)
      = (∑ n ∈ Finset.range (M + 2), w (n + 1) * g1 (n + 1) * g2 n) := by
    symm
    calc
      (∑ n ∈ Finset.range (M + 2), w (n + 1) * g1 (n + 1) * g2 n)
          = (∑ n ∈ Finset.range (M + 1), w (n + 1) * g1 (n + 1) * g2 n) + w (M + 2) * g1 (M + 2) * g2 (M + 1) := by
              rw [Finset.sum_range_succ]
      _ = ∑ j ∈ Finset.range (M + 1), w (j + 1) * g1 (j + 1) * g2 j := by simp [hgM1]
  exact h1.trans h2

/-- support of φ in coordinate 1, from vanishOn -/
lemma vanishOn_coord1 {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    ∀ m n, M < m → φ (m, n) = 0 := by
  intro m n hm
  exact hφ m n (Or.inl hm)

/-- support of φ in coordinate 2, from vanishOn -/
lemma vanishOn_coord2 {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    ∀ m n, M < n → φ (m, n) = 0 := by
  intro m n hn
  exact hφ m n (Or.inr hn)

-- double-sum lemmas: weight w; coordinate 1 up-shift
lemma dsum_c1_up (M : ℕ) (w : ℕ → ℝ) {φ : ℕ × ℕ → ℝ}
    (hw0 : w 0 = 0) (hφ1 : ∀ m n, M < m → φ (m, n) = 0) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w (m + 1) * (φ (m + 1, n)) ^ 2) =
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w m * (φ (m, n)) ^ 2) := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  exact sum_shiftUp_gen M w (g := fun m => (φ (m, v)) ^ 2) hw0 (by
    intro m hm
    have hz := hφ1 m v hm
    simp [hz])

-- coordinate 1 down-shift
lemma dsum_c1_dn (M : ℕ) (w : ℕ → ℝ) {φ : ℕ × ℕ → ℝ}
    (hw0 : w 0 = 0) (hφ1 : ∀ m n, M < m → φ (m, n) = 0) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w m * (φ (m - 1, n)) ^ 2) =
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w (m + 1) * (φ (m, n)) ^ 2) := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  exact sum_shiftDown_gen M w (g := fun m => (φ (m, v)) ^ 2) hw0 (by
    intro m hm
    have hz := hφ1 m v hm
    simp [hz])

-- coordinate 2 up-shift
lemma dsum_c2_up (M : ℕ) (w : ℕ → ℝ) {φ : ℕ × ℕ → ℝ}
    (hw0 : w 0 = 0) (hφ2 : ∀ m n, M < n → φ (m, n) = 0) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w (n + 1) * (φ (m, n + 1)) ^ 2) =
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w n * (φ (m, n)) ^ 2) := by
  apply Finset.sum_congr rfl
  intro m hm
  exact sum_shiftUp_gen M w (g := fun n => (φ (m, n)) ^ 2) hw0 (by
    intro n hn
    have hz := hφ2 m n hn
    simp [hz])

-- coordinate 2 down-shift
lemma dsum_c2_dn (M : ℕ) (w : ℕ → ℝ) {φ : ℕ × ℕ → ℝ}
    (hw0 : w 0 = 0) (hφ2 : ∀ m n, M < n → φ (m, n) = 0) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w n * (φ (m, n - 1)) ^ 2) =
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        w (n + 1) * (φ (m, n)) ^ 2) := by
  apply Finset.sum_congr rfl
  intro m hm
  exact sum_shiftDown_gen M w (g := fun n => (φ (m, n)) ^ 2) hw0 (by
    intro n hn
    have hz := hφ2 m n hn
    simp [hz])

/-- split-sqrt cross sum (canonical squeeze term) -/
noncomputable def crossSplit (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    (Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt (((n + 1 : ℕ) : ℝ))) * φ (m, n) *
      φ (m + 1, n + 1)

/-- plus-cross reindexing: cross term of ‖b₊φ‖² is crossSplit -/
lemma dsum_cross_plus {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ2 : ∀ m n, M < n → φ (m, n) = 0) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt ((n : ℕ) : ℝ) * φ (m + 1, n) *
          φ (m, n - 1)) = crossSplit M φ := by
  unfold crossSplit
  apply Finset.sum_congr rfl
  intro m hm
  have hstep := sum_crossDown_gen M
      (fun n => Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt ((n : ℕ) : ℝ))
      (fun n => φ (m + 1, n)) (fun n => φ (m, n))
      (by simp) (by
        intro n hn
        have hz := hφ2 m n hn
        simp [hz])
  rw [hstep]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- minus-cross reindexing: cross term of ‖b₋φ‖² is crossSplit -/
lemma dsum_cross_minus {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ1 : ∀ m n, M < m → φ (m, n) = 0) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        Real.sqrt (((n + 1 : ℕ) : ℝ)) * Real.sqrt ((m : ℕ) : ℝ) * φ (m, n + 1) *
          φ (m - 1, n)) = crossSplit M φ := by
  unfold crossSplit
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hstep := sum_crossDown_gen M
      (fun m => Real.sqrt (((n + 1 : ℕ) : ℝ)) * Real.sqrt ((m : ℕ) : ℝ))
      (fun m => φ (m, n + 1)) (fun m => φ (m, n))
      (by simp) (by
        intro m hm
        have hz := hφ1 m n hm
        simp [hz])
  rw [hstep]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- diagonal number sum Nd = ΣΣ (m+n)|φ(m,n)|² over the rectangle -/
noncomputable def rectDiag (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    (((m : ℕ) : ℝ) + ((n : ℕ) : ℝ)) * (φ (m, n)) ^ 2

/-- pair cross sum Np = ΣΣ √((m+1)(n+1)) φ(m,n) φ(m+1,n+1) (product sqrt, as in fsQuad) -/
noncomputable def rectPair (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    Real.sqrt ((((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))) * φ (m, n) * φ (m + 1, n + 1)

lemma crossSplit_eq_rectPair (M : ℕ) (φ : ℕ × ℕ → ℝ) : crossSplit M φ = rectPair M φ := by
  unfold crossSplit rectPair
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have h1 : 0 ≤ (((m + 1 : ℕ) : ℝ)) := by positivity
  rw [Real.sqrt_mul h1]

/-- fsQuad = A·Nd + 2B·Np -/
lemma fsQuad_eq {A B : ℝ} (M : ℕ) (φ : ℕ × ℕ → ℝ) :
    fsQuad A B M φ = A * rectDiag M φ + 2 * B * rectPair M φ := by
  unfold fsQuad rectDiag rectPair
  simp_rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring

/-- pointwise square identity for b₊ -/
lemma bplus_sq_summand {α : ℝ} (m n : ℕ) (φ : ℕ × ℕ → ℝ) :
    (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m + 1, n) +
        α * Real.sqrt ((n : ℕ) : ℝ) * φ (m, n - 1)) ^ 2 =
      (((m + 1 : ℕ) : ℝ)) * (φ (m + 1, n)) ^ 2 +
        α ^ 2 * (((n : ℕ) : ℝ) * (φ (m, n - 1)) ^ 2) +
        2 * α * (Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt ((n : ℕ) : ℝ) * φ (m + 1, n) *
          φ (m, n - 1)) := by
  ring_nf
  rw [Real.sq_sqrt (by positivity : 0 ≤ (((1 + m : ℕ) : ℝ)))]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (((n : ℕ) : ℝ)))]
  ring

/-- pointwise square identity for b₋ -/
lemma bminus_sq_summand {α : ℝ} (m n : ℕ) (φ : ℕ × ℕ → ℝ) :
    (Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n + 1) +
        α * Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n)) ^ 2 =
      (((n + 1 : ℕ) : ℝ)) * (φ (m, n + 1)) ^ 2 +
        α ^ 2 * (((m : ℕ) : ℝ) * (φ (m - 1, n)) ^ 2) +
        2 * α * (Real.sqrt (((n + 1 : ℕ) : ℝ)) * Real.sqrt ((m : ℕ) : ℝ) * φ (m, n + 1) *
          φ (m - 1, n)) := by
  ring_nf
  rw [Real.sq_sqrt (by positivity : 0 ≤ (((1 + n : ℕ) : ℝ)))]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (((m : ℕ) : ℝ)))]
  ring

/-- Nat cast: ↑(k+1) = ↑k + 1 -/
lemma cast_add_one (k : ℕ) : (((k + 1 : ℕ) : ℝ)) = ((k : ℕ) : ℝ) + 1 := by
  rw [Nat.cast_add]
  norm_num


/-- sum with weight (m:ℝ) -/
noncomputable def d1 (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    (((m : ℕ) : ℝ)) * (φ (m, n)) ^ 2

/-- sum with weight (n:ℝ) -/
noncomputable def d2 (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    (((n : ℕ) : ℝ)) * (φ (m, n)) ^ 2

/-- sum with weight ((m+1:ℕ):ℝ) -/
noncomputable def fmE1 (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    (((m + 1 : ℕ) : ℝ)) * (φ (m, n)) ^ 2

/-- sum with weight ((n+1:ℕ):ℝ) -/
noncomputable def fmE2 (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    (((n + 1 : ℕ) : ℝ)) * (φ (m, n)) ^ 2

lemma rectNorm_bPlus {α : ℝ} {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    rectNorm M (bPlus α φ) = d1 M φ + α ^ 2 * fmE2 M φ + 2 * α * crossSplit M φ := by
  have hExp :
      rectNorm M (bPlus α φ) =
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m + 1 : ℕ) : ℝ)) * (φ (m + 1, n)) ^ 2) +
        α ^ 2 * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((n : ℕ) : ℝ) * (φ (m, n - 1)) ^ 2)) +
        2 * α * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt ((n : ℕ) : ℝ) * φ (m + 1, n) * φ (m, n - 1))) := by
        unfold rectNorm bPlus
        simp_rw [bplus_sq_summand]
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  calc
    rectNorm M (bPlus α φ)
        = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m + 1 : ℕ) : ℝ)) * (φ (m + 1, n)) ^ 2) +
          α ^ 2 * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((n : ℕ) : ℝ) * (φ (m, n - 1)) ^ 2)) +
          2 * α * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt ((n : ℕ) : ℝ) * φ (m + 1, n) * φ (m, n - 1))) := hExp
    _ = d1 M φ + α ^ 2 * fmE2 M φ + 2 * α * crossSplit M φ := by
        rw [dsum_c1_up M (fun m : ℕ => (m : ℝ)) (by norm_num) (vanishOn_coord1 hφ)]
        rw [dsum_c2_dn M (fun n : ℕ => (n : ℝ)) (by norm_num) (vanishOn_coord2 hφ)]
        rw [dsum_cross_plus (vanishOn_coord2 hφ)]
        rfl

lemma rectNorm_bMinus {α : ℝ} {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    rectNorm M (bMinus α φ) = d2 M φ + α ^ 2 * fmE1 M φ + 2 * α * crossSplit M φ := by
  have hExp :
      rectNorm M (bMinus α φ) =
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((n + 1 : ℕ) : ℝ)) * (φ (m, n + 1)) ^ 2) +
        α ^ 2 * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m : ℕ) : ℝ) * (φ (m - 1, n)) ^ 2)) +
        2 * α * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (Real.sqrt (((n + 1 : ℕ) : ℝ)) * Real.sqrt ((m : ℕ) : ℝ) * φ (m, n + 1) * φ (m - 1, n))) := by
        unfold rectNorm bMinus
        simp_rw [bminus_sq_summand]
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  calc
    rectNorm M (bMinus α φ)
        = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((n + 1 : ℕ) : ℝ)) * (φ (m, n + 1)) ^ 2) +
          α ^ 2 * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m : ℕ) : ℝ) * (φ (m - 1, n)) ^ 2)) +
          2 * α * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (Real.sqrt (((n + 1 : ℕ) : ℝ)) * Real.sqrt ((m : ℕ) : ℝ) * φ (m, n + 1) * φ (m - 1, n))) := hExp
    _ = d2 M φ + α ^ 2 * fmE1 M φ + 2 * α * crossSplit M φ := by
        rw [dsum_c2_up M (fun n : ℕ => (n : ℝ)) (by norm_num) (vanishOn_coord2 hφ)]
        rw [dsum_c1_dn M (fun m : ℕ => (m : ℝ)) (by norm_num) (vanishOn_coord1 hφ)]
        rw [dsum_cross_minus (vanishOn_coord1 hφ)]
        rfl

lemma rectDiag_combine (M : ℕ) (φ : ℕ × ℕ → ℝ) : rectDiag M φ = d1 M φ + d2 M φ := by
  unfold rectDiag d1 d2
  calc
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (((m : ℕ) : ℝ) + ((n : ℕ) : ℝ)) * (φ (m, n)) ^ 2)
        = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m : ℕ) : ℝ) * (φ (m, n)) ^ 2 + ((n : ℕ) : ℝ) * (φ (m, n)) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m : ℕ) : ℝ) * (φ (m, n)) ^ 2)) +
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((n : ℕ) : ℝ) * (φ (m, n)) ^ 2)) := by
          simp_rw [Finset.sum_add_distrib]

lemma e_combine (M : ℕ) (φ : ℕ × ℕ → ℝ) : fmE1 M φ + fmE2 M φ = rectDiag M φ + 2 * rectNorm M φ := by
  unfold fmE1 fmE2 rectDiag rectNorm
  calc
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (((m + 1 : ℕ) : ℝ)) * (φ (m, n)) ^ 2) +
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((n + 1 : ℕ) : ℝ)) * (φ (m, n)) ^ 2)
        = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            ((((m + 1 : ℕ) : ℝ)) * (φ (m, n)) ^ 2 +
              ((n + 1 : ℕ) : ℝ) * (φ (m, n)) ^ 2)) := by
          simp_rw [← Finset.sum_add_distrib]
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            ((((m : ℕ) : ℝ) + ((n : ℕ) : ℝ)) * (φ (m, n)) ^ 2 + 2 * (φ (m, n)) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          rw [cast_add_one m, cast_add_one n]
          ring
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m : ℕ) : ℝ) + ((n : ℕ) : ℝ)) * (φ (m, n)) ^ 2) +
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2), 2 * (φ (m, n)) ^ 2) := by
          simp_rw [Finset.sum_add_distrib]
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (((m : ℕ) : ℝ) + ((n : ℕ) : ℝ)) * (φ (m, n)) ^ 2) +
        2 * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2), (φ (m, n)) ^ 2) := by
          simp_rw [← Finset.mul_sum]

/-- 2·D·α² = A − s (Bogoliubov coefficient identity) -/
lemma bog_two_alpha_sq_D {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    2 * bogD A B * (bogAlpha A B) ^ 2 = A - bogS A B := by
  have hneq : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hsq : (bogS A B) ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  rw [bog_A_sub_s_eq hA hB]
  unfold bogAlpha bogD
  field_simp [hneq]

/-- 4·D·α = 2·B -/
lemma bog_four_alpha_D {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    4 * bogD A B * bogAlpha A B = 2 * B := by
  have hαD := bog_alpha_mul_D hA hB
  nlinarith

lemma bP_bM_sum {α : ℝ} {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    rectNorm M (bPlus α φ) + rectNorm M (bMinus α φ) =
      (1 + α ^ 2) * rectDiag M φ + 2 * α ^ 2 * rectNorm M φ + 4 * α * crossSplit M φ := by
  calc
    rectNorm M (bPlus α φ) + rectNorm M (bMinus α φ)
        = (d1 M φ + α ^ 2 * fmE2 M φ + 2 * α * crossSplit M φ) +
          (d2 M φ + α ^ 2 * fmE1 M φ + 2 * α * crossSplit M φ) := by
          rw [rectNorm_bPlus hφ, rectNorm_bMinus hφ]
    _ = (d1 M φ + d2 M φ) + α ^ 2 * (fmE1 M φ + fmE2 M φ) + 4 * α * crossSplit M φ := by ring
    _ = rectDiag M φ + α ^ 2 * (rectDiag M φ + 2 * rectNorm M φ) + 4 * α * crossSplit M φ := by
          rw [← rectDiag_combine, e_combine]
    _ = (1 + α ^ 2) * rectDiag M φ + 2 * α ^ 2 * rectNorm M φ + 4 * α * crossSplit M φ := by ring

/-- THE 2-MODE BOGOLIUBOV IDENTITY (FS eq:BogIdentity, κ = 0), in quadratic-form form:

    ⟨φ,Hφ⟩ = D·(‖b₊φ‖² + ‖b₋φ‖²) − (A−s)·‖φ‖²

for `H = A(N₁+N₂) + B(aUpDag·aLoDag + aUp·aLo)`, `s = √(A²−B²)`, `D = (A+s)/2`,
`α = B/(A+s)`, `b₊ = aUp + α·aLoDag`, `b₋ = aLo + α·aUpDag`.  (Numerically verified
on 2000 random finite states.) -/
theorem fock_two_mode_identity {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (M : ℕ)
    {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    fsQuad A B M φ =
      bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) -
        (A - bogS A B) * rectNorm M φ := by
  have hc1 : bogD A B * (1 + bogAlpha A B ^ 2) = A := bog_D_mul_one_add_alpha_sq hA hB
  have hc2 : 2 * bogD A B * (bogAlpha A B) ^ 2 = A - bogS A B := bog_two_alpha_sq_D hA hB
  have hc3 : 4 * bogD A B * bogAlpha A B = 2 * B := bog_four_alpha_D hA hB
  calc
    fsQuad A B M φ = A * rectDiag M φ + 2 * B * rectPair M φ := fsQuad_eq M φ
    _ = A * rectDiag M φ + 2 * B * crossSplit M φ := by rw [crossSplit_eq_rectPair]
    _ = bogD A B *
          ((1 + bogAlpha A B ^ 2) * rectDiag M φ + 2 * bogAlpha A B ^ 2 * rectNorm M φ +
            4 * bogAlpha A B * crossSplit M φ) - (A - bogS A B) * rectNorm M φ := by
          have hR : bogD A B *
                ((1 + bogAlpha A B ^ 2) * rectDiag M φ + 2 * bogAlpha A B ^ 2 * rectNorm M φ +
                  4 * bogAlpha A B * crossSplit M φ) - (A - bogS A B) * rectNorm M φ =
              A * rectDiag M φ + 2 * B * crossSplit M φ := by
            calc
              bogD A B * ((1 + bogAlpha A B ^ 2) * rectDiag M φ +
                    2 * bogAlpha A B ^ 2 * rectNorm M φ + 4 * bogAlpha A B * crossSplit M φ) -
                  (A - bogS A B) * rectNorm M φ
                  = (bogD A B * (1 + bogAlpha A B ^ 2)) * rectDiag M φ +
                    (2 * bogD A B * bogAlpha A B ^ 2) * rectNorm M φ +
                    (4 * bogD A B * bogAlpha A B) * crossSplit M φ -
                    (A - bogS A B) * rectNorm M φ := by ring
              _ = A * rectDiag M φ + (A - bogS A B) * rectNorm M φ + 2 * B * crossSplit M φ -
                    (A - bogS A B) * rectNorm M φ := by rw [hc1, hc2, hc3]
              _ = A * rectDiag M φ + 2 * B * crossSplit M φ := by ring
          exact hR.symm
    _ = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) -
        (A - bogS A B) * rectNorm M φ := by
          rw [← bP_bM_sum (α := bogAlpha A B) hφ]

/-- GROUND ESTIMATE (FS eq:BogIneq, κ = 0): the pair Hamiltonian is bounded below by
    the negative zero-point constant:

    ⟨φ,Hφ⟩ ≥ −(A−s)·‖φ‖².

    Immediate from `fock_two_mode_identity` + `rectNorm_nonneg` + `bogD_pos`. -/
theorem fock_ground_estimate {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (M : ℕ)
    {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    - (A - bogS A B) * rectNorm M φ ≤ fsQuad A B M φ := by
  rw [fock_two_mode_identity hA hB M hφ]
  have hD : 0 < bogD A B := bogD_pos hA hB
  have hn1 : 0 ≤ rectNorm M (bPlus (bogAlpha A B) φ) := rectNorm_nonneg M (bPlus (bogAlpha A B) φ)
  have hn2 : 0 ≤ rectNorm M (bMinus (bogAlpha A B) φ) := rectNorm_nonneg M (bMinus (bogAlpha A B) φ)
  have hnn : 0 ≤ bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) :=
    mul_nonneg (le_of_lt hD) (add_nonneg hn1 hn2)
  linarith

end BoseGases
end Submission
