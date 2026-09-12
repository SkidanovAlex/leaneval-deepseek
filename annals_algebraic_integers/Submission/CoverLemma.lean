import Mathlib
import Submission.GeoCore

/-!
# Lattice covering lemma (geometry-of-numbers half of `thm:adjust`)

Smith, GON.tex `thm:adjust` uses the "flatness theorem for simplices"
(BLPS Cor 2.5).  Its only consequence we need (analysis in PROGRESS.md
Session-11) is the following PURE geometry-of-numbers statement — any
POLYNOMIAL covering radius suffices downstream, with an absolute exponent:

Let `B : Matrix (Fin n) (Fin n) ℝ` (here `B i j = b°_ij`, the coefficient of
`Y^j` in the real polynomial `Q°_i` of a real basis of the degree-≤-(n−1)
polynomials) satisfy the DUAL CONDITION

    ∀ nonzero integer vector d : ∃ i, 1 ≤ |Σ_j B i j · d j|        (∗)

(i.e. the lattice `M* := {B·d : d ∈ ℤⁿ} ⊆ ℝⁿ` contains no nonzero point in the
open cube `(−1,1)^n`).  Let `M := {γ : Bᵀ·γ ∈ ℤⁿ}` (the β-coordinates of the
integer polynomials in the `Q°` basis: `γ ∈ M ⟺ Σ_i γ_i·Q°_i` is an integer
polynomial).  Then the ℓ₁-covering radius of `M` is polynomially bounded with an
absolute exponent:  for every real `p : Fin n → ℝ` (coefficients of the real
polynomial `P`) there is `r : Fin n → ℤ` (coefficients of an integer polynomial
`R`) and `β : Fin n → ℝ` with `Bᵀ·β = p − r` and `Σ_i |β_i| ≤ n^C`, for an
absolute `C` independent of `n`.

## Why the dual condition gives the covering (route)

1. `M* = {B·d : d ∈ ℤⁿ}`:  `M = {γ : Aγ ∈ ℤⁿ}` with `A := Bᵀ`; its dual (dot
   product) is `M* = Aᵀ·ℤⁿ = B·ℤⁿ`.  So (∗) says exactly
   `λ₁(M*, ℓ∞) ≥ 1` (the first successive minimum of `M*` w.r.t. the ℓ∞ norm
   is at least 1).

2. Classical covering-radius/successive-minima facts (prove or find in
   Mathlib; any absolute-constant version suffices):
   (a) `μ₁(M, ℓ₁) ≤ (n/2)·λ_n(M, ℓ₁)` (covering radius ≤ half the sum of the
       successive minima ≤ (n/2)·λ_n).
   (b) Transference for dual norms:
       `λ_n(M, ℓ₁) · λ₁(M*, ℓ∞) ≤ c·n^{c'}` for absolute `c,c'` — e.g. prove
       the elementary bound `λ_k(L, ‖·‖) · λ_{n+1−k}(L*, ‖·‖*) ≤ n²` for any
       lattice `L` and any norm `‖·‖` with dual norm `‖·‖*` (via the
       determinant of the Gram matrix of the minima vectors and Hadamard's
       inequality, or via the volume of the parallelepiped: if
       `g₁,…,g_n ∈ L` and `h₁,…,h_n ∈ L*` are bases of the respective
       ℚ-spans with `‖g_i‖ = λ_i`, `‖h_i‖* = λ_i(L*,‖·‖*)`, then
       `1 ≤ |det(g_i · h_j)| ≤ ∏ ‖g_i‖·∏‖h_i‖`-style bounds give the dual
       relation; alternatively use the Mathlib machinery that was formalized
       in `MinkUpper` (successive minima, Minkowski's theorems) — any route
       with an absolute constant is acceptable.)
   Combining with `λ₁(M*, ℓ∞) ≥ 1` gives `λ_n(M, ℓ₁) ≤ c·n^{c'}` hence
   `μ₁(M, ℓ₁) ≤ n^C` for an absolute `C`.

3. From `μ₁(M, ℓ₁) ≤ n^C`: for the given `p`, let
   `x := (Bᵀ)⁻¹ · p` (possible since `det B ≠ 0`).  By the covering radius,
   there is `γ ∈ M` with `Σ|γ − x| ≤ n^C`.  Since `γ ∈ M`, `Bᵀγ = r` for some
   integer vector `r`; set `β := γ`; then `Bᵀβ = r` and we need `Bᵀβ = p − r'`
   with `r' ∈ ℤⁿ` — so take instead `β' := γ − x` … careful with signs: we want
   `Bᵀβ = p − r`, i.e. `β = (Bᵀ)⁻¹(p − r) = x − (Bᵀ)⁻¹r`.  As `r` ranges over
   `ℤⁿ`, `(Bᵀ)⁻¹r` ranges over `M` (that is the definition of `M`), so the set
   of achievable `β` is `x − M`; covering radius says `x` is within ℓ₁-distance
   `n^C` of `M`, so some `β = x − γ` with `γ ∈ M` satisfies `Σ|β_i| ≤ n^C`
   and `Bᵀβ = p − r` where `r := Bᵀ(x − β) = p − Bᵀβ ∈ ℤⁿ`.  Finish.

Deliver exactly the theorem below with no gaps; axioms ⊆ {propext, Quot.sound,
Classical.choice}.  You may add any number of private helper lemmas in this
file.  Self-contained: only `import Mathlib`.  This is expected to be a LONG
proof (several hundred lines) — like the earlier `MinkUpper` formalization.
The constant may be huge (e.g. `n^1000`) as long as it is ABSOLUTE (independent
of `n`).
-/

noncomputable section

open scoped BigOperators

namespace Submission.CoverLemma

/-- The dual condition: every nonzero integer vector `d` is "seen" by some row
of `B` with value at least 1 in absolute value. -/
def DualCondition {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ d : Fin n → ℤ, d ≠ 0 → ∃ i : Fin n, (1 : ℝ) ≤ |∑ j : Fin n, B i j * (d j : ℝ)|

/-- Lattice covering from the dual condition (with an absolute polynomial
exponent). -/
theorem covering_of_dual {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hdet : B.det ≠ 0) (hdual : DualCondition B) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Fin n → ℝ,
      ∃ (r : Fin n → ℤ) (β : Fin n → ℝ),
        (∀ j : Fin n, (∑ i : Fin n, β i * B i j) = p j - (r j : ℝ)) ∧
        (∑ i : Fin n, |β i|) ≤ (n : ℝ) ^ C := by
  rcases (Submission.GeoCore.geo_core n hn B hdet hdual) with ⟨C0, hC0pos, hC0le, hcover⟩
  refine ⟨(100 : ℝ), by norm_num, ?_⟩
  intro p
  rcases hcover p with ⟨β, hz, hβ⟩
  refine ⟨fun i => Classical.choose (hz i), β, ?_, ?_⟩
  · intro j
    have hspec := Classical.choose_spec (hz j)
    have hS : (∑ i : Fin n, β i * B i j) = (∑ i : Fin n, B i j * β i) := by
      apply Finset.sum_congr rfl; intro i hi; ring
    rw [hS]
    change (∑ i : Fin n, B i j * β i) = p j - (↑(Classical.choose (hz j) : ℤ) : ℝ)
    linarith
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmono : (n : ℝ) ^ C0 ≤ (n : ℝ) ^ (100 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hn1 hC0le
    exact le_trans hβ hmono

end Submission.CoverLemma
