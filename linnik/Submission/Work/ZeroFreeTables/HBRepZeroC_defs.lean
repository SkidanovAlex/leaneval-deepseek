/-
# ZeroFreeTables — HBRepZeroC_defs

The one input that `HBRepZeroC` needs: **HB Theorem 2, first half** (D. R.
Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least prime in
an arithmetic progression*, PLMS (3) **64** (1992) 265–338, p. 3):

> If `q` is sufficiently large, the function `∏_{χ mod q} L(s,χ)` has at most 2 zeros,
> counted according to multiplicity, in the region `σ ≥ 1 − 0.696/log q`, `|t| ≤ 1`.

The `Prop` below records this in the contract's vocabulary (`lamOf`, `zeroMult`,
`IsZ`'s height cut) in the *pair-count* form: a finite set of pairs `(χ, ρ)` of a
non-principal character and a zero of its `L`-function inside the region has total
multiplicity at most `2`.  That is exactly HB's count: the multiplicity of a zero of
the product `∏_{χ} L(s,χ)` at a point `ρ` is `∑_χ zeroMult χ ρ`, so a bound of `2` on
every finite set of pairs `(χ, ρ)` is the assertion that the product has at most two
zeros, counted with multiplicity, in the region.

(The principal character is left out of the pairs: `L(s,χ₀) = ζ(s)` contributes no
zero in the region — `σ ≥ 1 − 0.696/log q` with `|t| ≤ 1` and `q → ∞` is a vanishing
neighbourhood of `s = 1`, and `ζ` has neither a zero nor (for `t ≠ 0`) a pole there —
so HB's count of the full product is a count over the non-principal characters.)

The `Prop` is used only through the elementary observation
(`HBRepZeroC_proof.HBRepZeroC_of_thm2`) that a *multiple* zero `ρ₁` of `χ₁` outside
the real-real case contributes **four** pairs: `(χ₁, ρ₁)` and `(χ₁⁻¹, conj ρ₁)`, each
of multiplicity `≥ 2` (`Work.A7.zeroMult_conj_inv`:
`zeroMult χ₁⁻¹ (conj ρ₁) = zeroMult χ₁ ρ₁`), with `λ(conj ρ₁) = λ(ρ₁)` and
`|Im conj ρ₁| = |Im ρ₁|`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.Table8CertExtPrinted

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **HB Theorem 2, first half** (p. 3): for `q` large enough, the multiplicity-weighted
number of zeros of the non-principal `L`-functions mod `q` with `λ(ρ) ≤ 696/1000` and
`|Im ρ| ≤ 1` is at most `2`.

Stated in the pair form (a `Finset` of pairs `(χ, ρ)`, `χ ≠ 1`), which is what the
assembly consumes. -/
def HBThm2Count : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
    ∀ S : Finset (DirichletCharacter ℂ q × ℂ),
      (∀ p ∈ S, p.1 ≠ 1 ∧ lamOf q p.2 ≤ 696/1000 ∧ |p.2.im| ≤ 1) →
      S.sum (fun p => zeroMult p.1 p.2) ≤ 2


/-! ## HB Lemma 9.1 in the repeated-zero case

The second input: HB's §9 derivation `(9.1)`–`(9.13)` re-run at the **double** zero
`ρ₁` (i.e. with `ρ₀ = ρ₁`), where the multiplicity `2` multiplies the near-zero terms
`Re P₃(α/((s−ρ₁)𝓛))` of the explicit formula.  This is *not* the `ρ₁ = ρ₀` instance of
`HBLemma9_1` (which needs two distinct zeros and whose conclusion genuinely fails at
`λ₀ = λ₁`): the doubled terms give a *stronger* inequality, whose lossy form is
`ineq913 λ₁ λ₁ a K ε` — exactly the shape of HB's Table 8 read along its diagonal
`(λ₁, λ₀) = (0.696, 0.696)`.

The numerical content is the `Table 8` certificate row `(0.696, 0.696, a = 269/100)`:
`cond913 (696/1000) (696/1000) (269/100) (Kaff (696/1000))` and
`p913 (696/1000) (696/1000) (269/100) (Kaff (696/1000)) < 0`, both already proved in
`Table8CertExtPrinted.lean`.  See `HBRepZeroC_proof.HBRepZeroC_of_rep`. -/
def HBLemma9_1_rep : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → IsZ χ₁ ρ₁ →
      2 ≤ zeroMult χ₁ ρ₁ →
      cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K →
      ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε


/-! ## The certificate row and the `p913` monotonicity of the diagonal argument -/

/-- `λ(ρ) = (1 - Re ρ) log q` is invariant under complex conjugation. -/
theorem hbRZC_lamOf_conj (q : ℕ) (ρ : ℂ) : lamOf q ((starRingEnd ℂ) ρ) = lamOf q ρ := by
  rw [lamOf, lamOf, Complex.conj_re]
/-- The certified diagonal row of HB's Table 8, in the engine's `(λ₁, λ₀, a)` shape. -/
theorem hbRZC_t8diag_cert :
    cond913 (696/1000) (696/1000) (269/100) (Kaff (696/1000)) ∧
      p913 (696/1000) (696/1000) (269/100) (Kaff (696/1000)) < 0 :=
  Table8CertExtPrinted ((696/1000:ℝ), (696/1000:ℝ), (696/1000:ℝ), (269/100:ℝ))
    (by simp [t8certRowsExtP])
/-- `p913` is monotone along the diagonal `λ₀ = λ₁` (it is the sum of a monotone
`P₃R`-difference and of `(a+λ)ψ13 K`). -/
theorem hbRZC_p913_diag_mono {lam lam' a K : ℝ} (h0 : -a < lam) (h : lam ≤ lam')
    (ha : 0 < a) (hK : 0 ≤ K) : p913 lam lam a K ≤ p913 lam' lam' a K := by
  have hpos : 0 < a + lam := by linarith
  have hpos' : 0 < a + lam' := by linarith
  have hx : (a + lam) / (a + lam) = 1 := div_self (ne_of_gt hpos)
  have hx' : (a + lam') / (a + lam') = 1 := div_self (ne_of_gt hpos')
  have h1 : (a + lam) / a ≤ (a + lam') / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    linarith
  have h2 : P3R ((a + lam) / a) ≤ P3R ((a + lam') / a) := P3R_mono h1
  have hψ : 0 ≤ psi13 K := by
    unfold psi13
    nlinarith [sq_nonneg K]
  have hK2 : 0 ≤ K ^ 2 + 1/2 := by positivity
  have h3 : (a + lam) * psi13 K ≤ (a + lam') * psi13 K :=
    mul_le_mul_of_nonneg_right (by linarith) hψ
  have h4 : (K ^ 2 + 1/2) * (P3R ((a + lam) / a) - P3R 1)
      ≤ (K ^ 2 + 1/2) * (P3R ((a + lam') / a) - P3R 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hK2
  unfold p913
  rw [hx, hx']
  linarith
end Work.ZeroFreeTables
