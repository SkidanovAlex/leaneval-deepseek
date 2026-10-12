import Mathlib.Analysis.Real.Sqrt
import ChallengeDeps
import Submission.Fock2Mode
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5/6 — the two-mode Bogoliubov identity WITH the linear (κ) term
(FS eq:BogIdentity / eq:BogIneq, thm:bogolubov-complete, final_v2.tex ~3458-3506)

With the same data as Submission.Fock2Mode (`s := bogS A B`, `D := bogD A B`,
`α := bogAlpha A B`) and a REAL linear coefficient `L` (FS: κ = L ∈ ℝ), set

    γ := 2L/(A+B+s),     b₊ᵧ := b₊ + γ,   b₋ᵧ := b₋ + γ   (c-number shifts)

(FS write c₀ := 2κ̄/(A+B+s) for b₋ and c̄₀ for b₊; equal to γ in the real case.)
The full quadratic form including the linear term
    κ(a†₊ + a₋) + κ̄(a₊ + a†₋)  =  L·(aUp + aUpDag + aLo + aLoDag)
is `fsQuadLin A B L M φ = fsQuad A B M φ + 2L·(fmsLin1 M φ + fmsLin2 M φ)` where
    fmsLin1 := ΣΣ√(m+1)·φ(m,n)·φ(m+1,n)   (the symmetric form of ⟨φ,(a₊+a₊†)φ⟩/2)
    fmsLin2 := ΣΣ√(n+1)·φ(m,n)·φ(m,n+1)   (ditto for mode 2).

THEOREM (FS eq:BogIdentity with real κ = L; NUMERICALLY VERIFIED on 1000
random finite states, worst err < 1e-12):
    fsQuadLin A B L M φ =
      D·(‖b₊ᵧφ‖² + ‖b₋ᵧφ‖²) − (A−s)·‖φ‖² − (2L²/(A+B))·‖φ‖²
Corollary (eq:BogIneq, real κ = L):  fsQuadLin ≥ −[(A−s) + 2L²/(A+B)]·‖φ‖².

Derivation (matches FS; use in the proof):
  * ‖b₊ᵧφ‖² = ‖b₊φ‖² + 2γ·⟨b₊φ,φ⟩ + γ²‖φ‖²;  ‖b₋ᵧφ‖² likewise.
  * ⟨b₊φ,φ⟩ = fmsLin1 + α·fmsLin2   and   ⟨b₋φ,φ⟩ = fmsLin2 + α·fmsLin1
    (each ⟨·,·⟩ computed as a rectangle sum; reindex the α-part).
  * hence the S-type part (linear in the pair products): coefficient matching
    2Dγ·(1+α) = 2L  follows from  (1+α)(A+s) = A+B+s  i.e. α(A+s) = B;
  * the ‖φ‖² part: 2Dγ² = 2L²/(A+B)  follows from
    2(A+s)(A+B) = (A+B+s)²  [expand RHS using s² = A²−B²];
  * with those two coefficient identities the claim is the κ=0 identity
    `fock_two_mode_identity` plus exact bookkeeping of the linear terms.
Use `Finset.sum_bij`/reindexing as in Fock2Mode, `ring`, `nlinarith`,
`field_simp`, `positivity`, `bogS_sq`, `bog_A_sub_s_eq`, `bog_D_mul_one_add_alpha_sq`.
-/

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
namespace BoseGases

open scoped BigOperators

/-- `γ := 2L/(A+B+s)`, the c-number shift completing the square in the linear term. -/
noncomputable def fmsGamma (A B L : ℝ) : ℝ := 2 * L / (A + B + bogS A B)

/-- `ΣΣ √(m+1)·φ(m,n)·φ(m+1,n)` over the rectangle (half the symmetric form of
    the mode-1 creation+annihilation linear term). -/
noncomputable def fmsLin1 (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    Real.sqrt ((((m + 1 : ℕ) : ℝ))) * φ (m, n) * φ (m + 1, n)

/-- `ΣΣ √(n+1)·φ(m,n)·φ(m,n+1)` (mode-2 analogue of `fmsLin1`). -/
noncomputable def fmsLin2 (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
    Real.sqrt ((((n + 1 : ℕ) : ℝ))) * φ (m, n) * φ (m, n + 1)

/-- Quadratic form of `H = A(N₁+N₂) + B(aUpDag·aLoDag + aUp·aLo) + L(a₊+a₊†+a₋+a₋†)`. -/
noncomputable def fsQuadLin (A B L : ℝ) (M : ℕ) (φ : ℕ × ℕ → ℝ) : ℝ :=
  fsQuad A B M φ + 2 * L * (fmsLin1 M φ + fmsLin2 M φ)

/-- `b₊ᵧ := b₊ + γ` (shifted squeezing operator). -/
noncomputable def fmsBPlus (A B L : ℝ) (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  bPlus (bogAlpha A B) φ p + fmsGamma A B L * φ p

/-- `b₋ᵧ := b₋ + γ`. -/
noncomputable def fmsBMinus (A B L : ℝ) (φ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ := fun p =>
  bMinus (bogAlpha A B) φ p + fmsGamma A B L * φ p

/-- THE 2-MODE BOGOLIUBOV IDENTITY WITH LINEAR TERM (FS eq:BogIdentity, κ = L ∈ ℝ):

    ⟨φ,Hφ⟩ = D·(‖b₊ᵧφ‖² + ‖b₋ᵧφ‖²) − (A−s)·‖φ‖² − (2L²/(A+B))·‖φ‖². -/
private lemma sq_add_const_mul (x z : ℝ) (γ : ℝ) :
    (x + γ * z) ^ 2 = x ^ 2 + 2 * γ * (x * z) + γ ^ 2 * z ^ 2 := by
  rw [add_sq]
  ring

/-- squared norm of a pointwise shifted function:
    ‖ψ + γ·φ‖² = ‖ψ‖² + 2γ·⟨ψ,φ⟩ + γ²·‖φ‖²  (rectangular, finite sums) -/
lemma rectNorm_add_const_mul (M : ℕ) (ψ φ : ℕ × ℕ → ℝ) (γ : ℝ) :
    rectNorm M (fun p => ψ p + γ * φ p)
      = rectNorm M ψ +
        2 * γ * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2), ψ (m, n) * φ (m, n)) +
        γ ^ 2 * rectNorm M φ := by
  unfold rectNorm
  calc
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (ψ (m, n) + γ * φ (m, n)) ^ 2)
      = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
          (ψ (m, n) ^ 2 + 2 * γ * (ψ (m, n) * φ (m, n)) + γ ^ 2 * φ (m, n) ^ 2)) := by
          simp_rw [sq_add_const_mul]
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2), ψ (m, n) ^ 2) +
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
          (2 * γ * (ψ (m, n) * φ (m, n)))) +
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2), γ ^ 2 * φ (m, n) ^ 2) := by
          simp_rw [Finset.sum_add_distrib]
    _ = rectNorm M ψ +
        2 * γ * (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2), ψ (m, n) * φ (m, n)) +
        γ ^ 2 * rectNorm M φ := by
          simp_rw [rectNorm]
          simp_rw [Finset.mul_sum]

/-- per-m reindex for the mode-2 creation part of ⟨b₊φ,φ⟩ -/
lemma per_m_lin2 (M m : ℕ) {φ : ℕ × ℕ → ℝ} (hφ2 : ∀ m n, M < n → φ (m, n) = 0) :
    (∑ n ∈ Finset.range (M + 2), (Real.sqrt ((n : ℕ) : ℝ) * φ (m, n - 1) * φ (m, n)))
      = (∑ n ∈ Finset.range (M + 2), (Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n) * φ (m, n + 1))) := by
  calc
    (∑ n ∈ Finset.range (M + 2), (Real.sqrt ((n : ℕ) : ℝ) * φ (m, n - 1) * φ (m, n)))
      = (∑ n ∈ Finset.range (M + 2), (Real.sqrt ((n : ℕ) : ℝ) * φ (m, n) * φ (m, n - 1))) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (∑ n ∈ Finset.range (M + 2), (Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n + 1) * φ (m, n))) := by
          exact sum_crossDown_gen M (fun n => Real.sqrt ((n : ℕ) : ℝ))
            (fun n => φ (m, n)) (fun n => φ (m, n)) (by norm_num) (by intro n hn; exact hφ2 m n hn)
    _ = (∑ n ∈ Finset.range (M + 2), (Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n) * φ (m, n + 1))) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring

/-- per-n reindex for the mode-1 creation part of ⟨b₋φ,φ⟩ -/
lemma per_n_lin1 (M n : ℕ) {φ : ℕ × ℕ → ℝ} (hφ1 : ∀ m n, M < m → φ (m, n) = 0) :
    (∑ m ∈ Finset.range (M + 2), (Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n) * φ (m, n)))
      = (∑ m ∈ Finset.range (M + 2), (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m, n) * φ (m + 1, n))) := by
  calc
    (∑ m ∈ Finset.range (M + 2), (Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n) * φ (m, n)))
      = (∑ m ∈ Finset.range (M + 2), (Real.sqrt ((m : ℕ) : ℝ) * φ (m, n) * φ (m - 1, n))) := by
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ = (∑ m ∈ Finset.range (M + 2), (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m + 1, n) * φ (m, n))) := by
          exact sum_crossDown_gen M (fun m => Real.sqrt ((m : ℕ) : ℝ))
            (fun m => φ (m, n)) (fun m => φ (m, n)) (by norm_num) (by intro m hm; exact hφ1 m n hm)
    _ = (∑ m ∈ Finset.range (M + 2), (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m, n) * φ (m + 1, n))) := by
          apply Finset.sum_congr rfl
          intro m hm
          ring

/-- inner product ⟨b₊φ,φ⟩ splits into the fmsLin pieces: fmsLin1 + α·fmsLin2 -/
lemma ip_bPlus_eq {α : ℝ} {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (bPlus α φ (m, n) * φ (m, n))) = fmsLin1 M φ + α * fmsLin2 M φ := by
  have hlin1 : (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m + 1, n) * φ (m, n))) = fmsLin1 M φ := by
    unfold fmsLin1
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hlin2 : (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (Real.sqrt ((n : ℕ) : ℝ) * φ (m, n - 1) * φ (m, n))) = fmsLin2 M φ := by
    unfold fmsLin2
    apply Finset.sum_congr rfl
    intro m hm
    exact per_m_lin2 M m (vanishOn_coord2 hφ)
  calc
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (bPlus α φ (m, n) * φ (m, n)))
      = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
          ((Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m + 1, n) + α * Real.sqrt ((n : ℕ) : ℝ) * φ (m, n - 1)) *
            φ (m, n))) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          simp [bPlus]
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
          (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m + 1, n) * φ (m, n) +
            α * (Real.sqrt ((n : ℕ) : ℝ) * φ (m, n - 1) * φ (m, n)))) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m + 1, n) * φ (m, n))) +
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (α * (Real.sqrt ((n : ℕ) : ℝ) * φ (m, n - 1) * φ (m, n)))) := by
          simp_rw [Finset.sum_add_distrib]
    _ = fmsLin1 M φ + α * fmsLin2 M φ := by
          rw [hlin1]
          congr 1
          simp_rw [← Finset.mul_sum]
          rw [hlin2]

/-- inner product ⟨b₋φ,φ⟩ splits: fmsLin2 + α·fmsLin1 -/
lemma ip_bMinus_eq {α : ℝ} {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (bMinus α φ (m, n) * φ (m, n))) = fmsLin2 M φ + α * fmsLin1 M φ := by
  have hlin2 : (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n + 1) * φ (m, n))) = fmsLin2 M φ := by
    unfold fmsLin2
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hlin1 : (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n) * φ (m, n))) = fmsLin1 M φ := by
    calc
      (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
          (Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n) * φ (m, n)))
        = (∑ n ∈ Finset.range (M + 2), ∑ m ∈ Finset.range (M + 2),
            (Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n) * φ (m, n))) := by
            rw [Finset.sum_comm]
      _ = (∑ n ∈ Finset.range (M + 2), ∑ m ∈ Finset.range (M + 2),
            (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m, n) * φ (m + 1, n))) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact per_n_lin1 M n (vanishOn_coord1 hφ)
      _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (Real.sqrt (((m + 1 : ℕ) : ℝ)) * φ (m, n) * φ (m + 1, n))) := by
            rw [Finset.sum_comm]
  calc
    (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
        (bMinus α φ (m, n) * φ (m, n)))
      = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
          ((Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n + 1) + α * Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n)) *
            φ (m, n))) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          simp [bMinus]
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
          (Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n + 1) * φ (m, n) +
            α * (Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n) * φ (m, n)))) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (Real.sqrt (((n + 1 : ℕ) : ℝ)) * φ (m, n + 1) * φ (m, n))) +
        (∑ m ∈ Finset.range (M + 2), ∑ n ∈ Finset.range (M + 2),
            (α * (Real.sqrt ((m : ℕ) : ℝ) * φ (m - 1, n) * φ (m, n)))) := by
          simp_rw [Finset.sum_add_distrib]
    _ = fmsLin2 M φ + α * fmsLin1 M φ := by
          rw [hlin2]
          congr 1
          simp_rw [← Finset.mul_sum]
          rw [hlin1]


/-- ‖b₊ᵧφ‖² = ‖b₊φ‖² + 2γ·⟨b₊φ,φ⟩ + γ²·‖φ‖² with ⟨b₊φ,φ⟩ = fmsLin1 + α·fmsLin2 -/
lemma rectNorm_fmsBPlus {A B L : ℝ} {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    rectNorm M (fmsBPlus A B L φ)
      = rectNorm M (bPlus (bogAlpha A B) φ) +
        2 * fmsGamma A B L * (fmsLin1 M φ + bogAlpha A B * fmsLin2 M φ) +
        fmsGamma A B L ^ 2 * rectNorm M φ := by
  rw [show rectNorm M (fmsBPlus A B L φ)
        = rectNorm M (fun p => bPlus (bogAlpha A B) φ p + fmsGamma A B L * φ p) by rfl]
  rw [rectNorm_add_const_mul]
  rw [ip_bPlus_eq hφ]

/-- ‖b₋ᵧφ‖² = ‖b₋φ‖² + 2γ·⟨b₋φ,φ⟩ + γ²·‖φ‖² with ⟨b₋φ,φ⟩ = fmsLin2 + α·fmsLin1 -/
lemma rectNorm_fmsBMinus {A B L : ℝ} {M : ℕ} {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    rectNorm M (fmsBMinus A B L φ)
      = rectNorm M (bMinus (bogAlpha A B) φ) +
        2 * fmsGamma A B L * (fmsLin2 M φ + bogAlpha A B * fmsLin1 M φ) +
        fmsGamma A B L ^ 2 * rectNorm M φ := by
  rw [show rectNorm M (fmsBMinus A B L φ)
        = rectNorm M (fun p => bMinus (bogAlpha A B) φ p + fmsGamma A B L * φ p) by rfl]
  rw [rectNorm_add_const_mul]
  rw [ip_bMinus_eq hφ]

/-- linear coefficient identity: D·γ·(1+α) = L -/
lemma fms_lin_coeff {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B) :
    bogD A B * fmsGamma A B L * (1 + bogAlpha A B) = L := by
  have hden : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hden2 : A + B + bogS A B ≠ 0 := by
    have hs : 0 ≤ bogS A B := bogS_nonneg A B
    nlinarith
  unfold fmsGamma bogD bogAlpha
  field_simp [hden, hden2]
  ring

/-- norm-squared coefficient identity: 2D·γ² = 2L²/(A+B) -/
lemma fms_sq_coeff {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B) :
    2 * bogD A B * (fmsGamma A B L) ^ 2 = 2 * L ^ 2 / (A + B) := by
  have hden : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hden2 : A + B + bogS A B ≠ 0 := by
    have hs : 0 ≤ bogS A B := bogS_nonneg A B
    nlinarith
  have hABn : A + B ≠ 0 := by nlinarith
  have hsq : bogS A B ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  unfold fmsGamma bogD
  field_simp [hden2, hABn]
  nlinarith

/-- the shifted norms re-expressed with the linear coefficient absorbed:
    D·(‖b₊ᵧφ‖²+‖b₋ᵧφ‖²) = D·(‖b₊φ‖²+‖b₋φ‖²) + 2L·(Lin1+Lin2) + 2Dγ²·‖φ‖² -/
lemma fms_expand {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    bogD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ))
      = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) +
        2 * L * (fmsLin1 M φ + fmsLin2 M φ) +
        2 * bogD A B * (fmsGamma A B L) ^ 2 * rectNorm M φ := by
  have hc : bogD A B * fmsGamma A B L * (1 + bogAlpha A B) = L := fms_lin_coeff hA hB hAB
  calc
    bogD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ))
        = bogD A B * (rectNorm M (fmsBPlus A B L φ)) + bogD A B * (rectNorm M (fmsBMinus A B L φ)) := by
            ring
    _ = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) +
            2 * fmsGamma A B L * (fmsLin1 M φ + bogAlpha A B * fmsLin2 M φ) +
            fmsGamma A B L ^ 2 * rectNorm M φ) +
          bogD A B * (rectNorm M (bMinus (bogAlpha A B) φ) +
            2 * fmsGamma A B L * (fmsLin2 M φ + bogAlpha A B * fmsLin1 M φ) +
            fmsGamma A B L ^ 2 * rectNorm M φ) := by
            rw [rectNorm_fmsBPlus hφ, rectNorm_fmsBMinus hφ]
    _ = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) +
        2 * bogD A B * fmsGamma A B L * (1 + bogAlpha A B) * (fmsLin1 M φ + fmsLin2 M φ) +
        2 * bogD A B * (fmsGamma A B L) ^ 2 * rectNorm M φ := by
            ring
    _ = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) +
        2 * L * (fmsLin1 M φ + fmsLin2 M φ) +
        2 * bogD A B * (fmsGamma A B L) ^ 2 * rectNorm M φ := by
            have hc2 : 2 * bogD A B * fmsGamma A B L * (1 + bogAlpha A B) = 2 * L := by
              calc
                2 * bogD A B * fmsGamma A B L * (1 + bogAlpha A B)
                    = 2 * (bogD A B * fmsGamma A B L * (1 + bogAlpha A B)) := by ring
                _ = 2 * L := by rw [hc]
            rw [hc2]


/-- the full shifted RHS of eq:BogIdentity reduces to the unshifted identity plus 2L·Lin -/
lemma fms_rhs_eq {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    bogD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ)) -
        (A - bogS A B) * rectNorm M φ - (2 * L ^ 2 / (A + B)) * rectNorm M φ
      = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) -
        (A - bogS A B) * rectNorm M φ + 2 * L * (fmsLin1 M φ + fmsLin2 M φ) := by
  calc
    bogD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ)) -
        (A - bogS A B) * rectNorm M φ - (2 * L ^ 2 / (A + B)) * rectNorm M φ
        = (bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) +
            2 * L * (fmsLin1 M φ + fmsLin2 M φ) +
            2 * bogD A B * (fmsGamma A B L) ^ 2 * rectNorm M φ) -
          (A - bogS A B) * rectNorm M φ - (2 * L ^ 2 / (A + B)) * rectNorm M φ := by
            rw [fms_expand hA hB hAB M hφ]
    _ = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) -
        (A - bogS A B) * rectNorm M φ + 2 * L * (fmsLin1 M φ + fmsLin2 M φ) +
        (2 * bogD A B * (fmsGamma A B L) ^ 2 - 2 * L ^ 2 / (A + B)) * rectNorm M φ := by
            ring
    _ = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) -
        (A - bogS A B) * rectNorm M φ + 2 * L * (fmsLin1 M φ + fmsLin2 M φ) := by
            rw [fms_sq_coeff hA hB hAB]
            ring

/-- THE 2-MODE BOGOLIUBOV IDENTITY WITH LINEAR TERM (FS eq:BogIdentity, κ = L ∈ ℝ) -/

theorem fms_shift_identity {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    fsQuadLin A B L M φ =
      bogD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ)) -
        (A - bogS A B) * rectNorm M φ - (2 * L ^ 2 / (A + B)) * rectNorm M φ := by
  calc
    fsQuadLin A B L M φ = fsQuad A B M φ + 2 * L * (fmsLin1 M φ + fmsLin2 M φ) := by rfl
    _ = bogD A B * (rectNorm M (bPlus (bogAlpha A B) φ) + rectNorm M (bMinus (bogAlpha A B) φ)) -
        (A - bogS A B) * rectNorm M φ + 2 * L * (fmsLin1 M φ + fmsLin2 M φ) := by
          rw [fock_two_mode_identity hA hB M hφ]
    _ = bogD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ)) -
        (A - bogS A B) * rectNorm M φ - (2 * L ^ 2 / (A + B)) * rectNorm M φ := by
          rw [fms_rhs_eq hA hB hAB M hφ]

/-- GROUND ESTIMATE WITH LINEAR TERM (FS eq:BogIneq, κ = L ∈ ℝ) -/

theorem fms_ground_estimate {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    - ((A - bogS A B) + 2 * L ^ 2 / (A + B)) * rectNorm M φ ≤ fsQuadLin A B L M φ := by
  rw [fms_shift_identity hA hB hAB M hφ]
  have hD : 0 < bogD A B := bogD_pos hA hB
  have hn1 : 0 ≤ rectNorm M (fmsBPlus A B L φ) := rectNorm_nonneg M (fmsBPlus A B L φ)
  have hn2 : 0 ≤ rectNorm M (fmsBMinus A B L φ) := rectNorm_nonneg M (fmsBMinus A B L φ)
  have hnn : 0 ≤ bogD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ)) :=
    mul_nonneg (le_of_lt hD) (add_nonneg hn1 hn2)
  nlinarith
end BoseGases
end Submission
