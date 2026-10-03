import Submission.Work.Analysis.EndVar.Varp

/-!
# The pieces of the major arc part, indexed by quadruples

This module fixes the notation used by the reduction `majorArcVarEstimate_of_varp`
(`VarpStatement ⟹ ∃ Cv, MajorArcVarEstimate (majorArcPartR Pj P d C₀) p₁ p₂ p r Cv`).

The §5 decomposition of the major arc part of the halved average writes
`R_N(f,g) = Ã_N(Π_{≤l_{(N)},≤-Log N+l_{(N)}} f, Π_{≤l_{(N)},≤-dLog N+dl_{(N)}} g)`
as the quadruple sum

`R_N(f,g) = ∑_{l₁,l₂ ≤ l_{(N)}} ∑_{0 ≤ k₁,k₂ ≤ l_{(N)}} Ã_N(F^{0,l₁,k₁}_N f, G^{0,l₂,k₂}_N g)`

(the continuous frequencies `s₁ = k₁ ≥ 0` use the bottom scale `u = 0`).  The summands are the
families estimated by Theorem `varp` (`VarpStatement`), the clamping to the index set
`I^{max(l₁,l₂),k₁,k₂}` being exactly the hypothesis of `VarpStatement` at `u = 0`.

* `varpPiece Pj P d N f g l₁ l₂ k₁ k₂` — the unclamped summand
  `Ã_N(F^{0,l₁,k₁}_N f, G^{0,l₂,k₂}_N g)`;
* `varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂` — the summand clamped by the index set
  `I^{max(l₁,l₂),k₁,k₂} = {N : max(l₁,l₂), k₁, k₂ ≤ l_{(N)}}` along the sequence `a`, i.e.
  `n ↦ 1_{N(a n) ∈ I} Ã_{a n}(F^{0,l₁,k₁}_{N(a n)} f, G^{0,l₂,k₂}_{N(a n)} g)`; this is the family
  whose `ℓ^p(ℤ;V^r)` norm is bounded by `VarpStatement`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.Paraproduct (IWProjections)

/-- The unclamped summand of the §5 decomposition: the halved average of the two continuous
frequency pieces at the indices `(l₁,l₂,k₁,k₂)` (bottom scale `u = 0`). -/
def varpPiece (Pj : IWProjections) (P : ℤ[X]) (d : ℕ) (N : ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℂ :=
  AhalfR TZ N X P (Fpiece Pj 0 l₁ (k₁ : ℤ) (Nat.floor N) f)
    (Gpiece Pj (d : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor N) g)

/-- The summand of the §5 decomposition clamped to the index set
`I^{max(l₁,l₂),k₁,k₂}` of \eqref{index-def}: the family estimated by Theorem `varp`. -/
def varpCol (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) then
      varpPiece Pj P d (a n) f g l₁ l₂ k₁ k₂ x
    else 0

lemma varpCol_apply (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (x : ℤ) :
    varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x
      = if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) then
          varpPiece Pj P d (a n) f g l₁ l₂ k₁ k₂ x
        else 0 := rfl

/-- The membership in the index set `I^{max(l₁,l₂),k₁,k₂}` at a scale `N`, in terms of the four
natural indices. -/
lemma inIndexSet_iff_le {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {N : ℕ} :
    inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N ↔
      l₁ ≤ heightScale C₀ N ∧ l₂ ≤ heightScale C₀ N ∧
        k₁ ≤ heightScale C₀ N ∧ k₂ ≤ heightScale C₀ N := by
  have h1 : max (l₁ : ℤ) (l₂ : ℤ) ≤ (heightScale C₀ N : ℤ) ↔
      l₁ ≤ heightScale C₀ N ∧ l₂ ≤ heightScale C₀ N := by
    rw [max_le_iff]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨ha, hb⟩
      exact ⟨by omega, by omega⟩
  have h2 : (k₁ : ℤ) ≤ (heightScale C₀ N : ℤ) ↔ k₁ ≤ heightScale C₀ N := by omega
  have h3 : (k₂ : ℤ) ≤ (heightScale C₀ N : ℤ) ↔ k₂ ≤ heightScale C₀ N := by omega
  simp only [inIndexSet]
  tauto

/-- The clamped summand vanishes off the index set. -/
lemma varpCol_eq_zero {Pj : IWProjections} {P : ℤ[X]} {d C₀ : ℕ} {a : ℕ → ℝ≥0}
    {f g : ℤ → ℂ} {l₁ l₂ k₁ k₂ : ℕ} {n : ℕ} {x : ℤ}
    (h : ¬ (l₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧ l₂ ≤ heightScale C₀ (Nat.floor (a n)) ∧
        k₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧ k₂ ≤ heightScale C₀ (Nat.floor (a n)))) :
    varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  rw [varpCol_apply]
  rw [if_neg]
  simpa only [inIndexSet_iff_le] using h

/-- On the index set the clamped summand is the unclamped one. -/
lemma varpCol_eq_piece {Pj : IWProjections} {P : ℤ[X]} {d C₀ : ℕ} {a : ℕ → ℝ≥0}
    {f g : ℤ → ℂ} {l₁ l₂ k₁ k₂ : ℕ} {n : ℕ} {x : ℤ}
    (h : l₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧ l₂ ≤ heightScale C₀ (Nat.floor (a n)) ∧
        k₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧ k₂ ≤ heightScale C₀ (Nat.floor (a n))) :
    varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x
      = varpPiece Pj P d (a n) f g l₁ l₂ k₁ k₂ x := by
  rw [varpCol_apply, if_pos (by simpa only [inIndexSet_iff_le] using h)]

end

end Work.Analysis.EndVar
