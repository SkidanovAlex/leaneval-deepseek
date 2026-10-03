/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Peluse.Tools.bilinPair_AhalfZ_le
import Submission.Work.Peluse.Tools.bilinPair_AhalfZ_eq
import Submission.Work.Peluse.Tools.LambdaZ_half_decomp

/-!
# The elementary steps of the reduction of `AreaA2` to `PeluseCrux`

This module contains the three *elementary* steps of the reduction (everything else is the
content of the deep `PeluseCrux` of `Nodes.lean`):

* `AhalfZ_pairing_bound` — the trivial bound `δ N^d ≤ |⟨Ã_N(f,g),h⟩| ≤ 2N₀+1`;  it shows that in
  the non-degenerate case the scale imbalance `N^d/N₀` is at most `δ^{-1}` (up to a constant).
* `half_le_of_pairing` — `‖ΛHalfZ‖ ≥ ε` bounds `‖ΛZ N₀ N‖` or `‖ΛZ N₀ (N/2)‖` from below: the
  half-average is a full average minus half of the average over `[N/2]` (this is the step that
  replaces the paper's upper-half average by a full average `∑_{y ∈ [M]}`).
* the two versions of the bridge between `⟨Ã_N(f,g),h⟩` and `ΛHalfZ` (one for the bound, one for
  the halving).
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

open Work.Analysis.InverseTheory (AhalfZ bilinPair)

noncomputable section

/-- **The trivial bound.**  For `1`-bounded `f, g, h` with `h` supported in `[-N₀,N₀]`,
`|⟨Ã_N(f,g), h⟩| ≤ 2N₀+1`.  Consequently a correlation of size `δ N^d` forces
`δ N^d ≤ 2N₀+1`. -/
theorem AhalfZ_pairing_bound {N₀ N : ℕ} (hN : 0 < N) (P : Polynomial ℤ) (f g h : ℤ → ℂ)
    (hs0 : SupportIn h N₀) (hs1 : SupportIn f N₀) (hs2 : SupportIn g N₀)
    (hb0 : ∀ x : ℤ, ‖h x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f x‖ ≤ 1) (hb2 : ∀ x : ℤ, ‖g x‖ ≤ 1)
    {δ : ℝ} (hδ : δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖) :
    δ * (N : ℝ) ^ P.natDegree ≤ 2 * (N₀ : ℝ) + 1 :=
  hδ.trans (Tools.bilinPair_AhalfZ_le hN P f g h hs0 hs1 hs2 hb0 hb1 hb2)

/-- **The halving step.**  The upper-half average is a full average minus (at least) half of the
average over `[N/2]`:
`Λ^{N₀,N}_{X,P} = Λ^{(1/2)}_{N₀,N} + θ Λ^{N₀,⌊N/2⌋}_{X,P}` with `‖θ‖ ≤ 1/2` (Lemma
`LambdaZ_half_decomp`).  Hence a lower bound `ε` for the half-average gives a lower bound `ε/2`
for `ΛZ N₀ N` or `ε` for `ΛZ N₀ (N/2)`. -/
theorem half_le_of_pairing {N₀ M : ℕ} (hN₀ : 0 < N₀) (hM : 0 < M) (P : Polynomial ℤ)
    (f₀ f₁ f₂ : ℤ → ℂ) (hs0 : SupportIn f₀ N₀) (hs1 : SupportIn f₁ N₀) (hs2 : SupportIn f₂ N₀)
    {ε : ℝ}
    (hε : ε ≤ ‖LambdaHalfZ N₀ M P f₀ f₁ f₂‖) :
    ε / 2 ≤ ‖LambdaZ N₀ M P f₀ f₁ f₂‖ ∨ ε ≤ ‖LambdaZ N₀ (M / 2) P f₀ f₁ f₂‖ := by
  obtain ⟨θ, hθ, hdecomp⟩ := Tools.LambdaZ_half_decomp hN₀ hM P f₀ f₁ f₂ hs0 hs1 hs2
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hkey : LambdaHalfZ N₀ M P f₀ f₁ f₂
      = LambdaZ N₀ M P f₀ f₁ f₂ - θ * LambdaZ N₀ (M / 2) P f₀ f₁ f₂ := by
    rw [hdecomp]; ring
  have hbd : ‖LambdaHalfZ N₀ M P f₀ f₁ f₂‖
      ≤ ‖LambdaZ N₀ M P f₀ f₁ f₂‖ + (1/2) * ‖LambdaZ N₀ (M / 2) P f₀ f₁ f₂‖ := by
    rw [hkey]
    calc ‖LambdaZ N₀ M P f₀ f₁ f₂ - θ * LambdaZ N₀ (M / 2) P f₀ f₁ f₂‖
        ≤ ‖LambdaZ N₀ M P f₀ f₁ f₂‖ + ‖θ * LambdaZ N₀ (M / 2) P f₀ f₁ f₂‖ := norm_sub_le _ _
      _ = ‖LambdaZ N₀ M P f₀ f₁ f₂‖ + ‖θ‖ * ‖LambdaZ N₀ (M / 2) P f₀ f₁ f₂‖ := by rw [norm_mul]
      _ ≤ ‖LambdaZ N₀ M P f₀ f₁ f₂‖ + (1/2) * ‖LambdaZ N₀ (M / 2) P f₀ f₁ f₂‖ := by
          have h0 : (0:ℝ) ≤ ‖LambdaZ N₀ (M / 2) P f₀ f₁ f₂‖ := norm_nonneg _
          nlinarith [hθ]
  nlinarith [hε, hbd, h1, h2]

/-- **The bridge.**  `⟨Ã_N(f,g), h⟩ = N₀ · ΛHalfZ N₀ N P h f g`, hence
`ε N₀ ≤ |⟨Ã_N(f,g),h⟩|` implies `ε ≤ ‖ΛHalfZ N₀ N P h f g‖`. -/
theorem le_LambdaHalfZ_of_pairing {N₀ N : ℕ} (hN₀ : 0 < N₀) (hN : 0 < N) (P : Polynomial ℤ)
    (f g h : ℤ → ℂ) (hs0 : SupportIn h N₀) (hs1 : SupportIn f N₀) (hs2 : SupportIn g N₀)
    {ε : ℝ} (hε : ε * (N₀ : ℝ) ≤ ‖bilinPair (AhalfZ N P f g) h‖) :
    ε ≤ ‖LambdaHalfZ N₀ N P h f g‖ := by
  have hbridge := Tools.bilinPair_AhalfZ_eq hN₀ hN P f g h hs0 hs1 hs2
  have hnorm : ‖bilinPair (AhalfZ N P f g) h‖
      = (N₀ : ℝ) * ‖LambdaHalfZ N₀ N P h f g‖ := by
    rw [hbridge, norm_mul, Complex.norm_natCast]
  have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN₀
  rw [hnorm] at hε
  nlinarith [hε, hN₀pos, norm_nonneg (LambdaHalfZ N₀ N P h f g)]

end

end Work.Peluse
