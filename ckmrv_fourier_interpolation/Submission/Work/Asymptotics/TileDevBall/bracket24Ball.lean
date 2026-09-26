/-
# The `K_-^{(24)}` bracket bound on the cusp-`±1` tile ball

The target `Work.Asymptotics.TileDevBall.bracket24Ball` bounds

  `‖brMinus ℓ 24 τ ζ + Sh τ ζ · br0 24 ℓ τ ζ‖ ≤ C (scale w)^N`

on the tile ball `‖ζ - S • w‖ ≤ 29/20`, `3 ≤ Im ζ`, `w ∈ E = KEpsilon`, `τ = n +ᵥ w`, `n = ±1`.
By `Work.Asymptotics.Compact.tail_identity` the quantity being bounded is
`-3456π · Sh τ ζ · (K_-^{(24)}(τ,ζ) - 𝒢_-^{(24)}(τ,ζ))`, so this is the `K_-` analogue of
`Work.Asymptotics.TileDevBall.kplusDev24Ball`.

The proof uses the proved algebraic decomposition of the bracket

  `brMinus ℓ 24 + Sh · br0 24 = kmfd_BR ℓ + kmfd_dev ℓ`   (`kmfd_bracket_decomp`),

with the reference expansion `kmfd_BR = Σ_{k=1}^8 Ept^k · kmfd_c_k` (`kmfd_BR_expansion`); the
`τ`-atoms at `τ = n +ᵥ w` carry a factor `e^{2π Im (S • w)}` (the `j`-atoms) while the `ζ`-atoms
carry `e^{-kπ Im ζ}`, and each monomial of the two summands has total exponential weight `≤ 0`
because `Im ζ ≥ Im (S • w) - 29/20` on the ball (`Ball.im_ge`).  Everything is packaged in the
`BBdd` calculus of `TileDevBall/BallShape.lean`, with the atom inventory and the weight collapse
of `TileDevBall/Bracket24Aux.lean` and the monomial bounds of
`TileDevBall/Bracket24Pieces.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.KMFDZDevs
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.TileDevBall.BallShape
import Submission.Work.Asymptotics.TileDevBall.BallAtoms
import Submission.Work.Asymptotics.TileDevBall.Bracket24Aux
import Submission.Work.Asymptotics.TileDevBall.Bracket24Pieces

set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

open Work.Kernels

/-! ## The bracket identity -/

/-- **The `K_-^{(24)}` bracket** on the tile ball, in the `BBdd` calculus.  The summands
`kmfd_BR = Σ_k Ept^k·c_k` and `kmfd_dev` of `kmfd_bracket_decomp` are bounded piecewise
(`Bracket24Pieces.lean`). -/
theorem bracket24Ball_bdd (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Compact.brMinus ℓ 24 ((n:ℝ)+ᵥw) ζ
        + Compact.Sh ((n:ℝ)+ᵥw) ζ * Compact.br0 24 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have hBR : BBdd 0 0 (fun (w ζ : ℍ) => Work.Asymptotics.kmfd_BR ℓ ((n:ℝ)+ᵥw) ζ) := by
    have h1 := c1Piece ℓ n hn
    have h2 := c2Piece ℓ n hn
    have h3 := c3Piece ℓ n hn
    have h4 := c4Piece ℓ n hn
    have h5 := c5Piece ℓ n hn
    have h6 := c6Piece ℓ n hn
    have h7 := c7Piece ℓ n hn
    have h8 := c8Piece ℓ n hn
    refine (addGood (addGood (addGood (addGood (addGood (addGood (addGood h1 h2) h3) h4) h5)
      h6) h7) h8).congr ?_
    funext w ζ
    rw [Work.Asymptotics.kmfd_BR_expansion]
  have hdev : BBdd 0 0 (fun (w ζ : ℍ) => Work.Asymptotics.kmfd_dev ℓ ((n:ℝ)+ᵥw) ζ) := by
    have h1 := devDrefdA ℓ n hn
    have h2 := devDA24 ℓ n hn
    have h3 := devC24dW ℓ n hn
    have h4 := devJdWB ℓ n hn
    have h5 := devJdevWB ℓ n hn
    have h6 := devdShbr0 ℓ n hn
    refine (addGood (subGood (addGood (addGood (addGood h1 h2) h3) h4) h5) h6).congr ?_
    funext w ζ
    simp only [Work.Asymptotics.kmfd_dev]
  refine (addGood hBR hdev).congr ?_
  funext w ζ
  rw [Work.Asymptotics.kmfd_bracket_decomp]

/-! ## The target -/

set_option autoImplicit false in
theorem bracket24Ball (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane, ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          3 ≤ ζ.im →
          ‖Work.Asymptotics.Compact.brMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
            + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * Work.Asymptotics.Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) ζ‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := BBdd.exists_bound_zero (bracket24Ball_bdd ℓ 1 (Or.inl rfl))
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := BBdd.exists_bound_zero (bracket24Ball_bdd ℓ (-1) (Or.inr rfl))
  refine ⟨max C1 C2 + 1, max N1 N2, by positivity, le_max_of_le_left hN1, ?_⟩
  intro w hw n hn ζ hball him
  have hB : Ball w ζ := ⟨hw, hball, him⟩
  rcases hn with h | h
  · subst h
    exact le_trans (h1 w ζ hB)
      (le_mul_rpow_mono hB.one_le_scale (by linarith [le_max_left C1 C2]) (le_max_left N1 N2)
        (le_of_lt hC1))
  · subst h
    exact le_trans (h2 w ζ hB)
      (le_mul_rpow_mono hB.one_le_scale (by linarith [le_max_right C1 C2]) (le_max_right N1 N2)
        (le_of_lt hC2))

end Work.Asymptotics.TileDevBall
