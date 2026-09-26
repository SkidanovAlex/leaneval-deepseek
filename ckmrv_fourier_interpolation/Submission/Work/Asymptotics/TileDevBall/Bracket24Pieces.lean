/-
# The monomial pieces of the `d = 24` tile bracket

The `BBdd 0 0` bounds for the summands of

  `brMinus ℓ 24 τ ζ + Sh τ ζ · br0 24 ℓ τ ζ = kmfd_BR ℓ τ ζ + kmfd_dev ℓ τ ζ`

(`Work.Asymptotics.kmfd_bracket_decomp`), where `kmfd_BR = Σ_{k=1}^8 Ept^k · kmfd_c_k`
(`Work.Asymptotics.kmfd_BR_expansion`); see `TileDevBall/Bracket24Aux.lean` for the
`BBdd` calculus and the atom inventory.

Every piece below is a product of atoms with exponent pair `(c, d)`, `c + d ≤ 0`, which
`BBdd.toGood` collapses using the ball inequality `Im ζ ≥ Im (S • w) - 29/20`.
-/
import Mathlib
import Submission.Work.Asymptotics.TileDevBall.Bracket24Aux

set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

open Work.Kernels
open Work.Residues (Ept)

/-! ## §1  The expansion coefficients `kmfd_c_k` -/

/-- The `k = 1` piece `Ept · c₁` of `kmfd_BR`. -/
lemma c1Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ * Work.Asymptotics.kmfd_c1 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 1 * (jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw))) :=
    ((zEptB 1).mul (tjDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 1 * (jInvariantFun ((n:ℝ)+ᵥw)
        * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
            - psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)))) :=
    ((zEptB 1).mul ((tj n hn).mul (tPSB ℓ n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 1 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 1).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h4 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 1 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 1).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h5 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 1 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 1).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (addGood (addGood (BBdd.const_mul (27648:ℂ) h1)
    (BBdd.const_mul (24:ℂ) h2)) (BBdd.const_mul (-20570112:ℂ) h3))
    (BBdd.const_mul (15744:ℂ) h4)) (BBdd.const_mul (-29568:ℂ) h5)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c1]
  ring

/-- The `k = 2` piece `Ept² · c₂` of `kmfd_BR`. -/
lemma c2Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 2 * Work.Asymptotics.kmfd_c2 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 2 * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n:ℝ)+ᵥw)
        * (jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw))))) :=
    ((zEptB 2).mul ((zXcB ℓ).mul ((tj n hn).mul (tjDB n hn)))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 2 * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw)))) :=
    ((zEptB 2).mul ((zXcB ℓ).mul (tjDB n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 2 * (Compact.Xc ℓ ζ
      * DeltaFun ((n:ℝ)+ᵥw))) :=
    ((zEptB 2).mul ((zXcB ℓ).mul (tDB n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h4 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 2
      * (jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw))) :=
    ((zEptB 2).mul (tjDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h5 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 2
      * (jInvariantFun ((n:ℝ)+ᵥw) * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)))) :=
    ((zEptB 2).mul ((tj n hn).mul (tP2E10B ℓ n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h6 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 2
      * (jInvariantFun ((n:ℝ)+ᵥw) * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)))) :=
    ((zEptB 2).mul ((tj n hn).mul (tP4E8B ℓ n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h7 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 2 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 2).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h8 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 2 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 2).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h9 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 2 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 2).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (addGood (addGood (addGood (addGood (addGood (addGood
    (BBdd.const_mul (-3456:ℂ) h1) (BBdd.const_mul (4976640:ℂ) h2))
    (BBdd.const_mul (-1192402944:ℂ) h3)) (BBdd.const_mul (41472:ℂ) h4))
    (BBdd.const_mul (1080:ℂ) h5)) (BBdd.const_mul (648:ℂ) h6))
    (BBdd.const_mul (31850496:ℂ) h7)) (BBdd.const_mul (-651456:ℂ) h8))
    (BBdd.const_mul (-551232:ℂ) h9)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c2]
  ring

/-- The `k = 3` piece `Ept³ · c₃` of `kmfd_BR`. -/
lemma c3Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 3 * Work.Asymptotics.kmfd_c3 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 3 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 3).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 3 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 3).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 3 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 3).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (BBdd.const_mul (-5271257088:ℂ) h1)
    (BBdd.const_mul (3142656:ℂ) h2)) (BBdd.const_mul (-3142656:ℂ) h3)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c3]
  ring

/-- The `k = 4` piece `Ept⁴ · c₄` of `kmfd_BR`. -/
lemma c4Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 4 * Work.Asymptotics.kmfd_c4 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 4 * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw)))) :=
    ((zEptB 4).mul ((zXcB ℓ).mul (tjDB n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 4 * (Compact.Xc ℓ ζ
      * DeltaFun ((n:ℝ)+ᵥw))) :=
    ((zEptB 4).mul ((zXcB ℓ).mul (tDB n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 4 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 4).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h4 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 4 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 4).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h5 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 4 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 4).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (addGood (addGood (BBdd.const_mul (597196800:ℂ) h1)
    (BBdd.const_mul (-382205952000:ℂ) h2)) (BBdd.const_mul (8623521792:ℂ) h3))
    (BBdd.const_mul (-178689024:ℂ) h4)) (BBdd.const_mul (-119909376:ℂ) h5)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c4]
  ring

/-- The `k = 5` piece `Ept⁵ · c₅` of `kmfd_BR`. -/
lemma c5Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 5 * Work.Asymptotics.kmfd_c5 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 5 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 5).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 5 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 5).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 5 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 5).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (BBdd.const_mul (-496867737600:ℂ) h1)
    (BBdd.const_mul (287539200:ℂ) h2)) (BBdd.const_mul (-287539200:ℂ) h3)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c5]
  ring

/-- The `k = 6` piece `Ept⁶ · c₆` of `kmfd_BR`. -/
lemma c6Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 6 * Work.Asymptotics.kmfd_c6 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 6 * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw)))) :=
    ((zEptB 6).mul ((zXcB ℓ).mul (tjDB n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 6 * (Compact.Xc ℓ ζ
      * DeltaFun ((n:ℝ)+ᵥw))) :=
    ((zEptB 6).mul ((zXcB ℓ).mul (tDB n hn))).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 6 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 6).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h4 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 6 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 6).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h5 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 6 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 6).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (addGood (addGood (BBdd.const_mul (47775744000:ℂ) h1)
    (BBdd.const_mul (-34398535680000:ℂ) h2)) (BBdd.const_mul (917294284800:ℂ) h3))
    (BBdd.const_mul (-15460761600:ℂ) h4)) (BBdd.const_mul (-8427110400:ℂ) h5)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c6]
  ring

/-- The `k = 7` piece `Ept⁷ · c₇` of `kmfd_BR`. -/
lemma c7Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 7 * Work.Asymptotics.kmfd_c7 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 7 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 7).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 7 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 7).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 7 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 7).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (BBdd.const_mul (-9172942848000:ℂ) h1)
    (BBdd.const_mul (5308416000:ℂ) h2)) (BBdd.const_mul (-5308416000:ℂ) h3)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c7]
  ring

/-- The `k = 8` piece `Ept⁸ · c₈` of `kmfd_BR`. -/
lemma c8Piece (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 8 * Work.Asymptotics.kmfd_c8 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) => Ept ζ ^ 8 * DeltaFun ((n:ℝ)+ᵥw)) :=
    ((zEptB 8).mul (tDB n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 8 * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 8).mul (tP2E10B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w ζ : ℍ) =>
      Ept ζ ^ 8 * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((zEptB 8).mul (tP4E8B ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (BBdd.const_mul (27518828544000:ℂ) h1)
    (BBdd.const_mul (-15925248000:ℂ) h2)) (BBdd.const_mul (15925248000:ℂ) h3)).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_c8]
  ring


/-! ## §2  The composite `τ`-atoms of `kmfd_dev` -/

/-- `1728 - j(τ)` at `τ = n +ᵥ w`. -/
lemma oneSevenTwoEight_sub_j (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (2 * Real.pi) 0 (fun (w : ℍ) (_ : ℍ) =>
      (1728:ℂ) - jInvariantFun ((n:ℝ)+ᵥw)) := by
  have h := (BBdd.const (1728 : ℂ)).sub (tj n hn)
  exact h.mono (c' := 2 * Real.pi) (d' := 0)
    (max_le (by linarith [Real.pi_pos]) le_rfl) (max_le le_rfl le_rfl)

/-- `Nf`, the coefficient of `e^{-2}` in `br0 24`, is polynomially bounded. -/
lemma NfB (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) => Compact.Nf ℓ ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd 0 0 (fun (w ζ : ℍ) =>
      DeltaFun ((n:ℝ)+ᵥw) * Compact.Xc ℓ ζ) :=
    ((tDB n hn).mul (zXcB ℓ)).monoZero
      (by push_cast; nlinarith [Real.pi_pos]) (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w _ : ℍ) => DeltaFun ((n:ℝ)+ᵥw)) :=
    (tDB n hn).monoZero
      (by push_cast; nlinarith [Real.pi_pos]) (by push_cast; nlinarith [Real.pi_pos])
  have h3 : BBdd 0 0 (fun (w _ : ℍ) => psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
      - psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) :=
    (tPSB ℓ n hn).monoZero
      (by push_cast; nlinarith [Real.pi_pos]) (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (BBdd.const_mul (-3456:ℂ) h1) (BBdd.const_mul (3456:ℂ) h2))
    (BBdd.const_mul (3:ℂ) h3)).congr ?_
  funext w ζ
  simp only [Compact.Nf]
  ring

/-- `Mf`, the `e^{-2}`-free part of `br0 24`, lifted to the pair `(2π, 0)`. -/
lemma MfB (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (2 * Real.pi) 0 (fun (w ζ : ℍ) => Compact.Mf ℓ ((n:ℝ)+ᵥw)) := by
  have h1 : BBdd (2 * Real.pi) 0 (fun (w _ : ℍ) => DeltaFun ((n:ℝ)+ᵥw)) :=
    (tDB n hn).mono (c' := 2 * Real.pi) (d' := 0)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h2 : BBdd (2 * Real.pi) 0 (fun (w _ : ℍ) =>
      jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw)) :=
    (tjDB n hn).mono (c' := 2 * Real.pi) (d' := 0)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h3 : BBdd (2 * Real.pi) 0 (fun (w _ : ℍ) =>
      psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) :=
    (tP2E10B ℓ n hn).mono (c' := 2 * Real.pi) (d' := 0)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h4 : BBdd (2 * Real.pi) 0 (fun (w _ : ℍ) =>
      psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)) :=
    (tP4E8B ℓ n hn).mono (c' := 2 * Real.pi) (d' := 0)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h5 : BBdd (2 * Real.pi) 0 (fun (w _ : ℍ) => jInvariantFun ((n:ℝ)+ᵥw)
      * (psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))) :=
    ((tj n hn).mul (tP2E10B ℓ n hn)).mono (c' := 2 * Real.pi) (d' := 0)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h6 : BBdd (2 * Real.pi) 0 (fun (w _ : ℍ) => jInvariantFun ((n:ℝ)+ᵥw)
      * (psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))) :=
    ((tj n hn).mul (tP4E8B ℓ n hn)).mono (c' := 2 * Real.pi) (d' := 0)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  refine (BBdd.addS (BBdd.addS (BBdd.addS (BBdd.addS (BBdd.addS
    (BBdd.addS (BBdd.const_mul (-41472:ℂ) h1) (BBdd.const_mul (-3456:ℂ) h2))
    (BBdd.const_mul (2654208:ℂ) h1)) (BBdd.const_mul (3:ℂ) h5))
    (BBdd.const_mul (-1152:ℂ) h3)) (BBdd.const_mul (2880:ℂ) h4))
    (BBdd.const_mul (-3:ℂ) h6)).congr ?_
  funext w ζ
  simp only [Compact.Mf]
  ring

/-- `B24 = -3456 Δ(τ) + 2(ψ₄E₈ - ψ₂E₁₀)(τ)` is polynomially bounded. -/
lemma B24B (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) => Compact.B24 ℓ ((n:ℝ)+ᵥw)) := by
  have h1 : BBdd 0 0 (fun (w _ : ℍ) => DeltaFun ((n:ℝ)+ᵥw)) :=
    (tDB n hn).monoZero
      (by push_cast; nlinarith [Real.pi_pos]) (by push_cast; nlinarith [Real.pi_pos])
  have h2 : BBdd 0 0 (fun (w _ : ℍ) => psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
      - psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) :=
    (tPSB ℓ n hn).monoZero
      (by push_cast; nlinarith [Real.pi_pos]) (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (BBdd.const_mul (-3456:ℂ) h1) (BBdd.const_mul (-2:ℂ) h2)).congr ?_
  funext w ζ
  simp only [Compact.B24]
  ring

/-- `dSh = (E₄(ζ)³ - (1+240E²)³) - j(τ)(Δ(ζ) - E²)` is bounded by the pair `(2π, -4π)`. -/
lemma dShB (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (2 * Real.pi) (-(4 * Real.pi)) (fun (w ζ : ℍ) =>
      Work.Asymptotics.kmfd_dSh ((n:ℝ)+ᵥw) ζ) := by
  have h1 : BBdd (2 * Real.pi) (-(4 * Real.pi)) (fun (_ : ℍ) (z : ℍ) =>
      E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z) :=
    (zE4cdevB ℓ).mono (c' := 2 * Real.pi) (d' := -(4 * Real.pi))
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h2 : BBdd (2 * Real.pi) (-(4 * Real.pi)) (fun (w ζ : ℍ) =>
      jInvariantFun ((n:ℝ)+ᵥw) * (DeltaFun ζ - Ept ζ ^ 2)) :=
    ((tj n hn).mul (zDdiffB ℓ)).mono (c' := 2 * Real.pi) (d' := -(4 * Real.pi))
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  refine (BBdd.subS h1 h2).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_dSh]

/-- `B = -Mf + (720 - j(τ))·Nf` is bounded by the pair `(2π, 0)`. -/
lemma BB (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (2 * Real.pi) 0 (fun (w ζ : ℍ) =>
      - Compact.Mf ℓ ((n:ℝ)+ᵥw)
        + (720 - jInvariantFun ((n:ℝ)+ᵥw)) * Compact.Nf ℓ ((n:ℝ)+ᵥw) ζ) := by
  have hA : BBdd (2 * Real.pi) 0 (fun (w ζ : ℍ) =>
      (-1:ℂ) * Compact.Mf ℓ ((n:ℝ)+ᵥw)) := BBdd.const_mul (-1:ℂ) (MfB ℓ n hn)
  have hB : BBdd (2 * Real.pi) 0 (fun (w ζ : ℍ) =>
      (-1:ℂ) * (jInvariantFun ((n:ℝ)+ᵥw) * Compact.Nf ℓ ((n:ℝ)+ᵥw) ζ)) :=
    BBdd.const_mul (-1:ℂ) (((tj n hn).mul (NfB ℓ n hn)).mono
      (c' := 2 * Real.pi) (d' := 0) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hC : BBdd (2 * Real.pi) 0 (fun (w ζ : ℍ) =>
      (720:ℂ) * Compact.Nf ℓ ((n:ℝ)+ᵥw) ζ) :=
    BBdd.const_mul (720:ℂ) ((NfB ℓ n hn).mono (c' := 2 * Real.pi) (d' := 0)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  refine (BBdd.addS (BBdd.addS hA hC) hB).congr ?_
  funext w ζ
  ring

/-! ## §3  The pieces of `kmfd_dev` -/

/-- `Dref · (A24 - A24ref)`. -/
lemma devDrefdA (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Compact.Dref ζ * Work.Asymptotics.kmfd_dA ℓ ((n:ℝ)+ᵥw) ζ) := by
  have a1 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.Dref ζ * (DeltaFun ((n:ℝ)+ᵥw)
      * (Compact.dE14 ζ * ℓ.L ζ))) :=
    ((zDrefB ℓ).mul ((tDB n hn).mul ((zdE14B ℓ).mul (zLB ℓ)))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  have a2 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.Dref ζ * (DeltaFun ((n:ℝ)+ᵥw)
      * (Compact.E14ref ζ * Compact.dL ℓ ζ))) :=
    ((zDrefB ℓ).mul ((tDB n hn).mul ((zE14refB ℓ).mul (zdLB ℓ)))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  have a3 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.Dref ζ * ((psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
      - psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) * (Compact.dE10 ζ * (UFun ζ ^ 2 - VFun ζ ^ 2)))) :=
    ((zDrefB ℓ).mul ((tPSB ℓ n hn).mul ((zdE10B ℓ).mul (zD2B ℓ)))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  have a4 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.Dref ζ * ((psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
      - psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) * (Compact.E10ref ζ * Compact.dD2 ζ))) :=
    ((zDrefB ℓ).mul ((tPSB ℓ n hn).mul ((zE10refB ℓ).mul (zdD2B ℓ)))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (addGood (BBdd.const_mul (-3456:ℂ) a1) (BBdd.const_mul (-3456:ℂ) a2))
    (addGood (BBdd.const_mul (1:ℂ) a3) (BBdd.const_mul (1:ℂ) a4))).congr ?_
  funext w ζ
  simp only [Work.Asymptotics.kmfd_dA]
  ring

/-- `dDelta · A24`. -/
lemma devDA24 (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Compact.dDelta ζ * Compact.A24 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have b1 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.dDelta ζ
      * (DeltaFun ((n:ℝ)+ᵥw) * (E14Fun ζ * ℓ.L ζ))) :=
    ((zdDeltaB ℓ).mul ((tDB n hn).mul ((zE14).mul (zLB ℓ)))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  have b2 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.dDelta ζ
      * ((psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
          - psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw))
        * (E10Fun ζ * (UFun ζ ^ 2 - VFun ζ ^ 2)))) :=
    ((zdDeltaB ℓ).mul ((tPSB ℓ n hn).mul ((zE10).mul (zD2B ℓ)))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood (BBdd.const_mul (-3456:ℂ) b1) (BBdd.const_mul (1:ℂ) b2)).congr ?_
  funext w ζ
  simp only [Compact.A24]
  ring

/-- `C24 · dW`. -/
lemma devC24dW (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Compact.C24 ℓ ((n:ℝ)+ᵥw) * Compact.dW ζ) := by
  have c1 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.dW ζ
      * ((psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) * jInvariantFun ((n:ℝ)+ᵥw))) :=
    ((zdWB ℓ).mul ((tP2E10B ℓ n hn).mul (tj n hn))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  have c2 : BBdd 0 0 (fun (w ζ : ℍ) => Compact.dW ζ
      * ((psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw))
        * ((1728:ℂ) - jInvariantFun ((n:ℝ)+ᵥw)))) :=
    ((zdWB ℓ).mul ((tP4E8B ℓ n hn).mul (oneSevenTwoEight_sub_j n hn))).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood c1 c2).congr ?_
  funext w ζ
  simp only [Compact.C24]
  ring

/-- `(j(τ) - jref ζ) · dW · B24`. -/
lemma devJdWB (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      (jInvariantFun ((n:ℝ)+ᵥw) - Work.Asymptotics.kmfd_jref ζ)
        * Compact.dW ζ * Compact.B24 ℓ ((n:ℝ)+ᵥw)) := by
  have d1 : BBdd 0 0 (fun (w ζ : ℍ) => ((jInvariantFun ((n:ℝ)+ᵥw) * Compact.dW ζ)
      * Compact.B24 ℓ ((n:ℝ)+ᵥw))) :=
    (((tj n hn).mul (zdWB ℓ)).mul (B24B ℓ n hn)).toGood
      (by push_cast; nlinarith [Real.pi_pos])
  have d2 : BBdd 0 0 (fun (w ζ : ℍ) => ((Work.Asymptotics.kmfd_jref ζ * Compact.dW ζ)
      * Compact.B24 ℓ ((n:ℝ)+ᵥw))) :=
    (((zjrefB ℓ).mul (zdWB ℓ)).mul (B24B ℓ n hn)).monoZero
      (by push_cast; nlinarith [Real.pi_pos]) (by push_cast; nlinarith [Real.pi_pos])
  refine (subGood d1 d2).congr ?_
  funext w ζ
  ring

/-- `(j(ζ) - jref ζ) · W · B24`. -/
lemma devJdevWB (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      (jInvariantFun ζ - Work.Asymptotics.kmfd_jref ζ) * WFun ζ
        * Compact.B24 ℓ ((n:ℝ)+ᵥw)) := by
  have e1 : BBdd 0 0 (fun (w ζ : ℍ) =>
      ((jInvariantFun ζ - Work.Asymptotics.kmfd_jref ζ) * WFun ζ)
        * Compact.B24 ℓ ((n:ℝ)+ᵥw)) :=
    (((zjdevB ℓ).mul (zWB ℓ)).mul (B24B ℓ n hn)).monoZero
      (by push_cast; nlinarith [Real.pi_pos]) (by push_cast; nlinarith [Real.pi_pos])
  refine e1.congr ?_
  funext w ζ
  ring

/-- `dSh · br0 24`. -/
lemma devdShbr0 (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w ζ : ℍ) =>
      Work.Asymptotics.kmfd_dSh ((n:ℝ)+ᵥw) ζ * Compact.br0 24 ℓ ((n:ℝ)+ᵥw) ζ) := by
  have hneg : BBdd 0 0 (fun (w ζ : ℍ) => -Compact.Nf ℓ ((n:ℝ)+ᵥw) ζ) :=
    (NfB ℓ n hn).negGood
  have hA : BBdd 0 0 (fun (w ζ : ℍ) => Work.Asymptotics.kmfd_dSh ((n:ℝ)+ᵥw) ζ
      * (-Compact.Nf ℓ ((n:ℝ)+ᵥw) ζ * Compact.einv2 ζ)) :=
    ((dShB ℓ n hn).mul (hneg.mul zEinv2B)).toGood (by push_cast; nlinarith [Real.pi_pos])
  have hB : BBdd 0 0 (fun (w ζ : ℍ) => Work.Asymptotics.kmfd_dSh ((n:ℝ)+ᵥw) ζ
      * (-Compact.Mf ℓ ((n:ℝ)+ᵥw)
        + (720 - jInvariantFun ((n:ℝ)+ᵥw)) * Compact.Nf ℓ ((n:ℝ)+ᵥw) ζ)) :=
    ((dShB ℓ n hn).mul (BB ℓ n hn)).toGood (by push_cast; nlinarith [Real.pi_pos])
  refine (addGood hA hB).congr ?_
  funext w ζ
  rw [Compact.br0_24]
  ring

end Work.Asymptotics.TileDevBall
