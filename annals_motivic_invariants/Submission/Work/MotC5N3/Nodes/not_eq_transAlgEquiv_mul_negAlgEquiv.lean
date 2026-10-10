import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.negAlgEquiv_mul_transAlgEquiv
import Submission.Work.MotC2.transAlgEquiv_injective

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.Nodes
open WeierstrassCurve WeierstrassCurve.Affine

/-- **The projective fifth-torsion shift is not a reflection of the function field.**

Mathematics.  `Work.MotC2.transAlgEquiv E Q * Work.MotC2.negAlgEquiv E` is the reflection
`P ↦ Q - P` of the elliptic curve `E`, hence an involution in the automorphism group of `K̄(E)`.
Combined with `σS ^ 5 = 1` this forces `σS = σS ^ 5 = (σS ^ 2) ^ 2 * σS = σS`, i.e. `σS = 1`.

`Work.MotC5N3.KleinData.ShiftOf D σS` then reads `κ i = λ κ (i+1)` with `λ ≠ 0`, where
`κ i = kleinCoord D (Work.MotC5N3.KbA K) i`.  Iterating around the `5`-cycle gives `κ 0 = λ ^ 5 κ 0`, so
`λ ^ 5 = 1` as soon as some `κ i` is non-zero; and if `κ 0 = 0` then the ratio `κ i / κ 0` used by
`Work.MotV5.KleinData.Nonconstant` vanishes, hence is algebraic.  In characteristic `5`,
`λ ^ 5 = 1` forces `λ = 1` (`(λ - 1) ^ 5 = λ ^ 5 - 1 = 0`), so all Klein coordinates coincide and
`κ i₀ / κ 0 = 1` is algebraic — contradicting `Nonconstant D`. -/
theorem not_eq_transAlgEquiv_mul_negAlgEquiv (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]
    (D : Work.MotV.KleinData 𝕜) (hNon : Work.MotV5.KleinData.Nonconstant D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hpow : σS ^ 5 = 1) (hσS : Work.MotC5N3.KleinData.ShiftOf D σS)
    [DecidableEq (Work.MotC5N3.KbA K)] [hEll : (D.E.baseChange (Work.MotC5N3.KbA K)).IsElliptic]
    (Q : (D.E.baseChange (Work.MotC5N3.KbA K)).toAffine.Point)
    (hQ : σS = Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q *
      Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K))) : False := by
  -- Abbreviate the Klein coordinates and the base-changed curve.
  let κ : Fin 5 → Work.MotC5N3.OmA K D := fun i => Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
  -- The reflection `τ_Q ∘ [-1]` is an involution.
  have hn : Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) *
      Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) = 1 :=
    Work.MotC2.negAlgEquiv_mul_self _
  have htt : Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q *
      Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) (-Q) = 1 := by
    rw [← Work.MotC2.transAlgEquiv_add, add_neg_cancel, Work.MotC2.transAlgEquiv_zero]
  have hc := Work.MotC2.negAlgEquiv_mul_transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q
  have hinv : σS * σS = 1 := by
    rw [hQ]
    calc Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q *
            Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) *
          (Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q *
            Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)))
        = Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q *
            (Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) *
              Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q) *
            Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) := by group
      _ = Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q *
            (Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) (-Q) *
              Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K))) *
            Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) := by rw [hc]
      _ = (Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q *
            Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) (-Q)) *
            (Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) *
            Work.MotC2.negAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K))) := by group
      _ = 1 := by rw [htt, hn, one_mul]
  -- An involution of order dividing `5` is trivial.
  have h2 : σS ^ 2 = 1 := by rw [pow_two]; exact hinv
  have h59 : σS ^ 5 = σS := by
    have h : σS ^ 5 = (σS ^ 2) ^ 2 * σS ^ 1 := by
      rw [show (5:ℕ) = 4 + 1 by norm_num, pow_add, show (4:ℕ) = 2 * 2 by norm_num, pow_mul]
    rw [h, h2, one_pow, one_mul, pow_one]
  have hσS1 : σS = 1 := by rw [← h59, hpow]
  -- The shift relation with `σS = 1`.
  obtain ⟨lam, hlam0, hlam⟩ := hσS
  have hrel : ∀ i : Fin 5, κ i = lam * κ (i + 1) := by
    intro i
    have h := hlam i
    rw [hσS1, AlgEquiv.one_apply] at h
    exact h
  -- `Nonconstant` provides a transcendental Klein ratio.
  obtain ⟨i₀, hi₀⟩ := hNon
  have htr : Transcendental 𝕜 (κ i₀ / κ 0) := hi₀ (Work.MotC5N3.KbA K)
  -- In particular `κ 0 ≠ 0`: otherwise that ratio vanishes.
  have hκ0 : κ 0 ≠ 0 := by
    intro h0
    refine htr ?_
    rw [h0, div_zero]
    simpa using isAlgebraic_algebraMap (R := 𝕜) (A := Work.MotC5N3.OmA K D) (0 : 𝕜)
  -- Iterating the shift around the `5`-cycle: `κ 0 = λ ^ 5 κ 0`, hence `λ ^ 5 = 1`.
  have e01 : ((0 : Fin 5) + 1) = 1 := rfl
  have e12 : ((1 : Fin 5) + 1) = 2 := rfl
  have e23 : ((2 : Fin 5) + 1) = 3 := rfl
  have e34 : ((3 : Fin 5) + 1) = 4 := rfl
  have e40 : ((4 : Fin 5) + 1) = 0 := rfl
  have hiter0 : κ 0 = lam ^ 5 * κ 0 := by
    calc κ 0 = lam * κ 1 := by rw [hrel 0, e01]
      _ = lam * (lam * κ 2) := by rw [hrel 1, e12]
      _ = lam * (lam * (lam * κ 3)) := by rw [hrel 2, e23]
      _ = lam * (lam * (lam * (lam * κ 4))) := by rw [hrel 3, e34]
      _ = lam * (lam * (lam * (lam * (lam * κ 0)))) := by rw [hrel 4, e40]
      _ = lam ^ 5 * κ 0 := by ring
  have hlam5 : lam ^ 5 = 1 := by
    refine mul_right_cancel₀ hκ0 ?_
    rw [one_mul]; exact hiter0.symm
  -- `Work.MotC5N3.OmA K D` has characteristic `5`, so `λ ^ 5 = 1` forces `λ = 1`.
  haveI : CharP (Work.MotC5N3.OmA K D) 5 :=
    charP_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) 5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hlam1 : lam = 1 := by
    have h5 : (lam - 1) ^ 5 = 0 := by rw [sub_pow_char, hlam5]; simp
    exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 5) (by norm_num)).mp h5)
  -- All Klein coordinates coincide.
  have hrel1 : ∀ i : Fin 5, κ i = κ (i + 1) := by
    intro i; rw [hrel i, hlam1, one_mul]
  have hall : ∀ i : Fin 5, κ i = κ 0 := by
    intro i
    fin_cases i
    · rfl
    · exact (hrel1 0).symm
    · exact (hrel1 1).symm.trans (hrel1 0).symm
    · exact ((hrel1 2).symm.trans (hrel1 1).symm).trans (hrel1 0).symm
    · exact (((hrel1 3).symm.trans (hrel1 2).symm).trans (hrel1 1).symm).trans (hrel1 0).symm
  -- The transcendental ratio is `1`, an algebraic element: contradiction.
  refine htr ?_
  rw [hall i₀, div_self hκ0]
  simpa using isAlgebraic_algebraMap (R := 𝕜) (A := Work.MotC5N3.OmA K D) (1 : 𝕜)

end Work.MotC5N3.Nodes