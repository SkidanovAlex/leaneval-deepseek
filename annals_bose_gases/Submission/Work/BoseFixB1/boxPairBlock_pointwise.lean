import ChallengeDeps
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1.boxPInd_boxQInd_update
import Submission.Work.BoseFixB1S.PairValueAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The algebraic core

With `X := c₁c₂` the product of the two box indicators at the two slots of `p`, `F := Φ x`,
`W := wSmallPair M ℓ d u v (x p.1) (x p.2)` and `a₁ … a₄` the four slot means

`a₁ = V⁻¹∫_A Φ(x[p.1↦z])`,    `a₂ = V⁻¹∫_A Φ(x[p.2↦z])`,
`a₃ = V⁻²∫_A∫_A Φ(x[p.1↦z][p.2↦w])`,   `a₄ = V⁻²∫_A∫_A Φ(x[p.2↦z][p.1↦w])`,

the pair block `(Q + (P Q + Q P) + ω·P P)²w + 2(1−ω)(P Q + Q P)(P P)w` equals the displayed
difference of the three terms, where `w₁ = w(1−ω)` (the third term) and `w₂ = w₁(1+ω)` (the
second).  This is a plain polynomial identity: the two `F²` contributions agree, the two
`F·a₃·ω` contributions agree, and the rest collects to `X²Wa₃(1−ω)(2a₃ − 2a₃) = 0`. -/
private lemma pairBlock_alg (X F a1 a2 a3 a4 om W : ℝ) :
    (X * (F - a1 - a2 + a4) + (X * (a1 - a3) + X * (a2 - a4)) + om * (X * a3)) ^ 2 * W
      + 2 * (1 - om) * (X * (a1 - a3) + X * (a2 - a4)) * (X * a3) * W
    = (X * F) ^ 2 * W - (X * a3) ^ 2 * (W * (1 - om) * (1 + om))
      - 2 * (X * (F - a1 - a2 + a4) * (X * a3) * (W * (1 - om))) := by
  ring

theorem boxPairBlock_pointwise {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {p : Fin N × Fin N} (hp : p ∈ Submission.BoseGases.pairSet N)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.BoseFixB1.pairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.omC (Classical.choose h)) Φ p x
      = ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)
            * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
        - (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
          * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) (x p.1) (x p.2))
        - 2 * ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
              * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
              * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2))) := by
  classical
  have hij : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact fun y hy => hy.1
  -- the doubly projected state factors through the two box indicators and the double mean
  have hP : Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x p.1) * (A.indicator (fun _ => (1 : ℝ)) (x p.2)
          * ((1 / V) * ((1 / V) * ∫ y in A, ∫ z in A,
              Φ (Function.update (Function.update x p.1 y) p.2 z)))) := by
    rw [Work.BoseFixB1S.boxPInd_pair_factor V A p.1 p.2 hij Φ x]
    ring
  -- `P_{p.1}Q_{p.2}Φ`
  have hS1 : Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxQInd V A p.2 Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x p.1) * (A.indicator (fun _ => (1 : ℝ)) (x p.2)
          * ((1 / V) * (∫ z in A, Φ (Function.update x p.1 z))
            - (1 / V) * ((1 / V) * ∫ z in A, ∫ w in A,
                Φ (Function.update (Function.update x p.1 z) p.2 w)))) := by
    have key := Work.BoseFixB1.boxPInd_boxQInd_update (N := N) (ℓ := ℓ) (V := V)
      hℓ (A := A) hAmeas hAc (Φ := Φ) hΦc (s := p.1) (t := p.2) hij (x := x) hx (x p.1)
    rw [Function.update_eq_self] at key
    rw [key]
    ring
  -- `P_{p.2}Q_{p.1}Φ`
  have hS2 : Work.UBBInputs8.boxPInd V A p.2 (Work.UBBInputs8.boxQInd V A p.1 Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x p.2) * (A.indicator (fun _ => (1 : ℝ)) (x p.1)
          * ((1 / V) * (∫ z in A, Φ (Function.update x p.2 z))
            - (1 / V) * ((1 / V) * ∫ z in A, ∫ w in A,
                Φ (Function.update (Function.update x p.2 z) p.1 w)))) := by
    have key := Work.BoseFixB1.boxPInd_boxQInd_update (N := N) (ℓ := ℓ) (V := V)
      hℓ (A := A) hAmeas hAc (Φ := Φ) hΦc (s := p.2) (t := p.1) (Ne.symm hij) (x := x) hx
      (x p.2)
    rw [Function.update_eq_self] at key
    rw [key]
    ring
  -- `Q_{p.1}Φ`
  have hQi : Work.UBBInputs8.boxQInd V A p.1 Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x p.1)
        * (Φ x - (1 / V) * ∫ z in A, Φ (Function.update x p.1 z)) := by
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    ring
  -- `Q_{p.2}Q_{p.1}Φ`
  have hQ : Work.UBBInputs8.boxQInd V A p.2 (Work.UBBInputs8.boxQInd V A p.1 Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x p.2) * (A.indicator (fun _ => (1 : ℝ)) (x p.1)
            * (Φ x - (1 / V) * ∫ z in A, Φ (Function.update x p.1 z)))
        - A.indicator (fun _ => (1 : ℝ)) (x p.2) * (A.indicator (fun _ => (1 : ℝ)) (x p.1)
            * ((1 / V) * (∫ z in A, Φ (Function.update x p.2 z))
              - (1 / V) * ((1 / V) * ∫ z in A, ∫ w in A,
                  Φ (Function.update (Function.update x p.2 z) p.1 w)))) := by
    have h1 : Work.UBBInputs8.boxQInd V A p.2 (Work.UBBInputs8.boxQInd V A p.1 Φ) x
        = A.indicator (fun _ => (1 : ℝ)) (x p.2) * (Work.UBBInputs8.boxQInd V A p.1 Φ) x
          - Work.UBBInputs8.boxPInd V A p.2 (Work.UBBInputs8.boxQInd V A p.1 Φ) x := rfl
    rw [h1, hQi, hS2]
  -- the kernel relations `w₁ = w(1−ω)`, `w₂ = w₁(1+ω)`
  have hw1 : Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2)
      = Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)
        * (1 - Classical.choose h (x p.1 - x p.2)) :=
    Work.BoseFixB1.wSmall1Pair_eq_mul (v := v) h u (x p.1) (x p.2)
  have hw2 : Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) (x p.1)
        (x p.2)
      = Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2)
        * (1 + Classical.choose h (x p.1 - x p.2)) :=
    Work.BoseFixB1.wSmallPair_g2_eq_mul (v := v) h u (x p.1) (x p.2)
  -- expand the pair block and substitute the slot identities
  simp only [Work.BoseFixB1.pairBlock]
  rw [hw2, hw1, hP, hS1, hS2, hQ]
  simp only [Submission.BoseGases.omC]
  -- the residual is the algebraic core
  have halg := pairBlock_alg
    (A.indicator (fun _ => (1 : ℝ)) (x p.1) * A.indicator (fun _ => (1 : ℝ)) (x p.2))
    (Φ x)
    ((1 / V) * ∫ z in A, Φ (Function.update x p.1 z))
    ((1 / V) * ∫ z in A, Φ (Function.update x p.2 z))
    ((1 / V) * ((1 / V) * ∫ y in A, ∫ z in A,
      Φ (Function.update (Function.update x p.1 y) p.2 z)))
    ((1 / V) * ((1 / V) * ∫ z in A, ∫ w in A,
      Φ (Function.update (Function.update x p.2 z) p.1 w)))
    (Classical.choose h (x p.1 - x p.2))
    (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
  linear_combination halg

end Work.BoseFixB1
