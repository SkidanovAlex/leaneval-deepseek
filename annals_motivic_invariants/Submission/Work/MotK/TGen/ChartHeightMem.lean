import Mathlib
import Submission.Work.MotK.TGen.ChartHeightAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ChartHeightMem`

The four explicit elements `G1v, Av, Bv, Resv` of `ChartHeightAux` lie in the chart ideal
`chartIdeal K D H = Qideal D.a D.b H ⊔ span{X 0 - 1}` of the affine chart `y₀ = 1` of the twisted
Klein quintic, and `Resv` is nonzero.

`G1v`, `Av`, `Bv` are obtained from the Pfaffians `p₄`, `p₁`, `p₀` (`= kleinTwP … 4,1,0`) by
substituting `y₀ = 1` and `y₁ = (abH y₃² + b²H y₂y₄)/a²`; the identities are
* `G1v = p₄ - a²(y₀-1)y₁`,
* `Av  = p₁ - a²(y₀-1)y₄ + (b²/a²) y₃ G1v`,
* `Bv  = p₀ + ab(y₀²-1) + (b²H/a²) y₄ G1v`,
so all three are ideal combinations of the Pfaffians and the chart equation.  `Av` and `Bv` contain
divisions by `a`; multiplying by `a²` clears them and gives the division-free elements `AvC`, `BvC`.
`Resv` is the resultant of `Av` and `Bv` in `y₂`; it satisfies
`Resv = B1²·Av - (A2·B1·y₂ + A1·B1 - A2·B0)·Bv`, and after multiplying by `a⁶ = (a²)³` the same
identity holds with the divided quantities replaced by `A0c, A1c, A2c, B0c, B1c`.

Nonvanishing of `Resv` is proved by specialising `y₄ = 0` and reading off the coefficient of `y₃⁵`,
which is `-C(a³b³H³) ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

section

variable {K : Type} [Field K]

/-! ## The cleared (division-free) forms -/

/-- `C a² · Av`: the cleared form of `Av`. -/
noncomputable def AvC (a b H : K) : MvPolynomial (Fin 5) K :=
  -C (a ^(3:ℕ) * b) * (X 2) ^(2:ℕ) - C (b ^(4:ℕ) * H) * X 2 * X 3 * X 4 + C (a ^(4:ℕ)) * X 4
    - C (a * b ^(3:ℕ) * H) * (X 3) ^(3:ℕ)

/-- `C a² · Bv`: the cleared form of `Bv`. -/
noncomputable def BvC (a b H : K) : MvPolynomial (Fin 5) K :=
  C (a ^(4:ℕ) * H) * X 2 * X 3 - C (a ^(3:ℕ) * b) - C (a * b ^(3:ℕ) * H ^(2:ℕ)) * (X 3) ^(2:ℕ) * X 4
    - C (b ^(4:ℕ) * H ^(2:ℕ)) * X 2 * (X 4) ^(2:ℕ)

/-- `C a²` times the `y₂`-coefficient `b₁` of `Bv`. -/
noncomputable def B1c (a b H : K) : MvPolynomial (Fin 5) K :=
  C (a ^(4:ℕ) * H) * X 3 - C (b ^(4:ℕ) * H ^(2:ℕ)) * (X 4) ^(2:ℕ)

/-- `C a²` times the constant coefficient `b₀` of `Bv`. -/
noncomputable def B0c (a b H : K) : MvPolynomial (Fin 5) K :=
  -C (a ^(3:ℕ) * b) - C (a * b ^(3:ℕ) * H ^(2:ℕ)) * (X 3) ^(2:ℕ) * X 4

/-- `C a²` times the constant coefficient `a₀` of `Av`. -/
noncomputable def A0c (a b H : K) : MvPolynomial (Fin 5) K :=
  C (a ^(4:ℕ)) * X 4 - C (a * b ^(3:ℕ) * H) * (X 3) ^(3:ℕ)

/-- `C a²` times the `y₂`-coefficient `a₁` of `Av`. -/
noncomputable def A1c (a b H : K) : MvPolynomial (Fin 5) K :=
  -C (b ^(4:ℕ) * H) * X 3 * X 4

/-- `C a²` times the `y₂²`-coefficient `a₂` of `Av`. -/
noncomputable def A2c (a b H : K) : MvPolynomial (Fin 5) K :=
  -C (a ^(3:ℕ) * b)

/-- `(C a²)³ · Resv`: the cleared resultant. -/
noncomputable def ResvC (a b H : K) : MvPolynomial (Fin 5) K :=
  (B1c a b H) ^(2:ℕ) * A0c a b H - A1c a b H * B0c a b H * B1c a b H + A2c a b H * (B0c a b H) ^(2:ℕ)

/-! ## Clearing the denominators -/

theorem Av_clear (a b H : K) (ha : a ≠ 0) :
    (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * Av a b H = AvC a b H := by
  have ha2 : a ^(2:ℕ) ≠ 0 := pow_ne_zero 2 ha
  have s1 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(4:ℕ) * H / a ^(2:ℕ)) = C (b ^(4:ℕ) * H) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  have s2 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (a * b) = C (a ^(3:ℕ) * b) := by
    rw [← MvPolynomial.C_mul]; congr 1; ring
  have s3 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (a ^(2:ℕ)) = C (a ^(4:ℕ)) := by
    rw [← MvPolynomial.C_mul]; congr 1; ring
  have s4 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(3:ℕ) * H / a) = C (a * b ^(3:ℕ) * H) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  have hg : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * Av a b H
      = - (C (a ^(2:ℕ)) * C (a * b)) * (X 2) ^(2:ℕ)
        - (C (a ^(2:ℕ)) * C (b ^(4:ℕ) * H / a ^(2:ℕ))) * X 2 * X 3 * X 4
        + (C (a ^(2:ℕ)) * C (a ^(2:ℕ))) * X 4
        - (C (a ^(2:ℕ)) * C (b ^(3:ℕ) * H / a)) * (X 3) ^(3:ℕ) := by
    simp only [Av]; ring
  simp only [hg, s2, s1, s3, s4, AvC] <;> ring

theorem Bv_clear (a b H : K) (ha : a ≠ 0) :
    (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * Bv a b H = BvC a b H := by
  have ha2 : a ^(2:ℕ) ≠ 0 := pow_ne_zero 2 ha
  have s2 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (a * b) = C (a ^(3:ℕ) * b) := by
    rw [← MvPolynomial.C_mul]; congr 1; ring
  have s5 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (a ^(2:ℕ) * H) = C (a ^(4:ℕ) * H) := by
    rw [← MvPolynomial.C_mul]; congr 1; ring
  have s6 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(3:ℕ) * H ^(2:ℕ) / a) = C (a * b ^(3:ℕ) * H ^(2:ℕ)) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  have s7 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) = C (b ^(4:ℕ) * H ^(2:ℕ)) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  have hg : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * Bv a b H
      = (C (a ^(2:ℕ)) * C (a ^(2:ℕ) * H)) * X 2 * X 3 - (C (a ^(2:ℕ)) * C (a * b))
        - (C (a ^(2:ℕ)) * C (b ^(3:ℕ) * H ^(2:ℕ) / a)) * (X 3) ^(2:ℕ) * X 4
        - (C (a ^(2:ℕ)) * C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ))) * X 2 * (X 4) ^(2:ℕ) := by
    simp only [Bv]; ring
  simp only [hg, s5, s2, s6, s7, BvC] <;> ring

theorem Resv_clear (a b H : K) (ha : a ≠ 0) :
    ((C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K)) ^(3:ℕ) * Resv a b H = ResvC a b H := by
  have ha2 : a ^(2:ℕ) ≠ 0 := pow_ne_zero 2 ha
  have s1 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(4:ℕ) * H / a ^(2:ℕ)) = C (b ^(4:ℕ) * H) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  have s2 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (a * b) = C (a ^(3:ℕ) * b) := by
    rw [← MvPolynomial.C_mul]; congr 1; ring
  have s3 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (a ^(2:ℕ)) = C (a ^(4:ℕ)) := by
    rw [← MvPolynomial.C_mul]; congr 1; ring
  have s4 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(3:ℕ) * H / a) = C (a * b ^(3:ℕ) * H) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  have s5 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (a ^(2:ℕ) * H) = C (a ^(4:ℕ) * H) := by
    rw [← MvPolynomial.C_mul]; congr 1; ring
  have s6 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(3:ℕ) * H ^(2:ℕ) / a) = C (a * b ^(3:ℕ) * H ^(2:ℕ)) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  have s7 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) = C (b ^(4:ℕ) * H ^(2:ℕ)) := by
    rw [← MvPolynomial.C_mul]; congr 1; field_simp
  set B1 : MvPolynomial (Fin 5) K := C (a ^(2:ℕ) * H) * X 3 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 4) ^(2:ℕ) with hB1
  set A0 : MvPolynomial (Fin 5) K := C (a ^(2:ℕ)) * X 4 - C (b ^(3:ℕ) * H / a) * (X 3) ^(3:ℕ) with hA0
  set A1 : MvPolynomial (Fin 5) K := C (-(b ^(4:ℕ) * H / a ^(2:ℕ))) * X 3 * X 4 with hA1
  set B0 : MvPolynomial (Fin 5) K := C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 3) ^(2:ℕ) * X 4 with hB0
  set A2 : MvPolynomial (Fin 5) K := C (-(a * b)) with hA2
  have hResv : Resv a b H = B1 ^(2:ℕ) * A0 - A1 * B0 * B1 + A2 * B0 ^(2:ℕ) := by
    simp only [Resv]
    rw [← hB1, ← hA0, ← hA1, ← hB0, ← hA2] <;> ring
  have cB1 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * B1 = B1c a b H := by
    rw [hB1, B1c, mul_sub]
    congr 1
    · rw [← mul_assoc, s5]
    · rw [← mul_assoc, s7]
  have cA0 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * A0 = A0c a b H := by
    rw [hA0, A0c, mul_sub]
    congr 1
    · rw [← mul_assoc, s3]
    · rw [← mul_assoc, s4]
  have cA1 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * A1 = A1c a b H := by
    have hs : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (-(b ^(4:ℕ) * H / a ^(2:ℕ)))
        = -C (b ^(4:ℕ) * H) := by
      rw [MvPolynomial.C_neg, mul_neg, s1]
    rw [hA1, A1c,
      show (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * (C (-(b ^(4:ℕ) * H / a ^(2:ℕ))) * X 3 * X 4)
          = ((C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (-(b ^(4:ℕ) * H / a ^(2:ℕ)))) * X 3 * X 4
        from by ring,
      hs] <;> ring
  have cB0 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * B0 = B0c a b H := by
    have hs2 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (-(a * b)) = -C (a ^(3:ℕ) * b) := by
      rw [MvPolynomial.C_neg, mul_neg, s2]
    rw [hB0, hA2, B0c,
      show (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K)
            * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * X 3 ^(2:ℕ) * X 4)
          = ((C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * C (-(a * b)))
            - (C (a ^(2:ℕ)) * C (b ^(3:ℕ) * H ^(2:ℕ) / a)) * X 3 ^(2:ℕ) * X 4
        from by ring,
      hs2, s6] <;> ring
  have cA2 : (C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * A2 = A2c a b H := by
    rw [hA2, A2c, MvPolynomial.C_neg]
    simp only [mul_neg, s2] <;> ring
  have hgroup : ((C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K)) ^(3:ℕ) * (B1 ^(2:ℕ) * A0 - A1 * B0 * B1 + A2 * B0 ^(2:ℕ))
      = (C (a ^(2:ℕ)) * B1) ^(2:ℕ) * (C (a ^(2:ℕ)) * A0)
        - (C (a ^(2:ℕ)) * A1) * (C (a ^(2:ℕ)) * B0) * (C (a ^(2:ℕ)) * B1)
        + (C (a ^(2:ℕ)) * A2) * (C (a ^(2:ℕ)) * B0) ^(2:ℕ) := by
    refl_ring1
  have hResvC : ((C (a ^(2:ℕ)) : MvPolynomial (Fin 5) K)) ^(3:ℕ)
      * (B1 ^(2:ℕ) * A0 - A1 * B0 * B1 + A2 * B0 ^(2:ℕ)) = ResvC a b H := by
    simp only [hgroup, cB1, cA0, cA1, cB0, cA2, ResvC] <;> ring
  rw [hResv]
  exact hResvC

/-! ## The certificates: the cleared elements as combinations of the Pfaffians -/

theorem Av_cert (a b H : K) :
    AvC a b H = C (a ^(2:ℕ)) * kleinTwP (C a) (C b) (C H) (fun i => X i) 1
      - C (a ^(4:ℕ)) * (X (0 : Fin 5) - 1) * X 4 + C (b ^(2:ℕ)) * X 3 * G1v a b H := by
  have h1 : kleinTwP (C a) (C b) (C H) (fun i => X i) 1
      = Work.MotK.kleinTwP1 (C a) (C b) (C H) (fun i => X i) := rfl
  simp only [AvC, G1v, h1, Work.MotK.kleinTwP1, MvPolynomial.C_mul, MvPolynomial.C_pow]
    <;> ring

theorem Bv_cert (a b H : K) :
    BvC a b H = C (a ^(2:ℕ)) * kleinTwP (C a) (C b) (C H) (fun i => X i) 0
      + C (a ^(3:ℕ) * b) * ((X (0 : Fin 5)) ^(2:ℕ) - 1) + C (b ^(2:ℕ) * H) * X 4 * G1v a b H := by
  have h0 : kleinTwP (C a) (C b) (C H) (fun i => X i) 0
      = Work.MotK.kleinTwP0 (C a) (C b) (C H) (fun i => X i) := rfl
  simp only [BvC, G1v, h0, Work.MotK.kleinTwP0, MvPolynomial.C_mul, MvPolynomial.C_pow]
    <;> ring

theorem Resv_cert (a b H : K) :
    ResvC a b H = (B1c a b H) ^(2:ℕ) * AvC a b H
      - (A2c a b H * B1c a b H * X 2 + A1c a b H * B1c a b H - A2c a b H * B0c a b H)
        * BvC a b H := by
  simp only [ResvC, AvC, BvC, B1c, B0c, A0c, A1c, A2c] <;> ring

/-! ## Nonvanishing of `Resv` -/

theorem Resv_ne_zero (a b H : K) (ha : a ≠ 0) (hb : b ≠ 0) (hH : H ≠ 0) :
    Resv a b H ≠ 0 := by
  intro h
  have hself : Function.update (0 : Fin 5 → MvPolynomial (Fin 5) K) (3 : Fin 5)
        (MvPolynomial.X 3) 3 = MvPolynomial.X 3 :=
    Function.update_self (3 : Fin 5) (MvPolynomial.X 3) (0 : Fin 5 → MvPolynomial (Fin 5) K)
  have hne : Function.update (0 : Fin 5 → MvPolynomial (Fin 5) K) (3 : Fin 5)
        (MvPolynomial.X 3) 4 = 0 :=
    Function.update_of_ne (show (4 : Fin 5) ≠ 3 by decide) (MvPolynomial.X 3)
      (0 : Fin 5 → MvPolynomial (Fin 5) K)
  have h0 : ¬((0 : Fin 5 →₀ ℕ) = Finsupp.single (3 : Fin 5) 5) := by
    rw [eq_comm]; exact Finsupp.single_ne_zero.mpr (by norm_num)
  have hσ : MvPolynomial.aeval (Function.update (0 : Fin 5 → MvPolynomial (Fin 5) K)
      (3 : Fin 5) (MvPolynomial.X 3)) (Resv a b H) = 0 := by
    rw [h, map_zero]
  have hval : MvPolynomial.aeval (Function.update (0 : Fin 5 → MvPolynomial (Fin 5) K)
      (3 : Fin 5) (MvPolynomial.X 3)) (Resv a b H)
      = - (MvPolynomial.C (a ^(2:ℕ) * H)
            * (MvPolynomial.C (a ^(2:ℕ) * H)
              * (MvPolynomial.C (b ^(3:ℕ) * H / a) * (MvPolynomial.X 3) ^(5:ℕ))))
        - (MvPolynomial.C (a * b) * (MvPolynomial.C (a * b) * MvPolynomial.C (a * b))) := by
    simp only [Resv, map_add, map_sub, map_mul, map_pow, map_neg, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    rw [hself, hne]
    refl_ring1
  have hcoeff : (MvPolynomial.aeval (Function.update (0 : Fin 5 → MvPolynomial (Fin 5) K)
      (3 : Fin 5) (MvPolynomial.X 3)) (Resv a b H)).coeff
        (Finsupp.single (3 : Fin 5) 5) = 0 := by
    rw [hσ]; simp
  rw [hval] at hcoeff
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_neg, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C, h0, eq_self_iff_true, ite_true, ite_false,
    mul_one, mul_zero, zero_mul, sub_zero, neg_eq_zero] at hcoeff
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hH)
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hH)
      (div_ne_zero (mul_ne_zero (pow_ne_zero 3 hb) hH) ha))) hcoeff

end

theorem ChartHeightMem (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (H : K) (hH : H ≠ 0) :
    Work.MotK.TGen.G1v D.a D.b H ∈ Work.MotK.TGen.chartIdeal K D H ∧
    Work.MotK.TGen.Av D.a D.b H ∈ Work.MotK.TGen.chartIdeal K D H ∧
    Work.MotK.TGen.Bv D.a D.b H ∈ Work.MotK.TGen.chartIdeal K D H ∧
    Work.MotK.TGen.Resv D.a D.b H ∈ Work.MotK.TGen.chartIdeal K D H ∧
    Work.MotK.TGen.Resv D.a D.b H ≠ 0 := by
  have ha : D.a ≠ 0 := fun h => hD.ab_ne (by rw [h, zero_mul])
  have hb : D.b ≠ 0 := fun h => hD.ab_ne (by rw [h, mul_zero])
  have ha2 : D.a ^(2:ℕ) ≠ 0 := pow_ne_zero 2 ha
  have hp : ∀ k : Fin 5,
      Work.MotK.kleinTwP (C D.a) (C D.b) (C H) (fun i => X i) k ∈ chartIdeal K D H := by
    intro k
    rw [chartIdeal]
    exact Ideal.mem_sup_left (Ideal.le_radical (Ideal.subset_span ⟨k, rfl⟩))
  have hX0 : (X (0 : Fin 5) - 1) ∈ chartIdeal K D H := by
    rw [chartIdeal]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  have hX0sq : (X (0 : Fin 5)) ^(2:ℕ) - 1 ∈ chartIdeal K D H := by
    have h : ((X (0 : Fin 5)) ^(2:ℕ) - 1 : MvPolynomial (Fin 5) K)
        = (X (0 : Fin 5) - 1) * (X (0 : Fin 5) + 1) := by ring
    rw [h]
    exact Ideal.mul_mem_right (X (0 : Fin 5) + 1) (chartIdeal K D H) hX0
  have hG1 : G1v D.a D.b H ∈ chartIdeal K D H := by
    have hid : G1v D.a D.b H = Work.MotK.kleinTwP (C D.a) (C D.b) (C H) (fun i => X i) 4
        - C (D.a ^(2:ℕ)) * (X (0 : Fin 5) - 1) * X 1 := by
      have h4 : Work.MotK.kleinTwP (C D.a) (C D.b) (C H) (fun i => X i) 4
          = Work.MotK.kleinTwP4 (C D.a) (C D.b) (C H) (fun i => X i) := rfl
      simp only [G1v, h4, Work.MotK.kleinTwP4, MvPolynomial.C_mul, MvPolynomial.C_pow]
        <;> ring
    rw [hid]
    exact Ideal.sub_mem (chartIdeal K D H) (hp 4)
      (Ideal.mul_mem_right (X 1) (chartIdeal K D H)
        (Ideal.mul_mem_left (chartIdeal K D H) (C (D.a ^(2:ℕ))) hX0))
  have hAvC : AvC D.a D.b H ∈ chartIdeal K D H := by
    rw [Av_cert D.a D.b H]
    have h1 : C (D.a ^(2:ℕ)) * Work.MotK.kleinTwP (C D.a) (C D.b) (C H) (fun i => X i) 1
        ∈ chartIdeal K D H :=
      Ideal.mul_mem_left (chartIdeal K D H) (C (D.a ^(2:ℕ))) (hp 1)
    have h2 : C (D.a ^(4:ℕ)) * (X (0 : Fin 5) - 1) * X 4 ∈ chartIdeal K D H :=
      Ideal.mul_mem_right (X 4) (chartIdeal K D H)
        (Ideal.mul_mem_left (chartIdeal K D H) (C (D.a ^(4:ℕ))) hX0)
    have h3 : C (D.b ^(2:ℕ)) * X 3 * G1v D.a D.b H ∈ chartIdeal K D H :=
      Ideal.mul_mem_left (chartIdeal K D H) (C (D.b ^(2:ℕ)) * X 3) hG1
    exact Ideal.add_mem (chartIdeal K D H) (Ideal.sub_mem (chartIdeal K D H) h1 h2) h3
  have hAv : Av D.a D.b H ∈ chartIdeal K D H := by
    have hclear : (C (D.a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * Av D.a D.b H = AvC D.a D.b H :=
      Av_clear D.a D.b H ha
    have hEq : Av D.a D.b H = C ((D.a ^(2:ℕ))⁻¹) * AvC D.a D.b H := by
      have h1 : C ((D.a ^(2:ℕ))⁻¹) * AvC D.a D.b H = Av D.a D.b H := by
        rw [← hclear, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ ha2, MvPolynomial.C_1,
          one_mul]
      exact h1.symm
    rw [hEq]
    exact Ideal.mul_mem_left (chartIdeal K D H) (C ((D.a ^(2:ℕ))⁻¹)) hAvC
  have hBvC : BvC D.a D.b H ∈ chartIdeal K D H := by
    rw [Bv_cert D.a D.b H]
    have h1 : C (D.a ^(2:ℕ)) * Work.MotK.kleinTwP (C D.a) (C D.b) (C H) (fun i => X i) 0
        ∈ chartIdeal K D H :=
      Ideal.mul_mem_left (chartIdeal K D H) (C (D.a ^(2:ℕ))) (hp 0)
    have h2 : C (D.a ^(3:ℕ) * D.b) * ((X (0 : Fin 5)) ^(2:ℕ) - 1) ∈ chartIdeal K D H :=
      Ideal.mul_mem_left (chartIdeal K D H) (C (D.a ^(3:ℕ) * D.b)) hX0sq
    have h3 : C (D.b ^(2:ℕ) * H) * X 4 * G1v D.a D.b H ∈ chartIdeal K D H :=
      Ideal.mul_mem_left (chartIdeal K D H) (C (D.b ^(2:ℕ) * H) * X 4) hG1
    exact Ideal.add_mem (chartIdeal K D H) (Ideal.add_mem (chartIdeal K D H) h1 h2) h3
  have hBv : Bv D.a D.b H ∈ chartIdeal K D H := by
    have hclear : (C (D.a ^(2:ℕ)) : MvPolynomial (Fin 5) K) * Bv D.a D.b H = BvC D.a D.b H :=
      Bv_clear D.a D.b H ha
    have hEq : Bv D.a D.b H = C ((D.a ^(2:ℕ))⁻¹) * BvC D.a D.b H := by
      have h1 : C ((D.a ^(2:ℕ))⁻¹) * BvC D.a D.b H = Bv D.a D.b H := by
        rw [← hclear, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ ha2, MvPolynomial.C_1,
          one_mul]
      exact h1.symm
    rw [hEq]
    exact Ideal.mul_mem_left (chartIdeal K D H) (C ((D.a ^(2:ℕ))⁻¹)) hBvC
  have hRes : Resv D.a D.b H ∈ chartIdeal K D H := by
    have hclear : ((C (D.a ^(2:ℕ)) : MvPolynomial (Fin 5) K)) ^(3:ℕ) * Resv D.a D.b H
        = ResvC D.a D.b H := Resv_clear D.a D.b H ha
    have hResC : ResvC D.a D.b H ∈ chartIdeal K D H := by
      rw [Resv_cert D.a D.b H]
      have h1 : (B1c D.a D.b H) ^(2:ℕ) * AvC D.a D.b H ∈ chartIdeal K D H :=
        Ideal.mul_mem_left (chartIdeal K D H) ((B1c D.a D.b H) ^(2:ℕ)) hAvC
      have h2 : (A2c D.a D.b H * B1c D.a D.b H * X 2 + A1c D.a D.b H * B1c D.a D.b H
            - A2c D.a D.b H * B0c D.a D.b H) * BvC D.a D.b H ∈ chartIdeal K D H :=
        Ideal.mul_mem_left (chartIdeal K D H)
          (A2c D.a D.b H * B1c D.a D.b H * X 2 + A1c D.a D.b H * B1c D.a D.b H
            - A2c D.a D.b H * B0c D.a D.b H) hBvC
      exact Ideal.sub_mem (chartIdeal K D H) h1 h2
    have hEq : Resv D.a D.b H = (C ((D.a ^(2:ℕ))⁻¹)) ^(3:ℕ) * ResvC D.a D.b H := by
      have h1 : (C ((D.a ^(2:ℕ))⁻¹)) ^(3:ℕ) * ResvC D.a D.b H = Resv D.a D.b H := by
        rw [← hclear, ← mul_assoc, ← mul_pow, ← MvPolynomial.C_mul, inv_mul_cancel₀ ha2,
          MvPolynomial.C_1, one_pow, one_mul]
      exact h1.symm
    rw [hEq]
    exact Ideal.mul_mem_left (chartIdeal K D H) ((C ((D.a ^(2:ℕ))⁻¹)) ^(3:ℕ)) hResC
  exact ⟨hG1, hAv, hBv, hRes, Resv_ne_zero D.a D.b H ha hb hH⟩

end Work.MotK.TGen
