import Mathlib
import Submission.Work.MotK.TGen.ChartSetup
import Submission.Work.MotK.TGen.ChartHeightAux
import Submission.Work.MotK.TGen.HeightStepMonic
import Submission.Work.MotK.TGen.ChartHeightTrans
import Submission.Work.MotK.TGen.ChartHeightMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Work.MotK.TGen

open MvPolynomial

/-! ## The height chain -/

/-- **The height chain.**  A prime `P ⊆ K[y₀,…,y₄]` containing the four peeled elements
`y₀ - 1`, `G1v`, `Av`, `Resv` has height at least `4`.

Peeling the variables `y₀`, `y₁`, `y₂` (using respectively the linear elements `y₀ - 1`, `G1v`,
`Av`, whose leading coefficients are units) gives three successive height increments; the
resultant `Resv` restricts to a nonzero element of the prime cut out in the two variables
`y₃, y₄`, which therefore has height at least one. -/
theorem ht_ge_four_of_mem (K : Type) [Field K] {a b H : K} (ha : a ≠ 0) (hb : b ≠ 0) (hH : H ≠ 0)
    {P : Ideal (MvPolynomial (Fin 5) K)} (hP : P.IsPrime)
    (h0 : MvPolynomial.X (0 : Fin 5) - 1 ∈ P) (h1 : G1v a b H ∈ P) (h2 : Av a b H ∈ P)
    (h3 : Resv a b H ∈ P) (hR : Resv a b H ≠ 0) : (4 : ℕ∞) ≤ P.height := by
  classical
  haveI := hP
  obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, -⟩ := ChartHeightTrans K a b H ha hb hH
  -- ## level 4: peel `y₀`, using `y₀ - 1`
  set e4 : MvPolynomial (Fin 5) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 4) K) :=
    MvPolynomial.finSuccEquiv K 4 with he4
  set P0 : Ideal (Polynomial (MvPolynomial (Fin 4) K)) := P.map e4 with hP0def
  haveI hP0prime : P0.IsPrime := by
    rw [hP0def]; exact Ideal.map_isPrime_of_equiv e4
  have hP0ht : P0.height = P.height := by
    rw [hP0def]; exact RingEquiv.height_map e4.toRingEquiv P
  have hX : (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin 4) K)) ∈ P0 := by
    rw [hP0def, he4]
    have h := Ideal.mem_map_of_mem e4 h0
    rw [he4, map_sub, map_one, MvPolynomial.finSuccEquiv_X_zero] at h
    exact h
  set P1 : Ideal (MvPolynomial (Fin 4) K) := P0.comap Polynomial.C with hP1def
  haveI hP1prime : P1.IsPrime := by
    rw [hP1def]; exact Ideal.comap_isPrime Polynomial.C P0
  have step1 : P1.height + 1 ≤ P.height := by
    have h := HeightStepMonic P0 (Polynomial.X - 1) hX (n := 1) ?_
    · rwa [hP0ht] at h
    · have hc : (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin 4) K)).coeff 1 = 1 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_X,
          show (1 : Polynomial (MvPolynomial (Fin 4) K)) = Polynomial.C 1 from rfl,
          Polynomial.coeff_C]
        simp
      rw [hc]
      exact fun hmem => hP1prime.ne_top (Ideal.eq_top_of_isUnit_mem P1 hmem isUnit_one)
  -- ## level 3: peel `y₁`, using `G1v`
  have hG1 : G1v4 a b H ∈ P1 := by
    rw [hP1def, Ideal.mem_comap, hP0def, he4]
    have h := Ideal.mem_map_of_mem e4 h1
    rw [he4, hT1] at h
    exact h
  set e3 : MvPolynomial (Fin 4) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 3) K) :=
    MvPolynomial.finSuccEquiv K 3 with he3
  set Q1 : Ideal (Polynomial (MvPolynomial (Fin 3) K)) := P1.map e3 with hQ1def
  haveI hQ1prime : Q1.IsPrime := by
    rw [hQ1def]; exact Ideal.map_isPrime_of_equiv e3
  have hQ1ht : Q1.height = P1.height := by
    rw [hQ1def]; exact RingEquiv.height_map e3.toRingEquiv P1
  have hg : Polynomial.C (MvPolynomial.C (a ^ 2)) * Polynomial.X - Polynomial.C (g13 a b H) ∈ Q1 := by
    rw [hQ1def, he3]
    have h := Ideal.mem_map_of_mem e3 hG1
    rw [he3, hT2] at h
    exact h
  set P2 : Ideal (MvPolynomial (Fin 3) K) := Q1.comap Polynomial.C with hP2def
  haveI hP2prime : P2.IsPrime := by
    rw [hP2def]; exact Ideal.comap_isPrime Polynomial.C Q1
  have step2 : P2.height + 1 ≤ P1.height := by
    have h := HeightStepMonic Q1 (Polynomial.C (MvPolynomial.C (a ^ 2)) * Polynomial.X
      - Polynomial.C (g13 a b H)) hg (n := 1) ?_
    · rwa [hQ1ht] at h
    · have hc : (Polynomial.C (MvPolynomial.C (a ^ 2)) * Polynomial.X
          - Polynomial.C (g13 a b H) : Polynomial (MvPolynomial (Fin 3) K)).coeff 1
          = MvPolynomial.C (a ^ 2) := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        simp
      rw [hc]
      exact fun hmem => hP2prime.ne_top (Ideal.eq_top_of_isUnit_mem P2 hmem (IsUnit.map MvPolynomial.C
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 ha))))
  -- ## level 2: peel `y₂`, using `Av`
  have hAv : Av3 a b H ∈ P2 := by
    have hA4 : Av4 a b H ∈ P1 := by
      rw [hP1def, Ideal.mem_comap, hP0def, he4]
      have h := Ideal.mem_map_of_mem e4 h2
      rw [he4, hT3] at h
      exact h
    rw [hP2def, Ideal.mem_comap, hQ1def, he3]
    have h := Ideal.mem_map_of_mem e3 hA4
    rw [he3, hT4] at h
    exact h
  set e2 : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
    MvPolynomial.finSuccEquiv K 2 with he2
  set Q2 : Ideal (Polynomial (MvPolynomial (Fin 2) K)) := P2.map e2 with hQ2def
  haveI hQ2prime : Q2.IsPrime := by
    rw [hQ2def]; exact Ideal.map_isPrime_of_equiv e2
  have hQ2ht : Q2.height = P2.height := by
    rw [hQ2def]; exact RingEquiv.height_map e2.toRingEquiv P2
  have hq : -Polynomial.C (MvPolynomial.C (a * b)) * Polynomial.X ^ 2
      - Polynomial.C (MvPolynomial.C (b ^ 4 * H / a ^ 2) * MvPolynomial.X 0 * MvPolynomial.X 1)
        * Polynomial.X
      + Polynomial.C (MvPolynomial.C (a ^ 2) * MvPolynomial.X 1
        - MvPolynomial.C (b ^ 3 * H / a) * (MvPolynomial.X 0) ^ 3) ∈ Q2 := by
    rw [hQ2def, he2]
    have h := Ideal.mem_map_of_mem e2 hAv
    rw [he2, hT5] at h
    exact h
  set P3 : Ideal (MvPolynomial (Fin 2) K) := Q2.comap Polynomial.C with hP3def
  haveI hP3prime : P3.IsPrime := by
    rw [hP3def]; exact Ideal.comap_isPrime Polynomial.C Q2
  have step3 : P3.height + 1 ≤ P2.height := by
    have h := HeightStepMonic Q2
      (-Polynomial.C (MvPolynomial.C (a * b)) * Polynomial.X ^ 2
        - Polynomial.C (MvPolynomial.C (b ^ 4 * H / a ^ 2) * MvPolynomial.X 0 * MvPolynomial.X 1)
          * Polynomial.X
        + Polynomial.C (MvPolynomial.C (a ^ 2) * MvPolynomial.X 1
          - MvPolynomial.C (b ^ 3 * H / a) * (MvPolynomial.X 0) ^ 3)) hq (n := 2) ?_
    · rwa [hQ2ht] at h
    · have hc : (-Polynomial.C (MvPolynomial.C (a * b)) * Polynomial.X ^ 2
          - Polynomial.C (MvPolynomial.C (b ^ 4 * H / a ^ 2) * MvPolynomial.X 0 * MvPolynomial.X 1)
            * Polynomial.X
          + Polynomial.C (MvPolynomial.C (a ^ 2) * MvPolynomial.X 1
            - MvPolynomial.C (b ^ 3 * H / a) * (MvPolynomial.X 0) ^ 3) :
            Polynomial (MvPolynomial (Fin 2) K)).coeff 2
          = -MvPolynomial.C (a * b) := by
        have hpoly : (-Polynomial.C (MvPolynomial.C (a * b)) * Polynomial.X ^ 2
            - Polynomial.C (MvPolynomial.C (b ^ 4 * H / a ^ 2) * MvPolynomial.X 0 * MvPolynomial.X 1)
              * Polynomial.X
            + Polynomial.C (MvPolynomial.C (a ^ 2) * MvPolynomial.X 1
              - MvPolynomial.C (b ^ 3 * H / a) * (MvPolynomial.X 0) ^ 3) :
              Polynomial (MvPolynomial (Fin 2) K))
            = Polynomial.C (-MvPolynomial.C (a * b)) * Polynomial.X ^ 2
              - Polynomial.C (MvPolynomial.C (b ^ 4 * H / a ^ 2) * MvPolynomial.X 0 * MvPolynomial.X 1)
                * Polynomial.X
              + Polynomial.C (MvPolynomial.C (a ^ 2) * MvPolynomial.X 1
                - MvPolynomial.C (b ^ 3 * H / a) * (MvPolynomial.X 0) ^ 3) := by
          rw [Polynomial.C_neg]
        rw [hpoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow,
          Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        simp
      rw [hc]
      exact fun hmem => hP3prime.ne_top (Ideal.eq_top_of_isUnit_mem P3 hmem (IsUnit.neg (IsUnit.map MvPolynomial.C
        (isUnit_iff_ne_zero.mpr (mul_ne_zero ha hb)))))
  -- ## `Resv` restricts to a nonzero element of the prime in `K[y₃,y₄]`
  have hRes : ResPoly a b H ∈ P3 := by
    have hR4 : ResPoly4 a b H ∈ P1 := by
      rw [hP1def, Ideal.mem_comap, hP0def, he4]
      have h := Ideal.mem_map_of_mem e4 h3
      rw [he4, hT6] at h
      exact h
    have hR3 : ResPoly3 a b H ∈ P2 := by
      rw [hP2def, Ideal.mem_comap, hQ1def, he3]
      have h := Ideal.mem_map_of_mem e3 hR4
      rw [he3, hT7] at h
      exact h
    rw [hP3def, Ideal.mem_comap, hQ2def, he2]
    have h := Ideal.mem_map_of_mem e2 hR3
    rw [he2, hT8] at h
    exact h
  have hRne : ResPoly a b H ≠ 0 := by
    intro hz
    have hz3 : ResPoly3 a b H = 0 := by
      refine (MvPolynomial.finSuccEquiv K 2).injective ?_
      have : MvPolynomial.finSuccEquiv K 2 (ResPoly3 a b H) = 0 := by rw [hT8, hz, map_zero]
      simpa using this
    have hz4 : ResPoly4 a b H = 0 := by
      refine (MvPolynomial.finSuccEquiv K 3).injective ?_
      have : MvPolynomial.finSuccEquiv K 3 (ResPoly4 a b H) = 0 := by rw [hT7, hz3, map_zero]
      simpa using this
    refine hR ((MvPolynomial.finSuccEquiv K 4).injective ?_)
    have : MvPolynomial.finSuccEquiv K 4 (Resv a b H) = 0 := by rw [hT6, hz4, map_zero]
    simpa using this
  have step4 : (1 : ℕ∞) ≤ P3.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hbot
    exact hRne (by simpa [hbot] using hRes)
  -- ## combine
  have h34 : (2 : ℕ∞) ≤ P2.height :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ P3.height + 1 := add_le_add step4 le_rfl
      _ ≤ P2.height := step3
  have h24 : (3 : ℕ∞) ≤ P1.height :=
    calc (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ P2.height + 1 := add_le_add h34 le_rfl
      _ ≤ P1.height := step2
  calc (4 : ℕ∞) = 3 + 1 := by norm_num
    _ ≤ P1.height + 1 := add_le_add h24 le_rfl
    _ ≤ P.height := step1

/-! ## The target -/

theorem ChartHeightBound (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (H : K)
    (hH : H ≠ 0) : 4 ≤ (Work.MotK.TGen.chartIdeal K D H).height := by
  obtain ⟨hG1, hAv, -, hRes, hRne⟩ := ChartHeightMem K D hD H hH
  have ha : D.a ≠ 0 := fun h => hD.ab_ne (by rw [h, zero_mul])
  have hb : D.b ≠ 0 := fun h => hD.ab_ne (by rw [h, mul_zero])
  have hX0 : MvPolynomial.X (0 : Fin 5) - 1 ∈ chartIdeal K D H := by
    rw [chartIdeal]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ (fun J hJ => ?_)
  exact ht_ge_four_of_mem K ha hb hH hJ.isPrime (hJ.le hX0) (hJ.le hG1) (hJ.le hAv)
    (hJ.le hRes) hRne

end Work.MotK.TGen
