import ChallengeDeps
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Submission.Work.BoseBoxFock.PCFU.MiddleU_eq_four_split
import Submission.Work.BoseBoxFock.PCFU.MiddleU_iterated_eq
import Submission.Work.BoseBoxFock.PCFU.lhs_kernelForm
import Submission.Work.BoseBoxFock.PCFU.sum_chWord_eq_half_q3lowWord
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.pairI1_eq`

**The per-pair cubic dictionary identity at the honest condensate pin.**  With `ℓ = ellH v μ`,
`Θ_c = boxRestrictC ℓ Φ` and `Θ_r = boxRestrictR ℓ Φ`, the `(i,j)`-pair contribution of the cubic
middle kernel is

    ∫x∫y∫u star (Θ_c x)·pinCond(x_i)·MiddleU(x_j,y,u)·Θ_c(x[i↦y][j↦u])
      = ℓ³·chWord(Θ_r) + chSlotAB(Θ_r) + ℓ⁻³·chSlotCD(Θ_r) .

The three ingredients are

* the **Fubini bridge** `MiddleU_iterated_eq` (child node): the iterated integral equals the
  product-space integral `∫ q, star (Θ_c q.1)·pinCond(q.1 i)·MiddleU(q.1 j) q.2.1 q.2.2·Θ_c(…)`;
* the **pointwise reduction** `Θ_c = ↑Θ_r`, `star (↑r) = ↑r` (`ofReal_boxRestrictR`,
  `Complex.conj_ofReal`) and `pinCond v μ c = c·thetaFun` (definitional), which pulls the constant
  `c` out of the integral and turns the integrand into the one of `MiddleU_eq_four_integral`;
* `MiddleU_eq_four_integral` (the four-channel split, giving the `ℓ^{-9/2}`) composed with
  `chDiff_eq` (the four-channel word/slot form), and the scalar bookkeeping
  `c·ℓ^{-9/2} = ℓ^{-6}`, i.e. `c·ℓ^{-9/2}·(ℓ⁹, ℓ⁶, ℓ³) = (ℓ³, 1, ℓ^{-3})`
  (`pairI1_coeff`; note `c = (√(ℓ³))⁻¹ = ℓ^{-3/2}`).

Every declaration in this file is closed.
-/

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## The scalar bookkeeping

`(√(ℓ³))⁻¹ = ℓ^{-3/2}`, hence `(√(ℓ³))⁻¹·ℓ^{-9/2} = ℓ^{-6}`, and multiplying by `ℓ⁹`, `ℓ⁶`, `ℓ³`
gives `ℓ³`, `1`, `ℓ^{-3}`. -/

private lemma sqrt3inv_eq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (Real.sqrt (ℓ^3))⁻¹ = ℓ ^ (-(3/2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ℓ 3, ← Real.rpow_mul hℓ.le, ← Real.rpow_neg hℓ.le]
  congr 1
  norm_num

private lemma rpow_shift2 {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    ℓ ^ (-(3/2) : ℝ) * ℓ ^ (-(9/2) : ℝ) * ℓ ^ t = ℓ ^ (t - 6) := by
  rw [← Real.rpow_add hℓ (-(3/2)) (-(9/2)), ← Real.rpow_add hℓ ((-(3/2))+(-(9/2))) t]
  congr 1
  ring

private lemma pairI1_coeff {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (((Real.sqrt (ℓ^3))⁻¹ : ℝ) : ℂ) * ((ℓ ^ (-(9/2):ℝ) : ℝ) : ℂ) * ((ℓ:ℂ)^9)
        = ((ℓ:ℂ)^3)
    ∧ (((Real.sqrt (ℓ^3))⁻¹ : ℝ) : ℂ) * ((ℓ ^ (-(9/2):ℝ) : ℝ) : ℂ) * ((ℓ:ℂ)^6) = 1
    ∧ (((Real.sqrt (ℓ^3))⁻¹ : ℝ) : ℂ) * ((ℓ ^ (-(9/2):ℝ) : ℝ) : ℂ) * ((ℓ:ℂ)^3)
        = ((ℓ:ℂ)^(-3:ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h : ℓ ^ (-(3/2):ℝ) * ℓ ^ (-(9/2):ℝ) * ℓ ^ (9:ℕ) = ℓ ^ (3:ℕ) := by
      rw [(Real.rpow_natCast ℓ 9).symm, rpow_shift2 hℓ ((9:ℕ):ℝ), (Real.rpow_natCast ℓ 3).symm]
      congr 1
      norm_num
    rw [sqrt3inv_eq hℓ, ← Complex.ofReal_pow ℓ 9, ← Complex.ofReal_pow ℓ 3]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_injective.eq_iff]
    exact h
  · have h : ℓ ^ (-(3/2):ℝ) * ℓ ^ (-(9/2):ℝ) * ℓ ^ (6:ℕ) = 1 := by
      rw [(Real.rpow_natCast ℓ 6).symm, rpow_shift2 hℓ ((6:ℕ):ℝ)]
      rw [show ((6:ℕ):ℝ) - 6 = 0 from by norm_num, Real.rpow_zero]
    rw [sqrt3inv_eq hℓ, ← Complex.ofReal_pow ℓ 6]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      Complex.ofReal_injective.eq_iff]
    exact h
  · have h : ℓ ^ (-(3/2):ℝ) * ℓ ^ (-(9/2):ℝ) * ℓ ^ (3:ℕ) = ℓ ^ (-3:ℤ) := by
      rw [(Real.rpow_natCast ℓ 3).symm, rpow_shift2 hℓ ((3:ℕ):ℝ),
        (Real.rpow_intCast ℓ (-3)).symm]
      congr 1
      norm_num
    rw [sqrt3inv_eq hℓ, ← Complex.ofReal_pow ℓ 3, ← Complex.ofReal_zpow ℓ (-3)]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_injective.eq_iff]
    exact h

theorem pairI1_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (hsub : ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        Work.BoseBoxFock.fLh v fc μ N s ≠ 0 →
        ∀ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
          Work.BoseBoxFock.W1h v h μ fu N k ≠ 0 →
        Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)
          = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s
            - Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < Work.BoseBoxFock.PCFU.chKappa v μ)
    (hN : 2 * (Work.BoseBoxFock.PCFU.chKappa v μ) * Work.BoseBoxFock.ellH v μ / (2 * Real.pi)
      ≤ (N : ℝ))
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBoxFock.ellH v μ))
    (c : ℂ) (hc : c = (((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) :
    (∫ x : Submission.BoseGases.X n, ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3),
        star (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ) x)
          * Work.BoseBoxFock.pinCond v μ c (x i)
          * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ N (x j) y u
          * Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ)
              (Function.update (Function.update x i y) j u))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * Work.BoseBoxFock.PCFU.chWord v h fc fu μ N i j
              (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseBoxFock.PCFU.chSlotAB v h fc fu μ N i j
            (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ))
        + ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ (-3 : ℤ)
          * Work.BoseBoxFock.PCFU.chSlotCD v h fc fu μ N i j
              (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                (Φ : Submission.BoseGases.X n → ℝ)) := by
  -- ## the state facts about `boxRestrictC ℓ Φ` and its real twin `boxRestrictR ℓ Φ`
  obtain ⟨hΘCm, hΘCb, hΘCs, hΘCsymm⟩ := boxRestrict_state_facts Φ
  have hΘRm : Measurable (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) := by
    convert hΘCm.re using 1
    funext x
    exact (re_boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x).symm
  have hΘRb : ∃ C : ℝ,
      ∀ x, |boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x| ≤ C := by
    obtain ⟨C, hC⟩ := hΘCb
    exact ⟨C, fun x => by rw [← norm_boxRestrictC]; exact hC x⟩
  have hΘRs : Function.support (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
      ⊆ Submission.BoseGases.abox n (ellH v μ) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxnot
    exact hx (by rw [boxRestrictR, Set.indicator_of_notMem hxnot (fun _ => (1 : ℝ)), mul_zero])
  have hΘRpi : Submission.BoseGases.PermInvariant n
      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) := by
    intro σ x
    have hh := congrFun (hΘCsymm σ) x
    calc boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)
          (Submission.BoseGases.actPerm n σ x)
        = RCLike.re (boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)
            (x ∘ ⇑σ)) := (re_boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) _).symm
      _ = RCLike.re (boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x) := by
            rw [hh]
      _ = boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x :=
            re_boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x
  -- ## Fubini: the iterated integral is the product-space integral
  rw [MiddleU_iterated_eq (Θ := boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
    hij v h fc fu μ N c hΘCm hΘCb hΘCs]
  -- ## the pointwise reduction: `Θ_c = ↑Θ_r`, `pinCond = c·θ`
  have hpt : ∀ q : Submission.BoseGases.X n
        × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
      star (boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) q.1)
        * pinCond v μ c (q.1 i) * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
        * boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)
            (Function.update (Function.update q.1 i q.2.1) j q.2.2)
      = c * (((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
          * ((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)
              (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) := by
    intro q
    rw [← ofReal_boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) q.1,
      ← ofReal_boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) _]
    simp only [pinCond, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul]
  -- ## the four-channel split and the word/slot decomposition
  rw [MiddleU_eq_four_integral (n := n) hij v h fc fu μ N hsub
      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) hΘRm hΘRb hΘRs]
  rw [chDiff_eq (n := n) hij v h hvrad fc fu μ N hℓ hκ hN
      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) hΘRpi hΘRm hΘRb hΘRs]
  -- ## the scalar bookkeeping
  set B : ℂ := ((ellH v μ ^ (-(9/2) : ℝ) : ℝ) : ℂ) with hBdef
  set X9 : ℂ := ((ellH v μ : ℂ)) ^ 9 with hX9def
  set X6 : ℂ := ((ellH v μ : ℂ)) ^ 6 with hX6def
  set X3 : ℂ := ((ellH v μ : ℂ)) ^ 3 with hX3def
  set Xm3 : ℂ := ((ellH v μ : ℂ)) ^ (-3 : ℤ) with hXm3def
  set W : ℂ := chWord v h fc fu μ N i j
      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) with hWdef
  set S1 : ℂ := chSlotAB v h fc fu μ N i j
      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) with hS1def
  set S2 : ℂ := chSlotCD v h fc fu μ N i j
      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) with hS2def
  have hcoe := pairI1_coeff (ℓ := ellH v μ) hℓ
  have h1 : c * B * X9 = X3 := by rw [hBdef, hX9def, hX3def, hc]; exact hcoe.1
  have h2 : c * B * X6 = 1 := by rw [hBdef, hX6def, hc]; exact hcoe.2.1
  have h3 : c * B * X3 = Xm3 := by rw [hBdef, hX3def, hXm3def, hc]; exact hcoe.2.2
  rw [show c * (B * (X9 * W + X6 * S1 + X3 * S2))
        = (c * B) * (X9 * W) + (c * B) * (X6 * S1) + (c * B) * (X3 * S2) from by ring,
      show (c * B) * (X9 * W) = X3 * W from by rw [← mul_assoc, h1],
      show (c * B) * (X6 * S1) = S1 from by rw [← mul_assoc, h2, one_mul],
      show (c * B) * (X3 * S2) = Xm3 * S2 from by rw [← mul_assoc, h3]]

end Work.BoseBoxFock.PCFU
