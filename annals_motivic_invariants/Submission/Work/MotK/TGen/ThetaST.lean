import Mathlib
import Submission.Work.MotK.TGen.STRulingTheta
import Submission.Work.MotK.TGen.ThetaSTDefs
import Submission.Work.MotK.TGen.QZvL
import Submission.Work.MotK.TGen.ThPolyST
import Submission.Work.MotK.TGen.PropCertZv
import Submission.Work.MotK.TGen.STDegenerate

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The ruling line `ZvL a b h = T·rv + rw` of the fibre of the twisted quadro map over the chart
point has its fourth coordinate equal to `1`. -/
theorem ZvL_four (a b h : K) : ZvL a b h 4 = 1 := by
  show Polynomial.C (Work.MotK.TwCensus.rv a b h 4) * Polynomial.X
      + Polynomial.C (Work.MotK.TwCensus.rw a b h 4) = 1
  rw [show Work.MotK.TwCensus.rv a b h 4 = 0 from rfl,
      show Work.MotK.TwCensus.rw a b h 4 = 1 from rfl]
  simp

/-- The secant quintic of the ruling line is the fourth component of the inverse map at the image
of the ruling line: `I1'` (`KleinTwI1`) at `k = 4`, using `ZvL a b h 4 = 1`. -/
theorem SmL_eq_kleinTwR_four (a b h : K) :
    SmL a b h = Work.MotK.kleinTwR (Polynomial.C (MvPolynomial.C a))
      (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (PmL a b h) 4 := by
  have hI1 := Work.MotK.KleinTwI1 (Polynomial.C (MvPolynomial.C a))
    (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (ZvL a b h) 4
  rw [ZvL_four a b h, mul_one] at hI1
  simpa only [SmL, PmL] using hI1.symm

theorem ThetaST (K : Type) [Field K] (a b h : K) :
    Work.MotK.TGen.theta a b h (Work.MotK.TGen.sT a b h) = 0 := by
  by_cases hdeg : a = 0 ∨ b = 0 ∨ h = 0
  · -- degenerate case: `sT` itself vanishes
    rw [STDegenerate K a b h hdeg, map_zero]
  · simp only [not_or] at hdeg
    obtain ⟨ha, hb, hh⟩ := hdeg
    -- ## the inputs of the general case
    have hQ : Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a))
        (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (ZvL a b h) = 0 :=
      QZvL K a b h ha hb
    have hth : Work.MotK.TGen.thPoly a b h (Work.MotK.TGen.sT a b h)
        = (-(BmL a b h)) ^ 5 * SmL a b h := ThPolyST K a b h ha hb hh hQ
    have hcert := PropCertZv K a b h ha hb
    -- ## the coordinate ring `A` of the residual curve and its quotient map
    set A := MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotK.TwCensus.ZI a b h) with hA
    set mkR : MvPolynomial (Fin 3) K →+* A :=
      Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI a b h)) with hmkR
    -- the generators of the residual-curve ideal die in the quotient
    have hmkZ : ∀ k : Fin 5, mkR (Work.MotK.TwCensus.Zcub a b h k) = 0 := by
      intro k
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.le_radical (Ideal.subset_span (Set.mem_range_self k)))
    -- the kernel defect dies in the quotient
    have hWZ : Polynomial.map mkR (WZL a b h) = 0 := by
      simp only [WZL, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
        hmkZ 4, hmkZ 3, Polynomial.C_0, mul_zero, sub_zero]
    -- ## the proportionality `PmL ≡ PmL 4 · chartPt` in the quotient
    have hprop : ∀ k : Fin 5, Polynomial.map mkR (PmL a b h k)
        = Polynomial.map mkR (PmL a b h 4)
          * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) k)) := by
      intro k
      fin_cases k
      · -- `k = 0`: both sides vanish
        show Polynomial.map mkR (PmL a b h 0)
            = Polynomial.map mkR (PmL a b h 4)
              * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) 0))
        have hz : PmL a b h (0 : Fin 5)
            = Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a))
                (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h))
                (ZvL a b h) := rfl
        rw [hz, hQ, Polynomial.map_zero,
          show Work.MotK.TwCensus.chartPt (K := K) (0 : Fin 5) = 0 from rfl, map_zero]
        simp only [Polynomial.C_0, mul_zero]
      · -- `k = 1`
        show Polynomial.map mkR (PmL a b h 1)
            = Polynomial.map mkR (PmL a b h 4)
              * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) 1))
        have hh1 := congrArg (Polynomial.map mkR) hcert.1
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] at hh1
        rw [hWZ, mul_zero, sub_eq_zero] at hh1
        exact hh1
      · -- `k = 2`
        show Polynomial.map mkR (PmL a b h 2)
            = Polynomial.map mkR (PmL a b h 4)
              * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) 2))
        have hh2 := congrArg (Polynomial.map mkR) hcert.2.1
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] at hh2
        rw [hWZ, mul_zero, sub_eq_zero] at hh2
        exact hh2
      · -- `k = 3`
        show Polynomial.map mkR (PmL a b h 3)
            = Polynomial.map mkR (PmL a b h 4)
              * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) 3))
        have hh3 := congrArg (Polynomial.map mkR) hcert.2.2
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] at hh3
        rw [hWZ, mul_zero, sub_eq_zero] at hh3
        exact hh3
      · -- `k = 4`: trivial
        show Polynomial.map mkR (PmL a b h 4)
            = Polynomial.map mkR (PmL a b h 4)
              * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) 4))
        rw [show Work.MotK.TwCensus.chartPt (K := K) (4 : Fin 5) = 1 from rfl, map_one,
          Polynomial.C_1, mul_one]
    -- ## the factor `kleinTwR _ chartPt` vanishes in the quotient
    have h2 : Work.MotK.kleinTwR (mkR (MvPolynomial.C a)) (mkR (MvPolynomial.C b))
          (mkR (MvPolynomial.C h))
          (fun k => mkR (Work.MotK.TwCensus.chartPt (K := K) k)) 4 = 0 := by
      have h1 : Work.MotK.kleinTwR (mkR (MvPolynomial.C a)) (mkR (MvPolynomial.C b))
            (mkR (MvPolynomial.C h))
            (fun k => mkR (Work.MotK.TwCensus.chartPt (K := K) k)) 4
          = mkR (Work.MotK.TwCensus.Zcub a b h 4) :=
        (@Work.MotK.KleinTwData.map_data (MvPolynomial (Fin 3) K) A _ _ mkR
          (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)).2.2.2.2.2
          (Work.MotK.TwCensus.chartPt (K := K)) 4
      rw [h1, hmkZ 4]
    have h3 : Work.MotK.kleinTwR (Polynomial.C (mkR (MvPolynomial.C a)))
          (Polynomial.C (mkR (MvPolynomial.C b))) (Polynomial.C (mkR (MvPolynomial.C h)))
          (fun k => Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) k))) 4 = 0 := by
      have hCnat : Polynomial.C (Work.MotK.kleinTwR (mkR (MvPolynomial.C a))
            (mkR (MvPolynomial.C b)) (mkR (MvPolynomial.C h))
            (fun k => mkR (Work.MotK.TwCensus.chartPt (K := K) k)) 4)
          = Work.MotK.kleinTwR (Polynomial.C (mkR (MvPolynomial.C a)))
              (Polynomial.C (mkR (MvPolynomial.C b))) (Polynomial.C (mkR (MvPolynomial.C h)))
              (fun k => Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) k))) 4 :=
        (@Work.MotK.KleinTwData.map_data A (Polynomial A) _ _
          (algebraMap A (Polynomial A)) (mkR (MvPolynomial.C a)) (mkR (MvPolynomial.C b))
          (mkR (MvPolynomial.C h))).2.2.2.2.2
          (fun k => mkR (Work.MotK.TwCensus.chartPt (K := K) k)) 4
      rw [← hCnat, h2, Polynomial.C_0]
    -- ## the image of the secant quintic vanishes
    have hSm : Polynomial.map mkR (SmL a b h) = 0 := by
      rw [SmL_eq_kleinTwR_four a b h]
      -- naturality of `kleinTwR` under `Polynomial.map mkR`
      rw [show Polynomial.map mkR
            (Work.MotK.kleinTwR (Polynomial.C (MvPolynomial.C a))
              (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h))
              (PmL a b h) 4)
          = Work.MotK.kleinTwR (Polynomial.map mkR (Polynomial.C (MvPolynomial.C a)))
              (Polynomial.map mkR (Polynomial.C (MvPolynomial.C b)))
              (Polynomial.map mkR (Polynomial.C (MvPolynomial.C h)))
              (fun k => Polynomial.map mkR (PmL a b h k)) 4 from
        (@Work.MotK.KleinTwData.map_data (Polynomial (MvPolynomial (Fin 3) K)) (Polynomial A) _ _
          (Polynomial.mapRingHom mkR) (Polynomial.C (MvPolynomial.C a))
          (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h))).2.2.2.2.2
          (PmL a b h) 4]
      -- the proportionality, as an identity of vectors
      rw [show (fun k => Polynomial.map mkR (PmL a b h k))
            = fun k => Polynomial.map mkR (PmL a b h 4)
                * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) k)) from funext hprop]
      -- the coefficients land in the `Polynomial.C`-image of `A`
      rw [show Polynomial.map mkR (Polynomial.C (MvPolynomial.C a))
            = Polynomial.C (mkR (MvPolynomial.C a)) from by rw [Polynomial.map_C],
        show Polynomial.map mkR (Polynomial.C (MvPolynomial.C b))
            = Polynomial.C (mkR (MvPolynomial.C b)) from by rw [Polynomial.map_C],
        show Polynomial.map mkR (Polynomial.C (MvPolynomial.C h))
            = Polynomial.C (mkR (MvPolynomial.C h)) from by rw [Polynomial.map_C]]
      -- homogeneity in the ruling parameter
      rw [show Work.MotK.kleinTwR (Polynomial.C (mkR (MvPolynomial.C a)))
            (Polynomial.C (mkR (MvPolynomial.C b))) (Polynomial.C (mkR (MvPolynomial.C h)))
            (fun k => Polynomial.map mkR (PmL a b h 4)
              * Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) k))) 4
          = (Polynomial.map mkR (PmL a b h 4)) ^ 3
            * Work.MotK.kleinTwR (Polynomial.C (mkR (MvPolynomial.C a)))
              (Polynomial.C (mkR (MvPolynomial.C b))) (Polynomial.C (mkR (MvPolynomial.C h)))
              (fun k => Polynomial.C (mkR (Work.MotK.TwCensus.chartPt (K := K) k))) 4 from
        congrFun (Work.MotK.kleinTwR_homog _ _ _ _ _) 4]
      rw [h3, mul_zero]
    -- ## conclude
    show Polynomial.mapAlgHom
        (Ideal.Quotient.mkₐ K (Ideal.radical (Work.MotK.TwCensus.ZI a b h)))
        (Work.MotK.TGen.thPoly a b h (Work.MotK.TGen.sT a b h)) = 0
    rw [hth, map_mul, map_pow,
      show Polynomial.mapAlgHom
          (Ideal.Quotient.mkₐ K (Ideal.radical (Work.MotK.TwCensus.ZI a b h)))
          (SmL a b h) = Polynomial.map mkR (SmL a b h) from rfl,
      hSm, mul_zero]

end Work.MotK.TGen
