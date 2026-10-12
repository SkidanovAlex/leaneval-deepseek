import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Eps.Arith
import Submission.Work.BoseFixB3.Eps.convI_abs_le
import Submission.Work.BoseFixB3.Eps.hRes_bound
import Submission.Work.BoseFixB3.Eps.q3convWord_abs_le
import Submission.Work.BoseFixB3.Eps.sideAt_ge_of_dilute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Eps/b3EpsRoot_holds` — FS's `ε₂`-Cauchy–Schwarz

FS `lem:Q3-splitting1`, `Papers/fournais_solovej/final_v2.tex` ll. 1531–1545: the
convolution word `q3convWord` (the sum `Σ_{i,j}⟨P_iΦ, Q̄_{L,j}χ_Λ²P_jΦ⟩` produced by
`lem:Convolution`) is bounded below by

  `−Kμ²aℓ³·d^{2(M-1)}·‖Φ‖² − (b/200)ε_T(dℓ)⁻²n₊^H`

for dilute parameters.  FS's proof is the `ε₂`-Cauchy–Schwarz with
`ε₂ = (K_ℓK_L)^{-2M̃}`, which in the `p`-language reduces to two facts:

* the one-body residual `(1−f_L)(χ_ℓ²)` has size `(κℓ)^{-49}` uniformly
  (`Work.BoseFixB3.Eps.hRes_abs_le`, with `49 > M−1 = 47`);
* the convolution constant satisfies `|I| = |∫W₁ω| ≤ 16πa` (`convI_abs_le`);

together with the two elementary bounds `n ≤ 2μℓ³` (FS `eq:apriorinn+`) and
`Σ_j Q̄_{L,j}Q̄_{L,j}^* ≤ n₊^H` — the latter is *not even needed* here, because the
`n₊^H`-term on the right-hand side of `B3EpsRoot` is negative and may simply be dropped.

The `ε₂`-bookkeeping is thus absorbed into the universal constant `64πCH`: the word
`q3convWord` is `Iℓ^{-3}Σ_{i,j}∫P_iΦ·(1−f_L)_j(χ_Λ²P_jΦ)` and, because `P_jΦ` is
constant in the slot `j`, the multiplier acts on the fixed profile `χ_ℓ²` alone, so

  `|q3convWord| ≤ |I|ℓ^{-3}·CH(κℓ)^{-49}·n²‖Φ‖²
                ≤ 16πa·ℓ^{-3}·CH d^{94}·4μ²ℓ⁶‖Φ‖² = 64πCH·μ²aℓ³d^{94}‖Φ‖²`.

(FS obtain the same estimate with `d^{2(M-1)}` and the `n₊^H`-term playing the role of
the discarded error.)
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Eps

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem b3EpsRoot_holds (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (R : ℝ) (fc : Work.BoseBoxFix.LowCut)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v) :
    Work.BoseFixB3.B3EpsRoot v h fc := by
  classical
  obtain ⟨CH, hCH0, hCH⟩ := hRes_abs_le
  obtain ⟨ε₁, hε₁0, hε₁le, hε₁⟩ := sideAt_ge_of_dilute v hav hR
  refine ⟨64 * π * CH, min ε₁ 1, by positivity, lt_min hε₁0 one_pos, ?_⟩
  intro μ hAdm n Φ hn
  obtain ⟨hμ0, hμa3, hPO⟩ := hAdm
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := le_trans hμa3 (min_le_right _ _)
  have hε : μ * (BoseGases.a v) ^ 3 ≤ ε₁ := le_trans hμa3 (min_le_left _ _)
  have htpos : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hℓ : 0 < ellAt μ (BoseGases.a v) := ellAt_pos μ (BoseGases.a v) hμ0 hav
  have hℓne : ellAt μ (BoseGases.a v) ≠ 0 := ne_of_gt hℓ
  have hκ : 0 < kapAt μ (BoseGases.a v) := kapAt_pos htpos hℓ
  have hκℓ : 1 ≤ kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v) :=
    kapAt_mul_ellAt_ge_one htpos ht1 hℓne
  have hΦc : Continuous (Φ : X n → ℝ) := Φ.contDiff.continuous
  -- the one-body residual estimate
  have hH : ∀ z : EuclideanSpace ℝ (Fin 3),
      |hRes fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v)) z| ≤
        CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ)) :=
    fun z => hCH fc _ _ hκ hℓ hκℓ z
  have hC0 : (0 : ℝ) ≤
      CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ)) :=
    mul_nonneg hCH0 (zpow_nonneg (by positivity) _)
  -- the four numerical inputs
  have hI : |convI (ellAt μ (BoseGases.a v)) v h| ≤ 16 * π * BoseGases.a v :=
    convI_abs_le hv hvrad hR hv_supp hℓ (hε₁ μ hμ0 hε)
  have hdil : (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))
      ≤ (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1)) :=
    kapAt_ellAt_zpow_le_d μ (BoseGases.a v) htpos ht1 hℓne
  have hnn : ((n : ℝ)) ^ 2 ≤ (2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
  have hNB : 0 ≤ normB v μ n (Φ : X n → ℝ) := by
    simp only [normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg fun x => sq_nonneg _
  have ha0 : 0 ≤ BoseGases.a v := hav.le
  have hb0 : 0 ≤ (patAt μ (BoseGases.a v)).b := by
    rw [patAt_b]; exact bValue_pos.le
  have heT0 : 0 ≤ (patAt μ (BoseGases.a v)).eT := by
    rw [patAt_eT]; exact fsXp_nonneg (by positivity)
  have hd0 : 0 ≤ (patAt μ (BoseGases.a v)).d := (patAt_d_pos htpos).le
  -- the `n₊^H`-term on the right is nonnegative, so it may be discarded
  have hnp : 0 ≤ (patAt μ (BoseGases.a v)).b / 200 * (patAt μ (BoseGases.a v)).eT *
      ((patAt μ (BoseGases.a v)).d * ellAt μ (BoseGases.a v)) ^ (-(2 : ℤ)) *
      nPlusHB (ellAt μ (BoseGases.a v)) (patAt μ (BoseGases.a v)).d (Φ : X n → ℝ) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hb0 (by norm_num)) heT0) ?_)
      (nPlusHB_nonneg hℓ _)
    exact zpow_nonneg (mul_nonneg hd0 hℓ.le) _
  -- the word bound
  have hq : q3convWord fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
        (convI (ellAt μ (BoseGases.a v)) v h) (Φ : X n → ℝ)
      ≤ 64 * π * CH * μ ^ 2 * BoseGases.a v * (ellAt μ (BoseGases.a v)) ^ 3 *
          (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1)) *
          normB v μ n (Φ : X n → ℝ) := by
    have h1 := q3convWord_abs_le (fc := fc) (κ := kapAt μ (BoseGases.a v))
      (ℓ := ellAt μ (BoseGases.a v)) (I := convI (ellAt μ (BoseGases.a v)) v h)
      (C := CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ)))
      hℓ hC0 hΦc hH
    have hL3 : (0 : ℝ) ≤ (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) := zpow_nonneg hℓ.le _
    have hP0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have hQ0 : (0 : ℝ) ≤ ∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have hA0 : (0 : ℝ) ≤ 16 * π * BoseGases.a v := by positivity
    have hstep1 : |convI (ellAt μ (BoseGases.a v)) v h| *
          (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))
        ≤ (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := by
      have hX : (0 : ℝ) ≤ (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) :=
        mul_nonneg (mul_nonneg hL3 hC0) (mul_nonneg hP0 hQ0)
      have hle := mul_le_mul_of_nonneg_right hI hX
      calc |convI (ellAt μ (BoseGases.a v)) v h| *
            (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
            (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
            ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))
          = |convI (ellAt μ (BoseGases.a v)) v h| *
            ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
              (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
              ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))) := by
            ring
        _ ≤ (16 * π * BoseGases.a v) *
            ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
              (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
              ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))) := hle
        _ = (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
            (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
            ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := by
            ring
    have hstep2 : (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))
        ≤ (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
            (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := by
      have hX : (0 : ℝ) ≤ (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) :=
        mul_nonneg (mul_nonneg hA0 hL3) hC0
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnn hQ0) hX
    have hstep3 : (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
            (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))
        ≤ (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1))) *
          ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
            (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := by
      have hY : (0 : ℝ) ≤ (2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
          (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2) := by positivity
      have hD : (0 : ℝ) ≤ (patAt μ (BoseGases.a v)).d ^
          (2 * ((patAt μ (BoseGases.a v)).M - 1)) :=
        pow_nonneg hd0 (2 * ((patAt μ (BoseGases.a v)).M - 1))
      have h1' : CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))
          ≤ CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1)) :=
        mul_le_mul_of_nonneg_left hdil hCH0
      have h2' : (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
            (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ)))
          ≤ (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
            (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1))) :=
        mul_le_mul_of_nonneg_left h1' hL3
      have h3' : (16 * π * BoseGases.a v) *
            ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
              (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))))
          ≤ (16 * π * BoseGases.a v) *
            ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
              (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1)))) :=
        mul_le_mul_of_nonneg_left h2' hA0
      have h4' : ((16 * π * BoseGases.a v) *
            ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
              (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))))) *
            ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
              (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))
          ≤ ((16 * π * BoseGases.a v) *
            ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
              (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1))))) *
            ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
              (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) :=
        mul_le_mul_of_nonneg_right h3' hY
      calc (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
            (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
            ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
              (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))
          = ((16 * π * BoseGases.a v) *
              ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
                (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))))) *
              ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
                (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := by
              ring
        _ ≤ ((16 * π * BoseGases.a v) *
              ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
                (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1))))) *
              ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
                (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := h4'
        _ = (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
            (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1))) *
            ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
              (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := by
              ring
    have hfin : (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1))) *
          ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
            (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2))
        = 64 * π * CH * μ ^ 2 * BoseGases.a v * (ellAt μ (BoseGases.a v)) ^ 3 *
          (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1)) *
          normB v μ n (Φ : X n → ℝ) := by
      have hQeq : normB v μ n (Φ : X n → ℝ)
          = ∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2 := rfl
      rw [hQeq]
      have hsq : (2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2
          = 4 * μ ^ 2 * (ellAt μ (BoseGases.a v)) ^ 6 := by ring
      rw [hsq]
      have hz : (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ))
          = ((ellAt μ (BoseGases.a v)) ^ 3)⁻¹ := by
        simp only [zpow_neg, zpow_natCast]
        rfl
      rw [hz]
      field_simp
      ring
    calc q3convWord fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
          (convI (ellAt μ (BoseGases.a v)) v h) (Φ : X n → ℝ)
        ≤ |convI (ellAt μ (BoseGases.a v)) v h| *
            (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
            (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
            ((n : ℝ) ^ 2 *
              (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) :=
          le_trans (le_abs_self _) h1
      _ ≤ (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := hstep1
      _ ≤ (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (kapAt μ (BoseGases.a v) * ellAt μ (BoseGases.a v)) ^ (-(49 : ℤ))) *
          ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
            (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := hstep2
      _ ≤ (16 * π * BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ)) *
          (CH * (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1))) *
          ((2 * μ * (ellAt μ (BoseGases.a v)) ^ 3) ^ 2 *
            (∫ x in abox n (ellAt μ (BoseGases.a v)), (Φ x) ^ 2)) := hstep3
      _ = 64 * π * CH * μ ^ 2 * BoseGases.a v * (ellAt μ (BoseGases.a v)) ^ 3 *
          (patAt μ (BoseGases.a v)).d ^ (2 * ((patAt μ (BoseGases.a v)).M - 1)) *
          normB v μ n (Φ : X n → ℝ) := hfin
  linarith [hq, hnp]

end Work.BoseFixB3.Eps
