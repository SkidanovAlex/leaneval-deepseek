import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBdDefs
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Tools.shiftProdDz_of` — the `D_z` shift-product bound from the pointwise bound

From the pointwise master bound `PtBdDz α` (the content of `Tools/ptBoundDz.lean`) we deduce
the level-`6` `L²`-estimate

`HkSq α 6 (A · D_z f) ≤ C (MA² HkSq α 7 f
   + (1 + KA²) (1 + (γ-1)⁻¹ (HkSq α 6 A + HkSq α 6 f)) (HkSq α 6 A + HkSq α 6 f))`

for `A, f` smooth on the open quadrant with `A ∈ ℋ⁶`, `f ∈ ℋ⁶ ∩ ℋ⁷`, `|A| ≤ MA` and
`|∂_θA| ≤ KA` there.

## Route

`PtBdDz` bounds `HkIntegrand α 6 (A · D_z f)` pointwise by
`K MA² I⁷_f + K (1+(γ-1)⁻¹(|A|²+|f|²)) (I⁶_A + I⁶_f) + K KA² I⁶_f + K Σ_i T_i²`, where the
four `T_i` are the exceptional level-`6` slots pairing a `D_z⁵`-slot with the other datum
(`D_z⁵A · D_zD_θf`, `D_zD_θA · D_z⁵f`, `D_θA · D_z⁵f`, `D_θ²A · D_z⁵f`).

* The pointwise bound is upgraded, using `2ab ≤ a² + b²` and `(Σ|T_i|)² ≤ 4ΣT_i²`, to
  `K MA² I⁷_f + K(1+(γ-1)⁻¹(|A|²+|f|²))(I⁶_A+I⁶_f) + K(2 KA² I⁶_f + 8 Σ_i T_i²)`
  (so that every remaining slot enters with a factor at least `2`, which the final arithmetic
  spends on the `(1+KA²)` that multiplies the middle term).
* Each `T_i` is `L²`-square integrable with
  `L2Sq T_i ≤ C_i (γ-1)⁻¹ |A|²_{ℋ⁶} |f|²_{ℋ⁶}`, which is
  `N6Trans.T1SixAux.excDz5_mixed_pair_bound` at `(b,a) = (1,1), (1,1), (0,1), (0,2)`.
* The θ-slices and then the `z`-integrals are estimated by monotone convergence
  (`MeasurableTheory.integral_mono_of_nonneg`) plus the linearity of the iterated integral,
  and the final bookkeeping is the elementary lemma `arith_key` below (the `2ab`-trick plus
  `(γ-1)⁻¹ ≥ 10`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces

/-- The final arithmetic of the `D_z` shift-product bound: given the four exceptional `L²`-bounds
(each of the shape `≤ C_i (γ-1)⁻¹ |A|²_{ℋ⁶}|f|²_{ℋ⁶}`) and the `2ab`-bound
`4(γ-1)⁻¹|A|²|f|² ≤ (1+(γ-1)⁻¹(|A|²+|f|²))(|A|²+|f|²)`, the sum of the pieces estimated
pointwise is dominated by the claimed right-hand side with constant `4K + 2K Σ_i C_i + 1`. -/
private lemma arith_key {K Csum MA2 F7 KA2 CC γi A6 F6 S4 : ℝ}
    (hK : 0 ≤ K) (hCsum : 0 ≤ Csum) (hMA2 : 0 ≤ MA2) (hF7 : 0 ≤ F7) (hKA2 : 0 ≤ KA2)
    (hA6 : 0 ≤ A6) (hF6 : 0 ≤ F6) (hCC1 : 1 ≤ CC)
    (hS4 : S4 ≤ Csum * γi * A6 * F6)
    (hkey : 4 * (γi * A6 * F6) ≤ CC * (A6 + F6)) :
    K * MA2 * F7 + K * CC * (A6 + F6) + K * (2 * KA2 * F6 + 8 * S4)
      ≤ (4 * K + 2 * K * Csum + 1) * (MA2 * F7 + (1 + KA2) * CC * (A6 + F6)) := by
  have hT : 0 ≤ CC * (A6 + F6) := by positivity
  have hMnn : 0 ≤ MA2 * F7 + (1 + KA2) * CC * (A6 + F6) := by positivity
  have hKnn : 0 ≤ MA2 * F7 := by positivity
  have h1 : MA2 * F7 ≤ MA2 * F7 + (1 + KA2) * CC * (A6 + F6) := by
    linarith [show 0 ≤ (1 + KA2) * CC * (A6 + F6) by positivity]
  have h2 : CC * (A6 + F6) ≤ MA2 * F7 + (1 + KA2) * CC * (A6 + F6) := by
    have h2a : (1 : ℝ) ≤ 1 + KA2 := by linarith
    have h2b : CC * (A6 + F6) ≤ (1 + KA2) * (CC * (A6 + F6)) :=
      le_mul_of_one_le_left hT h2a
    nlinarith [h2b, hKnn]
  have h3 : KA2 * F6 ≤ MA2 * F7 + (1 + KA2) * CC * (A6 + F6) := by
    have h3a : F6 ≤ A6 + F6 := by linarith
    have h3b : KA2 * F6 ≤ KA2 * (A6 + F6) := mul_le_mul_of_nonneg_left h3a hKA2
    have h3c : KA2 * (A6 + F6) ≤ KA2 * (CC * (A6 + F6)) := by
      refine mul_le_mul_of_nonneg_left ?_ hKA2
      calc A6 + F6 = 1 * (A6 + F6) := (one_mul _).symm
        _ ≤ CC * (A6 + F6) := mul_le_mul_of_nonneg_right hCC1 (by linarith)
    have h3d : KA2 * (CC * (A6 + F6)) ≤ (1 + KA2) * (CC * (A6 + F6)) := by
      nlinarith [hT, hKA2]
    nlinarith [h3b, h3c, h3d, hKnn]
  have h4 : 8 * S4 ≤ 2 * Csum * (CC * (A6 + F6)) := by
    have h4a : 8 * S4 ≤ 8 * (Csum * γi * A6 * F6) := by linarith
    have h4b : 8 * (Csum * γi * A6 * F6) ≤ 2 * Csum * (CC * (A6 + F6)) := by
      nlinarith [hkey, hCsum]
    linarith
  have h5 : 2 * KA2 * F6 ≤ 2 * (MA2 * F7 + (1 + KA2) * CC * (A6 + F6)) := by linarith [h3]
  have h6 : 2 * Csum * (CC * (A6 + F6))
      ≤ 2 * Csum * (MA2 * F7 + (1 + KA2) * CC * (A6 + F6)) := by
    nlinarith [h2, hCsum]
  nlinarith [h1, h2, h3, h4, h5, h6, hMnn, hK, hCsum, hKnn, hT]

theorem shiftProdDz_of (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hB : Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBdDz α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA KA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA) →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dz f z θ)
        ≤ C * (MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + KA ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨K, hK, hBd⟩ := hB
  obtain ⟨C1, hC1, hsp1⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound 1 1 (by norm_num) (by norm_num)
  obtain ⟨C2, hC2, hsp2⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound 1 1 (by norm_num) (by norm_num)
  obtain ⟨C3, hC3, hsp3⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound 0 1 (by norm_num) (by norm_num)
  obtain ⟨C4, hC4, hsp4⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound 0 2 (by norm_num) (by norm_num)
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγnn : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  have hCsum : 0 ≤ C1 + C2 + C3 + C4 := by linarith [hC1.le, hC2.le, hC3.le, hC4.le]
  refine ⟨4 * K + 2 * K * (C1 + C2 + C3 + C4) + 1, by positivity, ?_⟩
  intro A f MA KA hsmA hsmf hmA hmf hmf7 hMA hKA
  have hA6 : 0 ≤ HkSq α 6 A := HkSq_nonneg α 6 A
  have hF6 : 0 ≤ HkSq α 6 f := HkSq_nonneg α 6 f
  have hF7 : 0 ≤ HkSq α 7 f := HkSq_nonneg α 7 f
  have hMA2 : 0 ≤ MA ^ 2 := sq_nonneg MA
  have hKA2 : 0 ≤ KA ^ 2 := sq_nonneg KA
  let E1 : ℝ → ℝ → ℝ := fun z θ => DzIter 5 A z θ * mixed 1 1 f z θ * Wt α z θ
  let E2 : ℝ → ℝ → ℝ := fun z θ => DzIter 5 f z θ * mixed 1 1 A z θ * Wt α z θ
  let E3 : ℝ → ℝ → ℝ := fun z θ => DzIter 5 f z θ * Dth A z θ * Wt α z θ
  let E4 : ℝ → ℝ → ℝ := fun z θ => DzIter 5 f z θ * DthIter 2 A z θ * Wt α z θ
  obtain ⟨hm1, hb1⟩ := hsp1 α A f hα hα1 hsmA hmA hsmf hmf
  obtain ⟨hm2, hb2⟩ := hsp2 α f A hα hα1 hsmf hmf hsmA hmA
  obtain ⟨hm3, hb3⟩ := hsp3 α f A hα hα1 hsmf hmf hsmA hmA
  obtain ⟨hm4, hb4⟩ := hsp4 α f A hα hα1 hsmf hmf hsmA hmA
  have hm1E : L2Mem E1 := hm1
  have hm2E : L2Mem E2 := hm2
  have hm3E : L2Mem E3 := hm3
  have hm4E : L2Mem E4 := hm4
  have hb1E : L2Sq E1 ≤ C1 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by
    calc L2Sq E1 ≤ C1 / (gam α - 1) * HkSq α 6 A * HkSq α 6 f := hb1
      _ = C1 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by rw [div_eq_mul_inv]
  have hb2E : L2Sq E2 ≤ C2 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by
    calc L2Sq E2 ≤ C2 / (gam α - 1) * HkSq α 6 f * HkSq α 6 A := hb2
      _ = C2 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by rw [div_eq_mul_inv]; ring
  have hb3E : L2Sq E3 ≤ C3 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by
    calc L2Sq E3 ≤ C3 / (gam α - 1) * HkSq α 6 f * HkSq α 6 A := hb3
      _ = C3 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by rw [div_eq_mul_inv]; ring
  have hb4E : L2Sq E4 ≤ C4 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by
    calc L2Sq E4 ≤ C4 / (gam α - 1) * HkSq α 6 f * HkSq α 6 A := hb4
      _ = C4 * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by rw [div_eq_mul_inv]; ring
  have hMsum : L2Sq E1 + (L2Sq E2 + (L2Sq E3 + L2Sq E4))
      ≤ (C1 + C2 + C3 + C4) * (gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f := by
    nlinarith [hb1E, hb2E, hb3E, hb4E]
  -- the angular integrals
  let J7 : ℝ → ℝ := fun z => ∫ θ in Iθ, HkIntegrand α 7 f z θ
  let JA : ℝ → ℝ := fun z => ∫ θ in Iθ, HkIntegrand α 6 A z θ
  let JF : ℝ → ℝ := fun z => ∫ θ in Iθ, HkIntegrand α 6 f z θ
  let M1 : ℝ → ℝ := fun z => ∫ θ in Iθ, (E1 z θ) ^ 2
  let M2 : ℝ → ℝ := fun z => ∫ θ in Iθ, (E2 z θ) ^ 2
  let M3 : ℝ → ℝ := fun z => ∫ θ in Iθ, (E3 z θ) ^ 2
  let M4 : ℝ → ℝ := fun z => ∫ θ in Iθ, (E4 z θ) ^ 2
  -- the pointwise bound
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HkIntegrand α 6 (fun z θ => A z θ * Dz f z θ) z θ
        ≤ (K * MA ^ 2 * HkIntegrand α 7 f z θ
          + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
              * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ))
          + K * (2 * KA ^ 2 * HkIntegrand α 6 f z θ
              + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))) := by
    intro z θ hz hθ hθ1
    have h := hBd A f MA KA hsmA hsmf hmA hmf hmf7 hMA hKA z θ hz hθ hθ1
    have d1 : (DzIter 5 A z θ * mixed 1 1 f z θ * Wt α z θ) ^ 2 = (E1 z θ) ^ 2 := rfl
    have d2 : (mixed 1 1 A z θ * DzIter 5 f z θ * Wt α z θ) ^ 2 = (E2 z θ) ^ 2 := by
      show (mixed 1 1 A z θ * DzIter 5 f z θ * Wt α z θ) ^ 2
        = (DzIter 5 f z θ * mixed 1 1 A z θ * Wt α z θ) ^ 2
      ring
    have d3 : (Dth A z θ * DzIter 5 f z θ * Wt α z θ) ^ 2 = (E3 z θ) ^ 2 := by
      show (Dth A z θ * DzIter 5 f z θ * Wt α z θ) ^ 2
        = (DzIter 5 f z θ * Dth A z θ * Wt α z θ) ^ 2
      ring
    have d4 : (DthIter 2 A z θ * DzIter 5 f z θ * Wt α z θ) ^ 2 = (E4 z θ) ^ 2 := by
      show (DthIter 2 A z θ * DzIter 5 f z θ * Wt α z θ) ^ 2
        = (DzIter 5 f z θ * DthIter 2 A z θ * Wt α z θ) ^ 2
      ring
    rw [d1, d2, d3, d4] at h
    have hIF : 0 ≤ HkIntegrand α 6 f z θ := HkIntegrand_nonneg α 6 f z θ
    have hK2 : 0 ≤ KA ^ 2 * HkIntegrand α 6 f z θ := mul_nonneg (sq_nonneg KA) hIF
    have he1 : 0 ≤ (E1 z θ) ^ 2 := sq_nonneg _
    have he2 : 0 ≤ (E2 z θ) ^ 2 := sq_nonneg _
    have he3 : 0 ≤ (E3 z θ) ^ 2 := sq_nonneg _
    have he4 : 0 ≤ (E4 z θ) ^ 2 := sq_nonneg _
    nlinarith [h, hK.le, hIF, hK2, he1, he2, he3, he4,
      mul_nonneg hK.le hK2, mul_nonneg hK.le he1, mul_nonneg hK.le he2,
      mul_nonneg hK.le he3, mul_nonneg hK.le he4]
  -- the angular integration at each positive radius
  have hinner : ∀ z : ℝ, 0 < z →
      (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => A z θ * Dz f z θ) z θ)
        ≤ K * MA ^ 2 * J7 z
          + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z)
          + K * (2 * KA ^ 2 * JF z + 8 * (M1 z + (M2 z + (M3 z + M4 z)))) := by
    intro z hz
    have hzI : z ∈ Iz := hz.le
    have h1 : Integrable (fun θ => K * MA ^ 2 * HkIntegrand α 7 f z θ)
        (volume.restrict Iθ) := (hmf7.1 z hzI).const_mul (K * MA ^ 2)
    have h2 : Integrable (fun θ => K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
        * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ)) (volume.restrict Iθ) :=
      ((hmA.1 z hzI).add (hmf.1 z hzI)).const_mul
        (K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)))
    have h3 : Integrable (fun θ => 2 * KA ^ 2 * HkIntegrand α 6 f z θ)
        (volume.restrict Iθ) := (hmf.1 z hzI).const_mul (2 * KA ^ 2)
    have h4 : Integrable (fun θ => (E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))
        (volume.restrict Iθ) :=
      (hm1E.1 z hzI).add ((hm2E.1 z hzI).add ((hm3E.1 z hzI).add (hm4E.1 z hzI)))
    have h5 : Integrable (fun θ => K * (2 * KA ^ 2 * HkIntegrand α 6 f z θ
        + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))))
        (volume.restrict Iθ) := (h3.add (h4.const_mul 8)).const_mul K
    have hbig : Integrable (fun θ => (K * MA ^ 2 * HkIntegrand α 7 f z θ
          + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
            * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ))
          + K * (2 * KA ^ 2 * HkIntegrand α 6 f z θ
            + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))))
        (volume.restrict Iθ) := (h1.add h2).add h5
    have hGeq : (∫ θ in Iθ, (K * MA ^ 2 * HkIntegrand α 7 f z θ
          + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
            * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ))
          + K * (2 * KA ^ 2 * HkIntegrand α 6 f z θ
            + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))))
        = K * MA ^ 2 * J7 z
          + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z)
          + K * (2 * KA ^ 2 * JF z + 8 * (M1 z + (M2 z + (M3 z + M4 z)))) := by
      have e1 : (∫ θ in Iθ, (K * MA ^ 2 * HkIntegrand α 7 f z θ
            + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
              * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ))
            + K * (2 * KA ^ 2 * HkIntegrand α 6 f z θ
              + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))))
          = (∫ θ in Iθ, K * MA ^ 2 * HkIntegrand α 7 f z θ
              + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
                * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ))
            + (∫ θ in Iθ, K * (2 * KA ^ 2 * HkIntegrand α 6 f z θ
              + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2))))) :=
        MeasureTheory.integral_add (h1.add h2) h5
      have e2 : (∫ θ in Iθ, K * MA ^ 2 * HkIntegrand α 7 f z θ
              + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
                * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ))
          = (∫ θ in Iθ, K * MA ^ 2 * HkIntegrand α 7 f z θ)
            + (∫ θ in Iθ, K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
                * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ)) :=
        MeasureTheory.integral_add h1 h2
      have e3 : (∫ θ in Iθ, K * MA ^ 2 * HkIntegrand α 7 f z θ)
          = K * MA ^ 2 * (∫ θ in Iθ, HkIntegrand α 7 f z θ) :=
        MeasureTheory.integral_const_mul (K * MA ^ 2) _
      have e4 : (∫ θ in Iθ, K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
              * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ))
          = K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
            * ((∫ θ in Iθ, HkIntegrand α 6 A z θ) + (∫ θ in Iθ, HkIntegrand α 6 f z θ)) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (hmA.1 z hzI) (hmf.1 z hzI)]
      have e5 : (∫ θ in Iθ, K * (2 * KA ^ 2 * HkIntegrand α 6 f z θ
              + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))))
          = K * (∫ θ in Iθ, 2 * KA ^ 2 * HkIntegrand α 6 f z θ
              + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))) :=
        MeasureTheory.integral_const_mul K _
      have e6 : (∫ θ in Iθ, 2 * KA ^ 2 * HkIntegrand α 6 f z θ
              + 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2))))
          = (∫ θ in Iθ, 2 * KA ^ 2 * HkIntegrand α 6 f z θ)
            + (∫ θ in Iθ, 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))) :=
        MeasureTheory.integral_add h3 (h4.const_mul 8)
      have e7 : (∫ θ in Iθ, 2 * KA ^ 2 * HkIntegrand α 6 f z θ)
          = 2 * KA ^ 2 * (∫ θ in Iθ, HkIntegrand α 6 f z θ) :=
        MeasureTheory.integral_const_mul (2 * KA ^ 2) _
      have e8 : (∫ θ in Iθ, 8 * ((E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2))))
          = 8 * (∫ θ in Iθ, (E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2))) :=
        MeasureTheory.integral_const_mul 8 _
      have e9 : (∫ θ in Iθ, (E1 z θ) ^ 2 + ((E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)))
          = (∫ θ in Iθ, (E1 z θ) ^ 2)
            + (∫ θ in Iθ, (E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2)) :=
        MeasureTheory.integral_add (hm1E.1 z hzI)
          ((hm2E.1 z hzI).add ((hm3E.1 z hzI).add (hm4E.1 z hzI)))
      have e10 : (∫ θ in Iθ, (E2 z θ) ^ 2 + ((E3 z θ) ^ 2 + (E4 z θ) ^ 2))
          = (∫ θ in Iθ, (E2 z θ) ^ 2) + (∫ θ in Iθ, (E3 z θ) ^ 2 + (E4 z θ) ^ 2) :=
        MeasureTheory.integral_add (hm2E.1 z hzI) ((hm3E.1 z hzI).add (hm4E.1 z hzI))
      have e11 : (∫ θ in Iθ, (E3 z θ) ^ 2 + (E4 z θ) ^ 2)
          = (∫ θ in Iθ, (E3 z θ) ^ 2) + (∫ θ in Iθ, (E4 z θ) ^ 2) :=
        MeasureTheory.integral_add (hm3E.1 z hzI) (hm4E.1 z hzI)
      rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
    rw [← hGeq]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun θ => HkIntegrand_nonneg α 6 _ z θ) hbig ?_
    filter_upwards [ae_mem_Ioo_Iθ_fts] with θ hθ
    exact hpt z θ hz hθ.1 hθ.2
  -- the radial integration
  have hAint : IntegrableOn (fun z => K * MA ^ 2 * J7 z) Iz :=
    hmf7.2.const_mul (K * MA ^ 2)
  have hBint : IntegrableOn (fun z => K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
      * (JA z + JF z)) Iz :=
    (hmA.2.add hmf.2).const_mul (K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)))
  have hSint : IntegrableOn (fun z => M1 z + (M2 z + (M3 z + M4 z))) Iz :=
    (hm1E.2).add ((hm2E.2).add ((hm3E.2).add (hm4E.2)))
  have hCint : IntegrableOn (fun z => K * (2 * KA ^ 2 * JF z
      + 8 * (M1 z + (M2 z + (M3 z + M4 z))))) Iz :=
    (((hmf.2.const_mul (2 * KA ^ 2)).add (hSint.const_mul 8))).const_mul K
  have hHz : (∫ z in Iz, ((K * MA ^ 2 * J7 z
          + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z))
          + K * (2 * KA ^ 2 * JF z + 8 * (M1 z + (M2 z + (M3 z + M4 z))))))
      = K * MA ^ 2 * HkSq α 7 f
        + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (HkSq α 6 A + HkSq α 6 f)
        + K * (2 * KA ^ 2 * HkSq α 6 f
            + 8 * (L2Sq E1 + (L2Sq E2 + (L2Sq E3 + L2Sq E4)))) := by
    have z1 : (∫ z in Iz, ((K * MA ^ 2 * J7 z
            + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z))
            + K * (2 * KA ^ 2 * JF z + 8 * (M1 z + (M2 z + (M3 z + M4 z))))))
        = (∫ z in Iz, K * MA ^ 2 * J7 z
            + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z))
          + (∫ z in Iz, K * (2 * KA ^ 2 * JF z
            + 8 * (M1 z + (M2 z + (M3 z + M4 z))))) :=
      MeasureTheory.integral_add (hAint.add hBint) hCint
    have z2 : (∫ z in Iz, K * MA ^ 2 * J7 z
            + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z))
        = (∫ z in Iz, K * MA ^ 2 * J7 z)
          + (∫ z in Iz, K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z)) :=
      MeasureTheory.integral_add hAint hBint
    have z3 : (∫ z in Iz, K * MA ^ 2 * J7 z) = K * MA ^ 2 * (∫ z in Iz, J7 z) :=
      MeasureTheory.integral_const_mul (K * MA ^ 2) _
    have z4 : (∫ z in Iz, K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z))
        = K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
          * ((∫ z in Iz, JA z) + (∫ z in Iz, JF z)) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmA.2 hmf.2]
    have z5 : (∫ z in Iz, K * (2 * KA ^ 2 * JF z
            + 8 * (M1 z + (M2 z + (M3 z + M4 z)))))
        = K * (∫ z in Iz, 2 * KA ^ 2 * JF z + 8 * (M1 z + (M2 z + (M3 z + M4 z)))) :=
      MeasureTheory.integral_const_mul K _
    have z6 : (∫ z in Iz, 2 * KA ^ 2 * JF z + 8 * (M1 z + (M2 z + (M3 z + M4 z))))
        = (∫ z in Iz, 2 * KA ^ 2 * JF z)
          + (∫ z in Iz, 8 * (M1 z + (M2 z + (M3 z + M4 z)))) :=
      MeasureTheory.integral_add (hmf.2.const_mul (2 * KA ^ 2)) (hSint.const_mul 8)
    have z7 : (∫ z in Iz, 2 * KA ^ 2 * JF z) = 2 * KA ^ 2 * (∫ z in Iz, JF z) :=
      MeasureTheory.integral_const_mul (2 * KA ^ 2) _
    have z8 : (∫ z in Iz, 8 * (M1 z + (M2 z + (M3 z + M4 z))))
        = 8 * (∫ z in Iz, M1 z + (M2 z + (M3 z + M4 z))) :=
      MeasureTheory.integral_const_mul 8 _
    have z9 : (∫ z in Iz, M1 z + (M2 z + (M3 z + M4 z)))
        = (∫ z in Iz, M1 z) + (∫ z in Iz, M2 z + (M3 z + M4 z)) :=
      MeasureTheory.integral_add hm1E.2 ((hm2E.2).add ((hm3E.2).add (hm4E.2)))
    have z10 : (∫ z in Iz, M2 z + (M3 z + M4 z))
        = (∫ z in Iz, M2 z) + (∫ z in Iz, M3 z + M4 z) :=
      MeasureTheory.integral_add hm2E.2 ((hm3E.2).add (hm4E.2))
    have z11 : (∫ z in Iz, M3 z + M4 z) = (∫ z in Iz, M3 z) + (∫ z in Iz, M4 z) :=
      MeasureTheory.integral_add hm3E.2 hm4E.2
    rw [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11]
    rfl
  have hmain : HkSq α 6 (fun z θ => A z θ * Dz f z θ)
      ≤ K * MA ^ 2 * HkSq α 7 f
        + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (HkSq α 6 A + HkSq α 6 f)
        + K * (2 * KA ^ 2 * HkSq α 6 f
            + 8 * (L2Sq E1 + (L2Sq E2 + (L2Sq E3 + L2Sq E4)))) := by
    have hmono : (∫ z in Iz, ∫ θ in Iθ,
          HkIntegrand α 6 (fun z θ => A z θ * Dz f z θ) z θ)
        ≤ ∫ z in Iz, ((K * MA ^ 2 * J7 z
            + K * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (JA z + JF z))
            + K * (2 * KA ^ 2 * JF z + 8 * (M1 z + (M2 z + (M3 z + M4 z))))) :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun z => integral_nonneg fun θ =>
          HkIntegrand_nonneg α 6 (fun z θ => A z θ * Dz f z θ) z θ)
        ((hAint.add hBint).add hCint)
        (by filter_upwards [ae_mem_Ioi_Iz_fts] with z hz; exact hinner z hz)
    rw [hHz] at hmono
    exact hmono
  -- final arithmetic
  have hcc1 : (1 : ℝ) ≤ 1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f) := by
    have : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f) := by positivity
    linarith
  have hkey : 4 * ((gam α - 1)⁻¹ * HkSq α 6 A * HkSq α 6 f)
      ≤ (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f)) * (HkSq α 6 A + HkSq α 6 f) := by
    have h1 : 4 * (HkSq α 6 A * HkSq α 6 f) ≤ (HkSq α 6 A + HkSq α 6 f) ^ 2 := by
      nlinarith [sq_nonneg (HkSq α 6 A - HkSq α 6 f)]
    nlinarith [h1, hγnn, hA6, hF6, mul_nonneg hγnn (add_nonneg hA6 hF6),
      mul_nonneg (mul_nonneg hγnn hA6) hF6]
  exact le_trans hmain (arith_key hK.le hCsum hMA2 hF7 hKA2 hA6 hF6 hcc1 hMsum hkey)

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
