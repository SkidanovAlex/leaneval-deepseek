import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBoxFock.PCFU.Bdecomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chBpointwise` — the pointwise `(B)`-slot estimate

The pointwise `(B)`-slot estimate of the cubic dictionary: the windowed `χ̂`-weighted `univ` frame
`KχfrU` minus its direct `χ_Λ ⋆ W₁` pairing is bounded by the two error terms which the dictionary
supplies as hypotheses:

* `hCE`  — the **UV-smearing error** `χ_Λ ⋆ (ψ_Λ ⋆ W₁ − W₁)` (`chiStarE_le`),
* `himg` — the **lattice images** `χ_Λ ⋆ Σ'_{d≠0} (ψ_Λ ⋆ W₁)(· + ℓ•d)` (`chB_img_le`).

## Route

The whole content is the decomposition `Bdecomp` (the periodisation identity
`KchiFrU_eq_periodisation` with the `d = 0` term split off), followed by the triangle inequality
for the Bochner norm and the two given estimates.  The factor `(√chiNormSq)⁻¹` multiplying `CE/Λ`
is the sup bound on the window, `χ_Λ(z) ≤ (√chiNormSq)⁻¹`.

Two bookkeeping points are worth recording:

* the second summand of `Bdecomp` carries the lattice sum in the form `↑(Σ'_ℝ …)`, whereas the
  hypothesis `himg` carries it as `Σ'_ℂ (↑…)`; the two are identified by `Complex.ofReal_tsum`
  (which in this Mathlib is *unconditional*) together with `tsum_congr` (splitting off `d = 0`);
* the first summand is a `ℂ`-valued integral of a real-valued integrand, converted to the real
  integral by `integral_ofReal` (also unconditional in this Mathlib), after which it matches the
  hypothesis `hCE` verbatim.

The abstract core is factored out as the private lemma `chB_est`, whose parameters are exactly the
objects appearing in `Bdecomp` and in the two hypotheses; `chBpointwise` is then one instantiation.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The abstract pointwise `(B)`-slot estimate.**  Given the decomposition
`K = χ_Λ ⋆ E + Img` (`hbd`), the sup bound on the window (`hχsup`), the smearing-error estimate
`hCE` and the image estimate `himg`, the windowed difference obeys the sum of the two bounds.

All parameters are the objects appearing in `Bdecomp`, so that `chBpointwise` is a pure
instantiation. -/
private lemma chB_est {χ W1 U : E3 → ℝ} {ℓ Λ CE Kimg R : ℝ} {K : ℂ} {z : E3}
    (hχ0 : ∀ w : E3, 0 ≤ χ w)
    (hχsup : χ z ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹)
    (hCE0 : 0 ≤ CE) (hΛ : 0 < Λ)
    (hbd : K - (∫ y : E3, ((χ y : ℝ) : ℂ) * ((W1 (y - z) : ℝ) : ℂ))
        = (∫ w : E3, ((χ w : ℝ) : ℂ) * (((U (z - w) - W1 (z - w) : ℝ)) : ℂ))
          + (∫ w : E3, ((χ w : ℝ) : ℂ)
              * (((∑' d : Fin 3 → ℤ, if d = 0 then 0
                  else U (z - w + ℓ • Work.BoseBoxFock.latVec d)) : ℝ) : ℂ)))
    (hCE : |∫ w : E3, χ w * (U (z - w) - W1 (z - w))| ≤ CE / Λ)
    (himg : χ z * (∫ w : E3, χ w
        * ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
            else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖)
      ≤ Kimg * (∫ x : E3, |W1 x|)
          * ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)) :
    χ z * ‖K - (∫ y : E3, ((χ y : ℝ) : ℂ) * ((W1 (y - z) : ℝ) : ℂ))‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE / Λ
        + Kimg * (∫ x : E3, |W1 x|)
            * ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by
  classical
  -- ## The two spellings of the lattice sum agree
  have htsum : ∀ w : E3,
      (((∑' d : Fin 3 → ℤ, if d = 0 then 0
          else U (z - w + ℓ • Work.BoseBoxFock.latVec d)) : ℝ) : ℂ)
        = (∑' d : Fin 3 → ℤ, if d = 0 then 0
            else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
    intro w
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun d => by by_cases hd : d = 0 <;> simp [hd])
  -- ## The first summand against `hCE`
  have hS1eq : (∫ w : E3, ((χ w : ℝ) : ℂ) * (((U (z - w) - W1 (z - w)) : ℝ) : ℂ))
      = (((∫ w : E3, χ w * (U (z - w) - W1 (z - w)) : ℝ)) : ℂ) := by
    have h1 : (∫ w : E3, ((χ w : ℝ) : ℂ) * (((U (z - w) - W1 (z - w)) : ℝ) : ℂ))
        = ∫ w : E3, (((χ w * (U (z - w) - W1 (z - w))) : ℝ) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun w => by simp only [Complex.ofReal_mul])
    exact h1.trans (integral_ofReal (μ := volume) (𝕜 := ℂ)
      (f := fun w => χ w * (U (z - w) - W1 (z - w))))
  have hS1 : ‖(∫ w : E3, ((χ w : ℝ) : ℂ) * (((U (z - w) - W1 (z - w)) : ℝ) : ℂ))‖ ≤ CE / Λ := by
    rw [hS1eq, Complex.norm_real, Real.norm_eq_abs]
    exact hCE
  -- ## The second summand against `himg`
  have hS2 : ‖(∫ w : E3, ((χ w : ℝ) : ℂ)
        * (((∑' d : Fin 3 → ℤ, if d = 0 then 0
            else U (z - w + ℓ • Work.BoseBoxFock.latVec d)) : ℝ) : ℂ))‖
      ≤ ∫ w : E3, χ w * ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
            else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ := by
    calc ‖(∫ w : E3, ((χ w : ℝ) : ℂ)
            * (((∑' d : Fin 3 → ℤ, if d = 0 then 0
                else U (z - w + ℓ • Work.BoseBoxFock.latVec d)) : ℝ) : ℂ))‖
        = ‖(∫ w : E3, ((χ w : ℝ) : ℂ)
            * (∑' d : Fin 3 → ℤ, if d = 0 then 0
                else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))‖ := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun w => by simp only [htsum w])
      _ ≤ ∫ w : E3, ‖((χ w : ℝ) : ℂ)
            * (∑' d : Fin 3 → ℤ, if d = 0 then 0
                else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ w : E3, χ w * ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
                else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
  -- ## The triangle inequality and the assembly
  rw [hbd]
  calc χ z * ‖(∫ w : E3, ((χ w : ℝ) : ℂ) * (((U (z - w) - W1 (z - w)) : ℝ) : ℂ))
          + (∫ w : E3, ((χ w : ℝ) : ℂ)
              * (((∑' d : Fin 3 → ℤ, if d = 0 then 0
                  else U (z - w + ℓ • Work.BoseBoxFock.latVec d)) : ℝ) : ℂ))‖
      ≤ χ z * (‖(∫ w : E3, ((χ w : ℝ) : ℂ) * (((U (z - w) - W1 (z - w)) : ℝ) : ℂ))‖
          + ‖(∫ w : E3, ((χ w : ℝ) : ℂ)
              * (((∑' d : Fin 3 → ℤ, if d = 0 then 0
                  else U (z - w + ℓ • Work.BoseBoxFock.latVec d)) : ℝ) : ℂ))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (hχ0 z)
    _ ≤ χ z * (CE / Λ) + χ z * (∫ w : E3, χ w
          * ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
              else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖) := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left hS1 (hχ0 z))
          (mul_le_mul_of_nonneg_left hS2 (hχ0 z))
    _ ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * (CE / Λ)
          + Kimg * (∫ x : E3, |W1 x|)
            * ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by
        refine add_le_add ?_ himg
        exact mul_le_mul_of_nonneg_right hχsup (div_nonneg hCE0 hΛ.le)
    _ = (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE / Λ
          + Kimg * (∫ x : E3, |W1 x|)
            * ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by ring

theorem chBpointwise {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {μ R : ℝ} {N : ℕ}
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) (hN : 1 ≤ N)
    (hΛ : 1 ≤ Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
    (hΛℓ : 1 ≤ Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N * Work.BoseBoxFock.ellH v μ)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hev : ∀ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
    {CE Kimg : ℝ} (hCE0 : 0 ≤ CE)
    (hCE : ∀ z : EuclideanSpace ℝ (Fin 3),
        |∫ w : EuclideanSpace ℝ (Fin 3), (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w) *
            (Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (z - w)
              - Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (z - w))|
          ≤ CE / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
    (himg : ∀ z : EuclideanSpace ℝ (Fin 3),
        (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z) *
          (∫ w : EuclideanSpace ℝ (Fin 3), (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w) *
            ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0 else
              ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (z - w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖)
        ≤ Kimg * (∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x|) *
          ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N * (Work.BoseBoxFock.ellH v μ))⁻¹
            + (R / (Work.BoseBoxFock.ellH v μ)) ^ 4
            + ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N * (Work.BoseBoxFock.ellH v μ)) ^ 2)⁻¹))
    (z : EuclideanSpace ℝ (Fin 3)) :
    (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z) *
      ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
        - (∫ y : EuclideanSpace ℝ (Fin 3),
            ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ) *
            ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (y - z) : ℝ) : ℂ))‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE
          / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
        + Kimg * (∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x|) *
            ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N * (Work.BoseBoxFock.ellH v μ))⁻¹
              + (R / (Work.BoseBoxFock.ellH v μ)) ^ 4
              + ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N * (Work.BoseBoxFock.ellH v μ)) ^ 2)⁻¹) := by
  refine chB_est (χ := fun x => Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) x)
    (W1 := fun x => Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
    (U := fun x => Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
      (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) x)
    (ℓ := Work.BoseBoxFock.ellH v μ) (Λ := Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
    (K := Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z) (CE := CE) (Kimg := Kimg) (z := z) (R := R)
    (fun w => chiLam_nonneg' _ w)
    (chiLam_le_chiSupAbs _ z)
    hCE0
    (lt_of_lt_of_le zero_lt_one hΛ)
    (Work.BoseBoxFock.PCFU.Bdecomp (v := v) (h := h) (fu := fu) (μ := μ) (N := N)
      hℓ0 hN hI hcs hev z)
    (hCE z) (himg z)

end Work.BoseBoxFock.PCFU
