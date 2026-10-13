import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefPrep
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## E. The pointwise bound for the `ℋ³`-integrand -/

/-- The sum of the squares of the weighted `D_z`-iterates of the radial profile. -/
def radSnorm (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 4, ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2

/-- The radial part of the constant, chosen large enough for the termwise bounds. -/
def radC0 : ℝ := max 400 (25600 * radTB ^ 2)

/-- The angular integrand whose integral bounds the angular part. -/
def radAngInt (α : ℝ) (θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The pointwise majorant of the `ℋ³`-integrand. -/
def radAMaj (α : ℝ) (θ : ℝ) : ℝ := 16 * radC0 * radAngInt α θ

/-! ## Unfolding lemmas for the four definitions above -/

lemma radSnorm_apply (z : ℝ) :
    radSnorm z = ∑ j ∈ Finset.range 4,
      ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 := rfl

lemma radC0_def : radC0 = max 400 (25600 * radTB ^ 2) := rfl

lemma radAngInt_apply (α θ : ℝ) :
    radAngInt α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl

lemma radAMaj_apply (α θ : ℝ) : radAMaj α θ = 16 * radC0 * radAngInt α θ := rfl

lemma sq_le_radSnorm {z : ℝ} {j : ℕ} (hj : j ≤ 3) :
    ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ radSnorm z :=
  Finset.single_le_sum (f := fun j : ℕ => ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))

lemma radSnorm_nonneg (z : ℝ) : 0 ≤ radSnorm z :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma radSnorm_zero : radSnorm 0 = 0 := by
  rw [radSnorm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Work.Spaces.w]
  norm_num

lemma radC0_ge_hundred : (100 : ℝ) ≤ radC0 := le_trans (by norm_num) (le_max_left _ _)

lemma radC0_ge_radTB : 100 * radTB ^ 2 ≤ radC0 :=
  le_trans (by nlinarith [sq_nonneg radTB]) (le_max_right _ _)

lemma radC0_nonneg : 0 ≤ radC0 := le_trans (by norm_num) radC0_ge_hundred

lemma radAngInt_nonneg {α θ : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) : 0 ≤ radAngInt α θ := by
  rw [radAngInt]
  refine add_nonneg (Real.rpow_nonneg hs _) ?_
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)

/-- The pure `D_z`-family summand of the `ℋ³`-integrand. -/
lemma term_A_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) (hi : i ≤ 3) :
    (Work.Spaces.DzIter i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hdz : Work.Spaces.DzIter i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
      = gamCoefAng α θ * (Work.Spaces.Zop^[i] bcoefRad) z := by
    rw [DzIter_ang_rad i bcoefRad (gamCoefAng α)]
  rw [hdz]
  have hkey : (gamCoefAng α θ * (Work.Spaces.Zop^[i] bcoefRad) z
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (gamCoefAng α θ) ^ 2 * (((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    rw [show gamCoefAng α θ * (Work.Spaces.Zop^[i] bcoefRad) z
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = gamCoefAng α θ * (((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z)
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) from by ring]
    rw [mul_pow, div_sin_eta_sq _ hs]
  rw [hkey]
  have h1 : (gamCoefAng α θ) ^ 2 ≤ 100 := gamCoefAng_sq_le hα hα1 hθ
  have h2 : ((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ radSnorm z :=
    sq_le_radSnorm (by omega)
  have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
  have h4 : 0 ≤ radSnorm z := radSnorm_nonneg z
  have h5 : (100 : ℝ) ≤ radC0 := radC0_ge_hundred
  calc (gamCoefAng α θ) ^ 2 * (((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 100 * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 h3) (mul_nonneg (sq_nonneg _) h3)
          (by norm_num)
    _ ≤ radC0 * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right h5 (mul_nonneg h4 h3)
    _ = radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring

/-- The mixed summand of the `ℋ³`-integrand. -/
lemma term_B_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ)
    (i j : ℕ) :
    (if 1 ≤ i ∧ i + j ≤ 3 then
        (Work.Spaces.mixed j i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0)
      ≤ radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  by_cases hp : 1 ≤ i ∧ i + j ≤ 3
  · rw [if_pos hp]
    have hi1 : 1 ≤ i := hp.1
    have hi3 : i ≤ 3 := by omega
    have hj3 : j ≤ 3 := by omega
    have hmix : Work.Spaces.mixed j i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
        = (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) * (Work.Spaces.Zop^[j] bcoefRad) z := by
      rw [mixed_ang_rad j i bcoefRad (gamCoefAng α)]
    rw [hmix]
    have hWt := Wt_sq_of_nonneg (α := α) (z := z) (θ := θ) hα hs
    have hkey : ((Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ
          * (Work.Spaces.Zop^[j] bcoefRad) z) * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
          * (((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      rw [mul_pow, hWt]
      ring
    rw [hkey]
    have h1 : (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
        ≤ 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) :=
      dthU_gamCoefAng_sq_le hα hα1 hθ hi1 hi3
    have h2 : ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ radSnorm z := sq_le_radSnorm hj3
    have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs _
    have h4 : 0 ≤ radSnorm z := radSnorm_nonneg z
    have h5 : 0 ≤ 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg radTB)) (mul_nonneg (sq_nonneg α) (sq_nonneg _))
    have h6 : 100 * radTB ^ 2 ≤ radC0 := radC0_ge_radTB
    have h7 : 0 ≤ α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (radSnorm z
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
      mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg _)) (mul_nonneg h4 h3)
    calc (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
          * (((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ (100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2)) * (radSnorm z
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 h3) (mul_nonneg (sq_nonneg _) h3) h5
      _ ≤ radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
          calc (100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2)) * (radSnorm z
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              = (100 * radTB ^ 2) * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
            _ ≤ radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
                mul_le_mul_of_nonneg_right h6 h7
      _ = radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
  · rw [if_neg hp]
    refine mul_nonneg (radSnorm_nonneg z) ?_
    exact mul_nonneg radC0_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg hs _))

/-- **The pointwise bound for the `ℋ³`-integrand of the projector coefficient.** -/
lemma hkIntegrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) z θ ≤ radSnorm z * radAMaj α θ := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst, radSnorm_zero, zero_mul]
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 3 _ z θ hsin]
    have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
      rw [hsin, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
    have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) = 0 := by
      rw [hsin, Real.zero_rpow (by rw [Work.Spaces.gam]; intro h; linarith)]
    have h0 : radSnorm z * radAMaj α θ = 0 := by
      rw [radAMaj, radAngInt, h1, h2]; ring
    rw [h0]
  · have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
    have hSsum : (∑ i ∈ Finset.range 4,
          (Work.Spaces.DzIter i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 4,
            radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
      Finset.sum_le_sum fun i hi => term_A_le hα hα1 hθ i
        (by have := Finset.mem_range.mp hi; omega)
    have hMsum : (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          if 1 ≤ i ∧ i + j ≤ 3 then
            (Work.Spaces.mixed j i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range 4, ∑ _j ∈ Finset.range 4,
            radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => term_B_le hα hα1 hθ i j
    rw [Work.Spaces.HkIntegrand]
    refine le_trans (add_le_add hSsum hMsum) ?_
    have hAe : (∑ _i ∈ Finset.range 4,
          radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        = 4 * (radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have hMe : (∑ _i ∈ Finset.range 4, ∑ _j ∈ Finset.range 4,
          radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
        = 16 * (radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hAe, hMe, radAMaj, radAngInt]
    have hA0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
    have hB0 : 0 ≤ α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)
    have hS0 : 0 ≤ radSnorm z := radSnorm_nonneg z
    have hradC0 : 0 ≤ radC0 := radC0_nonneg
    have hkey : radSnorm z * (16 * radC0 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          - (4 * (radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
            + 16 * (radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))))
        = 12 * (radSnorm z * radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    have hnn : 0 ≤ 12 * (radSnorm z * radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hS0 hradC0) hA0)
    linarith [hkey, hnn]


end Work.FTS.StrongPersist.L3Aux
