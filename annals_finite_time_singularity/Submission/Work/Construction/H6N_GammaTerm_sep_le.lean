import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Spaces.bt_aux
import Submission.Work.Elliptic.WtoH
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The pointwise `ℋ^k`-bound for a separated `Γ`-type function

For the separated function `F = Kfac α · ρ(z) · ψ(θ)` of `GammaTermAux` (`ρ = rhoR`,
`ψ = psiA α`), the two hypotheses

* `|(D_z^j ρ)(z)·w(z)| ≤ M/(1+z)²` for `j ≤ k` (the `z`-core), and
* `|(D_θ^i ψ)(θ)| ≤ D·Γ(θ)(sin(2θ)² + α)` for `1 ≤ i ≤ k` (the `θ`-core),

give the pointwise bound

`HkIntegrand α k F z θ ≤ (Kfac α)² (M/(1+z)²)² ·
   (4(k+1)·sin(2θ)^{-η} + 2(k+1)² D² (sin(2θ)^{-η} + α² sin(2θ)^{2α/3-γ}))`

on the domain.  This is the `k = 4` computation of `H4N_GammaTerm_le_of_cores`
(`hpt`) with the level `4` made arbitrary: the pure slots contribute `4` each
(`|ψ| ≤ 2`) and the mixed slots `2D²(…)` each; there are `k+1` of the former and
`(k+1)²` index pairs for the latter, and every term is bounded by the same quantity. -/
theorem HkN_GammaTerm_sep_le_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D) (k : ℕ)
    (hMr : ∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2)
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
        ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
  intro z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1z : 0 < 1 + z := by have hz0 : (0 : ℝ) ≤ z := hz; linarith
  by_cases hθi : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · -- interior of the angular interval: bound the pure and the mixed slots termwise
    have hbnd : ∀ j : ℕ, j ≤ k →
        ((Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z) ^ 2
          ≤ (M / (1 + z) ^ 2) ^ 2 := by
      intro j hj
      have hb := hMr j hj z hz
      rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ M / (1 + z) ^ 2)]
      exact hb
    have hψ2 : (psiA α θ) ^ 2 ≤ 4 := by
      have h := mul_self_le_mul_self (abs_nonneg (psiA α θ)) (psiA_abs_le_two hα hθ)
      have h2 := sq_abs (psiA α θ)
      nlinarith [h, h2]
    have hpure : ∀ i : ℕ, i ≤ k →
        (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      intro i hi
      have hsep : Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
          = Kfac α * (Work.Spaces.Zop^[i] rhoR) z * psiA α θ := by
        rw [sepF_DzIter, Zop_iter_const_mul, sepF]
      have hsq := hbnd i hi
      have hψs : (Kfac α * psiA α θ) ^ 2 ≤ (Kfac α) ^ 2 * 4 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hψ2 (sq_nonneg (Kfac α))
      calc (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((Work.Spaces.Zop^[i] rhoR) z * Work.Spaces.w z) ^ 2
              * (Kfac α * psiA α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
            rw [hsep]
            rw [Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
              (a := Kfac α * (Work.Spaces.Zop^[i] rhoR) z * psiA α θ) hθ]
            ring
        _ ≤ (M / (1 + z) ^ 2) ^ 2 * ((Kfac α) ^ 2 * 4)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hsq hψs (sq_nonneg _) (sq_nonneg _))
              (Real.rpow_nonneg hs0 _)
        _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
        (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      intro i j hi hij
      have hsep : Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
          = Kfac α * (Work.Spaces.Zop^[j] rhoR) z * (Work.Spaces.Lop^[i] (psiA α)) θ := by
        rw [sepF_mixed, Zop_iter_const_mul, sepF]
      have hsq := hbnd j (by omega)
      have hcore := hDl i hi (by omega) θ hθi
      have hang := mixed_angle_le hα hα1 hD.le hθ hcore
      calc (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          = (Kfac α) ^ 2 * ((Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z) ^ 2
              * (((Work.Spaces.Lop^[i] (psiA α)) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
            ring
        _ ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg (Kfac α))) hang
              (by positivity) (by positivity)
    rw [Work.Spaces.HkIntegrand]
    have hZsum : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (k + 1),
              ((Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
            Finset.sum_le_sum fun i hi =>
              hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hMsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      set Y : ℝ := (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
      have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
      calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1), Y :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
              · rw [if_neg hc]; exact hYnn
        _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul, hYdef]
            push_cast
            ring
    calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ((Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + ((Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))) :=
          add_le_add hZsum hMsum
      _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
          ring
  · -- angular boundary: `sin(2θ) = 0`, and every term of the integrand vanishes
    have hs : Real.sin (2 * θ) = 0 :=
      Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
    rw [HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
    have h0 : (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) = 0 := by
      rw [hs,
        Real.zero_rpow (by linarith [Work.Spaces.eta_pos] :
          (-(Work.Spaces.eta)) ≠ 0),
        Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith :
          (2 * α / 3 - Work.Spaces.gam α) ≠ 0)]
      ring
    rw [h0]
    simp

theorem H6N_GammaTerm_sep_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D)
    (hMr : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z|
        ≤ M / (1 + z) ^ 2)
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
          (Work.Construction.sepF (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
            (Work.Construction.psiA α)) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * ((28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
  intro z hz θ hθ
  calc Work.Spaces.HkIntegrand α 6
        (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
      ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * (4 * ((6 : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 2 * ((6 : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
        HkN_GammaTerm_sep_le_aux α hα hα1 hM hD 6 hMr hDl z hz θ hθ
    _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * ((28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 98 * D ^ 2 * α ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
        ring

end Work.Construction
