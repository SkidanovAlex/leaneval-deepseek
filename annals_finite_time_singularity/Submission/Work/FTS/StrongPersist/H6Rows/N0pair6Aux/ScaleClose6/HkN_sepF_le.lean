import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Construction.H6N_GammaTerm_sep_le
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Spaces.bt_aux
import Submission.Work.Elliptic.WtoH

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## The `ℋ^k`-integrand of a separated `a(z)·ψ(θ)` against a `z`-core and a `θ`-core

This is the "core" computation of `Work.Construction.HkN_GammaTerm_sep_le_aux`, freed
from the two concrete factors `Kfac α` and `rhoR`: for an arbitrary radial profile `a`
satisfying the `z`-core hypothesis

`|(D_z^j a)(z)·w(z)| ≤ M/(1+z)`  (`j ≤ k`)

and the angular core hypothesis on `ψ = psiA α`

`|(D_θ^i ψ)(θ)| ≤ D·Γ(θ)·(sin(2θ)² + α)`  (`1 ≤ i ≤ k`),

the `ℋ^k`-integrand of the separated function `F = a·ψ` is dominated by the separable
majorant `(M/(1+z))²·(4(k+1)·sin(2θ)^{-η} + 2(k+1)²D²(sin(2θ)^{-η} + α²sin(2θ)^{2α/3-γ}))`.

The pure `D_z`-slots contribute `4(k+1)·sin(2θ)^{-η}` (each term is `≤ (M/(1+z))²·4·sin^{-η}`
by `sq_mul_div_sin` + `|ψ| ≤ 2`), the mixed slots contribute `2(k+1)²D²(...)` each (by
`bt_Wt_sq` + `mixed_angle_le`), and there are `k+1` resp. `(k+1)²` of them.  At the angular
boundary `sin(2θ) = 0` everything vanishes (`HkIntegrand_eq_zero_of_sin_two_eq_zero`). -/
theorem HkN_sepF_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℝ → ℝ} {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D) (k : ℕ)
    (hMr : ∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] a) z * Work.Spaces.w z| ≤ M / (1 + z))
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
        ≤ (M / (1 + z)) ^ 2
          * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
  intro z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Construction.sin_two_nonneg_of_mem_Iθ hθ
  have h1z : 0 < 1 + z := by have hz0 : (0 : ℝ) ≤ z := hz; linarith
  by_cases hθi : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · -- interior of the angular interval: bound the pure and the mixed slots termwise
    have hbnd : ∀ j : ℕ, j ≤ k →
        ((Work.Spaces.Zop^[j] a) z * Work.Spaces.w z) ^ 2 ≤ (M / (1 + z)) ^ 2 := by
      intro j hj
      have hb := hMr j hj z hz
      have hMnn : (0 : ℝ) ≤ M / (1 + z) := div_nonneg hM.le h1z.le
      rw [sq_le_sq, abs_of_nonneg hMnn]
      exact hb
    have hψ2 : (Work.Construction.psiA α θ) ^ 2 ≤ 4 := by
      have h := mul_self_le_mul_self (abs_nonneg (Work.Construction.psiA α θ))
        (Work.Construction.psiA_abs_le_two hα hθ)
      have h2 := sq_abs (Work.Construction.psiA α θ)
      nlinarith [h, h2]
    have hpure : ∀ i : ℕ, i ≤ k →
        (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (M / (1 + z)) ^ 2 * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      intro i hi
      have hsep : Work.Spaces.DzIter i
            (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
          = (Work.Spaces.Zop^[i] a) z * Work.Construction.psiA α θ := by
        rw [Work.Construction.sepF_DzIter]
        rfl
      have hsq := hbnd i hi
      calc (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((Work.Spaces.Zop^[i] a) z * Work.Spaces.w z) ^ 2
              * (Work.Construction.psiA α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
            rw [hsep]
            rw [Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
              (a := (Work.Spaces.Zop^[i] a) z * Work.Construction.psiA α θ) hθ]
            ring
        _ ≤ (M / (1 + z)) ^ 2 * 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hsq hψ2 (sq_nonneg _) (sq_nonneg _))
              (Real.rpow_nonneg hs0 _)
        _ = (M / (1 + z)) ^ 2 * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
        (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ (M / (1 + z)) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      intro i j hi hij
      have hsep : Work.Spaces.mixed j i
            (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
          = (Work.Spaces.Zop^[j] a) z * (Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ := by
        rw [Work.Construction.sepF_mixed]
        rfl
      have hsq := hbnd j (by omega)
      have hcore := hDl i hi (by omega) θ hθi
      have hang := Work.Construction.mixed_angle_le hα hα1 hD.le hθ hcore
      calc (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          = ((Work.Spaces.Zop^[j] a) z * Work.Spaces.w z) ^ 2
              * (((Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
            ring
        _ ≤ (M / (1 + z)) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
            mul_le_mul hsq hang
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) (sq_nonneg _)
    rw [Work.Spaces.HkIntegrand]
    have hZsum : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (M / (1 + z)) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (k + 1),
              ((M / (1 + z)) ^ 2 * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
            Finset.sum_le_sum fun i hi =>
              hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = (M / (1 + z)) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hMsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (M / (1 + z)) ^ 2
            * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      set Y : ℝ := (M / (1 + z)) ^ 2
          * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
      have hYnn : 0 ≤ Y := by
        rw [hYdef]
        exact mul_nonneg (sq_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg D))
            (add_nonneg (Real.rpow_nonneg hs0 _)
              (mul_nonneg (sq_nonneg α) (Real.rpow_nonneg hs0 _))))
      calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1), Y :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
              · rw [if_neg hc]; exact hYnn
        _ = (M / (1 + z)) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul, hYdef]
            push_cast
            ring
    calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ((M / (1 + z)) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + ((M / (1 + z)) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))) :=
          add_le_add hZsum hMsum
      _ = (M / (1 + z)) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
          ring
  · -- angular boundary: `sin(2θ) = 0`, and every term of the integrand vanishes
    have hs : Real.sin (2 * θ) = 0 :=
      Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
    rw [Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
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

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6
