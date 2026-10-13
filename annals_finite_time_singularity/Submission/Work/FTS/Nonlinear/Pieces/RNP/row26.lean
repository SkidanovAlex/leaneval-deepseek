import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Elliptic.WtoH_IntZ
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# Row 26 of the per-piece table of `Work/FTS/Nonlinear`: `|N₅^{ss}|_{ℋ⁴} ≤ Kα²`

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals 194 (3) 2021, §8: the `ss`-piece of the quadratic term `N₅`
of the modulated self-similar equation, `N₅^{ss} = -sin²θ·(F_*,K)_{L²_θ}·F_*` (the design's
`Work.FTS.Nonlin.N5ss`), has `ℋ⁴`-norm at most `Kα²`, uniformly for `0 < α ≤ min(α₂,1)`.

The estimate is *unconditional* (it involves only the fundamental model `F_*`, not the
perturbation `g` or the stream functions `Φs`, `Φg`; `N4Norm` is carried only to fix the
context of the design table).  The proof is a direct computation in the weighted `ℋ⁴`-norm,
reducing everything to `HkSq_sep_le` and to the angular core
`Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound`; see the docstrings below.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The angular profile `θ ↦ sin²θ·Γ(θ)` of `N₅^{ss} = -sin²θ·FK(F_*)·F_*`. -/
def psiB (α : ℝ) (θ : ℝ) : ℝ := Real.sin θ ^ 2 * Work.Spaces.Gam α θ

theorem psiB_abs_le_one {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |psiB α θ| ≤ 1 := by
  have hΓ : |Work.Spaces.Gam α θ| ≤ 1 := by
    rw [abs_of_nonneg (Work.Construction.Gam_nonneg_of_Iθ hα hθ)]
    exact Work.Construction.Gam_le_one_of_Iθ hα hθ
  have hs : Real.sin θ ^ 2 ≤ 1 := by
    rw [← sq_abs (Real.sin θ)]
    nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
  have hsabs : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]; exact hs
  rw [psiB, abs_mul]
  calc |Real.sin θ ^ 2| * |Work.Spaces.Gam α θ| ≤ 1 * 1 :=
        mul_le_mul hsabs hΓ (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem HkSq_sep_le (D : ℝ) (hD : 0 < D)
    (hcore : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.HkSq α 4 (fun z θ => 4 * Work.Construction.rhoR z * psiB α θ) ≤ K := by
  obtain ⟨M, hM, hMr⟩ := Work.Construction.H4N_GammaTerm_rho_bound
  set Cθ : ℝ := (5 + 50 * D ^ 2) * 10000 + 50 * D ^ 2 * (3000 / 17) with hCθdef
  have hCθ : 0 < Cθ := by rw [hCθdef]; positivity
  refine ⟨(4 * M) ^ 2 * (2 * Cθ) + 1, by positivity, ?_⟩
  intro α hα hα1
  have hDnn : 0 ≤ D := hD.le
  set F : ℝ → ℝ → ℝ := fun z θ => 4 * Work.Construction.rhoR z * psiB α θ with hFdef
  have hFsep : F = Work.Construction.sepF (fun z => 4 * Work.Construction.rhoR z)
      (psiB α) := rfl
  set Big : ℝ → ℝ := fun θ => (5 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)
    with hBigdef
  -- pointwise bound on the integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 F z θ
        ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ := by
    intro z hz θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Construction.sin_two_nonneg_of_mem_Iθ hθ
    have h1z : 0 < 1 + z := by have hz0 : (0 : ℝ) ≤ z := hz; linarith
    rcases em (θ ∈ Set.Ioo 0 (π / 2)) with hθi | hθi
    · -- interior
      have hψ2 : (psiB α θ) ^ 2 ≤ 1 := by
        have h := mul_self_le_mul_self (abs_nonneg (psiB α θ)) (psiB_abs_le_one hα hθ)
        have h2 := sq_abs (psiB α θ)
        nlinarith [h, h2]
      have hbnd : ∀ j : ℕ, j ≤ 4 →
          (4 * (Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
            ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 := by
        intro j hj
        have hb := hMr j hj z hz
        have habs : |4 * ((Work.Spaces.Zop^[j] Work.Construction.rhoR) z
              * Work.Spaces.w z)| ≤ 4 * M * (1 / (1 + z) ^ 2) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          calc 4 * |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z|
              ≤ 4 * (M / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hb (by norm_num)
            _ = 4 * M * (1 / (1 + z) ^ 2) := by ring
        have h1 : (4 * (Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
            = |4 * ((Work.Spaces.Zop^[j] Work.Construction.rhoR) z
                * Work.Spaces.w z)| ^ 2 := by
          rw [sq_abs]; ring
        rw [h1]
        calc |4 * ((Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z)| ^ 2
            ≤ (4 * M * (1 / (1 + z) ^ 2)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) habs 2
          _ = (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 := by ring
      have hpure : ∀ i : ℕ, i ≤ 4 →
          (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        intro i hi
        have hsep : Work.Spaces.DzIter i F z θ
            = (4 * (Work.Spaces.Zop^[i] Work.Construction.rhoR) z) * psiB α θ := by
          rw [hFsep, Work.Construction.sepF_DzIter, Work.Construction.Zop_iter_const_mul,
            Work.Construction.sepF]
        have hsq := hbnd i hi
        have hSnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
        calc (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = (4 * (Work.Spaces.Zop^[i] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
                * (psiB α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
              rw [hsep, Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
                (a := (4 * (Work.Spaces.Zop^[i] Work.Construction.rhoR) z) * psiB α θ) hθ]
              ring
          _ ≤ ((4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * 1)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul (mul_le_mul hsq hψ2 (sq_nonneg _) (by positivity)) le_rfl hSnn
                (by positivity)
          _ = (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
      have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
          (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
        intro i j hi hij
        have hsep : Work.Spaces.mixed j i F z θ
            = (4 * (Work.Spaces.Zop^[j] Work.Construction.rhoR) z)
              * (Work.Spaces.Lop^[i] (psiB α)) θ := by
          rw [hFsep, Work.Construction.sepF_mixed, Work.Construction.Zop_iter_const_mul,
            Work.Construction.sepF]
        have hsq := hbnd j (by omega)
        have hcore' := hcore α hα hα1 i hi (by omega) θ hθi
        have hang := Work.Construction.mixed_angle_le hα hα1 hDnn hθ hcore'
        calc (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            = (4 * (Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
                * (((Work.Spaces.Lop^[i] (psiB α)) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
              ring
          _ ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
                * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
              mul_le_mul hsq hang (by positivity) (by positivity)
      rw [Work.Spaces.HkIntegrand]
      have hZsum : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
              * (5 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ ∑ _i ∈ Finset.range (4 + 1),
                ((4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
              Finset.sum_le_sum fun i hi =>
                hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          _ = 5 * ((4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
          _ = (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
                  * (5 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hMsum : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + 50 * D ^ 2 * α ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
        set Y : ℝ := (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
        have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
        calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Y :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
                by_cases hc : 1 ≤ i ∧ i + j ≤ 4
                · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
                · rw [if_neg hc]; exact hYnn
          _ = 25 * Y := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
          _ = (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + 50 * D ^ 2 * α ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
              rw [hYdef]; ring
      calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
              * (5 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + 50 * D ^ 2 * α ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) :=
            add_le_add hZsum hMsum
        _ = (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ := by simp only [hBigdef]; ring
    · -- boundary: every term vanishes
      have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
      have h0 : Big θ = 0 := by
        simp only [hBigdef, hs,
          Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : (-(Work.Spaces.eta)) ≠ 0),
          Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith :
            (2 * α / 3 - Work.Spaces.gam α) ≠ 0)]
        ring
      rw [h0]; norm_num
  -- integrability and value of the angular majorant
  have hint1 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
      (by linarith [Work.Spaces.eta_nonneg])).1
  have hval1 : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_nonneg])).2
    have hden : (-(Work.Spaces.eta)) + 1 = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hden] at h
    norm_num at h
    linarith
  have hp : 2 * α / 3 - Work.Spaces.gam α = -1 + 17 * α / 30 := by
    rw [Work.Spaces.gam]; ring
  have hpe1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [hp]; linarith
  have hpe2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [hp]; linarith
  have hint2 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hpe1 hpe2).1
  have hnn2 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      Real.rpow_nonneg (Work.Construction.sin_two_nonneg_of_mem_Iθ hθ) _
  have hval2 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 3000 / 17 := by
    have h := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hpe1 hpe2).2
    have hden : (2 * α / 3 - Work.Spaces.gam α) + 1 = 17 * α / 30 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at h
    calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        ≤ α ^ 2 * (100 / (17 * α / 30)) := mul_le_mul_of_nonneg_left h (sq_nonneg α)
      _ = 3000 * α / 17 := by field_simp; ring
      _ ≤ 3000 / 17 := by nlinarith [hα1]
  have hBignnI : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Big θ := by
    intro θ hθ
    simp only [hBigdef]
    exact add_nonneg
      (mul_nonneg (by positivity)
        (Real.rpow_nonneg (Work.Construction.sin_two_nonneg_of_mem_Iθ hθ) _))
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg α))
        (Real.rpow_nonneg (Work.Construction.sin_two_nonneg_of_mem_Iθ hθ) _))
  have hBignn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Big θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc hBignnI
  have hBigint : Integrable (fun θ : ℝ => Big θ) (volume.restrict Work.Spaces.Iθ) := by
    simp only [hBigdef]
    exact (hint1.const_mul (5 + 50 * D ^ 2)).add (hint2.const_mul (50 * D ^ 2 * α ^ 2))
  have hBigval : ∫ θ in Work.Spaces.Iθ, Big θ ≤ Cθ := by
    have htot : ∫ θ in Work.Spaces.Iθ, Big θ
        = (5 + 50 * D ^ 2) * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 50 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
      simp only [hBigdef]
      rw [MeasureTheory.integral_add (hint1.const_mul (5 + 50 * D ^ 2))
          (hint2.const_mul (50 * D ^ 2 * α ^ 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [htot, hCθdef]
    have h1 : (5 + 50 * D ^ 2) * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (5 + 50 * D ^ 2) * 10000 :=
      mul_le_mul_of_nonneg_left hval1 (by positivity)
    have h2 : 50 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        = 50 * D ^ 2 * (α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by ring
    have h3 : 50 * D ^ 2 * (α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))
        ≤ 50 * D ^ 2 * (3000 / 17) := mul_le_mul_of_nonneg_left hval2 (by positivity)
    rw [h2]
    linarith
  -- the `z`-integral of the weight
  have hzmeas : AEStronglyMeasurable (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    measurability
  have hzint : Integrable (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' Work.Elliptic.WtoH_IntZ.1 hzmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h3 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h2, h3]
  have hWint : 0 ≤ ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz => by positivity
  have hzval : ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 ≤ 2 := by
    have hle : (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z : ℝ => 1 / (1 + z) ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      have hz0 : (0 : ℝ) ≤ z := hz
      have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have h3 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
      nlinarith [h2, h3]
    exact le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun z => by positivity) Work.Elliptic.WtoH_IntZ.1 hle)
      Work.Elliptic.WtoH_IntZ.2
  -- the inner integral identity
  have hinner_eq : ∀ z : ℝ, ∫ θ in Work.Spaces.Iθ,
        (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ
      = (4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ) * (1 / (1 + z) ^ 2) ^ 2 := by
    intro z
    rw [MeasureTheory.integral_const_mul]
    ring
  have houter_eq : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ
      = (4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * ((4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)) from by
      funext z; rw [hinner_eq z]; ring]
    rw [MeasureTheory.integral_mul_const]
    ring
  have hMajint : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ) (volume.restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * ((4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)) from by
      funext z; rw [hinner_eq z]; ring]
    exact hzint.mul_const _
  -- the `ℋ⁴`-square bound
  have hHkSq : Work.Spaces.HkSq α 4 F ≤ (4 * M) ^ 2 * (2 * Cθ) := by
    rw [Work.Spaces.HkSq]
    have hstep : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 F z θ
        ≤ (4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
            * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := by
      calc ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F z θ
          ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (4 * M) ^ 2 * (1 / (1 + z) ^ 2) ^ 2 * Big θ :=
            MeasureTheory.integral_mono_of_nonneg
              (Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
                (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 F z θ))
              hMajint
              (ae_restrict_of_forall_mem measurableSet_Ici
                (fun z hz => MeasureTheory.integral_mono_of_nonneg
                  (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ =>
                    Work.Spaces.HkIntegrand_nonneg α 4 F z θ))
                  (hBigint.const_mul _)
                  (ae_restrict_of_forall_mem measurableSet_Icc (hpt z hz))))
        _ = (4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
            * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := houter_eq
    have hA : (4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ) ≤ (4 * M) ^ 2 * Cθ :=
      mul_le_mul_of_nonneg_left hBigval (by positivity)
    have h1 : (4 * M) ^ 2 * (∫ θ in Work.Spaces.Iθ, Big θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) ≤ (4 * M) ^ 2 * Cθ * 2 :=
      mul_le_mul hA hzval hWint (by positivity)
    linarith
  exact le_trans hHkSq (by linarith)

/-- **Row 26 of the design table** (Elgindi §8): `|N₅^{ss}|_{ℋ⁴} ≤ Kα²`, where
`N₅^{ss} = -sin²θ·FK(F_*)·F_*` is the `ss`-slot of the `N₅` block.

The claim does not involve the perturbation `g` at all: `FK(F_*) = α·2z/(1+z)²`
(`Work.FTS.Nonlin.FK_Fstar`) and `F_* = α(Γ/c)·2z/(1+z)²` are both explicit, so on the open
quadrant

  `N₅^{ss}(z,θ) = -α²·(Γ(θ)/c(α))·sin²θ·(2z/(1+z)²)² = -(α²/c(α))·(4·ρ(z))·ψ(θ)`

with `ρ(z) = z²/(1+z)⁴` (`Work.Construction.rhoR`) and `ψ(θ) = sin²θ·Γ(θ)`.  Hence
`Xₙ α (N₅^{ss}) = (α²/c(α))·|4ρψ|_{ℋ⁴}` (`HkSq_const_mul`, `Xn_const_mul`) and it suffices to
bound `HkSq α 4 (4ρψ) ≤ K'` uniformly in `α ∈ (0,1]`, which is `HkSq_sep_le`: the radial
factor is controlled by `H4N_GammaTerm_rho_bound` (`|D_z^jρ·w| ≤ 840/(1+z)²`, `j ≤ 4`), the
angular one pointwise by `|ψ| ≤ 1` and by the angular core `psiB_Lop_bound` together with
`mixed_angle_le` (`|D_θ^iψ| ≤ 10⁶Γ(θ)(sin²(2θ)+α)` gives
`(D_θ^iψ)²sin(2θ)^{-γ} ≤ 2·10¹²(sin(2θ)^{-η} + α²sin(2θ)^{2α/3-γ})`), and the two angular
majorants integrate to `10⁴` resp. `α^{-1}·3000/17` (`Work.Spaces.sin_two_rpow`).  Finally
`c(α) ≥ 1/10` (`Work.Spaces.c_bounds`). -/
theorem row26 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α)
        ≤ K * α ^ 2 := by
  obtain ⟨D, hD, hcore⟩ := Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound
  obtain ⟨K', hK'pos, hK'⟩ := HkSq_sep_le D hD hcore
  refine ⟨10 * Real.sqrt K', by have := Real.sqrt_pos.mpr hK'pos; linarith, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hsq : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N5ss α)
      = (α ^ 2 / Work.Spaces.c α) ^ 2
        * Work.Spaces.HkSq α 4 (fun z θ => 4 * Work.Construction.rhoR z * psiB α θ) := by
    have h1 : Work.Spaces.HkSq α 4 (fun z θ =>
          -(α ^ 2 / Work.Spaces.c α) * (4 * Work.Construction.rhoR z * psiB α θ))
        = (α ^ 2 / Work.Spaces.c α) ^ 2
          * Work.Spaces.HkSq α 4 (fun z θ => 4 * Work.Construction.rhoR z * psiB α θ) := by
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.HkSq_const_mul]
      ring
    have h2 : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N5ss α)
        = Work.Spaces.HkSq α 4 (fun z θ =>
            -(α ^ 2 / Work.Spaces.c α) * (4 * Work.Construction.rhoR z * psiB α θ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ hθ2 => by
        show Work.FTS.Nonlin.N5ss α z θ
            = -(α ^ 2 / Work.Spaces.c α) * (4 * Work.Construction.rhoR z * psiB α θ)
        rw [Work.FTS.Nonlin.N5ss, Work.FTS.Nonlin.FK_Fstar hα hα1]
        simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Construction.rhoR, psiB]
        have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
        have hc : Work.Spaces.c α ≠ 0 := ne_of_gt hcpos
        field_simp
        ring)
    exact h2.trans h1
  have hHK : Work.Spaces.HkSq α 4 (fun z θ => 4 * Work.Construction.rhoR z * psiB α θ) ≤ K' :=
    hK' α hα hα1
  have hXnb : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α)
      ≤ (α ^ 2 / Work.Spaces.c α) * Real.sqrt K' := by
    simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    rw [hsq]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (α ^ 2 / Work.Spaces.c α) ^ 2),
      Real.sqrt_sq (div_nonneg (sq_nonneg α) hcpos.le)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHK)
      (div_nonneg (sq_nonneg α) hcpos.le)
  refine hXnb.trans ?_
  have h2 : α ^ 2 / Work.Spaces.c α ≤ 10 * α ^ 2 := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc1, sq_nonneg α]
  have h3 : 0 ≤ Real.sqrt K' := Real.sqrt_nonneg K'
  calc (α ^ 2 / Work.Spaces.c α) * Real.sqrt K'
      ≤ (10 * α ^ 2) * Real.sqrt K' := mul_le_mul_of_nonneg_right h2 h3
    _ = 10 * Real.sqrt K' * α ^ 2 := by ring

end Work.FTS.Nonlinear.Pieces.RNP
