/-
# `Work.FTS.StrongPersist.AK6.HkMem_AK6` — the `ℋ⁶`-membership of the block `AK α`

The auxiliary block `AK α = (Γ(θ)/c α)·2z²/(1+z)³` of the modulation equation sits in `ℋ⁶`
as soon as the radial profile `ρ₀(z) = 2z²/(1+z)³` has bounded weighted `D_z`-jets up to order
`6` — which is exactly the hypothesis `hrad` of the statement:

`((D_z^j ρ₀)(z)·w z)² ≤ R/(1+z)²` for `j ≤ 6`, `z ∈ Iz`.

That hypothesis is *transparent* to the argument: `AK α` is the separable datum
`ρ(z)·Γ(θ)` with `ρ = ρ₀/c α` (so the radial input is `hrad` rescaled by `(1/c)² ≤ 100`,
using `1/10 ≤ c α`), and the generic separable majorant
`LocDataExt.HkIntegrand_sepGam_le` (at `k = 6`) turns it into

`HkIntegrand α 6 (AK α) z θ ≤ (7 + 49·10¹⁰)·(100 R)·angMaj α θ/(1+z)²`,

where the angular factor is priced by `Γ`'s `D_θ`-jets up to order `6`
(`LocData6.DthIter_Gam_abs_le6`, i.e. `(D_θ^iΓ)² ≤ 10¹⁰ Γ²`) and `angMaj α` is the
integrable angular majorant of `LocData.angMaj_mem`.  Since `z ↦ (1/(1+z))²` is integrable on
`Iz` (`H2.InvOneAddSq`), the domination criterion `LocData.HkMem_of_majorant` applies and
gives `HkMem α 6 (AK α)`; the interior regularity hypothesis of that criterion is the
`C⁶`-smoothness of `uncurry (AK α)` on the open quadrant (proved here from
`OpenPkg.contDiffOn_Gam_Q0`).

This is the order-`6` companion of `Work.FTS.NonlinRows.NAux3.HkMem_AK` (order `4`, with the
radial jets supplied by `AkRhoJetBasic.akRho_jet_bound` instead of being assumed).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.AK6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `AK α` in the *separable* shape `ρ(z)·Γ(θ)` consumed by
`LocDataExt.HkIntegrand_sepGam_le`. -/
theorem AK_eq_sep (α : ℝ) :
    Work.Construction.AK α = fun z θ =>
      (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
  funext z θ
  rw [Work.Construction.AK]
  ring

/-- **`AK α` is `C⁶` on the open quadrant.**  A product of `Γ(θ)/c α` and `2z²/(1+z)³`, both
smooth there (`OpenPkg.contDiffOn_Gam_Q0` and the rational factor). -/
theorem contDiffOn_six_AK (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.AK α)) Work.FTS.EllipticEst.Q0 := by
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0
    rw [h0] at h
    norm_num at h
  have hGam := (Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 6).div contDiffOn_const
    (fun _ _ => hcne)
  have hrad : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (contDiffOn_fst.pow 2)).div
      ((contDiffOn_const.add contDiffOn_fst).pow 3)
      (fun p hp => pow_ne_zero 3 (ne_of_gt
        (by linarith [Set.mem_Ioi.mp hp.1] : (0 : ℝ) < 1 + p.1)))
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)) = Function.uncurry (Work.Construction.AK α) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.AK]
  rw [← hfun]
  exact hGam.mul hrad

/-- **`HkMem α 6 (AK α)`** from the radial jet bound `hrad` for the profile `2z²/(1+z)³`. -/
theorem HkMem_AK6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {R : ℝ} (hR : 0 ≤ R) (hrad : ∀ (j : ℕ), j ≤ 6 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2) : Work.Spaces.HkMem α 6 (Work.Construction.AK α) := by
  obtain ⟨hc1, _hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : (0 : ℝ) < Work.Spaces.c α := by linarith
  have hR0 : (0 : ℝ) ≤ 100 * R := by linarith
  -- ## The radial jets of `ρ₀/c α`, from `hrad` rescaled by `(1/c)² ≤ 100`
  have hB : ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) z θ'
        * Work.Spaces.w z) ^ 2 ≤ 100 * R / (1 + z) ^ 2 := by
    intro j hj z hz θ'
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      rw [hw0, mul_zero, sq, zero_mul]
      exact div_nonneg hR0 (by norm_num)
    · have hfun : (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α)
          = fun z _ : ℝ => (1 / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := by
        funext z θ''
        ring
      have hmult := congrFun (congrFun (Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul j
        (1 / Work.Spaces.c α) (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3)) z) θ'
      rw [hfun, hmult]
      have hc10 : (1 / Work.Spaces.c α) ≤ 10 := by
        rw [div_le_iff₀ hc0]
        linarith
      have hsq : (1 / Work.Spaces.c α) ^ 2 ≤ 100 := by
        have h1 : (0 : ℝ) ≤ 1 / Work.Spaces.c α := by positivity
        nlinarith [hc10, h1]
      calc ((1 / Work.Spaces.c α)
              * Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
              * Work.Spaces.w z) ^ 2
          = (1 / Work.Spaces.c α) ^ 2
              * (Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
                * Work.Spaces.w z) ^ 2 := by ring
        _ ≤ 100 * (R / (1 + z) ^ 2) :=
            mul_le_mul hsq (hrad j hj z hz θ') (sq_nonneg _) (by norm_num)
        _ = 100 * R / (1 + z) ^ 2 := by ring
  -- ## The angular jets of `Γ`, up to order `6`
  have hΓ : ∀ i ≤ 6, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ') ^ 2 := by
    intro i hi θ' hθ'
    have h := Work.FTS.LocData6.DthIter_Gam_abs_le6 i hi α hα hα1 hθ'
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow] at h2
    have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
    calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (100000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ') ^ 2 := h2
      _ = (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ') ^ 2 := by rw [h10]
  -- ## The domination criterion, with the separable majorant
  refine Work.FTS.LocData.HkMem_of_majorant (f := Work.Construction.AK α)
    (M := fun z θ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R) / (1 + z) ^ 2)
      * Work.FTS.LocData.angMaj α θ) α 6 ?_ ?_ ?_ ?_
  · -- interior regularity of the integrand
    exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 6) (k := 6) le_rfl
      (contDiffOn_six_AK α hα hα1)
  · -- integrable `θ`-slices of the majorant
    intro z _hz
    exact ((Work.FTS.LocData.angMaj_mem α hα hα1).1).const_mul
      (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R) / (1 + z) ^ 2)
  · -- integrable `z`-integral of the majorant
    have hkey : IntegrableOn (fun z : ℝ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ioi 0) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul
        (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ))
    have hkeyIz : IntegrableOn (fun z : ℝ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ici 0) :=
      hkey.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have heqfun : (fun z : ℝ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            ((((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R) / (1 + z) ^ 2)
              * Work.FTS.LocData.angMaj α θ) := by
      funext z
      rw [MeasureTheory.integral_const_mul]
      rw [one_div, inv_pow, div_eq_mul_inv]
      ring
    rw [← heqfun]
    exact hkeyIz
  · -- pointwise domination by the separable majorant
    intro z hz θ hθ
    rw [AK_eq_sep]
    have h1 := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6 hR0 (by norm_num) hB hΓ hz hθ
    refine le_trans h1 (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ring

end Work.FTS.StrongPersist.AK6
