import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.Construction.H6N_GammaTerm_sep_le
import Submission.Work.Construction.H6N_GammaTerm_rho_bound
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.Spaces.bt_aux
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.zopIter_one_add_rhoR_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ⁶`-membership of the `(1+z)/(2α)`-scaled `close6` row

`close6 α (z,θ) = 8α² c2m(θ) z² Γ(θ)/(c(α)(1+z)⁴)` is the collapsed `I₁+I₂` combination of
`N₀` (the separable datum `Kfac α · ρ(z) · ψ(θ)` with `ρ = rhoR`, `ψ = psiA α`), and
`Work.FTS.StrongPersist.H6Rows.FstarI12H6` proves `close6 α ∈ ℋ⁶` with the pointwise majorant
`(Kfac α)²(M/(1+z)²)²·gammaAngMaj6 α D θ`.

Here we prove that the *scaled* row

`X α (z,θ) = (1+z)/(2α) · close6 α z θ = (Kfac α/(2α)) · ((1+z)ρ(z)) · ψ(θ)`

is still in `ℋ⁶`.  The factor `(1+z)/(2α)` is *not* a bounded radial multiplier
(`HkMem_radial_mul6` needs a uniform bound on the `Zop`-iterates, which `(1+z)/(2α)` does not
have), so the estimate is redone: the new radial factor `(1+z)·rhoR` satisfies only the weaker
bound
`|Zop^j ((1+z)ρ)(z)·w(z)| ≤ 64M/(1+z)`
(`zopIter_one_add_rhoR_bound`, from the Leibniz rule and the known `rhoR`-bound), and the
generalised separable majorant `HkN_sepF_le` turns such a bound into
`HkIntegrand α 6 X z θ ≤ (M'/(1+z))² · gammaAngMaj6 α D θ`.  Since `∫_0^∞ dz/(1+z)² < ∞`
(`Work.Elliptic.WtoH_IntZ`), the majorant is integrable and
`Work.FTS.LocData.HkMem_of_majorant` gives the membership.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

theorem HkMem_X_close6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 6 (fun z θ =>
      (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ) := by
  obtain ⟨M, hM, hMr⟩ := Work.Construction.H6N_GammaTerm_rho_bound
  obtain ⟨D, hD, hDl⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
  have hKfac_pos : 0 < Work.Construction.Kfac α := by
    rw [Work.Construction.Kfac]
    have hc : 0 < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    positivity
  -- the radial factor of the target, relative to the angular profile `psiA α`
  set a : ℝ → ℝ := fun z =>
    Work.Construction.Kfac α / (2 * α) * ((1 + z) * Work.Construction.rhoR z) with ha
  have hafn : a = fun z : ℝ =>
      Work.Construction.Kfac α / (2 * α) * ((1 + z) * Work.Construction.rhoR z) := by
    funext z; rw [ha]
  -- the target function, named
  let F0 : ℝ → ℝ → ℝ := fun z θ =>
    (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ
  change Work.Spaces.HkMem α 6 F0
  -- the pointwise identification of the target with the separable shape `a(z)·psiA α θ`
  have hpc : ∀ z θ : ℝ, F0 z θ = a z * Work.Construction.psiA α θ := by
    intro z θ
    show (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ
      = a z * Work.Construction.psiA α θ
    rw [show a z = Work.Construction.Kfac α / (2 * α)
        * ((1 + z) * Work.Construction.rhoR z) from congrFun hafn z]
    simp only [Work.FTS.StrongPersist.H6Rows.close6, Work.Construction.Kfac,
      Work.Construction.rhoR, Work.Construction.psiA]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hfun : F0 = Work.Construction.sepF a (Work.Construction.psiA α) := by
    funext z θ; exact hpc z θ
  rw [hfun]
  -- the price of the radial factor: `M' = (Kfac α/(2α))·64M`
  set M' : ℝ := Work.Construction.Kfac α / (2 * α) * (64 * M) with hM'def
  have hM'pos : 0 < M' := by rw [hM'def]; positivity
  have hKr : 0 ≤ Work.Construction.Kfac α / (2 * α) := le_of_lt (by positivity)
  have hMr' : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] a) z * Work.Spaces.w z| ≤ M' / (1 + z) := by
    intro j hj z hz
    have hb : |(Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
        * Work.Spaces.w z| ≤ (64 * M) / (1 + z) :=
      zopIter_one_add_rhoR_bound hM hMr j hj z hz
    rw [hafn, Work.Construction.Zop_iter_const_mul]
    simp only []
    calc |(Work.Construction.Kfac α / (2 * α)
            * (Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z)
            * Work.Spaces.w z|
        = (Work.Construction.Kfac α / (2 * α))
            * |(Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
                * Work.Spaces.w z| := by
          rw [show (Work.Construction.Kfac α / (2 * α)
                  * (Work.Spaces.Zop^[j]
                      (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z)
                  * Work.Spaces.w z
                = (Work.Construction.Kfac α / (2 * α))
                  * ((Work.Spaces.Zop^[j]
                      (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
                    * Work.Spaces.w z) from by ring,
            abs_mul, abs_of_nonneg hKr]
      _ ≤ (Work.Construction.Kfac α / (2 * α)) * ((64 * M) / (1 + z)) :=
          mul_le_mul_of_nonneg_left hb hKr
      _ = M' / (1 + z) := by rw [hM'def]; ring
  -- the majorant
  set Mmaj : ℝ → ℝ → ℝ := fun z θ =>
    (M' / (1 + z)) ^ 2 * Work.FTS.StrongPersist.H6Rows.gammaAngMaj6 α D θ with hMmaj
  -- continuity of the integrand on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6
      (Work.Construction.sepF a (Work.Construction.psiA α)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 6) (k := 6) le_rfl ?_
    have h1 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => (1 + p.1) / (2 * α))
        Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div (contDiffOn_const.add contDiffOn_fst)
        (contDiffOn_const : ContDiffOn ℝ (6 : ℕ) (fun _ : ℝ × ℝ => 2 * α)
          Work.FTS.EllipticEst.Q0) ?_
      intro p hp
      exact ne_of_gt (by linarith : (0 : ℝ) < 2 * α)
    have h2 : ContDiffOn ℝ (6 : ℕ) (Function.uncurry (Work.FTS.StrongPersist.H6Rows.close6 α))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongPersist.H6Rows.contDiffOn_uncurry_sep6 α).congr
        (fun p _ => (Work.FTS.StrongPersist.H6Rows.sep6_eq_close6 α p.1 p.2).symm)
    have h3 : ContDiffOn ℝ (6 : ℕ) (Function.uncurry F0) Work.FTS.EllipticEst.Q0 :=
      (h1.mul h2).congr (fun p _ => rfl)
    rw [← hfun]
    exact h3
  refine Work.FTS.LocData.HkMem_of_majorant
    (f := Work.Construction.sepF a (Work.Construction.psiA α)) (M := Mmaj) α 6 hcont ?_ ?_ ?_
  · -- the angular slices of the majorant are integrable
    intro z hz
    rw [hMmaj]
    have hbase := Work.FTS.StrongPersist.H6Rows.integrableOn_gammaAngMaj6 (α := α) (D := D) hα hα1
    exact hbase.const_mul ((M' / (1 + z)) ^ 2)
  · -- the `z`-integral of the majorant is integrable
    rw [hMmaj]
    have hbase : IntegrableOn (fun z : ℝ =>
        ((M' ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.gammaAngMaj6 α D θ))
          * (1 / (1 + z) ^ 2)) Work.Spaces.Iz := Work.Elliptic.WtoH_IntZ.1.const_mul _
    refine hbase.congr_fun (fun z hz => ?_) measurableSet_Ici
    dsimp only
    have hkey : (1 : ℝ) / (1 + z) ^ 2 = (1 / (1 + z)) ^ 2 := by
      rw [div_pow, one_pow]
    rw [MeasureTheory.integral_const_mul, hkey]
    ring
  · -- the pointwise domination by the separable majorant
    intro z hz θ hθ
    rw [hMmaj]
    have hle := HkN_sepF_le (a := a) (M := M') (D := D) hα hα1 hM'pos hD 6 hMr'
      (fun i hi1 hi6 θ' hθ' => hDl α hα hα1 i hi1 hi6 θ' hθ') z hz θ hθ
    refine hle.trans (le_of_eq ?_)
    simp only [Work.FTS.StrongPersist.H6Rows.gammaAngMaj6]
    ring

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6
