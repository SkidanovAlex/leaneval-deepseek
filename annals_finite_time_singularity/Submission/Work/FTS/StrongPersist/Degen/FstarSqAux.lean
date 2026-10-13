import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.Construction.Defs
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.Fstar_factor
import Submission.Work.FTS.LocData.PhiZ_eq
import Submission.Work.FTS.CoercivityFix.Assembly.exists_coerAdm_pos
import Submission.Work.FTS.StrongPersist.Degen.DthIterGamGen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.Degen

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# Auxiliary estimates for `FstarHkSqZeroSmooth`

The pointwise and slicewise estimates of the `ℋ⁴`-integrand of the self-similar profile
`F_* = α(Γ/c)·2z/(1+z)²`, with the general-`α` angular jet bound
`Work.FTS.StrongPersist.Degen.DthIterGamGen` as the only analytic input.  Split off from
`FstarHkSqZeroSmooth` for file-size reasons.
-/

/-! ## Elementary angular and `rpow` facts -/

lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma div_rpow_sq (A w s e : ℝ) :
    (A * (w / s ^ e)) ^ 2 = (A * w) ^ 2 * ((s ^ e) ^ 2)⁻¹ := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
  ring

lemma rpow_half_sq_inv (s e : ℝ) (hs : 0 ≤ s) : ((s ^ (e / 2)) ^ 2)⁻¹ = s ^ (-e) := by
  rw [show (s ^ (e / 2)) ^ 2 = s ^ e from by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; congr 1; ring]
  rw [← Real.rpow_neg hs]

lemma w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (by positivity) (by positivity)

/-! ## The smoothness of the self-similar profile -/

theorem smoothOpen_Fstar (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
  (Work.FTS.LocData.SmoothQuad_Fstar α).mono
    (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl)

/-! ## The radial factor of `F_*`: `D_z^i F_* = (α/c)·Γ·Φ_i` with `Φ_i` free of `θ` -/

/-- The sum of the squares of the five radial `D_z`-iterates of the profile `2z/(1+z)²`,
normalised: `Srad z = ∑_{i<5} Φ_i(z)²`.  It is a genuine real number for every `z`. -/
noncomputable def Srad (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, (Work.FTS.LocData.Phi i z 0) ^ 2

lemma Srad_nonneg (z : ℝ) : 0 ≤ Srad z :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The iterated `D_z`-derivative of the profile is `Φ_i(z)`, which does not depend on `θ`. -/
lemma profileIter_eq (i : ℕ) (hi : i ≤ 4) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ = Work.FTS.LocData.Phi i z θ :=
  Work.FTS.LocData.PhiZ_eq i hi z θ

lemma Phi_theta_indep (i : ℕ) (z θ : ℝ) :
    Work.FTS.LocData.Phi i z θ = Work.FTS.LocData.Phi i z 0 := rfl

lemma profileIter_sq_le_Srad (i : ℕ) (hi : i ≤ 4) (z θ : ℝ) :
    (Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ) ^ 2 ≤ Srad z := by
  rw [profileIter_eq i hi z θ, Phi_theta_indep i z θ, Srad]
  exact Finset.single_le_sum (f := fun i => (Work.FTS.LocData.Phi i z 0) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-! ## The `ℋ⁴`-integrand of `F_*` bounded by the angular majorant `angMaj` -/

/-- **The slot decomposition of `HkIntegrand · 4 (F_*)`.**  If every one of the five `D_z`-slots
is bounded by `K1` and every one of the (at most twenty-five) mixed slots by `K2 ≥ 0`, then the
integrand itself is bounded by `5·K1 + 25·K2`. -/
theorem HkIntegrand_Fstar_le_of_slots (α : ℝ) (z θ K1 K2 : ℝ) (hK2 : 0 ≤ K2)
    (hT1 : ∀ i : ℕ, i ≤ 4 → (Work.Spaces.DzIter i (Work.Construction.Fstar α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ K1)
    (hT2 : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
        (Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ K2) :
    Work.Spaces.HkIntegrand α 4 (Work.Construction.Fstar α) z θ ≤ 5 * K1 + 25 * K2 := by
  have hHk : Work.Spaces.HkIntegrand α 4 (Work.Construction.Fstar α) z θ
      = (∑ i ∈ Finset.range (4 + 1), (Work.Spaces.DzIter i (Work.Construction.Fstar α) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  rw [hHk]
  refine add_le_add ?_ ?_
  · calc (∑ i ∈ Finset.range (4 + 1), (Work.Spaces.DzIter i (Work.Construction.Fstar α) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (4 + 1), K1 := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [Finset.mem_range] at hi
          exact hT1 i (by omega)
      _ = 5 * K1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  · calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), K2 := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro j _
          by_cases hc : 1 ≤ i ∧ i + j ≤ 4
          · rw [if_pos hc]
            exact hT2 i j hc.1 hc.2
          · rw [if_neg hc]
            exact hK2
      _ = 25 * K2 := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring

/-- **The pointwise bound of the `F_*`-integrand by `angMaj`.**  For every `z`,
`HkIntegrand α 4 (F_*) z θ ≤ A(z)·angMaj α θ` with the `θ`-free constant
`A(z) = (α/c)² w(z)² (5 + 25K²) (1 + Srad z)`, `K = 1000(1+α²)²`.

The only analytic input is the general-`α` angular jet bound `DthIterGamGen`; everything else
is the factorisation `D_z^i F_* = (α/c)ΓΦ_i`, `D_z^jD_θ^i F_* = (α/c)·D_θ^iΓ·Φ_j` together
with `Γ²sin(2θ)^{-η} ≤ angMaj` and `Γ²sin(2θ)^{-γ} ≤ angMaj`. -/
theorem fstar_integrand_le_angMaj {α : ℝ} (hα : 0 < α) (z : ℝ)
    (hjet : ∀ i ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ 1000 * (1 + α ^ 2) ^ 2 * Work.Spaces.Gam α θ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Construction.Fstar α) z θ
        ≤ ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2
            * (5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2) * (1 + Srad z))
          * Work.FTS.LocData.angMaj α θ := by
  intro θ hθ
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hw0 : 0 ≤ Work.Spaces.w z := w_nonneg z
  have hS0 : 0 ≤ Srad z := Srad_nonneg z
  have hang0 : 0 ≤ Work.FTS.LocData.angMaj α θ := Work.FTS.LocData.angMaj_nonneg hθ
  have hG2 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ 1000 * (1 + α ^ 2) ^ 2 := by positivity
  have hang_eta : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.FTS.LocData.angMaj α θ := by
    rw [Work.FTS.LocData.angMaj_apply]
    have h := mul_nonneg hG2 (Real.rpow_nonneg hs0 (-(Work.Spaces.gam α)))
    linarith
  have hang_gam : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.FTS.LocData.angMaj α θ := by
    rw [Work.FTS.LocData.angMaj_apply]
    have h := mul_nonneg hG2 (Real.rpow_nonneg hs0 (-(Work.Spaces.eta)))
    linarith
  have hcoef0 : 0 ≤ (α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- the `D_z`-slots
  have hT1 : ∀ i : ℕ, i ≤ 4 → (Work.Spaces.DzIter i (Work.Construction.Fstar α) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2 * Srad z
          * Work.FTS.LocData.angMaj α θ := by
    intro i hi
    have hfac : Work.Spaces.DzIter i (Work.Construction.Fstar α) z θ
        = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
            * Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ :=
      congrFun (congrFun (Work.FTS.LocData.DzIter_Fstar_eq α i) z) θ
    rw [hfac]
    have hkey : (((α / Work.Spaces.c α) * Work.Spaces.Gam α θ
          * Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2)
            * ((Work.Spaces.Gam α θ) ^ 2
              * (Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      rw [div_rpow_sq, rpow_half_sq_inv _ _ hs0]
      ring
    rw [hkey]
    have hmain : (Work.Spaces.Gam α θ) ^ 2
          * (Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ Srad z * Work.FTS.LocData.angMaj α θ := by
      have h1 : (Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ) ^ 2
            * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ Srad z * Work.FTS.LocData.angMaj α θ :=
        mul_le_mul (profileIter_sq_le_Srad i hi z θ) hang_eta (by positivity) hS0
      calc (Work.Spaces.Gam α θ) ^ 2
            * (Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          = (Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ) ^ 2
            * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            ring
        _ ≤ Srad z * Work.FTS.LocData.angMaj α θ := h1
    calc ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2)
          * ((Work.Spaces.Gam α θ) ^ 2
              * (Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (Srad z * Work.FTS.LocData.angMaj α θ) :=
          mul_le_mul_of_nonneg_left hmain hcoef0
      _ = (α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2 * Srad z
            * Work.FTS.LocData.angMaj α θ := by ring
  -- the mixed slots
  have hT2 : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
      (Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (1000 * (1 + α ^ 2) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2
          * Srad z * Work.FTS.LocData.angMaj α θ := by
    intro i j hi hij
    have hi4 : i ≤ 4 := by omega
    have hj4 : j ≤ 4 := by omega
    have hfac : Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
        = (α / Work.Spaces.c α)
            * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
            * Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ :=
      congrFun (congrFun (Work.FTS.LocData.mixed_Fstar_eq α i j) z) θ
    have hWt : Work.Spaces.Wt α z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
    have hkey : ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
          * Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        = ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2)
            * ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
              * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
      have hSg : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
        congr 1
        ring
      simp only [mul_pow]
      rw [hSg]
      ring
    rw [hfac, hWt, hkey]
    have hD : (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ ((1000 * (1 + α ^ 2) ^ 2) * Work.Spaces.Gam α θ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (hjet i hi4 θ hθ) 2
      simpa only [sq_abs] using h
    have hmain : ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
          * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ((1000 * (1 + α ^ 2) ^ 2) ^ 2 * Srad z) * Work.FTS.LocData.angMaj α θ := by
      have hstep1 : ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
            * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ (((1000 * (1 + α ^ 2) ^ 2) * Work.Spaces.Gam α θ) ^ 2)
            * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      have hstep2 : (Work.Spaces.Gam α θ) ^ 2
            * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ Srad z * Work.FTS.LocData.angMaj α θ := by
        have h1 : (Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
              * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            ≤ Srad z * Work.FTS.LocData.angMaj α θ :=
          mul_le_mul (profileIter_sq_le_Srad j hj4 z θ) hang_gam (by positivity) hS0
        calc (Work.Spaces.Gam α θ) ^ 2
              * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            = (Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
              * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              ring
          _ ≤ Srad z * Work.FTS.LocData.angMaj α θ := h1
      calc ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
            * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ (((1000 * (1 + α ^ 2) ^ 2) * Work.Spaces.Gam α θ) ^ 2)
            * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := hstep1
        _ = (1000 * (1 + α ^ 2) ^ 2) ^ 2
            * ((Work.Spaces.Gam α θ) ^ 2
                * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
            ring
        _ ≤ (1000 * (1 + α ^ 2) ^ 2) ^ 2 * (Srad z * Work.FTS.LocData.angMaj α θ) :=
            mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ = ((1000 * (1 + α ^ 2) ^ 2) ^ 2 * Srad z) * Work.FTS.LocData.angMaj α θ := by
            ring
    calc ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2)
          * ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
              * ((Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        ≤ ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (((1000 * (1 + α ^ 2) ^ 2) ^ 2 * Srad z) * Work.FTS.LocData.angMaj α θ) :=
          mul_le_mul_of_nonneg_left hmain hcoef0
      _ = (α / Work.Spaces.c α) ^ 2 * (1000 * (1 + α ^ 2) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2
            * Srad z * Work.FTS.LocData.angMaj α θ := by ring
  have hK2nn : 0 ≤ (α / Work.Spaces.c α) ^ 2 * (1000 * (1 + α ^ 2) ^ 2) ^ 2
      * (Work.Spaces.w z) ^ 2 * Srad z * Work.FTS.LocData.angMaj α θ := by positivity
  have hmain := HkIntegrand_Fstar_le_of_slots α z θ
    ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2 * Srad z
      * Work.FTS.LocData.angMaj α θ)
    ((α / Work.Spaces.c α) ^ 2 * (1000 * (1 + α ^ 2) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2
      * Srad z * Work.FTS.LocData.angMaj α θ) hK2nn hT1 hT2
  have harith : 5 * ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2 * Srad z
        * Work.FTS.LocData.angMaj α θ)
      + 25 * ((α / Work.Spaces.c α) ^ 2 * (1000 * (1 + α ^ 2) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2
        * Srad z * Work.FTS.LocData.angMaj α θ)
      ≤ ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2
          * (5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2) * (1 + Srad z))
        * Work.FTS.LocData.angMaj α θ := by
    have hP0 : 0 ≤ (α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.LocData.angMaj α θ * (5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2) := by
      have h1 : 0 ≤ 5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hang0) h1
    have hSle : Srad z ≤ 1 + Srad z := by linarith [Srad_nonneg z]
    have e1 : 5 * ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2 * Srad z
          * Work.FTS.LocData.angMaj α θ)
        + 25 * ((α / Work.Spaces.c α) ^ 2 * (1000 * (1 + α ^ 2) ^ 2) ^ 2
          * (Work.Spaces.w z) ^ 2 * Srad z * Work.FTS.LocData.angMaj α θ)
        = ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.LocData.angMaj α θ * (5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2))
          * Srad z := by ring
    have e2 : ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2
          * (5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2) * (1 + Srad z))
        * Work.FTS.LocData.angMaj α θ
        = ((α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.LocData.angMaj α θ * (5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2))
          * (1 + Srad z) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hSle hP0
  exact hmain.trans harith

/-- **The `F_*`-slice of the `ℋ⁴`-integrand has finite upper integral.**  This is the input
that makes the slices of the *total* profile `F_* + f` honest in the `θ`-variable, uniformly in
`z > 0`; the bound is `A(z)·angMaj`, and `angMaj` is integrable on `Iθ`
(`Work.FTS.CoercivityFix.Assembly.angMaj_integrable`). -/
theorem fstar_slice_lt_top {α : ℝ} (hα : 0 < α)
    (hjet : ∀ i ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ 1000 * (1 + α ^ 2) ^ 2 * Work.Spaces.Gam α θ) (z : ℝ) :
    (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (Work.Construction.Fstar α) z θ)) < ⊤ := by
  have hpt := fstar_integrand_le_angMaj hα z hjet
  set A : ℝ := (α / Work.Spaces.c α) ^ 2 * (Work.Spaces.w z) ^ 2
      * (5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2) * (1 + Srad z) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have h1 : 0 ≤ 5 + 25 * (1000 * (1 + α ^ 2) ^ 2) ^ 2 := by positivity
    have h2 : 0 ≤ 1 + Srad z := by linarith [Srad_nonneg z]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1) h2
  have hstep : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (Work.Construction.Fstar α) z θ))
      ≤ ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (A * Work.FTS.LocData.angMaj α θ) := by
    refine lintegral_mono_ae ?_
    refine ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => ENNReal.ofReal_le_ofReal (hpt θ hθ))
  have hstep2 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (A * Work.FTS.LocData.angMaj α θ))
      = ENNReal.ofReal A * ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.FTS.LocData.angMaj α θ) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal A)
      (fun θ => ENNReal.ofReal (Work.FTS.LocData.angMaj α θ)) ENNReal.ofReal_lt_top.ne]
    refine lintegral_congr (fun θ => ?_)
    rw [ENNReal.ofReal_mul hA0]
  rw [hstep2] at hstep
  have hfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.FTS.LocData.angMaj α θ)) < ⊤ :=
    (Work.FTS.CoercivityFix.Assembly.angMaj_integrable α hα).lintegral_lt_top
  have hprod : ENNReal.ofReal A * (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.FTS.LocData.angMaj α θ)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  exact lt_of_le_of_lt hstep hprod

end Work.FTS.StrongPersist.Degen
