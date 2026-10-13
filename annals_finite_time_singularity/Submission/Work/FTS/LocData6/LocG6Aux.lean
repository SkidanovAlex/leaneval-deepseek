/-
# `Work.FTS.LocData6.LocG6Aux` — the `ℋ⁶` majorant, membership and `RegQ α 6` of the localised
datum, conditional on the order-`6` jet inputs

This module assembles, exactly as `LocDataExt/LocG5.lean` does at order `5`, the pointwise
`ℋ⁶`-majorant of the localised datum `locG α L β (hLoc α)`, its `ℋ⁶`-membership and the interior
regularity class `RegQ α 6`, from

* the order-`6` jet bound of `zfarR L` (`LocData6.hB_zfar6`, `HkIntegrand_zfar6_le` of the
  sibling module `LocData6.ZfarMaj6`) — carried here as a hypothesis on `Ici L`;
* the angular bound `(D_θ^iΓ)² ≤ Rθ·Γ²` (`i ≤ 6`) — carried as a hypothesis;
* the majorant `HkIntegrand α 6 (hLoc α) ≤ Kb·angMaj/(1+z)²` of the bump — carried as a
  hypothesis (delivered by `LocData6.hLoc_majorant6`);
* the vanishing of the integration-by-parts boundary terms at order `6`, which is the generic
  `LocDataExt.bdryTraces_locG` instantiated at `k = 6`.

The instantiation of all the hypotheses from the order-`6` jet lemmas is the assembly
(`LocData6.RegQ6`, `LocData6.Small6`, `LocData6.Main`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocData6.ZfarMaj6
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Traces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The generic-`h` form of the majorant (the order-`6` `HkIntegrand_locG_le_gen`) -/

/-- **The pointwise majorant of the `ℋ⁶`-integrand of `locG`, for an arbitrary bump `h`**: if
`Cz·α²·angMaj/(1+z)²` dominates the `ℋ⁶`-integrand of the far part `zfar L F_*` and
`K²·angMaj/(1+z)²` that of `h`, then `(2Cz·α² + 2β²K²)·angMaj/(1+z)²` dominates the
`ℋ⁶`-integrand of `locG α L β h` — the order-`6` form of
`Work.FTS.LocData.HkIntegrand_locG_le_gen`. -/
theorem HkIntegrand_locG_le_gen6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    {L β K Cz : ℝ} (hsh : Work.FTS.LocData.SmoothQuad h)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ ≤ K ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.locG α L β h) z θ
      ≤ (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  rw [Work.FTS.LocData.locG_as_sum]
  have hsq : Work.FTS.LocData.SmoothQuad
      (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) :=
    Work.FTS.LocData.smoothQuad_neg (Work.FTS.LocData.SmoothQuad_zfar_Fstar α L)
  have hsq2 : Work.FTS.LocData.SmoothQuad (fun z θ => β * h z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul β hsh
  have hstep := Work.FTS.LocData.HkIntegrand_add_le α 6 hsq hsq2 hz hθ
  have hneg : Work.Spaces.HkIntegrand α 6
      (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) z θ
      = Work.Spaces.HkIntegrand α 6
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ :=
    Work.FTS.LocData.HkIntegrand_neg α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
  have hcm : Work.Spaces.HkIntegrand α 6 (fun z θ => β * h z θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α 6 h z θ :=
    Work.FTS.LocData.HkIntegrand_const_mul α 6 β h z θ
  have hzfar := hCz z hz θ hθ
  have hbump := hK z hz θ hθ
  have hang : 0 ≤ Work.FTS.LocData.angMaj α θ := Work.FTS.LocData.angMaj_nonneg hθ
  have hden : 0 < (1 + z) ^ 2 := pow_pos (by linarith [show (0 : ℝ) ≤ z from hz]) 2
  rw [hneg, hcm] at hstep
  refine le_trans hstep ?_
  have h1 : 2 * Work.Spaces.HkIntegrand α 6
        (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      ≤ 2 * (Cz * α ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by linarith
  have h2 : 2 * (β ^ 2 * Work.Spaces.HkIntegrand α 6 h z θ)
      ≤ 2 * (β ^ 2 * (K ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)) := by
    have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
    nlinarith [hbump, hβ2, hang, hden]
  have h3 : 2 * (Cz * α ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
      + 2 * (β ^ 2 * (K ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2))
      = (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
    ring
  linarith [h1, h2, h3]

/-- **Membership of `locG α L β h` in `ℋ⁶` for an arbitrary bump `h`**, from the two majorants
(the order-`6` form of `Work.FTS.LocData.HkMem_locG_gen`). -/
theorem HkMem_locG_gen6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ} {L β K Cz : ℝ}
    (hsh : Work.FTS.LocData.SmoothQuad h)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ ≤ K ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 6 (Work.FTS.LocData.locG α L β h) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.locG α L β h) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 6 _
      (Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 hsh)
  refine Work.FTS.LocData.HkMem_of_majorant (f := Work.FTS.LocData.locG α L β h)
    (M := fun z θ => (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2)
      * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 6 hcont ?_ ?_ ?_
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α
      (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α
      (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) hα hα1).2
  · intro z hz θ hθ
    exact HkIntegrand_locG_le_gen6 α hα hα1 hsh hCz hK hz hθ

/-! ## The pointwise `ℋ⁶`-majorant of `locG` -/

/-- **The pointwise `ℋ⁶`-majorant of the localised datum** `locG α L β (hLoc α)`, from the
order-`6` jet bound of `zfarR L`, the angular bound and the majorant of the bump.  This is the
order-`6` instance of `Work.FTS.LocDataExt.HkIntegrand_locG_le5`. -/
theorem HkIntegrand_locG6_le (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨K₁, hK₁, h₁⟩ := HkIntegrand_zfar6_le α L hα hL hA hRθ hAz hΓ
  refine ⟨2 * K₁ + 2 * β ^ 2 * Kb, by nlinarith [hK₁, hKb0, sq_nonneg β], fun z hz θ hθ => ?_⟩
  -- the two separable pieces of `locG`
  have hcpos : 0 < Work.Spaces.c α := by
    exact lt_of_lt_of_le (by norm_num) (Work.FTS.LocData.c_ge_three_fifths α hα hα1)
  have hs1 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
        * Work.Spaces.Gam α θ) :=
    Work.FTS.LocDataExt.smoothQuad_sepGam (α := α) (by
      refine (ContDiffOn.const_smul (-(α / Work.Spaces.c α))
        (Work.FTS.LocDataExt.contDiffOn_zfarR L)).congr (fun z _ => ?_)
      simp [smul_eq_mul])
  have hs2 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ) :=
    Work.FTS.LocDataExt.smoothQuad_sepGam (α := α) (by
      refine (ContDiffOn.const_smul β
        (Work.FTS.LocData.contDiff_bumpZ.contDiffOn)).congr (fun z _ => ?_)
      simp [smul_eq_mul])
  -- the bump piece as the `β`-multiple of `hLoc α`
  have hp2 : Work.Spaces.HkIntegrand α 6
      (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ := by
    rw [show (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ)
        = fun z θ => β * Work.FTS.LocData.hLoc α z θ from by
      funext z θ
      rw [Work.FTS.LocData.hLoc_apply]
      ring]
    exact Work.FTS.LocData.HkIntegrand_const_mul α 6 β (Work.FTS.LocData.hLoc α) z θ
  have hA2 : (Work.Spaces.HkIntegrand α 6
        (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ) z θ)
      ≤ β ^ 2 * (Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    rw [hp2]
    exact mul_le_mul_of_nonneg_left (hKb z hz θ hθ) (sq_nonneg β)
  rw [Work.FTS.LocDataExt.locG_split α L β]
  refine (Work.FTS.LocData.HkIntegrand_add_le α 6 hs1 hs2 hz hθ).trans ?_
  refine (add_le_add (mul_le_mul_of_nonneg_left (h₁ z hz θ hθ) (by norm_num))
    (mul_le_mul_of_nonneg_left hA2 (by norm_num))).trans ?_
  refine le_of_eq ?_
  ring

/-! ## Membership in `ℋ⁶` -/

/-- **The localised datum lies in `ℋ⁶`**, from the order-`6` jet inputs. -/
theorem HkMem_locG6 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  obtain ⟨K, hK, hmaj⟩ := HkIntegrand_locG6_le α L β hα hα1 hL hA hRθ hAz hΓ hKb0 hKb
  refine Work.FTS.LocData.HkMem_of_majorant
    (f := Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 6
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 6 _
      (Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α)))
    ?_ ?_ ?_
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).2
  · intro z hz θ hθ
    exact hmaj z hz θ hθ

/-! ## The boundary traces at order `6` -/

/-- **The vanishing boundary traces of the localised datum at order `6`**: the generic
`Work.FTS.LocDataExt.bdryTraces_locG` at `k = 6`. -/
theorem bdryTraces_locG6 (α L β : ℝ) (hα : 0 < α) (hL : 1 ≤ L) {CΓ CF : ℝ}
    (hCΓ : 0 ≤ CΓ) (hCF : 0 ≤ CF)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ CΓ * Work.Spaces.Gam α θ)
    (hF : ∀ b ≤ 6, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    Work.FTS.Nonlin.BdryTraces α 6
      (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) :=
  Work.FTS.LocDataExt.bdryTraces_locG α L β hα hL (k := 6) hCΓ hCF hΓ hF

/-! ## `RegQ α 6` -/

/-- **The localised datum lies in `RegQ α 6`**, from the order-`6` jet inputs (the `Ici L` jet
bound of `zfarR L`, the angular bound and the majorant of the bump). -/
theorem regQ_locG6_of_jets (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2)
    (hΓabs : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ 100000 * Work.Spaces.Gam α θ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
    {CF : ℝ} (hCF : 0 ≤ CF)
    (hF : ∀ b ≤ 6, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    Work.FTS.Nonlin.RegQ α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) :=
  ⟨Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α),
    HkMem_locG6 α L β hα hα1 hL hA hRθ hAz hΓ hKb0 hKb,
    bdryTraces_locG6 α L β hα hL (by norm_num) hCF hΓabs hF⟩

end Work.FTS.LocData6
