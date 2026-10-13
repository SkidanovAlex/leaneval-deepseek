/-
# `Work.FTS.LocData.HkMem_zfar_Fstar` — the far part `zfar L F_*` lies in `𝓗⁴`

The target of this module is

  `HkMem_zfar_Fstar : Work.Spaces.HkMem α 4 (Work.Stability.zfar L (Work.Construction.Fstar α))`

for `0 < α ≤ 1` and `L ≥ 1`: the far part `(1 - χ(z/L))·F_*` of the reference profile is
*honestly* in the weighted space `ℋ⁴`, i.e. all the weighted derivatives occurring in
`HkSq α 4` give integrable iterated integrals.

The proof is the standard "membership by domination" of the chapter
(`Work.FTS.LocData.HkMem_of_majorant`), with the pointwise majorant

  `M z θ = C·α²·angMaj α θ / (1+z)²`,

where `C` is the *free* constant of `Work.FTS.LocData.ZfarFstar.ZFMaj.zfar_Fstar_hk_majorant`
(it must be free: the cut-off `χ = Real.smoothTransition (2 - ‖·‖)` has a fourth `D_z`-derivative
of size `≈1.8·10⁴` in the middle of its transition annulus, so no universal constant works; see
the discussion in `HkIntegrand_zfar_Fstar_le.lean`).

* the `ℋ⁴`-integrand of `zfar L F_*` is continuous on the open quadrant
  (`continuousOn_HkIntegrand_smoothQuad`, from `SmoothQuad (zfar L F_*)`);
* it is dominated by `M` on the closed quadrant (`zfar_Fstar_hk_majorant`);
* the `θ`-slices of `M` are integrable on `Iθ` and their `z`-integral is integrable on `Iz`
  (`angMaj_mem` + `∫_0^∞ (1+z)^{-2} < ∞`), which is `angMaj_majorant_integrable` below.

We prove the two smoothness/integrability ingredients here, since the module that used to
carry them (`Work.FTS.LocData.Main`) imports *this* one.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_locG
import Submission.Work.FTS.LocData.ZfarFstar.ZFMaj
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.angMaj_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The far part `zfar L F_*` is `C^∞` on the quadrant -/

/-- **`zfar L F_* = (1 - χ(z/L))·F_*` is `C^∞` on the open quadrant**: it is the difference
`1·F_* - χ(·/L)·F_*` of two products of the basic `C^∞` profiles of the chapter.  (The
hypotheses `0 < α`, `α ≤ 1` of the route are not needed.) -/
theorem zfar_Fstar_smoothQuad (α L : ℝ) :
    SmoothQuad (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  have hsub : SmoothQuad (fun z θ => (1 : ℝ) * Work.Construction.Fstar α z θ
      - Work.Stability.chi (z / L) * Work.Construction.Fstar α z θ) :=
    SmoothQuad_sub (SmoothQuad_const_mul 1 (Fstar_smoothQuad α))
      (SmoothQuad_mul (SmoothQuad_chi_div L) (Fstar_smoothQuad α))
  unfold SmoothQuad at hsub ⊢
  refine hsub.congr (fun p _ => ?_)
  simp only [Function.uncurry_def, Work.Stability.zfar_apply]
  ring

/-! ## Integrability of the angular majorant times the radial weight -/

/-- **The majorant `c·angMaj α θ/(1+z)²` is integrable in `θ` for every `z ∈ Iz`, and its
`z`-integral is integrable on `Iz`.**  This is the `hMslice`/`hMz` pair of
`Work.FTS.LocData.HkMem_of_majorant` for the angular majorant `angMaj` of the chapter:
`angMaj` is integrable on `Iθ` (`angMaj_mem`) and `z ↦ (1+z)^{-2}` is integrable on `Iz`. -/
theorem angMaj_majorant_integrable (α c : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => c * angMaj α θ / (1 + z) ^ 2) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        Work.Spaces.Iz := by
  obtain ⟨hint, _⟩ := angMaj_mem α hα hα1
  constructor
  · intro z _
    have h : IntegrableOn (fun θ => (c * ((1 + z) ^ 2)⁻¹) * angMaj α θ) Work.Spaces.Iθ :=
      hint.const_mul _
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Icc
    ring
  · have hbase : IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hconst : IntegrableOn (fun x : ℝ => (∫ θ in Work.Spaces.Iθ, c * angMaj α θ)
        * (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hbase.const_mul _
    have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
          = (∫ θ in Work.Spaces.Iθ, c * angMaj α θ) * (z + 1) ^ (-2 : ℝ) := by
      intro z _
      rw [show (fun θ => c * angMaj α θ / (1 + z) ^ 2)
          = fun θ => (c * angMaj α θ) * ((1 + z) ^ 2)⁻¹ from by funext θ; ring]
      rw [integral_mul_const]
      congr 1
      rw [show (1 + z : ℝ) = z + 1 by ring]
      norm_num [Real.rpow_natCast]
    have hcon : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      hconst.congr_fun (fun z hz => (heq z hz).symm) measurableSet_Ioi
    have hae : Set.Ici (0 : ℝ) =ᵐ[volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
    rw [Work.Spaces.Iz]
    exact hcon.congr_set_ae hae

/-! ## The target -/

/-- **The far part `zfar L F_*` of the reference profile lies in `𝓗⁴`** for `0 < α ≤ 1` and
`L ≥ 1`. -/
theorem HkMem_zfar_Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L : ℝ} (hL : 1 ≤ L) :
    Work.Spaces.HkMem α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  obtain ⟨C, hC0, hCle⟩ := ZF.zfar_Fstar_hk_majorant α hα hα1 hL
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α))
        p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 _ (zfar_Fstar_smoothQuad α L)
  refine HkMem_of_majorant α 4
    (M := fun z θ => C * α ^ 2 * angMaj α θ / (1 + z) ^ 2) hcont ?_ ?_ ?_
  · exact (angMaj_majorant_integrable α (C * α ^ 2) hα hα1).1
  · exact (angMaj_majorant_integrable α (C * α ^ 2) hα hα1).2
  · intro z hz θ hθ
    exact hCle z hz θ hθ

end Work.FTS.LocData
