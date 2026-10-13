/-
# `vopTransferK5c` — the `V`-slot of the pinned `K5` package

The target (statement frozen, at the bottom of this file) is the `V`-component of the elliptic
package at levels `2 ≤ k ≤ 5` in the *pinned* class used by the design's item A4:

  `HQo α k (V(Φ̃)) ∧ |V(Φ̃)|_{ℋᵏ} ≤ C (α²|z²∂_z²Ψ̂|_{ℋᵏ} + |∂_θ²Ψ̂|_{ℋᵏ} + |g|_{ℋᵏ})`,

where `Φ̃ = PhiTil α g Φg = EllResid α g Φg` is the elliptic residual and
`Ψ̂ = ellShift α g Φg = Φg + Gsing α g·sin 2θ` the straightened unknown, on which the weak
hypotheses (`EllWeakPos α k (orthSource g) Ψ̂` together with the two extra honesty levels
`HkMem α (k+3) (z²∂_z²Ψ̂)`, `HkMem α (k+2) (orthSource g)`) are imposed.

## The route

`V` is the *tangential* first-order operator `V(Ξ) = ∂_θΞ − tan θ·Ξ`; on the open quadrant

  `V(Ξ) = ∂_θΞ − 2 sin²θ · (Ξ / sin 2θ)`

(since `tan θ = 2 sin²θ / sin 2θ`), so the slot costs one angular derivative of the residual plus
the division-by-`sin 2θ` estimate.  Concretely:

* the traces of `D_z^jΞ` (`j ≤ k`) come from those of `D_z^jΨ̂` (`PkgK5.tracesK5`) by the exact
  identity `Ξ = Ψ̂ − Ḡ(α,g)·sin 2θ` (`PkgK5.residTracesK5`, `EllSol.ropBasic`);
* `VopAux.thetaPoincareOpenTrace k` turns `HkMem α k (∂_θ²Ξ)` into `HkMem α k Ξ`,
  `HkMem α k (∂_θΞ)` and the two norm comparisons;
* `PkgK5.divSinK5 k` gives `HkMem α k (Ξ/sin 2θ)` and `|Ξ/sin 2θ|_{ℋᵏ} ≤ C|∂_θΞ|_{ℋᵏ}`;
* `Work.Blocks.HkMul_ang_le` handles the `2 sin²θ` multiplier;
* the `∂_θ²`-membership and norm of `Ξ` are transferred from `Ψ̂` through the layer `Ḡ·sin 2θ`
  (`Cert.GbarLayer.layer_HkMem_target_of_smoothOpen`, `layer_Gbar_HkNorm_le_SmoothOpen`).

The two independent pieces of this route are isolated as the lemmas `vopcK5c_pth2_transfer`
(the layer transfer of `∂_θ²`) and `vopcK5c_core` (the abstract `V`-slot
`V(Ξ) ← ∂_θ²Ξ`); the remaining lemmas of this file are the smoothness of the residual, the
slice data it feeds to `divSinK5`, and the assembly.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.tracesK5
import Submission.Work.FTS.EllSol.PkgK5.divSinK5
import Submission.Work.FTS.EllSol.PkgK5.residTracesK5
import Submission.Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace
import Submission.Work.FTS.EllipticEst.Gbar_Hk_le_open
import Submission.Work.FTS.EllSol.ropBasic
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.Cert.GbarLayer.Target
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Smoothness of the residual and the slice data -/

/-- **`EllResid α g Φg` is `C^∞` on the open quadrant** for a source `g` of the class `C` and a
straightened unknown `Ψ̂ = ellShift α g Φg` smooth there: `Ξ = Ψ̂ − Ḡ(α,g)·sin 2θ`, and both
summands are smooth (`ClassC` supplies the all-order smoothness of `F_*(g)` and `HkMem α 7 g`,
i.e. precisely the hypotheses of `smoothOpen_negGbarSin_classC`). -/
theorem vopcK5c_resid_smooth {α : ℝ} {g Φg : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hC : Work.FTS.EllSol.ClassC α g)
    (hX : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Φg) := by
  have hG := smoothOpen_negGbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm hC.mem
  refine Work.FTS.EllipticEst.SmoothOpen.congr
    (Work.FTS.EllipticEst.smoothOpen_add hX hG) ?_
  intro z θ _ _ _
  rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
  simp only [Work.FTS.EllSol.ellShift_apply]
  ring

/-- **The angular slices of the radial iterates are `C^∞`** on `(0,π/2)`.  This is the
smoothness hypothesis consumed by `divSinK5` (whose interface asks for `C^∞` in the honest
order `Work.Stability.smoothOrder`). -/
theorem vopcK5c_slice_smooth {Ξ : ℝ → ℝ → ℝ} (hΞ : Work.FTS.EllipticEst.SmoothOpen Ξ)
    (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter j Ξ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hΞ.DzIter j) n
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DzIter j Ξ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx m _
    exact h1 m x hx m le_rfl
  exact Work.FTS.LocData.contDiffOn_slice_θ (s := Set.Ioi 0) (t := Set.Ioo 0 (Real.pi / 2)) h2 hz

/-! ## Piece 1 : the layer transfer of `∂_θ²` -/

/-- **The `∂_θ²`-slots of the residual from those of the straightened unknown.**  Since
`Ξ = Ψ̂ − Ḡ(α,g)·sin 2θ` and `∂_θ² (R(z)·sin 2θ) = −4 R(z)·sin 2θ`, on the open quadrant
`∂_θ²Ξ = ∂_θ²Ψ̂ + 4·(Ḡ·sin 2θ)`; the layer is in `ℋᵏ` (`layer_HkMem_target_of_smoothOpen`) with
`|Ḡ·sin 2θ|_{ℋᵏ} ≤ C|g|_{ℋᵏ}` (`layer_Gbar_HkNorm_le_SmoothOpen`), and `ClassC.mem` gives
`HkMem α 7 g`, hence `HkMem α k g` for `k ≤ 5`. -/
theorem vopcK5c_pth2_transfer :
    ∀ k : ℕ, k ≤ 5 → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg)) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
        ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
              + Work.Spaces.HkNorm α k g) := by
  intro k hk5
  obtain ⟨CG, hCG0, hGle⟩ :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen k
  refine ⟨Real.sqrt 2 * (1 + 4 * CG), by positivity, ?_⟩
  intro α g Φg hα hα4 hC hX hmemX
  have hα1 : α ≤ 1 := by linarith
  have hgn : Work.Spaces.HkMem α k g :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hC.reg.forall hC.mem
  -- the layer `Ḡ(α,g)·sin 2θ`, in both signs
  have hNsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-Work.Elliptic.Gbar α g z) * Real.sin (2 * θ)) :=
    smoothOpen_negGbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm hC.mem
  have hGsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.congr
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-1) hNsm)
      (fun z θ _ _ _ => by ring)
  have hGmem : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_HkMem_target_of_smoothOpen α hα hα1 k g hC.reg hgn
  have hGle' : Work.Spaces.HkNorm α k
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ≤ CG * Work.Spaces.HkNorm α k g :=
    hGle α g hα hα1 hC.reg hgn
  -- the pointwise identity `∂_θ²Ξ = ∂_θ²Ψ̂ + 4·(Ḡ sin 2θ)`
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ
          + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) := by
    intro z θ hz hθ0 hθ1
    have hE : Work.Elliptic.EllResid α g Φg
        = fun z θ => Work.FTS.EllSol.ellShift α g Φg z θ
            + (-Work.Elliptic.Gbar α g z) * Real.sin (2 * θ) := by
      funext z θ
      rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
      simp only [Work.FTS.EllSol.ellShift_apply]
      ring
    rw [hE, Work.FTS.EllipticEst.RPFresh.pthIter_add_on_Q0 hX hNsm 2 z θ hz hθ0 hθ1,
      congrFun (congrFun (Work.FTS.EllipticEst.RPFresh.pthIter_two_radial_sin
        (fun z => -Work.Elliptic.Gbar α g z)) z) θ]
    ring
  refine ⟨?_, ?_⟩
  · -- membership
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k ?_
      (fun z hz θ hθ => (hpoint z θ hz hθ.1 hθ.2).symm)
    exact Work.FTS.EllipticEst.HkMem_add_open hX.pth.pth
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 4 hGsm) hmemX
      (Work.FTS.LocData.HkMem_const_mul α k 4 hGmem)
  · -- norm
    have heq : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
        = Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pthIter 2
            (Work.FTS.EllSol.ellShift α g Φg) z θ
              + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ))) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
        Work.FTS.EllipticEst.HkSq_congr_open α k hpoint]
    rw [heq]
    have htri := Work.FTS.EllipticEst.HkNorm_add_le α k hX.pth.pth.forall
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 4 hGsm).forall hmemX
      (Work.FTS.LocData.HkMem_const_mul α k 4 hGmem)
    have h4 : Work.Spaces.HkNorm α k (fun z θ => 4 * (Work.Elliptic.Gbar α g z
        * Real.sin (2 * θ)))
        ≤ 4 * (CG * Work.Spaces.HkNorm α k g) := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul α k 4 hGsm.forall]
      have h2 : |(4 : ℝ)| = 4 := by norm_num
      rw [h2]
      exact mul_le_mul_of_nonneg_left hGle' (by norm_num)
    have hB0 := Work.Spaces.HkNorm_nonneg α k (Work.Spaces.pthIter 2
      (Work.FTS.EllSol.ellShift α g Φg))
    have hG0 := Work.Spaces.HkNorm_nonneg α k g
    calc Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pthIter 2
          (Work.FTS.EllSol.ellShift α g Φg) z θ
            + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
              (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k (fun z θ => 4 * (Work.Elliptic.Gbar α g z
                * Real.sin (2 * θ)))) := htri
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
              (Work.FTS.EllSol.ellShift α g Φg)) + 4 * (CG * Work.Spaces.HkNorm α k g)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl h4) (Real.sqrt_nonneg 2)
      _ ≤ Real.sqrt 2 * (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
              (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g) := by
          have hkey : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + 4 * (CG * Work.Spaces.HkNorm α k g)
              ≤ (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g) := by
            nlinarith [hB0, hG0, hCG0]
          calc Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + 4 * (CG * Work.Spaces.HkNorm α k g))
              ≤ Real.sqrt 2 * ((1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g)) :=
                mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg 2)
            _ = Real.sqrt 2 * (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g) := by ring

/-! ## Piece 2 : the abstract `V`-slot -/

/-- **The `V`-slot from the `∂_θ²`-data of the residual.**  On the open quadrant
`V(Ξ) = ∂_θΞ − 2 sin²θ·(Ξ/sin 2θ)`; `thetaPoincareOpenTrace` controls `Ξ`, `∂_θΞ` by `∂_θ²Ξ`,
`divSinK5` controls `Ξ/sin 2θ` by `∂_θΞ`, and `HkMul_ang_le` the angular multiplier `2 sin²θ`.
The slice-smoothness hypothesis is the interface of `divSinK5`. -/
theorem vopcK5c_core (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Ξ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen Ξ →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ξ) →
      Work.FTS.VocabO.HQo α k (Work.FTS.EllipticEst.Vop α Ξ) ∧
      Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
        ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by
  obtain ⟨Cd, hCd0, hdiv⟩ := divSinK5 k hk
  obtain ⟨Cp, hCp0, hpo⟩ := Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace k
  obtain ⟨Ca, hCa0, hang⟩ := Work.Blocks.HkMul_ang_le k
  have hCa0' : (0 : ℝ) ≤ Real.sqrt Ca := Real.sqrt_nonneg Ca
  refine ⟨Real.sqrt 2 * (1 + 2 * Real.sqrt Ca * Cd) * Cp, by positivity, ?_⟩
  intro α Ξ hα hα4 hsm htr hsl hmem
  have hα1 : α ≤ 1 := by linarith
  have htr0 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    fun z hz j hj => (htr j hj z hz).1
  have htr1 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    fun z hz j hj => (htr j hj z hz).2
  -- ## the Poincaré estimate on `Ξ`
  obtain ⟨hmemΞ, hmempthΞ, hleΞ, hlepthΞ⟩ := hpo α Ξ hα hα4 hsm.forall htr hmem
  -- ## the division estimate
  obtain ⟨hmemQ, hleQ⟩ := hdiv α Ξ hα hα1 hsm hsl htr0 htr1 hmempthΞ
  have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Ξ z θ / Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hsm
  -- ## the `sin²θ` multiplier
  have hSsmem : Work.Spaces.HkMem α k
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) :=
    ((hang α (fun z θ => Ξ z θ / Real.sin (2 * θ)) hα hα1 hQsm).2.2 hmemQ).2.2.1
  have hSsq : Work.Spaces.HkSq α k (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
      ≤ Ca * Work.Spaces.HkSq α k (fun z θ => Ξ z θ / Real.sin (2 * θ)) :=
    ((hang α (fun z θ => Ξ z θ / Real.sin (2 * θ)) hα hα1 hQsm).2.2 hmemQ).2.2.2
  have hSsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) :=
    Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul (a := fun θ => Real.sin θ ^ 2)
      (by fun_prop) hQsm
  have hTsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-2) hSsm
  have hTsmem : Work.Spaces.HkMem α k
      (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-2) hSsmem
  have hSnorm : Work.Spaces.HkNorm α k
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
      ≤ Real.sqrt Ca * Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ)) := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α k
        (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
        ≤ Real.sqrt (Ca * Work.Spaces.HkSq α k (fun z θ => Ξ z θ / Real.sin (2 * θ))) :=
      Real.sqrt_le_sqrt hSsq
    have h2 : Real.sqrt (Ca * Work.Spaces.HkSq α k (fun z θ => Ξ z θ / Real.sin (2 * θ)))
        = Real.sqrt Ca * Real.sqrt (Work.Spaces.HkSq α k
            (fun z θ => Ξ z θ / Real.sin (2 * θ))) :=
      Real.sqrt_mul (x := Ca) (le_of_lt hCa0) _
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact le_trans h1 (le_of_eq h2)
  have hTnorm : Work.Spaces.HkNorm α k
      (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
      ≤ 2 * (Real.sqrt Ca * (Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)))) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k (-2) hSsm.forall]
    have h1 : (|(-2 : ℝ)|) * Work.Spaces.HkNorm α k
        (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
        = 2 * Work.Spaces.HkNorm α k
          (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) := by norm_num
    rw [h1]
    have h2 : Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ))
        ≤ Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)) := by
      calc Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ))
          ≤ Cd * Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ) := hleQ
        _ ≤ Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)) :=
            mul_le_mul_of_nonneg_left hlepthΞ (le_of_lt hCd0)
    calc 2 * Work.Spaces.HkNorm α k (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
        ≤ 2 * (Real.sqrt Ca * Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hSnorm (by norm_num)
      _ ≤ 2 * (Real.sqrt Ca * (Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCa0') (by norm_num)
  -- ## the pointwise identity
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Vop α Ξ z θ
        = Work.Spaces.pth Ξ z θ
          + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) := by
    intro z θ hz hθ0 hθ1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
    have hsin : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ1]))
    show Work.Spaces.pth Ξ z θ - Real.tan θ * Ξ z θ = _
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
    ring
  -- ## smoothness, membership and norm
  have hVopsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Vop α Ξ) :=
    Work.FTS.EllipticEst.SmoothOpen.congr
      (Work.FTS.EllipticEst.smoothOpen_add hsm.pth hTsm)
      (fun z θ hz hθ0 hθ1 => (hpoint z θ hz hθ0 hθ1).symm)
  have hVopmem : Work.Spaces.HkMem α k (Work.FTS.EllipticEst.Vop α Ξ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hVopsm
      (fun z θ hz hθ0 hθ1 => (hpoint z θ hz hθ0 hθ1).symm)
      (Work.FTS.EllipticEst.HkMem_add_open hsm.pth hTsm hmempthΞ hTsmem)
  refine ⟨⟨hVopsm, hVopmem⟩, ?_⟩
  have hsqeq : Work.Spaces.HkSq α k (Work.FTS.EllipticEst.Vop α Ξ)
      = Work.Spaces.HkSq α k (fun z θ => Work.Spaces.pth Ξ z θ
          + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α k hpoint
  have hnormeq : Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
      = Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pth Ξ z θ
          + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsqeq]
  rw [hnormeq]
  have htri := Work.FTS.EllipticEst.HkNorm_add_le α k hsm.pth.forall hTsm.forall
    hmempthΞ hTsmem
  calc Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pth Ξ z θ
        + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ)
          + Work.Spaces.HkNorm α k (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2
              * (Ξ z θ / Real.sin (2 * θ))))) := htri
    _ ≤ Real.sqrt 2 * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)
          + 2 * (Real.sqrt Ca * (Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
        exact add_le_add hlepthΞ hTnorm
    _ = Real.sqrt 2 * (1 + 2 * Real.sqrt Ca * Cd) * Cp
          * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by ring

/-! ## The assembly -/

/-- **The `V`-slot from its two pieces.**  Everything else is the dissection of the residual
(smoothness, traces via `Ψ̂`, and the arithmetic of the constants); the conclusion is literally
the frozen target. -/
theorem vopcK5c_assembly
    (hB : ∀ k : ℕ, k ≤ 5 → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (g Φg : Fn), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllSol.ClassC α g →
        Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) →
        Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg)) →
        Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) ∧
        Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
          ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
                + Work.Spaces.HkNorm α k g))
    (hV : ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (Ξ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.SmoothOpen Ξ →
        (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
          Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
          Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
        (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2))) →
        Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ξ) →
        Work.FTS.VocabO.HQo α k (Work.FTS.EllipticEst.Vop α Ξ) ∧
        Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
          ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ))
    (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) := by
  obtain ⟨CB, hCB0, hB'⟩ := hB k hk5
  obtain ⟨CV, hCV0, hV'⟩ := hV k (by omega)
  refine ⟨CV * CB, mul_pos hCV0 hCB0, ?_⟩
  intro α g Φg hα hα4 hC hsol hsmo hweak hAh hFmem
  -- ## the straight unknown is smooth and carries the traces
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have htrX := tracesK5 k hk α g Φg hα hα4 hC hsol hsmo hweak hAh hFmem
  have htrΞ := residTracesK5 k α g Φg hα hα4 hC hXsm htrX
  -- ## the smoothness of the residual and of its slices
  have hΞsm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Φg) :=
    vopcK5c_resid_smooth (α := α) (g := g) (Φg := Φg) hα hC hXsm
  have hslice : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun z hz j _ => vopcK5c_slice_smooth hΞsm j hz
  -- ## the two pieces
  have hBk := hB' α g Φg hα hα4 hC hXsm hweak.memB
  have hVk := hV' α (Work.Elliptic.EllResid α g Φg) hα hα4 hΞsm
    (fun j hj z hz => htrΞ j (by omega) z hz) hslice hBk.1
  rw [Work.FTS.EllipticEst.Vop_PhiTil_eq]
  refine ⟨hVk.1, ?_⟩
  -- ## the arithmetic of the constants
  have hA0 : (0 : ℝ) ≤ α ^ 2 * Work.Spaces.HkNorm α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ) :=
    mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
  have hCVnn : (0 : ℝ) ≤ CV := le_of_lt hCV0
  calc Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Φg))
      ≤ CV * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) :=
        hVk.2
    _ ≤ CV * (CB * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g)) :=
        mul_le_mul_of_nonneg_left hBk.2 hCVnn
    _ = CV * CB * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g) := by ring
    _ ≤ CV * CB * (α ^ 2 * Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
          + Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hA0]

theorem vopTransferK5c (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) :=
  vopcK5c_assembly vopcK5c_pth2_transfer vopcK5c_core k hk hk5

end Work.FTS.EllSol.PkgK5
