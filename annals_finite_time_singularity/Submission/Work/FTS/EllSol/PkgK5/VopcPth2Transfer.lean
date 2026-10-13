import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.ropBasic
import Submission.Work.FTS.EllipticEst.Cert.GbarLayer.Target
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.alphaDzW_Hk_le
import Submission.Work.FTS.ClassC.pth_Vop_EllResid_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `Work.FTS.EllSol.PkgK5.VopcPth2Transfer`

The second angular derivative of the *residual* `Ξ = EllResid α g Φg` is controlled by that of
the *straightened* unknown `Ψ̂ = ellShift α g Φg` plus the source `g`, at every level `k ≤ 5`:

`∂_θθΞ ∈ ℋ^k`  and  `|∂_θθΞ|_{ℋ^k} ≤ C (|∂_θθΨ̂|_{ℋ^k} + |g|_{ℋ^k})`.

This is the *reverse* (and easier) direction of the sibling
`Work.FTS.ClassC.NormPieces.pthIter2_shift_le_classC`, and it is the transfer that lets a
consumer who has the `∂_θθ`-honesty of the straight unknown obtain the same for the object
`EllResid α g Φg` on which the operators `Rop`, `Uop`, `Vop` act.

## Proof

The two unknowns differ on the whole plane by the *layer* `Ḡ(α,g)·sin 2θ`
(`Gsing = Gstar + Ḡ`, `Gstar = -(1/(4α)) L₁₂`, `PhiTil = EllResid`):

  `Ξ = Ψ̂ - Ḡ·sin 2θ`   (pointwise, `EllResid_eq_ellShift_sub_Gbar_point`),

whence the pointwise identity on the open quadrant

  `∂_θθΞ = ∂_θθΨ̂ + 4·(Ḡ·sin 2θ)`    (`∂_θθ(a(z) sin 2θ) = -4 a(z) sin 2θ`).

The `ℋ^k`-membership of `∂_θθΞ` is then the membership of the right-hand side
(`HkMem_add_open` for `∂_θθΨ̂` and the layer, whose membership is
`Cert.GbarLayer.layer_HkMem_target_of_smoothOpen`), transported back along the open-quadrant
equality by `Cert.GbarSin.HkMem_congr_Q0` (which needs *no* smoothness on the side being
transported to).  The norm bound is `HkNorm_add_le` (the layer is `SmoothOpen`, from
`ClassC.smoothOpen_GbarSin_classC`) followed by `HkNorm_const_mul` and the norm bound
`Cert.GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen` of the layer.

`ClassC.mem` supplies `HkMem α 7 g`, which `TT.HkMem_descend_open` downgrades to the required
level `k ≤ 5 ≤ 7`; that is the only place the bound `k ≤ 5` is used (the statement in fact
holds for every `k ≤ 7`).
-/
theorem VopcPth2Transfer :
    ∀ k : ℕ, k ≤ 5 → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg)) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
        ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
              + Work.Spaces.HkNorm α k g) := by
  intro k hk
  obtain ⟨CG, hCGpos, hCG⟩ :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen k
  refine ⟨Real.sqrt 2 * (1 + 4 * CG), ?_, ?_⟩
  · exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (by linarith)
  intro α g Φg hα hα4 hC hSmH hMemH
  have hα1 : α ≤ 1 := by linarith
  -- ## the source at the level of the statement
  have hgn : Work.Spaces.HkMem α k g :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (k := k) (l := 7) (f := g)
      (by omega) hC.reg.forall hC.mem
  -- ## the layer `Ḡ(α,g)·sin 2θ`
  have hSmL : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
    Work.FTS.ClassC.smoothOpen_GbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm hC.mem
  have hMemL : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_HkMem_target_of_smoothOpen α hα hα1 k g
      hC.reg hgn
  have hSm4L : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_const_mul 4 hSmL
  have hMem4L : Work.Spaces.HkMem α k
      (fun z θ => 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k 4 hMemL
  -- ## abbreviations
  set Ψh : ℝ → ℝ → ℝ := Work.FTS.EllSol.ellShift α g Φg with hΨhdef
  set Ξ : ℝ → ℝ → ℝ := Work.Elliptic.EllResid α g Φg with hΞdef
  have hSmΨh : Work.FTS.EllipticEst.SmoothOpen Ψh := hSmH
  have hSmP2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψh) := hSmΨh.pth.pth
  -- ## the pointwise transfer identity on the open quadrant
  have hP2eq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter 2 Ξ z θ
        = Work.Spaces.pthIter 2 Ψh z θ
          + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) := by
    intro z θ hz h1 h2
    have hWeq : Ξ = fun z θ => Ψh z θ - Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
      rw [hΞdef, hΨhdef]
      funext z' θ'
      rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
      simp only [Work.FTS.EllSol.ellShift_apply]
    rw [hWeq, Work.FTS.EllipticEst.pthIter2_sub hSmΨh hSmL hz h1 h2,
      Work.FTS.EllipticEst.pthIter2_radial_sin_two (Work.Elliptic.Gbar α g) z θ]
    ring
  -- ## membership of `∂_θθΞ`
  have hMemSum : Work.Spaces.HkMem α k
      (fun z θ => Work.Spaces.pthIter 2 Ψh z θ
        + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_add_open (α := α) (k := k) hSmP2 hSm4L hMemH hMem4L
  have hMemX : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ξ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hMemSum
      (fun z hz θ hθ => (hP2eq z θ hz hθ.1 hθ.2).symm)
  refine ⟨hMemX, ?_⟩
  -- ## the norm bound
  have hSqEq : Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 Ξ)
      = Work.Spaces.HkSq α k (fun z θ => Work.Spaces.pthIter 2 Ψh z θ
          + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ hz h1 h2 => hP2eq z θ hz h1 h2)
  have htri := Work.FTS.EllipticEst.HkNorm_add_le (α := α) (k := k)
    (f := Work.Spaces.pthIter 2 Ψh)
    (g := fun z θ => 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
    hSmP2.forall hSm4L.forall hMemH hMem4L
  have hcm : Work.Spaces.HkNorm α k
        (fun z θ => 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
      = 4 * Work.Spaces.HkNorm α k
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k 4
        (f := fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) hSmL.forall,
      show |(4 : ℝ)| = 4 by norm_num]
  have hleL : Work.Spaces.HkNorm α k
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
      ≤ CG * Work.Spaces.HkNorm α k g := hCG α g hα hα1 hC.reg hgn
  have hkey : Work.Spaces.HkNorm α k
        (fun z θ => 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
      ≤ 4 * CG * Work.Spaces.HkNorm α k g := by
    rw [hcm]
    calc 4 * Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
        ≤ 4 * (CG * Work.Spaces.HkNorm α k g) := mul_le_mul_of_nonneg_left hleL (by norm_num)
      _ = 4 * CG * Work.Spaces.HkNorm α k g := by ring
  have htri' : Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pthIter 2 Ψh z θ
        + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh)
          + 4 * CG * Work.Spaces.HkNorm α k g) := by
    refine le_trans htri ?_
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hkey)
      (Real.sqrt_nonneg 2)
  have hBnn : (0 : ℝ) ≤ Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh) :=
    Work.Spaces.HkNorm_nonneg α k _
  have hgnn : (0 : ℝ) ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  have hstep : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh)
        + 4 * CG * Work.Spaces.HkNorm α k g
      ≤ (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh)
          + Work.Spaces.HkNorm α k g) := by
    have hA : (0 : ℝ) ≤ 4 * CG * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh) :=
      mul_nonneg (mul_nonneg (by norm_num) hCGpos.le) hBnn
    nlinarith [hA, hgnn, hBnn]
  have hfinal : Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh)
        + 4 * CG * Work.Spaces.HkNorm α k g)
      ≤ Real.sqrt 2 * (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh)
          + Work.Spaces.HkNorm α k g) := by
    have h4 := mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg 2)
    simpa only [mul_assoc] using h4
  calc Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)
      = Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pthIter 2 Ψh z θ
          + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ))) := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hSqEq]
    _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh)
          + 4 * CG * Work.Spaces.HkNorm α k g) := htri'
    _ ≤ Real.sqrt 2 * (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψh)
          + Work.Spaces.HkNorm α k g) := hfinal
    _ = Real.sqrt 2 * (1 + 4 * CG) * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g) := by rw [hΨhdef]

end Work.FTS.EllSol.PkgK5
