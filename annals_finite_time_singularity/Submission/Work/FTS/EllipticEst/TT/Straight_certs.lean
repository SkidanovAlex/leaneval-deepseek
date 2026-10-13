/-
Copyright: work module for the Elgindi finite-time singularity project.

# The "straightened solution" certificates of §'Elliptic Regularity Estimates'

This module proves `Work.FTS.EllipticEst.TT.Straight_certs`: the smoothness and `ℋ^k`-membership
certificates for the pieces of the straightened solution

  `Ψ̂ = Ψ + Gsing α F · sin 2θ`,  `Ḡ(α,F)·sin 2θ`,  `L₁₂(F)·sin 2θ`,  `Ḡ(α,F)`

of the elliptic chapter of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

The statement (and the name) are fixed by the caller.  The proof collects

* the `C^∞`-calculus of the radial multiples of `sin 2θ` (`pthIter_two_radialSin`,
  `SmoothOpen.sep_mul`, the `SmoothOpen`-closure of the iterated operators);
* the smoothness of `Gsing` and the two relations `α z G' = -5Ḡ`,
  `α²z²G'' + α(5+α)zG' = (15/4)F_*` (`Gsing_smooth_rel`);
* the membership `Ḡ·sin 2θ ∈ ℋ^k` (`HkMem_Gbar_sin_a1`, the `α ≤ 1` version of
  `Cert.GbarLayer.layer_HkMem_Gbar_sin`);
* the three further analytic inputs `D_zΨ ∈ ℋ^k`, the moment identity for `L₁₂(F)` and
  `L₁₂(F)·sin 2θ ∈ ℋ^k`, isolated below as `HkMem_Dz_a1`, `L12_moment_eq_a1`,
  `HkMem_L12_sin_a1`;
* the transfer of all statements from the right-hand sides of the pointwise identities to the
  straightened solution along the open quadrant (`HkMem_agreeOnQ`).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.GbarSin_layer
import Submission.Work.FTS.EllipticEst.Cert.Gsing_identities_eh
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar
import Submission.Work.FTS.EllipticEst.Cert.GbarLayer.Target
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.EllipticEst.Cert.L12Sin_mem
import Submission.Work.FTS.EllipticEst.Cert.HkMemRadialSin
import Submission.Work.FTS.EllipticEst.TT.Shim.FstarIterateIntegrable
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMemDzAux
import Submission.Work.FTS.EllipticEst.TT.Straight_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary `∂_θ`-calculus for radial multiples of `sin 2θ` -/

/-- `∂_θ (sin 2θ) = 2 cos 2θ`. -/
theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ
        ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
  exact h.deriv

/-- `∂_θ (2 cos 2θ) = -4 sin 2θ`. -/
theorem deriv_two_mul_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ = -4 * Real.sin (2 * θ) := by
  have h : HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (-4 * Real.sin (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
      simpa [Function.comp_def, mul_comm, mul_assoc] using
        (Real.hasDerivAt_cos (2 * θ)).comp θ
          ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
    have h2 := h1.const_mul 2
    have he : 2 * (-2 * Real.sin (2 * θ)) = -4 * Real.sin (2 * θ) := by ring
    rwa [he] at h2
  exact h.deriv

/-- The second `θ`-derivative of a radial multiple of `sin 2θ`: it is `-4` times the function. -/
theorem pthIter_two_radialSin (g : ℝ → ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ))
      = fun z θ => -4 * (g z * Real.sin (2 * θ)) := by
  have h1 : Work.Spaces.pth (fun z θ => g z * Real.sin (2 * θ))
      = fun z θ => g z * (2 * Real.cos (2 * θ)) := by
    funext z θ
    simp only [Work.Spaces.pth]
    rw [deriv_const_mul_field, deriv_sin_two]
  funext z θ
  rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, h1]
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_field, deriv_two_mul_cos_two]
  ring

/-! ## The `∂_θ`-iterates of `C^∞` functions on the open quadrant

The two facts below are the `SmoothOpen`-closure of the `∂_θ`-iterates and their additivity; the
proofs are the standard ones (`C^∞`-slices are differentiable, `deriv` is additive there). -/

/-- `SmoothOpen` is closed under the `∂_θ`-iterates. -/
theorem SmoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `∂_θ`-iterates are additive on data which are `C^∞` on the open quadrant. -/
theorem pthIter_add_of_smoothOpen {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i : ℕ) : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter i f z θ + Work.Spaces.pthIter i g z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((SmoothOpen_pthIter hf n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((SmoothOpen_pthIter hg n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      rw [Work.Spaces.pthIter_succ]
      show deriv (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ') θ
        = deriv (fun θ' => Work.Spaces.pthIter n f z θ') θ
          + deriv (fun θ' => Work.Spaces.pthIter n g z θ') θ
      rw [heq.deriv_eq]
      exact deriv_add hd1 hd2

/-! ## The smoothness of `Gsing` and its two relations -/

/-- **The `Gsing` certificates at `α ≤ 1`**: the singular term `Gsing α F` is `C^∞` on `(0,∞)`
and satisfies the two relations `α z ∂_zGsing = -5Ḡ` and
`α²z²∂_zzGsing + α(5+α)z∂_zGsing = (15/4)F_*` which drive the straightening. -/
theorem Gsing_smooth_rel (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ), α * z * deriv (Work.Elliptic.Gsing α F) z
        = -5 * Work.Elliptic.Gbar α F z) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z) := by
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.fstar_smooth_of_sol_fts α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol
      hHyp.memF
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α F hFsm hFint hα hα1
  refine ⟨?_, ?_, ?_⟩
  · intro m
    have h1 : ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.Cert.L12_contDiffOn_Ioi F hFsm hFint m
    have h2 : ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α F hα hFsm hFint m
    have h3 : ContDiffOn ℝ m (fun z => -(1 / (4 * α)) * Work.Elliptic.L12 F z) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.Cert.contDiffOn_const_mul_real (c := -(1 / (4 * α))) h1
    exact (h3.add h2).congr fun z _ => rfl
  · exact Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12 hFc hJ
  · exact Work.Elliptic.Gsing_ode α F hα hL12 hFc hJ

/-! ## The `ℋ^k`-certificate of `Ḡ(α,F)·sin 2θ` at `α ≤ 1` -/

/-- `Ḡ(α,F)·sin 2θ ∈ ℋ^k` for the data of `EllHyp` and `0 < α ≤ 1`.  This is the
`α ≤ 1/4`-statement `Cert.GbarLayer.layer_HkMem_Gbar_sin` with the (unused) bound relaxed, the
source `F` being replaced by its open-quadrant representative `bslOp α Ψ`. -/
theorem HkMem_Gbar_sin_a1 (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  have hOpen : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ hHyp.smoothNbhd
  have hMem : Work.Spaces.HkMem α k (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hHyp.memF
      (fun z hz θ hθ => (hHyp.sol.1 z hz θ hθ.1 hθ.2).symm)
  have hTarget :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_HkMem_target_of_smoothOpen α hα hα1 k
      (Work.Elliptic.bslOp α Ψ) hOpen hMem
  have hfs : ∀ s, 0 < s →
      Work.Elliptic.Fstar F s = Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) s :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_Fstar_bslOp_eq_of_sol α hHyp.sol
  refine Work.Coercivity.HkMem_congr_Ioi α k hTarget ?_
  intro z hz θ hθ
  rw [Work.FTS.EllipticEst.Cert.GbarSin.Gbar_congr_of_fstar_eq α hfs z hz]

/-! ## The three analytic inputs of the assembly

`HkMem_Dz_a1` (the radial `D_z`-Agmon estimate), `L12_moment_eq_a1` (the moment identity which
identifies `L₁₂(F)`) and `HkMem_L12_sin_a1` (the Hardy estimate for `L₁₂(F)·sin 2θ`) are the
three further certificates consumed below. -/

/-- `D_zΨ ∈ ℋ^k` for the data of `EllHyp` and `0 < α ≤ 1`. -/
theorem HkMem_Dz_a1 (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.Dz Ψ) :=
  HkMem_Dz_psi_a1 α k F Ψ hα hα1 hHyp

/-- The `ℋ^k`-certificate of the first singular term `L₁₂(F)·sin 2θ`, at `α ≤ 1`.

The moment identity `L₁₂(F)(z) = 15αF_*(Ψ)(z) + 3α²F_*(D_zΨ)(z)` (`L12_moment_eq_a1`) holds
on `(0,∞)`, and each of the two moments lies in `ℋ^k` after multiplication by `sin 2θ`
(`Cert.HkMem_Fstar_sin_open`, applied to `Ψ` resp. to `D_zΨ`), so the linear combination
`(15αF_*(Ψ) + 3α²F_*(D_zΨ))·sin 2θ` is in `ℋ^k`; the transfer to `L₁₂(F)·sin 2θ` is along the
open quadrant, where the two functions agree. -/
theorem HkMem_L12_sin_a1 (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) := by
  have hsin2 : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hHyp.smoothNbhd
  have hDzso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz Ψ) := hΨso.Dz
  have hmemDz : Work.Spaces.HkMem α k (Work.Spaces.Dz Ψ) := HkMem_Dz_a1 α k F Ψ hα hα1 hHyp
  have hF1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (Work.FTS.EllipticEst.Cert.contDiffOn_fstar_of_smoothNbhd Ψ hHyp.smoothNbhd) hsin2
  have hF2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (Work.FTS.EllipticEst.Cert.contDiffOn_fstar_of_smoothNbhd (Work.Spaces.Dz Ψ)
        (smoothNbhd_Dz hHyp.smoothNbhd)) hsin2
  have hM1 : Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Ψ hα hα1 hΨso hHyp.memPsi
  have hM2 : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k (Work.Spaces.Dz Ψ) hα hα1 hDzso hmemDz
  have hgmem : Work.Spaces.HkMem α k (fun z θ =>
      (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + (3 * α ^ 2) * (Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_add_open
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (15 * α) hF1)
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (3 * α ^ 2) hF2)
      (Work.FTS.LocData.HkMem_const_mul α k (15 * α) hM1)
      (Work.FTS.LocData.HkMem_const_mul α k (3 * α ^ 2) hM2)
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.fstar_smooth_of_sol_fts α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol
      hHyp.memF
  have hL12so : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (fun m => Work.FTS.EllipticEst.Cert.L12_contDiffOn_Ioi F hFsm hFint m) hsin2
  refine Work.FTS.EllipticEst.HkMem_agreeOnQ (g := fun z θ =>
      Work.Elliptic.L12 F z * Real.sin (2 * θ)) (f := fun z θ =>
      (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + (3 * α ^ 2) * (Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z * Real.sin (2 * θ)))
    hL12so ?_ hgmem
  intro z θ hz _ _
  change (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + (3 * α ^ 2) * (Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z * Real.sin (2 * θ))
      = Work.Elliptic.L12 F z * Real.sin (2 * θ)
  rw [L12_moment_eq_a1 α k F Ψ hα hα1 hHyp z hz]
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  ring

/-! ## The target -/

theorem Straight_certs (k : ℕ) (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (Work.Spaces.pthIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => Work.Elliptic.Gbar α F z)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) ∧
      Work.Spaces.HkMem α k (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) ∧
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) ∧
      Work.Spaces.HkMem α k (Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) ∧
      Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) := by
  -- ## the certificates
  obtain ⟨hGsing_sm, hGsing_rel, _hGsing_ode⟩ := Gsing_smooth_rel α k F Ψ hα hα1 hHyp
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.fstar_smooth_of_sol_fts α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol
      hHyp.memF
  have hGbar_sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) :=
    fun m => Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α F hα hFsm hFint m
  have hL12_sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    fun m => Work.FTS.EllipticEst.Cert.L12_contDiffOn_Ioi F hFsm hFint m
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- ## smoothness of the pieces
  have hsin2 : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hHyp.smoothNbhd
  have hGsingSo : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := Work.Elliptic.Gsing α F)
      (χ := fun θ : ℝ => Real.sin (2 * θ)) hGsing_sm hsin2
  have hGbarSo : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := Work.Elliptic.Gbar α F)
      (χ := fun θ : ℝ => Real.sin (2 * θ)) hGbar_sm hsin2
  have hL12So : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := Work.Elliptic.L12 F)
      (χ := fun θ : ℝ => Real.sin (2 * θ)) hL12_sm hsin2
  have hShat : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    smoothOpen_add hΨso hGsingSo
  -- ## the membership certificates
  have hmemGbar : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    HkMem_Gbar_sin_a1 α k F Ψ hα hα1 hHyp
  have hmemL12 : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) :=
    HkMem_L12_sin_a1 α k F Ψ hα hα1 hHyp
  have hmemDz : Work.Spaces.HkMem α k (Work.Spaces.Dz Ψ) := HkMem_Dz_a1 α k F Ψ hα hα1 hHyp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `Ψ̂` is `C^∞` on the open quadrant
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hShat
  · -- (2) so is `∂_θθΨ̂`
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      (SmoothOpen_pthIter hShat 2)
  · -- (3) and `z²∂_zzΨ̂`
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((hShat.pzIter 2).zsq_mul)
  · -- (4) `Ḡ·sin 2θ`
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hGbarSo
  · -- (5) `Ḡ`
    exact fun n => Work.FTS.EllipticEst.Cert.contDiffOn_comp_fst_Ioi hGbar_sm n
  · -- (6) `Ψ̂ ∈ ℋ^k`
    have hsum : Work.Spaces.HkMem α k (fun z θ => Ψ z θ
        + Work.Elliptic.Gbar α F z * Real.sin (2 * θ)
        + (-(1 / (4 * α))) * (Work.Elliptic.L12 F z * Real.sin (2 * θ))) :=
      Work.FTS.EllipticEst.HkMem_add_open (smoothOpen_add hΨso hGbarSo)
        (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-(1 / (4 * α))) hL12So)
        (Work.FTS.EllipticEst.HkMem_add_open hΨso hGbarSo hHyp.memPsi hmemGbar)
        (Work.FTS.LocData.HkMem_const_mul α k (-(1 / (4 * α))) hmemL12)
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ hShat ?_ hsum
    intro z θ _ _ _
    simp only [Work.Elliptic.Gsing, Work.Elliptic.Gstar]
    ring
  · -- (7) `∂_θθΨ̂ ∈ ℋ^k`
    have hpt_eq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pthIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          = Work.Spaces.pthIter 2 Ψ z θ
            + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
            + (1 / α) * (Work.Elliptic.L12 F z * Real.sin (2 * θ)) := by
      intro z θ hz hθ0 hθ1
      have hadd := pthIter_add_of_smoothOpen hΨso hGsingSo 2 z θ hz hθ0 hθ1
      have hg : Work.Spaces.pthIter 2
            (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          = -4 * (Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) := by
        simpa using congrFun (congrFun (pthIter_two_radialSin (Work.Elliptic.Gsing α F)) z) θ
      rw [hadd, hg]
      simp only [Work.Elliptic.Gsing, Work.Elliptic.Gstar]
      field_simp
      ring
    have hsum : Work.Spaces.HkMem α k (fun z θ => Work.Spaces.pthIter 2 Ψ z θ
        + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        + (1 / α) * (Work.Elliptic.L12 F z * Real.sin (2 * θ))) :=
      Work.FTS.EllipticEst.HkMem_add_open
        (smoothOpen_add (SmoothOpen_pthIter hΨso 2)
          (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-4) hGbarSo))
        (Work.FTS.EllipticEst.SmoothOpen.const_mul' (1 / α) hL12So)
        (Work.FTS.EllipticEst.HkMem_add_open (SmoothOpen_pthIter hΨso 2)
          (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-4) hGbarSo) hHyp.memDth2
          (Work.FTS.LocData.HkMem_const_mul α k (-4) hmemGbar))
        (Work.FTS.LocData.HkMem_const_mul α k (1 / α) hmemL12)
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ
      (SmoothOpen_pthIter hShat 2) ?_ hsum
    intro z θ hz hθ0 hθ1
    exact (hpt_eq z θ hz hθ0 hθ1).symm
  · -- (8) `∂_θθ (EllResid α F Ψ) ∈ ℋ^k`
    have hsum : Work.Spaces.HkMem α k (fun z θ => Work.Spaces.pthIter 2 Ψ z θ
        + (1 / α) * (Work.Elliptic.L12 F z * Real.sin (2 * θ))) :=
      Work.FTS.EllipticEst.HkMem_add_open (SmoothOpen_pthIter hΨso 2)
        (Work.FTS.EllipticEst.SmoothOpen.const_mul' (1 / α) hL12So) hHyp.memDth2
        (Work.FTS.LocData.HkMem_const_mul α k (1 / α) hmemL12)
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ
      (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter2_EllResid α hα hHyp.smoothNbhd hL12_sm) ?_ hsum
    intro z θ hz hθ0 hθ1
    rw [Work.FTS.EllipticEst.Cert.pthIter2_EllResid_pointwise α hα hHyp.smoothNbhd hz hθ0 hθ1]
    ring
  · -- (9) `D_zΨ̂ ∈ ℋ^k`
    have hDz_eq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          = Work.Spaces.Dz Ψ z θ
            + (-(5 / α)) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
      intro z θ hz hθ0 hθ1
      have hadd := Work.FTS.EllipticEst.SmoothOpen.DzIter_add hΨso hGsingSo 1 z θ hz hθ0 hθ1
      have hg : Work.Spaces.DzIter 1
            (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          = (z * deriv (Work.Elliptic.Gsing α F) z) * Real.sin (2 * θ) := by
        simpa using congrFun (congrFun
          (Work.FTS.EllipticEst.Dz_radialSin (Work.Elliptic.Gsing α F)) z) θ
      have hrel := hGsing_rel z hz
      have h2 : α * (z * deriv (Work.Elliptic.Gsing α F) z)
          = -5 * Work.Elliptic.Gbar α F z := by
        simpa only [mul_assoc] using hrel
      have h3 : z * deriv (Work.Elliptic.Gsing α F) z
          = -(5 / α) * Work.Elliptic.Gbar α F z := by
        have h2' : z * deriv (Work.Elliptic.Gsing α F) z * α
            = -5 * Work.Elliptic.Gbar α F z := by
          rw [mul_comm]; exact h2
        have h4 : z * deriv (Work.Elliptic.Gsing α F) z
            = (-5 * Work.Elliptic.Gbar α F z) / α := (eq_div_iff hα0).mpr h2'
        rw [h4]
        ring
      show Work.Spaces.DzIter 1
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ = _
      rw [hadd, hg, h3, show Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ from rfl]
      ring
    have hsum : Work.Spaces.HkMem α k (fun z θ => Work.Spaces.Dz Ψ z θ
        + (-(5 / α)) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
      Work.FTS.EllipticEst.HkMem_add_open hΨso.Dz
        (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-(5 / α)) hGbarSo) hmemDz
        (Work.FTS.LocData.HkMem_const_mul α k (-(5 / α)) hmemGbar)
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ hShat.Dz ?_ hsum
    intro z θ hz hθ0 hθ1
    exact (hDz_eq z θ hz hθ0 hθ1).symm
  · -- (10) `Ḡ·sin 2θ ∈ ℋ^k`
    exact hmemGbar
  · -- (11) `L₁₂(F)·sin 2θ ∈ ℋ^k`
    exact hmemL12

end Work.FTS.EllipticEst.TT
