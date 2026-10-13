import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS.EllipticEst.RegQ.pth_EllResid_pointwise_smoothQuad
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The slot algebra for `∂_θ(Uop α (EllResid α F Ψ))` in the class `EllHypQ`

Target: for `k ≥ 2`, `0 < α ≤ 1/4`, `EllHypQ α k F Ψ` and `OrthCond`, and every
`(z,θ) ∈ Iz × Iθ`,

`HkIntegrand α k (∂_θ(Uop α W)) z θ ≤ 18·HkIntegrand α k (∂_θW) z θ
   + 2·HkIntegrand α k (α·D_z∂_θW) z θ`,  `W := EllResid α F Ψ = Ψ - (1/(4α))sin 2θ·L₁₂(F)`.

## The mathematics

`Uop α W = -3W - α·D_zW` has coefficients *constant in* `θ`, so on the open quadrant

  `∂_θ(Uop α W) = -3·∂_θW - α·D_z(∂_θW)`,

and the whole content of the statement is the slotwise AM–GM estimate
`(slot of E)² ≤ 18(slot of f)² + 2α²(slot of g)²` for `E := -3f - αg`, `f := ∂_θW`,
`g := D_z∂_θW`.  This is exactly the statement of `RegQ.HkIntegrand_slot_le`
(proved in `RegQ/pthU_slot_alg.lean`), which needs three inputs:

* the pointwise identity above, i.e. `W ∈ C²` on the open quadrant
  (`RegQ.pth_Uop_eq`);
* `f = ∂_θW ∈ C^k` and `g = D_z∂_θW ∈ C^{k-1}` on the open quadrant.

The point of this file is that **these regularity inputs are available in `EllHypQ`**, contrary
to the naive expectation that `W ∈ C^{k+1}` is needed (it is not, and it is false, cf.
`RegQ/NOTES_pthU_EllResid_certs_FALSE.md`).  The reason is the *radial* structure of the
singular part: `W = Ψ - Λ(z)·sin 2θ` with `Λ = (1/(4α))L₁₂(F)`, so

* `∂_θW = ∂_θΨ - 2cos 2θ·Λ(z)` needs only `Λ ∈ C^k`, which follows from
  `L₁₂(F) ∈ C^k` — available from `SmoothOpen F` + `HkMem α k F` via
  `UopHk.contDiffOn_Fstar_of_smoothOpen_Hk` (`F_* ∈ C^{k-1}`) and the fundamental theorem of
  calculus for the tail integral (`UopHk.contDiffOn_L12_of_smoothOpen_Hk`);
* `D_z∂_θW = z(∂_z∂_θΨ - 2cos 2θ·Λ'(z))` needs only `Λ' ∈ C^{k-1}`, i.e. `Λ ∈ C^k` again;
* `W ∈ C^2` needs only `Λ ∈ C²`, which holds since `k ≥ 2`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

variable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## 0. Finite-order smoothness of the partials of a `SmoothQuad` function -/

/-- `∂_θG` is `C^n` on the open quadrant for `G` of class `C^∞` there. -/
theorem contDiffOn_pth_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.LocData.SmoothQuad G) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin Work.FTS.EllipticEst.isOpen_Q0
    ((smoothOpen_of_smoothQuad hG).forall (n + 1))

/-- `∂_z∂_θG` is `C^n` on the open quadrant for `G` of class `C^∞` there. -/
theorem contDiffOn_pz_pth_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.LocData.SmoothQuad G) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth G)))
      Work.FTS.EllipticEst.Q0 :=
  Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0
    (contDiffOn_pth_of_smoothQuad hG (n + 1))

/-! ## 1. The radial regularity of `L₁₂(F)` -/

/-- `L₁₂(F)` is `C^k` on `(0,∞)` for `F` smooth on the open quadrant with `HkMem α k F`
(`k ≥ 2`): its derivative is `-3F_*(z)/z` (`contDiffOn_L12_of_smoothOpen_Hk`), and
`F_* ∈ C^{k-1}` on `(0,∞)` (`contDiffOn_Fstar_of_smoothOpen_Hk`). -/
theorem contDiffOn_L12_of_hyp (hk : 2 ≤ k) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi 0) := by
  obtain ⟨-, hder⟩ := contDiffOn_L12_of_smoothOpen_Hk α k F hF hmem hk
  have hFstar : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem (by omega)
  have hg : ContDiffOn ℝ (k - 1) (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) :=
    (((contDiffOn_const (c := (3 : ℝ))).mul hFstar).div contDiffOn_id
      (fun z hz => ne_of_gt hz)).neg
  have h := contDiffOn_succ_of_hasDerivAt hder hg
  have heq : ((k - 1 : ℕ) : ℕ∞ω) + 1 = ((k : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : k - 1 + 1 = k)
  rwa [heq] at h

/-- The derivative `z ↦ -3F_*(z)/z` of `L₁₂(F)` is `C^{k-1}` on `(0,∞)`. -/
theorem contDiffOn_deriv_L12_of_hyp (hk : 2 ≤ k) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ContDiffOn ℝ (k - 1) (deriv (Work.Elliptic.L12 F)) (Set.Ioi 0) := by
  obtain ⟨-, hder⟩ := contDiffOn_L12_of_smoothOpen_Hk α k F hF hmem hk
  have hFstar : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem (by omega)
  have hg : ContDiffOn ℝ (k - 1) (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) :=
    (((contDiffOn_const (c := (3 : ℝ))).mul hFstar).div contDiffOn_id
      (fun z hz => ne_of_gt hz)).neg
  exact hg.congr (fun z hz => (hder z hz).deriv)

/-! ## 2. The pointwise `z`-derivative of `∂_θ(EllResid α F Ψ)` -/

/-- On the open quadrant,
`∂_z(∂_θW) = ∂_z(∂_θΨ) - 2cos 2θ·Λ'(z)` with `Λ = (1/(4α))L₁₂(F)`, `Λ'(z) = -3F_*(z)/z`. -/
theorem pz_pth_EllResid_eq (hα : 0 < α) (hΨ : Work.FTS.LocData.SmoothQuad Ψ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (hk : 2 ≤ k) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.pth Ψ) z θ
          - (1 / (4 * α)) * (2 * Real.cos (2 * θ))
            * (-(3 * Work.Elliptic.Fstar F z / z)) := by
  intro z θ hz hθ0 hθ1
  obtain ⟨-, hder⟩ := contDiffOn_L12_of_smoothOpen_Hk α k F hF hmem hk
  have hΨsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    (smoothOpen_of_smoothQuad hΨ).forall
  have hpth := (Work.FTS.EllipticEst.RegQ.pth_EllResid_pointwise_smoothQuad α hα F Ψ hΨ).1
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hev : (fun s : ℝ => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) s θ)
      =ᶠ[𝓝 z] (fun s : ℝ => Work.Spaces.pth Ψ s θ
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ))) * Work.Elliptic.L12 F s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    have hs' : -1 < s := by have h := Set.mem_Ioi.mp hs; linarith
    rw [hpth s θ hs' hθ0 hθ1]
  have h1 : DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.pth Ψ s θ) z := by
    have hs : ContDiffOn ℝ k (fun s : ℝ => Work.Spaces.pth Ψ s θ) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin
        (contDiffOn_pth_of_smoothQuad hΨ k) hθmem
    have hs1 : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.pth Ψ s θ) (Set.Ioi 0) :=
      hs.of_le (by exact_mod_cast (by omega : 1 ≤ k))
    exact (hs1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have h2 : DifferentiableAt ℝ (Work.Elliptic.L12 F) z := (hder z hz).differentiableAt
  have hd1 : HasDerivAt (fun s : ℝ => Work.Spaces.pth Ψ s θ)
      (deriv (fun s : ℝ => Work.Spaces.pth Ψ s θ) z) z := h1.hasDerivAt
  have hd2 : HasDerivAt (Work.Elliptic.L12 F) (deriv (Work.Elliptic.L12 F) z) z :=
    (hder z hz).congr_deriv (hder z hz).deriv.symm
  have hd3 : HasDerivAt (fun s : ℝ =>
      ((1 / (4 * α)) * (2 * Real.cos (2 * θ))) * Work.Elliptic.L12 F s)
      (((1 / (4 * α)) * (2 * Real.cos (2 * θ))) * deriv (Work.Elliptic.L12 F) z) z :=
    hd2.const_mul _
  have hfun : (fun s : ℝ => Work.Spaces.pth Ψ s θ
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ))) * Work.Elliptic.L12 F s)
      = ((fun s : ℝ => Work.Spaces.pth Ψ s θ)
          - fun s : ℝ => ((1 / (4 * α)) * (2 * Real.cos (2 * θ)))
              * Work.Elliptic.L12 F s) := by
    funext s
    simp only [Pi.sub_apply]
  have hmain : deriv (fun s : ℝ => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) s θ) z
      = deriv (fun s : ℝ => Work.Spaces.pth Ψ s θ) z
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ))) * deriv (Work.Elliptic.L12 F) z := by
    rw [Filter.EventuallyEq.deriv_eq hev, hfun, (hd1.sub hd3).deriv]
  show deriv (fun s : ℝ => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) s θ) z
      = deriv (fun s : ℝ => Work.Spaces.pth Ψ s θ) z
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ))) * (-(3 * Work.Elliptic.Fstar F z / z))
  rw [hmain, (hder z hz).deriv]

/-! ## 3. The three regularity certificates for the slot algebra -/

/-- `W = EllResid α F Ψ` is `C²` on the open quadrant. -/
theorem resid_contDiffOn_two (hk : 2 ≤ k) (hΨ : Work.FTS.LocData.SmoothQuad Ψ)
    (hL12 : ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi 0)) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Elliptic.EllResid α F Ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hΨsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    (smoothOpen_of_smoothQuad hΨ).forall
  have hL12' : ContDiffOn ℝ 2 (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    hL12.of_le (by exact_mod_cast hk)
  have hfst : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have hsl : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.Elliptic.L12 F p.1)
      Work.FTS.EllipticEst.Q0 :=
    hL12'.comp hfst (fun p hp => by
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod] at hp
      exact hp.1)
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hterm : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      (1 / (4 * α)) * Real.sin (2 * p.2) * Work.Elliptic.L12 F p.1)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := (1 / (4 * α)))).mul hsin).mul hsl
  have hmain : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      Ψ p.1 p.2 - (1 / (4 * α)) * Real.sin (2 * p.2) * Work.Elliptic.L12 F p.1)
      Work.FTS.EllipticEst.Q0 :=
    (hΨsm 2).sub hterm
  exact hmain.congr (fun p _ => rfl)

/-- `∂_θW = ∂_θΨ - 2cos 2θ·Λ(z)` is `C^k` on the open quadrant (from `L₁₂(F) ∈ C^k`). -/
theorem pth_resid_contDiffOn (hα : 0 < α) (hΨ : Work.FTS.LocData.SmoothQuad Ψ)
    (hL12 : ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi 0)) :
    ContDiffOn ℝ k
      (Function.uncurry (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)))
      Work.FTS.EllipticEst.Q0 := by
  have hΨsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    (smoothOpen_of_smoothQuad hΨ).forall
  have hpthΨ : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.pth Ψ))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_pth_of_smoothQuad hΨ k
  have hfst : ContDiffOn ℝ k (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have hsl : ContDiffOn ℝ k (fun p : ℝ × ℝ => Work.Elliptic.L12 F p.1)
      Work.FTS.EllipticEst.Q0 :=
    hL12.comp hfst (fun p hp => by
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod] at hp
      exact hp.1)
  have hcos : ContDiffOn ℝ k (fun p : ℝ × ℝ => (2 : ℝ) * Real.cos (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_const (c := (2 : ℝ)) |>.mul
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd))).contDiffOn
  have hterm : ContDiffOn ℝ k (fun p : ℝ × ℝ =>
      (1 / (4 * α)) * (2 * Real.cos (2 * p.2)) * Work.Elliptic.L12 F p.1)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := (1 / (4 * α)))).mul hcos).mul hsl
  have hmain : ContDiffOn ℝ k (fun p : ℝ × ℝ =>
      Work.Spaces.pth Ψ p.1 p.2
        - (1 / (4 * α)) * (2 * Real.cos (2 * p.2)) * Work.Elliptic.L12 F p.1)
      Work.FTS.EllipticEst.Q0 :=
    hpthΨ.sub hterm
  have hpth := (Work.FTS.EllipticEst.RegQ.pth_EllResid_pointwise_smoothQuad α hα F Ψ hΨ).1
  refine hmain.congr (fun p hp => ?_)
  rw [Work.FTS.EllipticEst.Q0, Set.mem_prod] at hp
  have hz : -1 < p.1 := by have h := Set.mem_Ioi.mp hp.1; linarith
  exact hpth p.1 p.2 hz hp.2.1 hp.2.2

/-- `D_z∂_θW = z(∂_z∂_θΨ - 2cos 2θ·Λ'(z))` is `C^{k-1}` on the open quadrant. -/
theorem Dz_pth_resid_contDiffOn (hk : 2 ≤ k) (hα : 0 < α)
    (hΨ : Work.FTS.LocData.SmoothQuad Ψ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ContDiffOn ℝ (k - 1)
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ))))
      Work.FTS.EllipticEst.Q0 := by
  have hΨsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    (smoothOpen_of_smoothQuad hΨ).forall
  have hFstar : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem (by omega)
  have hfst : ContDiffOn ℝ (k - 1) (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_fst
  have hFstarp : ContDiffOn ℝ (k - 1) (fun p : ℝ × ℝ => Work.Elliptic.Fstar F p.1)
      Work.FTS.EllipticEst.Q0 :=
    hFstar.comp hfst (fun p hp => by
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod] at hp
      exact hp.1)
  have hq : ContDiffOn ℝ (k - 1) (fun p : ℝ × ℝ => -(3 * Work.Elliptic.Fstar F p.1 / p.1))
      Work.FTS.EllipticEst.Q0 :=
    (((contDiffOn_const (c := (3 : ℝ))).mul hFstarp).div hfst (fun p hp => by
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod] at hp
      exact ne_of_gt hp.1)).neg
  have hpzpth : ContDiffOn ℝ (k - 1)
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth Ψ))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_pz_pth_of_smoothQuad hΨ (k - 1)
  have hcos : ContDiffOn ℝ (k - 1) (fun p : ℝ × ℝ => (2 : ℝ) * Real.cos (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_const (c := (2 : ℝ)) |>.mul
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd))).contDiffOn
  have hmain : ContDiffOn ℝ (k - 1) (fun p : ℝ × ℝ => p.1 *
      (Work.Spaces.pz (Work.Spaces.pth Ψ) p.1 p.2
        - (1 / (4 * α)) * (2 * Real.cos (2 * p.2))
          * (-(3 * Work.Elliptic.Fstar F p.1 / p.1)))) Work.FTS.EllipticEst.Q0 :=
    hfst.mul (hpzpth.sub
      (((contDiffOn_const (c := (1 / (4 * α)))).mul hcos).mul hq))
  have hpe := pz_pth_EllResid_eq (k := k) hα hΨ hF hmem hk
  refine hmain.congr (fun p hp => ?_)
  rw [Work.FTS.EllipticEst.Q0, Set.mem_prod] at hp
  have hz : 0 < p.1 := hp.1
  have hθ0 : 0 < p.2 := hp.2.1
  have hθ1 : p.2 < Real.pi / 2 := hp.2.2
  change Work.Spaces.Dz (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) p.1 p.2 = _
  rw [Work.Spaces.Dz, hpe p.1 p.2 hz hθ0 hθ1]

/-! ## 4. The target -/

theorem slot_algebra : ∀ k : ℕ, 2 ≤ k → ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.EllHypQ α k F Ψ →
    Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k
          (Work.Spaces.pth (Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α F Ψ))) z θ
        ≤ 18 * Work.Spaces.HkIntegrand α k (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ
          + 2 * Work.Spaces.HkIntegrand α k (fun z θ =>
              α * Work.Spaces.Dz (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ) z θ := by
  intro k hk α F Ψ hα hα4 hHyp hOrth z hz θ hθ
  have hFopen : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_of_smoothQuad hHyp.quadF
  have hmemF : Work.Spaces.HkMem α k F := hHyp.regF.2.1
  have hL12 : ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    contDiffOn_L12_of_hyp (α := α) hk hFopen hmemF
  have hW2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Elliptic.EllResid α F Ψ))
      Work.FTS.EllipticEst.Q0 :=
    resid_contDiffOn_two (k := k) (α := α) hk hHyp.quadPsi hL12
  have hf : ContDiffOn ℝ k
      (Function.uncurry (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)))
      Work.FTS.EllipticEst.Q0 :=
    pth_resid_contDiffOn (k := k) (α := α) hα hHyp.quadPsi hL12
  have hg : ContDiffOn ℝ (k - 1)
      (Function.uncurry
        (Work.Spaces.Dz (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ))))
      Work.FTS.EllipticEst.Q0 :=
    Dz_pth_resid_contDiffOn (k := k) (α := α) hk hα hHyp.quadPsi hFopen hmemF
  exact Work.FTS.EllipticEst.RegQ.HkIntegrand_slot_le α k
    (Work.FTS.EllipticEst.RegQ.pth_Uop_eq α hW2) hf hg z hz θ hθ

end Work.FTS.EllipticEst.UopHk
