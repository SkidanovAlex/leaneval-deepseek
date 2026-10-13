/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Aux/c1_of_locUnif_slots_lip.lean`

**The joint `C¹`-regularity of the level-`5` limit family.**

The extraction of `E5` produces a *family* `F : ℝ → Fn` of profiles, indexed by the fake time
`τ`, together with, at every `τ ∈ [0,T]`,

* the local uniform convergence on the open quadrant `Q0` of every slot `D_z^j D_θ^i`
  (`j + i ≤ 4`) of the `n`-th approximant towards the corresponding slot of `F τ`
  (`ConvLocUnifH6`), and in particular the `C⁴`-regularity of `F τ`;
* a `τ`-Lipschitz bound for the slots of order `≤ 1` of the approximants, uniform in `n` and
  locally uniform on `Q0`;
* the pointwise identification `∂_τ (F τ z θ) = W τ z θ` on the quadrant, with `W` jointly
  continuous on `(0,∞) × (0,π/2) × (0,T)`.

The theorem below shows that the *uncurried* family `(z,θ,τ) ↦ F τ z θ` is then `C¹` on
`(0,∞) × (0,π/2) × (0,T)`.  The point is that the two spatial slots of the limit inherit the
`τ`-Lipschitz bound (a locally uniform limit of Lipschitz functions is Lipschitz) and are
therefore *jointly* continuous in `(z,θ,τ)`, while the `τ`-derivative is `W` — so the whole
Fr´echet derivative is continuous and the `C¹`-criterion
`contDiffOn_succ_iff_fderiv_of_isOpen` applies.

## Structure of the file

* `clmHead` (`C1LocUnifAux.lean`, imported): the continuous linear map
  `(x,y) ↦ a x + L y` on `ℝ × E`, the carrier of the assembled derivative;
* `abs_sub_sub_mul_le.lean` (imported): the quantitative one-variable mean value bound;
* `hasDerivAt_of_fst_snd.lean` (imported): *two directional derivatives with continuous
  derivatives imply Fréchet differentiability*;
* `slot_lip_limit.lean`, `slot_joint_cont.lean` (imported): the `τ`-Lipschitz bound of the limit
  family and the joint continuity of its order-`≤1` slots;
* `hasDerivAt_uncurry_slice_z` / `hasDerivAt_uncurry_slice_th` below: the slices of a
  differentiable two-variable function have the expected one-variable derivatives;
* `c1_of_locUnif_slots_lip`: the theorem, assembled from the pieces above.
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.ConvLev0Defs
import Submission.Work.FTS.StrongEps.EpsSlotLipP
import Submission.Work.FTS.StrongEps.E5Aux.clmPairAPI
import Submission.Work.FTS.StrongEps.E5Aux.C1LocUnifAux
import Submission.Work.FTS.StrongEps.E5Aux.abs_sub_sub_mul_le
import Submission.Work.FTS.StrongEps.E5Aux.hasFDerivAt_of_fst_snd
import Submission.Work.FTS.StrongEps.E5Aux.slot_lip_limit
import Submission.Work.FTS.StrongEps.E5Aux.slot_joint_cont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Slice derivatives of a differentiable two-variable function -/

/-- The `z`-slice of a differentiable two-variable function has derivative `∂_z`. -/
theorem hasDerivAt_uncurry_slice_z {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    HasDerivAt (fun s : ℝ => f s θ) (Work.Spaces.pz f z θ) z := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  have hd := h.hasFDerivAt.comp_hasDerivAt z hcurve
  rw [Work.Spaces.pz_eq_fderiv h]
  exact hd

/-- The `θ`-slice of a differentiable two-variable function has derivative `∂_θ`. -/
theorem hasDerivAt_uncurry_slice_th {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    HasDerivAt (fun t : ℝ => f z t) (Work.Spaces.pth f z θ) θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hd := h.hasFDerivAt.comp_hasDerivAt θ hcurve
  rw [Work.Spaces.pth_eq_fderiv h]
  exact hd

/-- `toSpanSingleton` is the scalar multiple of the identity: this is the bridge between the
`HasDerivAt`-form (whose Fréchet derivative is a `toSpanSingleton`) and `clmPair`. -/
theorem toSpanSingleton_eq_smul_one (b : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ b = (b • (1 : ℝ →L[ℝ] ℝ)) := by
  refine ContinuousLinearMap.ext fun c => ?_
  rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smul_apply]
  simp [smul_eq_mul, mul_comm]

/-- `clmHead` in the one-dimensional second slot is `clmPair`. -/
theorem clmHead_smul_one (a b : ℝ) :
    clmHead ℝ a ((b • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ) = clmPair (a, b) :=
  clmHead_eq_clmPair a b

/-- `clmHead` with a `toSpanSingleton` second slot is `clmPair`. -/
theorem clmHead_toSpanSingleton (a b : ℝ) :
    clmHead ℝ a (ContinuousLinearMap.toSpanSingleton ℝ b) = clmPair (a, b) := by
  rw [toSpanSingleton_eq_smul_one, clmHead_smul_one]

/-! ## The theorem -/

theorem c1_of_locUnif_slots_lip {G : ℕ → Work.FTS.Galerkin.Fam} {F : ℝ → Work.FTS.Galerkin.Fn}
    {W : ℝ → Work.FTS.Galerkin.Fn} {α B T : ℝ}
    (hT : 0 < T)
    (hconv : ∀ τ ∈ Set.Icc 0 T,
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2|
            ≤ C * |τ - τ'|)
    (hW : ∀ τ ∈ Set.Icc 0 T, ∀ p ∈ Work.Construction.Qd,
      HasDerivWithinAt (fun s => F s p.1 p.2) (W τ p.1 p.2) (Set.Icc 0 T) τ)
    (hWc : ContinuousOn (fun p : ℝ × ℝ × ℝ => W p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T) := by
  set U : Set (ℝ × ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T with hU
  set A : ℝ × ℝ × ℝ → ℝ := (fun p : ℝ × ℝ × ℝ => F p.2.2 p.1 p.2.1) with hA
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hmemU : ∀ q : ℝ × ℝ × ℝ, q ∈ U →
      0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2 ∧ 0 < q.2.2 ∧ q.2.2 < T := by
    intro q hq
    rw [hU] at hq
    exact ⟨hq.1, hq.2.1.1, hq.2.1.2, hq.2.2.1, hq.2.2.2⟩
  have hQ0 : ∀ q : ℝ × ℝ × ℝ, q ∈ U → (q.1, q.2.1) ∈ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    have h := hmemU q hq
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h.1, h.2.1, h.2.2.1⟩
  have hUsub : U ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T := by
    intro q hq
    have h := hmemU q hq
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
    exact ⟨h.1, ⟨⟨h.2.1, h.2.2.1⟩, le_of_lt h.2.2.2.1, le_of_lt h.2.2.2.2⟩⟩
  -- (1) the slices are `C⁴`
  have hsm : ∀ τ ∈ Set.Icc 0 T,
      ContDiffOn ℝ 4 (Function.uncurry (F τ)) Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => (hconv τ hτ).2.1
  -- (2) the limit slots are Lipschitz in `τ`
  have hlipF := slot_lip_limit (G := G) (F := F) (α := α) (B := B) (T := T) hconv hlip
  -- (3) joint continuity of the slots of the limit
  have hslot := slot_joint_cont (F := F) (T := T) hsm hlipF
  -- (4) continuity of the partial derivatives on `U`
  have hmix10 : ∀ q : ℝ × ℝ × ℝ, Work.Spaces.mixed 1 0 (F q.2.2) q.1 q.2.1
      = q.1 * Work.Spaces.pz (F q.2.2) q.1 q.2.1 := fun q => rfl
  have hmix01 : ∀ q : ℝ × ℝ × ℝ, Work.Spaces.mixed 0 1 (F q.2.2) q.1 q.2.1
      = Real.sin (2 * q.2.1) * Work.Spaces.pth (F q.2.2) q.1 q.2.1 := fun q => rfl
  have hz0 : ∀ q ∈ U, q.1 ≠ 0 := fun q hq => ne_of_gt (hmemU q hq).1
  have hs0 : ∀ q ∈ U, Real.sin (2 * q.2.1) ≠ 0 := by
    intro q hq
    have h := hmemU q hq
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hpz_cont : ContinuousOn (fun q : ℝ × ℝ × ℝ => Work.Spaces.pz (F q.2.2) q.1 q.2.1) U := by
    have h10 : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed 1 0 (F q.2.2) q.1 q.2.1) U :=
      (hslot 1 0 (by norm_num)).mono hUsub
    have hz : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.1) U := continuous_fst.continuousOn
    refine (h10.div hz hz0).congr fun q hq => ?_
    change Work.Spaces.pz (F q.2.2) q.1 q.2.1
      = Work.Spaces.mixed 1 0 (F q.2.2) q.1 q.2.1 / q.1
    rw [hmix10 q, mul_div_cancel_left₀ _ (hz0 q hq)]
  have hpth_cont : ContinuousOn (fun q : ℝ × ℝ × ℝ => Work.Spaces.pth (F q.2.2) q.1 q.2.1) U := by
    have h01 : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed 0 1 (F q.2.2) q.1 q.2.1) U :=
      (hslot 0 1 (by norm_num)).mono hUsub
    have hs : ContinuousOn (fun q : ℝ × ℝ × ℝ => Real.sin (2 * q.2.1)) U :=
      (Real.continuous_sin.comp (continuous_const.mul
        (continuous_fst.comp continuous_snd))).continuousOn
    refine (h01.div hs hs0).congr fun q hq => ?_
    change Work.Spaces.pth (F q.2.2) q.1 q.2.1
      = Work.Spaces.mixed 0 1 (F q.2.2) q.1 q.2.1 / Real.sin (2 * q.2.1)
    rw [hmix01 q, mul_div_cancel_left₀ _ (hs0 q hq)]
  have hW_cont : ContinuousOn (fun q : ℝ × ℝ × ℝ => W q.2.2 q.1 q.2.1) U := hWc
  -- (5) slice derivatives
  have hsliceθ : ∀ τ ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun t : ℝ => F τ z t) (Work.Spaces.pth (F τ) z θ) θ := by
    intro τ hτ z θ hQ
    have hd : DifferentiableAt ℝ (Function.uncurry (F τ)) (z, θ) :=
      ((hsm τ hτ).differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
    exact hasDerivAt_uncurry_slice_th hd
  have hslicez : ∀ τ ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun s : ℝ => F τ s θ) (Work.Spaces.pz (F τ) z θ) z := by
    intro τ hτ z θ hQ
    have hd : DifferentiableAt ℝ (Function.uncurry (F τ)) (z, θ) :=
      ((hsm τ hτ).differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
    exact hasDerivAt_uncurry_slice_z hd
  have hsliceτ : ∀ τ ∈ Set.Ioo 0 T, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s : ℝ => F s z θ) (W τ z θ) τ := by
    intro τ hτ z θ hQ
    exact (hW τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩ (z, θ) hQ).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)
  -- (6) the inner Fréchet derivative: differentiation in `(θ, τ)` at fixed `z`
  have hinner : ∀ (z θ τ : ℝ), 0 < z →
      (θ, τ) ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T →
      HasFDerivAt (fun y : ℝ × ℝ => F y.2 z y.1)
        (clmPair (Work.Spaces.pth (F τ) z θ, W τ z θ)) (θ, τ) := by
    intro z θ τ hz hmem
    have hV : IsOpen (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) :=
      isOpen_Ioo.prod isOpen_Ioo
    have hp : (θ, τ) ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T := hmem
    have h₁ : ∀ q ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T,
        HasDerivAt (fun x : ℝ => F q.2 z x) (Work.Spaces.pth (F q.2) z q.1) q.1 := by
      intro q hq
      exact hsliceθ q.2 ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩ z q.1
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hq.1.1, hq.1.2⟩)
    have h₂ : ∀ q ∈ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T,
        HasFDerivAt (fun y : ℝ => F y z q.1) ((W q.2 z q.1) • (1 : ℝ →L[ℝ] ℝ)) q.2 := by
      intro q hq
      have hd := hsliceτ q.2 hq.2 z q.1 ⟨hz, hq.1.1, hq.1.2⟩
      rw [← toSpanSingleton_eq_smul_one]
      exact hd.hasFDerivAt
    have hmap : Set.MapsTo (fun q : ℝ × ℝ => (z, q.1, q.2))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) U := by
      intro q hq
      have h1 : 0 < q.1 := hq.1.1
      have h2 : q.1 < Real.pi / 2 := hq.1.2
      have h3 : 0 < q.2 := hq.2.1
      have h4 : q.2 < T := hq.2.2
      rw [hU]
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      tauto
    have hcont2 : Continuous (fun q : ℝ × ℝ => (z, q.1, q.2)) :=
      (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
    have hc₁ : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pth (F q.2) z q.1)
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) :=
      hpth_cont.comp hcont2.continuousOn hmap
    have hc₂ : ContinuousOn (fun q : ℝ × ℝ => (W q.2 z q.1) • (1 : ℝ →L[ℝ] ℝ))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) :=
      (hW_cont.comp hcont2.continuousOn hmap).smul continuousOn_const
    have hmain : HasFDerivAt (fun y : ℝ × ℝ => F y.2 z y.1)
        (clmHead ℝ (Work.Spaces.pth (F τ) z θ)
          ((W τ z θ) • (1 : ℝ →L[ℝ] ℝ))) (θ, τ) :=
      hasFDerivAt_of_fst_snd (E := ℝ)
        (f := fun q : ℝ × ℝ => F q.2 z q.1)
        (g₁ := fun q : ℝ × ℝ => Work.Spaces.pth (F q.2) z q.1)
        (g₂ := fun q : ℝ × ℝ => (W q.2 z q.1) • (1 : ℝ →L[ℝ] ℝ))
        hV hp h₁ h₂ hc₁ hc₂
    rw [clmHead_smul_one] at hmain
    exact hmain
  -- (7) the outer Fréchet derivative
  have hderiv : ∀ p ∈ U, HasFDerivAt A (clmHead (ℝ × ℝ)
      (Work.Spaces.pz (F p.2.2) p.1 p.2.1)
      (clmPair (Work.Spaces.pth (F p.2.2) p.1 p.2.1, W p.2.2 p.1 p.2.1))) p := by
    intro p hp
    refine hasFDerivAt_of_fst_snd (E := ℝ × ℝ) (f := A)
      (g₁ := fun q : ℝ × ℝ × ℝ => Work.Spaces.pz (F q.2.2) q.1 q.2.1)
      (g₂ := fun q : ℝ × ℝ × ℝ =>
        clmPair (Work.Spaces.pth (F q.2.2) q.1 q.2.1, W q.2.2 q.1 q.2.1))
      hUopen hp ?_ ?_ hpz_cont ?_
    · intro q hq
      have h := hmemU q hq
      exact hslicez q.2.2 ⟨le_of_lt h.2.2.2.1, le_of_lt h.2.2.2.2⟩ q.1 q.2.1
        (hQ0 q hq)
    · intro q hq
      have h := hmemU q hq
      refine hinner q.1 q.2.1 q.2.2 h.1 ?_
      simp only [Set.mem_prod, Set.mem_Ioo]
      exact ⟨⟨h.2.1, h.2.2.1⟩, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩
    · have hpair : ContinuousOn (fun q : ℝ × ℝ × ℝ =>
          (Work.Spaces.pth (F q.2.2) q.1 q.2.1, W q.2.2 q.1 q.2.1)) U :=
        hpth_cont.prodMk hW_cont
      exact clmPair.continuous.comp_continuousOn hpair
  -- (8) assemble `C¹`
  have hdiff : DifferentiableOn ℝ A U := fun p hp =>
    (hderiv p hp).differentiableAt.differentiableWithinAt
  have hfdc : ContinuousOn (fun p : ℝ × ℝ × ℝ => fderiv ℝ A p) U := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        (Work.Spaces.pz (F p.2.2) p.1 p.2.1,
          clmPair (Work.Spaces.pth (F p.2.2) p.1 p.2.1, W p.2.2 p.1 p.2.1))) U :=
      hpz_cont.prodMk (clmPair.continuous.comp_continuousOn (hpth_cont.prodMk hW_cont))
    have h2 := (clmHeadL (ℝ × ℝ)).continuous.comp_continuousOn h1
    refine h2.congr fun p hp => ?_
    rw [(hderiv p hp).fderiv]
    rfl
  have key : ContDiffOn ℝ (1 : ℕ∞ω) A U := by
    rw [show (1 : ℕ∞ω) = (0 : ℕ∞ω) + 1 from by norm_num]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hUopen).mpr ⟨hdiff, ?_, ?_⟩
    · intro h
      exact absurd h (by norm_num)
    · rw [contDiffOn_zero]
      exact hfdc
  exact key

end Work.FTS.StrongEps.E5Aux
