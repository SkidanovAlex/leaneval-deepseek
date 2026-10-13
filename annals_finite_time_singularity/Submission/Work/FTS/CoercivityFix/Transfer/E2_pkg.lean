import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2w
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Transfer.E2_blocks
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.HkMemGam
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.Transfer.GamSmooth
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.E2hat_contDiffOn_three
import Submission.Work.FTS.CoercivityFix.Assembly.E2hat_RegQ
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The package `(ℋ^n, BlocksCont n, BlocksAdd n)` for the `D_z`-defect `E₂ α f`

`E₂ α f = Ê₂ f + Γ(θ)·radS α f z` (`E2_eq`) is a sum of two functions with *different*
regularity:

* `Ê₂ f` is `C^∞` on the open quadrant (`AuxE2.E2hat_contDiffOn_three`), and its `ℋ^n`-membership
  descends from `RegQ α (n+1) f` (`Assembly.E2hat_RegQ`);
* `Γ(θ)·radS α f z` is only `C³` there (`E2pkg.radS_contDiffOn_three`) but *separates* into an
  angular and a radial factor, so its `ℋ^n`-membership for `n ≤ 3` is
  `E2pkg.HkMem_gam_rad`.

The block continuity `BlocksCont n (E₂ α f)` is the sibling `E2_blocks`; the block additivity
`BlocksAdd n (𝓛̂(D_z f)) (E₂ α f)` follows from the `C^n`-regularity of both functions on the
open quadrant (`E2pkg.blocksAdd_of_contDiffOn`). -/

/-- `𝓛̂(D_z f)` is `C^∞` on the open quadrant for a `SmoothQuad` datum.  (The proof is the
`D_z`-analogue of `E1Parts.contDiffOn_uncurry_Lhat_Dth`.) -/
theorem contDiffOn_uncurry_Lhat_Dz {f : Fn} (hsm : Work.FTS.LocData.SmoothQuad f) {n : ℕ} :
    ContDiffOn ℝ n (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)))
      E2pkg.Qd := by
  have hV : IsOpen E2pkg.Qd := E2pkg.isOpen_Qd
  have hsub : E2pkg.Qd ⊆ Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    refine ⟨?_, hp.2⟩
    have h : (0 : ℝ) < p.1 := hp.1
    exact Set.mem_Ioi.mpr (by linarith)
  have hfQ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) E2pkg.Qd :=
    hsm.mono hsub
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dz f)) E2pkg.Qd :=
    Work.FTS.LocData.contDiffOn_Dz hV hfQ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz f))) E2pkg.Qd :=
    Work.FTS.LocData.contDiffOn_pz hV h1
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f))) E2pkg.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV h1
  have hne : ∀ p ∈ E2pkg.Qd, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp
    have : (0 : ℝ) < p.1 := hp.1
    linarith
  have hmain : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))) E2pkg.Qd := by
    have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz f) p
          + p.1 * Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz f)) p
          - 2 * Function.uncurry (Work.Spaces.Dz f) p / (1 + p.1)
          - 3 * Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f)) p / (1 + p.1) := by
      funext p
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      rw [Work.FTS.CoercivityFix.Lhat_eq]
      simp only [Work.Spaces.Dz]
    rw [hfun]
    exact (((h1.add (contDiffOn_fst.mul h2)).sub
        ((contDiffOn_const.mul h1).div (contDiffOn_const.add contDiffOn_fst) hne)).sub
      ((contDiffOn_const.mul h3).div (contDiffOn_const.add contDiffOn_fst) hne))
  exact hmain.of_le (WithTop.coe_le_coe.mpr le_top)

/-- `E₂ α f` is `C^n` on the open quadrant for `CoerAdm α f` and `n ≤ 3`. -/
theorem contDiffOn_uncurry_E2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {n : ℕ} (hn : n ≤ 3) :
    ContDiffOn ℝ n (Function.uncurry (E2 α f)) E2pkg.Qd := by
  have hA : ContDiffOn ℝ 4 (fun z : ℝ => Work.Coercivity.L12f f z) (Set.Ioi 0) :=
    AuxE2.L12_contDiffOn_four_of_five α hα hα1 hf.reg.1 hf.reg.2.1 hf.l12
  have hradS : ContDiffOn ℝ 3 (fun z : ℝ => radS α f z) (Set.Ioi 0) :=
    AuxE2.radS_contDiffOn_three α hα hα1 hA
  have hE2hat : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2) E2pkg.Qd :=
    AuxE2.E2hat_contDiffOn_three hf.reg.1
  have hGR : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 * radS α f p.1) E2pkg.Qd :=
    (contDiffOn_Gam_Qd α 3).mul
      (hradS.comp contDiffOn_fst (fun p hp => hp.1))
  have hsum : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      Work.FTS.CoercivityFix.E2hat f p.1 p.2 + Work.Spaces.Gam α p.2 * radS α f p.1)
      E2pkg.Qd := hE2hat.add hGR
  have hfun : Function.uncurry (E2 α f)
      = fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2
          + Work.Spaces.Gam α p.2 * radS α f p.1 := by
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  rw [hfun]
  exact hsum.of_le (by exact_mod_cast hn)

/-- **The `E₂`-package**: the `D_z`-defect of the transfer lies in `ℋ^n`, has continuous blocks
and its blocks are additive against those of `𝓛̂(D_z f)`, for every `n ≤ 3`. -/
theorem E2_pkg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) :
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.CoerAdm α f →
      Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E2 α f) ∧
      Work.FTS.CoercivityFix.Assembly.BlocksCont n (Work.FTS.CoercivityFix.Transfer.E2 α f) ∧
      Work.FTS.CoercivityFix.Assembly.BlocksAdd n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
        (Work.FTS.CoercivityFix.Transfer.E2 α f) := by
  intro f hf
  have hE2hatC : ContDiffOn ℝ n (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
      E2pkg.Qd :=
    (AuxE2.E2hat_contDiffOn_three hf.reg.1).of_le (by exact_mod_cast hn)
  have hGRC : ContDiffOn ℝ n
      (Function.uncurry (fun z θ => Work.Spaces.Gam α θ * radS α f z)) E2pkg.Qd :=
    E2pkg.contDiffOn_uncurry_gam_rad α hα hα1 hf hn
  have hmE2hat : Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.E2hat f) :=
    (Work.FTS.CoercivityFix.Assembly.E2hat_RegQ α hα
      (Work.FTS.CoercivityFix.Assembly.regQ_mono (by omega) hf.reg)).2.1
  have hmGR : Work.Spaces.HkMem α n
      (fun z θ => Work.Spaces.Gam α θ * radS α f z) :=
    E2pkg.HkMem_gam_rad α hα hα1 hf hn
  have hsplit : Work.FTS.CoercivityFix.Transfer.E2 α f
      = Work.FTS.CoercivityFix.E2hat f
        + (fun z θ => Work.Spaces.Gam α θ * radS α f z) := by
    funext z θ
    rfl
  refine ⟨?_, E2_blocks α hα hα1 n hn f hf, ?_⟩
  · rw [hsplit]
    exact E2pkg.hkMem_add_of_contDiffOn α n hE2hatC hGRC hmE2hat hmGR
  · exact E2pkg.blocksAdd_of_contDiffOn
      (contDiffOn_uncurry_Lhat_Dz hf.reg.1)
      (contDiffOn_uncurry_E2 α hα hα1 hf hn)

end Work.FTS.CoercivityFix.Transfer
