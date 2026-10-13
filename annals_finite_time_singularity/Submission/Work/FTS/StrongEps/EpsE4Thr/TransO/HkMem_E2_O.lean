import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2_pkg
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSBase
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSFinal
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.gam_rad_package_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.E2hat_mem_contDiff_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.C0_sq_le_HkSq0_O
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkMem_E2_O` — the `D_z`-defect `E₂ α f` is honest in `ℋⁿ` (`n ≤ 3`) on the open class

`E₂ α f = Ê₂ f + Γ(θ)·radS α f z` splits into a part that is controlled by the *closed*-class
argument of `Transfer/E2_pkg.lean` (namely `Ê₂`) and a separated part `Γ(θ)·radS α f z`, whose
`ℋⁿ`-membership for `n ≤ 3` is the open-class package `E2O.gam_rad_package_O` fed by

* `E2O.contDiffOn_four_L12f` — `L₁₂ f ∈ C⁴` on `(0,∞)`;
* `E2O.radS_slotSum_le_O` — integrability of the radial slot sum `∑_{j≤n}(D_z^j radS)²w²`, whose
  only external input is the projector zero-mode bound `(C₀ f)² ≤ 16 |D_θ f|²_{ℋ⁰}`
  (`E2O.C0_sq_le_HkSq0_O`, the Cauchy–Schwarz estimate of `Transfer/E2norm`).

Assembling with the finite-order additivity `E2pkg.hkMem_add_of_contDiffOn` gives the claim.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1000000

/-- The uniform, `α`- and `n`-independent bound for the projector zero mode
`L₁₂(Transport f)(0)` in the open class (a local copy of the private `E2_norm_O.C0_bound_O`):
`(L₁₂(Transport f)(0))² ≤ 16 |D_θ f|²_{ℋⁿ}`. -/
private theorem C0_bound_O_local :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
  refine ⟨16, by norm_num, ?_⟩
  intro α hα hα1 n hn f hO hmem5 hl12
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  have hmemd0 : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f) :=
    Work.FTS.OpenPkg.HkMem_mono_open hO.Dth 0 (by omega) hmemdn
  have h := Work.FTS.StrongEps.EpsE4Thr.E2O.C0_sq_le_HkSq0_O (α := α) hO hmemd0
  have hmono : Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.zero_le n) hmemdn
  have h16 : (16 : ℝ) * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ 16 * Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    mul_le_mul_of_nonneg_left hmono (by norm_num)
  have h' : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := h
  linarith

/-- **The radial slot sum of `radS α f` is integrable on `Iz`**, for `CoerAdmO`-type data and
`n ≤ 3`. -/
private theorem radS_slot_integrable_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (n : ℕ)
    (hn : n ≤ 3) (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  obtain ⟨_C, _hCpos, hradS⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.E2O.radS_slotSum_le_O C0_bound_O_local
  exact (hradS α hα hα1 n hn f hO hmem5 hl12).1

theorem HkMem_E2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E2 α f) := by
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hl12 : Work.Construction.L12 f 0 = 0 := hf.2.2.2
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO n (by omega) hmem5
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  -- the `C^∞`-on-the-open-quadrant data of the two blocks
  have hslot : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    radS_slot_integrable_O α hα hα1 n hn hO hmem5 hl12
  have hA : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EpsE4Thr.E2O.contDiffOn_four_L12f α hα hα1 hO hmem5
  have hgam := Work.FTS.StrongEps.EpsE4Thr.E2O.gam_rad_package_O α hα hα1 hn hA hslot
  have hE2hat := Work.FTS.StrongEps.EpsE4Thr.E2O.E2hat_mem_contDiff_O α hα (by omega : n ≤ 4)
    hO hmemn hmemdn
  -- the split `E₂ α f = Ê₂ f + Γ·radS α f` and the finite-order additivity
  have hsplit : Work.FTS.CoercivityFix.Transfer.E2 α f
      = Work.FTS.CoercivityFix.E2hat f
        + (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := by
    funext z θ
    rfl
  rw [hsplit]
  exact Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α n
    hE2hat.2 hgam.1 hE2hat.1 hgam.2

end Work.FTS.StrongEps.EpsE4Thr.TransO
