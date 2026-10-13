/-
# `Transfer/E1_blocks` — block continuity of the `D_θ`-defect `E1 α f`

The transfer defect `E1 α f = (sin 2θ · Γ'(θ)) · radA α f z` (`Transfer/Profiles.lean`) is a
*separated product*: an angular factor `B(θ) = sin 2θ · Γ'(θ)` times a radial factor
`R(z) = radA α f z`.  `Assembly.Comm2w` consumes exactly `Assembly.BlocksCont n (E1 α f)`,
continuity of every mixed block `D_z^bD_θ^a (E1 α f)`, `a + b ≤ n`, on the open quadrant — the
weakened replacement for the refuted `RegQ α n (E1 α f)` (whose `SmoothQuad` conjunct fails
because `L₁₂ f` is not smooth through `z = 0`).

The angular factor is `C^∞` on `(0,π/2)` (it is `D_θ Γ`, and `Γ(θ) = (sinθcos²θ)^{α/3}` is
`C^∞` where `sinθcos²θ > 0`), while the radial factor `R = radA α f` involves `L₁₂ f`, which is
`C³` on `(0,∞)` for `SmoothQuad f` with `HkMem α 4 f` (`L12f_contDiffOn`).  Hence `E1 α f` is
jointly `C³` on the open quadrant and all its blocks are continuous there.

Since `a + b ≤ n ≤ 3` only the two factors' `C³`-regularity (on the respective open intervals)
is used, and everything reduces to continuity of a product of two separately continuous
functions on the product of the two open sets.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2w
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Core2
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.Spaces.c_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn
import Submission.Work.FTS.CoercivityFix.Transfer.BlocksCont_mul_factor

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

/-! ## `BlocksCont` is monotone in the order -/

/-- `BlocksCont j g` follows from `BlocksCont k g` for `j ≤ k` (fewer blocks to control). -/
theorem blocksCont_mono {j k : ℕ} (hjk : j ≤ k) {g : Fn}
    (h : Work.FTS.CoercivityFix.Assembly.BlocksCont k g) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont j g :=
  fun a b hab => h a b (le_trans hab hjk)

/-! ## The radial factor `radA α f` is `C³` -/

/-- `ampA α = fun z => 2z/(c(1+z)²)` is `C³` on `(0,∞)` (`c α ≥ 1/10 > 0`). -/
theorem contDiffOn_ampA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 3 (ampA α) (Set.Ioi 0) := by
  have hcne : Work.Spaces.c α ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (Work.Spaces.c_bounds α hα hα1).1)
  have hnum : ContDiffOn ℝ 3 (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ 3 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact mul_ne_zero hcne (pow_ne_zero 2 (by linarith))
  show ContDiffOn ℝ 3 (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) (Set.Ioi 0)
  exact hnum.div hden hne

/-- `ampB α = fun z => 2z²/(1+z)³` is `C³` on `(0,∞)`. -/
theorem contDiffOn_ampB (α : ℝ) :
    ContDiffOn ℝ 3 (ampB α) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ 3 (fun z : ℝ => 2 * z ^ 2) (Set.Ioi 0) :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hden : ContDiffOn ℝ 3 (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact pow_ne_zero 3 (by linarith)
  show ContDiffOn ℝ 3 (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi 0)
  exact hnum.div hden hne

/-- **The radial profile `radA α f` is `C³` on `(0,∞)`** as soon as `L₁₂ f` is.  Indeed
`radA α f z = -(2z/(c(1+z)²))·L₁₂ f(z) + (2z²/((1+z)³c))·L₁₂(Transport f)(0)`, a sum of a
product of a rational function with `L₁₂ f` and a rational function times a constant. -/
theorem radA_contDiffOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : Fn)
    (h12 : ContDiffOn ℝ 3 (Work.Coercivity.L12f f) (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (radA α f) (Set.Ioi 0) := by
  have hA := contDiffOn_ampA α hα hα1
  have hB := contDiffOn_ampB α
  have hconst : ContDiffOn ℝ 3
      (fun _ : ℝ => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi 0) :=
    contDiffOn_const
  have hmain : ContDiffOn ℝ 3 (fun z : ℝ =>
      -(ampA α z) * Work.Coercivity.L12f f z
        + (ampB α z / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi 0) :=
    (hA.neg.mul h12).add ((hB.div_const (Work.Spaces.c α)).mul hconst)
  refine hmain.congr (fun z _ => ?_)
  simp only [radA]

/-! ## The angular factor `B(θ) = sin 2θ · Γ'(θ)` is `C^∞` on `(0,π/2)` -/

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on `(0,π/2)`: there `sinθ·cos²θ > 0` and the real
power map is `C^∞` on `(0,∞)`. -/
theorem Gam_contDiffOn_infty (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.Spaces.Gam α) (Set.Ioo 0 (π / 2)) := by
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) := by
    fun_prop
  refine (hbase.rpow_const_of_ne (p := α / 3) ?_).congr (fun θ _ => rfl)
  intro θ hθ
  have h1 : (0 : ℝ) < θ := hθ.1
  have h2 : θ < π / 2 := hθ.2
  exact mul_ne_zero
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [h2, Real.pi_pos])))
    (pow_ne_zero 2 (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩)))

/-- **The angular factor is `C³` on `(0,π/2)`.**  It is `D_θ Γ` (the `z`-independent function),
which is `C^∞` there because `Γ` is. -/
theorem sinGam_contDiffOn_Ioo (α : ℝ) :
    ContDiffOn ℝ 3 (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (Set.Ioo 0 (π / 2)) := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hG : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun _ : ℝ => Work.Spaces.Gam α))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (Gam_contDiffOn_infty α).comp contDiffOn_snd (fun p hp => hp.2)
  have hD := Work.FTS.LocData.contDiffOn_Dth hV hG
  have hslice := Work.FTS.LocData.contDiffOn_slice_θ hD (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
  refine hslice.of_le (by simp) |>.congr (fun θ _ => ?_)
  simp only [Work.Spaces.Dth, Work.Spaces.pth]

/-- **The assembly of `E1_blocks`**, with the two analytic inputs as explicit hypotheses:

* `hA` — `C³`-regularity of `L₁₂ g` on `(0,∞)` for `SmoothQuad g` with `HkMem β 4 g`
  (the colleague's lemma `L12f_contDiffOn`);
* `hB` — block continuity of a separated product `B(θ)·R(z)` from `C³`-regularity of the two
  factors on their respective open intervals (the colleague's lemma `BlocksCont_mul_factor`).

Everything else is bookkeeping: `CoerAdm α f` gives `SmoothQuad f` and `HkMem α 5 f`, hence
`HkMem α 4 f`; `radA α f` is `C³` (`radA_contDiffOn`); the angular factor `sin 2θ·Γ'(θ)` is `C³`
on `(0,π/2)` (`sinGam_contDiffOn_Ioo`); and `E1 α f` is by definition the product of the two. -/
theorem E1_blocks_aux
    (hA : ∀ (β : ℝ), 0 < β → β ≤ 1 → ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem β 4 g →
      ContDiffOn ℝ 3 (Work.Coercivity.L12f g) (Set.Ioi 0))
    (hB : ∀ B R : ℝ → ℝ, ContDiffOn ℝ 3 B (Set.Ioo 0 (π / 2)) →
      ContDiffOn ℝ 3 R (Set.Ioi 0) →
      Work.FTS.CoercivityFix.Assembly.BlocksCont 3 (fun z θ : ℝ => B θ * R z))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) :
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.CoerAdm α f →
      Work.FTS.CoercivityFix.Assembly.BlocksCont n (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  intro f hf
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.reg.2.1
  have hmem4 : Work.Spaces.HkMem α 4 f := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  have h12 : ContDiffOn ℝ 3 (Work.Coercivity.L12f f) (Set.Ioi 0) := hA α hα hα1 f hsm hmem4
  have hR : ContDiffOn ℝ 3 (radA α f) (Set.Ioi 0) := radA_contDiffOn α hα hα1 f h12
  have hb : ContDiffOn ℝ 3 (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (Set.Ioo 0 (π / 2)) := sinGam_contDiffOn_Ioo α
  have h3 : Work.FTS.CoercivityFix.Assembly.BlocksCont 3
      (fun z θ : ℝ => (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) * radA α f z) :=
    hB _ _ hb hR
  exact blocksCont_mono hn h3

theorem E1_blocks (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) :
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.CoerAdm α f →
      Work.FTS.CoercivityFix.Assembly.BlocksCont n (Work.FTS.CoercivityFix.Transfer.E1 α f) :=
  E1_blocks_aux (fun β hβ hβ1 => L12f_contDiffOn β hβ hβ1)
    (fun B R => BlocksCont_mul_factor B R) α hα hα1 n hn

end Work.FTS.CoercivityFix.Transfer
