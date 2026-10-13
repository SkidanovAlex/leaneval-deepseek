import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongEps.FK_abs_le_of_classC
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gL12Sup
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.L12Iterate
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS_EllLimOK.PkgJets.Pieces.ang_moment_sup
import Submission.Work.FTS_EllLimOK.PkgJets.Pieces.L12_sup_six
import Submission.Work.FTS_EllLimOK.PkgJets.Pieces.qang_deriv_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12jets_classC` — the radial `z∂_z`-jets of `L₁₂` on the class `C`

`Work.Construction.L12 g z = ∫_z^∞ ∫_θ K(θ) g(s,θ)/s dθ ds` is the radial `L₁₂`-transform of the
fundamental model.  The goal is the *uniform* bound (uniform in `z > 0`, `α`-degradation allowed)

  `|D_z^j (L₁₂ g)(z)| ≤ C·Xn₆(g)`,   `j ≤ 4`,  `Xn₆(g) = |g|_{ℋ⁶}`,

for every `g` in the linear elliptic class `Work.FTS.ClassC.ClassC α`.

## Route

The jets are *angular moments*: with `Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ`,

* `j = 0`: `|L₁₂ g z| ≤ C·|g|_{ℋ⁴} ≤ C·|g|_{ℋ⁶}` by the Cauchy–Schwarz computation of
  `Work.FTS.GalBasis.cc.abs_L12_le_HkNorm` at level `6` (`Pieces.L12_sup_six`);
* `j ≥ 1`: the tower `D_z^{m+1}(L₁₂ g) = -Qang g m` (proved here by induction from
  `Pieces.qang_deriv_classC`, the differentiation of the angular moment under the `θ`-integral)
  converts the jet into `Qang g (j-1)`, and `Pieces.ang_moment_sup` bounds the moment by
  `4√3·Xn₆(g)`: the *window* form of the radial Hardy inequality
  (`FkAux.fkSliceSup_sliceSupGraded`) gives the slice bound
  `∫_θ sin(2θ)^{-η}(D_z^j g z θ)² ≤ 3 HkSq α 6 g` for **every** `z > 0`, which is what removes the
  `z`-dependence and makes the estimate uniform on `(0,∞)`.

The base case `D_z (L₁₂ g) = -Qang g 0` uses the fundamental theorem of calculus for the tail
integral (`Work.FM.hasDerivAt_L12`), whose two hypotheses are the integrability of the
`L₁₂`-density on `(0,∞)` (`MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn`, which
needs only continuity on the open quadrant plus `ℋ⁴`-honesty — exactly what `ClassC` supplies) and
its continuity at the base point (a consequence of the differentiability of `Qang g 0`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

open Work.FTS_EllLimOK.PkgJets.Pieces (ang_moment_sup L12_sup_six qang_deriv_classC)

/-! ## `Qang g 0` is the angular moment `FK g` -/

/-- `Qang g 0 z = ∫_θ K(θ)·g(z,θ) dθ = FK g z` (the two integrands differ only by the order of the
factors). -/
theorem Qang_zero_eq_FK (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang g 0 z = Work.Construction.FK g z := by
  rw [Work.Elliptic.Qang, Work.Construction.FK]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [Work.Spaces.DzIter_zero]
  rw [show Work.Elliptic.Ktheta = Work.Spaces.K from rfl]
  ring

/-! ## The tower identity `D_z^{m+1}(L₁₂ g) = -Qang g m` -/

/-- **The tower identity** for a `ClassC` datum: for `m ≤ 3` and `z > 0`,

  `D_z^{m+1}(L₁₂ g)(z) = - Qang g m z`,   `Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ`.

The proof is the induction with step `D_z(Qang g m) = Qang g (m+1)`, i.e.
`z·∂_z(Qang g m)(z) = Qang g (m+1)(z)`, which is `Pieces.qang_deriv_classC`. -/
theorem DzdIter_L12_eq_neg_Qang {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) {m : ℕ} (hm : m ≤ 3) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter (m + 1) (fun z => Work.Construction.L12 g z) z
      = - Work.Elliptic.Qang g m z := by
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 4 (by norm_num) hg.mem
  have hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0 := hg.reg.continuousOn
  have hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcont hmem4
  have hbase : ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g 0 z := by
    intro z hz
    have hcontD : ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z := by
      have hQ0 := qang_deriv_classC hα hα1 hg (m := 0) (by norm_num) hz
      have h1 : ContinuousAt (fun x => Work.Elliptic.Qang g 0 x / x) z :=
        hQ0.continuousAt.div continuousAt_id (ne_of_gt hz)
      refine h1.congr ?_
      filter_upwards with x
      exact (Work.Elliptic.L12dens_eq_Qang_div g x).symm
    have hd : deriv (fun z' => Work.Construction.L12 g z') z
        = -(Work.Construction.L12dens g z) :=
      (Work.FM.hasDerivAt_L12 hint hcontD hz).deriv
    change z * deriv (fun z' => Work.Construction.L12 g z') z = - Work.Elliptic.Qang g 0 z
    rw [hd, mul_neg, Work.Construction.mul_L12dens_eq_FK (ne_of_gt hz), Qang_zero_eq_FK]
  have hgen : ∀ m : ℕ, m ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (m + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g m z := by
    intro m
    induction m with
    | zero => intro _ z hz; exact hbase z hz
    | succ n ih =>
        intro hn z hz
        have hQ := qang_deriv_classC hα hα1 hg (m := n) (by omega) hz
        have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)
            =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (by omega) z' hz'
        have hdv : deriv (Work.Elliptic.DzdIter (n + 1)
              (fun z => Work.Construction.L12 g z)) z
            = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
          rw [hev.deriv_eq]
          exact deriv.neg
        change z * deriv (Work.Elliptic.DzdIter (n + 1)
              (fun z => Work.Construction.L12 g z)) z = - Work.Elliptic.Qang g (n + 1) z
        rw [hdv, hQ.deriv, mul_neg, mul_div_assoc',
          mul_div_cancel_left₀ (Work.Elliptic.Qang g (n + 1) z) (ne_of_gt hz)]
  exact hgen m hm z hz

/-! ## The target -/

theorem L12jets_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g := by
  obtain ⟨CL, hCLpos, hCL⟩ := L12_sup_six
  refine ⟨CL + 4 * Real.sqrt 3 + 1, by positivity, ?_⟩
  intro g hg j hj z hz
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hle1 : CL ≤ CL + 4 * Real.sqrt 3 + 1 := by linarith [Real.sqrt_nonneg 3]
  have hle2 : 4 * Real.sqrt 3 ≤ CL + 4 * Real.sqrt 3 + 1 := by linarith [hCLpos.le]
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    simp only [Work.Spaces.DzIter_zero]
    exact le_trans (hCL α g hmem6 z (le_of_lt hz)) (mul_le_mul_of_nonneg_right hle1 hXnn)
  · have hjk : j - 1 ≤ 3 := by omega
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 g z) j z 0]
    have htower := DzdIter_L12_eq_neg_Qang hα hα1 hg (m := j - 1) hjk hz
    rw [Nat.sub_add_cancel hjpos] at htower
    rw [htower, abs_neg]
    exact le_trans (ang_moment_sup hα hα1 hg hjk hz) (mul_le_mul_of_nonneg_right hle2 hXnn)

end Work.FTS_EllLimOK.PkgJets
