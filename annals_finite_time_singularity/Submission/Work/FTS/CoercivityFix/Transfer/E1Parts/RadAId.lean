/-
# `E1Parts/RadAId` — the pointwise identity for the integrand of `radA`

`(D_z^j (radA α f)(z))²w(z)² = Efun α f j z` on `(0,∞)`, for `j ≤ 3`, where `Efun` is the
explicit expression of `RadAPieces.Efun`: the sum obtained from the Leibniz rule on the product
`ampA α · L₁₂ f`, with the `D_z`-iterates of `L₁₂ f` rewritten through
`RadAPieces.dzdIter_L_as_if`, plus the constant term `(ampB α/c α)·L₁₂(Transport f)(0)`.

The two structural inputs are the additivity of the `D_z`-iterates on the sum
(`RadAZop.DzdIter_add_of_diff`) and the Leibniz rule
(`Nonlinear.Pieces.dzdIter_mul_leibniz`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn
import Submission.Work.FTS.CoercivityFix.Transfer.E1_blocks
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The pointwise decomposition of `radA` on `(0,∞)`. -/
theorem radA_split (α : ℝ) {f : ℝ → ℝ → ℝ} :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.FTS.CoercivityFix.Transfer.radA α f z
        = (-1 * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := by
  intro z hz
  have h1z : (1 + z) ≠ 0 := by
    have : (0 : ℝ) < z := hz
    linarith
  rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
  simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
  field_simp
  try ring

/-- **Additivity of the `D_z`-iterates of `radA`.** -/
theorem radA_iter_add (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = Work.Elliptic.DzdIter j (fun z : ℝ => -1
            * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) z
          + Work.Elliptic.DzdIter j (fun z : ℝ =>
              (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
                * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  have hLsm : ContDiffOn ℝ 3 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn α hα hα1 f hsm hmem
  have hAsm : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_ampA α hα hα1
  have hBsm : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_ampB α
  have hPsm : ContDiffOn ℝ 3
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
      (Set.Ioi (0 : ℝ)) := hAsm.mul hLsm
  have hU₁sm : ContDiffOn ℝ 3 (fun z : ℝ => -1
      * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))
      (Set.Ioi (0 : ℝ)) := contDiffOn_const.mul hPsm
  have hU₂sm : ContDiffOn ℝ 3 (fun z : ℝ =>
      (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
    (hBsm.div_const (Work.Spaces.c α)).mul contDiffOn_const
  have hdiff₁ : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))) z := by
    intro b hb z hz
    have hb3 : b + 1 ≤ 3 := by omega
    have hZ : DifferentiableAt ℝ (Work.Spaces.Zop^[b] (fun z : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))) z :=
      differentiableAt_Zop_iter_of_contDiffOn
        (hu := hU₁sm.of_le (by exact_mod_cast hb3)) hz
    have haux : Work.Elliptic.DzdIter b (fun z : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))
        = Work.Spaces.Zop^[b] (fun z : ℝ => -1
            * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b _
    rw [haux]
    exact hZ
  have hdiff₂ : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z := by
    intro b hb z hz
    have hb3 : b + 1 ≤ 3 := by omega
    have hZ : DifferentiableAt ℝ (Work.Spaces.Zop^[b] (fun z : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z :=
      differentiableAt_Zop_iter_of_contDiffOn
        (hu := hU₂sm.of_le (by exact_mod_cast hb3)) hz
    have haux : Work.Elliptic.DzdIter b (fun z : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
        = Work.Spaces.Zop^[b] (fun z : ℝ =>
            (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b _
    rw [haux]
    exact hZ
  intro z hz
  rw [DzdIter_congr_of_eqOn (Work.FTS.CoercivityFix.Transfer.radA α f)
    (fun z : ℝ => (-1 * (Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z))
        + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) (radA_split α) j z hz]
  exact DzdIter_add_of_diff j _ _ hdiff₁ hdiff₂ z hz

/-- **The Leibniz expansion of the first summand of `radA`.** -/
theorem radA_iter_U1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) z
        = -1 * ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
            * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  have hAsm : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_ampA α hα hα1
  intro z hz
  have hAdiff : ∀ b < j, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' := by
    intro b hb z' hz'
    have hb3 : b + 1 ≤ 3 := by omega
    have hZ : DifferentiableAt ℝ (Work.Spaces.Zop^[b]
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' :=
      differentiableAt_Zop_iter_of_contDiffOn (hu := hAsm.of_le (by exact_mod_cast hb3)) hz'
    have haux : Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α)
        = Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.Transfer.ampA α) :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b _
    rw [haux]
    exact hZ
  have hLdiff : ∀ b < j, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z' := by
    intro b hb z' hz'
    exact (differentiableOn_DzdIter_L12f α hα hα1 hf (b := b) (by omega) z' hz').differentiableAt
      (isOpen_Ioi.mem_nhds hz')
  have hleib := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
    (Work.FTS.CoercivityFix.Transfer.ampA α) (Work.Coercivity.L12f f) hAdiff hLdiff z hz
  have heq : Work.Elliptic.DzdIter j (fun z : ℝ => -1
      * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))
      = Work.Spaces.Zop^[j] (fun z : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j _
  rw [heq, Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
  dsimp only
  rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j
    (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)]
  rw [hleib]
  simp only [mul_assoc]

/-- **The second summand of `radA`.** -/
theorem radA_iter_U2 (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z : ℝ =>
          (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) := by
  intro z hz
  have hfun : (fun z : ℝ => (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      = fun z : ℝ => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * Work.FTS.CoercivityFix.Transfer.ampB α z := by
    funext w
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hfun, Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
    Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
    ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j
      (Work.FTS.CoercivityFix.Transfer.ampB α)]

/-- **The pointwise identity for the integrand of `radA`.** -/
theorem RadA_Efun_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2 = Efun α f j z := by
  intro z hz
  have hsum : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z))
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbj : j - b ≤ 4 := by
      have := Finset.mem_range.mp hb
      omega
    rw [dzdIter_L_as_if α hα hα1 hf hbj z hz]
  rw [radA_iter_add α hα hα1 f hf hj z hz, radA_iter_U1 α hα hα1 f hf hj z hz,
    radA_iter_U2 α f j z hz, Efun_eq_Big, Big_eq, hsum]
  ring

end Work.FTS.CoercivityFix.Transfer.E1Parts
