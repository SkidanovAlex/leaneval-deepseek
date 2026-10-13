/-
# `Transfer/E2pkg/RadSBnd.lean` — the pointwise majorant of the `D_z`-iterates of `radS`

With `L = L₁₂ f`, `Q = Qang f 0`, `C₀ = L₁₂(Transport f)(0)`, the Leibniz rule for
`D_z = z ∂_z` (`Nonlinear.Pieces.dzdIter_mul_leibniz`) expands the `D_z^j`-iterate of

  `radS α f = −(D_z a)·L + a·Q + (D_z b / c)·C₀`   on `(0,∞)`

into the three blocks `W1`, `W2`, `W3` of this file.  Bounding the coefficients `D_z^c a` by
`K` and applying Cauchy–Schwarz, the squared weighted iterate is dominated by the explicit
majorant `SmajA α f j K`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The three blocks of the expansion -/

/-- The first binomial block of `D_z^j (radS α f)`: `D_z^c (D_z a)` against `D_z^{j-c} L₁₂ f`. -/
noncomputable def W1 (α : ℝ) (f : Fn) (j : ℕ) : ℝ → ℝ := fun z =>
  ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)
    * (Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) z)
    * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z)

/-- The second binomial block: `D_z^c a` against `D_z^{j-c} (Qang f 0) = Qang f (j-c)`. -/
noncomputable def W2 (α : ℝ) (f : Fn) (j : ℕ) : ℝ → ℝ := fun z =>
  ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)
    * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
    * (Work.Elliptic.Qang f (j - b) z)

/-- The third (constant) block of `D_z^j (radS α f)`. -/
noncomputable def W3 (α : ℝ) (f : Fn) (j : ℕ) : ℝ → ℝ := fun z =>
  (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
    * (Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z)

/-- **The expansion of `D_z^j (radS α f)`** on `(0,∞)`, `j ≤ 3`. -/
theorem radS_DzdIter_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) :
    ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z
      = -(W1 α f j z) + W2 α f j z + W3 α f j z := by
  have hsmA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) IoiA :=
    contDiffOn_ampA_five α
  have hsmB5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) IoiA :=
    contDiffOn_ampB_five α
  -- the three summands
  set U1 : ℝ → ℝ := fun z =>
    -(Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) with hU1
  set U2 : ℝ → ℝ := fun z =>
    Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Elliptic.Qang f 0 z with hU2
  set U3 : ℝ → ℝ := fun z =>
    (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
      * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 with hU3
  -- differentiability of the coefficient iterates
  have hA1diff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)) z := by
    intro c hc z hz
    have hdc : Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)
        = Work.Elliptic.DzdIter (c + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) := by
      rw [show Work.FTS.CoercivityFix.Transfer.dAmpA α
          = Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampA α) from rfl]
      exact Work.FTS.Nonlinear.Pieces.DzdIter_add c 1 _
    rw [hdc]
    have hc4 : c + 1 ≤ 4 := by omega
    exact differentiableAt_dzdIter_of_contDiffOn_five (c := c + 1) hsmA5 hc4 hz
  have hA2diff : ∀ c ≤ 4, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampA α)) z :=
    fun c hc z hz => differentiableAt_dzdIter_of_contDiffOn_five hsmA5 hc hz
  have hsmL : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) IoiA :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five α hα hα1
      hf.reg.1 hf.reg.2.1 hf.l12
  have hLdiff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z := by
    intro c hc z hz
    rw [DzdIter_eq_Zop_iter]
    refine Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
      (b := c) (hu := hsmL.of_le (Nat.cast_le.mpr (by
        have h := Nat.add_le_add_right hc 1
        norm_num at h
        exact h))) hz
  have hQdiff : ∀ c ≤ 2, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Elliptic.Qang f 0 z)) z := by
    intro c hc z hz
    refine (differentiableAt_Qang_of_le_two α hα hα1 hf hc hz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact DzdIter_Qang_zero α hα hα1 hf c (by omega) w hw
  have hA3sm : ContDiffOn ℝ 4
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α) IoiA := by
    have h1 : (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
        = fun z => Work.Spaces.Zop^[1] (Work.FTS.CoercivityFix.Transfer.ampB α) z
            / Work.Spaces.c α := by
      funext z; rfl
    rw [h1]
    exact (Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' 1 4
      (hsmB5.of_le (Nat.cast_le.mpr (by norm_num)))).div_const _
  have hA3diff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z : ℝ =>
        Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)) z := by
    intro c hc z hz
    have hc4 : c + 1 ≤ 4 := by
      have h := Nat.add_le_add_right hc 1
      norm_num at h
      exact h
    exact differentiableAt_dzdIter_of_contDiffOn_general (c := c) (N := 4) hA3sm hc4 hz
  -- additivity / Leibniz data
  have hU12 : ∀ b < j, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (U1 + U2)) z := by
    intro b hb z hz
    have hu : ∀ c ≤ b, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c U1) z' := by
      intro c hc z' hz'
      have hcons : U1 = fun z => (-1 : ℝ) *
          (Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) := by
        rw [hU1]; funext w; ring
      rw [hcons]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
      exact (differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA1diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hLdiff c (by omega) z'' hz'') hz').const_mul (-1)
    have hv : ∀ c ≤ b, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c U2) z' := by
      intro c hc z' hz'
      exact differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA2diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hQdiff c (by omega) z'' hz'') hz'
    exact differentiableAt_dzdIter_add_of (j := b) hu hv hz
  have hU3diff : ∀ b < j, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b U3) z := by
    intro b hb z hz
    have hcons : U3 = fun z => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α) := by
      rw [hU3]; funext w; ring
    rw [hcons, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
    exact (hA3diff b (by omega) z hz).const_mul _
  -- the expansion
  have hsplit : ∀ z ∈ IoiA,
      Work.FTS.CoercivityFix.Transfer.radS α f z = (U1 + U2 + U3) z := by
    intro z hz
    have h := radS_split α hα hα1 hf z hz
    rw [h]
    simp only [hU1, hU2, hU3, Pi.add_apply]
  have hexp : ∀ z ∈ IoiA,
      Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z
        = Work.Elliptic.DzdIter j (U1 + U2 + U3) z :=
    fun z hz => Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hsplit j z hz
  have e1 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (U1 + U2 + U3) z
      = Work.Elliptic.DzdIter j (U1 + U2) z + Work.Elliptic.DzdIter j U3 z := by
    intro z hz
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j (U1 + U2) U3 hU12 hU3diff z hz
  have e2 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (U1 + U2) z
      = Work.Elliptic.DzdIter j U1 z + Work.Elliptic.DzdIter j U2 z := by
    intro z hz
    have h1 : ∀ b < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b U1) z' := by
      intro b hb z' hz'
      have hcons : U1 = fun z => (-1 : ℝ) *
          (Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) := by
        rw [hU1]; funext w; ring
      rw [hcons]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
      exact (differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA1diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hLdiff c (by omega) z'' hz'') hz').const_mul (-1)
    have h2 : ∀ b < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b U2) z' := by
      intro b hb z' hz'
      exact differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA2diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hQdiff c (by omega) z'' hz'') hz'
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j U1 U2 h1 h2 z hz
  have e3 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U1 z = -(W1 α f j z) := by
    intro z hz
    have hub : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)) z' :=
      fun c hc z' hz' => hA1diff c (by omega) z' hz'
    have hvb : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z' :=
      fun c hc z' hz' => hLdiff c (by omega) z' hz'
    have hlei := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
      (Work.FTS.CoercivityFix.Transfer.dAmpA α) (Work.Coercivity.L12f f) hub hvb z hz
    have hA1 : ∀ b, Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.dAmpA α)
        = Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) := by
      intro b
      rw [show Work.FTS.CoercivityFix.Transfer.dAmpA α
          = Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampA α) from rfl]
      exact Work.FTS.Nonlinear.Pieces.DzdIter_add b 1 _
    have hneg : Work.Elliptic.DzdIter j U1 z = - Work.Elliptic.DzdIter j (fun w =>
        Work.FTS.CoercivityFix.Transfer.dAmpA α w * Work.Coercivity.L12f f w) z := by
      rw [hU1, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_neg]
    rw [hneg, hlei, W1]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hA1 b]
    ring
  have e4 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U2 z = W2 α f j z := by
    intro z hz
    have hub : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampA α)) z' :=
      fun c hc z' hz' => hA2diff c (by omega) z' hz'
    have hvb : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Elliptic.Qang f 0 z)) z' :=
      fun c hc z' hz' => hQdiff c (by omega) z' hz'
    have hlei := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
      (Work.FTS.CoercivityFix.Transfer.ampA α) (fun z => Work.Elliptic.Qang f 0 z) hub hvb z hz
    rw [show U2 = fun z => Work.FTS.CoercivityFix.Transfer.ampA α z
        * Work.Elliptic.Qang f 0 z from hU2, hlei, W2]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [DzdIter_Qang_zero α hα hα1 hf (j - b) (by
      have := Finset.mem_range.mp hb; omega) z hz]
    ring
  have e5 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U3 z = W3 α f j z := by
    intro z hz
    have hfun : U3 = fun z => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * ((Work.Spaces.c α)⁻¹
            * Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampB α) z) := by
      rw [hU3]; funext w
      simp only [Work.FTS.CoercivityFix.Transfer.dAmpB, Work.Elliptic.DzdIter_succ,
        Work.Elliptic.DzdIter_zero, Work.Elliptic.Dzd]
      ring
    rw [hfun, W3, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul,
      show Work.Elliptic.DzdIter j (Work.Elliptic.DzdIter 1
            (Work.FTS.CoercivityFix.Transfer.ampB α))
          = Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) from
        Work.FTS.Nonlinear.Pieces.DzdIter_add j 1 _]
    ring
  intro z hz
  rw [hexp z hz, e1 z hz, e2 z hz, e3 z hz, e4 z hz, e5 z hz]

/-! ## The majorant -/

/-- The explicit majorant of the squared and weighted `j`-th iterate of `radS`. -/
noncomputable def SmajA (α : ℝ) (f : Fn) (j : ℕ) (K : ℝ) (z : ℝ) : ℝ :=
  3 * ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
      + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2))

/-- **The pointwise bound** `(D_z^j (radS α f)(z))² w(z)² ≤ SmajA α f j K z` on `(0,∞)`. -/
theorem radS_sq_le_SmajA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b ≤ 4, ∀ z ∈ IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) :
    ∀ z ∈ IoiA, (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
      * (Work.Spaces.w z) ^ 2 ≤ SmajA α f j K z := by
  have hC0 : ∀ b, ((j.choose b : ℕ) : ℝ) ^ 2 = ((j.choose b : ℝ)) ^ 2 := by
    intro b; push_cast; ring
  intro z hz
  rw [radS_DzdIter_eq α hα hα1 hf hj z hz, SmajA]
  set S1 : ℝ := W1 α f j z with hS1
  set S2 : ℝ := W2 α f j z with hS2
  set S3 : ℝ := W3 α f j z with hS3
  have hsq : (-S1 + S2 + S3) ^ 2 ≤ 3 * (S1 ^ 2 + S2 ^ 2 + S3 ^ 2) := by
    nlinarith [sq_nonneg (S1 - S2), sq_nonneg (S2 - S3), sq_nonneg (S3 + S1)]
  have hw_nn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hS1b : S1 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
      * (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := by
    have hcs : S1 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter (b + 1)
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := by
      rw [hS1, W1]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hK1 : (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter (b + 1)
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b hb => ?_
      have hbj : b + 1 ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hb1 : |Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd (b + 1) hbj z hz
      rw [mul_pow, hC0 b]
      exact mul_le_mul_of_nonneg_left
        (sq_le_sq' (abs_le.mp hb1).1 (abs_le.mp hb1).2) (sq_nonneg _)
    have hSnn : 0 ≤ (∑ b ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    calc S1 ^ 2 ≤ _ * (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := hcs
      _ ≤ ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) :=
          mul_le_mul_of_nonneg_right hK1 hSnn
  have hS2b : S2 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
      * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := by
    have hcs : S2 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := by
      rw [hS2, W2]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hK2 : (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b hb => ?_
      have hbj : b ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hb1 : |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd b hbj z hz
      rw [mul_pow, hC0 b]
      exact mul_le_mul_of_nonneg_left
        (sq_le_sq' (abs_le.mp hb1).1 (abs_le.mp hb1).2) (sq_nonneg _)
    have hSnn : 0 ≤ (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    calc S2 ^ 2 ≤ _ * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := hcs
      _ ≤ ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) :=
          mul_le_mul_of_nonneg_right hK2 hSnn
  have hS3b : S3 ^ 2 = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
      * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2) := by
    rw [hS3, W3]; ring
  have h1 : (S1 ^ 2 + S2 ^ 2 + S3 ^ 2) * (Work.Spaces.w z) ^ 2
      ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := by
    have e1 : (S1 ^ 2) * (Work.Spaces.w z) ^ 2
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
      calc S1 ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2))
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hS1b hw_nn
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * ((∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2) := by rw [← Finset.sum_mul]
    have e2 : (S2 ^ 2) * (Work.Spaces.w z) ^ 2
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      calc S2 ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2))
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hS2b hw_nn
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * ((∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
            rw [← Finset.sum_mul]
    have e3 : (S3 ^ 2) * (Work.Spaces.w z) ^ 2
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := by
      rw [hS3b]; ring
    linarith [e1, e2, e3.le]
  have h2 := mul_le_mul_of_nonneg_right hsq hw_nn
  linarith [h1, h2]

end Work.FTS.CoercivityFix.Transfer.E2pkg
