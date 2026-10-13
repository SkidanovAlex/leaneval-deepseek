import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.NMem6Parts
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.StrongEps.EpsGdotThird
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.ZTrunc` — the truncation `w ↦ ztrunc w` and its `ℋᵏ`-invariance

The target `blocks/N_BData` states its vanishing hypothesis in the **weak** form
`0 < z → θ ∉ Ioo 0 (π/2) → w z θ = 0` (nothing is assumed for `z ≤ 0`), whereas the tree's
`H6Adm`-based machinery (`H6Adm_of_classC_of_eqzero` and hence every `H6Adm` producer) needs the
**strong** form `¬ (0 < z ∧ θ ∈ Ioo 0 (π/2)) → w z θ = 0`.

The remedy is the truncation `ztrunc w z θ = if 0 < z then w z θ else 0`, which

* agrees with `w` on the open half-plane `z > 0` — in particular on the open quadrant, so all the
  `ℋᵏ`-quantities (which are integrals over `{z ≥ 0} × [0,π/2]`, with the weight
  `w(z) = (1+z)²/z²` vanishing at `z = 0`) are unchanged
  (`HkSq_congr_open`, `H6Pair6Aux.HkMem_congr_Qd`), and
* satisfies the strong vanishing form as soon as `w` satisfies the weak one.

Everything the estimates need about `w` (`ClassC`, the elliptic packages, `HkMem`, `HkSq`) can
therefore be transported to `ztrunc w`; the transfer lemmas for `ClassC` and the two elliptic
packages live in `N_aux.ZTruncClassC` and `N_aux.ZTruncPkgs`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The truncation of `w` to the half-plane `z > 0` (zero elsewhere). -/
noncomputable def ztrunc (w : Fn) : Fn := fun z θ => if 0 < z then w z θ else 0

@[simp] theorem ztrunc_of_pos {w : Fn} {z θ : ℝ} (hz : 0 < z) : ztrunc w z θ = w z θ := by
  simp [ztrunc, hz]

theorem ztrunc_of_nonpos {w : Fn} {z θ : ℝ} (hz : ¬ 0 < z) : ztrunc w z θ = 0 := by
  simp [ztrunc, hz]

/-- The truncation agrees with `w` on the open quadrant. -/
theorem ztrunc_eq_on_Qd {w : Fn} {z θ : ℝ} (hz : 0 < z) : ztrunc w z θ = w z θ :=
  ztrunc_of_pos hz

/-- The truncation agrees with `w` on the open quadrant (curried form for the congruence
lemmas). -/
theorem ztrunc_eq_of_Qd {w : Fn} {z θ : ℝ} (hz : 0 < z) (_hθ : 0 < θ)
    (_h2 : θ < Real.pi / 2) : ztrunc w z θ = w z θ :=
  ztrunc_of_pos hz

/-! ## The strong vanishing form -/

/-- If `w` satisfies the weak vanishing hypothesis (only for `z > 0`) then `ztrunc w` satisfies
the strong one. -/
theorem ztrunc_strong_zero {α : ℝ} {w : Fn} (_hw : Work.FTS.ClassC.ClassC α w)
    (hz : ∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) :
    ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → ztrunc w z θ = 0 := by
  intro z θ hzq
  by_cases hpos : 0 < z
  · have hθ : θ ∉ Set.Ioo 0 (Real.pi / 2) := fun hc => hzq ⟨hpos, hc⟩
    rw [ztrunc_of_pos hpos]
    exact hz z θ hpos hθ
  · exact ztrunc_of_nonpos hpos

/-! ## Invariance of the `ℋᵏ`-quantities -/

/-- `HkSq` is unchanged by the truncation. -/
theorem HkSq_ztrunc (α : ℝ) (k : ℕ) (w : Fn) :
    Work.Spaces.HkSq α k (ztrunc w) = Work.Spaces.HkSq α k w :=
  Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ hz _ _ => ztrunc_of_pos hz)

/-- `HkNorm` is unchanged by the truncation. -/
theorem HkNorm_ztrunc (α : ℝ) (k : ℕ) (w : Fn) :
    Work.Spaces.HkNorm α k (ztrunc w) = Work.Spaces.HkNorm α k w := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, HkSq_ztrunc]

/-- `Xn` is unchanged by the truncation. -/
theorem Xn_ztrunc (α : ℝ) (w : Fn) :
    Work.FTS.Nonlin.Xn α (ztrunc w) = Work.FTS.Nonlin.Xn α w :=
  HkNorm_ztrunc α 4 w

/-- `HkMem` transfers to the truncation. -/
theorem HkMem_ztrunc {α : ℝ} {k : ℕ} {w : Fn} (h : Work.Spaces.HkMem α k w) :
    Work.Spaces.HkMem α k (ztrunc w) :=
  Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
    (fun z θ hzθ => (ztrunc_of_pos hzθ.1).symm) h

/-- `HkMem` transfers back from the truncation. -/
theorem HkMem_of_ztrunc {α : ℝ} {k : ℕ} {w : Fn}
    (h : Work.Spaces.HkMem α k (ztrunc w)) : Work.Spaces.HkMem α k w :=
  Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
    (fun z θ hzθ => ztrunc_of_pos hzθ.1) h

/-- `SmoothOpen` transfers to the truncation. -/
theorem smoothOpen_ztrunc {w : Fn} (h : Work.FTS.EllipticEst.SmoothOpen w) :
    Work.FTS.EllipticEst.SmoothOpen (ztrunc w) :=
  Work.FTS.EllipticEst.RPFresh.smoothOpen_congr h
    (fun z θ hz _ _ => ztrunc_of_pos hz)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
