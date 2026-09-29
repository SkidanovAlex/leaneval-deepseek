import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.APsi.defs
import Submission.Work.APsi.slit_facts
import Submission.Work.APsi.lune_facts
import Submission.Work.APsi.slit_norm_eq_one
import Submission.Work.APsi.psiA_facts
import Submission.Work.ANum.psiA_lower
import Submission.Work.ANum.spick_relax

/-!
# The Schwarz–Pick bound for the derivative of the Theorem-A contour map `ψ_A`

**Goal.** `Work.ANum.psiA_deriv_le_schwarz`: for `z` in the closed unit disc and any `a ≤ ‖ψ_A z‖`,
`b ≥ ‖z‖` with `b ≤ 1`,

  `‖ψ_A' z‖ ≤ (4/5)·(491/500)·(1 - (25/16)a²)/(1 - (491/500)²b²)`.

**Proof (Schwarz–Pick telescoping, cf. `Work/ANum/STATUS3.md` §4).**  Write
`ψ_A(z) = Ψ((491/500) z)` with

  `Ψ = (-(4/5) ·) ∘ lune(36/5) ∘ (−·) ∘ rot t₄ ∘ slit r₄ ∘ rot t₃ ∘ slit r₃ ∘ rot t₂ ∘ slit r₂ ∘ rot t₁ ∘ slit r₁`

(`r₁, …, r₄` and `t₁, …, t₄` as in `Submission.CDTPlan.slitsA`).  Grouping the rotations with the
following slit map gives five holomorphic self-maps `stA1, …, stA5` of the unit disc and
`Ψ = (-(4/5)·) ∘ chainA` with `chainA = stA5 ∘ stA4 ∘ stA3 ∘ stA2 ∘ stA1`.  Every stage maps the
open disc into itself, hence so does the composite `chainA`; Schwarz–Pick applied to `chainA`
(`Commons.Analysis.Complex.schwarzPick_norm_deriv`) gives, at `w = (491/500) z`,

  `‖chainA' w‖ ≤ (1 - ‖chainA w‖²)/(1 - ‖w‖²)`,

and `‖chainA w‖ = (5/4)‖ψ_A z‖`, `‖w‖ = (491/500)‖z‖`.  Since the modulus of the outermost linear
factor `-(4/5)·` is *exactly* `4/5` and the chain rule gives
`ψ_A' z = (-(4/5)·chainA' w)·(491/500)`, the claim follows after replacing `‖ψ_A z‖` by the lower
bound `a` (numerator up) and `‖z‖` by the upper bound `b` (denominator down) — the last step is the
delegated lemma `Work.ANum.spick_relax` applied with `a' = (5/4)a`, `b' = (491/500)b`.

Note the bound is *sharp* (numerically the ratio `‖ψ_A' z‖ / RHS` reaches `1` inside the disc), so
no cruder argument can replace the Schwarz–Pick step.
-/

namespace Work.ANum

open Submission.CDTPlan Work.APsi Complex Metric

noncomputable section

/-! ## The building blocks of `ψ_A` as self-maps of the unit disc -/

/-- The rotation `z ↦ rot t · z`. -/
def cRot (t : ℝ) : ℂ → ℂ := fun z => rot t * z

/-- `z ↦ -z`. -/
def cNeg : ℂ → ℂ := fun z => -z

/-- The first slit stage `slit (9/10)`. -/
def stA1 : ℂ → ℂ := slit (9 / 10)

/-- The second slit stage, rotation included. -/
def stA2 : ℂ → ℂ := slit (379 / 625) ∘ cRot (2033 / 25000)

/-- The third slit stage, rotation included. -/
def stA3 : ℂ → ℂ := slit (673 / 1250) ∘ cRot (2927 / 25000)

/-- The fourth slit stage, rotation included. -/
def stA4 : ℂ → ℂ := slit (7487 / 10000) ∘ cRot (453 / 12500)

/-- The lune stage, including the final rotation and the sign. -/
def stA5 : ℂ → ℂ := lune (36 / 5) ∘ (cNeg ∘ cRot (-1971 / 25000))

/-- The full composite `stA5 ∘ stA4 ∘ stA3 ∘ stA2 ∘ stA1`, i.e. `lune(36/5, −slitsA ·)`. -/
def chainA : ℂ → ℂ := stA5 ∘ stA4 ∘ stA3 ∘ stA2 ∘ stA1

/-- The initial scaling `z ↦ (491/500) z`. -/
def scMulA : ℂ → ℂ := fun z => (491 / 500) * z

/-- `Ψ = (-(4/5)·) ∘ chainA`, so that `psiA = Ψ ∘ scMulA`. -/
def psiAPre : ℂ → ℂ := fun w => -(4 / 5) * chainA w

theorem cRot_maps (t : ℝ) : Set.MapsTo (cRot t) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [cRot, norm_mul, norm_rot, one_mul]
  exact hz

theorem cNeg_diff : DifferentiableOn ℂ cNeg (ball 0 1) := by
  unfold cNeg
  exact differentiableOn_id.neg

theorem cNeg_maps : Set.MapsTo cNeg (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  simpa [cNeg] using hz

theorem slit_diff_ball (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    DifferentiableOn ℂ (slit r) (ball 0 1) := (slit_facts r hr0 hr1).2.1

theorem slit_maps_ball (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Set.MapsTo (slit r) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  exact slit_norm_lt_one r hr0 hr1 z hz

theorem lune_diff_ball (c : ℝ) (hc : 1 < c) : DifferentiableOn ℂ (lune c) (ball 0 1) :=
  (lune_facts c hc).2.1

theorem lune_maps_ball (c : ℝ) (hc : 1 < c) : Set.MapsTo (lune c) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  exact lune_norm_lt_one c hc z hz

theorem stA1_diff : DifferentiableOn ℂ stA1 (ball 0 1) :=
  slit_diff_ball (9 / 10) (by norm_num) (by norm_num)

theorem stA1_maps : Set.MapsTo stA1 (ball 0 1) (ball 0 1) :=
  slit_maps_ball (9 / 10) (by norm_num) (by norm_num)

theorem stA2_diff : DifferentiableOn ℂ stA2 (ball 0 1) :=
  DifferentiableOn.comp (slit_diff_ball (379 / 625) (by norm_num) (by norm_num))
    (differentiableOn_id.const_mul _) (cRot_maps _)

theorem stA2_maps : Set.MapsTo stA2 (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp (slit_maps_ball (379 / 625) (by norm_num) (by norm_num)) (cRot_maps _)

theorem stA3_diff : DifferentiableOn ℂ stA3 (ball 0 1) :=
  DifferentiableOn.comp (slit_diff_ball (673 / 1250) (by norm_num) (by norm_num))
    (differentiableOn_id.const_mul _) (cRot_maps _)

theorem stA3_maps : Set.MapsTo stA3 (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp (slit_maps_ball (673 / 1250) (by norm_num) (by norm_num)) (cRot_maps _)

theorem stA4_diff : DifferentiableOn ℂ stA4 (ball 0 1) :=
  DifferentiableOn.comp (slit_diff_ball (7487 / 10000) (by norm_num) (by norm_num))
    (differentiableOn_id.const_mul _) (cRot_maps _)

theorem stA4_maps : Set.MapsTo stA4 (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp (slit_maps_ball (7487 / 10000) (by norm_num) (by norm_num)) (cRot_maps _)

theorem stA5_diff : DifferentiableOn ℂ stA5 (ball 0 1) :=
  DifferentiableOn.comp (lune_diff_ball (36 / 5) (by norm_num))
    (DifferentiableOn.comp cNeg_diff (differentiableOn_id.const_mul _) (cRot_maps _))
    (Set.MapsTo.comp cNeg_maps (cRot_maps _))

theorem stA5_maps : Set.MapsTo stA5 (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp (lune_maps_ball (36 / 5) (by norm_num))
    (Set.MapsTo.comp cNeg_maps (cRot_maps _))

/-! ## The composite `chainA` is a holomorphic self-map of the disc -/

theorem chainA12_diff : DifferentiableOn ℂ (stA2 ∘ stA1) (ball 0 1) :=
  DifferentiableOn.comp stA2_diff stA1_diff stA1_maps

theorem chainA12_maps : Set.MapsTo (stA2 ∘ stA1) (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp stA2_maps stA1_maps

theorem chainA123_diff : DifferentiableOn ℂ (stA3 ∘ (stA2 ∘ stA1)) (ball 0 1) :=
  DifferentiableOn.comp stA3_diff chainA12_diff chainA12_maps

theorem chainA123_maps : Set.MapsTo (stA3 ∘ (stA2 ∘ stA1)) (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp stA3_maps chainA12_maps

theorem chainA1234_diff : DifferentiableOn ℂ (stA4 ∘ (stA3 ∘ (stA2 ∘ stA1))) (ball 0 1) :=
  DifferentiableOn.comp stA4_diff chainA123_diff chainA123_maps

theorem chainA1234_maps : Set.MapsTo (stA4 ∘ (stA3 ∘ (stA2 ∘ stA1))) (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp stA4_maps chainA123_maps

theorem chainA_diff : DifferentiableOn ℂ chainA (ball 0 1) :=
  DifferentiableOn.comp stA5_diff chainA1234_diff chainA1234_maps

theorem chainA_maps : Set.MapsTo chainA (ball 0 1) (ball 0 1) :=
  Set.MapsTo.comp stA5_maps chainA1234_maps

/-! ## `ψ_A` as `Ψ ∘ (491/500)·` -/

theorem psiA_eq_chain : psiA = psiAPre ∘ scMulA := by
  funext z
  simp only [psiAPre, chainA, stA5, stA4, stA3, stA2, stA1, cRot, cNeg, scMulA, psiA, slitsA,
    Function.comp_apply]

/-! ## The main estimate -/

/-- Schwarz–Pick telescoping for the chain: at `w = (491/500) z`,
`‖chainA' w‖ ≤ (1 - (25/16)‖ψ_A z‖²)/(1 - (491/500)²‖z‖²)`. -/
theorem chainA_deriv_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖deriv chainA (scMulA z)‖ ≤
      (1 - (25 / 16) * ‖psiA z‖ ^ 2) / (1 - (491 / 500) ^ 2 * ‖z‖ ^ 2) := by
  have hw : scMulA z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    have h1 : ‖scMulA z‖ = (491 / 500) * ‖z‖ := by rw [scMulA, norm_mul]; norm_num
    rw [h1]
    nlinarith [norm_nonneg z]
  have hpsi_norm : ‖psiA z‖ = (4 / 5) * ‖chainA (scMulA z)‖ := by
    rw [psiA_eq_chain, Function.comp_apply, psiAPre, norm_mul]
    norm_num
  have hrel := spick_relax (f := chainA) chainA_diff chainA_maps
    (z := scMulA z) (a := (5 / 4) * ‖psiA z‖) (b := (491 / 500) * ‖z‖)
    (by positivity)
    (by rw [hpsi_norm]; linarith)
    (by rw [scMulA, norm_mul]; norm_num)
    (by nlinarith)
  refine le_trans hrel (le_of_eq ?_)
  rw [show ((5 / 4) * ‖psiA z‖) ^ 2 = (25 / 16) * ‖psiA z‖ ^ 2 by ring,
    show ((491 / 500) * ‖z‖) ^ 2 = (491 / 500) ^ 2 * ‖z‖ ^ 2 by ring]

theorem psiA_deriv_le_schwarz {z : ℂ} {a b : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ ‖Submission.CDTPlan.psiA z‖)
    (hb : ‖z‖ ≤ b) (hb1 : b ≤ 1) :
    ‖deriv Submission.CDTPlan.psiA z‖ ≤ (4 / 5) * (491 / 500) *
      ((1 - (25 / 16) * a ^ 2) / (1 - (491 / 500) ^ 2 * b ^ 2)) := by
  have hz1 : ‖z‖ ≤ 1 := le_trans hb hb1
  have hw : scMulA z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    have h1 : ‖scMulA z‖ = (491 / 500) * ‖z‖ := by rw [scMulA, norm_mul]; norm_num
    rw [h1]
    nlinarith [norm_nonneg z]
  -- chain rule: `ψ_A' z = (-(4/5)·chainA' w)·(491/500)`
  have hMsc : HasDerivAt scMulA (491 / 500 : ℂ) z := by
    rw [show scMulA = fun y : ℂ => (491 / 500 : ℂ) * y from rfl]
    exact hasDerivAt_const_mul ((491 / 500 : ℂ))
  have hrestAt : DifferentiableAt ℂ chainA (scMulA z) :=
    chainA_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hw)
  have hC : HasDerivAt (fun y : ℂ => -(4 / 5) * y) (-(4 / 5) : ℂ) (chainA (scMulA z)) :=
    hasDerivAt_const_mul (-(4 / 5) : ℂ)
  have hPsiAt : HasDerivAt psiAPre (-(4 / 5) * deriv chainA (scMulA z)) (scMulA z) := by
    rw [show psiAPre = (fun y : ℂ => -(4 / 5) * y) ∘ chainA from rfl]
    exact hC.comp (scMulA z) hrestAt.hasDerivAt
  have hcomp : HasDerivAt (psiAPre ∘ scMulA)
      ((-(4 / 5) : ℂ) * deriv chainA (scMulA z) * (491 / 500)) z := hPsiAt.comp z hMsc
  have hderiv : deriv psiA z = (-(4 / 5) : ℂ) * deriv chainA (scMulA z) * (491 / 500) := by
    rw [psiA_eq_chain]
    exact hcomp.deriv
  have hnorm : ‖deriv psiA z‖ = (4 / 5) * (491 / 500) * ‖deriv chainA (scMulA z)‖ := by
    rw [hderiv, norm_mul, norm_mul]
    norm_num
    ring
  rw [hnorm]
  -- Schwarz–Pick (with the relaxation `a ≤ ‖ψ_A z‖`, `‖z‖ ≤ b`)
  have hreq : ‖psiA z‖ = (4 / 5) * ‖chainA (scMulA z)‖ := by
    rw [psiA_eq_chain, Function.comp_apply, psiAPre, norm_mul]
    norm_num
  have ha0' : 0 ≤ (5 / 4) * a := by linarith
  have ha' : (5 / 4) * a ≤ ‖chainA (scMulA z)‖ := by
    rw [hreq] at ha
    linarith
  have hb' : ‖scMulA z‖ ≤ (491 / 500) * b := by
    have h1 : ‖scMulA z‖ = (491 / 500) * ‖z‖ := by rw [scMulA, norm_mul]; norm_num
    rw [h1]
    exact mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ (491 : ℝ) / 500)
  have hb1' : (491 / 500) * b < 1 := by nlinarith
  have hrel := spick_relax chainA_diff chainA_maps ha0' ha' hb' hb1'
  have hrel' : ‖deriv chainA (scMulA z)‖ ≤
      (1 - (25 / 16) * a ^ 2) / (1 - (491 / 500) ^ 2 * b ^ 2) := by
    refine le_trans hrel (le_of_eq ?_)
    rw [show ((5 / 4) * a) ^ 2 = (25 / 16) * a ^ 2 by ring,
      show ((491 / 500) * b) ^ 2 = (491 / 500) ^ 2 * b ^ 2 by ring]
  exact mul_le_mul_of_nonneg_left hrel' (by norm_num : (0 : ℝ) ≤ (4 : ℝ) / 5 * (491 / 500))

end

end Work.ANum
