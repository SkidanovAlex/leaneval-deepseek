/-
# `bdata_blkNstar` — the `BData` of the linear-in-`w` block `-μ w - c D_z w`
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.Common

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`BData` for `blkNstar w μ lam = -μ w - (μ+λ+μλ) D_z w`.**  Purely algebraic: the two
level shifts `HkSq_Dz_le_succ'` and `HkSq_const_mul` give
`HkSq α k (blkNstar w μ lam) ≤ 2(|μ|² + |μ+λ+μλ|²)·HkSq α (k+1) w`, and `|μ| ≤ 1/2`,
`|λ| ≤ 1` bound the coefficient by `2(1/4 + 4) = 17/2 < 9`. -/
theorem bdata_blkNstar (C₀ : ℝ) :
    ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ KS : ℝ, 0 < KS ∧ ∀ {w : Fn} (μ lam : ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      |μ| ≤ 1 / 2 → |lam| ≤ 1 → Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KS
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam) := by
  intro α hαI
  refine ⟨9, by norm_num, ?_⟩
  intro w μ lam hcls hXw hμ hlam
  have hα0 : 0 < α := hαI.1
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hsmw.Dz
  have hm6Dz : Work.Spaces.HkMem α 6 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 6 hsmw hm7
  have hm4Dz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  -- the coefficient bounds
  have hμ0 : 0 ≤ |μ| := abs_nonneg μ
  have hl0 : 0 ≤ |lam| := abs_nonneg lam
  have h1 : |μ + lam + μ * lam| ≤ |μ| + |lam| + |μ| * |lam| := by
    calc |μ + lam + μ * lam| ≤ |μ + lam| + |μ * lam| := abs_add_le _ _
      _ = |μ + lam| + |μ| * |lam| := by rw [abs_mul]
      _ ≤ (|μ| + |lam|) + |μ| * |lam| := by linarith [abs_add_le μ lam]
      _ = |μ| + |lam| + |μ| * |lam| := by ring
  have hab : |μ| * |lam| ≤ 1 / 2 := by
    have h := mul_le_mul hμ hlam hl0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h1 : (1 / 2 : ℝ) * 1 = 1 / 2 := by norm_num
    linarith [h, h1]
  have h2 : |μ| + |lam| + |μ| * |lam| ≤ 2 := by linarith [hμ, hlam, hab]
  have h3 : |μ + lam + μ * lam| ≤ 2 := h1.trans h2
  have hcc : (μ + lam + μ * lam) ^ 2 ≤ 4 := by
    calc (μ + lam + μ * lam) ^ 2 = |μ + lam + μ * lam| ^ 2 := (sq_abs _).symm
      _ ≤ 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = 4 := by norm_num
  have hmm : μ ^ 2 ≤ 1 / 4 := by
    calc μ ^ 2 = |μ| ^ 2 := (sq_abs μ).symm
      _ ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hμ0 hμ 2
      _ = 1 / 4 := by norm_num
  -- the pointwise shape
  have hshape : Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam
      = fun z θ => (-μ) * w z θ + (-(μ + lam + μ * lam)) * Work.Spaces.Dz w z θ := by
    funext z θ
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar, Work.Construction.Nstar]
    ring
  have hA1s : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-μ) * w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-μ) hsmw
  have hA2s : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul _ hsmDz
  have hA1m4 : Work.Spaces.HkMem α 4 (fun z θ => (-μ) * w z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-μ) hm4
  have hA2m4 : Work.Spaces.HkMem α 4
      (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz w z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 4 _ hm4Dz
  have hA1m6 : Work.Spaces.HkMem α 6 (fun z θ => (-μ) * w z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-μ) hm6
  have hA2m6 : Work.Spaces.HkMem α 6
      (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz w z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 _ hm6Dz
  have hm6star : Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam) := by
    rw [hshape]
    exact Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 6 hA1s hA2s hA1m6 hA2m6
  have hsmstar : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam) := by
    rw [hshape]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.smoothOpen_add hA1s hA2s
  -- the level-four estimate
  have h4shift : Work.Spaces.HkSq α 4 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 4 hsmw hm5
  have h45 : Work.Spaces.HkSq α 4 w ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm5
  have h4 : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam)
      ≤ 9 * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [hshape]
    have hadd := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα0 hA1s hA2s hA1m4 hA2m4
    have h1 : Work.Spaces.HkSq α 4 (fun z θ => (-μ) * w z θ)
        = μ ^ 2 * Work.Spaces.HkSq α 4 w := by
      rw [Work.FTS.StrongEps.HkSq_const_mul α 4 (-μ) w]; ring
    have h2 : Work.Spaces.HkSq α 4 (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz w z θ)
        = (μ + lam + μ * lam) ^ 2 * Work.Spaces.HkSq α 4 (Work.Spaces.Dz w) := by
      rw [Work.FTS.StrongEps.HkSq_const_mul α 4 (-(μ + lam + μ * lam)) (Work.Spaces.Dz w)]
      ring
    rw [h1, h2] at hadd
    have hSs5 : 0 ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
    nlinarith [hadd, h4shift, h45, hcc, hmm, hSs5]
  -- the level-six estimate
  have h6shift : Work.Spaces.HkSq α 6 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 6 hsmw hm7
  have h67 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm7
  have h6 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam)
      ≤ 9 * (1 + Work.Spaces.HkSq α 7 w) + 9 * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    rw [hshape]
    have hadd := Work.FTS.GalFields.RHS.HkSq_add_le_open α 6 hα0 hA1s hA2s hA1m6 hA2m6
    have h1 : Work.Spaces.HkSq α 6 (fun z θ => (-μ) * w z θ)
        = μ ^ 2 * Work.Spaces.HkSq α 6 w := by
      rw [Work.FTS.StrongEps.HkSq_const_mul α 6 (-μ) w]; ring
    have h2 : Work.Spaces.HkSq α 6 (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz w z θ)
        = (μ + lam + μ * lam) ^ 2 * Work.Spaces.HkSq α 6 (Work.Spaces.Dz w) := by
      rw [Work.FTS.StrongEps.HkSq_const_mul α 6 (-(μ + lam + μ * lam)) (Work.Spaces.Dz w)]
      ring
    rw [h1, h2] at hadd
    have hSs6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
    have hSs7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
    nlinarith [hadd, h6shift, h67, hcc, hmm, hSs6, hSs7,
      sq_nonneg (1 + Work.Spaces.HkSq α 6 w)]
  exact ⟨hsmstar, hm6star, h4, h6⟩

end Work.FTS.StrongEps.E4R3.RawE6Aux
