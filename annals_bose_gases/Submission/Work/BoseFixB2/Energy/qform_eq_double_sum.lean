import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseFixB2.Energy.gradeA_support_herm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.qform_eq_double_sum`

FS §6 (`lem:LocMatrices`): the quadratic form `⟪ψ, 𝒜ψ⟫` of the graded box state, as
computed by `Work.UBBInputs3.qform` over the **window** index range
`iRange (fsNn v μ n) = [0, nn−1]`, equals the double sum over the **sector** range
`[0,n]²`.

This is the elementary bookkeeping that lets the §6 argument replace the abstract
window sum of Lieb–Solovej's localisation theorem by the concrete sector sum in which
the band property (`𝒜^{(k)} = 0` for `k ≥ 3`) and FS's `eq:dvapriori` are formulated.
The two ingredients are:

* the window range contains the sector range, since
  `fsNn v μ n = gradeNn n 𝓜 = max (n+1) (gradeMw 𝓜) ≥ n+1`, i.e.
  `iRange (fsNn v μ n) = [0, fsNn − 1] ⊇ [0,n]`;
* the norm profile `gradePsi` vanishes outside `[0,n]` (its defining `if` guard), so
  every index outside `[0,n]` kills the corresponding summand `star ψ_i · 𝒜_{ij} · ψ_j`.

No hypothesis on `Φ` (smoothness, positivity of `normB`) is needed: the identity rests
only on the support statement of the profile.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric Finset

namespace Work.BoseFixB2.Energy

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The abstract collapse lemma -/

/-- **`qform` over a window range containing the support collapses to the double sum
over the support.**  If the vector `g` vanishes outside `[0,n]` (`n : ℕ`) and the window
range `iRange N = [0,N−1]` contains `[0,n]`, then the sesquilinear form of `A` on `g`
over `iRange N` is the double sum over `[0,n]²`.

The hypothesis `hvan` is applied only through the two factors `star (g i)` and `g j`,
so no support condition on `A` is required. -/
lemma qform_iRange_eq_sum_Icc {N n : ℕ} (hN : (n : ℤ) ≤ ((N : ℕ) : ℤ) - 1)
    (A : ℤ → ℤ → ℂ) (g : ℤ → ℂ)
    (hvan : ∀ i : ℤ, i ∉ Finset.Icc (0 : ℤ) (n : ℤ) → g i = 0) :
    qform A (iRange N) g g
      = (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ),
          ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), star (g i) * A i j * g j).re := by
  simp only [qform, iRange]
  congr 1
  have hL := sum_Icc_congr_of_eq_zero_outside
    (fun i : ℤ => ∑ j ∈ Finset.Icc (0 : ℤ) ((N : ℤ) - 1), star (g i) * A i j * g j)
    (a := 0) (b := (N : ℤ) - 1) (c := 0) (d := (n : ℤ)) le_rfl hN
    (fun i hi => by simp [hvan i hi])
  refine hL.trans ?_
  exact Finset.sum_congr rfl (fun i _ =>
    sum_Icc_congr_of_eq_zero_outside (fun j : ℤ => star (g i) * A i j * g j)
      (a := 0) (b := (N : ℤ) - 1) (c := 0) (d := (n : ℤ)) le_rfl hN
      (fun j hj => by simp [hvan j hj]))

/-! ## 2. The profile vanishes outside the sector range -/

/-- The norm profile `gradePsi` vanishes outside the sector range `[0,n]` (the defining
guard, in membership form). -/
lemma gradePsi_eq_zero_of_not_mem {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} {i : ℤ}
    (hi : i ∉ Finset.Icc (0 : ℤ) (n : ℤ)) :
    gradePsi v h μ n (fsSide v μ) Φ i = 0 :=
  gradePsi_eq_zero_of_not v h μ n (fsSide v μ) Φ i (by simpa [Finset.mem_Icc] using hi)

/-! ## 3. The target -/

/-- **The `qform` of the graded box data is the sector double sum.**  The window range
`iRange (fsNn v μ n)` contains the sector range `[0,n]` and the profile `gradePsi`
vanishes outside it, so the two sums agree. -/
theorem qform_eq_double_sum {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} : Work.UBBInputs3.qform (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) = (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), star (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ i) * Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j * Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ j).re := by
  -- `n + 1 ≤ fsNn v μ n`, so `iRange (fsNn v μ n) = [0, fsNn−1]` contains `[0,n]`.
  have hN : (n : ℤ) ≤ ((fsNn v μ n : ℕ) : ℤ) - 1 := by
    have hnn : n + 1 ≤ fsNn v μ n := by
      rw [fsNn]
      exact succ_le_gradeNn n
    have h : ((n + 1 : ℕ) : ℤ) ≤ ((fsNn v μ n : ℕ) : ℤ) := by exact_mod_cast hnn
    push_cast at h ⊢
    linarith
  exact qform_iRange_eq_sum_Icc hN _ _
    (fun i hi => gradePsi_eq_zero_of_not_mem hi)

end Work.BoseFixB2.Energy
