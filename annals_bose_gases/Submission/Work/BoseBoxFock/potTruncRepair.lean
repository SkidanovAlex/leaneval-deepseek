import ChallengeDeps
import Submission.Work.BoseBoxFock.PotGroupAssembly
import Submission.Work.BoseBoxFock.PotGroupsIntegrable_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.potTruncRepair` — the lattice-cut-off (`Nmin`) repair of the potential half

## The defect (found by the holder of `PotChiLin_holds`, 10:32)

The four potential-group `Prop`s of `Work.BoseBoxFock.PotGroupDefs` carry the lattice cut-off
`Nmin : ℝ → ℕ` as a **free parameter**: their body is

    ∀ HM : ∀ μ, HonestModes v μ, (∀ μ, Nmin μ ≤ (HM μ).N) → …

so the node theorems `FormW2Bpot_holds`/`PotChiLin_holds`/… (`Nmin` a parameter, `∃ ε C` after it)
claim the rows for **every** mode family with `N ≥ Nmin μ`, in particular for the degenerate
families with `N = O(1)`.

That is false for the three groups whose rows contain **truncated lattice sums**
(`PotChiLin`, `PotPairRows`, `PotCubic`): the χ-mode sums of `potChiLin` are the partial sums of
the dual-lattice Fourier series, and the omitted tail `T_N = χ_Λ² − θ − Σ_{|m|_∞≤N}χ̂(2πm)qVec(k_m)`
is **non-zero for every `N`** (it vanishes iff χ is a trigonometric polynomial).  A state with one
excitation in the tail direction `T_N/‖T_N‖` therefore produces a row deficit of the order of the
row scale, while the only error slot `(1/2)·errKafz v R μ C·‖Φ‖²` is `o(1)` relative to that scale
as `t = μa³ → 0` — independently of `C`.  Full write-up and the counterexample family:
`Submission/Work/BoseBoxFock/FINDING_PotChiLin_holds_FALSE.md`.

The group `PotContactChem` uses **only** the condensate mode `e 0` (which the a.e. pinning fixes
exactly), so it has no truncation defect and its `∀Nmin`-form is the right (and true) statement.

## The repair

The truncated sums only have to beat the error for **large enough** `N`: `χ` is `C^∞` with compact
support, so `χ̂(2πm) = O(|m|^{-K})` for every `K`, and choosing the threshold
`Nmin μ ≍ (μa³)^{-1}` makes the tail super-polynomially small in `t`, i.e. below `errKafz`'s
polynomial slots (`t^{9/646}`, `t^{2/323}`, `t^{1/1615}`).  This is exactly FS's own device ("choose
the cube size `N(μ)` so that the tails are below the budget", `BOSE_BOXFOCK_LEAD.md` §2.3), and it
is *consistent with the frozen target*: `Work.BoseBoxFock.box_to_model` begins
`∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), …`, i.e. `Nmin` is ours to choose, and
`Work.BoseBoxFock.box_to_model_of_row` already consumes `hRow : ∃ Nmin ε₀ C, RowB … Nmin ε₀ C`.

So the repaired leaf statements are obtained by moving `Nmin` **inside** the existential:

    ∃ Nmin ε₀ C, 0 < ε₀ ∧ 0 ≤ C ∧ PotChiLin v h fc fu R J Nmin ε₀ C           (and similarly)

and the repaired assembly combines the four thresholds by the pointwise `max` — which is legitimate
because every group `Prop` is **antitone in `Nmin`** (`…_mono` below: a larger threshold makes the
hypothesis `∀ μ, Nmin μ ≤ (HM μ).N` stronger, hence the `Prop` weaker).

⚠ The same repair is **not** needed for the kinetic half: `FormRowKin`'s LHS is a sum of *positive*
terms (`τ̃_k ≥ 0` times norm squares, and the gap rows), so truncating the mode set only *decreases*
it — the `∀Nmin`-form of `FormRowKin` is the right one (this is
`FINDING_FormRowKin_holds.md` §1's "rapid decay / truncation only removes positive terms").

Everything here is `sorry`-free and proved.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. Every group `Prop` is antitone in the lattice cut-off `Nmin` -/

/-- A larger lattice threshold (the conclusion's `Nmin₁`) makes `PotContactChem` weaker. -/
theorem PotContactChem_mono {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin₁ Nmin₂ : ℝ → ℕ} {ε₀ C : ℝ}
    (hle : ∀ μ, Nmin₂ μ ≤ Nmin₁ μ)
    (hP : Work.BoseBoxFock.PotContactChem v h fc fu R J Nmin₂ ε₀ C) :
    Work.BoseBoxFock.PotContactChem v h fc fu R J Nmin₁ ε₀ C := by
  intro HM hN
  exact hP HM (fun μ => le_trans (hle μ) (hN μ))

/-- A larger lattice threshold makes `PotChiLin` weaker. -/
theorem PotChiLin_mono {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin₁ Nmin₂ : ℝ → ℕ} {ε₀ C : ℝ}
    (hle : ∀ μ, Nmin₂ μ ≤ Nmin₁ μ)
    (hP : Work.BoseBoxFock.PotChiLin v h fc fu R J Nmin₂ ε₀ C) :
    Work.BoseBoxFock.PotChiLin v h fc fu R J Nmin₁ ε₀ C := by
  intro HM hN
  exact hP HM (fun μ => le_trans (hle μ) (hN μ))

/-- A larger lattice threshold makes `PotPairRows` weaker. -/
theorem PotPairRows_mono {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin₁ Nmin₂ : ℝ → ℕ} {ε₀ C : ℝ}
    (hle : ∀ μ, Nmin₂ μ ≤ Nmin₁ μ)
    (hP : Work.BoseBoxFock.PotPairRows v h fc fu R J Nmin₂ ε₀ C) :
    Work.BoseBoxFock.PotPairRows v h fc fu R J Nmin₁ ε₀ C := by
  intro HM hN
  exact hP HM (fun μ => le_trans (hle μ) (hN μ))

/-- A larger lattice threshold makes `PotCubic` weaker. -/
theorem PotCubic_mono {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin₁ Nmin₂ : ℝ → ℕ} {ε₀ C : ℝ}
    (hle : ∀ μ, Nmin₂ μ ≤ Nmin₁ μ)
    (hP : Work.BoseBoxFock.PotCubic v h fc fu R J Nmin₂ ε₀ C) :
    Work.BoseBoxFock.PotCubic v h fc fu R J Nmin₁ ε₀ C := by
  intro HM hN
  exact hP HM (fun μ => le_trans (hle μ) (hN μ))

/-! ## 2. The repaired assembly: `FormW2Bpot` with the lattice cut-off *chosen* -/

/-- **`FormW2Bpot` from the four group statements with `Nmin` existentially chosen.**

The four group thresholds are combined by the pointwise `max` (legitimate by the `…_mono` lemmas),
the four error constants by their sum (legitimate because `errKafz` is linear in `C`), and the four
thresholds `ε₀` by `max`. -/
theorem FormW2Bpot_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (h0 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotContactChem v h fc fu R J Nmin ε₀ C)
    (h1 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotChiLin v h fc fu R J Nmin ε₀ C)
    (h2 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotPairRows v h fc fu R J Nmin ε₀ C)
    (h3 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotCubic v h fc fu R J Nmin ε₀ C) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FormW2Bpot v h fc fu R J Nmin ε₀ C := by
  obtain ⟨N0, ε0, C0, hε0, hC0, g0⟩ := h0
  obtain ⟨N1, ε1, C1, hε1, hC1, g1⟩ := h1
  obtain ⟨N2, ε2, C2, hε2, hC2, g2⟩ := h2
  obtain ⟨N3, ε3, C3, hε3, hC3, g3⟩ := h3
  let N : ℝ → ℕ := fun μ => max (max (N0 μ) (N1 μ)) (max (N2 μ) (N3 μ))
  have hN0 : ∀ μ, N0 μ ≤ N μ := fun μ => le_trans (le_max_left _ _) (le_max_left _ _)
  have hN1 : ∀ μ, N1 μ ≤ N μ := fun μ => le_trans (le_max_right _ _) (le_max_left _ _)
  have hN2 : ∀ μ, N2 μ ≤ N μ := fun μ => le_trans (le_max_left _ _) (le_max_right _ _)
  have hN3 : ∀ μ, N3 μ ≤ N μ := fun μ => le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨N, ?_⟩
  exact Work.BoseBoxFock.FormW2Bpot_of_potGroups v h hv hv1 hvrad hR hv_supp hav fc fu J hB3 N
      ⟨ε0, C0, hε0, hC0, PotContactChem_mono hN0 g0⟩
      ⟨ε1, C1, hε1, hC1, PotChiLin_mono hN1 g1⟩
      ⟨ε2, C2, hε2, hC2, PotPairRows_mono hN2 g2⟩
      ⟨ε3, C3, hε3, hC3, PotCubic_mono hN3 g3⟩
      (fun {ε₀} => Work.BoseBoxFock.PotGroupsIntegrable_holds v h hv hv1 hvrad hR hv_supp hav
        fc fu J hB3 N ε₀)

end Work.BoseBoxFock
