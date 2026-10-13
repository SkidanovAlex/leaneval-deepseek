import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.DzFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstar_slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-!
# `fstarDat` --- the datum package for the fundamental profile `F_*`

This is the `ℱ`-side input of the level-six `N`-row: the three fields `F_*`, `D_θF_*`, `D_zF_*`
are `C^∞` on the open quadrant, their `𝒲^{6,∞}`-membership holds with norms `≤ Cα`, and every
slot `D_z^jD_θ^i` (`j + i ≤ 6`) obeys the *flat* pointwise price

  `|D_z^jD_θ^i F| ≤ Cα·z/(1+z)² · (1 if i = 0 else sin(2θ)^{α/3})`.

## Route

The pieces are already available, so the lemma is an assembly:

* `H6Pair6Aux.smoothOpen_Fstar` (with `SmoothOpen.Dth`, `SmoothOpen.Dz`) gives the three
  smoothness clauses (no hypothesis on `α`);
* `StrongPersist.Fstar_W6`, `StrongPersist.DthFstar_W6`, `StrongPersist.DzFstar_W6` give the
  `WlInfMem`/`WlInf` clauses (the `D_θ`-one with `α²`, which is `≤ α` since `α ≤ 1`);
* the pointwise clauses are `FS.G0_le`/`FS.G0_le_sin`, `FS.G1_le`/`FS.G1_le_sin`,
  `FS.G2_le`/`FS.G2_le_sin` from `fstar_slots` (where `F_* = c₀·(Γ ⊗ φ)`, `φ = z/(1+z)²`,
  `Γ = (sinθcos²θ)^{α/3}` and the `sin(2θ)^{α/3}` gain comes from `Γ ≤ sin(2θ)^{α/3}`).
-/

/-- The `i = 0` shape of the pointwise bound: the angular factor is `1`. -/
private lemma fd_plain_le {X a A α Hz : ℝ} (h : X ≤ a * α * Hz) (haA : a ≤ A) (hα : 0 ≤ α)
    (hHz : 0 ≤ Hz) : X ≤ A * α * Hz * 1 := by
  calc X ≤ a * α * Hz := h
    _ = a * (α * Hz) := by ring
    _ ≤ A * (α * Hz) := mul_le_mul_of_nonneg_right haA (mul_nonneg hα hHz)
    _ = A * α * Hz * 1 := by ring

/-- The `i ≥ 1` shape of the pointwise bound: the extra angular factor is
`sin(2θ)^{α/3}`. -/
private lemma fd_sin_le {X a A α Hz s : ℝ} (h : X ≤ a * α * s * Hz) (haA : a ≤ A) (hα : 0 ≤ α)
    (hs : 0 ≤ s) (hHz : 0 ≤ Hz) : X ≤ A * α * Hz * s := by
  calc X ≤ a * α * s * Hz := h
    _ = a * (α * (s * Hz)) := by ring
    _ ≤ A * (α * (s * Hz)) := mul_le_mul_of_nonneg_right haA (mul_nonneg hα (mul_nonneg hs hHz))
    _ = A * α * Hz * s := by ring

theorem fstarDat : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) ∧
    Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ C * α ∧
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ∧
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α ∧
    (∀ (A : Work.FTS.Galerkin.Fn),
        (A = Work.Construction.Fstar α ∨ A = Work.Spaces.Dth (Work.Construction.Fstar α) ∨
         A = Work.Spaces.Dz (Work.Construction.Fstar α)) →
        ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ C * α * (z / (1 + z) ^ 2) *
            (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨C3, hC3pos, hC3⟩ := Work.FTS.StrongPersist.DzFstar_W6
  set C : ℝ := max C1 (max C2 (max C3 FS.Cst)) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC1le : C1 ≤ C := by
    rw [hCdef]
    have h := le_max_left C1 (max C2 (max C3 FS.Cst))
    linarith
  have hC2le : C2 ≤ C := by
    rw [hCdef]
    have h1 := le_max_left C2 (max C3 FS.Cst)
    have h2 := le_max_right C1 (max C2 (max C3 FS.Cst))
    linarith
  have hC3le : C3 ≤ C := by
    rw [hCdef]
    have h1 := le_max_left C3 FS.Cst
    have h2 := le_max_right C2 (max C3 FS.Cst)
    have h3 := le_max_right C1 (max C2 (max C3 FS.Cst))
    linarith
  have hCstle : FS.Cst ≤ C := by
    rw [hCdef]
    have h1 := le_max_right C3 FS.Cst
    have h2 := le_max_right C2 (max C3 FS.Cst)
    have h3 := le_max_right C1 (max C2 (max C3 FS.Cst))
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  obtain ⟨hwFmem, hwFle⟩ := hC1 α hα hα1
  obtain ⟨hwDmem, hwDle⟩ := hC2 α hα hα1
  obtain ⟨hwZmem, hwZle⟩ := hC3 α hα hα1
  refine ⟨?_, ?_, ?_, hwFmem, ?_, hwDmem, ?_, hwZmem, ?_, ?_⟩
  · exact Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz
  · exact le_trans hwFle (mul_le_mul_of_nonneg_right hC1le hα.le)
  · refine le_trans hwDle ?_
    calc C2 * α ^ 2 ≤ C * α ^ 2 := mul_le_mul_of_nonneg_right hC2le (sq_nonneg α)
      _ ≤ C * α := mul_le_mul_of_nonneg_left (by nlinarith [hα.le, hα1]) hCpos.le
  · exact le_trans hwZle (mul_le_mul_of_nonneg_right hC3le hα.le)
  · intro A hA j i hji z θ hz hθ0 hθ2
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hHz : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz.le (sq_nonneg (1 + z))
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ (α / 3) := FS.sin_rpow_nonneg hθ
    rcases hA with rfl | rfl | rfl
    · by_cases hi : 1 ≤ i
      · rw [if_pos hi]
        have h := FS.G0_le_sin hα hα1 hi hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_sin_le h hCstle hα.le hs hHz
      · rw [if_neg hi]
        have h := FS.G0_le hα hα1 hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_plain_le h hCstle hα.le hHz
    · by_cases hi : 1 ≤ i
      · rw [if_pos hi]
        have h := FS.G1_le_sin hα hα1 hi hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_sin_le h hCstle hα.le hs hHz
      · rw [if_neg hi]
        have h := FS.G1_le hα hα1 hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_plain_le h hCstle hα.le hHz
    · by_cases hi : 1 ≤ i
      · rw [if_pos hi]
        have h := FS.G2_le_sin hα hα1 hi hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_sin_le h hCstle hα.le hs hHz
      · rw [if_neg hi]
        have h := FS.G2_le hα hα1 hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_plain_le h hCstle hα.le hHz

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
