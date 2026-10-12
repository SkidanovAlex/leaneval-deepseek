import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.maskSymm

/-!
# `Work.BoseRowQ2.gchiAtMaskOfMatLe` — the Fock-level reduction of the sharp mask row

FS l.3253 (`hGchi`, the sharp mask form) is a **one-body** statement: the operator inequality

    `Gop ⪯ (1+ε)·Σ_k a_k†a_k + ((1+1/ε)Cχ)·maskNum + δ·N`

on the honest Fock space.  Because the honest model represents every operator in play as
`besselOpMat` of a `Fin m × Fin m` matrix (`GchiIdentify.lean`:

    `Gop = besselOpMat (GchiA)`,  `allNumOp = besselOpMat (GchiF)`,
    `maskNum = besselOpMat (Dmask)`,  `N = besselOpMat (diag)`),

the Fock-level inequality follows from the *matrix* inequality
(`besselOpMat_le_of_mat`, `GchiReduction.lean`) as soon as the matrix difference

    `B := (1+ε)·GchiF + δ·diag + ((1+1/ε)Cχ)·Dmask − GchiA`

is symmetric and positive semidefinite on `Fin m → ℝ`.  This module proves that reduction:
`gchiAtMaskOfMatLe` is *exactly* the statement that the one-body matrix inequality

    `∀ u, ⟨u, GchiA u⟩ ≤ (1+ε)⟨u, GchiF u⟩ + ((1+1/ε)Cχ)⟨u, Dmask u⟩ + δ‖u‖²`

implies `GchiAtMask Cχ δ HM μ ε`.  The analytic content (the proof of the matrix
inequality, i.e. the smooth-mask estimate `GchiA ⪯ (1+ε)GchiF + γ·Dmask + δ·1`) is
*not* here; it is the input hypothesis `hmat`.

The ingredients used are the symmetries of the three matrices and of the diagonal
(`maskSymm.lean`: `GchiA_symm`, `GchiF_symm`, `Dmask_symm`, `besselOpMat_diag_eq_totNumOp`).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB4 Work.BoseB7 Work.BoseB7A Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseRowsFS

set_option linter.unusedVariables false

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
  {fc fu : Work.BoseBoxFix.LowCut}

/-! ## 1. The quadratic form of a matrix, and its additivity

The one-body matrix inequality is a statement about the quadratic form
`u ↦ ∑_i ∑_j u_i M_{ij} u_j`.  The three elementary rules below (additivity,
homogeneity, and the diagonal) are what turns the *sum* matrix
`(1+ε)·GchiF + δ·diag + γ·Dmask − GchiA` into the combination of the three quadratic
forms appearing in the hypothesis `hmat`. -/

/-- Additivity/homogeneity/diagonality of the quadratic form of a matrix, in the exact shape
in which the row's matrices are combined:
`⟨u, ((c·M + e·N) + g·D − A) u⟩ = c⟨u,Mu⟩ + e⟨u,Nu⟩ + g⟨u,Du⟩ − ⟨u,Au⟩`. -/
lemma gchi_quad_combined {m : ℕ} (M N D A : Fin m → Fin m → ℝ) (c e g : ℝ) (u : Fin m → ℝ) :
    (∑ i, ∑ j, u i * ((c * M i j + e * N i j) + g * D i j - A i j) * u j)
      = c * (∑ i, ∑ j, u i * M i j * u j) + e * (∑ i, ∑ j, u i * N i j * u j)
        + g * (∑ i, ∑ j, u i * D i j * u j) - (∑ i, ∑ j, u i * A i j * u j) := by
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form of the identity matrix: `∑_i ∑_j u_i δ_{ij} u_j = ∑_i u_i²`. -/
lemma gchi_quad_diag {m : ℕ} (u : Fin m → ℝ) :
    (∑ i, ∑ j, u i * (if i = j then (1 : ℝ) else 0) * u j) = ∑ i, (u i) ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [if_true, mul_one]; ring
  · intro j _ hj
    rw [if_neg (Ne.symm hj)]; ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ## 2. The operator identities at the mask matrices -/

/-- **`besselOpMat ((1+ε)·GchiF + δ·1) = (1+ε)·allNumOp + δ·N`.**  The `δ·1` slot of the matrix
inequality becomes `δ·N` at the operator level, where `N = totNumOp m` is the honest total
number operator. -/
theorem gchi_besselOpMat_masked (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (ε δ : ℝ) :
    besselOpMat (HM μ).m
        (fun l l' : Fin (HM μ).m => (1 + ε) * GchiF HM μ l l' + δ * (if l = l' then (1 : ℝ) else 0))
      = (1 + ε) • (honF v h fc fu HM μ).allNumOp + δ • (honT v h fc fu HM μ).N := by
  rw [show (fun l l' : Fin (HM μ).m => (1 + ε) * GchiF HM μ l l' + δ * (if l = l' then (1 : ℝ) else 0))
        = (1 + ε) • GchiF HM μ + δ • (fun l l' : Fin (HM μ).m => if l = l' then (1 : ℝ) else 0) from by
      funext l l'; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]]
  rw [besselOpMat_add, besselOpMat_smul, besselOpMat_smul,
    besselOpMat_GchiF (v := v) (h := h) (fc := fc) (fu := fu) HM μ,
    besselOpMat_diag_eq_totNumOp]
  rfl

/-- **`besselOpMat (γ·Dmask) = γ·maskNum`** — the mask-complement slot. -/
theorem gchi_besselOpMat_Dmask_smul (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (γ : ℝ) :
    besselOpMat (HM μ).m
        (fun l l' : Fin (HM μ).m => γ * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l')
      = γ • (honT v h fc fu HM μ).maskNum (honE v h fc fu HM μ) := by
  rw [show (fun l l' : Fin (HM μ).m => γ * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l')
        = γ • Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ from by
      funext l l'; simp only [Pi.smul_apply, smul_eq_mul]]
  rw [besselOpMat_smul, besselOpMat_Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ]
  rfl

/-! ## 3. The reduction -/

theorem gchiAtMaskOfMatLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (Cχ δ : ℝ)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hmat : ∀ u : Fin (HM μ).m → ℝ,
      (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
          u l * Work.BoseRowQ2.GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
        ≤ (1 + ε) * (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
            u l * Work.BoseRowQ2.GchiF HM μ l l' * u l')
          + ((1 + 1 / ε) * Cχ) * (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
              u l * Work.BoseRowQ2.Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
          + δ * (∑ l : Fin (HM μ).m, (u l) ^ 2)) :
    Work.BoseRowQ2.GchiAtMask (v := v) (h := h) (fc := fc) (fu := fu) Cχ δ HM μ ε := by
  intro Ψ
  -- the matrix `B + C - A` of `besselOpMat_le_of_mat`, entrywise
  have hsym : ∀ i j : Fin (HM μ).m,
      ((1 + ε) * GchiF HM μ i j + δ * (if i = j then (1 : ℝ) else 0))
        + ((1 + 1 / ε) * Cχ) * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ i j
        - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ i j
      = ((1 + ε) * GchiF HM μ j i + δ * (if j = i then (1 : ℝ) else 0))
        + ((1 + 1 / ε) * Cχ) * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ j i
        - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ j i := by
    intro i j
    rw [GchiF_symm HM μ i j, Dmask_symm HM μ i j, GchiA_symm HM μ i j]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  -- its positive semidefiniteness is exactly the hypothesis
  have hquad : ∀ u : Fin (HM μ).m → ℝ,
      0 ≤ ∑ i : Fin (HM μ).m, ∑ j : Fin (HM μ).m,
          u i * (((1 + ε) * GchiF HM μ i j + δ * (if i = j then (1 : ℝ) else 0))
            + ((1 + 1 / ε) * Cχ) * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ i j
            - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ i j) * u j := by
    intro u
    have hsplit := gchi_quad_combined (M := GchiF HM μ)
      (N := fun l l' : Fin (HM μ).m => if l = l' then (1 : ℝ) else 0)
      (D := Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
      (A := GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
      (c := 1 + ε) (e := δ) (g := (1 + 1 / ε) * Cχ) u
    have hdiag := gchi_quad_diag u
    rw [hsplit, hdiag]
    linarith [hmat u]
  have key := besselOpMat_le_of_mat (m := (HM μ).m)
    (A := GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
    (B := fun l l' : Fin (HM μ).m =>
      (1 + ε) * GchiF HM μ l l' + δ * (if l = l' then (1 : ℝ) else 0))
    (C := fun l l' : Fin (HM μ).m =>
      ((1 + 1 / ε) * Cχ) * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l')
    hsym hquad Ψ
  rw [gchi_besselOpMat_masked (v := v) (h := h) (fc := fc) (fu := fu) HM μ ε δ,
    gchi_besselOpMat_Dmask_smul (v := v) (h := h) (fc := fc) (fu := fu) HM μ ((1 + 1 / ε) * Cχ),
    besselOpMat_GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ] at key
  -- the same inequality in `qw` form (the structure-level quadratic form; the two spellings
  -- are definitionally equal, `qw Ψ X = bomb m (X Ψ) Ψ`)
  have key2 : (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
      ≤ (honF v h fc fu HM μ).qw Ψ
          ((1 + ε) • (honF v h fc fu HM μ).allNumOp + δ • (honT v h fc fu HM μ).N)
        + (honF v h fc fu HM μ).qw Ψ
          (((1 + 1 / ε) * Cχ) • (honT v h fc fu HM μ).maskNum (honE v h fc fu HM μ)) := key
  -- split the RHS by linearity of `qw` in the operator
  rw [Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_smul,
    Work.BoseB7.FockData.qw_smul, Work.BoseB7.FockData.qw_smul] at key2
  linarith [key2]

end Work.BoseRowQ2
