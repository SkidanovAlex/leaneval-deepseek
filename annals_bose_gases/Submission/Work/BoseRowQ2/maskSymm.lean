import ChallengeDeps
import Submission.Work.BoseB7AK.W1rows.chat_neg
import Submission.Work.BoseRowQ2.maskSharpMain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.maskSymm` — the symmetry bookkeeping of the sharp mask row

The Fock-level reduction of the sharp mask row (`besselOpMat_le_of_mat`, used in
`Submission/Work/BoseRowQ2/gchiAtMaskOfMatLe.lean`) needs the matrix
`(1+ε)·GchiF + γ·Dmask + δ·diag − GchiA` to be **symmetric**.  `GchiF` and `Dmask` are
manifestly symmetric sums of products; `GchiA` is not, because its kernel is
`fL s · fL s' · χ̂²(s'−s)` and the summation is over the *ordered* pairs `(s,s')`.  The
symmetry of `GchiA` therefore reduces to the evenness of the honest `χ̂²` as a function on
the mode lattice:

* `honE_hatChiSq_even` — `hatChiSq (−s) = hatChiSq s` (the honest `hatChiSq` unfolds to
  `chat (χ_ℓ²) (kmom ·) / chat (χ_ℓ²) 0`, `chat` is even and `kmom` is odd);
* `honE_hatChiSq_sub_comm` — `hatChiSq (s − t) = hatChiSq (t − s)`;
* `GchiA_symm`, `GchiF_symm`, `Dmask_symm` — the three symmetries.

Also here: `besselOpMat_diag_eq_totNumOp`, the identification of the `besselOpMat` of the
identity matrix with the honest total number operator (`tildeDataHon.N = totNumOp m`),
which is the piece of vocabulary the Fock reduction needs to read the `δ‖u‖²` slot of the
matrix inequality as `δ⟨N⟩`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB4 Work.BoseB7 Work.BoseB7A Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseRowsFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
  {fc fu : Work.BoseBoxFix.LowCut}

/-! ## 1. The honest `χ̂²` is even -/

/-- **The honest `hatChiSq` is even.**  `(honE)·hatChiSq k = chat (χ_ℓ²) (kmom k) / chat (χ_ℓ²) 0`
with `ℓ = sideAt μ (a v)`; `chat W` is even for every real `W` and `kmom` is odd. -/
theorem honE_hatChiSq_even (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (k : Lab (HM μ).N) :
    (honE v h fc fu HM μ).hatChiSq (-k) = (honE v h fc fu HM μ).hatChiSq k := by
  have hfun : (honE v h fc fu HM μ).hatChiSq
      = fun k => Work.BoseFixR.chat
          (fun z => Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z ^ 2)
          ((honF v h fc fu HM μ).kmom k)
        / Work.BoseFixR.chat
          (fun z => Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z ^ 2) 0 := by
    simp only [Work.BoseRowsFS.honE, Work.BoseRowsFS.honF, Work.BoseBoxFock.HonestBoxFam,
      Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs]
  simp only [hfun, (honF v h fc fu HM μ).kmom_neg k, Work.BoseB7AK.W1rows.chat_neg]

/-- **`hatChiSq (s − t) = hatChiSq (t − s)`** (a restatement of the evenness on the differences
of the lattice). -/
theorem honE_hatChiSq_sub_comm (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (s t : Lab (HM μ).N) :
    (honE v h fc fu HM μ).hatChiSq (s - t) = (honE v h fc fu HM μ).hatChiSq (t - s) := by
  rw [← honE_hatChiSq_even HM μ (s - t)]
  congr 1
  abel

/-! ## 2. The three symmetries -/

/-- **`GchiA` is symmetric.**  The kernel `fL s fL s' χ̂²(s'−s)` is symmetric in `(s,s')`
precisely because `χ̂²` is even; the remaining factor is `g s' l · g s l'` against
`g s l' · g s' l`, i.e. commutativity. -/
theorem GchiA_symm (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (l l' : Fin (HM μ).m) :
    GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l'
      = GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l' l := by
  simp only [GchiA]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  rw [honE_hatChiSq_sub_comm HM μ s s']
  ring

/-- **`GchiF` is symmetric** (`∑_k f k l · f k l'`). -/
theorem GchiF_symm (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (l l' : Fin (HM μ).m) :
    GchiF HM μ l l' = GchiF HM μ l' l := by
  simp only [GchiF]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **`Dmask` is symmetric** (`∑_{s∈excited} (1−fL s)² g s l g s l'`). -/
theorem Dmask_symm (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (l l' : Fin (HM μ).m) :
    Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l'
      = Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l' l := by
  simp only [Dmask]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The identity matrix as a `besselOpMat` is the honest total number operator.**  This is
the vocabulary that turns the `δ‖u‖²` slot of the one-body matrix inequality into the
`δ⟨N⟩` slot of `GchiAtMask` (`tildeDataHon.N = totNumOp m`). -/
theorem besselOpMat_diag_eq_totNumOp (m : ℕ) :
    besselOpMat m (fun l l' : Fin m => if l = l' then (1 : ℝ) else 0)
      = totNumOp m := by
  rw [besselOpMat, totNumOp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl, one_smul, modeNumOp]
  · intro l' _ hl'
    rw [if_neg (Ne.symm hl'), zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

end Work.BoseRowQ2
