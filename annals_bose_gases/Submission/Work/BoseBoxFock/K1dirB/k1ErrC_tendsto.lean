import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1dirB.k1RowCut_sub_lim_uniform
import Submission.Work.BoseBoxFock.K1dirB.pinQCl_add_int
import Submission.Work.BoseBoxFock.K1dirBDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.k1ErrC_tendsto` — the third `χ̂`-row error is uniformly small

**Statement.**  For every `ε > 0` there is `N₀` with

    ‖k1ErrC v μ fu N Wa Wb y‖ ≤ ε      for all `N ≥ N₀` and all `y : ℝ³`,

where `k1ErrC v μ fu N Wa Wb = pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) −
pinQCl (ellH v μ) (Wa + Wb)` is the third row error (`χθ`) of the `K1exp`/`K1lim` comparison
(`Submission.Work.BoseBoxFock.K1pairingDefs`), under the *only* hypothesis that `Wa`, `Wb` are
integrable.

## Route

The `χ̂`-rows `pinQC`/`pinQCl` are *absolutely* convergent lattice series, so no oscillation
control is needed — this is the sibling `k1ErrB_tendsto` with the *conjugate* phase
`e^{-i⟪κ,y⟫}` in place of `e^{+i⟪κ,w⟫}`.

* `k1pinQC_split` rewrites the truncated sum as the `θχ`-row
  `pinQC … = k1RowCutM ℓ fu N (k1ChiHatWt ℓ Wa) + k1RowM ℓ N (k1ChiHatWt ℓ Wb)`
  (`ℓ = ellH v μ`), the first factor carrying the cut;
* `chat` is additive in its kernel on integrable kernels
  (`Work.BoseRowsFS.CoulBilin.chat_add`), whence
  `pinQCl ℓ (Wa + Wb) y = pinQCl ℓ Wa y + pinQCl ℓ Wb y` — the delegated corpus lemma
  `pinQCl_add_int` below — and `pinQCl ℓ W` is *definitionally* the limit row
  `k1RowLimM ℓ (k1ChiHatWt ℓ W)`;
* the mirror rows are the rows at `−y` (`k1RowCutM_eq`, `k1RowM_eq`, `k1RowLimM_eq`), so

      k1ErrC = (k1RowCut − k1RowLim) [the `Wa`/cut piece] + (k1Row − k1RowLim) [the `Wb` piece]

  at the point `−y`, and each piece is *uniformly* small in the position variable:

  - `k1Row_tendsto` (proved) — the truncated row converges to its `tsum` uniformly;
  - `k1RowCut_sub_lim_uniform` (proved) — the cut row converges to the limit row uniformly: the
    cut differs from the un-cut row only on the lattice ball of radius `N/4`, whose tail is
    arbitrarily small by `k1BallTail_le`/`k1BallTail_mono`.

The weight `k1ChiHatWt ℓ W n = Ŵ(kmomInt ℓ n)·χ̂(ℓ • kmomInt ℓ n)` has order-`52` lattice decay
for **every** `W` (`k1ChiHatWt_majorant`: `|Ŵ|` is bounded by the `L¹` mass `∫|W|`, and `χ̂`
decays at order `52`), which is exactly the majorant the lattice-tail statements consume.  No
boundedness, measurability or compact-support hypothesis on `Wa`, `Wb` is used — in particular
the family `k1ChiHatWt ℓ W` is defined for every `W` and its majorant `k1ChiHatWt_majorant` needs
no hypothesis on `W`.

Every declaration below is proved from the imported corpus lemmas, with no unproved
placeholder.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.K1dirB

open Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. The limit row of the `χ̂`-weight -/

/-- The limit row `pinQCl` is *definitionally* the limit lattice row of the `χ̂`-weight. -/
private lemma pinQCl_eq_k1RowLimM (ℓ : ℝ) (W : E3 → ℝ) (y : E3) :
    pinQCl ℓ W y = k1RowLimM ℓ (k1ChiHatWt ℓ W) y := rfl

/-! ## 2. The pair row `(cut + row) − (limit + limit)` is uniformly small -/

private lemma pairRow_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    {Fa Fb : (Fin 3 → ℤ) → ℂ}
    (hFa : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fa n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)
    (hFb : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fb n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : E3,
      ‖(k1RowCut ℓ fu N' Fa z + k1Row ℓ N' Fb z)
        - (k1RowLim ℓ Fa z + k1RowLim ℓ Fb z)‖ ≤ ε := by
  intro ε hε
  obtain ⟨Na, ha⟩ := k1RowCut_sub_lim_uniform hℓ fu hFa (ε / 2) (by linarith)
  obtain ⟨Nb, hb⟩ := k1Row_tendsto hℓ hFb (ε / 2) (by linarith)
  refine ⟨max Na Nb, fun N' hN' z => ?_⟩
  have ha' := ha N' (le_trans (le_max_left _ _) hN') z
  have hb' := hb N' (le_trans (le_max_right _ _) hN') z
  calc ‖(k1RowCut ℓ fu N' Fa z + k1Row ℓ N' Fb z)
        - (k1RowLim ℓ Fa z + k1RowLim ℓ Fb z)‖
      = ‖(k1RowCut ℓ fu N' Fa z - k1RowLim ℓ Fa z)
          + (k1Row ℓ N' Fb z - k1RowLim ℓ Fb z)‖ := by
        congr 1; ring
    _ ≤ ‖k1RowCut ℓ fu N' Fa z - k1RowLim ℓ Fa z‖
          + ‖k1Row ℓ N' Fb z - k1RowLim ℓ Fb z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add ha' hb'
    _ = ε := by ring

/-! ## 3. The error as a pair of lattice rows -/

/-- **The third `χ̂`-row error is a pair of lattice rows.**  With `ℓ = ellH v μ`, `k1ErrC v μ fu N
Wa Wb y` is the difference of the truncated pair row and the limit pair row of the weights
`k1ChiHatWt ℓ Wa` (cut) and `k1ChiHatWt ℓ Wb` (un-cut), evaluated at `−y`. -/
private lemma k1ErrC_eq_pairRow {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut)
    {Wa Wb : E3 → ℝ} (hIa : MeasureTheory.Integrable Wa) (hIb : MeasureTheory.Integrable Wb)
    (N : ℕ) (y : E3) :
    k1ErrC v μ fu N Wa Wb y
      = (k1RowCut (ellH v μ) fu N (k1ChiHatWt (ellH v μ) Wa) (-y)
          + k1Row (ellH v μ) N (k1ChiHatWt (ellH v μ) Wb) (-y))
        - (k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wa) (-y)
          + k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wb) (-y)) := by
  unfold k1ErrC
  rw [k1pinQC_split fu N y,
    pinQCl_add_int (ellH_pos v μ) hIa hIb y,
    pinQCl_eq_k1RowLimM, pinQCl_eq_k1RowLimM,
    k1RowCutM_eq, k1RowM_eq, k1RowLimM_eq, k1RowLimM_eq]

/-! ## 4. The target -/

theorem k1ErrC_tendsto {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut)
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ} (hWai : MeasureTheory.Integrable Wa)
    (hWbi : MeasureTheory.Integrable Wb) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.k1ErrC v μ fu N Wa Wb y‖ ≤ ε := by
  intro ε hε
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨N, hN⟩ := pairRow_uniform hℓ fu (k1ChiHatWt_majorant hℓ Wa)
    (k1ChiHatWt_majorant hℓ Wb) ε hε
  refine ⟨N, fun N' hN' y => ?_⟩
  rw [k1ErrC_eq_pairRow fu hWai hWbi N' y]
  exact hN N' hN' (-y)

end Work.BoseBoxFock.K1dirB
