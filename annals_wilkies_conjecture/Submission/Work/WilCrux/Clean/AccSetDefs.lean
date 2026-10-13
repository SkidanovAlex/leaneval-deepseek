/-
  `Work.WilCrux.Clean` — vocabulary for the accumulation-set lemma
  `Work.WilCrux.Clean.AccSetMem`.

  For `E ⊆ ℝ^{a+b}` the *accumulation set*

  `acc E = {w : ℝ^a | ∀ δ > 0, ∃ z : ℝ^b, 0 < ‖z‖ ∧ ‖z‖ < δ ∧ (w,z) ∈ E}`

  is supposed to be `Ω`-definable.  The proof works in `ℝ^{(a+1)+b}` with coordinates
  `(w, δ, z)` and uses the auxiliary `Ω`-set `Qset a b E`:

  * `iIdx a b : Fin (a+b) → Fin ((a+1)+b)` embeds the coordinates `(w,z)` of `ℝ^{a+b}` as the
    `w`-block (first `a` coordinates) and the `z`-block (last `b` coordinates) of
    `ℝ^{(a+1)+b}`, skipping the distinguished coordinate `δ = x (dIdx a b)`;
  * `Qset a b E` is the pullback of `E` along `iIdx`, intersected with `δ > 0`, `z ≠ 0` and
    `|z j| < δ` (for `b ≥ 1` the last condition is `‖z‖ < δ`; the conjunct `δ > 0` is carried
    along so that `Qset` is `Ω`-definable for every `b`).

  With `J = projN b (Qset a b E) ⊆ ℝ^{a+1}` the set of pairs `(w,δ)` for which some `z` works,
  the accumulation set is `(projLast (Jᶜ ∩ {δ > 0}))ᶜ`: a point `w` fails the accumulation
  condition exactly when *some* `δ > 0` admits *no* `z`, and the two quantifiers are absorbed
  as a projection after a complement.

  The main theorems of this file are `Qset_mem` (in `AccSetMem.lean`) and `mem_Qset`.
-/
import Mathlib
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilCrux.TripleMem

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilCrux.Clean

open WilkiesDesign WilkiesConjecture

/-! ## 1. The coordinates of `ℝ^{(a+1)+b}` and the embedding `iIdx` -/

/-- The coordinate of the `j`-th fibre variable `z j` in `ℝ^{(a+1)+b}`. -/
def zIdx (a b : ℕ) (j : Fin b) : Fin ((a + 1) + b) := Fin.natAdd (a + 1) j

/-- The coordinate of `δ` in `ℝ^{(a+1)+b}`. -/
def dIdx (a b : ℕ) : Fin ((a + 1) + b) := Fin.castAdd b (Fin.last a)

/-- The map embedding the coordinates `(w,z)` of `ℝ^{a+b}` into `ℝ^{(a+1)+b}` as the `w`-block
(first `a` coordinates) followed by the `z`-block (last `b` coordinates). -/
def iIdx (a b : ℕ) : Fin (a + b) → Fin ((a + 1) + b) :=
  Fin.addCases (fun i : Fin a => Fin.castAdd b (Fin.castSucc i)) (fun j : Fin b => zIdx a b j)

@[simp] theorem iIdx_castAdd (a b : ℕ) (i : Fin a) :
    iIdx a b (Fin.castAdd b i) = Fin.castAdd b (Fin.castSucc i) := by
  simp only [iIdx, Fin.addCases_left]

@[simp] theorem iIdx_natAdd (a b : ℕ) (j : Fin b) :
    iIdx a b (Fin.natAdd a j) = zIdx a b j := by
  simp only [iIdx, Fin.addCases_right]

/-! ## 2. The point `Fin.append (Fin.snoc w t) z` -/

/-- The `δ`-coordinate of `Fin.append (Fin.snoc w t) z` is `t`. -/
@[simp] theorem append_snoc_dIdx (a b : ℕ) (w : Fin a → ℝ) (t : ℝ) (z : Fin b → ℝ) :
    Fin.append (Fin.snoc w t) z (dIdx a b) = t := by
  simp only [dIdx, Fin.append_left, Fin.snoc_last]

/-- The `z`-block of `Fin.append (Fin.snoc w t) z` is `z`. -/
@[simp] theorem append_snoc_zIdx (a b : ℕ) (w : Fin a → ℝ) (t : ℝ) (z : Fin b → ℝ) (j : Fin b) :
    Fin.append (Fin.snoc w t) z (zIdx a b j) = z j := by
  simp only [zIdx, Fin.append_right]

/-- Pulling back `Fin.append (Fin.snoc w t) z` along `iIdx` gives `Fin.append w z`. -/
theorem append_snoc_comp_iIdx (a b : ℕ) (w : Fin a → ℝ) (t : ℝ) (z : Fin b → ℝ) :
    (fun i : Fin (a + b) => Fin.append (Fin.snoc w t) z (iIdx a b i)) = Fin.append w z := by
  funext i
  induction i using Fin.addCases with
  | left i' => simp only [iIdx_castAdd, Fin.append_left, Fin.snoc_castSucc]
  | right j => simp only [iIdx_natAdd, zIdx, Fin.append_right]

/-! ## 3. The auxiliary `Ω`-set `Qset` -/

/-- The auxiliary set in `ℝ^{(a+1)+b}` with coordinates `(w, δ, z)`: `(w,z) ∈ E`, `δ > 0`,
`z ≠ 0` and `|z j| < δ` for all `j`. -/
def Qset (a b : ℕ) (E : Set (Fin (a + b) → ℝ)) : Set (Fin ((a + 1) + b) → ℝ) :=
  {x | x ∘ iIdx a b ∈ E} ∩ {x | 0 < x (dIdx a b)} ∩
    ({x | (fun j : Fin b => x (zIdx a b j)) ≠ 0} ∩
      {x | ∀ j : Fin b, |x (zIdx a b j)| < x (dIdx a b)})

/-! ## 4. Generic `Ω`-bookkeeping used by the assembly -/

/-- Binary intersection of two `Ω`-sets: the format is the maximum plus one, the degrees add. -/
theorem inter2_mem {S : SOMin} {F₁ F₂ D₁ D₂ n : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω F₁ D₁ n) (hY : Y ∈ S.Ω F₂ D₂ n) :
    X ∩ Y ∈ S.Ω (max F₁ F₂ + 1) (D₁ + D₂) n := by
  have h1 : X ∈ S.Ω (max F₁ F₂) D₁ n := Work.WilG5.mem_mono hX _ _ (le_max_left _ _) le_rfl
  have h2 : Y ∈ S.Ω (max F₁ F₂) D₂ n := Work.WilG5.mem_mono hY _ _ (le_max_right _ _) le_rfl
  have h := S.inter (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by intro i; fin_cases i
        · simpa using h1
        · simpa using h2)
  rw [show (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ from by
    rw [Fin.sum_univ_two]; norm_num] at h
  rwa [Work.WilG4a.iInter_fin_two X Y] at h

end Work.WilCrux.Clean
