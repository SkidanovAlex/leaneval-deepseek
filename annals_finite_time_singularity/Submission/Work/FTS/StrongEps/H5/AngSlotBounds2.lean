import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux
import Submission.Work.FTS.StrongEps.H5.SA2Def
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# Angular slot bounds for the three `F_*`-angular profiles

This file proves `AngSlotBounds2`: for every `α ∈ (0,1]` there are constants `B0, B1 > 0` with
`|SAi α θ| ≤ B0` on `Iθ` and `|D_θ^j (SAi α ·)|(0,θ)| ≤ B1 · SGmj α θ` on `Iθ`, where
`SA0 α = αΓ/c`, `SA1 α = α D_θΓ/c` and `SA2 α = α D_θ²Γ/c` are the three angular profiles of
the scaled `F_*`-atoms and `SGmj α θ = Γ(θ)(α + sin 2θ)`.

Everything rests on the crude angular-jet bound `DthIter_Gam_abs_le6`
(`|D_θ^m Γ| ≤ 10⁵ Γ` for `m ≤ 6`), the majorant inequality `Γ ≤ SGmj/α` on `Iθ`, and
`c_bounds` (`1/10 ≤ c(α) ≤ 10`).  Concretely `B0 = B1 = 10⁶` works: the factor `α/c ≤ 10α`
supplies the `α` that is `≤ α + sin 2θ`, and the remaining `10⁶ Γ` is `≤ 10⁶ Γ(α + sin 2θ)`.
-/

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
lemma AngSlot_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- The `D_θ`-iterates of the `θ`-only function `SA0 α` are `(α/c)` times those of `Γ`. -/
lemma DthIter_SA0_repr' (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.FTS.StrongEps.ClassCRHS.SA0 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => Work.FTS.StrongEps.ClassCRHS.SA0 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.FTS.StrongEps.ClassCRHS.SA0 α θ') z θ,
    hfun, Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (fun s => Work.Spaces.Gam α s)]

/-- The `D_θ`-iterates of `SA1 α = (α/c) D_θΓ` are `(α/c)` times those of `Γ`, shifted by one. -/
lemma DthIter_SA1_repr' (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.FTS.StrongEps.ClassCRHS.SA1 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => Work.FTS.StrongEps.ClassCRHS.SA1 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α)
          * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.FTS.StrongEps.ClassCRHS.SA1 α θ') z θ,
    hfun, Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (Work.Spaces.dthU (fun s => Work.Spaces.Gam α s)),
    Work.Spaces.dthU_iter_comp i (fun s => Work.Spaces.Gam α s)]

/-- The `D_θ`-iterates of `SA2 α = (α/c) D_θ²Γ` are `(α/c)` times those of `Γ`, shifted by two. -/
lemma DthIter_SA2_repr' (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.FTS.StrongEps.H5.SA2 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 2] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => Work.FTS.StrongEps.H5.SA2 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α)
          * Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.FTS.StrongEps.H5.SA2 α θ') z θ, hfun,
    Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s))]
  rw [← Function.iterate_add_apply]

/-- **The pointwise bound `|(α/c)·D_θ^mΓ| ≤ 10⁶`** for `m ≤ 6` on `Iθ`. -/
lemma AngProfAbsLe' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {m : ℕ} (hm : m ≤ 6) :
    |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 10 ^ 6 := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]; nlinarith [hc.1, hα]
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hjet : |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    rw [← Work.FTS.LocData.DthIter_rad_eq m (fun t => Work.Spaces.Gam α t) 0 θ]
    exact Work.FTS.LocData6.DthIter_Gam_abs_le6 m hm α hα hα1 hθ
  have hnn : 0 ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hG.1]
  calc |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      = (α / Work.Spaces.c α) * |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| := by
        rw [abs_mul, abs_of_nonneg hdc]
    _ ≤ (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hjet hdc
    _ ≤ (10 * α) * (100000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_right hdiv hnn
    _ = 10 ^ 6 * (α * Work.Spaces.Gam α θ) := by ring
    _ ≤ 10 ^ 6 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa using mul_le_mul hα1 hG.2 hG.1 (by norm_num : (0 : ℝ) ≤ 1)
    _ = 10 ^ 6 := by norm_num

/-- **The pointwise jet bound `|(α/c)·D_θ^mΓ| ≤ 10⁶·SGmj α θ`** for `m ≤ 6` on `Iθ`. -/
lemma AngProfJetLe' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {m : ℕ} (hm : m ≤ 6) :
    |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 10 ^ 6 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]; nlinarith [hc.1, hα]
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hsin := AngSlot_sin_two_nonneg hθ
  have hjet : |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    rw [← Work.FTS.LocData.DthIter_rad_eq m (fun t => Work.Spaces.Gam α t) 0 θ]
    exact Work.FTS.LocData6.DthIter_Gam_abs_le6 m hm α hα hα1 hθ
  have hnn : 0 ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hG.1]
  calc |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      = (α / Work.Spaces.c α) * |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| := by
        rw [abs_mul, abs_of_nonneg hdc]
    _ ≤ (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hjet hdc
    _ ≤ (10 * α) * (100000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_right hdiv hnn
    _ = 10 ^ 6 * (α * Work.Spaces.Gam α θ) := by ring
    _ ≤ 10 ^ 6 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc α * Work.Spaces.Gam α θ ≤ (α + Real.sin (2 * θ)) * Work.Spaces.Gam α θ :=
              mul_le_mul_of_nonneg_right (by linarith) hG.1
          _ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by ring
    _ = 10 ^ 6 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ := by
        rw [Work.FTS.StrongEps.ClassCRHS.SGmj]

/-- Angular slot bounds for the three `F_*`-angular profiles: `SA0 α θ = αΓ(θ)/c`,
`SA1 α θ = α D_θΓ(θ)/c` (`Work.FTS.StrongEps.ClassCRHS.SA0`, `SA1`) and
`SA2 α θ = α D_θ²Γ(θ)/c` (`Work.FTS.StrongEps.H5.SA2`), against the sharp majorant
`SGmj α θ = Γ(θ)(α + sin 2θ)`.

For each `α ∈ (0,1]` there are constants `B0, B1 > 0` with `|SAi α θ| ≤ B0` on `Iθ` and
`|DthIter j (fun _ θ' => SAi α θ') 0 θ| ≤ B1·SGmj α θ` for the indicated orders.  The proof is
immediate from the crude angular-jet bound `Work.FTS.LocData6.DthIter_Gam_abs_le6`
(`|D_θ^m Γ| ≤ 10⁵ Γ` for `m ≤ 6`), the majorant inequality `Γ ≤ SGmj/α` on `Iθ`, and
`Work.Spaces.c_bounds` (`1/10 ≤ c(α) ≤ 10`); the orders are chosen so that `SA0` needs `m ≤ 5`,
`SA1` needs `m ≤ 6` and `SA2` needs `m ≤ 6`. -/
theorem AngSlotBounds2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ B0 B1 : ℝ, 0 < B0 ∧ 0 < B1 ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.StrongEps.ClassCRHS.SA0 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ θ' => Work.FTS.StrongEps.ClassCRHS.SA0 α θ') 0 θ|
          ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.StrongEps.ClassCRHS.SA1 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ θ' => Work.FTS.StrongEps.ClassCRHS.SA1 α θ') 0 θ|
          ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.StrongEps.H5.SA2 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ θ' => Work.FTS.StrongEps.H5.SA2 α θ') 0 θ|
          ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) := by
  refine ⟨10 ^ 6, 10 ^ 6, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `|SA0| ≤ 10⁶`
    intro θ hθ
    have h := AngProfAbsLe' α hα hα1 hθ (m := 0) (by omega)
    have heq : Work.FTS.StrongEps.ClassCRHS.SA0 α θ
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[0] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Function.iterate_zero_apply]
      simp only [Work.FTS.StrongEps.ClassCRHS.SA0]
      ring
    rw [heq]; exact h
  · -- the `SA0`-slots, `i ≤ 5`
    intro i hi1 hi5 θ hθ
    rw [DthIter_SA0_repr' α i 0 θ]
    exact AngProfJetLe' α hα hα1 hθ (by omega)
  · -- `|SA1| ≤ 10⁶`
    intro θ hθ
    have h := AngProfAbsLe' α hα hα1 hθ (m := 1) (by omega)
    have heq : Work.FTS.StrongEps.ClassCRHS.SA1 α θ
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Function.iterate_one]
      simp only [Work.FTS.StrongEps.ClassCRHS.SA1]
      ring
    rw [heq]; exact h
  · -- the `SA1`-slots, `i ≤ 5`
    intro i hi1 hi5 θ hθ
    rw [DthIter_SA1_repr' α i 0 θ]
    exact AngProfJetLe' α hα hα1 hθ (by omega)
  · -- `|SA2| ≤ 10⁶`
    intro θ hθ
    have h := AngProfAbsLe' α hα hα1 hθ (m := 2) (by omega)
    have heq : Work.FTS.StrongEps.H5.SA2 α θ
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ := by
      simp only [Work.FTS.StrongEps.H5.SA2]
      ring
    rw [heq]; exact h
  · -- the `SA2`-slots, `i ≤ 4`
    intro i hi1 hi4 θ hθ
    rw [DthIter_SA2_repr' α i 0 θ]
    exact AngProfJetLe' α hα hα1 hθ (by omega)

end

end Work.FTS.StrongEps.H5
