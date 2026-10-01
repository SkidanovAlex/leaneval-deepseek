import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.boxMaxZero

/-!
# `Work.LinnikAreas.boxMaxZeroH` — the maximal zero of `L(·, χ₀)` in the box `|Im| ≤ H`

This is the general-height version of `Work.LinnikAreas.boxMaxZero`: for an arbitrary height
`H ≥ 1` (rather than the specific value `10 log q`), and given a non-zero multiplicity zero `ρ`
of `χ₀` with `|Im ρ| ≤ 1` and `ρ ≠ ρ₀`, we produce a zero `ρ₂ ≠ ρ₀` of `χ₀` in the box
`|Im| ≤ H` which minimises `lamOf q = (1 - Re ·) log q` among *all* zeros of `χ₀` in that box
other than `ρ₀`.

The argument is exactly that of `boxMaxZero`; only the height is a parameter.  The finiteness of
the candidate set is `boxMaxZeroAux.finite_zeroMult_box`, which is stated for an arbitrary height.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **The zero of maximal real part of `L(·,χ₀)` in the box `|Im| ≤ H`, other than `ρ₀`.**

For `2 ≤ q` and `H ≥ 1`, given a non-zero multiplicity zero `ρ ≠ ρ₀` of `χ₀` with `|Im ρ| ≤ 1`,
there is a zero `ρ₂ ≠ ρ₀` of `χ₀` in the box `|Im| ≤ H` which *minimises* `lamOf q`
(equivalently maximises the real part) among all zeros of `χ₀` in that box except `ρ₀`; in
particular `lamOf q ρ₂ ≤ lamOf q ρ`. -/
theorem boxMaxZeroH {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ : ℂ)
    {H : ℝ} (hH1 : 1 ≤ H) (hρ : Work.LinnikContract.zeroMult χ₀ ρ ≠ 0) (him : |ρ.im| ≤ 1)
    (hne : ρ ≠ ρ₀) :
    ∃ ρ₂ : ℂ, Work.LinnikContract.zeroMult χ₀ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ H ∧ ρ₂ ≠ ρ₀ ∧
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ H → u ≠ ρ₀ →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u := by
  classical
  -- `log q > 0` and `ρ` itself lies in the box `|Im| ≤ H`
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have him' : |ρ.im| ≤ H := him.trans hH1
  have hρre : ρ.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one χ₀ hρ
  -- the finite candidate set: zeros in the box with `Re ρ' ≥ Re ρ` (i.e. `lamOf q ρ' ≤ lamOf q ρ`)
  have hfin := boxMaxZeroAux.finite_zeroMult_box χ₀ ρ.re H
  set S := hfin.toFinset with hS
  have hmemS : ∀ u : ℂ, u ∈ S ↔
      zeroMult χ₀ u ≠ 0 ∧ ρ.re ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ H := by
    intro u
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  have hρS : ρ ∈ S := by
    rw [hmemS]
    exact ⟨hρ, le_rfl, le_of_lt hρre, him'⟩
  -- a minimiser of `lamOf q` over the candidate set with `ρ₀` removed
  have hne' : (S.filter (fun u => u ≠ ρ₀)).Nonempty :=
    ⟨ρ, Finset.mem_filter.mpr ⟨hρS, hne⟩⟩
  obtain ⟨ρ₂, hρ₂mem, hmin⟩ :=
    Finset.exists_min_image (S.filter (fun u => u ≠ ρ₀)) (fun u => lamOf q u) hne'
  have hρ₂S : ρ₂ ∈ S := (Finset.mem_filter.mp hρ₂mem).1
  have hρ₂ne : ρ₂ ≠ ρ₀ := (Finset.mem_filter.mp hρ₂mem).2
  obtain ⟨hzm₂, -, -, him₂⟩ := (hmemS ρ₂).mp hρ₂S
  refine ⟨ρ₂, hzm₂, him₂, hρ₂ne, hmin ρ (Finset.mem_filter.mpr ⟨hρS, hne⟩), ?_⟩
  -- minimality among *all* zeros of `χ₀` in the box, except `ρ₀`
  intro u hzu himu hune
  rcases lt_or_ge (lamOf q ρ) (lamOf q u) with hlt | hle
  · exact le_trans (hmin ρ (Finset.mem_filter.mpr ⟨hρS, hne⟩)) (le_of_lt hlt)
  · -- `lamOf q u ≤ lamOf q ρ` forces `Re u ≥ Re ρ`, so `u` is a candidate as well
    have hre_le : ρ.re ≤ u.re := by
      have h1 : (1 - u.re) * Real.log q ≤ (1 - ρ.re) * Real.log q := hle
      have h2 : 1 - u.re ≤ 1 - ρ.re := (mul_le_mul_iff_left₀ hlogpos).mp h1
      linarith
    have huS : u ∈ S := by
      rw [hmemS]
      exact ⟨hzu, hre_le, le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ₀ hzu), himu⟩
    exact hmin u (Finset.mem_filter.mpr ⟨huS, hune⟩)

end Work.LinnikAreas
